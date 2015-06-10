
open Term
open Declarations
open Names
open Libnames
open Pp
open Errors
open Util
open Mod_subst
open Names
open Vars
open Context
open Declareops
open Environ
open Reduction
open Reductionops
open Inductive
open Termops
open Inductiveops
open Recordops
open Namegen
open Globnames
open Pp
open Minihs

let undefined = Obj.magic 0

type state = {
  st_inductives : any_hs_ind Indmap.t
}
let empty_state = {
  st_inductives = Indmap.empty
}
let state = ref empty_state

let sequence_option l = List.fold_right
    (fun a b -> match a, b with
       | Some x, Some y -> Some (x :: y)
       | _ -> None) l (Some [])

let rec is_type_scheme env t =
  match kind_of_term (whd_betadeltaiota env Evd.empty t) with
  | Prod (x,t,c) -> is_type_scheme (push_rel (x,None,t) env) c
  | Sort _ -> true
  | _ -> false

let rec max_var : type a. a var_sing -> a option = function
  | Var_empty -> None
  | Var_next x -> Some (max_var x)
           
let rec extract_kind' : type a. a var_sing -> env -> bool list -> constr -> a hs_kind option = fun x env vs c ->
  match x, kind_of_term (whd_betaiotazeta Evd.empty c) with
  | _, Rel x when x-1 < List.length vs && List.nth vs (x-1) -> Some KStar
  | _, App (a, bs) -> extract_app_kind x env vs a (List.rev (Array.to_list bs))
  | _, Ind (n, u) ->
    let Any_hs_ind ind = Indmap.find n !state.st_inductives in
    (match var_dec_eq x ind.ind_arity with
     | Some Refl -> Some (KConst (ind.ind_arity, Hs_dataname ind.ind_name, TyApp (TyConst (Hs_sdataname ind.ind_name), TyVar (max_var ind.ind_arity))))
     | None -> None
    )
  | Var_empty, Prod (n, t, d) ->
    let env' = push_rel_assum (n,t) env in
    (match extract_kind x env vs t, extract_kind x env' (false :: vs) d with
     | Some kt, Some kd -> Some (KArrow (kt, kd))
     | Some KStar, None -> Option.map (fun a -> KArrow (KUnknown, a)) (extract_kind x env' (true :: vs) d)
     | _ -> None
    )
  | Var_empty, Sort _ -> Some KStar
  | _ -> None
and extract_app_kind : type a. a var_sing -> env -> bool list -> constr -> constr list -> a hs_kind option = fun x env vs a ->
  function
  | [] -> extract_kind x env vs a
  | b :: bs -> match extract_app_kind (Var_next x) env vs a bs, extract_kind x env vs b with
    | Some a, Some b -> Some (KApp (a, b))
    | _ -> None
and extract_kind : type a. a var_sing -> env -> bool list -> constr -> a hs_kind option = fun x env vs c ->
  let k = extract_kind' x env vs c in
  Option.map (fun k -> msg_info (Printer.pr_constr c ++ str " : " ++ pr_hs_kind k); k) k

(* a : type variables *)
(* b : applications *)
(* g : ? extract dependencies *)

and extract_type : type a b. a var_sing -> b var_sing -> bool -> env ->
  a hs_type list -> (b -> a hs_type) -> constr -> a hs_type
  = fun x y g env tvs args c ->
    match y, kind_of_term (whd_betaiotazeta Evd.empty c) with
    | _, App (a, bs) -> extract_app_type x y g env tvs args a (List.rev (Array.to_list bs))
    | _, Ind (n, u) ->
      let Any_hs_ind ind = Indmap.find n !state.st_inductives in
      (match var_dec_eq y ind.ind_arity with
       | Some Refl -> 
         fold_var_sing
           (fun x -> args x, ind.ind_signature x)
           (TyConst (if g then Hs_gdataname ind.ind_name else Hs_dataname ind.ind_name))
           (fun (a, k) b -> if g || is_unlifted_kind k
             then TyApp (b, a)
             else b
           )
           y
       | None -> msg_info (Printer.pr_constr c); assert false
      )
    | Var_empty, Prod (n, t, d) ->
      let env' = push_rel_assum (n,t) env in
      (match extract_kind' Var_empty env [] t with
       | Some k when g ->
         TyForall (k, TyArrow (sing_of (fun _ -> TyVar None) k
                              , extract_type (Var_next x) Var_empty g env' (TyVar None :: List.map lift_type tvs) (fun x -> lift_type (args x)) d))
       | Some k when is_type_scheme env t ->
         TyForall (k, extract_type (Var_next x) Var_empty g env' (TyVar None :: List.map lift_type tvs) (fun x -> lift_type (args x)) d)
       | None when is_type_scheme env t ->
         msg_error (str "type scheme is not a kind " ++ Printer.pr_constr t); TyUnknown
       | _ ->
         TyArrow (extract_type x Var_empty g env tvs args t, extract_type x Var_empty g env' (TyUnknown :: tvs) args d)
      )
    | _, Rel x when x <= List.length tvs -> List.nth tvs (x-1)
    | _, Construct ((n,i),_) when g ->
      let Any_hs_ind ind = Indmap.find n !state.st_inductives in
      let Any_hs_constructor_signature (ar, _, sg) = ind.ind_constructor_signatures.(i-1) in
      (match var_dec_eq y ar with
       | Some Refl ->
         fold_var_sing
           (fun x -> args x, sg x)
           (TyConst (Hs_pconstrname ind.ind_consnames.(i-1)))
           (fun (a, k) b -> if k <> KUnknown
             then TyApp (b, a)
             else b
           )
           y
       | None -> msg_error (str ind.ind_consnames.(i-1) ++ spc () ++ int (int_of_var_sing y) ++ spc () ++ int (int_of_var_sing ar)); TyUnknown (* assert false *)
      )
    | _ -> TyUnknown
and extract_app_type : type a b. a var_sing -> b var_sing -> bool -> env -> a hs_type list -> (b -> a hs_type) -> constr -> constr list -> a hs_type = fun x y g env tvs args a ->
  function
  | [] -> extract_type x y g env tvs args a
  | b :: bs -> extract_app_type x (Var_next y) g env tvs (Option.cata args (extract_type x Var_empty g env tvs Empty.absurd b)) a bs
and extract_signature env c : any_hs_signature =
  let rec extract_signature' : 'a hs_kind -> any_hs_signature = function
    | KArrow (a, b) ->
      let Any_hs_signature (ai, sign) = extract_signature' b in
      Any_hs_signature (Var_next ai, Option.cata sign a)
    | _ -> Any_hs_signature (Var_empty, Empty.absurd)
  in match extract_kind Var_empty env [] c with
  | Some x -> extract_signature' x
    
  (* match kind_of_term (whd_betaiotazeta Evd.empty c) with *)
  (* | Prod (n, t, d) -> *)
  (*   let env' = push_rel_assum (n,t) env in *)
  (*   let Any_hs_signature (ai, sign) = extract_signature env' d in *)
  (*   (match extract_kind Var_empty env [] t with *)
  (*    | None -> msg_error (Printer.pr_constr c); assert false *)
  (*    | Some kt -> Any_hs_signature (Var_next ai, Option.cata sign kt) *)
  (*   ) *)
  (* | Sort _ -> Any_hs_signature (Var_empty, Empty.absurd) *)
  (* | _ -> assert false *)

let rec extract_inductive env kn =
  let mib = Environ.lookup_mind kn env in
  Array.iteri (extract_one_inductive_kind env kn mib) mib.mind_packets;
  Array.iteri (extract_one_inductive env kn mib) mib.mind_packets
and extract_one_inductive_kind env kn mib i mip =
  let (ind,u), ctx = Universes.fresh_inductive_instance env (kn,i) in
  let ar = Inductive.type_of_inductive env ((mib,mip),u) in
  msg_info (str "Inductive signature : " ++ Printer.pr_constr ar);
  let nm = String.capitalize (Names.Id.to_string (mip.mind_typename)) in
  let Any_hs_signature (ari, sign) = extract_signature env ar in
  state := { !state with
             st_inductives = Indmap.add
                 (kn,i)
                 (Any_hs_ind { ind_name = nm
                             ; ind_arity = ari
                             ; ind_signature = sign
                             ; ind_constructor_signatures = Array.map (fun _ -> undefined) mip.mind_consnames
                             ; ind_gconstructors = Array.map (fun _ -> TyUnknown) mip.mind_consnames
                             ; ind_constructors = Array.map (fun _ -> TyUnknown) mip.mind_consnames
                             ; ind_consnames = Array.map (fun s -> String.capitalize (Names.Id.to_string s))
                                   mip.mind_consnames
                             })
                 !state.st_inductives}
and extract_one_inductive env kn mib i mip =
  let (ind,u), ctx = Universes.fresh_inductive_instance env (kn,i) in
  let ar = Inductive.type_of_inductive env ((mib,mip),u) in
  msg_info (str "Inductive signature : " ++ Printer.pr_constr ar);
  let types = arities_of_constructors env ((kn,i),u) in
  let constrs = Array.map (extract_type Var_empty Var_empty false env [] Empty.absurd) types in
  let constr_sigs = Array.map (fun x -> constructor_signature x) constrs in
  let gconstrs = Array.map (extract_type Var_empty Var_empty true env [] Empty.absurd) types in
  state := { !state with
             st_inductives =
               Indmap.modify
                 (kn,i)
                 (fun _ (Any_hs_ind a) -> Any_hs_ind { a with ind_constructor_signatures = constr_sigs
                                                            ; ind_gconstructors = gconstrs
                                                            ; ind_constructors = constrs })
                 !state.st_inductives
           }

let extract_module env r : unit =
  let meb = Modops.destr_nofunctor (lookup_module r env).mod_type in
  List.iter (function
      | (l, SFBmind _) -> extract_inductive env (MutInd.make2 r l)
      | _ -> ()
    ) meb

let locate_module r =
  let q = snd (qualid_of_reference r) in
  try Nametab.locate_module q
  with Not_found -> Nametab.error_global_not_found q

let locate_ref r =
  let q = snd (qualid_of_reference r) in
  try Smartlocate.global_with_alias r
  with Nametab.GlobalizationError _ | UserError _ -> Nametab.error_global_not_found q

let reset () =
  state := empty_state

let out () =
  Indmap.iter (fun _ (Any_hs_ind i) -> msg_info (pr_hs_ind_simple i)) !state.st_inductives;
  Indmap.iter (fun _ (Any_hs_ind i) -> msg_info (pr_hs_ind_sing i)) !state.st_inductives;
  Indmap.iter (fun _ (Any_hs_ind i) -> msg_info (pr_hs_ind_g i)) !state.st_inductives

let module_extraction r =
  reset ();
  let env = Global.env () in
  List.iter (fun r -> extract_module env (locate_module r)) r;
  out ()

let extraction r =
  reset ();
  let env = Global.env () in
  List.iter (fun r ->
      match locate_ref r with
      | IndRef (r,_) -> extract_inductive env r
      | _ -> ()
    ) r;
  out ()
