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
open Hutil
open Minihs

module Indmap = Minihs.Indmap

let rec extract_type : type a. inductive option -> a svar -> (a -> a hs_kind) -> a option list -> Environ.env -> constr -> a hs_type =
  fun df v ks vs env c -> extract_type_signature df v ks vs env c
and extract_kind : type a. inductive option -> a svar -> (a -> a hs_kind) -> a option list -> Environ.env -> constr -> a hs_kind =
  fun df v ks vs env c -> defunctionalise v ks (extract_type df v ks vs env c)
and extract_type_singleton : type a. inductive option -> a svar -> (a -> a hs_kind) -> a option list -> Environ.env -> constr -> a hs_type =
  fun df v ks vs env c -> singletonise v ks (extract_type df v ks vs env c)
and extract_type_signature : type a. inductive option -> a svar -> (a -> a hs_kind) -> a option list -> Environ.env -> constr -> a hs_type =
  fun df v ks vs env c ->
    let cs, (envl, l) = signature_view env c in
    let rec extract_type_signature' : type a. a svar -> (a -> a hs_kind) -> a option list -> (Environ.env * constr) list -> a hs_type =
      fun v ks vs -> function
        | [] -> extract_type_application df v ks vs envl l
        | (env, c) :: cs when not (head_is_inductive df env c) ->
          let k = extract_kind df v ks vs env c in
          let t = TyForall ( k
                           , extract_type_signature' (V_next v) (extend_kind_list (lift_kind k) ks) (Some None :: List.map some vs) cs)
          in t
        | (env, c) :: cs ->
          TyArrow ( extract_type df v ks vs env c
                  , extract_type_signature' v ks (None :: vs) cs)
    in extract_type_signature' v ks vs cs
and extract_type_application : type a. inductive option -> a svar -> (a -> a hs_kind) -> a option list -> Environ.env -> constr -> a hs_type =
  fun df v ks vs env c ->
    match application_view env c with
    | Sort _, [] -> TyStar
    | Ind (n, u), bs ->
      (try
         let ind = Indmap.find n !state.st_inductives in
         type_application
           (TyConst (Hs_dataname ind.ind_name))
           (List.map (extract_type df v ks vs env) bs)
       with Not_found -> msg_error (Names.MutInd.print (fst n)); raise Not_found
      )
    | Rel x, bs when x <= List.length vs ->
      type_application
        (TyKind (match List.nth vs (x-1) with | Some v -> KVar v | None -> msg_error (str "UNKNOWN VAR"); KUnknown))
        (List.map (extract_type df v ks vs env) bs)
    | Construct ((n,i),_), bs ->
      (try
         let ind = Indmap.find n !state.st_inductives in
         type_application
           (TyConst (Hs_pconstrname (ind.ind_name, i-1)))
           (List.map2
              (function
                | true -> fun t -> TyApp (TyConst Hs_ToSing, extract_type df v ks vs env t)
                | false -> extract_type df v ks vs env
              ) ind.ind_consarities.(i-1) bs)
       with Not_found -> failwith "")
    | h, _ -> msg_error (Printer.pr_constr c); TyUnknown

let rec extract_type_constructor_arities : type a. inductive -> Environ.env -> constr -> bool list =
  fun df env c -> extract_type_constructor_arities_signature df env c
and extract_type_constructor_arities_signature : type a. inductive -> Environ.env -> constr -> bool list =
  fun df env c ->
    let cs, (envl, l) = signature_view env c in
    let rec extract_type_constructor_arities_signature' : type a. (Environ.env * constr) list -> bool list =
      function
        | [] -> []
        | (env, c) :: cs ->
          not (head_is_inductive (Some df) env c) :: extract_type_constructor_arities_signature' cs
    in extract_type_constructor_arities_signature' cs

let rec extract_signature df env c =
  let cs, (envl, l) = signature_view env c in
  let rec extract_signature' : type a. a svar -> (a -> a hs_kind) -> a option list -> (Environ.env * constr) list -> a any_hs_kind_signature = fun v ks vs -> function
    | [] -> Any_kind_signature (KSig_empty (extract_kind df v ks vs envl l))
    | (env, c) :: cs ->
      let k = extract_kind df v ks vs env c in
      let Any_kind_signature s = extract_signature' (V_next v) (extend_kind_list (lift_kind k) ks) (Some None :: List.map some vs) cs in
      Any_kind_signature (KSig_next (k, s))
  in
  extract_signature' V_empty Empty.absurd [] cs


let rec extract_inductive env kn =
  let mib = Environ.lookup_mind kn env in
  Array.iteri (extract_one_inductive_signature env kn mib) mib.mind_packets;
  Array.iteri (extract_one_inductive_constructors env kn mib) mib.mind_packets
and extract_one_inductive_signature env kn mib i mip =
  let (ind,u), ctx = Universes.fresh_inductive_instance env (kn,i) in
  let ar = Inductive.type_of_inductive env ((mib,mip),u) in
  msg_info (str "Inductive signature : " ++ Printer.pr_constr ar);
  let nm = String.capitalize (Id.to_string (mip.mind_typename)) in
  let Any_kind_signature s = extract_signature (Some (kn,i)) env ar in
  let ct, _ = mk_constant (Hs_dataname (kn, i)) V_empty Empty.absurd s in
  let ind = { ind_name        = (kn, i)
            ; ind_printname   = nm
            ; ind_signature   = Any_kind_signature s
            ; ind_consnames   = Array.map (fun s -> "BAD") mip.mind_consnames
            ; ind_constypes   = Array.map (fun s -> TyStar) mip.mind_consnames
            ; ind_sconstypes  = Array.map (fun s -> TyStar) mip.mind_consnames
            ; ind_consarities = Array.map (fun s -> []) mip.mind_consnames
            } in
  state := { !state with
             st_inductives = Indmap.add
                 (kn, i) ind !state.st_inductives
           ; st_list = Hs_sind (kn,i) :: Hs_ind (kn,i) :: !state.st_list
           };
  state := { !state with
             st_defunctionalise_const_map =
               Namemap.add (Hs_dataname ind.ind_name) ct !state.st_defunctionalise_const_map
           }
and extract_one_inductive_constructors env kn mib i mip =
  let (ind,u), ctx = Universes.fresh_inductive_instance env (kn,i) in
  let types = arities_of_constructors env ((kn,i),u) in
  Array.iter (fun x -> msg_info (str "Constructor signature : " ++ Printer.pr_constr x)) types;
  let consnames =  Array.map (fun s -> String.capitalize (Names.Id.to_string s)) mip.mind_consnames in
  let constypes = Array.map (extract_type_singleton (Some (kn,i)) V_empty Empty.absurd [] env) types in
  let sconstypes = Array.mapi (fun j c -> singleton_constructor V_empty Empty.absurd
                                  (TyConst (Hs_pconstrname ((kn, i), j))) c) constypes in
  let consarities = Array.map (extract_type_constructor_arities (kn,i) env) types in
  state := { !state with
             st_inductives =
               Indmap.modify
                 (kn,i)
                 (fun _ a -> { a with ind_consnames = consnames
                                    ; ind_constypes = constypes
                                    ; ind_sconstypes = sconstypes
                                    ; ind_consarities = consarities })
                 !state.st_inductives
           ; st_list = !state.st_list
           }

let rec extract_constant env kn =
  let cb = Environ.lookup_constant kn env in
  let nm = String.uncapitalize (Label.to_string (Constant.label kn)) in
  let ty = (match cb.const_type with
      | RegularArity ty -> msg_info (Printer.pr_constr ty); let t = extract_type_singleton None V_empty Empty.absurd [] env ty in msg_info (pr_hs_type t); t
      | TemplateArity _ -> failwith "TemplateArity"
    ) in
  (* let ex = (match cb.const_body with *)
  (*     | Def a -> (try extract_term true [] [] env (Mod_subst.force_constr a) *)
  (*                 with _ -> EUnknown) *)
  (*     | _     -> msg_error (Names.Constant.print kn); EUnknown *)
  (*   ) in *)
  state := { !state with
             st_constants =
               Cmap.add
                 kn
                 { const_name = nm
                 ; const_type = ty
                 ; const_expr = EUnknown
                 }
                 !state.st_constants;
             st_list = Hs_const kn :: !state.st_list
           }
(* and extract_term : type a b. bool -> a list -> b hs_type list -> Environ.env -> constr -> (a, b) hs_expr = *)
(*   fun sg vs ts env c -> match kind_of_term (whd_betadeltaiota env Evd.empty c)  with *)
(*     | Lambda (x,t,c) -> *)
(*       let env' = push_rel (x,None,t) env in *)
(*       let k = extract_type None true false ts env t in *)
(*       EForall *)
(*         (EAbs (Some (singleton_of k), extract_term sg (None :: List.map (fun x -> Some x) vs) (TyVar None :: List.map lift_type ts) env' c)) *)
(*     | Case (ci, creturn, a, bs) -> *)
(*       (try *)
(*          let ind = Indmap.find ci.ci_ind !state.st_inductives in *)
(*          msg_info (str "MATCH\n" ++ *)
(*                    prvect_with_sep spc int ci.ci_cstr_ndecls ++ fnl () ++ *)
(*                    prvect_with_sep spc int ci.ci_cstr_nargs++ fnl () ++ *)
(*                    Printer.pr_constr creturn ++ fnl () ++ *)
(*                    Printer.pr_constr a ++ fnl () ++ *)
(*                    prvect_with_sep fnl Printer.pr_constr bs *)
(*                   ); *)
(*          ECase ( extract_term false vs ts env a *)
(*                , Array.mapi (fun i c -> *)
(*                      let ar = List.length (ind.ind_consarities.(i)) in *)
(*                      let Any_con_pattern (p, v) = mk_con_pattern (Hs_sconstrname ind.ind_consnames.(i)) ar in *)
(*                      Any_match (PCon p, extract_term sg (List.map Either.left vs) ts env c) *)
(*                    ) bs *)
(*                ) *)
(*        with Not_found -> failwith "TODO") *)
(*     | App _ | Rel _ | Construct _ when sg -> EApp (EConst (Hs_constrname "SomeSing"), extract_term false vs ts env c) *)
(*     | App (a, bs) -> *)
(*       expr_application *)
(*         (extract_term false vs ts env a) *)
(*         (List.map (extract_term false vs ts env) (Array.to_list bs)) *)
(*     | Rel x when x <= List.length vs -> EVar (List.nth vs (x-1)) *)
(*     | Construct ((n,i),_) -> *)
(*       (try *)
(*          let ind = Indmap.find n !state.st_inductives in *)
(*          EConst (Hs_sconstrname ind.ind_consnames.(i-1)) *)
(*        with Not_found -> failwith "") *)
(*     | t -> msg_error (Printer.pr_constr c); EUnknown *)

(* and extract_term : type a b. bool -> a list -> b hs_type list -> Environ.env -> constr -> (a, b) hs_expr = *)
(*   fun sg vs ts env c -> extract_term_abstraction sg vs ts env c *)
(* and extract_term_abstraction : type a b. bool -> a list -> b hs_type list -> Environ.env -> constr -> (a, b) hs_expr = *)
(*   fun sg vs ts env c -> *)
(*     let cs, (envl, l) = abstraction_view env c in *)
(*     let rec extract_term_abstraction' : type a b. a list -> b hs_type list -> (Environ.env * constr) list -> (a, b) hs_expr = *)
(*       fun vs ts -> function *)
(*         | [] when sg -> EApp (EConst (Hs_constrname "SomeSing"), extract_term_application vs ts envl l) *)
(*         | [] -> extract_term_application vs ts envl l *)
(*         | (env, c) :: cs -> *)
(*           let k = extract_type None ts env c in *)
(*           EForall *)
(*             (EAbs ( Some (singleton_of k) *)
(*                   , extract_term_abstraction' (None :: List.map (fun x -> Some x) vs) (TyVar None :: List.map lift_type ts) cs)) *)
(*     in extract_term_abstraction' vs ts cs *)
(* and extract_term_application : type a b. a list -> b hs_type list -> Environ.env -> constr -> (a, b) hs_expr = *)
(*   fun vs ts env c -> *)
(*     match application_view env c with *)
(*     | Rel x, bs when x <= List.length vs -> *)
(*       expr_application *)
(*         (EVar (List.nth vs (x-1))) *)
(*         (List.map (extract_term false vs ts env) bs) *)
(*     | Construct ((n,i),_), bs -> *)
(*       (try *)
(*          let ind = Indmap.find n !state.st_inductives in *)
(*          expr_application *)
(*            (EConst (Hs_constrname ind.ind_consnames.(i-1))) *)
(*            (List.map2 *)
(*               (function *)
(*                 | true -> fun t -> EApp (EConst (Hs_dataname "SSing"), extract_term false vs ts env t) *)
(*                 | false -> extract_term false vs ts env *)
(*               ) ind.ind_consarities.(i-1) bs) *)
(*        with Not_found -> failwith "") *)
(*     | h, _ -> msg_error (Printer.pr_constr c); EUnknown *)

let out () =
  let cout = open_out "OUT.hs" in
  let ft = Format.formatter_of_out_channel cout in
  Format.pp_set_margin ft 120;
  pp_with ft (
    str "{-# LANGUAGE GADTs, RankNTypes, DataKinds, PolyKinds, TypeFamilies, TypeOperators, ScopedTypeVariables #-}" ++ fnl () ++
    str "{-# LANGUAGE MultiParamTypeClasses, FlexibleInstances, UndecidableInstances, FlexibleContexts #-}" ++ fnl () ++
    str "{-# LANGUAGE TemplateHaskell, EmptyCase, PartialTypeSignatures, NoMonomorphismRestriction, ImpredicativeTypes #-}" ++ fnl () ++
    str "{-# OPTIONS_GHC -fno-max-relevant-binds #-}" ++ fnl () ++
    str "{-# OPTIONS_GHC -fprint-explicit-kinds #-}" ++ fnl () ++
    str "{-# OPTIONS_GHC -fwarn-unticked-promoted-constructors #-}" ++ fnl () ++

    str "module OUT where" ++ fnl () ++ fnl () ++
    str "import Prelude ()" ++ fnl () ++
    str "import qualified Prelude as P" ++ fnl () ++
    str "import qualified Language.Haskell.TH as TH" ++ fnl () ++ fnl () ++

    str "data family Sing (k :: *) :: k -> *" ++ fnl () ++
    str "type Sing' (x :: k) = Sing k x" ++ fnl () ++
    (* str "class SingI (k :: *\) (x :: k) where" ++ fnl () ++ *)
    (* str "  sing :: Sing k x" ++ fnl () ++ *)
    str "type family FromSing (y :: Sing k x) :: k" ++ fnl () ++
    str "type family ToSing (x :: k) :: Sing k x" ++ fnl () ++
    str "class SingKind (k :: *) where" ++ fnl () ++
    str "  fromSing :: Sing k x -> k" ++ fnl () ++ 
    str "data SomeSing (k :: *) where SomeSing :: forall (k :: *) (x :: k). Sing k x -> SomeSing k" ++ fnl () ++
    str "$(do TH.reportWarning \"Typechecked Sing\"; P.return [])" ++ fnl () ++ fnl () ++

    str "data instance Sing * x where" ++ fnl () ++
    str "  SStar :: forall (x :: *). Sing * x" ++ fnl () ++
    str "$(do TH.reportWarning \"Typechecked SStar\"; P.return [])" ++ fnl () ++ fnl () ++

    str "data TyFun' (a :: *) (b :: *) :: *" ++ fnl () ++
    str "type TyFun (a :: *) (b :: *) = TyFun' a b -> *" ++ fnl () ++
    str "type family (a :: TyFun k1 k2) @@ (b :: k1) :: k2" ++ fnl () ++
    str "data TyPi' (a :: *) (b :: TyFun a *) :: *" ++ fnl () ++
    str "type TyPi (a :: *) (b :: TyFun a *) = TyPi' a b -> *" ++ fnl () ++
    str "type family (a :: TyPi k1 k2) @@@ (b :: k1) :: k2 @@ b" ++ fnl () ++
    str "data instance Sing (TyPi k1 k2) x where" ++ fnl () ++
    str "  SLambda :: (forall (t :: k1). Sing k1 t -> Sing (k2 @@ t) (f @@@ t)) -> Sing (TyPi k1 k2) f" ++ fnl () ++
    str "unSLambda :: Sing (TyPi k1 k2) f -> (forall t. Sing k1 t -> Sing (k2 @@ t) (f @@@ t))" ++ fnl () ++
    str "unSLambda (SLambda x) = x" ++ fnl () ++
    str "$(do TH.reportWarning \"Typechecked TyFun & TyPi\"; P.return [])" ++ fnl () ++ fnl () ++

    str "data instance Sing (Sing k x) y where" ++ fnl () ++
    str "  SSing :: forall (y :: Sing k x). Sing k x -> Sing (Sing k x) y" ++ fnl () ++
    str "$(do TH.reportWarning \"Typechecked SSing\"; P.return [])" ++ fnl () ++
    str "type instance ToSing (y :: Sing k x) = 'SSing y" ++ fnl () ++
    str "type instance FromSing ('SSing y) = y" ++ fnl () ++ 
    str "instance SingKind (Sing k x) where" ++ fnl () ++
    str "  fromSing (SSing x) = x" ++ fnl () ++ fnl () ++

    List.fold_right (fun i acc -> acc ++ match i with
      | Hs_ind d -> pr_hs_ind (Indmap.find d !state.st_inductives)
      | Hs_sind d -> pr_hs_sing (Indmap.find d !state.st_inductives)
      | Hs_const c -> pr_hs_constant (Cmap.find c !state.st_constants)
      | Hs_symbol s -> pr_hs_symbol (Stringmap.find s !state.st_symbols) ++ pr_th_hack ()
      | Hs_typefamily (a, b) -> pr_hs_type_family (Tfmap.find (a, b) !state.st_typefamilies) ++ pr_th_hack ()
      ) (List.concat (List.rev (sort_elems !state.st_list))) (mt ()));
  close_out cout


let extract_module env r : unit =
  let meb = Modops.destr_nofunctor (lookup_module r env).mod_type in
  List.iter (function
      | (l, SFBmind _) -> extract_inductive env (MutInd.make2 r l)
      (* | (l, SFBconst _) -> extract_constant env (Constant.make2 r l) *)
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

let extraction ms gs =
  reset ();
  let env = Global.env () in
  List.iter (fun r -> extract_module env (locate_module r)) ms;
  List.iter (fun r ->
      match locate_ref r with
      | IndRef (r,_) -> extract_inductive env r
      | ConstRef c -> extract_constant env c
      | _ -> ()
    ) gs;
  out ()
