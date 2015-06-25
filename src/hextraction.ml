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

let rec extract_type : type a. inductive option -> a svar -> (a -> a hs_kind) -> a hs_kind option list -> Environ.env -> constr -> a hs_type =
  fun df v ks vs env c -> extract_type_signature df v ks vs env c
and extract_kind : type a. inductive option -> a svar -> (a -> a hs_kind) -> a hs_kind option list -> Environ.env -> constr -> a hs_kind =
  fun df v ks vs env c -> defunctionalise v ks (extract_type df v ks vs env c)
and extract_type_singleton : type a. inductive option -> a svar -> (a -> a hs_kind) -> a hs_kind option list -> Environ.env -> constr -> a hs_type =
  fun df v ks vs env c -> singletonise v ks (extract_type df v ks vs env c)
and extract_type_signature : type a. inductive option -> a svar -> (a -> a hs_kind) -> a hs_kind option list -> Environ.env -> constr -> a hs_type =
  fun df v ks vs env c ->
    let cs, (envl, l) = signature_view env c in
    let rec extract_type_signature' : type a. a svar -> (a -> a hs_kind) -> a hs_kind option list -> (Environ.env * constr) list -> a hs_type =
      fun v ks vs -> function
        | [] -> extract_type_application df v ks vs envl l
        | (env, c) :: cs when not (head_is_inductive df env c) ->
          let k = extract_kind df v ks vs env c in
          let t = TyForall ( k
                           , extract_type_signature' (V_next v) (extend_kind_list (lift_kind k) ks) (Some (KVar None) :: List.map (Option.map lift_kind) vs) cs)
          in t
        | (env, c) :: cs ->
          TyArrow ( extract_type df v ks vs env c
                  , extract_type_signature' v ks (None :: vs) cs)
    in extract_type_signature' v ks vs cs
and extract_type_application : type a. inductive option -> a svar -> (a -> a hs_kind) -> a hs_kind option list -> Environ.env -> constr -> a hs_type =
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
        (TyKind (match List.nth vs (x-1) with | Some v -> v | None -> msg_error (str "UNKNOWN VAR"); KUnknown))
        (List.map (extract_type df v ks vs env) bs)
    | Construct ((n,i),_), bs ->
      (try
         let ind = Indmap.find n !state.st_inductives in
         type_application
           (TyConst (Hs_pconstrname (ind.ind_name, i-1)))
           (List.map2
              (function
                | true -> fun t -> TyToSing (extract_type df v ks vs env t)
                | false -> extract_type df v ks vs env
              ) ind.ind_consarities.(i-1) bs)
       with Not_found -> failwith "Unknown construct")
    | Lambda (x, t, c), [] ->
      let env' = push_rel (x,None,t) env in
      let k = extract_kind df v ks vs env t in
      let cty = extract_kind df (V_next v) (extend_kind_list (lift_kind k) ks) (Some (KVar None) :: List.map (Option.map lift_kind) vs) env' (Retyping.get_type_of ~polyprop:true env' Evd.empty c) in
      let c' = extract_kind df (V_next v) (extend_kind_list (lift_kind k) ks) (Some (KVar None) :: List.map (Option.map lift_kind) vs) env' c in
      TyKind (defunctionalise_lambda v ks k cty c')
    | Case (ci, creturn, a, bs), [] ->
      (try
         let ind = Indmap.find ci.ci_ind !state.st_inductives in
         let a' = extract_kind df v ks vs env a in
         let t = extract_kind df v ks vs env (Retyping.get_type_of ~polyprop:true env Evd.empty a) in
         let k = extract_kind df v ks vs env creturn in
         let ts = Array.map (extract_kind df v ks vs env) bs in
         msg_error (str "MATCH\n" ++
                    Printer.pr_constr c ++ fnl () ++
                    prvect_with_sep spc int ci.ci_cstr_ndecls ++ fnl () ++
                    prvect_with_sep spc int ci.ci_cstr_nargs ++ fnl () ++
                    Printer.pr_constr creturn ++ fnl () ++
                    pr_hs_kind k ++ fnl () ++
                    str "sc: " ++ Printer.pr_constr a ++ fnl () ++
                    pr_hs_kind t ++ fnl () ++
                    prvect_with_sep fnl Printer.pr_constr bs ++ fnl () ++
                    str "ts: " ++ prvect_with_sep fnl pr_hs_kind ts
                  ); TyKind (defunctionalise_match ind v ks a' t k ts)
       with Not_found -> failwith "TODO")
    | Fix ((a, b), (c, d, e)), _ ->
      let env' = push_rec_types (c, d, e) env in
      let fks = Array.map (extract_kind df v ks vs env) d in
      TyKind (defunctionalise_fix v ks fks (fun a -> Array.map (extract_kind df v ks (List.map some a @ vs) env') e) b)
    | h, _ -> msg_error (str "Unknown type" ++ Printer.pr_constr c); TyUnknown

and extract_term : type a b. a svar -> a option list -> b svar -> (b -> b hs_kind) -> b hs_kind option list -> Environ.env -> constr -> (a, b) hs_expr =
  fun v vs v' ks kvs env t -> extract_term_application v vs v' ks kvs env t
(* and extract_term_abstraction : type a b. a svar -> a option list -> b svar -> (b -> b hs_kind) -> b hs_kind option list -> Environ.env -> constr -> (a, b) hs_expr = *)
(*   fun v vs v' ks kvs env t -> *)
(*     let cs, (envl, l) = abstraction_view env t in *)
(*     let rec extract_term_abstraction' : type a b. a svar -> a option list -> b svar -> (b -> b hs_kind) -> b hs_kind option list -> (Environ.env * constr) list -> (a, b) hs_expr = *)
(*       fun v vs v' ks kvs -> function *)
(*         | (env, c) :: cs -> *)
(*           let k = extract_kind None v' ks kvs env c in *)
(*           EForall *)
(*             (EAbs ( Some (TySing (lift_kind k, None)) *)
(*                   , extract_term_abstraction' (V_next v) (Some (KVar None) :: List.map (Option.map lift_kind) vs) (V_next v') (extend_kind_list (lift_kind k) ks) (Some (KVar None) :: List.map (Option.map lift_kind) kvs) cs *)
(*                   )) *)
(*         | [] -> extract_term_application v vs v' ks kvs envl l *)
(*     in extract_term_abstraction' v vs v' ks kvs cs *)
and extract_term_application : type a b. a svar -> a option list -> b svar -> (b -> b hs_kind) -> b hs_kind option list -> Environ.env -> constr -> (a, b) hs_expr =
  fun v vs v' ks kvs env c ->
    match application_view env c with
    | Prod (_, _, _), [] -> EStar
    | Lambda (x, t, c'), [] ->
      let env' = push_rel (x,None,t) env in
      let k1 = extract_kind None v' ks kvs env c in
      let k = extract_kind None v' ks kvs env t in
      EForall
        ( Some k1
        , EAbs ( Some (TySing (lift_kind k, None))
               , extract_term (V_next v) (Some None :: List.map (Option.map some) vs) (V_next v') (extend_kind_list (lift_kind k) ks) (Some (KVar None) :: List.map (Option.map lift_kind) kvs) env' c'
               ))
    | Rel x, bs when x <= List.length vs ->
      expr_fun_application
        (match List.nth vs (x-1) with | Some v -> EVar v | None -> msg_error (str "UNKNOWN VAR"); EUnknown)
        (List.map (extract_term v vs v' ks kvs env) bs)
    | Case (ci, creturn, a, bs), cs ->
      (try
         let ind = Indmap.find ci.ci_ind !state.st_inductives in
         let a' = extract_term v vs v' ks kvs env a in
         (* let a' = extract_kind df v ks vs env a in *)
         (* let t = extract_kind df v ks vs env (Retyping.get_type_of ~polyprop:true env Evd.empty a) in *)
         (* let k = extract_kind df v ks vs env creturn in *)
         (* let ts = Array.map (extract_kind df v ks vs env) bs in *)
         ECase ( a'
               , Array.mapi (fun i b ->
                    let Any_con_pattern (p, l) = mk_con_pattern (Hs_sconstrname (ind.ind_name, i)) (List.length ind.ind_consarities.(i)) in
                     Any_match ( PCon p
                               , expr_fun_application
                                   (map_expr Either.left id (extract_term v vs v' ks kvs env b))
                                   (List.map (fun v -> EVar (Either.right v)) l)
                               )
                 ) bs
               )
       with Not_found -> failwith "TODO")
    | Construct ((n,i),_), bs ->
      (try
         let ind = Indmap.find n !state.st_inductives in
         expr_fun_application
           (EConst (Hs_ssconstrname (ind.ind_name, i-1)))
           (List.map2
              (function
                | true -> fun t -> extract_term v vs v' ks kvs env t
                | false -> extract_term v vs v' ks kvs env
              ) ind.ind_consarities.(i-1) bs)
       with Not_found -> failwith "Unknown Construct")
    | _ -> EUnknown


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
  let rec extract_signature' : type a. a svar -> (a -> a hs_kind) -> a hs_kind option list -> (Environ.env * constr) list -> a any_hs_kind_signature = fun v ks vs -> function
    | [] -> Any_kind_signature (KSig_empty (extract_kind df v ks vs envl l))
    | (env, c) :: cs ->
      let k = extract_kind df v ks vs env c in
      let Any_kind_signature s = extract_signature' (V_next v) (extend_kind_list (lift_kind k) ks) (Some (KVar None) :: List.map (Option.map lift_kind) vs) cs in
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
  let nm = find_dataname (String.capitalize (Id.to_string (mip.mind_typename))) in
  let Any_kind_signature s = extract_signature (Some (kn,i)) env ar in
  let _, ct, _ = mk_constant (Hs_dataname (kn, i)) V_empty Empty.absurd Empty.absurd s in
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
  let consarities = Array.map (extract_type_constructor_arities (kn,i) env) types in
  let consnames = Array.map (fun s -> find_constrname (String.capitalize (Names.Id.to_string s))) mip.mind_consnames in
  let constypes = Array.map (extract_type_singleton (Some (kn,i)) V_empty Empty.absurd [] env) types in
  let conscts = Array.mapi (fun j c -> let n = Hs_pconstrname ((kn,i),j) in
                             n, constructor_mk_constant n c) constypes in
  let consects = Array.mapi (fun j (_, c) ->
                              ((kn,i),j)
                            , constructor_mk_econstant (KConst c) (Hs_sconstrname ((kn, i), j)) consarities.(j)
                            ) conscts in
  let sconstypes = Array.mapi (fun j c -> singleton_constructor V_empty Empty.absurd
                                  (TyConst (Hs_pconstrname ((kn, i), j))) c) constypes in
  state := { !state with
             st_inductives =
               Indmap.modify
                 (kn,i)
                 (fun _ a -> { a with ind_consnames = consnames
                                    ; ind_constypes = constypes
                                    ; ind_sconstypes = sconstypes
                                    ; ind_consarities = consarities })
                 !state.st_inductives
           ; st_ssconstrs =
               Array.fold_left (fun acc (k, v) -> Constrmap.add k v acc) !state.st_ssconstrs consects
           ; st_list =
               Array.fold_left (fun acc (k, _) -> Hs_ssconstr k :: acc) !state.st_list consects
           ; st_defunctionalise_const_map =
               Array.fold_left (fun acc (k, v) -> Namemap.add k v acc) !state.st_defunctionalise_const_map conscts
           }

let rec extract_constant env kn =
  let cb = Environ.lookup_constant kn env in
  let k, e = match cb.const_body with
    | Def a -> extract_kind None V_empty Empty.absurd [] env (Mod_subst.force_constr a)
             , extract_term V_empty [] V_empty Empty.absurd [] env (Mod_subst.force_constr a)
    | _     -> msg_error (str "Opaque constant ? " ++ Names.Constant.print kn); KUnknown, EUnknown in
  state := { !state with
             st_constants =
               Cmap.add
                 kn
                 { const_name = find_functionname (String.uncapitalize ((Names.Label.to_string (Constant.label kn))))
                 ; const_type = TyKind k
                 ; const_expr = e
                 }
                 !state.st_constants
           ; st_list = Hs_const kn :: !state.st_list
           }

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

    List.fold_right (fun i acc -> List.fold_right (fun i acc -> acc ++ match i with
        | Hs_ind d -> pr_hs_ind (Indmap.find d !state.st_inductives)
        | Hs_sind d -> pr_hs_sing (Indmap.find d !state.st_inductives)
        | Hs_const c -> pr_hs_constant (Cmap.find c !state.st_constants)
        | Hs_symbol s -> pr_hs_symbol (Stringmap.find s !state.st_symbols)
        | Hs_typefamily a -> pr_hs_type_family (Stringmap.find a !state.st_typefamilies)
        | Hs_tyarr a -> pr_hs_type_family (Stringmap.find a !state.st_tyarrs)
        | Hs_typi a -> pr_hs_type_family (Stringmap.find a !state.st_typis)
        | Hs_ssconstr a -> pr_hs_constant (Constrmap.find a !state.st_ssconstrs)
      ) i (acc ++ pr_th_hack ())
      ) (List.rev (sort_elems !state.st_list)) (mt ()));
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
