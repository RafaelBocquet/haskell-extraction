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

module ExtractEnv = struct
  type ('a, 'b) t = 'a svar * 'b svar * ('b -> 'b hs_kind) * (('a * 'b hs_kind) option list)
  let empty : (Empty.t, Empty.t) t = V_empty, V_empty, Empty.absurd, []
  let extend k (va, vb, ks, vs) = ( V_next va
                                  , V_next vb
                                  , extend_kind_list (lift_kind k) ks
                                  , Some (None, KVar None) ::
                                    List.map (Option.map (fun (a, b) -> some a, lift_kind b)) vs
                                  )
  let extend' (va, vb, ks, vs) = (va, vb, ks, None :: vs)
  let extend_fix vc vcs (va, vb, ks, vs) = ( V_either (va, vc), vb, ks
                                           , List.map (fun (a, b) -> Some (Either.right a, b)) vcs @ List.map (Option.map (fun (a, b) -> Either.left a, b)) vs
                                           )
end

let rec extract_type : type a b. (a, b) ExtractEnv.t -> Environ.env -> constr -> (a, b) hs_expr * b hs_kind =
  fun ((va, vb, ks, vs) as eenv) env c -> extract_type_signature eenv env c
and extract_type_signature : type a b. (a, b) ExtractEnv.t -> Environ.env -> constr -> (a, b) hs_expr * b hs_kind =
  fun ((va, vb, ks, vs) as eenv) env c ->
    let cs, (envl, l) = signature_view env c in
    let rec extract_type_signature' : type a b. (a, b) ExtractEnv.t -> (Environ.env * constr) list -> (a, b) hs_expr * b hs_kind =
      fun ((va, vb, ks, vs) as eenv) -> function
        | [] -> extract_type_application eenv envl l
        | (env, c) :: cs ->
          let _, k = extract_type eenv env c in
          let _, sk = extract_type_signature' (ExtractEnv.extend k eenv) cs in
          EStar, KPi (k, defunctionalise_pi vb ks k sk)
    in extract_type_signature' eenv cs
and extract_type_application : type a b. (a, b) ExtractEnv.t -> Environ.env -> constr -> (a, b) hs_expr * b hs_kind =
  fun ((va, vb, ks, vs) as eenv) env c ->
    match application_view env c with
    | Sort _, [] -> EStar, KStar
    | Ind (n, u), bs ->
      (try
         let ind = Indmap.find n !state.st_inductives in
         let se, sk = List.split (List.map (extract_type eenv env) bs) in
         EUnknown
       , kind_application
           (KConst (Hs_dataname ind.ind_name))
           sk
       with Not_found -> msg_error (Names.MutInd.print (fst n)); raise Not_found
      )
    | Rel x, bs when x <= List.length vs ->
      let se, sk = List.split (List.map (extract_type eenv env) bs) in
      let e, k = match List.nth vs (x-1) with
        | Some (v, v') -> EVar v, v'
        | None -> msg_error (str "UNKNOWN VAR"); EUnknown, KUnknown
      in
      expr_fun_application e se
    , kind_fun_application k sk
    | Construct ((n,i),_), bs ->
      (try
         let ind = Indmap.find n !state.st_inductives in
         let es, ks = List.split (List.map2
                                    (function
                                      | true -> fun t ->
                                        let e, k = extract_type eenv env t
                                        in e, KToSing k
                                      | false -> extract_type eenv env
                                    ) (constructor_arity ind.ind_constypes.(i-1)) bs)
         in
         expr_application
           (EConst (Hs_sconstrname (ind.ind_name, i-1)))
           es
       , kind_application
           (KConst (Hs_pconstrname (ind.ind_name, i-1)))
           ks

       with Not_found -> failwith "Unknown construct")
    | Lambda (x, t, c), [] ->
      let env' = push_rel (x,None,t) env in
      let _, k = extract_type eenv env t in
      let _, cty = extract_type (ExtractEnv.extend k eenv) env' (Retyping.get_type_of ~polyprop:true env' Evd.empty c) in
      let e, c' = extract_type (ExtractEnv.extend k eenv) env' c in
      let ck = defunctionalise_lambda vb ks k cty c' in
      EForall
        ( Some ck
        , EAbs ( Some (KSing (lift_kind k, None))
               , e
               )
        )
    , ck
    | Case (ci, creturn, scrut, bs), cs ->
      (try
         let ind = Indmap.find ci.ci_ind !state.st_inductives in
         let a, ak = extract_type eenv env scrut in
         let _, t = extract_type eenv env (Retyping.get_type_of ~polyprop:true env Evd.empty scrut) in
         let _, k = extract_type eenv env creturn in
         let ts = Array.map (extract_type eenv env) bs in
         let se, sk = List.split (List.map (extract_type eenv env) cs) in
         expr_fun_application
           (ECase ( a
                  , Array.mapi (fun i (e, t) ->
                        let Any_con_pattern (p, l) = mk_con_pattern (Hs_sconstrname (ind.ind_name, i)) (List.length (constructor_arity ind.ind_constypes.(i))) in
                        Any_match ( PCon p
                                  , expr_fun_application
                                      (map_expr Either.left id e)
                                      (List.map (fun v -> EVar (Either.right v)) l)
                                  )
                      ) ts
                  )) se
       , kind_fun_application (defunctionalise_match ind vb ks ak t k (Array.map snd ts)) sk
       with Not_found -> failwith "TODO")
    | Fix ((_, i), (c, d, e)), bs ->
      let env' = push_rec_types (c, d, e) env in
      let fks = Array.map (extract_type eenv env) d in
      let Any_var ar = svar_of_int (Array.length d) in
      let e, k = defunctionalise_fix vb ks (Array.map snd fks)
          (fun (Any_fix_result (vc, vcs)) ->
             let eenv' = ExtractEnv.extend_fix vc vcs eenv in
             let b = Array.map (extract_type eenv' env') e in
             EFix (vc, (fun x -> fst b.(int_of_svar vc x)), EVar (Either.right (fst (List.nth vcs i)))), Array.map snd b
          ) in
      let se, sk = List.split (List.map (extract_type eenv env) bs) in
      expr_fun_application e se
    , kind_fun_application k.(i) sk
    | h, _ -> msg_error (str "Unknown type" ++ Printer.pr_constr c); EUnknown, KUnknown

let rec extract_type_constructor : type a. inductive -> Environ.env -> constr -> Empty.t hs_constructor =
  fun df env c ->
    let cs, (envl, l) = signature_view env c in
    let rec extract_type_constructor' : type a b. (a, b) ExtractEnv.t -> (Environ.env * constr) list -> b hs_constructor =
      fun ((va, vb, ks, vs) as eenv) -> function
        | [] -> Hs_constructor (KSig_empty (snd (extract_type eenv envl l)), [])
        | (env, c) :: cs when (head_is_inductive (Some df) env c) ->
          let _, t = extract_type eenv env c in
          let Hs_constructor (s, ts) = extract_type_constructor' (ExtractEnv.extend' eenv) cs in
          Hs_constructor (s, map_kind (lift_of_kind_signature s) t :: ts)
        | (env, c) :: cs ->
          let _, k = extract_type eenv env c in
          let Hs_constructor (s, ts) = extract_type_constructor' (ExtractEnv.extend k eenv) cs in
          Hs_constructor (KSig_next (k, s), map_kind (lift_of_kind_signature s) (KSing (lift_kind k, None)) :: ts)
    in extract_type_constructor' ExtractEnv.empty cs

let rec extract_signature env c =
  let cs, (envl, l) = signature_view env c in
  let rec extract_signature' : type a b. (a, b) ExtractEnv.t -> (Environ.env * constr) list -> b any_hs_kind_signature =
    fun ((va, vb, ks, vs) as eenv) -> function
      | [] -> Any_kind_signature (KSig_empty (snd (extract_type eenv envl l)))
      | (env, c) :: cs ->
        let _, k = extract_type eenv env c in
        let Any_kind_signature s = extract_signature' (ExtractEnv.extend k eenv) cs in
        Any_kind_signature (KSig_next (k, s))
  in extract_signature' ExtractEnv.empty cs


let rec extract_inductive env kn =
  let mib = Environ.lookup_mind kn env in
  Array.iteri (extract_one_inductive_signature env kn mib) mib.mind_packets;
  Array.iteri (extract_one_inductive_constructors env kn mib) mib.mind_packets
and extract_one_inductive_signature env kn mib i mip =
  let (ind,u), ctx = Universes.fresh_inductive_instance env (kn,i) in
  let ar = Inductive.type_of_inductive env ((mib,mip),u) in
  msg_info (str "Inductive signature : " ++ Printer.pr_constr ar);
  let nm = find_dataname (String.capitalize (Id.to_string (mip.mind_typename))) in
  let Any_kind_signature s = extract_signature env ar in
  let _, ct, _ = mk_constant (Hs_dataname (kn, i)) V_empty Empty.absurd Empty.absurd s in
  let ind = { ind_name        = (kn, i)
            ; ind_printname   = nm
            ; ind_signature   = Any_kind_signature s
            ; ind_consnames   = Array.map (fun s -> "BAD") mip.mind_consnames
            ; ind_constypes   = Array.map (fun s -> Obj.magic 0) mip.mind_consnames
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
  let consnames = Array.map (fun s -> find_constrname (String.capitalize (Names.Id.to_string s))) mip.mind_consnames in
  let constypes = Array.map (extract_type_constructor (kn,i) env) types in
  let conscts = Array.mapi (fun j c -> let n = ((kn,i),j) in
                             Hs_pconstrname n, constructor_mk_constant V_empty Empty.absurd n c) constypes in
  state := { !state with
             st_inductives =
               Indmap.modify
                 (kn,i)
                 (fun _ a -> { a with ind_consnames = consnames
                                    ; ind_constypes = constypes })
                 !state.st_inductives
           }

let rec extract_constant env kn =
  let cb = Environ.lookup_constant kn env in
  let e, k = match cb.const_body with
    | Def a -> extract_type ExtractEnv.empty env (Mod_subst.force_constr a)
    | _     -> msg_error (str "Opaque constant ? " ++ Names.Constant.print kn); EUnknown, KUnknown in
  state := { !state with
             st_constants =
               Cmap.add
                 kn
                 { const_name = find_functionname (String.uncapitalize ((Names.Label.to_string (Constant.label kn))))
                 ; const_type = k
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
