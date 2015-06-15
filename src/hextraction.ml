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

module InductiveOrdered = struct
  type t = inductive
  let compare = ind_ord
end
module InductiveOrdered_env = struct
  type t = inductive
  let compare = ind_user_ord
end
module Indset = Set.Make(InductiveOrdered)
module Indmap = CMap.Make(InductiveOrdered)
module Indmap_env = CMap.Make(InductiveOrdered_env)

type state =
  { st_inductives_list : Indmap.key list
  ; st_inductives : hs_ind Indmap.t
  }
let empty_state =
  { st_inductives_list = []
  ; st_inductives = Indmap.empty
  }
let state = ref empty_state

let rec extract_type : type a. inductive option -> bool -> a hs_type list -> Environ.env -> constr -> a hs_type = fun df g vs env c -> extract_type_signature df g vs env c
and extract_type_signature : type a. inductive option -> bool -> a hs_type list -> Environ.env -> constr -> a hs_type =
  fun df g vs env c ->
  let cs, (envl, l) = signature_view env c in
  let rec extract_type_signature' : type a. a hs_type list -> (Environ.env * constr) list -> a hs_type =
    fun vs -> function
    | [] -> extract_type_application df g vs envl l
    | (env, c) :: cs when g && not (head_is_inductive df env c) ->
      let k = extract_type df false vs env c in
      TyForall ( k
               , TyArrow ( singleton_of k
                         , (extract_type_signature' (TyVar None :: List.map lift_type vs)
                              cs)))
    | (env, c) :: cs ->
      TyArrow ( extract_type df false vs env c
              , extract_type_signature' (TyUnknown :: vs)
                  cs)
  in extract_type_signature' vs cs
and extract_type_application : type a. inductive option -> bool -> a hs_type list -> Environ.env -> constr -> a hs_type = fun df g vs env c ->
  match application_view env c with
  | Sort _, [] -> TyStar
  | Ind (n, u), bs ->
    let ind = Indmap.find n !state.st_inductives in
    type_application
      (TyConst (Hs_dataname ind.ind_name))
      (List.map (extract_type df g vs env) bs)
  | Rel x, bs when x <= List.length vs ->
    type_application
      (List.nth vs (x-1))
      (List.map (extract_type df g vs env) bs)
  | Construct ((n,i),_), bs ->
    let ind = Indmap.find n !state.st_inductives in
    type_application
      (TyConst (Hs_pconstrname ind.ind_consnames.(i-1)))
      (List.map (extract_type df g vs env) bs)
  | h, _ -> msg_error (Printer.pr_constr c); failwith "TODO"

let rec extract_signature df env c =
  let cs, (envl, l) = signature_view env c in
  let rec extract_signature' : type a. a hs_type list -> (Environ.env * constr) list -> a any_hs_signature = fun vs -> function
    | [] -> Any_signature (Sig_empty (extract_type df false vs envl l))
    | (env, c) :: cs ->
       let Any_signature s = extract_signature' (TyVar None :: List.map lift_type vs) cs in
       Any_signature (Sig_next (extract_type df false vs env c, s))
  in
  extract_signature' [] cs


let rec extract_inductive env kn =
  let mib = Environ.lookup_mind kn env in
  Array.iteri (extract_one_inductive_signature env kn mib) mib.mind_packets;
  Array.iteri (extract_one_inductive_constructors env kn mib) mib.mind_packets
and extract_one_inductive_signature env kn mib i mip =
  let (ind,u), ctx = Universes.fresh_inductive_instance env (kn,i) in
  let ar = Inductive.type_of_inductive env ((mib,mip),u) in
  msg_info (str "Inductive signature : " ++ Printer.pr_constr ar);
  let nm = String.capitalize (Names.Id.to_string (mip.mind_typename)) in
  let s = extract_signature (Some (kn,i)) env ar in
  msg_info (str nm ++ pr_any_hs_signature s);
  state := { !state with
             st_inductives = Indmap.add
                 (kn, i)
                 { ind_name      = nm
                 ; ind_signature = s
                 ; ind_consnames = Array.map (fun s -> String.capitalize (Names.Id.to_string s)) mip.mind_consnames
                 ; ind_constypes = Array.map (fun s -> TyStar) mip.mind_consnames
                 }
                 !state.st_inductives
           }
and extract_one_inductive_constructors env kn mib i mip =
  let (ind,u), ctx = Universes.fresh_inductive_instance env (kn,i) in
  let ar = Inductive.type_of_inductive env ((mib,mip),u) in
  let nm = String.capitalize (Names.Id.to_string (mip.mind_typename)) in
  let types = arities_of_constructors env ((kn,i),u) in
  Array.iter (fun x -> msg_info (str "Constructor signature : " ++ Printer.pr_constr x)) types;
  let constrs = Array.map (extract_type (Some (kn,i)) true [] env) types in
  state := { !state with
             st_inductives =
               Indmap.modify
                 (kn,i)
                 (fun _ a -> { a with ind_constypes = constrs })
                 !state.st_inductives;
             st_inductives_list = (kn,i) :: !state.st_inductives_list
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
  let cout = open_out "OUT.hs" in
  let ft = Format.formatter_of_out_channel cout in
  pp_with ft (
    str "{-# LANGUAGE GADTs, RankNTypes, DataKinds, PolyKinds, TypeFamilies, ScopedTypeVariables #-}" ++ fnl () ++
    str "{-# LANGUAGE MultiParamTypeClasses, FlexibleInstances, FlexibleContexts #-}" ++ fnl () ++
    str "{-# LANGUAGE TemplateHaskell, UndecidableInstances, EmptyCase #-}" ++ fnl () ++
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
    str "  fromSing :: Sing k x -> k" ++ fnl () ++ fnl () ++
    str "$(do TH.reportWarning \"Typechecked Sing\"; P.return [])" ++ fnl () ++ fnl () ++

    str "data instance Sing (Sing k x) y where" ++ fnl () ++
    str "  SSing :: forall (y :: Sing k x). Sing k x -> Sing (Sing k x) y" ++ fnl () ++
    str "$(do TH.reportWarning \"Typechecked SSing\"; P.return [])" ++ fnl () ++
    str "type instance ToSing (y :: Sing k x) = 'SSing y" ++ fnl () ++
    str "type instance FromSing ('SSing y) = y" ++ fnl () ++ 
    str "instance SingKind (Sing k x) where" ++ fnl () ++
    str "  fromSing (SSing x) = x" ++ fnl () ++ fnl () ++

    List.fold_right (fun i acc -> acc ++ pr_hs_ind (Indmap.find i !state.st_inductives)) (!state.st_inductives_list) (mt ()));
  close_out cout

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
