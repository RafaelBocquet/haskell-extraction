
open Pp
open Hutil
open Names

module InductiveOrdered = struct
  type t = inductive
  let compare = ind_ord
end
module Indset = Set.Make(InductiveOrdered)
module Indmap = CMap.Make(InductiveOrdered)

let string_of_list l =
  let l' = ref ('0'::List.rev l) in
  String.init (List.length l) (fun _ -> l' := List.tl !l'; List.hd !l')
let keywords = [ "if"; "of"; "in"; "do"
               ; "then" ; "else"; "case"
               ; "while"
               ; "fromSing" ; "sing"
               ; "Sing"; "ToSing"; "FromSing"; "TyArr"; "TyPi"
               ; "T"
               ]
let ids = let open Sequence in
  let r = map Char.chr (Char.code 'a' -- Char.code 'z') in
  ref (filter (fun s -> not (List.mem s keywords))
         (map string_of_list
            (concat (iterate
                       (flat_map (fun s -> map (fun a -> a :: s) r))
                       (singleton [])))))

let tids = let open Sequence in
  let r = map Char.chr (Char.code 'A' -- Char.code 'Z') in
  ref (filter (fun s -> not (List.mem s keywords))
         (map string_of_list
            (concat (iterate
                       (flat_map (fun s -> map (fun a -> a :: s) r))
                       (singleton [])))))
let mk_id () = ids := Sequence.drop 1 !ids; Sequence.head_exn (!ids)
let mk_tid () = tids := Sequence.drop 1 !tids; Sequence.head_exn (!tids)

type 'a hs_type =
  | TyStar
  | TyVar of 'a
  | TyApp of 'a hs_type * 'a hs_type
  | TyForall of 'a hs_kind * 'a option hs_type
  | TyArrow of 'a hs_type * 'a hs_type
  | TyConst of hs_name
  | TyKind of 'a hs_kind
  | TySing of 'a hs_kind * 'a
  | TyUnknown
and 'a hs_kind =
  | KStar
  | KVar of 'a
  | KApp of 'a hs_kind * 'a hs_kind
  | KFunapp of 'a hs_kind * 'a hs_kind
  | KPi of 'a hs_kind * 'a hs_kind
  | KPi' of 'a hs_kind * 'a hs_kind
  | KArrow of 'a hs_kind * 'a hs_kind
  | KArrow' of 'a hs_kind * 'a hs_kind
  | KConst of hs_name
  | KSing of 'a hs_kind * 'a
  | KUnknown
and any_hs_kind =
  | Any_kind : 'a svar * 'a hs_kind -> any_hs_kind
and ('a, 'b) hs_signature =
  | Sig_empty : 'b hs_type -> ('b, 'b) hs_signature
  | Sig_next : 'a hs_kind * ('a option, 'b) hs_signature -> ('a, 'b) hs_signature
and 'a any_hs_signature =
  | Any_signature : ('a, 'b) hs_signature -> 'a any_hs_signature
and ('a, 'b) hs_kind_signature =
  | KSig_empty : 'b hs_kind -> ('b, 'b) hs_kind_signature
  | KSig_next : 'a hs_kind * ('a option, 'b) hs_kind_signature -> ('a, 'b) hs_kind_signature
and 'a any_hs_kind_signature =
  | Any_kind_signature : ('a, 'b) hs_kind_signature -> 'a any_hs_kind_signature
and 'a any_hs_equation =
  | Any_equation : 'b svar * 'b hs_type list * 'b hs_type -> 'a any_hs_equation
and hs_name =
  | Hs_dataname of string
  | Hs_sdataname of string
  | Hs_constrname of string
  | Hs_sconstrname of string
  | Hs_pconstrname of string
  | Hs_psconstrname of string
  | Hs_ename of string
and hs_ind =
  { ind_name : string
  ; ind_signature : Empty.t any_hs_kind_signature
  ; ind_consnames : string array
  ; ind_constypes : Empty.t hs_type array
  ; ind_consarities : bool list array
  }
and hs_type_family =
  { tf_name      : string
  ; tf_signature : Empty.t any_hs_kind_signature option
  ; tf_closed    : bool
  ; tf_equations : Empty.t any_hs_equation array
  }
and ('a, 'b) hs_expr =
  | EVar of 'a
  | EApp of ('a, 'b) hs_expr * ('a, 'b) hs_expr
  | EAbs of 'b hs_type option * ('a option, 'b) hs_expr
  | EForall of ('a, 'b option) hs_expr
  | ECase of ('a, 'b) hs_expr * ('a, 'b) hs_match array
  | EConst of hs_name
  | EUnknown
and ('a, 'b) hs_match =
  | Any_match : 'c hs_pattern * (('a, 'c) Either.t, 'b) hs_expr -> ('a, 'b) hs_match
and _ hs_pattern =
  | PAny : unit hs_pattern
  | PCon : 'c hs_con_pattern -> 'c hs_pattern
and _ hs_con_pattern =
  | PC_empty : hs_name -> Empty.t hs_con_pattern
  | PC_next : 'c hs_con_pattern * 'd hs_pattern -> ('c, 'd) Either.t hs_con_pattern
and any_hs_con_pattern =
  | Any_con_pattern : 'c hs_con_pattern * 'c list -> any_hs_con_pattern
and hs_constant =
  { const_name : string
  ; const_type : Empty.t hs_type
  ; const_expr : (Empty.t, Empty.t) hs_expr
  }
and hs_symbol =
  | Any_symbol : string * 'a svar * ('a -> 'a hs_kind) -> hs_symbol
and 'a svar =
  | V_empty : Empty.t svar
  | V_next : 'a svar -> 'a option svar
and any_svar =
  | Any_var : 'a svar -> any_svar
and ('a, 'b) eq =
  | Refl : ('a, 'a) eq

let rec svar_dec_eq : type a b. a svar -> b svar -> (a, b) eq option = function
  | V_empty -> (function
      | V_empty -> Some Refl
      | V_next _ -> None
    )
  | V_next a -> (function
      | V_empty -> None
      | V_next b -> (match svar_dec_eq a b with
          | Some Refl -> Some Refl
          | None -> None
        )
    )

let rec svar_of_int : int -> any_svar = function
  | 0 -> Any_var V_empty
  | n -> let Any_var v = svar_of_int (n-1) in Any_var (V_next v)

let rec fold_left_svar : type a b c. (a -> b) -> (c -> b -> c) -> c -> a svar -> c =
  fun f g a -> function
    | V_empty -> a
    | V_next v -> fold_left_svar (fun x -> f (Some x)) g (g a (f None)) v

let rec fold_right_svar : type a b c. (a -> b) -> (b -> c -> c) -> a svar -> c -> c =
  fun f g -> function
    | V_empty -> fun a -> a
    | V_next v -> fun a -> g (f None) (fold_right_svar (fun x -> f (Some x)) g v a)

module DefunOrdered = struct
  type t = T : 'a svar * ('a -> 'a hs_kind) * 'a hs_kind * 'a option hs_type -> t
  let compare (T (a, b, c, d)) (T (a', b', c', d')) =
    (match svar_dec_eq a a' with
     | Some Refl -> Pervasives.compare (fold_right_svar b cons a [], c, d) (fold_right_svar b' cons a' [], c', d')
     | None -> Pervasives.compare (Any_var a) (Any_var a')
    )
end
module DefunMap = CMap.Make(DefunOrdered)

module NameOrdered = struct
  type t = hs_name
  let compare = Pervasives.compare
end
module Namemap = CMap.Make(NameOrdered)



type hs_elem =
  | Hs_ind of inductive
  | Hs_sind of inductive
  | Hs_const of Constant.t
  | Hs_symbol of hs_symbol
  | Hs_typefamily of hs_type_family
type state =
  { st_list : hs_elem list
  ; st_inductives : hs_ind Indmap.t
  ; st_constants : hs_constant Names.Cmap.t
  ; st_defunctionalise_map : any_hs_kind DefunMap.t
  ; st_defunctionalise_const_map : hs_name Namemap.t
  }
let empty_state =
  { st_list = []
  ; st_inductives = Indmap.empty
  ; st_constants = Cmap.empty
  ; st_defunctionalise_map = DefunMap.empty
  ; st_defunctionalise_const_map = Namemap.empty
  }
let state = ref empty_state

let rec map_kind : type a b. (a -> b) -> a hs_kind -> b hs_kind = fun f -> function
  | KStar -> KStar
  | KVar x -> KVar (f x)
  | KApp (a, b) -> KApp (map_kind f a, map_kind f b)
  | KFunapp (a, b) -> KFunapp (map_kind f a, map_kind f b)
  | KArrow (a, b) -> KArrow (map_kind f a, map_kind f b)
  | KArrow' (a, b) -> KArrow' (map_kind f a, map_kind f b)
  | KPi (k, a) -> KPi (map_kind f k, map_kind f a)
  | KPi' (k, a) -> KPi' (map_kind f k, map_kind f a)
  | KSing (k, a) -> KSing (map_kind f k, f a)
  | KConst s -> KConst s
  | KUnknown -> KUnknown

let rec map_type : type a b. (a -> b) -> a hs_type -> b hs_type = fun f -> function
  | TyStar -> TyStar
  | TyVar x -> TyVar (f x)
  | TyApp (a, b) -> TyApp (map_type f a, map_type f b)
  | TyArrow (a, b) -> TyArrow (map_type f a, map_type f b)
  | TyForall (k, a) -> TyForall (map_kind f k, map_type (Option.map f) a)
  | TyConst s -> TyConst s
  | TySing (k, a) -> TySing (map_kind f k, f a)
  | TyKind k -> TyKind (map_kind f k)
  | TyUnknown -> TyUnknown

let lift_kind : type a. a hs_kind -> a option hs_kind = fun ty -> map_kind (fun x -> Some x) ty
let lift_type : type a. a hs_type -> a option hs_type = fun ty -> map_type (fun x -> Some x) ty

let extend_kind_list : type a. a option hs_kind -> (a -> a hs_kind) -> (a option -> a option hs_kind) =
  fun k f -> Option.cata (fun x -> lift_kind (f x)) k


(* let rec bind_kind : type a b. (a -> b hs_kind) -> a hs_kind -> b hs_kind = fun f -> function *)
(*   | KStar -> KStar *)
(*   | KVar x -> f x *)
(*   | KApp (a, b) -> KApp (bind_kind f a, bind_kind f b) *)
(*   | KArrow (a, b) -> KArrow (bind_kind f a, bind_kind f b) *)
(*   | KPi (k, a) -> KPi (bind_kind f k, bind_kind f a) *)
(*   | KConst s -> KConst s *)
(*   | KUnknown -> KUnknown *)

(* let rec bind_type : type a b. (a -> b hs_type) -> a hs_type -> b hs_type = fun f -> function *)
(*   | TyStar -> TyStar *)
(*   | TyVar x -> f x *)
(*   | TyApp (a, b) -> TyApp (bind_type f a, bind_type f b) *)
(*   | TyArrow (a, b) -> TyArrow (bind_type f a, bind_type f b) *)
(*   | TyForall (k, a) -> TyForall (bind_kind f k, bind_type (Option.cata (fun x -> lift_type (f x)) (TyVar None)) a) *)
(*   | TyConst s -> TyConst s *)
(*   | TyUnknown -> TyUnknown *)

(* let subst_type : type a. a hs_type -> a option hs_type -> a hs_type = fun a b -> bind_type (Option.cata (fun x -> TyVar x) a) b *)

let rec signature_last : type a b. (a, b) hs_signature -> b hs_type = function
  | Sig_empty a -> a
  | Sig_next (_, a) -> signature_last a

let rec fold_left_kind_signature : type a b c z. (unit -> b) -> (a -> b -> a) -> a -> (c, z) hs_kind_signature -> a =
  fun f g a -> function
    | KSig_empty _ -> a
    | KSig_next (_, s) -> fold_left_kind_signature f g (g a (f ())) s

let rec fold_left_signature : type a b c z. (unit -> b) -> (a -> b -> a) -> a -> (c, z) hs_signature -> a =
  fun f g a -> function
    | Sig_empty _ -> a
    | Sig_next (_, s) -> fold_left_signature f g (g a (f ())) s

let rec map_signature : type a b. (b hs_type -> b hs_type) -> (a, b) hs_signature -> (a, b) hs_signature =
  fun f -> function
    | Sig_empty x -> Sig_empty (f x)
    | Sig_next (x, s) -> Sig_next (x, map_signature f s)

let rec lift_type_signature : type a b. (a, b) hs_signature -> a hs_type -> b hs_type = function
  | Sig_empty _ -> fun x -> x
  | Sig_next (_, s) -> fun x -> lift_type_signature s (lift_type x)

let type_application f args = List.fold_left (fun x y -> TyApp (x, y)) f args
let kind_application f args = List.fold_left (fun x y -> KApp (x, y)) f args
let expr_application f args = List.fold_left (fun x y -> EApp (x, y)) f args

let rec view_type_signature : type a b. a hs_type -> a any_hs_signature =
  fun ty -> match ty with
    | TyStar | TyVar _ | TyConst _ | TyApp _ | TyKind _ | TyUnknown | TySing _ ->
      Any_signature (Sig_empty ty)
    | TyArrow (a, b) ->
      let Any_signature sb = view_type_signature b in
      Any_signature (map_signature (fun b -> TyArrow (lift_type_signature sb a, b)) sb)
    | TyForall (k, a) ->
      let Any_signature sa = view_type_signature a in
      Any_signature (Sig_next (k, sa))

let rec view_type_arrow : type a. a hs_type -> a hs_type list * a hs_type =
  fun ty -> match ty with
    | TyArrow (a, b) ->
      let xs, l = view_type_arrow b in
      a :: xs, l
    | TyStar | TyVar _ | TyConst _ | TyApp _ | TyUnknown | TyForall _ | TyKind _ | TySing _ ->
      [], ty
let rec view_type_application' : type a. a hs_type -> a hs_type list -> a hs_type * a hs_type list =
  fun ty acc -> match ty with
    | TyApp (a, b) ->
      view_type_application' a (b :: acc)
    | TyStar | TyVar _ | TyConst _ | TyArrow _ | TyUnknown | TyForall _ | TyKind _ | TySing _ ->
       ty, acc
and view_type_application : type a. a hs_type -> a hs_type * a hs_type list =
  fun ty -> view_type_application' ty []

let rec type_arity : type a. a hs_type -> int = fun t ->
  let Any_signature s = view_type_signature t in
  List.length (fst (view_type_arrow (signature_last s)))

let rec mk_constant : type a b. hs_name -> a svar -> (a -> a hs_kind) -> (a, b) hs_kind_signature -> hs_name * a hs_kind =
  fun n v vs -> function
    | KSig_empty k     -> n, k
    | KSig_next (k, s) ->
      let na = mk_tid () and nb = mk_tid () in
      let n', k' = mk_constant n (V_next v) (extend_kind_list (lift_kind k) vs) s in
      let sb = Any_symbol (nb, V_next v, extend_kind_list (KArrow' (lift_kind k, KStar)) vs) in
      let tb = { tf_signature = None
               ; tf_name      = "(@@)"
               ; tf_closed    = false
               ; tf_equations = Array.make 1
                     (Any_equation ( V_next v
                                   , [ type_application (TyConst (Hs_dataname nb))
                                         (List.rev (fold_right_svar (fun x -> TyVar (Some x)) cons v []))
                                     ; TyVar None]
                                   , TyKind k'))
               } in
      let kb = kind_application (KConst (Hs_dataname nb))
          (List.rev (fold_right_svar (fun x -> KVar x) cons v [])) in
      let sa = Any_symbol (na, V_next v, extend_kind_list (KPi' (lift_kind k, lift_kind kb)) vs) in
      let ta = { tf_signature = None
               ; tf_name      = "(@@@)"
               ; tf_closed    = false
               ; tf_equations = Array.make 1
                     (Any_equation ( V_next v
                                   , [ type_application
                                        (TyConst (Hs_dataname na))
                                        (List.rev (fold_right_svar (fun x -> TyVar (Some x)) cons v []))
                                     ; TyVar None]
                                   , type_application
                                       (TyConst n')
                                        (List.rev (fold_right_svar (fun x -> TyVar x) cons (V_next v) []))))
               } in
      state := { !state with
                 st_list =
                   Hs_typefamily ta ::
                   Hs_symbol sa ::
                   Hs_typefamily tb ::
                   Hs_symbol sb ::
                   !state.st_list
               };
      Hs_dataname na,
      KPi (k, kb)

and defunctionalise : type a. a svar -> (a -> a hs_kind) -> a hs_type -> a hs_kind =
  fun v vs -> function
    | TyStar -> KStar
    | TyForall (k, a) -> KPi (k, defunctionalise_lambda v vs k a)
    | TyVar v -> KVar v
    | TyApp (a, b) -> KFunapp (defunctionalise v vs a, defunctionalise v vs b)
    | TyKind k -> k
    | TyConst s -> KConst (defunctionalise_const s)
    | TySing (a, b) -> KSing (a, b)
    | TyArrow (a, b) -> KArrow (defunctionalise v vs a, defunctionalise v vs b)
    | t -> msg_error (str "DEFUN : " ++ pr_hs_type t); KUnknown
and defunctionalise_lambda : type a. a svar -> (a -> a hs_kind) -> a hs_kind -> a option hs_type -> a hs_kind =
  fun v vs k a ->
    try let Any_kind (v', k') = DefunMap.find (DefunOrdered.T (v, vs, k, a)) !state.st_defunctionalise_map in
      (match svar_dec_eq v v' with
       | Some Refl -> k'
       | None -> failwith "impossible")
    with Not_found ->
      let nb = mk_tid () in
      let vl = var_list v in
      let sb = Any_symbol (nb, V_next v, Option.cata (rmap lift_kind vs) (KArrow' (lift_kind k, KStar))) in
      let tb = { tf_signature = None
               ; tf_name      = "(@@)"
               ; tf_closed    = false
               ; tf_equations = Array.make 1
                     (Any_equation (V_next v
                                   , [type_application
                                        (TyConst (Hs_dataname nb))
                                        (List.map (fun v -> TyVar (Some v)) (List.rev vl))
                                     ; TyVar None]
                                   , TyKind (defunctionalise (V_next v) (extend_kind_list KUnknown vs) a)))
               } in
      let k' = kind_application
          (KConst (Hs_dataname nb))
          (List.map (fun v -> KVar v) (List.rev vl)) in
      state := { !state with
                 st_list =
                   Hs_typefamily tb ::
                   Hs_symbol sb ::
                   !state.st_list
               ; st_defunctionalise_map =
                   DefunMap.add (DefunOrdered.T (v, vs, k, a)) (Any_kind (v, k'))
                     !state.st_defunctionalise_map
               }; k'
and defunctionalise_const : hs_name -> hs_name =
  fun n ->
    try Namemap.find n !state.st_defunctionalise_const_map
    with Not_found -> msg_error (str "No constant for : " ++ pr_hs_name n); failwith ""

and singletonise :  type a. a svar -> (a -> a hs_kind) -> a hs_type -> a hs_type =
  fun v vs ty ->
    let Any_signature s = view_type_signature ty in
    singletonise_signature v vs s
and singletonise_signature : type a b. a svar -> (a -> a hs_kind) -> (a, b) hs_signature -> a hs_type =
  fun v vs -> function
    | Sig_empty t ->
      let xs, r = view_type_arrow t in
      singletonise_arrow v vs xs r
    | Sig_next (KSing (k, k'), t) ->
      TyForall ( KSing (k, k')
               , TyArrow ( TySing (lift_kind k, Some k')
                         , singletonise_signature (V_next v) (extend_kind_list KUnknown vs) t))
    | Sig_next (k, t) ->
      TyForall ( k
               , TyArrow ( TySing (lift_kind k, None)
                         , singletonise_signature (V_next v) (extend_kind_list KUnknown vs) t))
and singletonise_arrow : type a b. a svar -> (a -> a hs_kind) -> a hs_type list -> a hs_type -> a hs_type =
  fun v vs -> function
    | [] -> fun t ->
      let r, xs = view_type_application t in
      type_application r (List.map (singletonise v vs) xs)
    | x :: xs -> fun t ->
      TyArrow (singletonise v vs x, singletonise_arrow v vs xs t)

and singleton_constructor : type a. a svar -> (a -> a hs_kind) -> a hs_type -> a hs_type -> a hs_type =
  fun v vs con ty ->
    let Any_signature s = view_type_signature ty in
    singleton_constructor_signature v vs con s
and singleton_constructor_signature : type a b. a svar -> (a -> a hs_kind) -> a hs_type -> (a, b) hs_signature -> a hs_type =
  fun v vs con -> function
    | Sig_empty t ->
      let xs, r = view_type_arrow t in
      singleton_constructor_arrow v vs con xs r
    | Sig_next (k, t) -> TyForall (k, singleton_constructor_signature (V_next v) (extend_kind_list KUnknown vs) (lift_type con) t)
and singleton_constructor_arrow : type a b. a svar -> (a -> a hs_kind) -> a hs_type -> a hs_type list -> a hs_type -> a hs_type =
  fun v vs con -> function
    | [] -> fun t ->
      (match view_type_application t with
       | TyConst (Hs_dataname h), _ -> TyApp (TyConst (Hs_sdataname h), con)
       | _ -> failwith ""
      )
    | x :: xs -> fun t ->
      (match defunctionalise v vs x with
       | KSing (k, k') ->
         TyForall (KSing (k, k'), TyArrow ( TySing (lift_kind k, Some k')
                                          , singleton_constructor_arrow (V_next v) (extend_kind_list KUnknown vs) (TyApp (lift_type con, TyVar None))
                                              (List.map lift_type xs) (lift_type t)))
       | k ->
         TyForall (k, TyArrow ( TySing (lift_kind k, None)
                              , singleton_constructor_arrow (V_next v) (extend_kind_list KUnknown vs) (TyApp (lift_type con, TyVar None))
                                  (List.map lift_type xs) (lift_type t)))
     )

and mk_con_pattern : hs_name -> int -> any_hs_con_pattern =
  fun nm -> function
    | 0 -> Any_con_pattern (PC_empty nm, [])
    | n -> let Any_con_pattern (p, l) = mk_con_pattern nm (n-1) in
      Any_con_pattern (PC_next (p, PAny), Either.Right () :: List.map Either.left l)

and var_list : type a. a svar -> a list = function
  | V_empty -> []
  | V_next v -> None :: List.map (fun x -> Some x) (var_list v)

and mk_names : type a. a svar -> (a -> std_ppcmds) = function
  | V_empty -> fun _ -> failwith "impossible"
  | V_next v -> Option.cata (mk_names v) (str (mk_id ()))

and mk_pattern_names : type a. a hs_pattern -> (a -> std_ppcmds) = function
  | PAny -> let n = mk_id () in fun () -> str n
  | PCon c -> mk_con_pattern_names c
and mk_con_pattern_names : type a. a hs_con_pattern -> (a -> std_ppcmds) = function
  | PC_empty n     -> Empty.absurd
  | PC_next (c, p) -> Either.either (mk_con_pattern_names c) (mk_pattern_names p)

and tosing_type_family : hs_ind -> hs_type_family = fun ind ->
  { tf_name      = "ToSing"
  ; tf_signature = None
  ; tf_closed    = false
  ; tf_equations =
      Array.mapi (fun i t ->
          let Any_var ar = svar_of_int (type_arity t) in
          let nms = fold_left_svar (fun x -> TyVar x) (fun xs x -> x :: xs) [] ar in
          let nms' = List.map (fun n -> TyApp (TyConst (Hs_dataname "ToSing"), n)) nms in
          Any_equation ( ar
                       , [ type_application (TyConst (Hs_pconstrname (ind.ind_consnames.(i)))) nms]
                       , type_application (TyConst (Hs_psconstrname ind.ind_consnames.(i))) nms')
        )
        ind.ind_constypes
  }

and fromsing_type_family : hs_ind -> hs_type_family = fun ind ->
  { tf_name      = "FromSing"
  ; tf_signature = None
  ; tf_closed    = false
  ; tf_equations =
      Array.mapi (fun i t ->
          let Any_var ar = svar_of_int (type_arity t) in
          let nms = fold_left_svar (fun x -> TyVar x) (fun xs x -> x :: xs) [] ar in
          let nms' = List.map (fun n -> TyApp (TyConst (Hs_dataname "FromSing"), n)) nms in
          Any_equation ( ar
                       , [ type_application (TyConst (Hs_psconstrname (ind.ind_consnames.(i)))) nms]
                       , type_application (TyConst (Hs_pconstrname ind.ind_consnames.(i))) nms')
        )
        ind.ind_constypes
  }

and fromsing_expr : hs_ind -> (Empty.t, Empty.t) hs_expr = fun ind ->
  EAbs ( None
       , ECase (EVar None
               , Array.mapi
                   (fun i t ->
                      let ar = type_arity t in
                      let Any_con_pattern (p, nms) = mk_con_pattern (Hs_sconstrname ind.ind_consnames.(i)) ar in
                      Any_match (PCon p
                                , expr_application
                                    (EConst (Hs_constrname ind.ind_consnames.(i)))
                                    (List.map
                                       (fun n ->
                                          EApp (EConst (Hs_ename "fromSing")
                                               , EVar (Either.Right n)))
                                       (List.rev nms))))
                   ind.ind_constypes
               ))

and pr_hs_type : type a. a hs_type -> std_ppcmds = fun ty -> pr_hs_type_par false ty
and pr_hs_type_par : type a. bool -> a hs_type -> std_ppcmds =
  fun par ty -> pr_hs_type' par (fun _ -> str "UNBOUND_VAR") ty
and pr_hs_type' : type a. bool -> (a -> std_ppcmds) -> a hs_type -> std_ppcmds =
  fun par f ty -> match view_type_signature ty with
    | Any_signature (Sig_empty ty') ->
      pr_hs_type_simple par f ty'
    | Any_signature s ->
      pp_par par
        (str "forall" ++ pr_hs_type_forall f s)
and pr_hs_type_simple : type a. bool -> (a -> std_ppcmds) -> a hs_type -> std_ppcmds =
  fun par f -> function
    | TyStar -> str "*"
    | TyVar x -> f x
    | TyApp (a, b) -> pp_par par
                        (pr_hs_type' false f a ++ spc () ++
                         pr_hs_type' true f b)
    | TyArrow (a, b) -> pp_par par
                          (pr_hs_type' true f a ++
                           spc () ++ str "->" ++ spc () ++
                           pr_hs_type' false f b)
    | TyForall (k, a) -> failwith "impossible"
    | TyConst s -> pr_hs_name_par par s
    | TyKind k -> pr_hs_kind' par f k
    | TySing (k, a) -> pp_par par
                         (str "Sing" ++ spc () ++
                          pr_hs_kind' true f k ++ spc () ++
                          f a ++ spc ())
    | TyUnknown -> str "UNKNOWN"
and pr_hs_kind : type a. a hs_kind -> std_ppcmds = fun ty -> pr_hs_kind_par false ty
and pr_hs_kind_par : type a. bool -> a hs_kind -> std_ppcmds =
  fun par ty -> pr_hs_kind' par (fun _ -> str "UNBOUND_VAR") ty
and pr_hs_kind' : type a. bool -> (a -> std_ppcmds) -> a hs_kind -> std_ppcmds =
  fun par f -> function
    | KStar -> str "*"
    | KVar x -> f x
    | KApp (a, b) -> pp_par par
                       (pr_hs_kind' false f a ++ spc () ++
                        pr_hs_kind' true f b)
    | KFunapp (a, b) -> pp_par par
                       (pr_hs_kind' false f a ++
                        spc () ++ str "@@@" ++ spc () ++
                        pr_hs_kind' true f b)
    | KArrow (a, b) -> pp_par par
                         (str "TyArr" ++ spc () ++
                          pr_hs_kind' true f a ++ spc () ++
                          pr_hs_kind' true f b ++ spc ())
    | KArrow' (a, b) -> pp_par par
                          (str "TyArr'" ++ spc () ++
                           pr_hs_kind' true f a ++ spc () ++
                           pr_hs_kind' true f b ++ spc ())
    | KPi (k, a) -> pp_par par
                      (str "TyPi" ++ spc () ++
                       pr_hs_kind' true f k ++ spc () ++
                       pr_hs_kind' true f a ++ spc ())
    | KPi' (k, a) -> pp_par par
                       (str "TyPi'" ++ spc () ++
                        pr_hs_kind' true f k ++ spc () ++
                        pr_hs_kind' true f a ++ spc ())
    | KConst s -> pr_hs_name_par par s
    | KSing (a, b) -> pp_par par
                        (str "Sing" ++ spc () ++
                         pr_hs_kind' true f a ++ spc () ++
                         f b ++ spc ())
    | KUnknown -> str "UNKNOWN"
and pr_hs_type_forall : type a b. (a -> std_ppcmds) -> (a, b) hs_signature -> std_ppcmds =
  fun f -> function
    | Sig_empty ty -> str "." ++ spc () ++ pr_hs_type' false f ty
    | Sig_next (k, s) ->
      let n = str (mk_id ()) in
      spc () ++ str "(" ++ n ++ spc () ++ str "::" ++ spc () ++
      pr_hs_kind' false f k ++ str ")" ++ pr_hs_type_forall (Option.cata f n) s
and pr_hs_kind_signature : type a b. (a, b) hs_kind_signature -> std_ppcmds =
  fun s -> pr_hs_kind_signature' (fun _ -> str "UNBOUND_VAR") s
and pr_hs_kind_signature' : type a b. (a -> std_ppcmds) -> (a, b) hs_kind_signature -> std_ppcmds =
  fun f -> function
    | KSig_empty ty -> spc () ++ str "::" ++ spc () ++ pr_hs_kind' false f ty
    | KSig_next (k, s) ->
      let n = str (mk_id ()) in
      spc () ++ str "(" ++ n ++ spc () ++ str "::" ++ spc () ++
      pr_hs_kind' false f k ++ str ")" ++ pr_hs_kind_signature' (Option.cata f n) s
and pr_any_hs_kind_signature : type a. a any_hs_kind_signature -> std_ppcmds = function
  | Any_kind_signature s -> pr_hs_kind_signature s
and pr_hs_name : hs_name -> std_ppcmds = fun n -> pr_hs_name_par false n
and pr_hs_name_par : type a. bool -> hs_name -> std_ppcmds = fun par -> function
  | Hs_dataname s -> str s
  | Hs_sdataname s -> str "Sing'"
  | Hs_constrname s -> str s
  | Hs_sconstrname s -> str ("S" ^ s)
  | Hs_pconstrname s -> str ("\'" ^ s)
  | Hs_psconstrname s -> str ("\'S" ^ s)
  | Hs_ename s -> str s
and pr_hs_equation : 'a any_hs_equation -> std_ppcmds =
  fun (Any_equation (a, s, t)) ->
    let nms = mk_names a in
    prlist_with_sep spc (pr_hs_type' true nms) s ++ spc () ++ str "=" ++ spc () ++ pr_hs_type' false nms t
and pr_hs_type_family : hs_type_family -> std_ppcmds = fun tf ->
  let has_sig = Option.has_some tf.tf_signature in
  (match tf.tf_signature with
   | Some s ->
     h 0 (str "type family" ++ spc () ++
          pr_hs_name (Hs_dataname tf.tf_name) ++ spc () ++
          pr_any_hs_kind_signature s ++
          (if tf.tf_closed then str "where" else mt ())
         ) ++ fnl ()
   | None -> mt ()) ++
  (if has_sig && tf.tf_closed then hov 2 else fun x -> x)
    (prvect_with_sep fnl (fun e ->
         hov 2
           ((if tf.tf_closed
             then str "type"
             else str "type instance"
            ) ++ spc () ++
            pr_hs_name (Hs_dataname tf.tf_name) ++ spc () ++
            pr_hs_equation e
           )) tf.tf_equations) ++ fnl ()
and pr_hs_expr : type a b. (a, b) hs_expr -> std_ppcmds = fun e -> pr_hs_expr_par false e
and pr_hs_expr_par : type a b. bool -> (a, b) hs_expr -> std_ppcmds =
  fun par e -> pr_hs_expr' par (fun _ -> str "UNBOUND_VAR") (fun _ -> str "UNBOUND TYPE VAR") e
and pr_hs_expr' : type a b. bool -> (a -> std_ppcmds) -> (b -> std_ppcmds) -> (a, b) hs_expr -> std_ppcmds =
  fun par f g -> function
    | EVar x -> f x
    | EApp (a, b) -> pp_par par (pr_hs_expr' false f g a ++ spc () ++ pr_hs_expr' true f g b)
    | EAbs (t, a) ->
      let n = mk_id () in
      pp_par par
        ((match t with
            | Some t -> str "\\(" ++ str n ++ spc () ++ str "::" ++ spc () ++ pr_hs_type' false g t ++ str ")"
            | None -> str "\\" ++ str n
          ) ++ spc () ++ str "->" ++ spc () ++ pr_hs_expr' false (Option.cata f (str n)) g a)
    | EForall a ->
      let n = mk_id () in
      pr_hs_expr' par f (Option.cata g (str n)) a
    | ECase (x, ps) ->
      pp_par par
        (str "case" ++ spc () ++
         pr_hs_expr' true f g x ++ spc () ++
         str "of" ++ spc () ++ str "{" ++ spc () ++
         prvect_with_sep (fun _ -> str ";" ++ spc ())
           (fun (Any_match (p, e)) ->
              let h = mk_pattern_names p in
              pr_hs_pattern' false h p ++
              spc () ++ str "->" ++ spc () ++
              pr_hs_expr' false (Either.either f h) g e
           )
           ps ++ spc () ++ str "}")
    | EConst n -> pr_hs_name_par par n
    | EUnknown -> str "P.undefined"
and pr_hs_pattern' : type a. bool -> (a -> std_ppcmds) -> a hs_pattern -> std_ppcmds =
  fun par f -> function
    | PAny -> f ()
    | PCon c -> pr_hs_con_pattern' par f c
and pr_hs_con_pattern' : type a. bool -> (a -> std_ppcmds) -> a hs_con_pattern -> std_ppcmds =
  fun par f -> function
    | PC_empty n -> pr_hs_name n
    | PC_next (c, p) -> pp_par par
                          (pr_hs_con_pattern' false (fun x -> f (Either.left x)) c ++ spc () ++
                           pr_hs_pattern' true (fun x -> f (Either.right x)) p)
and pr_hs_ind : hs_ind -> std_ppcmds = fun ind ->
  h 0 (str "data" ++ spc () ++ str ind.ind_name ++
       pr_any_hs_kind_signature ind.ind_signature ++ spc () ++ str "where" ++ fnl ()) ++
  hov 2 (str "  " ++
         prvecti_with_sep fnl (fun i c ->
             pr_hs_name (Hs_constrname ind.ind_consnames.(i)) ++
             spc () ++ str "::" ++ spc () ++
             hov 2 (ws 2 ++ pr_hs_type c)
           ) ind.ind_constypes
        ) ++ fnl ()
  (* FIXME : do not always apply FromSing or ToSing, to prevent several layers of Sing *)
  (* pr_hs_type_family (tosing_type_family ind) ++ fnl () ++ *)
  (* pr_hs_type_family (fromsing_type_family ind) ++ fnl () ++ *)
  (* pr_hs_singinstance ind ++ *)
and pr_hs_sing : hs_ind -> std_ppcmds = fun ind ->
  let Any_kind_signature s = ind.ind_signature in
  h 0 (str "data instance" ++ spc () ++ str "Sing" ++ spc () ++
       (match s with
        | KSig_empty _ -> str ind.ind_name
        | _ -> pp_par true (fold_left_kind_signature (fun _ -> str (mk_id ()))
                              (fun a b -> a ++ spc () ++ b) (str ind.ind_name) s)) ++ spc () ++
       str (mk_id ()) ++ spc () ++
       str "where" ++ fnl ()
      ) ++
  hov 2 (str "  " ++
         prvecti_with_sep fnl (fun i c ->
             pr_hs_name (Hs_sconstrname ind.ind_consnames.(i)) ++
             spc () ++ str "::" ++ spc () ++
             hov 2 (ws 2 ++ pr_hs_type (singleton_constructor V_empty Empty.absurd
                                          (TyConst (Hs_pconstrname ind.ind_consnames.(i)))
                                          c))
           ) ind.ind_constypes
        ) ++ fnl () ++
  pr_th_hack ()
and pr_hs_singinstance : hs_ind -> std_ppcmds = fun ind ->
  let Any_kind_signature s = ind.ind_signature in
  h 0 (str "instance SingKind" ++ spc () ++
       (match s with
        | KSig_empty _ -> str ind.ind_name
        | _ -> pp_par true (fold_left_kind_signature (fun _ -> str (mk_id ()))
                              (fun a b -> a ++ spc () ++ b) (str ind.ind_name) s)) ++ spc () ++
       str "where"
      ) ++ fnl () ++
  hov 2 (str "  " ++
         str "fromSing = " ++ pr_hs_expr (fromsing_expr ind)
        ) ++ fnl ()
and pr_hs_constant : hs_constant -> std_ppcmds = fun cs ->
  hov 2 (pr_hs_name (Hs_ename cs.const_name) ++
         spc () ++ str "::" ++ spc () ++ str "_" ++ spc () ++ str "=>" ++ spc () ++
         pr_hs_type cs.const_type
        ) ++ fnl () ++
  hov 2 (pr_hs_name (Hs_ename cs.const_name) ++
         spc () ++ str "=" ++ spc () ++
         pr_hs_expr cs.const_expr) ++ fnl () ++ fnl ()
and pr_hs_symbol : hs_symbol -> std_ppcmds = fun (Any_symbol (n, v, s)) ->
  let nm = mk_names v in
  h 0 (str "data" ++ spc () ++
       fold_right_svar
         (fun x -> pp_par true (nm x ++
                                spc () ++ str "::" ++ spc () ++
                                pr_hs_kind' false nm (s x)))
         (fun a b -> b ++ spc () ++ a)
         v (pr_hs_name (Hs_dataname n))
      ) ++ fnl ()
and pr_th_hack () = str "$(P.return [])" ++ fnl ()
