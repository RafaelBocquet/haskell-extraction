
open Pp
open Hutil
open Names
open Graph

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
               ; "Sing"; "ToSing"; "FromSing"; "TyArr"; "TyFun"; "TyPi"
               ]
type 'a hs_type =
  | TyStar
  | TyVar of 'a
  | TyApp of 'a hs_type * 'a hs_type
  | TyForall of 'a hs_kind * 'a option hs_type
  | TyArrow of 'a hs_type * 'a hs_type
  | TyConst of hs_name
  | TyKind of 'a hs_kind
  | TyToSing of 'a hs_type
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
  | KToSing of 'a hs_kind
  | KFromSing of 'a hs_kind
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
  | Any_equation : 'b svar * 'b hs_kind list * 'b hs_kind -> 'a any_hs_equation
and hs_name =
  | Hs_dataname of inductive
  | Hs_sdataname of inductive
  | Hs_tfname of string
  | Hs_symbolname of string
  | Hs_constrname of constructor
  | Hs_sconstrname of constructor
  | Hs_pconstrname of constructor
  | Hs_psconstrname of constructor
  | Hs_ssconstrname of constructor
  | Hs_ename of string
and hs_ind =
  { ind_name : inductive
  ; ind_printname : string
  ; ind_signature : Empty.t any_hs_kind_signature
  ; ind_consnames : string array
  ; ind_constypes : Empty.t hs_type array
  ; ind_sconstypes : Empty.t hs_type array
  ; ind_consarities : bool list array
  }
and any_hs_type_family_signature =
  | Any_type_family_signature : 'a svar * ('a -> 'a hs_kind) * 'a hs_kind -> any_hs_type_family_signature
and hs_type_family =
  { tf_name      : string
  ; tf_signature : any_hs_type_family_signature option
  ; tf_closed    : bool
  ; tf_equations : Empty.t any_hs_equation array
  }
and ('a, 'b) hs_expr =
  | EVar of 'a
  | EStar
  | EApp of ('a, 'b) hs_expr * ('a, 'b) hs_expr
  | EFunapp of ('a, 'b) hs_expr * ('a, 'b) hs_expr
  | EAbs of 'b hs_type option * ('a option, 'b) hs_expr
  | EForall of 'b hs_kind option * ('a, 'b option) hs_expr
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
and 'a any_lifted_svar =
  | Any_lifted_var : 'b svar * ('a -> 'b) * 'b list -> 'a any_lifted_svar
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

let rec lift_var_by : type a. a svar -> a list -> int -> a any_lifted_svar =
  fun v l -> function
    | 0 -> Any_lifted_var (v, id, l)
    | n ->
      let Any_lifted_var (v', f, l) = lift_var_by (V_next v) (None :: List.map some l) (n-1) in
      Any_lifted_var (v', (fun x -> f (some x)), l)

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
  type t = T : 'a svar * ('a -> 'a hs_kind) * 'a hs_kind * 'a option hs_kind -> t
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

module StringOrdered = struct
  type t = string
  let compare = Pervasives.compare
end
module Stringset = Set.Make(StringOrdered)
module Stringmap = CMap.Make(StringOrdered)

module TfOrdered = struct
  type t = string * string
  let compare = Pervasives.compare
end
module Tfmap = CMap.Make(TfOrdered)



type hs_elem =
  | Hs_ind of inductive
  | Hs_sind of inductive
  | Hs_const of Constant.t
  | Hs_ssconstr of constructor
  | Hs_symbol of string
  | Hs_typefamily of string
  | Hs_tyarr of string
  | Hs_typi of string
type state =
  { st_list : hs_elem list
  ; st_inductives : hs_ind Indmap.t
  ; st_constants : hs_constant Names.Cmap.t
  ; st_symbols : hs_symbol Stringmap.t
  ; st_typefamilies : hs_type_family Stringmap.t
  ; st_tyarrs : hs_type_family Stringmap.t
  ; st_typis : hs_type_family Stringmap.t
  ; st_ssconstrs : hs_constant Constrmap.t
  ; st_defunctionalise_map : any_hs_kind DefunMap.t
  ; st_defunctionalise_const_map : hs_name Namemap.t

  ; st_defined_datanames : Stringset.t
  ; st_defined_constrnames : Stringset.t
  ; st_defined_functionnames : Stringset.t

  ; st_reductions : (hs_name * bool list) Namemap.t (* stupid : if A -> B in reductions, A a b c ... @@@/@@ x -> A a b c ... x  *)
  }
let empty_state =
  { st_list = []
  ; st_inductives = Indmap.empty
  ; st_constants = Cmap.empty
  ; st_symbols = Stringmap.empty
  ; st_typefamilies = Stringmap.empty
  ; st_tyarrs = Stringmap.empty
  ; st_typis = Stringmap.empty
  ; st_ssconstrs = Constrmap.empty
  ; st_defunctionalise_map = DefunMap.empty
  ; st_defunctionalise_const_map = Namemap.empty

  ; st_defined_datanames = Stringset.of_list keywords
  ; st_defined_constrnames = Stringset.of_list keywords
  ; st_defined_functionnames = Stringset.of_list keywords

  ; st_reductions = Namemap.empty
  }
let state = ref empty_state

let find_dataname s =
  let rec find_dataname' i =
    let n = s ^ Option.cata string_of_int "" i in
    let i' = Some (Option.cata ((+) 1) 0 i) in
    if Stringset.mem n !state.st_defined_datanames
    then find_dataname' i'
    else n
  in
  let n = find_dataname' None in
  state := { !state with st_defined_datanames = Stringset.add n !state.st_defined_datanames };
  n

let find_constrname s =
  let rec find_constrname' i =
    let n = s ^ Option.cata string_of_int "" i in
    let i' = Some (Option.cata ((+) 1) 0 i) in
    if Stringset.mem n !state.st_defined_constrnames
    then find_constrname' i'
    else n
  in
  let n = find_constrname' None in
  state := { !state with st_defined_constrnames = Stringset.add n !state.st_defined_constrnames };
  n

let find_functionname s =
  let rec find_functionname' i =
    let n = s ^ Option.cata string_of_int "" i in
    let i' = Some (Option.cata ((+) 1) 0 i) in
    if Stringset.mem n !state.st_defined_functionnames
    then find_functionname' i'
    else n
  in
  let n = find_functionname' None in
  state := { !state with st_defined_functionnames = Stringset.add n !state.st_defined_functionnames };
  n

let ids = let open Sequence in
  let r = map Char.chr (Char.code 'a' -- Char.code 'z') in
  ref (filter (fun s -> not ( Stringset.mem s !state.st_defined_datanames
                              || Stringset.mem s !state.st_defined_constrnames
                              || Stringset.mem s !state.st_defined_functionnames
                            ))
         (map string_of_list
            (concat (iterate
                       (flat_map (fun s -> map (fun a -> a :: s) r))
                       (singleton [])))))

let tids = let open Sequence in
  let r = map Char.chr (Char.code 'A' -- Char.code 'Z') in
  ref (filter (fun s -> not ( Stringset.mem s !state.st_defined_datanames
                              || Stringset.mem s !state.st_defined_constrnames
                              || Stringset.mem s !state.st_defined_functionnames
                            ))
         (map string_of_list
            (concat (iterate
                       (flat_map (fun s -> map (fun a -> a :: s) r))
                       (singleton [])))))
let mk_id () = ids := Sequence.drop 1 !ids; Sequence.head_exn (!ids)
let mk_tid () = tids := Sequence.drop 1 !tids; Sequence.head_exn (!tids)


module ElemOrdered = struct
  type t = hs_elem
  let compare = Pervasives.compare
  let hash _ = 0
  let equal = function
    | Hs_ind a -> (function
        | Hs_ind b -> Names.eq_ind a b
        | _ -> false
      )
    | Hs_sind a -> (function
        | Hs_sind b -> Names.eq_ind a b
        | _ -> false
      )
    | Hs_const a -> (function
        | Hs_const b -> Names.Constant.equal a b
        | _ -> false
      )
    | Hs_symbol a -> (function
        | Hs_symbol b -> a = b
        | _ -> false
      )
    | Hs_typefamily a -> (function
        | Hs_typefamily b -> a = b
        | _ -> false
      )
    | Hs_tyarr a -> (function
        | Hs_tyarr b -> a = b
        | _ -> false
      )
    | Hs_typi a -> (function
        | Hs_typi b -> a = b
        | _ -> false
      )
    | Hs_ssconstr a -> (function
        | Hs_ssconstr b -> Names.eq_constructor a b
        | _ -> false
      )
end
module Elemset = Set.Make(ElemOrdered)

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
  | KToSing k -> KToSing (map_kind f k)
  | KFromSing k -> KFromSing (map_kind f k)
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
  | TyToSing k -> TyToSing (map_type f k)
  | TyKind k -> TyKind (map_kind f k)
  | TyUnknown -> TyUnknown

let rec map_expr : type a b c d. (a -> b) -> (c -> d) -> (a, c) hs_expr -> (b, d) hs_expr = fun f g -> function
  | EStar -> EStar
  | EVar x -> EVar (f x)
  | EApp (a, b) -> EApp (map_expr f g a, map_expr f g b)
  | EFunapp (a, b) -> EFunapp (map_expr f g a, map_expr f g b)
  | EAbs (k, a) -> EAbs (Option.map (map_type g) k, map_expr (Option.map f) g a)
  | EForall (k, a) -> EForall (Option.map (map_kind g) k, map_expr f (Option.map g) a)
  | EUnknown -> EUnknown
  | EConst n -> EConst n
  | ECase (a, p) -> ECase (map_expr f g a, Array.map (map_case f g) p)
and map_case : type a b c d. (a -> b) -> (c -> d) -> (a, c) hs_match -> (b, d) hs_match = fun f g -> function
  | Any_match (p, e) -> Any_match (p, map_expr (Either.map_left f) g e)

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
let kind_fun_application f args = List.fold_left (fun x y -> KFunapp (x, y)) f args
let expr_application f args = List.fold_left (fun x y -> EApp (x, y)) f args
let expr_fun_application f args = List.fold_left (fun x y -> EFunapp (x, y)) f args

let rec view_type_signature : type a b. a hs_type -> a any_hs_signature =
  fun ty -> match ty with
    | TyStar | TyVar _ | TyConst _ | TyApp _ | TyKind _ | TyUnknown | TySing _ | TyToSing _ ->
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
    | TyStar | TyVar _ | TyConst _ | TyApp _ | TyUnknown | TyForall _ | TyKind _ | TySing _ | TyToSing _ ->
      [], ty
let rec view_type_application' : type a. a hs_type -> a hs_type list -> a hs_type * a hs_type list =
  fun ty acc -> match ty with
    | TyApp (a, b) ->
      view_type_application' a (b :: acc)
    | TyStar | TyVar _ | TyConst _ | TyArrow _ | TyUnknown | TyForall _ | TyKind _ | TySing _ | TyToSing _ ->
       ty, acc
and view_type_application : type a. a hs_type -> a hs_type * a hs_type list =
  fun ty -> view_type_application' ty []

let rec view_kind_application' : type a. a hs_kind -> a hs_kind list -> a hs_kind * a hs_kind list =
  fun k acc -> match k, acc with
    | KApp (a, b), _ ->
      view_kind_application' a (b :: acc)
    | _ -> k, acc
and view_kind_application : type a. a hs_kind -> a hs_kind * a hs_kind list =
  fun k -> view_kind_application' k []

let rec view_kind_fun_application' : type a. a hs_kind -> a hs_kind list -> a hs_kind * a hs_kind list =
  fun k acc -> match k, acc with
    | KFunapp (a, b), _ ->
      view_kind_fun_application' a (b :: acc)
    | _ -> k, acc
and view_kind_fun_application : type a. a hs_kind -> a hs_kind * a hs_kind list =
  fun k -> view_kind_fun_application' k []

let rec type_arity : type a. a hs_type -> int = fun t ->
  let Any_signature s = view_type_signature t in
  List.length (fst (view_type_arrow (signature_last s)))


let rec reduce_kind : type a. a hs_kind -> a hs_kind =
  fun k ->
    let k, bs = view_kind_fun_application k in
    let k, cs = view_kind_application k in
    reduce_kind' k cs bs
and reduce_kind' : type a. a hs_kind -> a hs_kind list -> a hs_kind list -> a hs_kind =
  fun k bs cs -> match k, cs with
    | KConst s, c :: cs ->
      (try let n, l = Namemap.find s !state.st_reductions in
         reduce_kind' (KConst n) (List.map snd (List.filter fst (List.combine l (bs @ [c])))) cs
       with Not_found -> kind_fun_application (kind_application k bs) (c :: cs)
      )
    | _ -> kind_fun_application (kind_application k bs) cs

and mk_constant : type a b. hs_name -> a svar -> (a -> bool) -> (a -> a hs_kind) -> (a, b) hs_kind_signature -> bool * hs_name * a hs_kind =
  fun n v es vs -> function
    | KSig_empty k     -> true, n, k
    | KSig_next (k, s) ->
      let na = mk_tid () and nb = mk_tid () in
      let imp, n', k' = mk_constant n (V_next v) (Option.cata es true) (extend_kind_list (lift_kind k) vs) s in
      let vl = List.rev (fold_right_svar (fun x -> KVar x) cons v []) in
      let vl' = List.rev (fold_right_svar (fun x -> es x, KVar x) (fun (b, x) xs -> if b || not imp then x :: xs else xs) v []) in
      let ar = List.rev (fold_right_svar (fun x -> es x) (fun b xs -> if b || not imp then true :: xs else false :: xs) v []) in
      let sb = Any_symbol (nb, V_next v, extend_kind_list (KArrow' (lift_kind k, KStar)) vs) in
      let tb = { tf_signature = None
               ; tf_name      = "(@@)"
               ; tf_closed    = false
               ; tf_equations = Array.make 1
                     (Any_equation ( V_next v
                                   , [ kind_application (KConst (Hs_symbolname nb))
                                         (List.map lift_kind vl)
                                     ; KVar None]
                                   , k'))
               } in
      let kb = kind_application (KConst (Hs_symbolname nb)) vl in
      let sa = Any_symbol (na, V_next v, extend_kind_list (KPi' (lift_kind k, lift_kind kb)) vs) in
      let ta = { tf_signature = None
               ; tf_name      = "(@@@)"
               ; tf_closed    = false
               ; tf_equations = Array.make 1
                     (Any_equation ( V_next v
                                   , [ kind_application
                                        (KConst (Hs_symbolname na))
                                        (List.map lift_kind vl)
                                     ; KVar None]
                                   , kind_application
                                       (KConst n')
                                        (List.map lift_kind vl' @ [KVar None])))
               } in
      msg_error (str na);
      state := { !state with
                 st_symbols =
                   Stringmap.add na sa
                     (Stringmap.add nb sb !state.st_symbols)
               ; st_typis =
                   Stringmap.add na ta !state.st_typis
               ; st_tyarrs =
                   Stringmap.add nb tb !state.st_tyarrs
               ; st_list =
                   Hs_symbol na :: Hs_typi na ::
                   Hs_symbol nb :: Hs_tyarr nb ::
                   !state.st_list
               ; st_reductions = Namemap.add (Hs_symbolname na) (n', ar @ [true]) !state.st_reductions
               };
      false,
      Hs_symbolname na,
      KPi (k, kb)

and defunctionalise : type a. a svar -> (a -> a hs_kind) -> a hs_type -> a hs_kind =
  fun v vs -> function
    | TyStar -> KStar
    | TyForall (k, a) -> KPi (k, defunctionalise_pi v vs k a)
    | TyVar v -> KVar v
    | TyApp (a, b) -> KFunapp (defunctionalise v vs a, defunctionalise v vs b)
    | TyKind k -> k
    | TyConst s -> KConst (defunctionalise_const s)
    | TySing (a, b) -> KSing (a, b)
    | TyToSing t -> KToSing (defunctionalise v vs t)
    | TyArrow (a, b) -> KArrow (defunctionalise v vs a, defunctionalise v vs b)
    | t -> msg_error (str "DEFUN : " ++ pr_hs_type t); KUnknown
and defunctionalise_match : type a. hs_ind -> a svar -> (a -> a hs_kind) -> a hs_kind -> a hs_kind -> a hs_kind -> a hs_kind array -> a hs_kind =
  fun ind v vs a at t bs ->
    let ta = mk_tid () in
    let vl = var_list v in
    let tf = { tf_signature = Some (Any_type_family_signature (V_next v, extend_kind_list (lift_kind at) vs, KFunapp (lift_kind t, KVar None)))
             ; tf_name      = ta
             ; tf_closed    = true
             ; tf_equations = Array.mapi
                   (fun i b ->
                      let Any_lifted_var (v', f, l) = lift_var_by v [] (List.length ind.ind_consarities.(i)) in
                      Any_equation
                        ( v'
                        , List.map (fun v -> KVar (f v)) vl
                          @ [ kind_application
                                (KConst (Hs_pconstrname (ind.ind_name, i)))
                                (List.map (fun v -> KVar v) l)
                            ]
                        , kind_fun_application (map_kind f b)
                            (List.map (fun v -> KVar v) l)
                        )
                   )
                   bs
             } in
      let k' = kind_application
          (KConst (Hs_tfname ta))
          (List.map (fun v -> KVar v) (List.rev vl)) in
    msg_error (str ta);
    state := { !state with
               st_typefamilies =
                 Stringmap.add ta tf !state.st_typefamilies
             ; st_list =
                 Hs_typefamily ta ::
                 !state.st_list
             }; KApp (k', a)

and defunctionalise_lambda : type a. a svar -> (a -> a hs_kind) -> a hs_kind -> a option hs_kind -> a option hs_kind -> a hs_kind =
  fun v vs k t a ->
    let na = mk_tid () in
    let vl = var_list v in
    let sa = Any_symbol (na, V_next v, Option.cata (rmap lift_kind vs) (lift_kind (KPi' (k, defunctionalise_pi v vs k (TyKind t))))) in
    let ta = { tf_signature = None
             ; tf_name      = "(@@@)"
             ; tf_closed    = false
             ; tf_equations = Array.make 1
                   (Any_equation (V_next v
                                 , [kind_application
                                      (KConst (Hs_symbolname na))
                                      (List.map (fun v -> KVar (Some v)) (List.rev vl))
                                   ; KVar None]
                                 , a))
             } in
      let k' = kind_application
          (KConst (Hs_symbolname na))
          (List.map (fun v -> KVar v) (List.rev vl)) in
    state := { !state with
               st_symbols =
                 Stringmap.add na sa !state.st_symbols
             ; st_typis =
                 Stringmap.add na ta !state.st_typis
             ; st_list =
                 Hs_symbol na :: Hs_typi na ::
                 !state.st_list
             }; k'
and defunctionalise_pi : type a. a svar -> (a -> a hs_kind) -> a hs_kind -> a option hs_type -> a hs_kind =
  fun v vs k a ->
    let a' = defunctionalise (V_next v) (extend_kind_list (lift_kind k) vs) a in
    try let Any_kind (v', k') = DefunMap.find (DefunOrdered.T (v, vs, k, a')) !state.st_defunctionalise_map in
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
                                   , [kind_application
                                        (KConst (Hs_symbolname nb))
                                        (List.map (fun v -> KVar (Some v)) (List.rev vl))
                                     ; KVar None]
                                   , a'))
               } in
      let k' = kind_application
          (KConst (Hs_symbolname nb))
          (List.map (fun v -> KVar v) (List.rev vl)) in
      state := { !state with
                 st_symbols =
                   Stringmap.add nb sb !state.st_symbols
               ; st_tyarrs =
                   Stringmap.add nb tb !state.st_tyarrs
               ; st_list =
                   Hs_symbol nb :: Hs_tyarr nb ::
                   !state.st_list
               ; st_defunctionalise_map =
                   DefunMap.add (DefunOrdered.T (v, vs, k, a')) (Any_kind (v, k')) !state.st_defunctionalise_map
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

and constructor_mk_econstant : Empty.t hs_kind -> hs_name -> bool list -> hs_constant =
  fun k n l -> { const_name = mk_id ()
               ; const_type = TyKind k
               ; const_expr = constructor_mk_econstant_expr (EConst n) l
               }
and constructor_mk_econstant_expr : type a b. (a, b) hs_expr -> bool list -> (a, b) hs_expr
  = fun e -> function
    | [] -> e
    | x :: xs -> EAbs (None, constructor_mk_econstant_expr (EApp (map_expr some id e, EVar None)) xs)

and constructor_mk_constant : type a. hs_name -> Empty.t hs_type -> hs_name =
  fun n ty ->
    let Any_signature s = view_type_signature ty in
    constructor_mk_constant_signature n V_empty Empty.absurd s
and constructor_mk_constant_signature : type a b. hs_name -> a svar -> (a -> a hs_kind) -> (a, b) hs_signature -> hs_name =
  fun n v vs -> function
    | Sig_empty t ->
      let xs, r = view_type_arrow t in
      let Any_kind_signature s = constructor_signature_arrow v vs xs r in
      let (_, n', _) = mk_constant n v (fun _ -> false) vs s in
      n'
    | Sig_next (k, t) -> constructor_mk_constant_signature n (V_next v) (extend_kind_list (lift_kind k) vs) t
and constructor_signature_arrow : type a. a svar -> (a -> a hs_kind) -> a hs_type list -> a hs_type -> a any_hs_kind_signature =
  fun v vs -> function
    | [] -> fun t ->
      Any_kind_signature (KSig_empty (defunctionalise v vs t))
    | x :: xs -> fun t ->
      let k = defunctionalise v vs x in
      (match constructor_signature_arrow (V_next v) (extend_kind_list KUnknown vs) (List.map lift_type xs) (lift_type t) with
       | Any_kind_signature s -> Any_kind_signature (KSig_next (k, s))
      )


and singleton_constructor : type a. a svar -> (a -> a hs_kind) -> a hs_type -> a hs_type -> a hs_type =
  fun v vs con ty ->
    let Any_signature s = view_type_signature ty in
    singleton_constructor_signature v vs con s
and singleton_constructor_signature : type a b. a svar -> (a -> a hs_kind) -> a hs_type -> (a, b) hs_signature -> a hs_type =
  fun v vs con -> function
    | Sig_empty t ->
      let xs, r = view_type_arrow t in
      singleton_constructor_arrow v vs con xs r
    | Sig_next (k, t) -> TyForall (k, singleton_constructor_signature (V_next v) (extend_kind_list (lift_kind k) vs) (lift_type con) t)
and singleton_constructor_arrow : type a. a svar -> (a -> a hs_kind) -> a hs_type -> a hs_type list -> a hs_type -> a hs_type =
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

and mk_var_names : type a. a svar -> (a -> std_ppcmds) = function
  | V_empty -> fun _ -> failwith "impossible"
  | V_next v -> Option.cata (mk_var_names v) (int (fold_left_svar (fun _ -> 1) (+) 0 v))

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
          let nms = fold_left_svar (fun x -> KVar x) (fun xs x -> x :: xs) [] ar in
          let nms' = List.map (fun n -> KToSing n) nms in
          Any_equation ( ar
                       , [ kind_application (KConst (Hs_pconstrname (ind.ind_name, i))) nms]
                       , kind_application (KConst (Hs_psconstrname (ind.ind_name, i))) nms')
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
          let nms = fold_left_svar (fun x -> KVar x) (fun xs x -> x :: xs) [] ar in
          let nms' = List.map (fun n -> KFromSing n) nms in
          Any_equation ( ar
                       , [ kind_application (KConst (Hs_psconstrname (ind.ind_name, i))) nms]
                       , kind_application (KConst (Hs_pconstrname (ind.ind_name, i))) nms')
        )
        ind.ind_constypes
  }

and fromsing_expr : hs_ind -> (Empty.t, Empty.t) hs_expr = fun ind ->
  EAbs ( None
       , ECase (EVar None
               , Array.mapi
                   (fun i t ->
                      let ar = type_arity t in
                      let Any_con_pattern (p, nms) = mk_con_pattern (Hs_sconstrname (ind.ind_name, i)) ar in
                      Any_match (PCon p
                                , expr_application
                                    (EConst (Hs_constrname (ind.ind_name, i)))
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
    | TyKind k -> str "{- KIND -} " ++ pr_hs_kind' par f k
    | TySing (k, a) -> pp_par par
                         (str "Sing" ++ spc () ++
                          pr_hs_kind' true f k ++ spc () ++
                          f a )
    | TyToSing k -> pp_par par
                     (str "ToSing" ++ spc () ++
                      pr_hs_type' true f k)
    | TyUnknown -> str "UNKNOWN"
and pr_hs_kind : type a. a hs_kind -> std_ppcmds = fun ty -> pr_hs_kind_par false ty
and pr_hs_kind_par : type a. bool -> a hs_kind -> std_ppcmds =
  fun par ty -> pr_hs_kind' par (fun _ -> str "UNBOUND_VAR") ty
and pr_hs_kind' : type a. bool -> (a -> std_ppcmds) -> a hs_kind -> std_ppcmds =
  fun par f k -> pr_hs_kind'' par f (reduce_kind k)
and pr_hs_kind'' : type a. bool -> (a -> std_ppcmds) -> a hs_kind -> std_ppcmds =
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
                         (str "TyFun" ++ spc () ++
                          pr_hs_kind' true f a ++ spc () ++
                          pr_hs_kind' true f b )
    | KArrow' (a, b) -> pp_par par
                          (str "TyFun'" ++ spc () ++
                           pr_hs_kind' true f a ++ spc () ++
                           pr_hs_kind' true f b )
    | KPi (k, a) -> pp_par par
                      (str "TyPi" ++ spc () ++
                       pr_hs_kind' true f k ++ spc () ++
                       pr_hs_kind' true f a )
    | KPi' (k, a) -> pp_par par
                       (str "TyPi'" ++ spc () ++
                        pr_hs_kind' true f k ++ spc () ++
                        pr_hs_kind' true f a )
    | KConst s -> pr_hs_name_par par s
    | KSing (a, b) -> pp_par par
                        (str "Sing" ++ spc () ++
                         pr_hs_kind' true f a ++ spc () ++
                         f b )
    | KFromSing k -> pp_par par
                       (str "FromSing" ++ spc () ++
                        pr_hs_kind' true f k)
    | KToSing k -> pp_par par
                     (str "ToSing" ++ spc () ++
                      pr_hs_kind' true f k)
    | KUnknown -> str "KUNKNOWN"
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
  | Hs_dataname i -> str (Indmap.find i !state.st_inductives).ind_printname
  | Hs_sdataname s -> str "Sing'"
  | Hs_symbolname s -> str s
  | Hs_tfname s -> str s
  | Hs_constrname (c, i) -> str (Indmap.find c !state.st_inductives).ind_consnames.(i)
  | Hs_sconstrname (c, i) -> str ("S" ^ (Indmap.find c !state.st_inductives).ind_consnames.(i))
  | Hs_pconstrname (c, i) -> str ("\'" ^ (Indmap.find c !state.st_inductives).ind_consnames.(i))
  | Hs_psconstrname (c, i) -> str ("\'S" ^ (Indmap.find c !state.st_inductives).ind_consnames.(i))
  | Hs_ssconstrname c -> str (Constrmap.find c !state.st_ssconstrs).const_name
  | Hs_ename s -> str s
and pr_hs_equation : 'a any_hs_equation -> std_ppcmds =
  fun (Any_equation (a, s, t)) ->
    let nms = mk_names a in
    prlist_with_sep spc (pr_hs_kind' true nms) s ++ spc () ++ str "=" ++ spc () ++ pr_hs_kind' false nms t
and pr_hs_type_family : hs_type_family -> std_ppcmds = fun tf ->
  let has_sig = Option.has_some tf.tf_signature in
  (match tf.tf_signature with
   | Some (Any_type_family_signature (v, f, k)) ->
     let g = mk_names v in
     h 0 (str "type family" ++ spc () ++
          pr_hs_name (Hs_tfname tf.tf_name) ++ spc () ++
          fold_left_svar (fun v ->
              pp_par true (g v ++
                           spc () ++ str "::" ++ spc () ++
                           pp_par false (pr_hs_kind' false g (f v)))
            ) (fun a b -> b ++ spc () ++ a) (mt ()) v ++
          spc () ++ str "::" ++ spc () ++ pr_hs_kind' false g k ++
          (if tf.tf_closed then spc () ++ str "where" else mt ())
         ) ++ fnl ()
   | None -> mt ()) ++
  (if has_sig && tf.tf_closed then fun x -> hov 2 (str "  " ++ x) else fun x -> x)
    (prvect_with_sep fnl (fun e ->
         hov 2
           ((if tf.tf_closed
             then mt ()
             else str "type instance"
            ) ++ spc () ++
            pr_hs_name (Hs_tfname tf.tf_name) ++ spc () ++
            pr_hs_equation e
           )) tf.tf_equations) ++ fnl ()
and pr_hs_expr : type a b. (a, b) hs_expr -> std_ppcmds = fun e -> pr_hs_expr_par false e
and pr_hs_expr_par : type a b. bool -> (a, b) hs_expr -> std_ppcmds =
  fun par e -> pr_hs_expr' par (fun _ -> str "UNBOUND_VAR") (fun _ -> str "UNBOUND TYPE VAR") e
and pr_hs_expr' : type a b. bool -> (a -> std_ppcmds) -> (b -> std_ppcmds) -> (a, b) hs_expr -> std_ppcmds =
  fun par f g -> function
    | EStar -> str "SStar"
    | EVar x -> f x
    | EFunapp (a, b) -> pp_par par (pr_hs_expr' false f g a ++ spc () ++ str "`unSLambda`" ++ spc () ++ pr_hs_expr' true f g b)
    | EApp (a, b) -> pp_par par (pr_hs_expr' false f g a ++ spc () ++ pr_hs_expr' true f g b)
    | EAbs (t, a) ->
      let n = mk_id () in
      pp_par par
        ( str "SLambda" ++ spc () ++
          pp_par true
            ((match t with
                | Some t -> str "\\(" ++ str n ++ spc () ++ str "::" ++ spc () ++ pr_hs_type' false g t ++ str ")"
                | None -> str "\\" ++ str n
              ) ++ spc () ++ str "->" ++ spc () ++ pr_hs_expr' false (Option.cata f (str n)) g a))
    | EForall (None, a) ->
      let n = mk_id () in
      pr_hs_expr' par f (Option.cata g (str n)) a
    | EForall (Some k, a) ->
      let fn = mk_id () and n = mk_id () in
      str "let {" ++ spc () ++ str fn ++
      spc () ++ str "::" ++ spc () ++
      str "Sing" ++ spc () ++ pr_hs_kind' true g k ++ str ";" ++ spc () ++
      str fn ++
      spc () ++ str "=" ++ spc () ++
      pr_hs_expr' false f (Option.cata g (str n)) a ++
      str "} in" ++ spc () ++ str fn
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
  h 0 (str "data" ++ spc () ++ pr_hs_name (Hs_dataname ind.ind_name) ++
       pr_any_hs_kind_signature ind.ind_signature ++ spc () ++ str "where" ++ fnl ()) ++
  hov 2 (str "  " ++
         prvecti_with_sep fnl (fun i c ->
             pr_hs_name (Hs_constrname (ind.ind_name, i)) ++
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
        | KSig_empty _ -> pr_hs_name (Hs_dataname ind.ind_name)
        | _ -> pp_par true (fold_left_kind_signature (fun _ -> str (mk_id ()))
                              (fun a b -> a ++ spc () ++ b) (pr_hs_name (Hs_dataname ind.ind_name)) s)) ++ spc () ++
       str (mk_id ()) ++ spc () ++
       str "where" ++ fnl ()
      ) ++
  hov 2 (str "  " ++
         prvecti_with_sep fnl (fun i c ->
             pr_hs_name (Hs_sconstrname (ind.ind_name, i)) ++
             spc () ++ str "::" ++ spc () ++
             hov 2 (ws 2 ++ pr_hs_type c)
           ) ind.ind_sconstypes
        ) ++ fnl ()
and pr_hs_singinstance : hs_ind -> std_ppcmds = fun ind ->
  let Any_kind_signature s = ind.ind_signature in
  h 0 (str "instance SingKind" ++ spc () ++
       (match s with
        | KSig_empty _ -> pr_hs_name (Hs_dataname ind.ind_name)
        | _ -> pp_par true (fold_left_kind_signature (fun _ -> str (mk_id ()))
                              (fun a b -> a ++ spc () ++ b) (pr_hs_name (Hs_dataname ind.ind_name)) s)) ++ spc () ++
       str "where"
      ) ++ fnl () ++
  hov 2 (str "  " ++
         str "fromSing = " ++ pr_hs_expr (fromsing_expr ind)
        ) ++ fnl ()
and pr_hs_constant : hs_constant -> std_ppcmds = fun cs ->
  hov 2 (pr_hs_name (Hs_ename cs.const_name) ++
         spc () ++ str "::" ++ spc () ++
         str "Sing'" ++ spc () ++
         pr_hs_type' true Empty.absurd cs.const_type
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
         v (pr_hs_name (Hs_symbolname n))
      ) ++ fnl ()
and pr_th_hack () = str "$(P.return [])" ++ fnl ()


let rec sort_elems : hs_elem list -> hs_elem list list = fun e ->
  let module G = struct
    module V = ElemOrdered
    type t = hs_elem list
    let iter_vertex = List.iter
    let iter_succ f _ e = Elemset.iter f (elem_succ e)
  end in
  let module C = Components.Make(G) in
  C.scc_list e
and elem_succ : hs_elem -> Elemset.t = function
  | Hs_ind i ->
    (try ind_succ i (Indmap.find i !state.st_inductives)
     with Not_found -> failwith "TODO IND")
  | Hs_sind i ->
    (try sind_succ i (Indmap.find i !state.st_inductives)
     with Not_found -> failwith "TODO SIND")
  | Hs_const n ->
    (try const_succ (Cmap.find n !state.st_constants)
    with Not_found -> failwith "TODO CONSTANT")
  | Hs_symbol s ->
    (try let Any_symbol (a, v, vs) = Stringmap.find s !state.st_symbols in
       fold_left_svar vs (fun a k -> Elemset.union a (kind_succ k)) Elemset.empty v
     with Not_found -> failwith "TODO SYMBOL")
  | Hs_typefamily a ->
    (try let tf = Stringmap.find a !state.st_typefamilies in
       typefamily_succ tf
     with Not_found -> msg_error (str a); failwith "TODO TF")
  | Hs_tyarr a ->
    (try let tf = Stringmap.find a !state.st_tyarrs in
       typefamily_succ tf
     with Not_found -> failwith "TODO ARR")
  | Hs_typi a ->
    (try let tf = Stringmap.find a !state.st_typis in
       typefamily_succ tf
     with Not_found -> failwith "TODO PI")
  | Hs_ssconstr a ->
    (try const_succ (Constrmap.find a !state.st_ssconstrs)
     with Not_found -> failwith "TODO PI")
and typefamily_succ : hs_type_family -> Elemset.t = fun tf ->
  Elemset.union
    (Option.cata (fun (Any_type_family_signature (v, f, k)) ->
         fold_left_svar (rmap kind_succ f) Elemset.union (kind_succ k) v
       ) Elemset.empty tf.tf_signature)
    (Array.fold_left Elemset.union Elemset.empty
       (Array.map equation_succ tf.tf_equations))
and const_succ c =
  Elemset.union
    (type_succ c.const_type)
    (expr_succ c.const_expr)
and expr_succ : type a b. (a, b) hs_expr -> Elemset.t = function
  | EStar | EUnknown | EVar _ -> Elemset.empty
  | EApp (a, b) | EFunapp (a, b) -> Elemset.union (expr_succ a) (expr_succ b)
  | EAbs (t, a) -> Elemset.union (Option.cata type_succ Elemset.empty t) (expr_succ a)
  | EForall (k, a) -> Elemset.union (Option.cata kind_succ Elemset.empty k) (expr_succ a)
  | ECase (a, m) -> Elemset.union (expr_succ a)
                      (Array.fold_left Elemset.union Elemset.empty (Array.map match_succ m))
  | EConst n -> name_succ n
and match_succ : type a b. (a, b) hs_match -> Elemset.t = function
  | Any_match (p, e) -> Elemset.union (pattern_succ p) (expr_succ e)
and pattern_succ : type a. a hs_pattern -> Elemset.t = function
  | PAny -> Elemset.empty
  | PCon c -> con_pattern_succ c
and con_pattern_succ : type a. a hs_con_pattern -> Elemset.t = function
  | PC_empty c -> name_succ c
  | PC_next (c, p) -> Elemset.union (con_pattern_succ c) (pattern_succ p)
and equation_succ (Any_equation (_, b, c)) =
  Elemset.union (List.fold_left Elemset.union Elemset.empty (List.map kind_succ b))
    (kind_succ c)
and name_succ = function
  | Hs_dataname n -> Elemset.singleton (Hs_ind n)
  | Hs_sdataname n -> Elemset.singleton (Hs_sind n)
  | Hs_tfname a -> Elemset.singleton (Hs_typefamily a)
  | Hs_symbolname n -> Elemset.singleton (Hs_symbol n)
  | Hs_constrname n | Hs_pconstrname n -> Elemset.singleton (Hs_ind (fst n))
  | Hs_sconstrname n | Hs_psconstrname n | Hs_ssconstrname n -> Elemset.singleton (Hs_sind (fst n))
  | Hs_ename _ -> failwith ""
and type_succ : type a. a hs_type -> Elemset.t = function
  | TyStar | TyVar _ | TyUnknown ->  Elemset.empty
  | TyApp (a, b) | TyArrow (a, b) ->  Elemset.union (type_succ a) (type_succ b)
  | TyForall (a, b) ->  Elemset.union (kind_succ a) (type_succ b)
  | TyConst n ->  name_succ n
  | TyToSing t -> type_succ t
  | TyKind k | TySing (k, _) ->  kind_succ k
and kind_succ : type a. a hs_kind -> Elemset.t = fun k -> kind_succ' (reduce_kind k)
and kind_succ' : type a. a hs_kind -> Elemset.t = function
  | KStar | KUnknown | KVar _ -> Elemset.empty
  | KApp (a, b)
  | KArrow (a, b) | KArrow' (a, b) ->  Elemset.union (kind_succ a) (kind_succ b)
  | KFunapp (a, b) ->
    Elemset.union
      (Elemset.union (kind_succ a) (kind_succ b))
      (match view_kind_application a with
       | KConst (Hs_symbolname s), _ -> Elemset.singleton (Hs_typi s)
       | _ -> Elemset.empty
      )
  | KPi' (a, b) | KPi (a, b) ->
    Elemset.union
      (Elemset.union (kind_succ a) (kind_succ b))
      (match view_kind_application b with
       | KConst (Hs_symbolname s), _ -> Elemset.singleton (Hs_tyarr s)
       | _ -> Elemset.empty
      )
  | KSing (k, _) | KFromSing k | KToSing k ->  kind_succ k
  | KConst s ->  name_succ s
and kind_signature_succ : type a b. (a, b) hs_kind_signature -> Elemset.t = function
  | KSig_empty k -> kind_succ k
  | KSig_next (k, s) -> Elemset.union (kind_succ k) (kind_signature_succ s)
and ind_succ : inductive -> hs_ind -> Elemset.t = fun i ind ->
  let Any_kind_signature s = ind.ind_signature in
  Elemset.union (kind_signature_succ s)
    (Array.fold_left Elemset.union Elemset.empty (Array.map type_succ ind.ind_constypes))
and sind_succ : inductive -> hs_ind -> Elemset.t = fun i ind ->
  let Any_kind_signature s = ind.ind_signature in
  Elemset.add (Hs_ind i)
    (Array.fold_left Elemset.union Elemset.empty (Array.map type_succ ind.ind_sconstypes))

