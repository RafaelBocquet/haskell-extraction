
open Pp

module Empty : sig
    type t
    val absurd : t -> 'a
  end = struct
    type t = ()
    let absurd _ = failwith "absurd"
  end
       
let id = ref 0
let mk_id () = incr id; "a" ^ string_of_int (!id - 1)

type 'a hs_type =
  | TyVar of 'a
  | TyArrow of 'a hs_type * 'a hs_type
  | TyApp of 'a hs_type * 'a hs_type
  | TyForall of Empty.t hs_kind * 'a option hs_type
  | TyConst of hs_name
  | TyUnknown
and 'a hs_kind =
  | KVar of 'a
  | KStar
  | KApp of 'a option hs_kind * 'a hs_kind
  | KArrow of 'a hs_kind * 'a hs_kind
  | KConst of 'a var_sing * hs_name * 'a option hs_type
  | KUnknown
and 'a hs_ind = {
    ind_name : string;
    ind_arity : 'a var_sing;
    ind_signature : 'a -> Empty.t hs_kind;
    ind_constructor_signatures : any_hs_constructor_signature array;
    ind_gconstructors : Empty.t hs_type array;
    ind_constructors : Empty.t hs_type array;
    ind_consnames : string array
  }
and any_hs_ind =
    Any_hs_ind : 'a hs_ind -> any_hs_ind
and any_hs_signature =
    Any_hs_signature : 'a var_sing * ('a -> Empty.t hs_kind) -> any_hs_signature
and 'c any_hs_constructor_signature' =
    Any_hs_constructor_signature' : 'a var_sing * 'b var_sing * ('a -> 'b hs_kind) * ('c hs_kind -> 'b hs_kind) -> 'c any_hs_constructor_signature'
and any_hs_constructor_signature =
    Any_hs_constructor_signature : 'a var_sing * 'b var_sing * ('a -> 'b hs_kind) -> any_hs_constructor_signature
and _ var_sing =
  | Var_empty : Empty.t var_sing
  | Var_next  : 'a var_sing -> 'a option var_sing
and hs_name =
  | Hs_dataname of string
  | Hs_gdataname of string
  | Hs_sdataname of string
  | Hs_constrname of string
  | Hs_pconstrname of string
  | Hs_sconstrname of string
  | Hs_gconstrname of string


let rec is_unlifted_kind : type s. s hs_kind -> bool = function
  | KVar v -> true (* TODO check *)
  | KStar -> true
  | KApp _ -> false
  | KArrow (a, b) -> is_unlifted_kind a && is_unlifted_kind b
  | KConst _ -> false
  | KUnknown -> false

let rec map_type : 'a 'b. ('a -> 'b) -> 'a hs_type -> 'b hs_type = fun f -> function
  | TyVar x -> TyVar (f x)
  | TyArrow (a, b) -> TyArrow (map_type f a, map_type f b)
  | TyApp (a, b) -> TyApp (map_type f a, map_type f b)
  | TyForall (k, ty) -> TyForall (k, map_type (Option.map f) ty)
  | TyConst s -> TyConst s
  | TyUnknown -> TyUnknown

let lift_type a = map_type (fun x -> Some x) a

let rec subst_type : 'a 'b. ('a -> 'b hs_type) -> 'a hs_type -> 'b hs_type = fun f -> function
  | TyVar x -> f x
  | TyArrow (a, b) -> TyArrow (subst_type f a, subst_type f b)
  | TyApp (a, b) -> TyApp (subst_type f a, subst_type f b)
  | TyForall (k, ty) -> TyForall (k, subst_type (Option.cata
                                                   (fun x -> map_type (fun x -> Some x) (f x))
                                                   (TyVar None)) ty)  
  | TyConst s -> TyConst s
  | TyUnknown -> TyUnknown

let subst_type1 ty = subst_type (Option.cata (fun x -> TyVar x) ty)

let rec map_kind : type a b. (a -> b) -> (a var_sing -> b var_sing) -> a hs_kind -> b hs_kind = fun f g -> function
  | KVar v -> KVar (f v)
  | KStar -> KStar
  | KApp (a, b) -> KApp (map_kind (Option.map f) (fun (Var_next x) -> Var_next (g x)) a, map_kind f g b)
  | KArrow (a, b) -> KArrow (map_kind f g a, map_kind f g b)
  | KConst (a, b, c) -> KConst (g a, b, map_type (Option.map f) c)
  | KUnknown -> KUnknown
let lift_kind : type a. a hs_kind -> a option hs_kind = fun x -> map_kind (fun x -> Some x) (fun x -> Var_next x) x

type _ type_view =
  | Type_view : 'a hs_type -> 'a type_view
  | Forall_view : Empty.t hs_kind * 'a option type_view -> 'a type_view

let rec fold_type_view : 'a. 'a type_view -> 'a hs_type = function
  | Type_view x -> x
  | Forall_view (k, x) -> TyForall (k, fold_type_view x)

let rec type_view : 'a. 'a hs_type -> 'a type_view = function
  | TyVar x -> Type_view (TyVar x)
  | TyArrow (a, b) -> Type_view (TyArrow (a, b))
  | TyApp (a, b) -> Type_view (TyApp (a, b))
  | TyForall (k, ty) -> Forall_view (k, type_view ty)
  | TyConst s -> Type_view (TyConst s)
  | TyUnknown -> Type_view TyUnknown

let rec type_view_arrow : 'a. 'a hs_type -> 'a type_view -> 'a type_view = fun a -> function
  | Type_view b -> Type_view (TyArrow (a, b))
  | Forall_view (k, b) -> Forall_view (k, type_view_arrow (lift_type a) b)

let rec simpl_type_view : 'a. 'a hs_type -> 'a type_view = function
  | TyVar x -> Type_view (TyVar x)
  | TyArrow (a, b) -> type_view_arrow (simpl_type a) (simpl_type_view b)
  | TyApp (a, b) -> Type_view (TyApp (simpl_type a, simpl_type b))
  | TyForall (k, ty) -> Forall_view (k, simpl_type_view ty)
  | TyConst s -> Type_view (TyConst s)
  | TyUnknown -> Type_view TyUnknown
and simpl_type : 'a. 'a hs_type -> 'a hs_type = fun x -> fold_type_view (simpl_type_view x)

type (_, _) eq = Refl : ('a, 'a) eq
(* let rec fold_var_sing : type a b c. (a -> b) -> c -> (b -> c -> c) -> a var_sing -> c = fun f c g -> function *)
(*   | Var_empty -> c *)
(*   | Var_next x -> g (f None) (fold_var_sing (fun x -> f (Some x)) c g x) *)
let rec fold_var_sing : type a b c. (a -> b) -> c -> (b -> c -> c) -> a var_sing -> c = fun f c g -> function
  | Var_empty -> c
  | Var_next x -> fold_var_sing (fun x -> f (Some x)) (g (f None) c) g x
let int_of_var_sing : type a. a var_sing -> int = fun a -> fold_var_sing (fun _ -> ()) 0 (fun _ c -> 1 + c) a
let rec var_try_lift' : type a b. a var_sing -> b var_sing -> (b -> a) option = fun x y -> match x, y with
  | _, Var_empty -> Some Empty.absurd
  | Var_empty, Var_next _ -> None
  | Var_next x, Var_next y -> Option.map Option.lift (var_try_lift' x y) 
let var_try_lift : type a b. a var_sing -> b var_sing -> b hs_type -> a hs_type option =
  fun x y t -> Option.map (fun f -> map_type f t) (var_try_lift' x y)
let rec var_dec_eq : type a b. a var_sing -> b var_sing -> (a, b) eq option = fun x y -> match x, y with
  | Var_empty, Var_empty -> Some Refl
  | Var_next x, Var_next y ->
     (match var_dec_eq x y with
      | Some Refl -> Some Refl
      | None -> None
     )
  | _ -> None

let rec sing_of : type a b. (b option -> a option hs_type) -> b hs_kind -> a option hs_type = fun f -> function
  | KVar v -> assert false 
  | KStar -> TyApp (TyConst (Hs_dataname "Proxy"), TyVar None)
  | KApp (a, b) -> sing_of (Option.cata f (sing_of f b)) a
  | KArrow _ -> assert false
  (* | KArrow (a, b) -> *)
  (*   TyForall (a, TyApp (TyApp (TyArrow, sing_of (fun _ -> TyVar None) a) *)
  (*                                       , sing_of (fun _ -> TyApp (lift_type (f None), TyVar None)) b)) *)
  | KConst (_, _, ty) -> subst_type f ty
  | KUnknown -> assert false
                        
let pp_par par st = if par then str "(" ++ st ++ str ")" else st

let pr_hs_name = function
  | Hs_dataname s   -> str s
  | Hs_sdataname s  -> str "Sing"
  | Hs_gdataname s  -> str ("G" ^ s)
  | Hs_constrname s -> str s
  | Hs_pconstrname s -> str ("\'" ^ s)
  | Hs_sconstrname s -> str ("S" ^ s)
  | Hs_gconstrname s -> str ("G" ^ s)
                       

let rec pr_hs_type' : type s. bool -> (s -> std_ppcmds) -> s hs_type -> std_ppcmds = fun par p ty ->
  let v = type_view ty in
  match v with
  | Type_view _  -> pr_hs_type_inner par p ty
  | Forall_view _ -> pp_par par (str "forall" ++ pr_hs_type_forall p v)
and pr_hs_type_forall : type s. (s -> std_ppcmds) -> s type_view -> std_ppcmds = fun p -> function
  | Type_view ty -> str "." ++ spc () ++ pr_hs_type_inner false p ty
  | Forall_view (k, v) ->
    let n = mk_id () in
    spc () ++ str "(" ++ str n ++ spc () ++ str "::" ++ spc () ++
    pr_hs_kind' false Empty.absurd k ++ str ")" ++
    pr_hs_type_forall (Option.cata p (str n)) v
and pr_hs_type_inner : type s. bool -> (s -> std_ppcmds) -> s hs_type -> std_ppcmds = fun par p -> function 
  | TyVar a -> p a
  | TyArrow (a, b) ->
    pp_par par (pr_hs_type' false p a ++ spc () ++ str "->" ++ spc () ++ pr_hs_type' false p b)
  | TyApp (a, b) ->
    pp_par par (pr_hs_type' false p a ++ spc () ++ pr_hs_type' true p b)
  | TyForall (k, t) ->
    let n = mk_id () in
    pp_par par (str "forall" ++ spc () ++
                str "(" ++ str n ++ spc () ++ str "::" ++ spc () ++ pr_hs_kind' false Empty.absurd k ++ str ")." ++ spc () ++
                pr_hs_type' false (Option.cata p (str n)) t
               )
  | TyConst s -> pr_hs_name s
  | TyUnknown -> str "({--})"
and pr_hs_kind' : type s. bool -> (s -> std_ppcmds) -> s hs_kind -> std_ppcmds = fun par p -> function
  | KVar v -> p v
  | KStar -> str "*"
  | KApp (a, b) ->
    pp_par par (pr_hs_kind' false (Option.cata p (pr_hs_kind' true p b)) a) ++ spc () ++ pr_hs_kind' true p b
  | KArrow (a, b) ->
    pp_par par (pr_hs_kind' false p a ++ spc () ++ str "->" ++ spc () ++ pr_hs_kind' false p b)
  | KConst (ar, n, _) -> pr_hs_name n
  | KUnknown -> str "BAD"
    
let pr_hs_type : type s. s hs_type -> std_ppcmds = fun t -> pr_hs_type' false (fun _ -> str "var") t
let pr_hs_kind : type s. s hs_kind -> std_ppcmds = fun k -> pr_hs_kind' false (fun _ -> str "var") k

let pr_hs_constructor_signature (Any_hs_constructor_signature (ar, vs, ks)) =
  fold_var_sing ks (mt ()) (fun k p -> pp_par true (pr_hs_kind k) ++ spc () ++ p) ar

let rec promote_type : type a b. a var_sing -> (b -> a hs_kind) -> b hs_type -> a hs_kind =
  fun x f -> function
    | TyVar x -> f x
    | TyArrow (a, b) -> KArrow ( promote_type x f a
                               , promote_type x f b)
    | TyApp (a, b) -> KApp ( promote_type (Var_next x) (fun x -> lift_kind (f x)) a
                           , promote_type x f b)
    | TyForall _ -> assert false
    | TyConst s -> KConst (x, s, TyConst s)
    | TyUnknown -> KUnknown

let rec constructor_signature' : type a b. b var_sing -> (a -> b hs_kind) -> a hs_type -> b any_hs_constructor_signature'
  = fun vs bs -> function
    | TyForall (KStar, a) ->
      let Any_hs_constructor_signature' (ar, vs', sg, p) =
        constructor_signature' (Var_next vs) (Option.cata (fun x -> lift_kind (bs x)) (KVar None)) a in
      Any_hs_constructor_signature' (Var_next ar, vs', Option.cata sg KUnknown, (fun x -> p (lift_kind x)))
    | TyForall (k, a) ->
      let Any_hs_constructor_signature' (ar, vs', sg, p) =
        constructor_signature' vs (Option.cata bs KUnknown) a in
      Any_hs_constructor_signature' (Var_next ar, vs', Option.cata sg KUnknown, p)
    | TyArrow (a, b) ->
      let Any_hs_constructor_signature' (ar, vs', sg, p) =
        constructor_signature' vs bs b in
      Any_hs_constructor_signature' (Var_next ar, vs', Option.cata sg (p (promote_type vs bs a)), p)
    | t -> Any_hs_constructor_signature' (Var_empty, vs, Empty.absurd, fun x -> x) (* , promote_type vs bs t) *)

let constructor_signature : type a. a hs_type -> any_hs_constructor_signature = fun ty ->
  let Any_hs_constructor_signature' (a, b, c, _) =
    constructor_signature' Var_empty (fun y -> assert false) ty in
  Any_hs_constructor_signature (a, b, c)
                                             
let rec pr_hs_signature_simple : type a. a var_sing -> (a -> Empty.t hs_kind) -> std_ppcmds = fun x f -> match x with
  | Var_empty -> mt ()
  | Var_next x ->
    let k = f None in
    (if is_unlifted_kind k
     then pp_par true (str (mk_id ()) ++ spc () ++ str "::" ++ spc () ++ pr_hs_kind (f None)) ++ spc ()
     else mt ()) ++ pr_hs_signature_simple x (fun x -> f (Some x))

let rec pr_hs_signature_sing : type a. a var_sing -> (a -> Empty.t hs_kind) -> std_ppcmds = fun x f -> match x with
  | Var_empty -> mt ()
  | Var_next x ->
    let k = f None in
    (if is_unlifted_kind k
     then pr_hs_kind' true Empty.absurd k ++ spc ()
     else mt ()) ++ pr_hs_signature_sing x (fun x -> f (Some x))

let rec pr_hs_signature : type a. a var_sing -> (a -> Empty.t hs_kind) -> std_ppcmds = fun x f -> match x with
  | Var_empty -> mt ()
  | Var_next x -> pp_par true (str (mk_id ()) ++ spc () ++ str "::" ++ spc () ++ pr_hs_kind (f None)) ++ spc () ++
                  pr_hs_signature x (fun x -> f (Some x))

let pr_hs_ind_simple { ind_name; ind_arity; ind_signature; ind_constructors; ind_consnames } =
  h 0 (str "data" ++ spc () ++ pr_hs_name (Hs_dataname ind_name) ++ spc () ++
         pr_hs_signature_simple ind_arity ind_signature ++
         str "where" ++ fnl ()) ++
  hov 2 (str "  " ++
         prvecti (fun i c -> pr_hs_name (Hs_constrname ind_consnames.(i)) ++
                             spc () ++ str "::" ++ spc () ++
                             hov 2 (ws 2 ++ pr_hs_type (simpl_type c)) ++ fnl ())
           ind_constructors
        ) ++ fnl ()


let pr_hs_ind_sing { ind_name; ind_arity; ind_signature; ind_constructors; ind_consnames } =
  str "genSingletons [''" ++ str ind_name ++ str "]" ++ fnl ()
  (* str "data" ++ spc () ++ pr_hs_name (Hs_sdataname ind_name) ++ spc () ++ *)
  (* pp_par true (str (mk_id ()) ++ spc () ++ str "::" ++ spc () ++ *)
  (*              str ind_name ++ spc () ++ pr_hs_signature_sing ind_arity ind_signature) ++ spc () ++ *)
  (* str "where" ++ fnl () ++ *)
  (* hov 2 (str "  " ++ *)
  (*        prvecti (fun i c -> str ("S" ^ ind_consnames.(i)) ++ *)
  (*                            spc () ++ str "::" ++ spc () ++ pr_hs_type (sing_constructor c) ++ fnl ()) *)
  (*          ind_constructors *)
  (*       ) ++ fnl () *)


let pr_hs_ind_g { ind_name; ind_arity; ind_signature; ind_gconstructors; ind_consnames } =
  h 0 (str "data" ++ spc () ++ pr_hs_name (Hs_gdataname ind_name) ++ spc () ++
       pr_hs_signature ind_arity ind_signature ++
       str "where" ++ fnl ()) ++
  hov 2 (str "  " ++
         prvecti (fun i c -> pr_hs_name (Hs_gconstrname ind_consnames.(i)) ++
                             spc () ++ str "::" ++ spc () ++
                             hov 2 (ws 2 ++ pr_hs_type (simpl_type c)) ++ fnl ())
           ind_gconstructors
        ) ++ fnl ()
