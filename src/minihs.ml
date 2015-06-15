
open Pp
open Hutil

let string_of_list l =
  let l' = ref ('0'::l) in
  String.init (List.length l) (fun _ -> l' := List.tl !l'; List.hd !l')
let keywords = [ "if"; "of"; "in"; "do"
               ; "then" ; "else"; "case"
               ; "while"
               ]
let ids = let open Sequence in
  let r = map Char.chr (Char.code 'a' -- Char.code 'z') in
  ref (filter (fun s -> not (List.mem s keywords)) (map string_of_list (concat (iterate (flat_map (fun s -> map (fun a -> a :: s) r)) (singleton [])))))
let mk_id () = ids := Sequence.drop 1 !ids; Sequence.head_exn (!ids)

type 'a hs_type =
  | TyStar
  | TyVar of 'a
  | TyApp of 'a hs_type * 'a hs_type
  | TyForall of 'a hs_type * 'a option hs_type
  | TyArrow of 'a hs_type * 'a hs_type
  | TyConst of hs_name
  | TyUnknown
and ('a, 'b) hs_signature =
  | Sig_empty : 'b hs_type -> ('b, 'b) hs_signature
  | Sig_next : 'a hs_type * ('a option, 'b) hs_signature -> ('a, 'b) hs_signature
and 'a any_hs_signature =
  | Any_signature : ('a, 'b) hs_signature -> 'a any_hs_signature
and 'a any_hs_equation =
  | Any_equation : 'b svar * 'b hs_type list * 'b hs_type -> 'a any_hs_equation
and hs_name =
  | Hs_singname
  | Hs_dataname of string
  | Hs_sdataname of string
  | Hs_constrname of string
  | Hs_sconstrname of string
  | Hs_pconstrname of string
  | Hs_psconstrname of string
  | Hs_ename of string
and hs_ind =
  { ind_name : string
  ; ind_signature : Empty.t any_hs_signature
  ; ind_consnames : string array
  ; ind_constypes : Empty.t hs_type array
  }
and hs_type_family =
  { tf_name : string
  ; tf_signature : Empty.t any_hs_signature option
  ; tf_closed    : bool
  ; tf_equations : Empty.t any_hs_equation array
  }
and ('a, 'b) hs_expr =
  | EVar of 'a
  | EApp of ('a, 'b) hs_expr * ('a, 'b) hs_expr
  | EAbs of ('a option, 'b) hs_expr
  | ECase of ('a, 'b) hs_expr * ('a, 'b) hs_match array
  | EConst of hs_name
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
and 'a svar =
  | V_empty : Empty.t svar
  | V_next : 'a svar -> 'a option svar
and any_svar =
  | Any_var : 'a svar -> any_svar

let rec map_type : type a b. (a -> b) -> a hs_type -> b hs_type = fun f -> function
  | TyStar -> TyStar
  | TyVar x -> TyVar (f x)
  | TyApp (a, b) -> TyApp (map_type f a, map_type f b)
  | TyArrow (a, b) -> TyArrow (map_type f a, map_type f b)
  | TyForall (k, a) -> TyForall (map_type f k, map_type (Option.map f) a)
  | TyConst s -> TyConst s
  | TyUnknown -> TyUnknown

let lift_type : type a. a hs_type -> a option hs_type = fun ty -> map_type (fun x -> Some x) ty

let rec bind_type : type a b. (a -> b hs_type) -> a hs_type -> b hs_type = fun f -> function
  | TyStar -> TyStar
  | TyVar x -> f x
  | TyApp (a, b) -> TyApp (bind_type f a, bind_type f b)
  | TyArrow (a, b) -> TyArrow (bind_type f a, bind_type f b)
  | TyForall (k, a) -> TyForall (bind_type f k, bind_type (Option.cata (fun x -> lift_type (f x)) (TyVar None)) a)
  | TyConst s -> TyConst s
  | TyUnknown -> TyUnknown

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

let rec signature_last : type a b. (a, b) hs_signature -> b hs_type = function
  | Sig_empty a -> a
  | Sig_next (_, a) -> signature_last a

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
let expr_application f args = List.fold_left (fun x y -> EApp (x, y)) f args

let rec singleton_of : type a. a hs_type -> a option hs_type = function
  | ty -> TyApp (TyApp (TyConst Hs_singname, lift_type ty), TyVar None)

let rec view_type_signature : type a b. a hs_type -> a any_hs_signature =
  fun ty -> match ty with
    | TyStar | TyVar _ | TyConst _ | TyApp _ | TyUnknown ->
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
    | TyStar | TyVar _ | TyConst _ | TyApp _ | TyUnknown | TyForall _ ->
      [], ty
let rec view_type_application' : type a. a hs_type -> a hs_type list -> a hs_type * a hs_type list =
  fun ty acc -> match ty with
    | TyApp (a, b) ->
      view_type_application' a (b :: acc)
    | TyStar | TyVar _ | TyConst _ | TyArrow _ | TyUnknown | TyForall _ ->
       ty, acc
and view_type_application : type a. a hs_type -> a hs_type * a hs_type list =
  fun ty -> view_type_application' ty []

let rec type_arity : type a. a hs_type -> int = fun t ->
  let Any_signature s = view_type_signature t in
  List.length (fst (view_type_arrow (signature_last s)))

let rec singleton_constructor : type a. a hs_type -> a hs_type -> a hs_type =
  fun con ty ->
    let Any_signature s = view_type_signature ty in
    singleton_constructor_signature con s
and singleton_constructor_signature : type a b. a hs_type -> (a, b) hs_signature -> a hs_type =
  fun con -> function
    | Sig_empty t ->
      let xs, r = view_type_arrow t in
      singleton_constructor_arrow con xs r
    | Sig_next (k, t) -> TyForall (k, singleton_constructor_signature (lift_type con) t)
and singleton_constructor_arrow : type a b. a hs_type -> a hs_type list -> a hs_type -> a hs_type =
  fun con -> function
    | [] -> fun t ->
      let TyConst (Hs_dataname h), _ = view_type_application t in
      TyApp (TyConst (Hs_sdataname h), con)
    | x :: xs -> fun t ->
      TyForall (x, TyArrow (singleton_of x
                           , singleton_constructor_arrow (TyApp (lift_type con, TyVar None))
                               (List.map lift_type xs) (lift_type t)))

let rec mk_con_pattern : hs_name -> int -> any_hs_con_pattern =
  fun nm -> function
    | 0 -> Any_con_pattern (PC_empty nm, [])
    | n -> let Any_con_pattern (p, l) = mk_con_pattern nm (n-1) in
      Any_con_pattern (PC_next (p, PAny), Either.Right () :: List.map (fun x -> Either.Left x) l)

let rec mk_names : type a. a svar -> (a -> std_ppcmds) = function
  | V_empty -> fun _ -> failwith "impossible"
  | V_next v -> Option.cata (mk_names v) (str (mk_id ()))

let rec mk_pattern_names : type a. a hs_pattern -> (a -> std_ppcmds) = function
  | PAny -> let n = mk_id () in fun () -> str n
  | PCon c -> mk_con_pattern_names c
and mk_con_pattern_names : type a. a hs_con_pattern -> (a -> std_ppcmds) = function
  | PC_empty n     -> Empty.absurd
  | PC_next (c, p) -> Either.either (mk_con_pattern_names c) (mk_pattern_names p)

let rec tosing_type_family : hs_ind -> hs_type_family = fun ind ->
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

let rec fromsing_type_family : hs_ind -> hs_type_family = fun ind ->
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

let rec fromsing_expr : hs_ind -> (Empty.t, Empty.t) hs_expr = fun ind ->
  EAbs (ECase (EVar None
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

let rec pr_hs_type : type a. a hs_type -> std_ppcmds = fun ty -> pr_hs_type_par false ty
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
    | TyUnknown -> str "UNKNOWN"
and pr_hs_type_forall : type a b. (a -> std_ppcmds) -> (a, b) hs_signature -> std_ppcmds =
  fun f -> function
    | Sig_empty ty -> str "." ++ spc () ++ pr_hs_type' false f ty
    | Sig_next (k, s) ->
      let n = str (mk_id ()) in
      spc () ++ str "(" ++ n ++ spc () ++ str "::" ++ spc () ++
      pr_hs_type' false f k ++ str ")" ++ pr_hs_type_forall (Option.cata f n) s
and pr_hs_signature : type a b. (a, b) hs_signature -> std_ppcmds =
  fun s -> pr_hs_signature' (fun _ -> str "UNBOUND8VAR") s
and pr_hs_signature' : type a b. (a -> std_ppcmds) -> (a, b) hs_signature -> std_ppcmds =
  fun f -> function
    | Sig_empty ty -> spc () ++ str "::" ++ spc () ++ pr_hs_type' false f ty
    | Sig_next (k, s) ->
      let n = str (mk_id ()) in
      spc () ++ str "(" ++ n ++ spc () ++ str "::" ++ spc () ++
      pr_hs_type' false f k ++ str ")" ++ pr_hs_signature' (Option.cata f n) s
and pr_any_hs_signature : type a. a any_hs_signature -> std_ppcmds = function
  | Any_signature s -> pr_hs_signature s
and pr_hs_name : hs_name -> std_ppcmds = fun n -> pr_hs_name_par false n
and pr_hs_name_par : type a. bool -> hs_name -> std_ppcmds = fun par -> function
  | Hs_singname -> str "Sing"
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
          pr_any_hs_signature s ++
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
           )) tf.tf_equations)
and pr_hs_expr : type a b. (a, b) hs_expr -> std_ppcmds = fun e -> pr_hs_expr_par false e
and pr_hs_expr_par : type a b. bool -> (a, b) hs_expr -> std_ppcmds =
  fun par e -> pr_hs_expr' par (fun _ -> str "UNBOUND_VAR") e
and pr_hs_expr' : type a b. bool -> (a -> std_ppcmds) -> (a, b) hs_expr -> std_ppcmds =
  fun par f -> function
    | EVar x -> f x
    | EApp (a, b) -> pp_par par (pr_hs_expr' false f a ++ spc () ++ pr_hs_expr' true f b)
    | EAbs a ->
      let n = mk_id () in
      pp_par par (str "\\" ++ str n ++ spc () ++ str "->" ++ spc () ++ pr_hs_expr' false (Option.cata f (str n)) a)
    | ECase (x, ps) ->
      pp_par par
        (str "case" ++ spc () ++
         pr_hs_expr' true f x ++ spc () ++
         str "of" ++ spc () ++ str "{" ++ spc () ++
         prvect_with_sep (fun _ -> str ";" ++ spc ())
           (fun (Any_match (p, e)) ->
              let g = mk_pattern_names p in
              pr_hs_pattern' false g p ++
              spc () ++ str "->" ++ spc () ++
              pr_hs_expr' false (Either.either f g) e
           )
           ps ++ spc () ++ str "}")
    | EConst n -> pr_hs_name_par par n
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
       pr_any_hs_signature ind.ind_signature ++ spc () ++ str "where" ++ fnl ()) ++
  hov 2 (str "  " ++
         prvecti_with_sep fnl (fun i c ->
             pr_hs_name (Hs_constrname ind.ind_consnames.(i)) ++
             spc () ++ str "::" ++ spc () ++
             hov 2 (ws 2 ++ pr_hs_type c)
           ) ind.ind_constypes
        ) ++ fnl () ++
  pr_hs_sing ind ++
  pr_hs_type_family (tosing_type_family ind) ++ fnl () ++
  pr_hs_type_family (fromsing_type_family ind) ++ fnl () ++
  pr_hs_singinstance ind ++
  fnl ()
and pr_hs_sing : hs_ind -> std_ppcmds = fun ind ->
  let Any_signature s = ind.ind_signature in
  h 0 (str "data instance" ++ spc () ++
       pr_hs_name Hs_singname ++ spc () ++
       (match s with
        | Sig_empty _ -> str ind.ind_name
        | _ -> pp_par true (fold_left_signature (fun _ -> str (mk_id ()))
                              (fun a b -> a ++ spc () ++ b) (str ind.ind_name) s)) ++ spc () ++
       str (mk_id ()) ++ spc () ++
       str "where" ++ fnl ()
      ) ++
  hov 2 (str "  " ++
         prvecti_with_sep fnl (fun i c ->
             pr_hs_name (Hs_sconstrname ind.ind_consnames.(i)) ++
             spc () ++ str "::" ++ spc () ++
             hov 2 (ws 2 ++ pr_hs_type (singleton_constructor
                                          (TyConst (Hs_pconstrname ind.ind_consnames.(i)))
                                          c))
           ) ind.ind_constypes
        ) ++ fnl () ++
  str ("$(do TH.reportWarning \"Typechecked " ^ ind.ind_name ^ "\"; P.return [])") ++ fnl ()
and pr_hs_singinstance : hs_ind -> std_ppcmds = fun ind ->
  let Any_signature s = ind.ind_signature in
  h 0 (str "instance SingKind" ++ spc () ++
       (match s with
        | Sig_empty _ -> str ind.ind_name
        | _ -> pp_par true (fold_left_signature (fun _ -> str (mk_id ()))
                              (fun a b -> a ++ spc () ++ b) (str ind.ind_name) s)) ++ spc () ++
       str "where"
      ) ++ fnl () ++
  hov 2 (str "  " ++
         str "fromSing = " ++ pr_hs_expr (fromsing_expr ind)
        ) ++ fnl ()

