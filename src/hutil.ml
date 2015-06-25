
open Pp
open Names
open Term
open Termops
open Environ
open Reduction
open Reductionops

let id x = x
let const x y = x
let cons x xs = x :: xs
let some x = Some x
let rmap f g = fun x -> f (g x)
let flip f x y = f y x

(* empty type *)
module Empty = struct
  type t = {e : 'a. 'a}
  let absurd {e} = e
end

(* either type *)
module Either = struct
  type ('a, 'b) t = Left of 'a | Right of 'b
  let either f g = function
    | Left a  -> f a
    | Right a -> g a
  let left x = Left x
  let right x = Right x
  let map_left f = function
    | Left x -> Left (f x)
    | Right y -> Right y
  let map_right f = function
    | Right x -> Right (f x)
    | Left y -> Left y
end

(* pretty *)
let pp_par p a = if p then str "(" ++ a ++ str ")" else a

(* option *)
let option_bind f = function
  | Some x -> f x
  | None -> None

let option_sequence l = List.fold_right (Option.lift2 (fun x xs -> x :: xs)) l (Some [])

(* map *)
let memoize_map (type a) (module M : CMap.S with type key = a) = fun f ->
  let m = ref M.empty in fun x ->
    msg_info (int (M.cardinal !m));
    try M.find x !m
    with Not_found ->
      let y = f x in
      m := M.add x y !m; M.find x !m

(* coq *)

let rec signature_view env c =
  match kind_of_term (whd_betadeltaiota env Evd.empty c) with
  | Prod (x, t, c) ->
    let args, ty = signature_view (push_rel (x,None,t) env) c in
    (env, t) :: args, ty
  | _ -> [], (env, c)

let rec abstraction_view env c =
  match kind_of_term (whd_betadeltaiota env Evd.empty c) with
  | Lambda (x, t, c) ->
    let args, ty = abstraction_view (push_rel (x,None,t) env) c in
    (env, t) :: args, ty
  | _ -> [], (env, c)

let rec application_view env c =
  match kind_of_term (whd_betadeltaiota env Evd.empty c) with
  | App (a, bs) ->
    let h, xs = application_view env a in
    h, xs @ Array.to_list bs
  | c -> c, []

let head_is_inductive df env c =
  Option.cata (fun ((kn,i) as df) -> match fst (application_view env c) with
      | Ind ((kn',i') as n, u) -> eq_ind n df
      | _ -> false
    ) false df
