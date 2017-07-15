open Term
open Declarations
open Names
open Libnames
open Pp
open CErrors
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
open Feedback
open Hutil

type sexp = Atom of string
          | Sexp of sexp list

let rec pr_sexp = function
  | Atom s -> str s
  | Sexp ss -> str "(" ++ prlist_with_sep spc pr_sexp ss ++ str ")"

type state =
  { st_inds : sexp list Mindmap.t
  ; st_cons : sexp Cmap.t
  }
let empty_state = { st_inds = Mindmap.empty
                  ; st_cons = Cmap.empty
                  }
let state = ref empty_state
let reset () = state := empty_state

(* *)

let type_of env c = Retyping.get_type_of ~polyprop:true env Evd.empty (strip_outer_cast c)

let rec extract_constr ind genv env c =
  match kind_of_term (whd_all env Evd.empty c) with
  | Sort _ -> Atom "Type"
  | App (a, bs) ->
    snd (Array.fold_left
           (fun (a, a') b ->
              let b' = extract_constr ind genv env b in
              let ab = mkApp (a, [|b|]) in
              (ab, Sexp [Atom "App"; a'; b'; extract_constr ind genv env (type_of env ab)])
           )
           (a, extract_constr ind genv env a)
           bs
        )
  | Prod (x,t,c) ->
    let env' = push_rel_assum (x,t) env in
    Sexp [Atom "Prod"; extract_constr ind genv env t; extract_constr ind genv env' c]
  | Lambda (x,t,c) ->
    let env' = push_rel_assum (x,t) env in
    Sexp [Atom "Lambda"; extract_constr ind genv env t; extract_constr ind genv env' c]
  | Rel x -> Sexp [Atom "Var"; Atom (string_of_int x)]
  | Fix ((_, i), (c, d, e)) ->
    let env' = push_rec_types (c, d, e) env in
    Sexp [ Atom "Fix"
         ; Sexp (List.map2 (fun x y -> Sexp [x; y])
                   (Array.to_list (Array.map (extract_constr ind genv env) d))
                   (Array.to_list (Array.map (extract_constr ind genv env') e)))
         ; Atom (string_of_int i)
         ]
  | Case (ci, creturn, scrut, bs) ->
    extract_inductive genv (fst ci.ci_ind);
    Sexp [ Atom "Case"
         ; Sexp [Atom (MutInd.to_string (fst ci.ci_ind)); Atom (string_of_int (snd ci.ci_ind))]
         ; extract_constr ind genv env scrut
         ; extract_constr ind genv env creturn
         ; extract_constr ind genv env (Constr.mkApp (creturn,Array.of_list [scrut]))
         ; Sexp (Array.to_list (Array.map (extract_constr ind genv env) bs))
         ]
  | LetIn (x,u,t,c) ->
    let env' = push_rel_assum (x,t) env in
    Sexp [ Atom "Let"
         ; extract_constr ind genv env t
         ; extract_constr ind genv env' c
         ]
  | Ind ((n, i), _) when Option.cata (eq_mind n) false ind ->
    Sexp [Atom "Ind"; Atom (MutInd.to_string n); Atom (string_of_int i)]
  | Ind ((n, i), _) ->
    extract_inductive genv n;
    Sexp [Atom "Ind"; Atom (MutInd.to_string n); Atom (string_of_int i)]
  | Construct (((n, i), j), _) ->
    extract_inductive genv n;
    Sexp [Atom "Construct"; Atom (MutInd.to_string n); Atom (string_of_int i); Atom (string_of_int j)]
  | Const (c,_) ->
    extract_constant genv c;
    Sexp [Atom "Const"; Atom (Constant.to_string c)]
  | _ -> msg_error (Printer.pr_constr c); failwith "ex onstr"
and extract_signature' i genv env c =
  match kind_of_term (whd_betaiota Evd.empty c) with
  | Prod (x,t,c) ->
    let env' = push_rel_assum (x,t) env in
    let a, b = extract_signature' i genv env' c in
    extract_constr i genv env t :: a, b
  | _ -> [], extract_constr i genv env c
and extract_signature i genv env c = let a, b = extract_signature' i genv env c in Sexp [Sexp a; b]
and extract_constructor' i genv env c =
  match kind_of_term (whd_betaiota Evd.empty c) with
  | Prod (x,t,c) ->
    let env' = push_rel_assum (x,t) env in
    let a, b = extract_constructor' i genv env' c in
    extract_constr i genv env t :: a, b
  | _ -> [], extract_application i genv env c
and extract_constructor i genv env c = let a, b = extract_constructor' i genv env c in Sexp [Sexp a; b]
and extract_application' i genv env c =
  match kind_of_term (whd_betaiota Evd.empty c) with
  | App (f, bs) -> extract_constr i genv env f, List.map (extract_constr i genv env) (Array.to_list bs)
  | _ -> extract_constr i genv env c, []
and extract_application i genv env c = let a, b = extract_application' i genv env c in Sexp [a; Sexp b]
and extract_inductive env kn =
  if Mindmap.mem kn !state.st_inds
  then ()
  else begin
    let mib = Environ.lookup_mind kn env in
    let mips = Array.mapi (fun i mip ->
        let (ind, u), ctx = Universes.fresh_inductive_instance env (kn,i) in
        let co = mib.mind_finite = Decl_kinds.CoFinite in
        let ar = extract_signature None env env (Inductive.type_of_inductive env ((mib,mip),u)) in
        let types = arities_of_constructors env ((kn,i),u) in
        let cons = Array.mapi (fun i t -> Sexp [ Atom (Names.Id.to_string mip.mind_consnames.(i))
                                               ; extract_constructor (Some kn) env env t]) types in
        Sexp [Atom (Names.Id.to_string mip.mind_typename)
             ; Atom (if co then "Coinductive" else "Inductive")
             ; ar
             ; Sexp (Array.to_list cons)
             ]
      ) mib.mind_packets in
    state := { !state with st_inds = Mindmap.add kn (Array.to_list mips) !state.st_inds }
  end
and extract_constant env c =
  if Cmap.mem c !state.st_cons
  then ()
  else begin
    let cb = Environ.lookup_constant c env in
    let ce = extract_constr None env env (match cb.const_body with
        | Def a -> Mod_subst.force_constr a
        | OpaqueDef a -> Opaqueproof.force_proof (Environ.opaque_tables env) a
        | _ -> failwith ":("
      ) in
    state := { !state with st_cons = Cmap.add c ce !state.st_cons }
  end

let rec extract_module env r : unit =
  let meb = Modops.destr_nofunctor (lookup_module r env).mod_type in
  List.iter (function
      | (l, SFBmind _) -> extract_inductive env (MutInd.make2 r l)
      | (l, SFBconst _) -> extract_constant env (Constant.make2 r l)
      | (l, SFBmodule m) -> extract_module env m.mod_mp
      | _ -> ()
    ) meb

let locate_module r =
  let q = snd (qualid_of_reference r) in
  try Nametab.locate_module q
  with Not_found -> Nametab.error_global_not_found q

let locate_ref r =
  let q = snd (qualid_of_reference r) in
  try Smartlocate.global_with_alias r
  with Nametab.GlobalizationError _
     | UserError _
    -> Nametab.error_global_not_found q
let out () =
  msg_info (str "Writing output...");
  let cout = open_out "OUT.coc" in
  let ft = Format.formatter_of_out_channel cout in
  Format.pp_set_margin ft 120;
  pp_with ft (
    h 0
      (str "(" ++ fnl () ++
       Cmap.fold (fun k v acc ->
           acc ++ fnl () ++
           pr_sexp (Sexp [Atom "Constant"; Atom (Constant.to_string k); v])
         ) !state.st_cons (mt ()) ++
       Mindmap.fold (fun k v acc ->
           acc ++ fnl () ++
           pr_sexp (Sexp [Atom "Inductive"; Atom (MutInd.to_string k); Sexp v])
         ) !state.st_inds (mt ()) ++ fnl () ++
       str ")"
      ) ++ fnl ()
  );
  close_out cout

let extraction ms gs =
  reset ();
  let env = Global.env () in
  List.iter (fun r -> extract_module env (locate_module r)) ms;
  List.iter (fun r ->
      match locate_ref r with
      | IndRef (r, _) -> extract_inductive env r
      | ConstRef c -> extract_constant env c
      | _ -> ()
    ) gs;
  out ()
