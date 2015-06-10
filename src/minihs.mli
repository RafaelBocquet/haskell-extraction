
open Pp

module Empty : sig
    type t
    val absurd : t -> 'a
  end

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



                                  
type (_, _) eq = Refl : ('a, 'a) eq
val fold_var_sing : ('a -> 'b) -> 'c -> ('b -> 'c -> 'c) -> 'a var_sing -> 'c
val int_of_var_sing : 'a var_sing -> int
val var_try_lift : 'a var_sing -> 'b var_sing -> 'b hs_type -> 'a hs_type option
val var_dec_eq : 'a var_sing -> 'b var_sing -> ('a, 'b) eq option
                                                        
val is_unlifted_kind : 'a hs_kind -> bool
                                                        
val map_type : ('a -> 'b) -> 'a hs_type -> 'b hs_type
val lift_type : 'a hs_type -> 'a option hs_type
val subst_type : ('a -> 'b hs_type) -> 'a hs_type -> 'b hs_type
val subst_type1 : 'a hs_type -> 'a option hs_type -> 'a hs_type
val simpl_type : 'a hs_type -> 'a hs_type

val sing_of : ('b option -> 'a option hs_type) -> 'b hs_kind -> 'a option hs_type
val constructor_signature : 'a hs_type -> any_hs_constructor_signature

val pr_hs_name : hs_name -> std_ppcmds
val pr_hs_type : 'a hs_type -> std_ppcmds
val pr_hs_kind : 'a hs_kind -> std_ppcmds
val pr_hs_ind_simple : 'a hs_ind -> std_ppcmds
val pr_hs_ind_sing : 'a hs_ind -> std_ppcmds
val pr_hs_ind_g : 'a hs_ind -> std_ppcmds
