Require Import HaskellExtraction.HaskellExtraction.

Inductive list : Type -> Type :=
| nil : forall A, list A
| cons : forall A, A -> list A -> list A
.

Inductive fin : nat -> Type :=
| fZ : forall n, fin (S n)
| fS : forall n, fin n -> fin (S n)
.

Inductive vec : Type -> nat -> Type :=
| vnil : forall A, vec A 0
| vcons : forall A n, A -> vec A n -> vec A (S n)
.

Inductive hlist : list Type -> Type :=
| hnil : hlist (nil Type)
| hcons : forall A AS, A -> hlist AS -> hlist (cons Type A AS)
.

Inductive type := tyunit : type | tyarrow : type -> type -> type.

Inductive expr : list type -> type -> Type :=
| eapp : forall e a b, expr e (tyarrow a b) -> expr e a -> expr e b
| eabs : forall e a b, expr (cons type a e) b -> expr e (tyarrow a b)
.

Inductive cmp : forall A, A -> A -> Type :=
| LT : forall A (x y : A), cmp A x y
.

Hextraction nat list fin vec hlist type expr.

(* Hextraction Module Coq.Init.Datatypes *)

