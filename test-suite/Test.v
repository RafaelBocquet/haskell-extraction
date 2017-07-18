

Require Import
  Coq.Lists.List
  Coq.Setoids.Setoid
  Coq.Vectors.Fin
  Coq.Vectors.VectorDef
  Coq.Vectors.VectorSpec
  Coq.Logic.JMeq
  Coq.Init.Nat
  Coq.Arith.Lt
  Coq.Arith.EqNat
  Coq.Arith.PeanoNat
  Coq.Arith.Peano_dec
.

Require Import HaskellExtraction.HaskellExtraction.

Inductive FIN : nat -> Type :=
| fZ : forall n, FIN (S n)
| fS : forall n, FIN n -> FIN (S n)
.

Inductive VEC (A:Type) : nat -> Type :=
| vZ : VEC A 0
| vS : forall n, A -> VEC A n -> VEC A (S n)
.

Inductive Elem (A:Type) : forall n, VEC A n -> A -> FIN n -> Type :=
| Here : forall n z zs, Elem A (S n) (vS _ _ z zs) z (fZ _)
| There : forall n z zs y x, Elem A n zs y x -> Elem A (S n) (vS _ _ z zs) y (fS _ x)
.

Hextraction
  (* Coq.Init.Logic *)
  (* Coq.Init.Notations *)
  (* Coq.Init.Datatypes *)
  (* Coq.Init.Nat *)
  (* Coq.Init.Peano *)
  (* Coq.Init.Logic_Type *)
  (* Coq.Init.Specif *)
  (* Coq.Init.Tactics *)
  (* Coq.Init.Wf *)
  (* Coq.Setoids.Setoid *)
  (* Coq.Logic.Decidable *)
  (* Coq.Arith.PeanoNat *)
  (* Coq.Arith.Peano_dec *)
  (* Coq.Arith.Lt *)
  (* Coq.Vectors.Fin *)
  (* Coq.Vectors.VectorDef *)
  (* Coq.Vectors.VectorSpec *)
, nat plus mult divmod FIN VEC
.
