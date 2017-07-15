

Require Import
  Coq.Lists.List
  Coq.Setoids.Setoid
  Coq.Vectors.Fin
  Coq.Vectors.VectorDef
  Coq.Vectors.VectorSpec
  Coq.Logic.JMeq
  Coq.Arith.Lt
  Coq.Arith.EqNat
  Coq.Arith.PeanoNat
  Coq.Arith.Peano_dec
.

Require Import HaskellExtraction.HaskellExtraction.

Fixpoint x t := match t with tt => tt end.

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
  , unit nat plus
.
