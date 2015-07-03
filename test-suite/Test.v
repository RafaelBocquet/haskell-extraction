Require Import HaskellExtraction.HaskellExtraction.

Require Import
  Coq.Lists.List
  Coq.Setoids.Setoid
  Coq.Vectors.Fin
  Coq.Vectors.VectorDef
  Coq.Vectors.VectorSpec.

Fixpoint aaa n :=
  match n with      
    | O => O
    | S n => S (bbb n)
  end
with bbb n :=
       match n with
         | O => O
         | S n => S (aaa n)
       end.

Definition p1 n :=
  match n with
    | O => S O
    | S n => S (S n)
  end.

Definition p2 n b := match b with
                       | false => n
                       | true => S n
                     end.

Hextraction
  (* Coq.Init.Logic *)
  (* Coq.Init.Logic_Type *)
  (* Coq.Init.Notations *)
  (* Coq.Init.Datatypes *)
  (* Coq.Init.Peano *)
  (* Coq.Init.Specif *)
  (* Coq.Init.Tactics *)
  (* Coq.Vectors.Fin *)
  (* Coq.Init.Wf *) (* https://github.com/goldfirere/ghc/issues/15 *)
  (* Coq.Setoids.Setoid *)
  (* Coq.Vectors.VectorDef *)
  (* Coq.Vectors.VectorSpec *)
  , nat plus mult
.

