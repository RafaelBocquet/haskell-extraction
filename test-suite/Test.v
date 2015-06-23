Require Import HaskellExtraction.HaskellExtraction.

Require Import
  Coq.Lists.List
  Coq.Setoids.Setoid
  Coq.Vectors.Fin
  Coq.Vectors.VectorDef
  Coq.Vectors.VectorSpec
  .

Hextraction
  Coq.Init.Logic
  Coq.Init.Logic_Type
  Coq.Init.Notations
  Coq.Init.Datatypes
  (* Coq.Init.Peano *)
  (* Coq.Init.Specif *)
  (* Coq.Init.Tactics *)
  Coq.Vectors.Fin
  (* Coq.Init.Wf *)
  (* Coq.Setoids.Setoid *)
  (* Coq.Vectors.VectorDef *)
  (* Coq.Vectors.VectorSpec *)
  ,
  id not FS_inj
.
