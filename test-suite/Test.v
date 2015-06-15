Require Import HaskellExtraction.HaskellExtraction.

Require Import
  Coq.Lists.List
  Coq.Setoids.Setoid
  Coq.Vectors.Fin
  Coq.Vectors.VectorDef
  Coq.Vectors.VectorSpec
.

Hextraction Module
            Coq.Init.Notations
            Coq.Init.Datatypes
            (* Coq.Init.Logic *)
            (* Coq.Init.Logic_Type *)
            (* Coq.Init.Peano *)
            (* Coq.Init.Specif *)
            (* Coq.Init.Tactics *)
            (* Coq.Init.Wf *)
            (* Coq.Setoids.Setoid *)
            Coq.Vectors.Fin
            (* Coq.Vectors.VectorDef *)
            (* Coq.Vectors.VectorSpec *)
.
