/-
Authors: Ze Yuan, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe v₁ v₂ u₁ u₂

open CategoryTheory CategoryTheory.Limits

noncomputable section

variable {C : Type u₁} [Category.{v₁} C]
variable {F : C ⥤ Cat}
variable [∀ S : C, HasColimitsOfShape (F.obj S) GrpCat]
variable [HasColimitsOfShape C GrpCat]

/- Lemma 2.7.11 is the `GrpCat` specialization of the canonical Grothendieck-construction
comparison isomorphism: taking the fiberwise colimit first and then the colimit over the base is
canonically isomorphic to taking the single colimit over all pairs `(S, U)`. -/
#check
  (fun fundamentalGroupDiagram : Grothendieck F ⥤ GrpCat ↦
    (colimitFiberwiseColimitIso fundamentalGroupDiagram :
      colimit (fiberwiseColimit fundamentalGroupDiagram) ≅
        colimit fundamentalGroupDiagram))

/- The cocone leg for a pair `(S, U)` factors through the iterated-colimit comparison by the
canonical component formula. -/
#check
  (fun (fundamentalGroupDiagram : Grothendieck F ⥤ GrpCat) (S : C) (U : F.obj S) ↦
    (ι_colimitFiberwiseColimitIso_hom fundamentalGroupDiagram S U :
      colimit.ι (Grothendieck.ι F S ⋙ fundamentalGroupDiagram) U ≫
          colimit.ι (fiberwiseColimit fundamentalGroupDiagram) S ≫
          (colimitFiberwiseColimitIso fundamentalGroupDiagram).hom =
        colimit.ι fundamentalGroupDiagram ⟨S, U⟩))
