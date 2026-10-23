module

public import stacks_project.Chap07.PlusNotation

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Opposite
open scoped CategoryTheory.GrothendieckTopology.PlusNotation

universe v u

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
variable (P : Cᵒᵖ ⥤ Type (max u v))

/- Domain-style sampling for Lemma 7.10.3:
- primary domain: the plus construction for set-valued presheaves on a Grothendieck site;
- sampled owner API:
  `CategoryTheory.GrothendieckTopology.plusObj`,
  `CategoryTheory.GrothendieckTopology.toPlus`,
  `CategoryTheory.GrothendieckTopology.toPlusNatTrans`,
  `CategoryTheory.Presheaf.isLocallySurjective_toPlus`;
- source-facing layer: the source introduces the plus construction `P ↦ P⁺` and its canonical map;
- core/canonical owner: `J.plusObj P` and `J.toPlus P`;
- bridge/view: the functorial packaging `J.plusFunctor` and `J.toPlusNatTrans`.

Primitive data are only the topology `J` and the presheaf `P`. The map `J.toPlus P` is derived
from the owner construction, so this file should remain a direct recall of the canonical API
rather than introduce a local wrapper.
-/
/-
Lemma 7.10.3: the plus construction on a set-valued presheaf `P` canonically gives the presheaf
`P⁺`.
-/
#check P⁺

/- Companion recall: the plus construction comes with the canonical map of presheaves
`J.toPlus P : P ⟶ P⁺`. -/
#check J.toPlus P
