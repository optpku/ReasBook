module

public import Mathlib.CategoryTheory.Sites.LocallySurjective
import Mathlib.Tactic.Recall
public import stacks_project.Chap07.PlusNotation

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Opposite
open scoped CategoryTheory.GrothendieckTopology.PlusNotation

universe v u

namespace CategoryTheory.GrothendieckTopology

section

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
variable {ℱ : Cᵒᵖ ⥤ Type (max u v)}

/- Domain-style sampling for Lemma 7.49.1:
- primary domain: the plus construction for set-valued presheaves on a Grothendieck site;
- sampled owner API:
  `GrothendieckTopology.plusObj`,
  `GrothendieckTopology.toPlus`,
  `GrothendieckTopology.toPlusNatTrans`,
  `(J.plusFunctor (Type (max u v))).PreservesMonomorphisms`,
  `Presheaf.isLocallySurjective_toPlus`;
- best owner abstraction: `J.plusObj` with its canonical map `J.toPlus`, functorially packaged by
  `J.plusFunctor` and `J.toPlusNatTrans`;
- source/core/bridge triage:
  `source-facing`: the textbook lemma enumerates the canonical output `ℱ⁺`, the map
    `ℱ ⟶ ℱ⁺`, its functoriality, preservation of monomorphisms, and local surjectivity;
  `core/canonical`: the owner declarations listed above on `GrothendieckTopology` and
    `Presheaf`;
  `bridge/view`: the earlier chapter items Lemma 7.10.3, Lemma 7.10.4, and Lemma 7.10.8 are
    already source-facing recalls of these same owners.

Primitive data are only `J` and the presheaf `ℱ`: for set-valued presheaves, `Type (max u v)`
already supplies the limits and colimits used internally by the plus construction. The map
`J.toPlus ℱ`, its naturality, the monomorphism-preservation statement, and its local surjectivity
are all derived from that owner abstraction, so this file should stay at the direct recall/use
layer instead of introducing a parallel local wrapper.
-/

/- Lemma 7.49.1 (1): the plus construction sends a presheaf `ℱ` on `(C, J)` to the presheaf
`ℱ⁺`. -/
#check ℱ⁺

/- Lemma 7.49.1 (2): the plus construction comes with the canonical map
`J.toPlus ℱ : ℱ ⟶ ℱ⁺`. -/
#check J.toPlus ℱ

/- Lemma 7.49.1 (3): the assignment `ℱ ↦ (J.toPlus ℱ : ℱ ⟶ ℱ⁺)` is functorial, i.e. it
is the canonical natural transformation from the identity functor to the plus functor. -/
#check J.toPlusNatTrans (Type (max u v))

/- Lemma 7.49.1 (4): the plus construction sends monomorphisms of presheaves of sets to
monomorphisms. The owner-level canonical form is that the plus functor preserves monomorphisms. -/
#check
  (inferInstance : (J.plusFunctor (Type (max u v))).PreservesMonomorphisms)

/- Lemma 7.49.1 (5): every section of `ℱ⁺` is locally induced from `ℱ`; canonically,
this is the local surjectivity of `J.toPlus ℱ`. -/
recall Presheaf.isLocallySurjective_toPlus :
  Presheaf.IsLocallySurjective J (J.toPlus ℱ)

end

end CategoryTheory.GrothendieckTopology
