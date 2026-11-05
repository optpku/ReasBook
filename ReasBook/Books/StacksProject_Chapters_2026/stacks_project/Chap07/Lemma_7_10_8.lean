module

public import Mathlib.CategoryTheory.Sites.LocallySurjective
import Mathlib.Tactic.Recall

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Opposite

universe v u

section

variable {C : Type u} [Category.{v} C]
variable (J : GrothendieckTopology C)
variable (ℱ : Cᵒᵖ ⥤ Type (max u v))

/- Domain-style sampling for Lemma 7.10.8:
- primary domain: the plus construction and local surjectivity for set-valued presheaves on a
  Grothendieck site;
- sampled owner API:
  `CategoryTheory.GrothendieckTopology.plusObj`,
  `CategoryTheory.GrothendieckTopology.toPlus`,
  `CategoryTheory.Presheaf.IsLocallySurjective`,
  `CategoryTheory.Presheaf.isLocallySurjective_toPlus`;
- best owner abstraction: the canonical predicate `Presheaf.IsLocallySurjective J` applied to the
  canonical plus map `J.toPlus ℱ`;
- source/core/bridge triage:
  `source-facing`: the textbook lemma says the canonical map `ℱ ⟶ ℱ⁺` is locally surjective;
  `core/canonical`: the owner constructions `J.plusObj ℱ`, `J.toPlus ℱ`, and the predicate
    `Presheaf.IsLocallySurjective J`;
  `bridge/view`: the canonical derived instance
    `Presheaf.isLocallySurjective_toPlus J ℱ`.
- primitive data: only `J` and `ℱ`;
- derived API: the plus object `J.plusObj ℱ`, the canonical map `J.toPlus ℱ`, and the instance
  `Presheaf.isLocallySurjective_toPlus J ℱ`.

No local wrapper or chapter-level restatement should remain here: this item is already best
expressed as a direct recall of the owner instance.
-/
/- Lemma 7.10.8: the canonical map `θ : ℱ ⟶ ℱ⁺`, namely `J.toPlus ℱ` with `ℱ⁺ = J.plusObj ℱ`, is
locally surjective. Equivalently, for every object `U` and every section `s ∈ ℱ⁺(U)`, there
exists a covering of `U` on which the restriction of `s` lies in the image of `θ`. -/
recall Presheaf.isLocallySurjective_toPlus :
  Presheaf.IsLocallySurjective J (J.toPlus ℱ)

end
