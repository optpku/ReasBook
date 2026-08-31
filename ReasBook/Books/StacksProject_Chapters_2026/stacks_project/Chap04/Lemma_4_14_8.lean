module

import Mathlib.CategoryTheory.Limits.HasLimits
import Mathlib.Tactic.Recall

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

universe v₁ v₂ v u₁ u₂ u

open CategoryTheory

namespace CategoryTheory.Limits

variable {I : Type u₁} [Category.{v₁} I]
variable {J : Type u₂} [Category.{v₂} J]
variable {C : Type u} [Category.{v} C]
variable {M : I ⥤ C} [HasColimit M]
variable {N : J ⥤ C} [HasColimit N]
variable {H : I ⥤ J}

/- Domain-style sampling for Lemma 4.14.8:
- primary domain: category theory of colimits.
- sampled canonical owner abstractions: `Cocone.whisker`, `Cocone.precompose`,
  `colimit.desc`, `colimit.existsUnique`.
- source/core/bridge triage:
  - source-facing: the comparison morphism `colimit M ⟶ colimit N` induced by
    `t : M ⟶ H ⋙ N`;
  - core/canonical: the cocone on `M` obtained by precomposing
    `((colimit.cocone N).whisker H)` along `t`;
  - bridge: the textbook existence-and-uniqueness statement is exactly the
    specialization of `colimit.existsUnique` to that induced cocone. -/

/- Lemma 4.14.8: a natural transformation `t : M ⟶ H ⋙ N` induces a unique
morphism from `colimit M` to `colimit N` whose composites with the colimit legs
agree with `t` componentwise. -/
#check
  (show ∀ t : M ⟶ H ⋙ N, ∃! θ : colimit M ⟶ colimit N,
      ∀ i : I, colimit.ι M i ≫ θ = t.app i ≫ colimit.ι N (H.obj i) from
    fun t ↦ by
      simpa using
        colimit.existsUnique ((Cocone.precompose t).obj ((colimit.cocone N).whisker H)))

end CategoryTheory.Limits
