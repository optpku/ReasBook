module

public import Mathlib.CategoryTheory.Limits.HasLimits
import Mathlib.Tactic.Recall

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory

universe v₁ u₁ v₂ u₂ v₃ u₃

namespace CategoryTheory.Limits

variable {I : Type u₁} [Category.{v₁} I]
variable {J : Type u₂} [Category.{v₂} J]
variable {C : Type u₃} [Category.{v₃} C]

variable {M : I ⥤ C} [HasLimit M] {N : J ⥤ C} [HasLimit N] {H : I ⥤ J}

/-- The comparison morphism from `limit N` to `limit M` induced by precomposing the limit cone
of `N` along `H` and postcomposing with `t`. -/
noncomputable def limitComparison (t : H ⋙ N ⟶ M) : limit N ⟶ limit M :=
  limit.lift M ((Cone.postcompose t).obj ((limit.cone N).whisker H))

-- Proof sketch: apply `limit.lift_π` to the cone on `M` obtained by whiskering `limit.cone N`
-- along `H` and postcomposing with `t`.
/-- The comparison morphism induced by `t` commutes with the limit projections. -/
theorem limitComparison_π (t : H ⋙ N ⟶ M) (i : I) :
    limitComparison t ≫ limit.π M i = limit.π N (H.obj i) ≫ t.app i := by
  -- The comparison map is the universal lift from the induced cone on `M`.
  unfold limitComparison
  -- The `i`-th leg of that cone is definitionally the required composite.
  simpa using limit.lift_π ((Cone.postcompose t).obj ((limit.cone N).whisker H)) i

-- Proof sketch: apply `limit.existsUnique` to the cone on `M` with vertex `limit N` obtained by
-- whiskering `limit.cone N` along `H` and postcomposing with `t`.
/-- Lemma 4.14.9: a natural transformation `t : H ⋙ N ⟶ M` induces a unique morphism from
`limit N` to `limit M` whose composites with the projections are `t.app i`. -/
theorem limitComparison_existsUnique (t : H ⋙ N ⟶ M) :
    ∃! θ : limit N ⟶ limit M,
      ∀ i : I, θ ≫ limit.π M i = limit.π N (H.obj i) ≫ t.app i := by
  -- The source-faithful route is to apply the universal property to the induced cone on `M`.
  simpa [limitComparison] using
    (limit.existsUnique ((Cone.postcompose t).obj ((limit.cone N).whisker H)))

end CategoryTheory.Limits
