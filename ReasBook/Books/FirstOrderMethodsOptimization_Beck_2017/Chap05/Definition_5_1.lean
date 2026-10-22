/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u

section

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]

/- Definition 5.1 is `source-facing`: it introduces the chapter smoothness-on-a-set predicate.
Domain sampling shows that the `core/canonical` owners are mathlib's `DifferentiableAt`,
`LipschitzOnWith`, and `fderiv`. The gradient formulation is an inner-product `bridge/view`,
derived from this owner abstraction rather than stored as primitive data. -/

/-- Definition 5.1: a real-valued function is `L`-smooth on `D` when it is differentiable at every
point of `D` and its Fréchet derivative is `L`-Lipschitz on `D`. -/
def is_l_smooth_on (f : E → ℝ) (D : Set E) (L : NNReal) : Prop :=
  (∀ x ∈ D, DifferentiableAt ℝ f x) ∧ LipschitzOnWith L (fderiv ℝ f) D

-- Proof sketch: unfold `is_l_smooth_on`, then rewrite `LipschitzOnWith` using
-- `lipschitzOnWith_iff_norm_sub_le`; the metric on continuous linear maps is induced by the
-- operator norm, so the Lipschitz condition becomes the displayed derivative estimate.
/-- An `L`-smooth function on `D` is equivalently differentiable at every point of `D` and
satisfies the textbook estimate `‖f'(x) - f'(y)‖ ≤ L ‖x - y‖` for all `x, y ∈ D`. -/
theorem is_l_smooth_on_iff {f : E → ℝ} {D : Set E} {L : NNReal} :
    is_l_smooth_on f D L ↔
      (∀ x ∈ D, DifferentiableAt ℝ f x) ∧
        ∀ x ∈ D, ∀ y ∈ D, ‖fderiv ℝ f x - fderiv ℝ f y‖ ≤ (L : ℝ) * ‖x - y‖ := by
  rw [is_l_smooth_on, lipschitzOnWith_iff_norm_sub_le]

end

section

open scoped Gradient

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

-- Proof sketch: combine `is_l_smooth_on_iff` with `DifferentiableAt.hasGradientAt`, which
-- identifies `fderiv ℝ f x` with `toDual ℝ E (∇ f x)` at differentiability points. Since
-- `gradient f = (toDual ℝ E).symm ∘ fderiv ℝ f` and `toDual ℝ E` is a linear isometry
-- equivalence, Lipschitz control of `fderiv ℝ f` on `D` is equivalent to Lipschitz control of the
-- canonical gradient field on `D`.
/-- In a real Hilbert space, `is_l_smooth_on` is equivalently differentiability on `D` together
with `L`-Lipschitz control of the canonical gradient field on `D`. -/
theorem is_l_smooth_on_iff_lipschitzOnWith_gradient {f : E → ℝ} {D : Set E} {L : NNReal} :
    is_l_smooth_on f D L ↔
      (∀ x ∈ D, DifferentiableAt ℝ f x) ∧ LipschitzOnWith L (∇ f) D := by
  rw [is_l_smooth_on]
  constructor
  · rintro ⟨hdiff, hderiv⟩
    refine ⟨hdiff, ?_⟩
    rw [lipschitzOnWith_iff_norm_sub_le] at hderiv ⊢
    intro x hx y hy
    have hx' := hdiff x hx
    have hy' := hdiff y hy
    have hxy : ‖InnerProductSpace.toDual ℝ E (∇ f x - ∇ f y)‖ ≤ (L : ℝ) * ‖x - y‖ := by
      simpa [hx'.hasGradientAt.hasFDerivAt.fderiv, hy'.hasGradientAt.hasFDerivAt.fderiv, map_sub]
        using hderiv hx hy
    rwa [(InnerProductSpace.toDual ℝ E).norm_map] at hxy
  · rintro ⟨hdiff, hgrad⟩
    refine ⟨hdiff, ?_⟩
    rw [lipschitzOnWith_iff_norm_sub_le] at hgrad ⊢
    intro x hx y hy
    have hx' := hdiff x hx
    have hy' := hdiff y hy
    have hxy : ‖InnerProductSpace.toDual ℝ E (∇ f x - ∇ f y)‖ ≤ (L : ℝ) * ‖x - y‖ := by
      rw [(InnerProductSpace.toDual ℝ E).norm_map]
      exact hgrad hx hy
    simpa [hx'.hasGradientAt.hasFDerivAt.fderiv, hy'.hasGradientAt.hasFDerivAt.fderiv, map_sub]
      using hxy

-- Proof sketch: combine `is_l_smooth_on_iff_lipschitzOnWith_gradient` with
-- `lipschitzOnWith_iff_norm_sub_le` in the normed target space `E`.
/-- In a real Hilbert space, `is_l_smooth_on` is equivalently differentiability on `D` together
with the textbook Lipschitz estimate for the gradient field. -/
theorem is_l_smooth_on_iff_forall_norm_sub_le {f : E → ℝ} {D : Set E} {L : NNReal} :
    is_l_smooth_on f D L ↔
      (∀ x ∈ D, DifferentiableAt ℝ f x) ∧
        ∀ x ∈ D, ∀ y ∈ D,
          ‖∇ f x - ∇ f y‖ ≤ (L : ℝ) * ‖x - y‖ := by
  rw [is_l_smooth_on_iff_lipschitzOnWith_gradient, lipschitzOnWith_iff_norm_sub_le]

end
