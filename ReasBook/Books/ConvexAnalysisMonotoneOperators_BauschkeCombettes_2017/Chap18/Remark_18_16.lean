/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Gradient InnerProductSpace
open InnerProductSpace

universe u

namespace ERealFunction

noncomputable section

section StrongerDifferentiabilityNotions

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- The affine first-order model at `x` determined by the gradient of `f`. -/
def gradientAffineModelAt (f : H → ℝ) (x : H) : H → ℝ :=
  fun y ↦ f x + ⟪y - x, ∇ f x⟫_ℝ

/-- The quadratic model at `x` obtained by adding the `β / 2 * ‖y - x‖²` correction term to the
first-order affine model. -/
def gradientQuadraticModelAt (f : H → ℝ) (β : Set.Ioi (0 : ℝ)) (x : H) : H → ℝ :=
  fun y ↦ gradientAffineModelAt f x y + ((β : ℝ) / 2) * ‖y - x‖ ^ (2 : ℕ)

-- Proof sketch: Proposition 17.7 gives the global first-order support inequality for the affine
-- model at `x`. Theorem 18.15 turns differentiability together with `β`-Lipschitz continuity of
-- `∇ f` and convexity into the quadratic descent estimate, which is exactly the pointwise upper
-- bound by the quadratic model.
/-- Remark 18.16: for a convex function with `β`-Lipschitz gradient, the affine model at `x`
minorizes `f` and the quadratic model with curvature `β` majorizes `f`. -/
theorem gradient_models_sandwich_at
    (f : H → ℝ) (β : Set.Ioi (0 : ℝ)) (x : H)
    (hDiff : Differentiable ℝ f) (hconv : ConvexOn ℝ Set.univ f)
    (hLip : LipschitzWith (Real.toNNReal (β : ℝ)) (∇ f)) :
    gradientAffineModelAt f x ≤ f ∧ f ≤ gradientQuadraticModelAt f β x := sorry

-- Proof sketch: evaluate the explicit formulas at the base point `x`; both `x - x` and the
-- quadratic correction term vanish.
/-- Both explicit models in Remark 18.16 touch `f` at the base point `x`. -/
theorem gradient_models_eq_at_basePoint
    (f : H → ℝ) (β : Set.Ioi (0 : ℝ)) (x : H) :
    gradientAffineModelAt f x x = f x ∧
      gradientQuadraticModelAt f β x x = f x := sorry

-- Proof sketch: the affine model has constant Fréchet derivative `toDual ℝ H (∇ f x)`, and the
-- extra quadratic term in the quadratic model has zero derivative at `x` because it is second
-- order in `y - x`.
/-- Both explicit models in Remark 18.16 have Fréchet derivative `∇ f x` at the base point. -/
theorem gradient_models_hasFDerivAt_basePoint
    (f : H → ℝ) (β : Set.Ioi (0 : ℝ)) (x : H) :
    HasFDerivAt (gradientAffineModelAt f x) (toDual ℝ H (∇ f x)) x ∧
      HasFDerivAt (gradientQuadraticModelAt f β x) (toDual ℝ H (∇ f x)) x := sorry

end StrongerDifferentiabilityNotions

end

end ERealFunction
