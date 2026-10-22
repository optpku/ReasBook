/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import Mathlib.Analysis.InnerProductSpace.PiL2
import OptimizationTheoryAndMethods_SunYuan_2006.Chap02.Theorem_2_2_9
import OptimizationTheoryAndMethods_SunYuan_2006.Chap05.Definition_5_1_extra_1

noncomputable section

open scoped Gradient

section Chapter05Exercise54

-- Domain sampling:
-- * primary domain: strong convexity and gradient secant curvature
-- * sampled canonical declarations:
--   `StrongConvexOn`,
--   `StrongConvexOn.gradientStrongMonotone_univ`,
--   `satisfiesCurvatureCondition`,
--   `secantCurvature_pos_of_step_nonzero_of_lowerLevelHessianLowerBound`
-- * source-facing layer here: `secantCurvature_pos_of_strongConvex`
-- * core/canonical owner: `StrongConvexOn Set.univ m f`
-- * bridge/view layer here: the Euclidean `dotProduct` reformulation of the Chapter 5 curvature
--   owner `satisfiesCurvatureCondition`
-- * primitive data: the strong convexity modulus `m`, the gradient data for `f`, a base point
--   `xk`, and a nonzero step `sk`
-- * derived API here: the Euclidean pointwise secant-curvature positivity statement in `ℝ^n`

section

variable {Point : Type*} [NormedAddCommGroup Point] [InnerProductSpace ℝ Point]
  [CompleteSpace Point]

/-- If `f` is globally `m`-strongly convex on a real inner product space and `sk ≠ 0`, then the
secant pair formed from the gradient increment satisfies the canonical Chapter 5 curvature
condition. -/
theorem secantCurvatureCondition_of_strongConvex
    (f : Point → ℝ) (m : ℝ) (xk sk : Point)
    (hm : 0 < m)
    (hStrong : StrongConvexOn Set.univ m f)
    (h_hasGradient : ∀ x : Point, HasGradientAt f (∇ f x) x)
    (hsk : sk ≠ 0) :
    satisfiesCurvatureCondition sk (∇ f (xk + sk) - ∇ f xk) := by
  rw [satisfiesCurvatureCondition]
  have hmono := hStrong.gradientStrongMonotone_univ h_hasGradient (xk + sk) xk
  have hbound : m * ‖sk‖ ^ (2 : ℕ) ≤ inner ℝ sk (∇ f (xk + sk) - ∇ f xk) := by
    simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hmono
  have hmul_pos : 0 < m * ‖sk‖ ^ (2 : ℕ) := by
    have hnorm_pos : 0 < ‖sk‖ := norm_pos_iff.mpr hsk
    positivity
  exact lt_of_lt_of_le hmul_pos hbound

section

variable {n : ℕ}

local notation "Point" => EuclideanSpace ℝ (Fin n)

/-- Chapter05 Exercise 5.4: if `f` is strongly convex and
`yk = ∇ f (xk + sk) - ∇ f xk`, then `y_kᵀ s_k > 0`, written in the Euclidean model as
`0 < dotProduct (∇ f (xk + sk) - ∇ f xk) sk` for every nonzero step `sk`. This is the
Euclidean bridge from the Chapter 5 curvature owner to the textbook scalar pairing. -/
theorem secantCurvature_pos_of_strongConvex
    (f : Point → ℝ) (m : ℝ) (xk sk : Point)
    (hm : 0 < m)
    (hStrong : StrongConvexOn Set.univ m f)
    (h_hasGradient : ∀ x : Point, HasGradientAt f (∇ f x) x)
    (hsk : sk ≠ 0) :
    0 < dotProduct (∇ f (xk + sk) - ∇ f xk) sk := by
  have hcurvature :
      0 < dotProduct sk (∇ f (xk + sk) - ∇ f xk) :=
    (satisfiesCurvatureCondition_iff_dotProduct_pos).1 <|
      secantCurvatureCondition_of_strongConvex f m xk sk hm hStrong h_hasGradient hsk
  simpa [dotProduct_comm] using hcurvature

end

end
