/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import OptimizationTheoryAndMethods_SunYuan_2006.Chap01.Theorem_1_3_13
import OptimizationTheoryAndMethods_SunYuan_2006.Chap01.Theorem_1_4_4
import Mathlib.Analysis.Calculus.Deriv.AffineMap
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Convex.Extrema

section Chapter01Theorem149

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

open AffineMap

-- Primary mathematical domain: first-order optimality for convex differentiable functions.
-- Core/canonical owners: `ConvexOn`, `IsMinOn`, and the Chapter 1 stationary-point owner
-- `IsStationaryPoint`.
-- Bridge/view layer used here:
-- * `gradient_eq_zero_of_isLocalMinOn` for the first-order necessary condition;
-- * `ConvexOn.isMinOn_of_rightDeriv_eq_zero` on the line segment through `xStar` and `y`.
-- Primitive data: convexity on `Set.univ` and differentiability at `xStar`.
-- Derived API: the global-minimizer/stationary-point criterion.

/-- Convex sufficiency in Chapter 1 owner form: for a convex objective on the whole space, a
stationary point is a global minimizer. The proof reduces to the one-dimensional convex function on
each affine line through `xStar`. -/
theorem isMinOn_univ_of_isStationaryPoint_of_convex
    (f : E → ℝ) (xStar : E)
    (hconv : ConvexOn ℝ Set.univ f) (hStat : IsStationaryPoint f xStar) :
    IsMinOn f Set.univ xStar := by
  rw [isMinOn_univ_iff]
  intro y
  let g : ℝ → ℝ := f ∘ lineMap xStar y
  have hconv_g : ConvexOn ℝ Set.univ g := by
    simpa [g] using
      (hconv.comp_affineMap (lineMap xStar y : ℝ →ᵃ[ℝ] E))
  have hgDeriv : HasDerivAt g 0 0 := by
    have hLine : HasDerivAt (lineMap xStar y : ℝ → E) (y - xStar) 0 :=
      hasDerivAt_lineMap
    have hFDeriv : HasFDerivAt f ((InnerProductSpace.toDual ℝ E) 0) xStar :=
      hStat.hasGradientAt.hasFDerivAt
    simpa [g] using
      (hFDeriv.comp_hasDerivAt_of_eq
        (0 : ℝ) hLine (lineMap_apply_zero xStar y).symm)
  have hgMin : IsMinOn g Set.univ 0 := by
    refine hconv_g.isMinOn_of_rightDeriv_eq_zero ?_ ?_
    · simp
    · exact hgDeriv.hasDerivWithinAt.derivWithin (uniqueDiffWithinAt_Ioi 0)
  simpa [g, lineMap_apply_zero, lineMap_apply_one] using
    (isMinOn_univ_iff.mp hgMin) 1

/-- Chapter01 Theorem 1.4.9: in a real complete inner product space, a differentiable convex
function on the whole space has a global minimizer at `xStar` if and only if
`gradient f xStar = 0`. The textbook's `ℝⁿ` statement is the Euclidean specialization. -/
theorem isMinOn_univ_iff_gradient_eq_zero_of_convex
    (f : E → ℝ) (xStar : E)
    (hconv : ConvexOn ℝ Set.univ f) (hdiff : DifferentiableAt ℝ f xStar) :
    IsMinOn f Set.univ xStar ↔ gradient f xStar = 0 := by
  constructor
  · intro hmin
    simpa using
      gradient_eq_zero_of_isLocalMinOn Set.univ f xStar isOpen_univ (by simp) hdiff
        hmin.localize
  · intro hgrad
    exact isMinOn_univ_of_isStationaryPoint_of_convex f xStar hconv
      ((isStationaryPoint_iff f xStar).2 ⟨hgrad, hdiff⟩)

end Chapter01Theorem149
