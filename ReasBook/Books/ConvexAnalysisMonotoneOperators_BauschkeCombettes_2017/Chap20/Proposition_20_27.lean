/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap01.Text_1_0_13
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap20.Definition_20_20

-- Declarations for this item will be appended below by the statement pipeline.

open scoped InnerProductSpace

universe u

namespace Function

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- A single-valued operator is hemicontinuous when every scalar slice
`α ↦ ⟪z, A (x + α • y)⟫_ℝ` is right-continuous at `0`. -/
def IsHemicontinuous (A : H → H) : Prop :=
  ∀ x y z : H,
    ContinuousWithinAt (fun α : ℝ ↦ ⟪z, A (x + α • y)⟫_ℝ) (Set.Ioi 0) 0

-- Proof sketch: unfold `Function.IsHemicontinuous` and `ContinuousWithinAt`; this rewrites the
-- right-continuity condition exactly as the textbook right-limit formula along `α ↓ 0`.
/-- The hemicontinuity condition is equivalent to the textbook right-limit formulation
`lim_{α ↓ 0} ⟪z, A (x + α • y)⟫ = ⟪z, A x⟫`. -/
theorem isHemicontinuous_iff_tendsto (A : H → H) :
    A.IsHemicontinuous ↔
      ∀ x y z : H,
        Filter.Tendsto (fun α : ℝ ↦ ⟪z, A (x + α • y)⟫_ℝ)
          (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds ⟪z, A x⟫_ℝ) :=
by
  constructor
  · intro h x y z
    simpa [ContinuousWithinAt, zero_smul] using h x y z
  · intro h x y z
    simpa [ContinuousWithinAt, zero_smul] using h x y z

-- Proof sketch: use the characterization of maximal monotonicity from Definition 20.20. If
-- `(x, u)` is monotonically related to the singleton-valued graph of `A`, test the inequality at
-- points `x + α • (u - A x)` for `α > 0`; monotonicity gives the sign condition, and
-- hemicontinuity lets `α ↓ 0` to deduce `‖u - A x‖² ≤ 0`, hence `u = A x`.
/-- Proposition 20.27: a monotone hemicontinuous single-valued operator on a real Hilbert space is
maximally monotone when viewed as its associated singleton-valued set-valued operator. -/
theorem toSetValuedOperator_isMaximallyMonotone_of_monotone_hemicontinuous
    (A : H → H) (hA_mono : A.toSetValuedOperator.IsMonotone) (hA_hemi : A.IsHemicontinuous) :
    Maximal SetValuedOperator.IsMonotone A.toSetValuedOperator := sorry

end Function
