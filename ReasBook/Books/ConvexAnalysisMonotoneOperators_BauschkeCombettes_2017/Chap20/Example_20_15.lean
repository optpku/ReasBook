/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap02.Definition_2_23
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap20.Proposition_20_27

-- Declarations for this item will be appended below by the statement pipeline.

open scoped InnerProductSpace

universe u

namespace LinearMap

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

-- Proof sketch: use the canonical owner `SetValuedOperator.ofFunction_isMonotone_iff` in its
-- `Set.univ` specialization to rewrite monotonicity as the pairwise inequality
-- `0 ≤ ⟪x - y, T x - T y⟫_ℝ`, then use linearity to rewrite `T x - T y = T (x - y)` and
-- `real_inner_comm` to identify this with the quadratic-form condition from Definition 2.23 (1).
/-- Example 20.15: when a monotone operator is given by a linear map `T`, the monotonicity of the
associated singleton-valued operator from Definition 20.1 is exactly the linear monotonicity
condition of Definition 2.23 (1). -/
theorem toSetValuedOperator_isMonotone_iff (T : H →ₗ[ℝ] H) :
    (T : H → H).toSetValuedOperator.IsMonotone ↔ T.IsMonotone := by
  let S : Set H := Set.univ
  let F : S → H := fun x ↦ T x
  have hsingleton :
      (T : H → H).toSetValuedOperator.IsMonotone ↔
        ∀ x y : H, 0 ≤ ⟪x - y, T x - T y⟫_ℝ := by
    have howner :
        (SetValuedOperator.ofFunction S F).IsMonotone ↔
          ∀ x y : S, 0 ≤ ⟪(x : H) - (y : H), F x - F y⟫_ℝ :=
      SetValuedOperator.ofFunction_isMonotone_iff
    simpa [S, F, Function.toSetValuedOperator] using howner
  rw [hsingleton, LinearMap.IsMonotone]
  constructor
  · intro h x
    simpa [real_inner_comm] using h x 0
  · intro h x y
    simpa [LinearMap.map_sub, real_inner_comm] using h (x - y)

end LinearMap
