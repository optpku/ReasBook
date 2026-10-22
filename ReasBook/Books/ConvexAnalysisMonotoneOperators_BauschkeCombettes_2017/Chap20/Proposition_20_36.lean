/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap20.Definition_20_20

-- Declarations for this item will be appended below by the statement pipeline.

open scoped InnerProductSpace

universe u

namespace SetValuedOperator

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/- Source/core/bridge triage:
- `source-facing`: Proposition 20.36 asserts that every value `A x` of a maximally monotone
  operator is closed and convex.
- `core/canonical`: the owner abstraction is maximal monotonicity `Maximal IsMonotone A`,
  accessed through the chapter owner theorem `Maximal.mem_iff`.
- `bridge/view`: the halfspace-intersection formula for `A x` is a derived Minty-style view used
  only to prove the closedness and convexity clauses, so it should stay internal to this file. -/

-- Proof sketch: unfold maximal monotonicity at the fixed point `x`; this says exactly that `A x`
-- is the intersection of the affine halfspaces cut out by all graph points `(y, v)` of `A`.
private theorem value_eq_iInter_halfspaces
    {A : SetValuedOperator H H} (hA : Maximal IsMonotone A) (x : H) :
    A x = ⋂ y : H, ⋂ v : H, ⋂ _ : v ∈ A y, {w : H | 0 ≤ ⟪x - y, w - v⟫_ℝ} := by
  ext u
  simp only [Set.mem_iInter, Set.mem_setOf_eq]
  simpa using (Maximal.mem_iff hA x u)

-- Proof sketch: use the halfspace description above. Each set `{u | 0 ≤ ⟪x - y, u - v⟫_ℝ}` is a
-- closed affine halfspace because `u ↦ ⟪x - y, u - v⟫_ℝ` is continuous, and arbitrary
-- intersections of closed sets are closed.
/-- Proposition 20.36 (1): for a maximally monotone operator on a real Hilbert space, every value
set `A x` is closed. -/
theorem Maximal.value_isClosed
    {A : SetValuedOperator H H} (hA : Maximal IsMonotone A) (x : H) :
    IsClosed (A x) := by
  rw [value_eq_iInter_halfspaces hA x]
  refine isClosed_iInter fun y ↦ isClosed_iInter fun v ↦ isClosed_iInter fun hv ↦ ?_
  have hclosed :
      IsClosed {w : H | 0 ≤ ⟪x - y, w⟫_ℝ - ⟪x - y, v⟫_ℝ} := by
    simpa using
      isClosed_le
        (continuous_const : Continuous fun _ : H ↦ (0 : ℝ))
        (((continuous_const : Continuous fun _ : H ↦ x - y).inner continuous_id).sub
          (continuous_const : Continuous fun _ : H ↦ ⟪x - y, v⟫_ℝ))
  simpa [inner_sub_right] using hclosed

-- Proof sketch: use the same halfspace description of `A x` furnished by maximal monotonicity.
-- Each set `{u | 0 ≤ ⟪x - y, u - v⟫_ℝ}` is convex because it is an affine halfspace, and arbitrary
-- intersections of convex sets are convex.
/-- Proposition 20.36 (2): for a maximally monotone operator on a real Hilbert space, every value
set `A x` is convex. -/
theorem Maximal.value_convex
    {A : SetValuedOperator H H} (hA : Maximal IsMonotone A) (x : H) :
    Convex ℝ (A x) := by
  rw [value_eq_iInter_halfspaces hA x]
  refine convex_iInter fun y ↦ convex_iInter fun v ↦ convex_iInter fun hv ↦ ?_
  change Convex ℝ {w : H | 0 ≤ (innerₛₗ ℝ (x - y)) (w - v)}
  let T : Set H := {w : H | 0 ≤ (innerₛₗ ℝ (x - y)) w}
  have hT : Convex ℝ T := by
    simpa [T] using
      (convex_halfSpace_ge (LinearMap.isLinear (innerₛₗ ℝ (x - y))) (0 : ℝ))
  simpa [T, sub_eq_add_neg] using hT.translate_preimage_left (-v)

end SetValuedOperator
