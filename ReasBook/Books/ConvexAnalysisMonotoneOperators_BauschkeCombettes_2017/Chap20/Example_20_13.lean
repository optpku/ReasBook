/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap17.Proposition_17_25
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap20.Definition_20_1
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap20.Proposition_20_2

-- Declarations for this item will be appended below by the statement pipeline.

open scoped InnerProductSpace Pointwise

universe u

namespace SetValuedOperator

variable {H : Type u} [NormedAddCommGroup H]

section

variable [InnerProductSpace ℝ H]

-- Proof sketch: use the Chapter 20 owner `SetValuedOperator.IsMonotone` together with the
-- canonical four-point reformulation from Proposition 20.2. If `u ∈ (-Φ[C]) x` and
-- `v ∈ (-Φ[C]) y`, then `-u` and `-v` are active farthest points in `C`; comparing the
-- maximizing property of `-u` against `-v` at `x`, and of `-v` against `-u` at `y`, gives the
-- two squared-distance inequalities whose sum is exactly the required four-point inequality.
/-- Example 20.13: the negation of the chapter's active farthest-point operator `Φ[C]` is
monotone. -/
theorem neg_chebyshevCenterActiveSet_isMonotone (C : Set H) :
    (-Φ[C]).IsMonotone := by
  rw [SetValuedOperator.isMonotone_iff]
  intro x u y v hu hv
  have huActive : -u ∈ Φ[C] x := by
    simpa using hu
  have hvActive : -v ∈ Φ[C] y := by
    simpa using hv
  have hu' : -u ∈ C ∧ IsMaxOn (fun r ↦ (((‖x - r‖ ^ (2 : ℕ) : ℝ) : EReal))) C (-u) := by
    simpa [chebyshevCenterActiveSet] using huActive
  have hv' : -v ∈ C ∧ IsMaxOn (fun r ↦ (((‖y - r‖ ^ (2 : ℕ) : ℝ) : EReal))) C (-v) := by
    simpa [chebyshevCenterActiveSet] using hvActive
  rcases hu' with ⟨huC, huMax⟩
  rcases hv' with ⟨hvC, hvMax⟩
  have hxE :
      (((‖x - (-v)‖ ^ (2 : ℕ) : ℝ) : EReal)) ≤ (((‖x - (-u)‖ ^ (2 : ℕ) : ℝ) : EReal)) :=
    (isMaxOn_iff.mp huMax) (-v) hvC
  have hyE :
      (((‖y - (-u)‖ ^ (2 : ℕ) : ℝ) : EReal)) ≤ (((‖y - (-v)‖ ^ (2 : ℕ) : ℝ) : EReal)) :=
    (isMaxOn_iff.mp hvMax) (-u) huC
  have hx : ‖x - (-v)‖ ^ 2 ≤ ‖x - (-u)‖ ^ 2 := by
    exact_mod_cast hxE
  have hy : ‖y - (-u)‖ ^ 2 ≤ ‖y - (-v)‖ ^ 2 := by
    exact_mod_cast hyE
  have hfour :
      ‖y - (-v)‖ ^ 2 + ‖x - (-u)‖ ^ 2 ≥ ‖x - (-v)‖ ^ 2 + ‖y - (-u)‖ ^ 2 := by
    nlinarith
  have hinner : 0 ≤ ⟪x - y, -v + u⟫_ℝ := by
    simpa [sub_eq_add_neg] using
      (four_point_sq_norm_inequality_iff_inner_nonneg x (-v) y (-u)).mpr hfour
  simpa [sub_eq_add_neg, add_comm] using hinner

end

end SetValuedOperator
