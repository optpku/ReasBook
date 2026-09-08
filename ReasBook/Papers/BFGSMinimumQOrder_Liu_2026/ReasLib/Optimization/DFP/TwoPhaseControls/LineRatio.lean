module

public import ReasLib.Optimization.DFP.TwoPhaseControls

public section

/-!
# Line ratios of the two-phase DFP controls
-/

namespace TwoPhaseControls

/-- Every two-phase line ratio is one of the two prescribed rational values. -/
theorem phase_tau_mem (epsilon : ℝ) (i : Fin 2) :
    (phase epsilon i).tau = 2 / 3 ∨ (phase epsilon i).tau = 1 / 3 := by
  have hi : i = 0 ∨ i = 1 := by omega
  rcases hi with rfl | rfl
  · left
    rw [phase_zero, first_tau]
  · right
    rw [phase_one, second_tau]

/-- The absolute strong-Wolfe ratio of either phase is at most `2 / 3`. -/
theorem abs_one_sub_phase_tau_le (epsilon : ℝ) (i : Fin 2) :
    |1 - (phase epsilon i).tau| ≤ 2 / 3 := by
  rcases phase_tau_mem epsilon i with h | h
  · rw [h]
    norm_num
  · rw [h]
    norm_num

/-- The two absolute strong-Wolfe ratios are exactly `1 / 3` and `2 / 3`. -/
theorem abs_one_sub_phase_tau_mem (epsilon : ℝ) (i : Fin 2) :
    |1 - (phase epsilon i).tau| = 1 / 3 ∨
      |1 - (phase epsilon i).tau| = 2 / 3 := by
  rcases phase_tau_mem epsilon i with h | h
  · left
    rw [h]
    norm_num
  · right
    rw [h]
    norm_num

end TwoPhaseControls
