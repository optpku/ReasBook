/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.Normed.Module.Normalize

public section

noncomputable section

namespace VariationalRegularization

/-- If `y` lies in the closed unit ball of `EuclideanSpace ℝ (Fin d)`, then
`inner ℝ x y` is bounded above by `‖x‖`. -/
theorem inner_le_norm_of_mem_closedUnitBall {d : ℕ}
    (x y : EuclideanSpace ℝ (Fin d))
    (hy : y ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) 1) :
    inner ℝ x y ≤ ‖x‖ := by
  calc
    inner ℝ x y ≤ ‖x‖ * ‖y‖ := real_inner_le_norm x y
    _ ≤ ‖x‖ * 1 :=
      mul_le_mul_of_nonneg_left (mem_closedBall_zero_iff.1 hy) (norm_nonneg _)
    _ = ‖x‖ := by ring

/-- The canonical normalized vector `NormedSpace.normalize x` attains the value
`‖x‖` under the map `y ↦ inner ℝ x y`. -/
theorem inner_eq_norm_of_normalize {d : ℕ}
    (x : EuclideanSpace ℝ (Fin d)) :
    inner ℝ x (NormedSpace.normalize x) = ‖x‖ := by
  by_cases hx : x = 0
  · simp [hx, NormedSpace.normalize]
  · calc
      inner ℝ x (NormedSpace.normalize x) = ‖x‖⁻¹ * inner ℝ x x := by
        rw [NormedSpace.normalize, real_inner_smul_right]
      _ = ‖x‖⁻¹ * ‖x‖ ^ 2 := by rw [real_inner_self_eq_norm_sq]
      _ = ‖x‖ := by
        rw [pow_two, ← mul_assoc, inv_mul_cancel₀ (norm_ne_zero_iff.2 hx), one_mul]

/-- The normalized vector `‖x‖⁻¹ • x` attains the value `‖x‖` under the map
`y ↦ inner ℝ x y`. -/
theorem inner_eq_norm_of_inv_norm_smul {d : ℕ}
    (x : EuclideanSpace ℝ (Fin d)) :
    inner ℝ x (‖x‖⁻¹ • x) = ‖x‖ := by
  simpa [NormedSpace.normalize] using inner_eq_norm_of_normalize x

/-- Exercise 8.6. The supremum of `y ↦ inner ℝ x y` over the closed unit ball
`Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) 1` is `‖x‖`. -/
theorem sSup_inner_closedUnitBall_eq_norm {d : ℕ}
    (x : EuclideanSpace ℝ (Fin d)) :
    sSup ((fun y : EuclideanSpace ℝ (Fin d) ↦ inner ℝ x y) ''
      Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) 1) = ‖x‖ := by
  let s : Set ℝ :=
    (fun y : EuclideanSpace ℝ (Fin d) ↦ inner ℝ x y) ''
      Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) 1
  have hs_nonempty : s.Nonempty := by
    refine ⟨0, ?_⟩
    refine ⟨0, Metric.mem_closedBall_self zero_le_one, ?_⟩
    simp
  have hs_bdd : BddAbove s := by
    refine ⟨‖x‖, ?_⟩
    rintro z ⟨y, hy, rfl⟩
    exact inner_le_norm_of_mem_closedUnitBall x y hy
  refine le_antisymm (csSup_le hs_nonempty ?_) (le_csSup hs_bdd ?_)
  · rintro z ⟨y, hy, rfl⟩
    exact inner_le_norm_of_mem_closedUnitBall x y hy
  · refine ⟨NormedSpace.normalize x, ?_, inner_eq_norm_of_normalize x⟩
    refine mem_closedBall_zero_iff.2 ?_
    by_cases hx : x = 0
    · simp [hx, NormedSpace.normalize]
    · exact le_of_eq (NormedSpace.norm_normalize hx)

end VariationalRegularization
