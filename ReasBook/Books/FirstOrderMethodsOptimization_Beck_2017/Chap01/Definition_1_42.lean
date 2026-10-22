/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import FirstOrderMethodsOptimization_Beck_2017.Chap01.Lemma_1_1
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u

section

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]

/- Definition 1.42: the dual norm on `E*` is the canonical chapter owner declaration `dualNorm`,
defined as the operator norm of the associated continuous linear functional. -/
recall dualNorm

end

section

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- The dual norm is the greatest value of the canonical pairing on the closed unit ball. -/
theorem dualNorm_isGreatest_on_closedBall (y : Module.Dual ℝ E) :
    IsGreatest (y '' Metric.closedBall (0 : E) 1) (dualNorm y) := by
  let f : E →L[ℝ] ℝ := y.toContinuousLinearMap
  have hcompact : IsCompact (Metric.closedBall (0 : E) 1) := isCompact_closedBall (0 : E) 1
  have hnonempty : (Metric.closedBall (0 : E) 1).Nonempty :=
    Metric.nonempty_closedBall.2 zero_le_one
  obtain ⟨x, hx_mem, hx_max⟩ := hcompact.exists_isMaxOn hnonempty f.continuous.continuousOn
  have hdual_nonneg : 0 ≤ dualNorm y := by
    change 0 ≤ ‖y.toContinuousLinearMap‖
    exact norm_nonneg _
  have hyx_nonneg : 0 ≤ y x := by
    simpa [f] using hx_max (by simp : (0 : E) ∈ Metric.closedBall (0 : E) 1)
  have hdual_le : dualNorm y ≤ y x := by
    change ‖y‖ ≤ y x
    refine (ContinuousLinearMap.opNorm_le_iff hyx_nonneg).2 fun z ↦ ?_
    by_cases hz : z = 0
    · simp [hz]
    · let u : E := ‖z‖⁻¹ • z
      have hu_mem : u ∈ Metric.closedBall (0 : E) 1 := by
        refine mem_closedBall_zero_iff.mpr ?_
        dsimp [u]
        rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr (norm_nonneg _)),
          inv_mul_cancel₀ (norm_ne_zero_iff.mpr hz)]
      have hneg_u_mem : -u ∈ Metric.closedBall (0 : E) 1 := by
        refine mem_closedBall_zero_iff.mpr ?_
        simpa using (mem_closedBall_zero_iff.mp hu_mem)
      have hu_le : y u ≤ y x := by
        simpa using hx_max hu_mem
      have hneg_u_le : y (-u) ≤ y x := by
        simpa using hx_max hneg_u_mem
      have hu_abs_le : |y u| ≤ y x := by
        refine abs_le.2 ⟨?_, hu_le⟩
        have hneg : -(y u) ≤ y x := by
          simpa using hneg_u_le
        simpa using neg_le_neg hneg
      have hz_decomp : ‖z‖ • u = z := by
        dsimp [u]
        rw [smul_smul, mul_inv_cancel₀ (norm_ne_zero_iff.mpr hz), one_smul]
      calc
        ‖y z‖ = ‖y (‖z‖ • u)‖ := by rw [hz_decomp]
        _ = ‖‖z‖ • y u‖ := by rw [map_smul]
        _ = ‖z‖ * ‖y u‖ := by simp
        _ ≤ ‖z‖ * y x := by
          gcongr
          simpa [Real.norm_eq_abs] using hu_abs_le
        _ = y x * ‖z‖ := by ring
  have hyx_le : y x ≤ dualNorm y := by
    calc
      y x ≤ |y x| := le_abs_self _
      _ ≤ dualNorm y * ‖x‖ := abs_apply_le_dual_norm_mul_norm y x
      _ ≤ dualNorm y := by
        simpa [mul_one] using
          mul_le_mul_of_nonneg_left (mem_closedBall_zero_iff.mp hx_mem) hdual_nonneg
  refine ⟨⟨x, hx_mem, le_antisymm hyx_le hdual_le⟩, ?_⟩
  rintro _ ⟨z, hz_mem, rfl⟩
  calc
    y z ≤ |y z| := le_abs_self _
    _ ≤ dualNorm y * ‖z‖ := abs_apply_le_dual_norm_mul_norm y z
    _ ≤ dualNorm y := by
      simpa [mul_one] using
        mul_le_mul_of_nonneg_left (mem_closedBall_zero_iff.mp hz_mem) hdual_nonneg

-- Proof sketch: extract the maximizing point from `dualNorm_isGreatest_on_closedBall`.
/-- A vector in the closed unit ball attains the dual norm, matching the textbook maximum formula
for `‖y‖_*`. -/
theorem exists_dualNorm_eq_apply (y : Module.Dual ℝ E) :
    ∃ x : E, ‖x‖ ≤ 1 ∧ dualNorm y = y x := by
  rcases (dualNorm_isGreatest_on_closedBall y).1 with ⟨x, hx_mem, hxy⟩
  exact ⟨x, mem_closedBall_zero_iff.mp hx_mem, hxy.symm⟩

end
