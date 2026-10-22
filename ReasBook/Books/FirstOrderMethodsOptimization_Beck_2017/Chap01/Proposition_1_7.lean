/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import FirstOrderMethodsOptimization_Beck_2017.Chap01.Definition_1_42

-- Declarations for this item will be appended below by the statement pipeline.

universe u

section

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [FiniteDimensional ℝ E] [Nontrivial E]

-- Proof sketch: use the chapter owner declaration `dualNorm` and the earlier attainment theorem on
-- the closed unit ball. If `dualNorm y = 0`, every value on the unit sphere is `0`. Otherwise, a
-- maximizer on the closed unit ball must already lie on the unit sphere, since the dual-pairing
-- inequality would force strict inequality whenever `‖x‖ < 1`.
/-- Proposition 1.7: the dual norm of `y ∈ E*` can be computed by maximizing the canonical pairing
over the unit sphere, not just over the closed unit ball. Equivalently, `‖y‖_*` is the greatest
value of `y x` for `x` on `Metric.sphere (0 : E) 1`. -/
theorem dualNorm_isGreatest_on_unit_sphere (y : Module.Dual ℝ E) :
    IsGreatest (y '' Metric.sphere (0 : E) 1) (dualNorm y) := by
  by_cases hy : dualNorm y = 0
  · obtain ⟨x, hx⟩ : (Metric.sphere (0 : E) 1).Nonempty :=
      NormedSpace.sphere_nonempty.mpr zero_le_one
    refine ⟨?_, ?_⟩
    · refine ⟨x, hx, ?_⟩
      have hle : |y x| ≤ 0 := by
        simpa [hy] using abs_apply_le_dual_norm_mul_norm y x
      have hzero : y x = 0 := abs_eq_zero.mp <| le_antisymm hle (abs_nonneg _)
      simp [hy, hzero]
    · rintro _ ⟨x, hx, rfl⟩
      have hle : |y x| ≤ 0 := by
        simpa [hy, mem_sphere_zero_iff_norm.mp hx] using abs_apply_le_dual_norm_mul_norm y x
      have hzero : y x = 0 := abs_eq_zero.mp <| le_antisymm hle (abs_nonneg _)
      simp [hy, hzero]
  · obtain ⟨x, hxball, hxy⟩ := exists_dualNorm_eq_apply y
    have hynonneg : 0 ≤ dualNorm y := by
      rw [dualNorm_eq_toContinuousLinearMap_norm]
      exact norm_nonneg _
    have hypos : 0 < dualNorm y := lt_of_le_of_ne hynonneg (Ne.symm hy)
    have hxge : 1 ≤ ‖x‖ := by
      have hle : dualNorm y ≤ dualNorm y * ‖x‖ := by
        calc
          dualNorm y = |y x| := by rw [← hxy, abs_of_nonneg hynonneg]
          _ ≤ dualNorm y * ‖x‖ := abs_apply_le_dual_norm_mul_norm y x
      have hle' : dualNorm y * 1 ≤ dualNorm y * ‖x‖ := by
        simpa using hle
      exact le_of_mul_le_mul_left hle' hypos
    have hxnorm : ‖x‖ = 1 := le_antisymm hxball hxge
    have hx : x ∈ Metric.sphere (0 : E) 1 := mem_sphere_zero_iff_norm.mpr hxnorm
    refine ⟨⟨x, hx, hxy.symm⟩, ?_⟩
    rintro _ ⟨x, hx, rfl⟩
    calc
      y x ≤ |y x| := le_abs_self _
      _ ≤ dualNorm y * ‖x‖ := abs_apply_le_dual_norm_mul_norm y x
      _ = dualNorm y := by rw [mem_sphere_zero_iff_norm.mp hx, mul_one]

end
