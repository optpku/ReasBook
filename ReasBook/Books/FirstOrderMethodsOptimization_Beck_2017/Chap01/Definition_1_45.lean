/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import FirstOrderMethodsOptimization_Beck_2017.Chap01.LinearMapFiniteDimensionalNorm

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u v

namespace LinearMap

section

variable {E : Type u} {V : Type v}
variable [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable [NormedAddCommGroup V] [NormedSpace ℝ V]

variable (A : E →ₗ[ℝ] V)

/- Definition 1.45 is recall-only: for a linear transformation on a finite-dimensional real normed
space, the textbook norm `‖A‖` is the canonical operator norm of the associated continuous linear
map `A.toContinuousLinearMap`. -/
#check (‖A‖ : ℝ)

-- Proof sketch: apply `ContinuousLinearMap.unit_le_opNorm` to the continuous linear map
-- `A.toContinuousLinearMap`; this canonical operator norm is exactly the textbook norm of `A`.
/-- Every vector in the closed unit ball is sent to a vector whose norm is bounded by the norm of
the linear transformation. -/
theorem norm_image_le (A : E →ₗ[ℝ] V) {x : E} (hx : ‖x‖ ≤ 1) : ‖A x‖ ≤ ‖A‖ := by
  simpa using A.toContinuousLinearMap.unit_le_opNorm x hx

-- Proof sketch: the closed unit ball in the finite-dimensional normed space `E` is compact, and
-- the map `x ↦ ‖A x‖` is continuous. Therefore it attains a maximum on that ball, and the
-- preceding bound identifies that maximum with `‖A‖`.
/-- The norm of a linear transformation is the greatest norm of its values on the closed unit ball.
-/
theorem norm_isGreatest_on_closedBall (A : E →ₗ[ℝ] V) :
    IsGreatest ((fun x : E ↦ ‖A x‖) '' Metric.closedBall (0 : E) 1) ‖A‖ := by
  let f : E → ℝ := fun y ↦ ‖A y‖
  have hcompact : IsCompact (Metric.closedBall (0 : E) 1) := isCompact_closedBall (0 : E) 1
  have hnonempty : (Metric.closedBall (0 : E) 1).Nonempty :=
    Metric.nonempty_closedBall.2 zero_le_one
  have hcont : ContinuousOn f (Metric.closedBall (0 : E) 1) := by
    have hAcont : Continuous f := by
      let g : E →L[ℝ] V := A.toContinuousLinearMap
      simpa [f, g] using g.continuous.norm
    exact hAcont.continuousOn
  obtain ⟨x, hx_mem, hx_max⟩ := hcompact.exists_isMaxOn hnonempty hcont
  have hnorm_le : ‖A‖ ≤ ‖A x‖ := by
    change ‖A.toContinuousLinearMap‖ ≤ ‖A x‖
    refine (ContinuousLinearMap.opNorm_le_iff (norm_nonneg (A x))).2 ?_
    intro y
    by_cases hy : y = 0
    · simp [hy]
    · have hy_mem : ‖‖y‖⁻¹ • y‖ ≤ 1 := by
        rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr (norm_nonneg _)),
          inv_mul_cancel₀ (norm_ne_zero_iff.mpr hy)]
      have hscaled : ‖A (‖y‖⁻¹ • y)‖ ≤ ‖A x‖ := hx_max (mem_closedBall_zero_iff.mpr hy_mem)
      have hy_decomp : ‖y‖ • (‖y‖⁻¹ • y) = y := by
        rw [smul_smul, mul_inv_cancel₀ (norm_ne_zero_iff.mpr hy), one_smul]
      calc
        ‖A y‖ = ‖A (‖y‖ • (‖y‖⁻¹ • y))‖ := by rw [hy_decomp]
        _ = ‖‖y‖ • A (‖y‖⁻¹ • y)‖ := by rw [map_smul]
        _ = ‖y‖ * ‖A (‖y‖⁻¹ • y)‖ := by
          rw [norm_smul, Real.norm_of_nonneg (norm_nonneg _)]
        _ ≤ ‖y‖ * ‖A x‖ := mul_le_mul_of_nonneg_left hscaled (norm_nonneg _)
        _ = ‖A x‖ * ‖y‖ := by ring
  have hx_le_norm : ‖A x‖ ≤ ‖A‖ := norm_image_le A (mem_closedBall_zero_iff.mp hx_mem)
  refine ⟨⟨x, hx_mem, le_antisymm hx_le_norm hnorm_le⟩, ?_⟩
  · rintro _ ⟨y, hy_mem, rfl⟩
    exact norm_image_le A (mem_closedBall_zero_iff.mp hy_mem)

/-- A vector in the closed unit ball realizes the norm of the linear transformation, recovering
the textbook maximum formula. -/
theorem exists_norm_le_one_eq_norm (A : E →ₗ[ℝ] V) :
    ∃ x : E, ‖x‖ ≤ 1 ∧ ‖A‖ = ‖A x‖ := by
  rcases (norm_isGreatest_on_closedBall A).1 with ⟨x, hx_mem, hxA⟩
  exact ⟨x, mem_closedBall_zero_iff.mp hx_mem, hxA.symm⟩

end

end LinearMap
