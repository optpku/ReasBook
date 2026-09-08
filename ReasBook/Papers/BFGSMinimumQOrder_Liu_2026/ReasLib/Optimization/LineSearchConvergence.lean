module

public import ReasLib.Analysis.Convergence.QOrder
public import ReasLib.Optimization.LineSearch
public import Mathlib.Analysis.CStarAlgebra.Matrix
public import Mathlib.Analysis.Calculus.ContDiff.Comp
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.Calculus.Gradient.Basic
public import Mathlib.Analysis.InnerProductSpace.Rayleigh
public import Mathlib.Analysis.Matrix.Hermitian
public import Mathlib.LinearAlgebra.Matrix.PosDef

public section

open scoped Topology

namespace QConvergence

/-- A positive-definite real matrix defines a uniformly coercive quadratic form on its
Euclidean space. -/
private lemma positiveDefiniteMatrixQuadraticLowerBound {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef) :
    ∃ μ > 0, ∀ v : EuclideanSpace ℝ (Fin n),
      μ * ‖v‖ ^ 2 ≤
        ContinuousLinearMap.reApplyInnerSelf
          ((Matrix.toEuclideanCLM :
            Matrix (Fin n) (Fin n) ℝ ≃⋆ₐ[ℝ]
              (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))) A) v := by
  let T : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) :=
    (Matrix.toEuclideanCLM :
      Matrix (Fin n) (Fin n) ℝ ≃⋆ₐ[ℝ]
        (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))) A
  -- Compactness upgrades strict positivity on the unit sphere to a uniform lower bound.
  have hpositive : ∀ v ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1,
      0 < T.reApplyInnerSelf v := by
    intro v hv
    have hv_ne : v ≠ 0 := by
      intro hv_zero
      simp [hv_zero] at hv
    simpa [ContinuousLinearMap.reApplyInnerSelf_apply, real_inner_comm,
      Matrix.inner_toEuclideanCLM, T] using
        hA.dotProduct_mulVec_pos (x := v) (by simpa using hv_ne)
  obtain ⟨μ, hμ, hμ_lower⟩ :=
    (isCompact_sphere (0 : EuclideanSpace ℝ (Fin n)) 1).exists_forall_le'
      T.reApplyInnerSelf_continuous.continuousOn hpositive
  refine ⟨μ, hμ, ?_⟩
  intro v
  rcases eq_or_ne v 0 with rfl | hv
  · simp [ContinuousLinearMap.reApplyInnerSelf_apply]
  · -- Normalize a nonzero vector and rescale the unit-sphere inequality.
    have hv_norm : 0 < ‖v‖ := norm_pos_iff.mpr hv
    have hunit : ‖v‖⁻¹ • v ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1 := by
      simp [norm_smul, hv_norm.ne']
    have hscaled := mul_le_mul_of_nonneg_right (hμ_lower _ hunit) (sq_nonneg ‖v‖)
    rw [ContinuousLinearMap.reApplyInnerSelf_smul] at hscaled
    simp only [Real.norm_eq_abs, abs_inv, abs_of_pos hv_norm, inv_pow] at hscaled
    calc
      μ * ‖v‖ ^ 2 ≤ (‖v‖ ^ 2)⁻¹ * T.reApplyInnerSelf v * ‖v‖ ^ 2 := hscaled
      _ = T.reApplyInnerSelf v := by field_simp
      _ = ContinuousLinearMap.reApplyInnerSelf
          ((Matrix.toEuclideanCLM :
            Matrix (Fin n) (Fin n) ℝ ≃⋆ₐ[ℝ]
              (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))) A) v := rfl

/-- A differentiable scalar function whose gradient is differentiable has the expected
second-order Peano remainder at a critical point. -/
private lemma secondOrderRemainder_isLittleO {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (F : E → ℝ) (x₀ : E) (T : E →L[ℝ] E)
    (h_diff : ∀ᶠ y in 𝓝 x₀, DifferentiableAt ℝ F y)
    (h_gradient : gradient F x₀ = 0)
    (h_deriv : HasFDerivAt (gradient F) T x₀)
    (h_symmetric : (T : E →ₗ[ℝ] E).IsSymmetric) :
    (fun y ↦ F y - F x₀ - (2 : ℝ)⁻¹ * T.reApplyInnerSelf (y - x₀)) =o[𝓝 x₀]
      (fun y ↦ ‖y - x₀‖ ^ 2) := by
  -- The derivative remainder is little-o of the displacement by differentiability of the gradient.
  have h_gradient_remainder :
      (fun y ↦ gradient F y - T (y - x₀)) =o[𝓝 x₀] (fun y ↦ y - x₀) := by
    simpa only [h_gradient, sub_zero] using h_deriv.isLittleO
  have h_dual_remainder :
      (fun y ↦ InnerProductSpace.toDual ℝ E (gradient F y - T (y - x₀))) =o[𝓝 x₀]
        (fun y ↦ ‖y - x₀‖) := by
    rw [Asymptotics.isLittleO_iff] at h_gradient_remainder ⊢
    intro c hc
    simpa only [LinearIsometryEquiv.norm_map, norm_norm] using h_gradient_remainder hc
  obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff_ball.mp h_diff
  let s := Metric.closedBall x₀ (r / 2)
  have hx₀s : x₀ ∈ s := Metric.mem_closedBall_self (by positivity)
  have h_differentiable_on : ∀ y ∈ s, DifferentiableAt ℝ F y := by
    intro y hy
    exact hball y (Metric.closedBall_subset_ball (half_lt_self hr) hy)
  have h_quadratic_deriv (y : E) :
      HasFDerivAt
        ((2 : ℝ)⁻¹ • (T.reApplyInnerSelf ∘ fun z ↦ z - x₀))
        (InnerProductSpace.toDual ℝ E (T (y - x₀))) y := by
    have h_raw := (h_symmetric.hasStrictFDerivAt_reApplyInnerSelf (y - x₀)).hasFDerivAt.comp y
      (hasFDerivAt_sub_const x₀)
    refine (h_raw.const_smul (2 : ℝ)⁻¹).congr_fderiv ?_
    ext z
    simp [InnerProductSpace.toDual_apply_apply, innerSL_apply_apply]
  have h_remainder_deriv (y : E) (hy : DifferentiableAt ℝ F y) :
      HasFDerivAt
        ((fun z ↦ F z - F x₀) -
          ((2 : ℝ)⁻¹ • (T.reApplyInnerSelf ∘ fun z ↦ z - x₀)))
        (InnerProductSpace.toDual ℝ E (gradient F y - T (y - x₀))) y := by
    have h_raw := (hy.hasGradientAt.hasFDerivAt.sub_const (F x₀)).sub (h_quadratic_deriv y)
    simpa only [map_sub] using h_raw
  have h_dual_remainder_within :
      (fun y ↦ InnerProductSpace.toDual ℝ E (gradient F y - T (y - x₀)))
          =o[𝓝[s] x₀] (fun y ↦ ‖y - x₀‖ ^ 1) := by
    simpa only [pow_one] using h_dual_remainder.mono
      (nhdsWithin_le_nhds : 𝓝[s] x₀ ≤ 𝓝 x₀)
  have h_integrated := (convex_closedBall x₀ (r / 2)).isLittleO_pow_succ hx₀s
    (fun y hy ↦ (h_remainder_deriv y (h_differentiable_on y hy)).hasFDerivWithinAt)
    h_dual_remainder_within (n := 1)
  -- The modeled remainder vanishes at the base point, so the integrated estimate is the goal.
  rw [nhdsWithin_eq_nhds.mpr (Metric.closedBall_mem_nhds x₀ (half_pos hr))] at h_integrated
  simpa [s, Function.comp_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
    ContinuousLinearMap.reApplyInnerSelf_apply] using h_integrated

/-- A coercive quadratic model with a second-order Peano remainder gives two-sided local
quadratic bounds. -/
private lemma eventuallyQuadraticBounds {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (F : E → ℝ) (x₀ : E) (T : E →L[ℝ] E) (μ : ℝ) (hμ : 0 < μ)
    (h_coercive : ∀ v : E, μ * ‖v‖ ^ 2 ≤ T.reApplyInnerSelf v)
    (h_remainder :
      (fun y ↦ F y - F x₀ - (2 : ℝ)⁻¹ * T.reApplyInnerSelf (y - x₀)) =o[𝓝 x₀]
        (fun y ↦ ‖y - x₀‖ ^ 2)) :
    ∃ m > 0, ∃ M > 0, ∀ᶠ y in 𝓝 x₀,
      m * ‖y - x₀‖ ^ 2 ≤ F y - F x₀ ∧
        F y - F x₀ ≤ M * ‖y - x₀‖ ^ 2 := by
  -- The operator norm supplies the matching global upper bound for the quadratic form.
  have h_quadratic_upper (v : E) :
      T.reApplyInnerSelf v ≤ ‖T‖ * ‖v‖ ^ 2 := by
    calc
      T.reApplyInnerSelf v = inner ℝ (T v) v := by
        simp [ContinuousLinearMap.reApplyInnerSelf_apply]
      _ ≤ ‖T v‖ * ‖v‖ := real_inner_le_norm _ _
      _ ≤ (‖T‖ * ‖v‖) * ‖v‖ :=
        mul_le_mul_of_nonneg_right (T.le_opNorm v) (norm_nonneg v)
      _ = ‖T‖ * ‖v‖ ^ 2 := by ring
  have h_remainder_bound := h_remainder.bound (by positivity : 0 < μ / 4)
  refine ⟨μ / 4, by positivity, ‖T‖ / 2 + μ / 4, ?_, ?_⟩
  · have hT_nonneg : 0 ≤ ‖T‖ := norm_nonneg T
    positivity
  · -- Add the small remainder to the lower and upper estimates for the quadratic model.
    filter_upwards [h_remainder_bound] with y hy
    have hy_abs :
        |F y - F x₀ - (2 : ℝ)⁻¹ * T.reApplyInnerSelf (y - x₀)| ≤
          μ / 4 * ‖y - x₀‖ ^ 2 := by
      simpa only [Real.norm_eq_abs, norm_pow, norm_norm, abs_pow, abs_norm] using hy
    have hy_lower := (abs_le.mp hy_abs).1
    have hy_upper := (abs_le.mp hy_abs).2
    have hq_lower := h_coercive (y - x₀)
    have hq_upper := h_quadratic_upper (y - x₀)
    constructor
    · nlinarith
    · nlinarith

/-- Every convergent, eventually nonstationary sequence generated by exact nonnegative
line searches near a critical point with positive-definite Hessian has Q-order at least one. -/
theorem hasOrderAtLeast_one_of_exactLineSearch {n : ℕ}
    (F : EuclideanSpace ℝ (Fin n) → ℝ) (xStar : EuclideanSpace ℝ (Fin n))
    (x : ℕ → EuclideanSpace ℝ (Fin n)) (h_smooth : ContDiffAt ℝ 2 F xStar)
    (h_gradient : gradient F xStar = 0)
    (h_hessian : Matrix.PosDef
      ((Matrix.toEuclideanCLM :
          Matrix (Fin n) (Fin n) ℝ ≃⋆ₐ[ℝ]
            (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))).symm
        (fderiv ℝ (gradient F) xStar)))
    (h_tendsto : Filter.Tendsto x Filter.atTop (𝓝 xStar))
    (h_ne : ∀ᶠ k in Filter.atTop, x k ≠ xStar)
    (h_step : ∀ k, ∃ (d : EuclideanSpace ℝ (Fin n)) (α : ℝ),
      LineSearch.IsExact F (x k) d α ∧ x (k + 1) = x k + α • d) :
    HasOrderAtLeast x xStar 1 := by
  let H : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) :=
    fderiv ℝ (gradient F) xStar
  let A : Matrix (Fin n) (Fin n) ℝ :=
    (Matrix.toEuclideanCLM :
      Matrix (Fin n) (Fin n) ℝ ≃⋆ₐ[ℝ]
        (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))).symm H
  -- Positive definiteness supplies symmetry and a uniform lower bound for the Hessian model.
  have hA : A.PosDef := by
    simpa only [A, H] using h_hessian
  obtain ⟨μ, hμ, h_coercive_A⟩ := positiveDefiniteMatrixQuadraticLowerBound A hA
  have h_coercive : ∀ v : EuclideanSpace ℝ (Fin n),
      μ * ‖v‖ ^ 2 ≤ H.reApplyInnerSelf v := by
    intro v
    simpa [A, H] using h_coercive_A v
  have h_symmetric : (H : EuclideanSpace ℝ (Fin n) →ₗ[ℝ]
      EuclideanSpace ℝ (Fin n)).IsSymmetric := by
    have hA_symmetric :
        (((Matrix.toEuclideanCLM :
          Matrix (Fin n) (Fin n) ℝ ≃⋆ₐ[ℝ]
            (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))) A) :
              EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin n)).IsSymmetric := by
      rw [Matrix.coe_toEuclideanCLM_eq_toEuclideanLin]
      exact Matrix.isSymmetric_toEuclideanLin_iff.mpr hA.isHermitian
    have h_operator :
        (Matrix.toEuclideanCLM :
          Matrix (Fin n) (Fin n) ℝ ≃⋆ₐ[ℝ]
            (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))) A = H := by
      simp only [A, StarAlgEquiv.apply_symm_apply]
    rw [h_operator] at hA_symmetric
    exact hA_symmetric
  -- C² regularity provides differentiability of `F` nearby and differentiability of its gradient.
  have h_diff : ∀ᶠ y in 𝓝 xStar, DifferentiableAt ℝ F y := by
    filter_upwards [h_smooth.eventually (by norm_num)] with y hy
    exact hy.differentiableAt (by norm_num)
  have h_gradient_contDiff : ContDiffAt ℝ 1 (gradient F) xStar := by
    have h_fderiv_contDiff : ContDiffAt ℝ 1 (fderiv ℝ F) xStar :=
      h_smooth.fderiv_right (m := 1) (by norm_num)
    unfold gradient
    simpa only [Function.comp_def, LinearIsometry.coe_toContinuousLinearMap,
      LinearIsometryEquiv.coe_toLinearIsometry] using
      h_fderiv_contDiff.continuousLinearMap_comp
        (InnerProductSpace.toDual ℝ
          (EuclideanSpace ℝ (Fin n))).symm.toLinearIsometry.toContinuousLinearMap
  have h_gradient_deriv : HasFDerivAt (gradient F) H xStar := by
    simpa only [H] using h_gradient_contDiff.differentiableAt (by norm_num) |>.hasFDerivAt
  have h_remainder := secondOrderRemainder_isLittleO F xStar H h_diff h_gradient
    h_gradient_deriv h_symmetric
  obtain ⟨m, hm, M, hM, h_bounds⟩ :=
    eventuallyQuadraticBounds F xStar H μ hμ h_coercive h_remainder
  -- Exactness at the feasible step `0` makes the objective nonincreasing along the iterates.
  have h_descent (k : ℕ) : F (x (k + 1)) ≤ F (x k) := by
    obtain ⟨d, α, h_exact, h_update⟩ := h_step k
    rw [LineSearch.isExact_iff] at h_exact
    rw [h_update]
    simpa using h_exact.2 (show (0 : ℝ) ∈ Set.Ici 0 by simp)
  have h_bounds_current := h_tendsto.eventually h_bounds
  have h_bounds_next :=
    (h_tendsto.comp (Filter.tendsto_add_atTop_nat 1)).eventually h_bounds
  rw [hasOrderAtLeast_iff]
  refine ⟨h_tendsto, h_ne, le_rfl, Real.sqrt (M / m), Real.sqrt_pos.2 (div_pos hM hm), ?_⟩
  -- The quadratic sandwich turns objective descent into a uniform adjacent-error bound.
  filter_upwards [h_bounds_current, h_bounds_next] with k hk hk_next
  simp only [Function.comp_apply] at hk_next
  have h_squared :
      m * ‖x (k + 1) - xStar‖ ^ 2 ≤ M * ‖x k - xStar‖ ^ 2 := by
    linarith [hk_next.1, h_descent k, hk.2]
  have h_ratio_nonneg : 0 ≤ M / m := (div_pos hM hm).le
  have h_squared_ratio :
      ‖x (k + 1) - xStar‖ ^ 2 ≤ (M / m) * ‖x k - xStar‖ ^ 2 := by
    rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ hm).2
    simpa only [mul_comm, mul_left_comm, mul_assoc] using h_squared
  have h_squared_sqrt :
      ‖x (k + 1) - xStar‖ ^ 2 ≤
        (Real.sqrt (M / m) * ‖x k - xStar‖) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt h_ratio_nonneg]
    exact h_squared_ratio
  simpa only [error_apply, Real.rpow_one] using
    (sq_le_sq₀ (norm_nonneg (x (k + 1) - xStar))
      (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg (x k - xStar)))).mp h_squared_sqrt

end QConvergence
