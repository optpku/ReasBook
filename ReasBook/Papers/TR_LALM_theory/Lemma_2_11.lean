/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@5bf5af722d85bd5c98368c41c4066124a15e8fd3:ReasBook/Papers/TR_LALM_theory/README.md (formalization contributor).
-/

module

public import TR_LALM_theory.Definition_2_2.KKT
import TR_LALM_theory.Lemma_2_6
import TR_LALM_theory.Lemma_2_8
public import TR_LALM_theory.Lemma_2_11.Residual

public section

namespace LALM

variable {n m : ℕ}
variable {f : EuclideanSpace ℝ (Fin n) → ℝ}
variable {c : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m)}

namespace Run

variable {x₀ : EuclideanSpace ℝ (Fin n)}
variable {multiplier₀ : EuclideanSpace ℝ (Fin m)}

/-- Helper for Lemma 2.11: on an admissible segment, the penalty-scaled image
of the constraint linearization error is controlled by the step norm. -/
private lemma normPenaltyConstraintGradientError_le
    (h : EqualityConstrained.Regularity f c)
    (params : Parameters h x₀ multiplier₀)
    (run : Run f c params.rho params.beta x₀ multiplier₀)
    (j : ℕ)
    (hsegment : segment ℝ (run.point j) (run.point (j + 1)) ⊆ h.region)
    (hstep : ‖run.step j‖ ≤ params.delta) :
    ‖(params.rho : ℝ) •
        EqualityConstrained.constraintGradient c (run.point j) (run.error j)‖ ≤
      params.rho * h.constraintGradientBound * linearizationConstant h * params.delta *
        ‖run.step j‖ := by
  -- First pass from the operator norm to the quadratic linearization-error bound.
  have hx : run.point j ∈ h.region := hsegment (left_mem_segment ℝ _ _)
  have hoperator := h.norm_constraintGradient_le (run.point j) hx
  have herror := run.error_le h j hsegment
  have happlication :
      ‖EqualityConstrained.constraintGradient c (run.point j) (run.error j)‖ ≤
        h.constraintGradientBound * ‖run.error j‖ :=
    (EqualityConstrained.constraintGradient c (run.point j)).le_opNorm (run.error j) |>.trans
      (mul_le_mul_of_nonneg_right hoperator (norm_nonneg _))
  have hlinearized :
      ‖EqualityConstrained.constraintGradient c (run.point j) (run.error j)‖ ≤
        h.constraintGradientBound *
          (linearizationConstant h * ‖run.step j‖ ^ 2) :=
    happlication.trans
      (mul_le_mul_of_nonneg_left herror (NNReal.coe_nonneg h.constraintGradientBound))
  -- Use the admissible step radius to turn the quadratic error into a linear bound.
  have hstepProduct :
      ‖run.step j‖ * ‖run.step j‖ ≤ params.delta * ‖run.step j‖ :=
    mul_le_mul_of_nonneg_right hstep (norm_nonneg _)
  have hcoefficientNonneg :
      0 ≤ (params.rho : ℝ) * h.constraintGradientBound * linearizationConstant h := by
    positivity
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos run.rho_pos]
  calc
    params.rho *
        ‖EqualityConstrained.constraintGradient c (run.point j) (run.error j)‖ ≤
        params.rho *
          (h.constraintGradientBound *
            (linearizationConstant h * ‖run.step j‖ ^ 2)) :=
      mul_le_mul_of_nonneg_left hlinearized run.rho_pos.le
    _ = (params.rho * h.constraintGradientBound * linearizationConstant h) *
        (‖run.step j‖ * ‖run.step j‖) := by ring
    _ ≤ (params.rho * h.constraintGradientBound * linearizationConstant h) *
        (params.delta * ‖run.step j‖) :=
      mul_le_mul_of_nonneg_left hstepProduct hcoefficientNonneg
    _ = params.rho * h.constraintGradientBound * linearizationConstant h * params.delta *
        ‖run.step j‖ := by ring

/-- Helper for Lemma 2.11: stationarity at the next iterate is bounded by the
current step with the primal comparison constant. -/
private lemma normStationarityPointSucc_le
    (h : EqualityConstrained.Regularity f c)
    (params : Parameters h x₀ multiplier₀)
    (run : Run f c params.rho params.beta x₀ multiplier₀)
    {N k : ℕ} (h_admissible : run.IsAdmissiblePrefix h N) (hk : k < N) :
    ‖KKT.stationarity f c (run.point (k + 1)) (run.multiplier (k + 1))‖ ≤
      primalComparisonConstant h params.delta params.beta params.rho
        params.multiplierBound * ‖run.step k‖ := by
  -- Extract the endpoint regularity and uniform bounds from the admissible prefix.
  have hsegments := (run.isAdmissiblePrefix_iff h N).1 h_admissible
  have hsegment := hsegments k hk
  have hxCurrent : run.point k ∈ h.region :=
    hsegment (left_mem_segment ℝ _ _)
  have hxNext : run.point (k + 1) ∈ h.region :=
    hsegment (right_mem_segment ℝ _ _)
  have hstep := norm_step_le h params run h_admissible hk
  have hmultiplier :=
    norm_multiplier_le h params run h_admissible (show k + 1 ≤ N by omega)
  have herror :=
    normPenaltyConstraintGradientError_le h params run k hsegment hstep
  -- Rearrange the perturbed multiplier identity into the three stationarity terms.
  have hstationarityIdentity :
      KKT.stationarity f c (run.point (k + 1)) (run.multiplier (k + 1)) =
        (-(params.beta : ℝ) • run.step k +
          (params.rho : ℝ) •
            EqualityConstrained.constraintGradient c (run.point k) (run.error k)) +
        (gradient f (run.point (k + 1)) - gradient f (run.point k)) +
        (EqualityConstrained.constraintGradient c (run.point (k + 1)) -
          EqualityConstrained.constraintGradient c (run.point k))
            (run.multiplier (k + 1)) := by
    rw [KKT.stationarity_def]
    simp only [sub_apply]
    linear_combination (norm := module) run.perturbedMultiplierIdentity k
  -- The point update identifies all regularity distances with the current step norm.
  have hpointDistance :
      dist (run.point (k + 1)) (run.point k) = ‖run.step k‖ := by
    rw [run.point_succ, dist_eq_norm, add_sub_cancel_left]
  have hgradientDifference :
      ‖gradient f (run.point (k + 1)) - gradient f (run.point k)‖ ≤
        h.gradientLipschitz * ‖run.step k‖ := by
    calc
      ‖gradient f (run.point (k + 1)) - gradient f (run.point k)‖ =
          dist (gradient f (run.point (k + 1))) (gradient f (run.point k)) :=
        (dist_eq_norm _ _).symm
      _ ≤ h.gradientLipschitz * dist (run.point (k + 1)) (run.point k) :=
        h.lipschitzOn_gradient.dist_le_mul
          (run.point (k + 1)) hxNext (run.point k) hxCurrent
      _ = h.gradientLipschitz * ‖run.step k‖ := by rw [hpointDistance]
  have hoperatorDifference :
      ‖EqualityConstrained.constraintGradient c (run.point (k + 1)) -
          EqualityConstrained.constraintGradient c (run.point k)‖ ≤
        h.constraintGradientLipschitz * ‖run.step k‖ := by
    calc
      ‖EqualityConstrained.constraintGradient c (run.point (k + 1)) -
          EqualityConstrained.constraintGradient c (run.point k)‖ =
          dist (EqualityConstrained.constraintGradient c (run.point (k + 1)))
            (EqualityConstrained.constraintGradient c (run.point k)) :=
        (dist_eq_norm _ _).symm
      _ ≤ h.constraintGradientLipschitz *
          dist (run.point (k + 1)) (run.point k) :=
        h.lipschitzOn_constraintGradient.dist_le_mul
          (run.point (k + 1)) hxNext (run.point k) hxCurrent
      _ = h.constraintGradientLipschitz * ‖run.step k‖ := by
        rw [hpointDistance]
  have hoperatorApplied :
      ‖(EqualityConstrained.constraintGradient c (run.point (k + 1)) -
          EqualityConstrained.constraintGradient c (run.point k))
            (run.multiplier (k + 1))‖ ≤
        h.constraintGradientLipschitz * params.multiplierBound * ‖run.step k‖ := by
    calc
      ‖(EqualityConstrained.constraintGradient c (run.point (k + 1)) -
          EqualityConstrained.constraintGradient c (run.point k))
            (run.multiplier (k + 1))‖ ≤
          ‖EqualityConstrained.constraintGradient c (run.point (k + 1)) -
            EqualityConstrained.constraintGradient c (run.point k)‖ *
              ‖run.multiplier (k + 1)‖ :=
        (EqualityConstrained.constraintGradient c (run.point (k + 1)) -
          EqualityConstrained.constraintGradient c (run.point k)).le_opNorm
            (run.multiplier (k + 1))
      _ ≤ (h.constraintGradientLipschitz * ‖run.step k‖) *
          params.multiplierBound :=
        mul_le_mul hoperatorDifference hmultiplier (norm_nonneg _)
          (mul_nonneg (NNReal.coe_nonneg _) (norm_nonneg _))
      _ = h.constraintGradientLipschitz * params.multiplierBound *
          ‖run.step k‖ := by ring
  -- Combine the proximal and linearization-error terms into the primal constant.
  have hproximalError :
      ‖-(params.beta : ℝ) • run.step k +
          (params.rho : ℝ) •
            EqualityConstrained.constraintGradient c (run.point k) (run.error k)‖ ≤
        primalConstant h params.delta params.beta params.rho * ‖run.step k‖ := by
    calc
      ‖-(params.beta : ℝ) • run.step k +
          (params.rho : ℝ) •
            EqualityConstrained.constraintGradient c (run.point k) (run.error k)‖ ≤
          ‖-(params.beta : ℝ) • run.step k‖ +
            ‖(params.rho : ℝ) •
              EqualityConstrained.constraintGradient c (run.point k) (run.error k)‖ :=
        norm_add_le _ _
      _ = params.beta * ‖run.step k‖ +
          ‖(params.rho : ℝ) •
            EqualityConstrained.constraintGradient c (run.point k) (run.error k)‖ := by
        rw [norm_smul, Real.norm_eq_abs, abs_neg, abs_of_pos run.beta_pos]
      _ ≤ params.beta * ‖run.step k‖ +
          params.rho * h.constraintGradientBound * linearizationConstant h * params.delta *
            ‖run.step k‖ := add_le_add_right herror _
      _ = primalConstant h params.delta params.beta params.rho * ‖run.step k‖ := by
        rw [primalConstant_def]
        ring
  -- Apply the three termwise estimates and collect their named coefficients.
  rw [hstationarityIdentity]
  calc
    ‖(-(params.beta : ℝ) • run.step k +
          (params.rho : ℝ) •
            EqualityConstrained.constraintGradient c (run.point k) (run.error k)) +
        (gradient f (run.point (k + 1)) - gradient f (run.point k)) +
        (EqualityConstrained.constraintGradient c (run.point (k + 1)) -
          EqualityConstrained.constraintGradient c (run.point k))
            (run.multiplier (k + 1))‖ ≤
        ‖-(params.beta : ℝ) • run.step k +
          (params.rho : ℝ) •
            EqualityConstrained.constraintGradient c (run.point k) (run.error k)‖ +
        ‖gradient f (run.point (k + 1)) - gradient f (run.point k)‖ +
        ‖(EqualityConstrained.constraintGradient c (run.point (k + 1)) -
          EqualityConstrained.constraintGradient c (run.point k))
            (run.multiplier (k + 1))‖ := by
      have hfirst := norm_add_le
        (-(params.beta : ℝ) • run.step k +
          (params.rho : ℝ) • EqualityConstrained.constraintGradient c
            (run.point k) (run.error k))
        (gradient f (run.point (k + 1)) - gradient f (run.point k))
      have hsecond := norm_add_le
        ((-(params.beta : ℝ) • run.step k +
            (params.rho : ℝ) • EqualityConstrained.constraintGradient c
              (run.point k) (run.error k)) +
          (gradient f (run.point (k + 1)) - gradient f (run.point k)))
        ((EqualityConstrained.constraintGradient c (run.point (k + 1)) -
          EqualityConstrained.constraintGradient c (run.point k))
            (run.multiplier (k + 1)))
      linarith
    _ ≤ primalConstant h params.delta params.beta params.rho * ‖run.step k‖ +
        h.gradientLipschitz * ‖run.step k‖ +
        h.constraintGradientLipschitz * params.multiplierBound * ‖run.step k‖ :=
      add_le_add (add_le_add hproximalError hgradientDifference) hoperatorApplied
    _ = primalComparisonConstant h params.delta params.beta params.rho
        params.multiplierBound * ‖run.step k‖ := by
      rw [primalComparisonConstant_def]
      ring

/-- Helper for Lemma 2.11: the multiplier update identifies squared feasibility
with the penalty-scaled squared multiplier increment. -/
private lemma constraintNormSq_eq_multiplierIncrementNormSqDiv
    {ρ β : ℝ} (run : Run f c ρ β x₀ multiplier₀) (k : ℕ) :
    ‖c (run.point (k + 1))‖ ^ 2 =
      ‖run.multiplier (k + 1) - run.multiplier k‖ ^ 2 / ρ ^ 2 := by
  -- Normalize the update law and cancel the positive penalty factor.
  rw [run.multiplier_succ k, add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
    abs_of_pos run.rho_pos]
  field_simp [ne_of_gt run.rho_pos]

/-- Lemma 2.11: on every deterministic admissible prefix, the squared aggregate
KKT residual after iteration `k` is controlled by the current and preceding
squared step norms. -/
theorem residual_sq_le (h : EqualityConstrained.Regularity f c)
    (params : Parameters h x₀ multiplier₀)
    (run : Run f c params.rho params.beta x₀ multiplier₀)
    {N k : ℕ} (h_admissible : run.IsAdmissiblePrefix h N)
    (hk_pos : 1 ≤ k) (hk : k < N) :
    KKT.residual f c (run.point (k + 1)) (run.multiplier (k + 1)) ^ 2 ≤
      residualComparisonConstant h params.delta params.beta params.rho
        params.multiplierBound *
        (‖run.step k‖ ^ 2 + ‖run.step (k - 1)‖ ^ 2) := by
  -- Bound stationarity by the current step and square the nonnegative inequality.
  have hstationarity :=
    normStationarityPointSucc_le h params run h_admissible hk
  have hcomparisonNonneg :
      0 ≤ primalComparisonConstant h params.delta params.beta params.rho
        params.multiplierBound := by
    rw [primalComparisonConstant_def, primalConstant_def]
    positivity
  have hstationaritySquare :
      ‖KKT.stationarity f c (run.point (k + 1)) (run.multiplier (k + 1))‖ ^ 2 ≤
        primalComparisonConstant h params.delta params.beta params.rho
          params.multiplierBound ^ 2 * ‖run.step k‖ ^ 2 := by
    have hsquared :=
      (sq_le_sq₀ (norm_nonneg _)
        (mul_nonneg hcomparisonNonneg (norm_nonneg _))).2 hstationarity
    simpa only [mul_pow] using hsquared
  have hstationarityExpanded :
      ‖KKT.stationarity f c (run.point (k + 1)) (run.multiplier (k + 1))‖ ^ 2 ≤
        primalComparisonConstant h params.delta params.beta params.rho
          params.multiplierBound ^ 2 *
          (‖run.step k‖ ^ 2 + ‖run.step (k - 1)‖ ^ 2) :=
    hstationaritySquare.trans
      (mul_le_mul_of_nonneg_left (le_add_of_nonneg_right (sq_nonneg _)) (sq_nonneg _))
  -- Transport feasibility to the multiplier increment and apply Lemma 2.8.
  have hmultiplier :=
    norm_multiplier_succ_sub_sq_le h params run h_admissible hk_pos hk
  have hfeasibility :
      ‖c (run.point (k + 1))‖ ^ 2 ≤
        multiplierPrimalConstant h params.delta params.beta params.rho
            params.multiplierBound / params.rho ^ 2 *
          (‖run.step k‖ ^ 2 + ‖run.step (k - 1)‖ ^ 2) := by
    calc
      ‖c (run.point (k + 1))‖ ^ 2 =
          ‖run.multiplier (k + 1) - run.multiplier k‖ ^ 2 / params.rho ^ 2 :=
        constraintNormSq_eq_multiplierIncrementNormSqDiv run k
      _ ≤ (multiplierPrimalConstant h params.delta params.beta params.rho
            params.multiplierBound *
          (‖run.step k‖ ^ 2 + ‖run.step (k - 1)‖ ^ 2)) / params.rho ^ 2 :=
        div_le_div_of_nonneg_right hmultiplier (sq_nonneg _)
      _ = multiplierPrimalConstant h params.delta params.beta params.rho
            params.multiplierBound / params.rho ^ 2 *
          (‖run.step k‖ ^ 2 + ‖run.step (k - 1)‖ ^ 2) := by ring
  -- Expose the two residual components, add their estimates, and factor the sum.
  calc
    KKT.residual f c (run.point (k + 1)) (run.multiplier (k + 1)) ^ 2 =
        ‖KKT.stationarity f c (run.point (k + 1)) (run.multiplier (k + 1))‖ ^ 2 +
          ‖c (run.point (k + 1))‖ ^ 2 := by
      rw [KKT.residual_def,
        Real.sq_sqrt (add_nonneg (sq_nonneg _) (sq_nonneg _))]
    _ ≤ primalComparisonConstant h params.delta params.beta params.rho
            params.multiplierBound ^ 2 *
          (‖run.step k‖ ^ 2 + ‖run.step (k - 1)‖ ^ 2) +
        multiplierPrimalConstant h params.delta params.beta params.rho
            params.multiplierBound / params.rho ^ 2 *
          (‖run.step k‖ ^ 2 + ‖run.step (k - 1)‖ ^ 2) :=
      add_le_add hstationarityExpanded hfeasibility
    _ = residualComparisonConstant h params.delta params.beta params.rho
        params.multiplierBound *
          (‖run.step k‖ ^ 2 + ‖run.step (k - 1)‖ ^ 2) := by
      rw [residualComparisonConstant_def]
      ring

end Run

end LALM

end
