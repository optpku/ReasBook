/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@5bf5af722d85bd5c98368c41c4066124a15e8fd3:ReasBook/Papers/TR_LALM_theory/README.md (formalization contributor).
-/

module

public import TR_LALM_theory.Assumption_2_3.Parameters
import TR_LALM_theory.Lemma_2_6

public section

namespace LALM.Run

variable {n m : ℕ}
variable {f : EuclideanSpace ℝ (Fin n) → ℝ}
variable {c : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m)}
variable {x₀ : EuclideanSpace ℝ (Fin n)}
variable {multiplier₀ : EuclideanSpace ℝ (Fin m)}

/-- Helper for Lemma 2.8: subtracting the perturbed multiplier identities at two
successive iterations expresses the constraint-gradient image of the multiplier
increment in terms of the two steps and regularity differences. -/
private lemma constraintGradientMultiplierIncrement
    {ρ β : ℝ} (run : Run f c ρ β x₀ multiplier₀) (k : ℕ) (hk_pos : 1 ≤ k) :
    EqualityConstrained.constraintGradient c (run.point k)
        (run.multiplier (k + 1) - run.multiplier k) =
      (-β • run.step k +
          ρ • EqualityConstrained.constraintGradient c (run.point k) (run.error k)) +
        (β • run.step (k - 1) -
          ρ • EqualityConstrained.constraintGradient c (run.point (k - 1))
            (run.error (k - 1))) +
        (gradient f (run.point (k - 1)) - gradient f (run.point k)) +
        (EqualityConstrained.constraintGradient c (run.point (k - 1)) -
          EqualityConstrained.constraintGradient c (run.point k)) (run.multiplier k) := by
  -- Normalize the predecessor successor before subtracting the two identities.
  have hpred : k - 1 + 1 = k := Nat.sub_add_cancel hk_pos
  have hcurrent := run.perturbedMultiplierIdentity k
  have hprevious := run.perturbedMultiplierIdentity (k - 1)
  rw [hpred] at hprevious
  simp only [map_sub, sub_apply]
  linear_combination (norm := module) hcurrent - hprevious

/-- Helper for Lemma 2.8: on an admissible segment, a step bounded by `delta`
controls the scaled constraint-gradient image of its linearization error. -/
private lemma normScaledConstraintGradientError_le
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
  -- Bound the operator application and then insert the quadratic error estimate.
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

/-- Helper for Lemma 2.8: the constraint-gradient image of a multiplier increment
is controlled by the current step and the preceding step with the named primal
comparison constants. -/
private lemma normConstraintGradientMultiplierIncrement_le
    (h : EqualityConstrained.Regularity f c)
    (params : Parameters h x₀ multiplier₀)
    (run : Run f c params.rho params.beta x₀ multiplier₀)
    {N k : ℕ} (h_admissible : run.IsAdmissiblePrefix h N)
    (hk_pos : 1 ≤ k) (hk : k < N) :
    ‖EqualityConstrained.constraintGradient c (run.point k)
        (run.multiplier (k + 1) - run.multiplier k)‖ ≤
      primalConstant h params.delta params.beta params.rho * ‖run.step k‖ +
        primalComparisonConstant h params.delta params.beta params.rho
          params.multiplierBound * ‖run.step (k - 1)‖ := by
  -- Extract the two admissible segments and their endpoint memberships.
  have hpred : k - 1 + 1 = k := Nat.sub_add_cancel hk_pos
  have hk_previous : k - 1 < N := by omega
  have hsegments := (run.isAdmissiblePrefix_iff h N).1 h_admissible
  have hsegmentCurrent := hsegments k hk
  have hsegmentPrevious := hsegments (k - 1) hk_previous
  have hxCurrent : run.point k ∈ h.region :=
    hsegmentCurrent (left_mem_segment ℝ _ _)
  have hxPrevious : run.point (k - 1) ∈ h.region :=
    hsegmentPrevious (left_mem_segment ℝ _ _)
  have hstepCurrent := norm_step_le h params run h_admissible hk
  have hstepPrevious := norm_step_le h params run h_admissible hk_previous
  have hmultiplier := norm_multiplier_le h params run h_admissible (show k ≤ N by omega)
  have herrorCurrent :=
    normScaledConstraintGradientError_le h params run k hsegmentCurrent hstepCurrent
  have herrorPrevious :=
    normScaledConstraintGradientError_le h params run (k - 1) hsegmentPrevious hstepPrevious
  -- The point update identifies both regularity distances with the preceding step norm.
  have hpointDistance :
      dist (run.point (k - 1)) (run.point k) = ‖run.step (k - 1)‖ := by
    calc
      dist (run.point (k - 1)) (run.point k) =
          dist (run.point (k - 1)) (run.point (k - 1 + 1)) := by rw [hpred]
      _ = ‖run.step (k - 1)‖ := by
        rw [run.point_succ, dist_eq_norm, norm_sub_rev, add_sub_cancel_left]
  have hgradientDifference :
      ‖gradient f (run.point (k - 1)) - gradient f (run.point k)‖ ≤
        h.gradientLipschitz * ‖run.step (k - 1)‖ := by
    calc
      ‖gradient f (run.point (k - 1)) - gradient f (run.point k)‖ =
          dist (gradient f (run.point (k - 1))) (gradient f (run.point k)) :=
        (dist_eq_norm _ _).symm
      _ ≤ h.gradientLipschitz * dist (run.point (k - 1)) (run.point k) :=
        h.lipschitzOn_gradient.dist_le_mul
          (run.point (k - 1)) hxPrevious (run.point k) hxCurrent
      _ = h.gradientLipschitz * ‖run.step (k - 1)‖ := by rw [hpointDistance]
  have hoperatorDifference :
      ‖EqualityConstrained.constraintGradient c (run.point (k - 1)) -
          EqualityConstrained.constraintGradient c (run.point k)‖ ≤
        h.constraintGradientLipschitz * ‖run.step (k - 1)‖ := by
    calc
      ‖EqualityConstrained.constraintGradient c (run.point (k - 1)) -
          EqualityConstrained.constraintGradient c (run.point k)‖ =
          dist (EqualityConstrained.constraintGradient c (run.point (k - 1)))
            (EqualityConstrained.constraintGradient c (run.point k)) :=
        (dist_eq_norm _ _).symm
      _ ≤ h.constraintGradientLipschitz *
          dist (run.point (k - 1)) (run.point k) :=
        h.lipschitzOn_constraintGradient.dist_le_mul
          (run.point (k - 1)) hxPrevious (run.point k) hxCurrent
      _ = h.constraintGradientLipschitz * ‖run.step (k - 1)‖ := by
        rw [hpointDistance]
  have hoperatorApplied :
      ‖(EqualityConstrained.constraintGradient c (run.point (k - 1)) -
          EqualityConstrained.constraintGradient c (run.point k)) (run.multiplier k)‖ ≤
        h.constraintGradientLipschitz * params.multiplierBound *
          ‖run.step (k - 1)‖ := by
    calc
      ‖(EqualityConstrained.constraintGradient c (run.point (k - 1)) -
          EqualityConstrained.constraintGradient c (run.point k)) (run.multiplier k)‖ ≤
          ‖EqualityConstrained.constraintGradient c (run.point (k - 1)) -
            EqualityConstrained.constraintGradient c (run.point k)‖ *
              ‖run.multiplier k‖ :=
        (EqualityConstrained.constraintGradient c (run.point (k - 1)) -
          EqualityConstrained.constraintGradient c (run.point k)).le_opNorm
            (run.multiplier k)
      _ ≤ (h.constraintGradientLipschitz * ‖run.step (k - 1)‖) *
          params.multiplierBound :=
        mul_le_mul hoperatorDifference hmultiplier (norm_nonneg _)
          (mul_nonneg (NNReal.coe_nonneg _) (norm_nonneg _))
      _ = h.constraintGradientLipschitz * params.multiplierBound *
          ‖run.step (k - 1)‖ := by ring
  -- Each error-step pair contributes exactly the named primal coefficient.
  have hcurrentPair :
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
            ‖run.step k‖ := add_le_add_right herrorCurrent _
      _ = primalConstant h params.delta params.beta params.rho * ‖run.step k‖ := by
        rw [primalConstant_def]
        ring
  have hpreviousPair :
      ‖(params.beta : ℝ) • run.step (k - 1) -
          (params.rho : ℝ) • EqualityConstrained.constraintGradient c
            (run.point (k - 1)) (run.error (k - 1))‖ ≤
        primalConstant h params.delta params.beta params.rho *
          ‖run.step (k - 1)‖ := by
    calc
      ‖(params.beta : ℝ) • run.step (k - 1) -
          (params.rho : ℝ) • EqualityConstrained.constraintGradient c
            (run.point (k - 1)) (run.error (k - 1))‖ ≤
          ‖(params.beta : ℝ) • run.step (k - 1)‖ +
            ‖(params.rho : ℝ) • EqualityConstrained.constraintGradient c
              (run.point (k - 1)) (run.error (k - 1))‖ := norm_sub_le _ _
      _ = params.beta * ‖run.step (k - 1)‖ +
          ‖(params.rho : ℝ) • EqualityConstrained.constraintGradient c
            (run.point (k - 1)) (run.error (k - 1))‖ := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos run.beta_pos]
      _ ≤ params.beta * ‖run.step (k - 1)‖ +
          params.rho * h.constraintGradientBound * linearizationConstant h * params.delta *
            ‖run.step (k - 1)‖ := add_le_add_right herrorPrevious _
      _ = primalConstant h params.delta params.beta params.rho *
          ‖run.step (k - 1)‖ := by
        rw [primalConstant_def]
        ring
  -- Substitute the identity, apply the four termwise estimates, and collect coefficients.
  rw [constraintGradientMultiplierIncrement run k hk_pos]
  calc
    ‖(-(params.beta : ℝ) • run.step k +
          (params.rho : ℝ) •
            EqualityConstrained.constraintGradient c (run.point k) (run.error k)) +
        ((params.beta : ℝ) • run.step (k - 1) -
          (params.rho : ℝ) • EqualityConstrained.constraintGradient c (run.point (k - 1))
            (run.error (k - 1))) +
        (gradient f (run.point (k - 1)) - gradient f (run.point k)) +
        (EqualityConstrained.constraintGradient c (run.point (k - 1)) -
          EqualityConstrained.constraintGradient c (run.point k)) (run.multiplier k)‖ ≤
        ‖-(params.beta : ℝ) • run.step k +
          (params.rho : ℝ) •
            EqualityConstrained.constraintGradient c (run.point k) (run.error k)‖ +
        ‖(params.beta : ℝ) • run.step (k - 1) -
          (params.rho : ℝ) • EqualityConstrained.constraintGradient c (run.point (k - 1))
            (run.error (k - 1))‖ +
        ‖gradient f (run.point (k - 1)) - gradient f (run.point k)‖ +
        ‖(EqualityConstrained.constraintGradient c (run.point (k - 1)) -
          EqualityConstrained.constraintGradient c (run.point k)) (run.multiplier k)‖ := by
      have hfirst := norm_add_le
        (-(params.beta : ℝ) • run.step k +
          (params.rho : ℝ) • EqualityConstrained.constraintGradient c
            (run.point k) (run.error k))
        ((params.beta : ℝ) • run.step (k - 1) -
          (params.rho : ℝ) • EqualityConstrained.constraintGradient c
            (run.point (k - 1)) (run.error (k - 1)))
      have hsecond := norm_add_le
        ((-(params.beta : ℝ) • run.step k +
            (params.rho : ℝ) • EqualityConstrained.constraintGradient c
              (run.point k) (run.error k)) +
          ((params.beta : ℝ) • run.step (k - 1) -
            (params.rho : ℝ) • EqualityConstrained.constraintGradient c
              (run.point (k - 1)) (run.error (k - 1))))
        (gradient f (run.point (k - 1)) - gradient f (run.point k))
      have hthird := norm_add_le
        (((-(params.beta : ℝ) • run.step k +
              (params.rho : ℝ) • EqualityConstrained.constraintGradient c
                (run.point k) (run.error k)) +
            ((params.beta : ℝ) • run.step (k - 1) -
              (params.rho : ℝ) • EqualityConstrained.constraintGradient c
                (run.point (k - 1)) (run.error (k - 1)))) +
          (gradient f (run.point (k - 1)) - gradient f (run.point k)))
        ((EqualityConstrained.constraintGradient c (run.point (k - 1)) -
          EqualityConstrained.constraintGradient c (run.point k)) (run.multiplier k))
      linarith
    _ ≤ primalConstant h params.delta params.beta params.rho * ‖run.step k‖ +
        primalConstant h params.delta params.beta params.rho * ‖run.step (k - 1)‖ +
        h.gradientLipschitz * ‖run.step (k - 1)‖ +
        h.constraintGradientLipschitz * params.multiplierBound *
          ‖run.step (k - 1)‖ :=
      add_le_add (add_le_add (add_le_add hcurrentPair hpreviousPair) hgradientDifference)
        hoperatorApplied
    _ = primalConstant h params.delta params.beta params.rho * ‖run.step k‖ +
        primalComparisonConstant h params.delta params.beta params.rho
          params.multiplierBound * ‖run.step (k - 1)‖ := by
      rw [primalComparisonConstant_def]
      ring

/-- Lemma 2.8: for every positive iteration index in an admissible prefix, the
squared successive-multiplier difference is bounded by the multiplier-primal
constant times the sum of the current and preceding squared step norms. -/
theorem norm_multiplier_succ_sub_sq_le (h : EqualityConstrained.Regularity f c)
    (params : Parameters h x₀ multiplier₀)
    (run : Run f c params.rho params.beta x₀ multiplier₀)
    {N k : ℕ} (h_admissible : run.IsAdmissiblePrefix h N)
    (hk_pos : 1 ≤ k) (hk : k < N) :
    ‖run.multiplier (k + 1) - run.multiplier k‖ ^ 2 ≤
      multiplierPrimalConstant h params.delta params.beta params.rho params.multiplierBound *
        (‖run.step k‖ ^ 2 + ‖run.step (k - 1)‖ ^ 2) := by
  -- LICQ converts the comparison estimate on the constraint-gradient image into a
  -- scalar estimate for the multiplier increment itself.
  have hsegments := (run.isAdmissiblePrefix_iff h N).1 h_admissible
  have hsegment := hsegments k hk
  have hx : run.point k ∈ h.region := hsegment (left_mem_segment ℝ _ _)
  have hcomparison :=
    normConstraintGradientMultiplierIncrement_le h params run h_admissible hk_pos hk
  have hlicq := h.licqLowerBound (run.point k) hx
    (run.multiplier (k + 1) - run.multiplier k)
  have hscaled := hlicq.trans hcomparison
  have hprimalNonneg :
      0 ≤ primalConstant h params.delta params.beta params.rho := by
    rw [primalConstant_def]
    positivity
  have hcomparisonNonneg :
      0 ≤ primalComparisonConstant h params.delta params.beta params.rho
        params.multiplierBound := by
    rw [primalComparisonConstant_def]
    positivity
  have hleftNonneg :
      0 ≤ (h.licqModulus : ℝ) *
        ‖run.multiplier (k + 1) - run.multiplier k‖ :=
    mul_nonneg h.licqModulus_pos.le (norm_nonneg _)
  have hrightNonneg :
      0 ≤ primalConstant h params.delta params.beta params.rho * ‖run.step k‖ +
        primalComparisonConstant h params.delta params.beta params.rho
          params.multiplierBound * ‖run.step (k - 1)‖ :=
    add_nonneg (mul_nonneg hprimalNonneg (norm_nonneg _))
      (mul_nonneg hcomparisonNonneg (norm_nonneg _))
  have hscaledSquare :
      ((h.licqModulus : ℝ) *
          ‖run.multiplier (k + 1) - run.multiplier k‖) ^ 2 ≤
        (primalConstant h params.delta params.beta params.rho * ‖run.step k‖ +
          primalComparisonConstant h params.delta params.beta params.rho
            params.multiplierBound * ‖run.step (k - 1)‖) ^ 2 :=
    (sq_le_sq₀ hleftNonneg hrightNonneg).2 hscaled
  -- Bound the two squared coefficients by their maximum and use the elementary
  -- two-term square estimate.
  have hprimalMax :
      (primalConstant h params.delta params.beta params.rho) ^ 2 ≤
        max ((primalConstant h params.delta params.beta params.rho) ^ 2)
          ((primalComparisonConstant h params.delta params.beta params.rho
            params.multiplierBound) ^ 2) := le_max_left _ _
  have hcomparisonMax :
      (primalComparisonConstant h params.delta params.beta params.rho
          params.multiplierBound) ^ 2 ≤
        max ((primalConstant h params.delta params.beta params.rho) ^ 2)
          ((primalComparisonConstant h params.delta params.beta params.rho
            params.multiplierBound) ^ 2) := le_max_right _ _
  have hcurrentTerm :
      (primalConstant h params.delta params.beta params.rho * ‖run.step k‖) ^ 2 ≤
        max ((primalConstant h params.delta params.beta params.rho) ^ 2)
          ((primalComparisonConstant h params.delta params.beta params.rho
            params.multiplierBound) ^ 2) * ‖run.step k‖ ^ 2 := by
    rw [mul_pow]
    exact mul_le_mul_of_nonneg_right hprimalMax (sq_nonneg _)
  have hpreviousTerm :
      (primalComparisonConstant h params.delta params.beta params.rho
          params.multiplierBound * ‖run.step (k - 1)‖) ^ 2 ≤
        max ((primalConstant h params.delta params.beta params.rho) ^ 2)
          ((primalComparisonConstant h params.delta params.beta params.rho
            params.multiplierBound) ^ 2) * ‖run.step (k - 1)‖ ^ 2 := by
    rw [mul_pow]
    exact mul_le_mul_of_nonneg_right hcomparisonMax (sq_nonneg _)
  have htwoTermSquare :
      (primalConstant h params.delta params.beta params.rho * ‖run.step k‖ +
          primalComparisonConstant h params.delta params.beta params.rho
            params.multiplierBound * ‖run.step (k - 1)‖) ^ 2 ≤
        2 * max ((primalConstant h params.delta params.beta params.rho) ^ 2)
          ((primalComparisonConstant h params.delta params.beta params.rho
            params.multiplierBound) ^ 2) *
          (‖run.step k‖ ^ 2 + ‖run.step (k - 1)‖ ^ 2) := by
    calc
      (primalConstant h params.delta params.beta params.rho * ‖run.step k‖ +
          primalComparisonConstant h params.delta params.beta params.rho
            params.multiplierBound * ‖run.step (k - 1)‖) ^ 2 ≤
          2 * ((primalConstant h params.delta params.beta params.rho *
              ‖run.step k‖) ^ 2 +
            (primalComparisonConstant h params.delta params.beta params.rho
              params.multiplierBound * ‖run.step (k - 1)‖) ^ 2) := by
        nlinarith [sq_nonneg
          (primalConstant h params.delta params.beta params.rho * ‖run.step k‖ -
            primalComparisonConstant h params.delta params.beta params.rho
              params.multiplierBound * ‖run.step (k - 1)‖)]
      _ ≤ 2 *
          (max ((primalConstant h params.delta params.beta params.rho) ^ 2)
              ((primalComparisonConstant h params.delta params.beta params.rho
                params.multiplierBound) ^ 2) * ‖run.step k‖ ^ 2 +
            max ((primalConstant h params.delta params.beta params.rho) ^ 2)
              ((primalComparisonConstant h params.delta params.beta params.rho
                params.multiplierBound) ^ 2) * ‖run.step (k - 1)‖ ^ 2) :=
        mul_le_mul_of_nonneg_left (add_le_add hcurrentTerm hpreviousTerm) (by norm_num)
      _ = 2 * max ((primalConstant h params.delta params.beta params.rho) ^ 2)
          ((primalComparisonConstant h params.delta params.beta params.rho
            params.multiplierBound) ^ 2) *
          (‖run.step k‖ ^ 2 + ‖run.step (k - 1)‖ ^ 2) := by ring
  have hmaxProductNonneg :
      0 ≤ max ((primalConstant h params.delta params.beta params.rho) ^ 2)
          ((primalComparisonConstant h params.delta params.beta params.rho
            params.multiplierBound) ^ 2) *
        (‖run.step k‖ ^ 2 + ‖run.step (k - 1)‖ ^ 2) :=
    mul_nonneg ((sq_nonneg _).trans (le_max_left _ _))
      (add_nonneg (sq_nonneg _) (sq_nonneg _))
  have hscaledFinal :
      (h.licqModulus : ℝ) ^ 2 *
          ‖run.multiplier (k + 1) - run.multiplier k‖ ^ 2 ≤
        4 * max ((primalConstant h params.delta params.beta params.rho) ^ 2)
          ((primalComparisonConstant h params.delta params.beta params.rho
            params.multiplierBound) ^ 2) *
          (‖run.step k‖ ^ 2 + ‖run.step (k - 1)‖ ^ 2) := by
    calc
      (h.licqModulus : ℝ) ^ 2 *
          ‖run.multiplier (k + 1) - run.multiplier k‖ ^ 2 =
          ((h.licqModulus : ℝ) *
            ‖run.multiplier (k + 1) - run.multiplier k‖) ^ 2 := by ring
      _ ≤ (primalConstant h params.delta params.beta params.rho * ‖run.step k‖ +
          primalComparisonConstant h params.delta params.beta params.rho
            params.multiplierBound * ‖run.step (k - 1)‖) ^ 2 := hscaledSquare
      _ ≤ 2 * max ((primalConstant h params.delta params.beta params.rho) ^ 2)
          ((primalComparisonConstant h params.delta params.beta params.rho
            params.multiplierBound) ^ 2) *
          (‖run.step k‖ ^ 2 + ‖run.step (k - 1)‖ ^ 2) := htwoTermSquare
      _ ≤ 4 * max ((primalConstant h params.delta params.beta params.rho) ^ 2)
          ((primalComparisonConstant h params.delta params.beta params.rho
            params.multiplierBound) ^ 2) *
          (‖run.step k‖ ^ 2 + ‖run.step (k - 1)‖ ^ 2) := by
        nlinarith
  have hlicqSquarePos : 0 < (h.licqModulus : ℝ) ^ 2 := sq_pos_of_pos h.licqModulus_pos
  have hdivided :
      ‖run.multiplier (k + 1) - run.multiplier k‖ ^ 2 ≤
        (4 * max ((primalConstant h params.delta params.beta params.rho) ^ 2)
          ((primalComparisonConstant h params.delta params.beta params.rho
            params.multiplierBound) ^ 2) *
          (‖run.step k‖ ^ 2 + ‖run.step (k - 1)‖ ^ 2)) /
            (h.licqModulus : ℝ) ^ 2 := by
    rw [le_div_iff₀ hlicqSquarePos]
    simpa only [mul_comm] using hscaledFinal
  rw [multiplierPrimalConstant_def]
  calc
    ‖run.multiplier (k + 1) - run.multiplier k‖ ^ 2 ≤
        (4 * max ((primalConstant h params.delta params.beta params.rho) ^ 2)
          ((primalComparisonConstant h params.delta params.beta params.rho
            params.multiplierBound) ^ 2) *
          (‖run.step k‖ ^ 2 + ‖run.step (k - 1)‖ ^ 2)) /
            (h.licqModulus : ℝ) ^ 2 := hdivided
    _ = (4 / (h.licqModulus : ℝ) ^ 2) *
        max ((primalConstant h params.delta params.beta params.rho) ^ 2)
          ((primalComparisonConstant h params.delta params.beta params.rho
            params.multiplierBound) ^ 2) *
        (‖run.step k‖ ^ 2 + ‖run.step (k - 1)‖ ^ 2) := by ring

end LALM.Run

end
