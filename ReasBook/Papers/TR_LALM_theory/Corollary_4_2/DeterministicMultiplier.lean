/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@5bf5af722d85bd5c98368c41c4066124a15e8fd3:ReasBook/Papers/TR_LALM_theory/README.md (formalization contributor).
-/

module

public import TR_LALM_theory.Corollary_4_2.DeterministicPrefix

public section

open scoped InnerProductSpace NNReal

namespace LALM.Correction.Run

variable {n m : ℕ}
variable {f : EuclideanSpace ℝ (Fin n) → ℝ}
variable {c : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m)}
variable {x₀ : EuclideanSpace ℝ (Fin n)}
variable {multiplier₀ : EuclideanSpace ℝ (Fin m)}

/-- Helper for Corollary 4.2: subtracting corrected perturbed-stationarity
identities expresses a multiplier increment through two consecutive base steps. -/
private lemma constraintGradientMultiplierIncrement
    {ρ β : ℝ} (run : Run f c ρ β x₀ multiplier₀) (k : ℕ) (hk_pos : 1 ≤ k) :
    EqualityConstrained.constraintGradient c (run.point k)
        (run.multiplier (k + 1) - run.multiplier k) =
      (-β • run.baseStep k +
          ρ • EqualityConstrained.constraintGradient c (run.point k)
            (error c (run.point k) (run.baseStep k))) +
        (β • run.baseStep (k - 1) -
          ρ • EqualityConstrained.constraintGradient c (run.point (k - 1))
            (error c (run.point (k - 1)) (run.baseStep (k - 1)))) +
        (gradient f (run.point (k - 1)) - gradient f (run.point k)) +
        (EqualityConstrained.constraintGradient c (run.point (k - 1)) -
          EqualityConstrained.constraintGradient c (run.point k)) (run.multiplier k) := by
  -- Normalize each corrected next multiplier to the stored successor before subtraction.
  have hpred : k - 1 + 1 = k := Nat.sub_add_cancel hk_pos
  have hcurrent := perturbedMultiplierIdentity f c ρ β (run.point k)
    (run.multiplier k) (run.baseStep k) (run.minimizes_baseStep k)
  have hprevious := perturbedMultiplierIdentity f c ρ β (run.point (k - 1))
    (run.multiplier (k - 1)) (run.baseStep (k - 1))
      (run.minimizes_baseStep (k - 1))
  rw [← run.multiplier_succ k] at hcurrent
  rw [← run.multiplier_succ (k - 1), hpred] at hprevious
  simp only [map_sub, sub_apply]
  linear_combination (norm := module) hcurrent - hprevious

/-- Helper for Corollary 4.2: a bounded admissible base step controls the
scaled constraint-gradient image of its corrected nonlinear error. -/
private lemma normScaledConstraintGradientError_le
    (h : EqualityConstrained.Regularity f c)
    (params : Parameters h x₀ multiplier₀)
    (run : Run f c params.rho params.beta x₀ multiplier₀)
    (j : ℕ) (hadm : IsAdmissible h (run.point j) (run.baseStep j))
    (hstep : ‖run.baseStep j‖ ≤ params.delta) :
    ‖(params.rho : ℝ) • EqualityConstrained.constraintGradient c (run.point j)
        (error c (run.point j) (run.baseStep j))‖ ≤
      params.rho * h.constraintGradientBound * errorFactor h params.delta *
        params.delta * ‖run.baseStep j‖ := by
  -- Bound the operator application and insert the corrected quadratic error estimate.
  have hx := base_mem_region h (run.point j) (run.baseStep j) hadm
  have hoperator := h.norm_constraintGradient_le (run.point j) hx
  have herror := norm_error_le_factor h params.delta
    (run.point j) (run.baseStep j) hadm hstep
  have happlication :
      ‖EqualityConstrained.constraintGradient c (run.point j)
          (error c (run.point j) (run.baseStep j))‖ ≤
        h.constraintGradientBound * ‖error c (run.point j) (run.baseStep j)‖ :=
    (EqualityConstrained.constraintGradient c (run.point j)).le_opNorm
      (error c (run.point j) (run.baseStep j)) |>.trans
        (mul_le_mul_of_nonneg_right hoperator (norm_nonneg _))
  have herrorApplied :
      ‖EqualityConstrained.constraintGradient c (run.point j)
          (error c (run.point j) (run.baseStep j))‖ ≤
        h.constraintGradientBound *
          (errorFactor h params.delta * ‖run.baseStep j‖ ^ 2) :=
    happlication.trans
      (mul_le_mul_of_nonneg_left herror (NNReal.coe_nonneg h.constraintGradientBound))
  have hstepProduct :
      ‖run.baseStep j‖ * ‖run.baseStep j‖ ≤
        params.delta * ‖run.baseStep j‖ :=
    mul_le_mul_of_nonneg_right hstep (norm_nonneg _)
  have hcoefficientNonneg :
      0 ≤ (params.rho : ℝ) * h.constraintGradientBound *
        errorFactor h params.delta := by
    rw [errorFactor_def, errorConstant_def]
    positivity
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos run.rho_pos]
  calc
    params.rho * ‖EqualityConstrained.constraintGradient c (run.point j)
        (error c (run.point j) (run.baseStep j))‖ ≤
        params.rho * (h.constraintGradientBound *
          (errorFactor h params.delta * ‖run.baseStep j‖ ^ 2)) :=
      mul_le_mul_of_nonneg_left herrorApplied run.rho_pos.le
    _ = (params.rho * h.constraintGradientBound * errorFactor h params.delta) *
        (‖run.baseStep j‖ * ‖run.baseStep j‖) := by ring
    _ ≤ (params.rho * h.constraintGradientBound * errorFactor h params.delta) *
        (params.delta * ‖run.baseStep j‖) :=
      mul_le_mul_of_nonneg_left hstepProduct hcoefficientNonneg
    _ = params.rho * h.constraintGradientBound * errorFactor h params.delta *
        params.delta * ‖run.baseStep j‖ := by ring

/-- Helper for Corollary 4.2: the constraint-gradient image of a corrected
multiplier increment is controlled by the current and preceding base steps. -/
private lemma normConstraintGradientMultiplierIncrement_le
    (h : EqualityConstrained.Regularity f c)
    (params : Parameters h x₀ multiplier₀)
    (run : Run f c params.rho params.beta x₀ multiplier₀)
    {N k : ℕ} (h_admissible : run.IsAdmissiblePrefix h N)
    (hk_pos : 1 ≤ k) (hk : k < N) :
    ‖EqualityConstrained.constraintGradient c (run.point k)
        (run.multiplier (k + 1) - run.multiplier k)‖ ≤
      primalConstant h params.delta params.beta params.rho * ‖run.baseStep k‖ +
        primalComparisonConstant h params.delta params.beta params.rho
          params.multiplierBound * ‖run.baseStep (k - 1)‖ := by
  -- Extract both corrected transitions and their prefix bounds.
  have hpred : k - 1 + 1 = k := Nat.sub_add_cancel hk_pos
  have hk_previous : k - 1 < N := by omega
  have hadmissible := (run.isAdmissiblePrefix_iff h N).1 h_admissible
  have hadmCurrent := hadmissible k hk
  have hadmPrevious := hadmissible (k - 1) hk_previous
  have hxCurrent := base_mem_region h (run.point k) (run.baseStep k) hadmCurrent
  have hxPrevious :=
    base_mem_region h (run.point (k - 1)) (run.baseStep (k - 1)) hadmPrevious
  have hstepCurrent := run.norm_baseStep_le h params h_admissible hk
  have hstepPrevious := run.norm_baseStep_le h params h_admissible hk_previous
  have hmultiplier := run.norm_multiplier_le h params h_admissible (show k ≤ N by omega)
  have herrorCurrent := normScaledConstraintGradientError_le
    h params run k hadmCurrent hstepCurrent
  have herrorPrevious := normScaledConstraintGradientError_le
    h params run (k - 1) hadmPrevious hstepPrevious
  -- Corrected displacement replaces the exact uncorrected point-step equality.
  have hpointDisplacement :
      ‖run.point k - run.point (k - 1)‖ ≤
        displacementFactor h params.delta * ‖run.baseStep (k - 1)‖ := by
    have hdisplacement := displacement_le h params.delta (run.point (k - 1))
      (run.baseStep (k - 1)) hadmPrevious hstepPrevious
    rw [← run.point_succ (k - 1), hpred] at hdisplacement
    exact hdisplacement
  have hgradientDifference :
      ‖gradient f (run.point (k - 1)) - gradient f (run.point k)‖ ≤
        h.gradientLipschitz * displacementFactor h params.delta *
          ‖run.baseStep (k - 1)‖ := by
    have hlipschitz :
        ‖gradient f (run.point (k - 1)) - gradient f (run.point k)‖ ≤
          h.gradientLipschitz * ‖run.point k - run.point (k - 1)‖ := by
      calc
        ‖gradient f (run.point (k - 1)) - gradient f (run.point k)‖ =
            dist (gradient f (run.point (k - 1))) (gradient f (run.point k)) :=
          (dist_eq_norm _ _).symm
        _ ≤ h.gradientLipschitz * dist (run.point (k - 1)) (run.point k) :=
          h.lipschitzOn_gradient.dist_le_mul
            (run.point (k - 1)) hxPrevious (run.point k) hxCurrent
        _ = h.gradientLipschitz * ‖run.point k - run.point (k - 1)‖ := by
          rw [dist_eq_norm, norm_sub_rev]
    calc
      ‖gradient f (run.point (k - 1)) - gradient f (run.point k)‖ ≤
          h.gradientLipschitz * ‖run.point k - run.point (k - 1)‖ := hlipschitz
      _ ≤ h.gradientLipschitz *
          (displacementFactor h params.delta * ‖run.baseStep (k - 1)‖) :=
        mul_le_mul_of_nonneg_left hpointDisplacement (NNReal.coe_nonneg _)
      _ = h.gradientLipschitz * displacementFactor h params.delta *
          ‖run.baseStep (k - 1)‖ := by ring
  have hoperatorDifference :
      ‖EqualityConstrained.constraintGradient c (run.point (k - 1)) -
          EqualityConstrained.constraintGradient c (run.point k)‖ ≤
        h.constraintGradientLipschitz * displacementFactor h params.delta *
          ‖run.baseStep (k - 1)‖ := by
    have hlipschitz :
        ‖EqualityConstrained.constraintGradient c (run.point (k - 1)) -
            EqualityConstrained.constraintGradient c (run.point k)‖ ≤
          h.constraintGradientLipschitz * ‖run.point k - run.point (k - 1)‖ := by
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
        _ = h.constraintGradientLipschitz *
            ‖run.point k - run.point (k - 1)‖ := by
          rw [dist_eq_norm, norm_sub_rev]
    calc
      ‖EqualityConstrained.constraintGradient c (run.point (k - 1)) -
          EqualityConstrained.constraintGradient c (run.point k)‖ ≤
          h.constraintGradientLipschitz * ‖run.point k - run.point (k - 1)‖ :=
        hlipschitz
      _ ≤ h.constraintGradientLipschitz *
          (displacementFactor h params.delta * ‖run.baseStep (k - 1)‖) :=
        mul_le_mul_of_nonneg_left hpointDisplacement (NNReal.coe_nonneg _)
      _ = h.constraintGradientLipschitz * displacementFactor h params.delta *
          ‖run.baseStep (k - 1)‖ := by ring
  have hdisplacementFactorNonneg :
      0 ≤ displacementFactor h params.delta := by
    rw [displacementFactor_def, stepConstant_def]
    positivity
  have hoperatorApplied :
      ‖(EqualityConstrained.constraintGradient c (run.point (k - 1)) -
          EqualityConstrained.constraintGradient c (run.point k)) (run.multiplier k)‖ ≤
        h.constraintGradientLipschitz * params.multiplierBound *
          displacementFactor h params.delta * ‖run.baseStep (k - 1)‖ := by
    calc
      ‖(EqualityConstrained.constraintGradient c (run.point (k - 1)) -
          EqualityConstrained.constraintGradient c (run.point k)) (run.multiplier k)‖ ≤
          ‖EqualityConstrained.constraintGradient c (run.point (k - 1)) -
            EqualityConstrained.constraintGradient c (run.point k)‖ *
              ‖run.multiplier k‖ :=
        (EqualityConstrained.constraintGradient c (run.point (k - 1)) -
          EqualityConstrained.constraintGradient c (run.point k)).le_opNorm
            (run.multiplier k)
      _ ≤ (h.constraintGradientLipschitz * displacementFactor h params.delta *
            ‖run.baseStep (k - 1)‖) * params.multiplierBound :=
        mul_le_mul hoperatorDifference hmultiplier (norm_nonneg _)
          (mul_nonneg
            (mul_nonneg (NNReal.coe_nonneg _) hdisplacementFactorNonneg)
            (norm_nonneg _))
      _ = h.constraintGradientLipschitz * params.multiplierBound *
          displacementFactor h params.delta * ‖run.baseStep (k - 1)‖ := by ring
  -- Pair each base step with its corrected error contribution.
  have hcurrentPair :
      ‖-(params.beta : ℝ) • run.baseStep k +
          (params.rho : ℝ) • EqualityConstrained.constraintGradient c (run.point k)
            (error c (run.point k) (run.baseStep k))‖ ≤
        primalConstant h params.delta params.beta params.rho * ‖run.baseStep k‖ := by
    calc
      ‖-(params.beta : ℝ) • run.baseStep k +
          (params.rho : ℝ) • EqualityConstrained.constraintGradient c (run.point k)
            (error c (run.point k) (run.baseStep k))‖ ≤
          ‖-(params.beta : ℝ) • run.baseStep k‖ +
            ‖(params.rho : ℝ) • EqualityConstrained.constraintGradient c (run.point k)
              (error c (run.point k) (run.baseStep k))‖ := norm_add_le _ _
      _ = params.beta * ‖run.baseStep k‖ +
          ‖(params.rho : ℝ) • EqualityConstrained.constraintGradient c (run.point k)
            (error c (run.point k) (run.baseStep k))‖ := by
        rw [norm_smul, Real.norm_eq_abs, abs_neg, abs_of_pos run.beta_pos]
      _ ≤ params.beta * ‖run.baseStep k‖ +
          params.rho * h.constraintGradientBound * errorFactor h params.delta *
            params.delta * ‖run.baseStep k‖ := add_le_add_right herrorCurrent _
      _ = primalConstant h params.delta params.beta params.rho * ‖run.baseStep k‖ := by
        rw [primalConstant_def]
        ring
  have hpreviousPair :
      ‖(params.beta : ℝ) • run.baseStep (k - 1) -
          (params.rho : ℝ) • EqualityConstrained.constraintGradient c
            (run.point (k - 1))
            (error c (run.point (k - 1)) (run.baseStep (k - 1)))‖ ≤
        primalConstant h params.delta params.beta params.rho *
          ‖run.baseStep (k - 1)‖ := by
    calc
      ‖(params.beta : ℝ) • run.baseStep (k - 1) -
          (params.rho : ℝ) • EqualityConstrained.constraintGradient c
            (run.point (k - 1))
            (error c (run.point (k - 1)) (run.baseStep (k - 1)))‖ ≤
          ‖(params.beta : ℝ) • run.baseStep (k - 1)‖ +
            ‖(params.rho : ℝ) • EqualityConstrained.constraintGradient c
              (run.point (k - 1))
              (error c (run.point (k - 1)) (run.baseStep (k - 1)))‖ := norm_sub_le _ _
      _ = params.beta * ‖run.baseStep (k - 1)‖ +
          ‖(params.rho : ℝ) • EqualityConstrained.constraintGradient c
            (run.point (k - 1))
            (error c (run.point (k - 1)) (run.baseStep (k - 1)))‖ := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos run.beta_pos]
      _ ≤ params.beta * ‖run.baseStep (k - 1)‖ +
          params.rho * h.constraintGradientBound * errorFactor h params.delta *
            params.delta * ‖run.baseStep (k - 1)‖ := add_le_add_right herrorPrevious _
      _ = primalConstant h params.delta params.beta params.rho *
          ‖run.baseStep (k - 1)‖ := by
        rw [primalConstant_def]
        ring
  -- Substitute the four-term identity and collect the corrected comparison coefficient.
  rw [constraintGradientMultiplierIncrement run k hk_pos]
  calc
    ‖(-(params.beta : ℝ) • run.baseStep k +
          (params.rho : ℝ) • EqualityConstrained.constraintGradient c (run.point k)
            (error c (run.point k) (run.baseStep k))) +
        ((params.beta : ℝ) • run.baseStep (k - 1) -
          (params.rho : ℝ) • EqualityConstrained.constraintGradient c (run.point (k - 1))
            (error c (run.point (k - 1)) (run.baseStep (k - 1)))) +
        (gradient f (run.point (k - 1)) - gradient f (run.point k)) +
        (EqualityConstrained.constraintGradient c (run.point (k - 1)) -
          EqualityConstrained.constraintGradient c (run.point k)) (run.multiplier k)‖ ≤
        ‖-(params.beta : ℝ) • run.baseStep k +
          (params.rho : ℝ) • EqualityConstrained.constraintGradient c (run.point k)
            (error c (run.point k) (run.baseStep k))‖ +
        ‖(params.beta : ℝ) • run.baseStep (k - 1) -
          (params.rho : ℝ) • EqualityConstrained.constraintGradient c (run.point (k - 1))
            (error c (run.point (k - 1)) (run.baseStep (k - 1)))‖ +
        ‖gradient f (run.point (k - 1)) - gradient f (run.point k)‖ +
        ‖(EqualityConstrained.constraintGradient c (run.point (k - 1)) -
          EqualityConstrained.constraintGradient c (run.point k)) (run.multiplier k)‖ := by
      have hfirst := norm_add_le
        (-(params.beta : ℝ) • run.baseStep k +
          (params.rho : ℝ) • EqualityConstrained.constraintGradient c
            (run.point k) (error c (run.point k) (run.baseStep k)))
        ((params.beta : ℝ) • run.baseStep (k - 1) -
          (params.rho : ℝ) • EqualityConstrained.constraintGradient c
            (run.point (k - 1))
            (error c (run.point (k - 1)) (run.baseStep (k - 1))) )
      have hsecond := norm_add_le
        ((-(params.beta : ℝ) • run.baseStep k +
            (params.rho : ℝ) • EqualityConstrained.constraintGradient c
              (run.point k) (error c (run.point k) (run.baseStep k))) +
          ((params.beta : ℝ) • run.baseStep (k - 1) -
            (params.rho : ℝ) • EqualityConstrained.constraintGradient c
              (run.point (k - 1))
              (error c (run.point (k - 1)) (run.baseStep (k - 1)))))
        (gradient f (run.point (k - 1)) - gradient f (run.point k))
      have hthird := norm_add_le
        (((-(params.beta : ℝ) • run.baseStep k +
              (params.rho : ℝ) • EqualityConstrained.constraintGradient c
                (run.point k) (error c (run.point k) (run.baseStep k))) +
            ((params.beta : ℝ) • run.baseStep (k - 1) -
              (params.rho : ℝ) • EqualityConstrained.constraintGradient c
                (run.point (k - 1))
                (error c (run.point (k - 1)) (run.baseStep (k - 1))))) +
          (gradient f (run.point (k - 1)) - gradient f (run.point k)))
        ((EqualityConstrained.constraintGradient c (run.point (k - 1)) -
          EqualityConstrained.constraintGradient c (run.point k)) (run.multiplier k))
      linarith
    _ ≤ primalConstant h params.delta params.beta params.rho * ‖run.baseStep k‖ +
        primalConstant h params.delta params.beta params.rho * ‖run.baseStep (k - 1)‖ +
        h.gradientLipschitz * displacementFactor h params.delta *
          ‖run.baseStep (k - 1)‖ +
        h.constraintGradientLipschitz * params.multiplierBound *
          displacementFactor h params.delta * ‖run.baseStep (k - 1)‖ :=
      add_le_add (add_le_add (add_le_add hcurrentPair hpreviousPair)
        hgradientDifference) hoperatorApplied
    _ = primalConstant h params.delta params.beta params.rho * ‖run.baseStep k‖ +
        primalComparisonConstant h params.delta params.beta params.rho
          params.multiplierBound * ‖run.baseStep (k - 1)‖ := by
      rw [primalComparisonConstant_def]
      ring

/-- Helper for Corollary 4.2: every positive corrected transition has its
squared multiplier increment controlled by two adjacent base-step squares. -/
theorem norm_multiplier_succ_sub_sq_le
    (h : EqualityConstrained.Regularity f c)
    (params : Parameters h x₀ multiplier₀)
    (run : Run f c params.rho params.beta x₀ multiplier₀)
    {N k : ℕ} (h_admissible : run.IsAdmissiblePrefix h N)
    (hk_pos : 1 ≤ k) (hk : k < N) :
    ‖run.multiplier (k + 1) - run.multiplier k‖ ^ 2 ≤
      multiplierPrimalConstant h params.delta params.beta params.rho
        params.multiplierBound *
          (‖run.baseStep k‖ ^ 2 + ‖run.baseStep (k - 1)‖ ^ 2) := by
  -- LICQ first converts the image comparison into a scalar inequality.
  have hadm := (run.isAdmissiblePrefix_iff h N).1 h_admissible k hk
  have hx := base_mem_region h (run.point k) (run.baseStep k) hadm
  have hcomparison := normConstraintGradientMultiplierIncrement_le
    h params run h_admissible hk_pos hk
  have hlicq := h.licqLowerBound (run.point k) hx
    (run.multiplier (k + 1) - run.multiplier k)
  have hscaled := hlicq.trans hcomparison
  have herrorFactorNonneg : 0 ≤ errorFactor h params.delta := by
    rw [errorFactor_def, errorConstant_def]
    positivity
  have hdisplacementFactorNonneg : 0 ≤ displacementFactor h params.delta := by
    rw [displacementFactor_def, stepConstant_def]
    positivity
  have hprimalNonneg :
      0 ≤ primalConstant h params.delta params.beta params.rho := by
    rw [primalConstant_def]
    exact add_nonneg run.beta_pos.le
      (mul_nonneg
        (mul_nonneg
          (mul_nonneg run.rho_pos.le (NNReal.coe_nonneg _)) herrorFactorNonneg)
        (NNReal.coe_nonneg _))
  have hcomparisonNonneg :
      0 ≤ primalComparisonConstant h params.delta params.beta params.rho
        params.multiplierBound := by
    rw [primalComparisonConstant_def]
    exact add_nonneg hprimalNonneg
      (mul_nonneg
        (add_nonneg (NNReal.coe_nonneg _)
          (mul_nonneg (NNReal.coe_nonneg _) (by positivity)))
        hdisplacementFactorNonneg)
  have hleftNonneg :
      0 ≤ (h.licqModulus : ℝ) *
        ‖run.multiplier (k + 1) - run.multiplier k‖ :=
    mul_nonneg h.licqModulus_pos.le (norm_nonneg _)
  have hrightNonneg :
      0 ≤ primalConstant h params.delta params.beta params.rho * ‖run.baseStep k‖ +
        primalComparisonConstant h params.delta params.beta params.rho
          params.multiplierBound * ‖run.baseStep (k - 1)‖ :=
    add_nonneg (mul_nonneg hprimalNonneg (norm_nonneg _))
      (mul_nonneg hcomparisonNonneg (norm_nonneg _))
  have hscaledSquare :
      ((h.licqModulus : ℝ) *
          ‖run.multiplier (k + 1) - run.multiplier k‖) ^ 2 ≤
        (primalConstant h params.delta params.beta params.rho * ‖run.baseStep k‖ +
          primalComparisonConstant h params.delta params.beta params.rho
            params.multiplierBound * ‖run.baseStep (k - 1)‖) ^ 2 :=
    (sq_le_sq₀ hleftNonneg hrightNonneg).2 hscaled
  -- Bound both squared coefficients by the maximum used in the named constant.
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
      (primalConstant h params.delta params.beta params.rho * ‖run.baseStep k‖) ^ 2 ≤
        max ((primalConstant h params.delta params.beta params.rho) ^ 2)
          ((primalComparisonConstant h params.delta params.beta params.rho
            params.multiplierBound) ^ 2) * ‖run.baseStep k‖ ^ 2 := by
    rw [mul_pow]
    exact mul_le_mul_of_nonneg_right hprimalMax (sq_nonneg _)
  have hpreviousTerm :
      (primalComparisonConstant h params.delta params.beta params.rho
          params.multiplierBound * ‖run.baseStep (k - 1)‖) ^ 2 ≤
        max ((primalConstant h params.delta params.beta params.rho) ^ 2)
          ((primalComparisonConstant h params.delta params.beta params.rho
            params.multiplierBound) ^ 2) * ‖run.baseStep (k - 1)‖ ^ 2 := by
    rw [mul_pow]
    exact mul_le_mul_of_nonneg_right hcomparisonMax (sq_nonneg _)
  have htwoTermSquare :
      (primalConstant h params.delta params.beta params.rho * ‖run.baseStep k‖ +
          primalComparisonConstant h params.delta params.beta params.rho
            params.multiplierBound * ‖run.baseStep (k - 1)‖) ^ 2 ≤
        2 * max ((primalConstant h params.delta params.beta params.rho) ^ 2)
          ((primalComparisonConstant h params.delta params.beta params.rho
            params.multiplierBound) ^ 2) *
          (‖run.baseStep k‖ ^ 2 + ‖run.baseStep (k - 1)‖ ^ 2) := by
    calc
      (primalConstant h params.delta params.beta params.rho * ‖run.baseStep k‖ +
          primalComparisonConstant h params.delta params.beta params.rho
            params.multiplierBound * ‖run.baseStep (k - 1)‖) ^ 2 ≤
          2 * ((primalConstant h params.delta params.beta params.rho *
              ‖run.baseStep k‖) ^ 2 +
            (primalComparisonConstant h params.delta params.beta params.rho
              params.multiplierBound * ‖run.baseStep (k - 1)‖) ^ 2) := by
        nlinarith [sq_nonneg
          (primalConstant h params.delta params.beta params.rho * ‖run.baseStep k‖ -
            primalComparisonConstant h params.delta params.beta params.rho
              params.multiplierBound * ‖run.baseStep (k - 1)‖)]
      _ ≤ 2 *
          (max ((primalConstant h params.delta params.beta params.rho) ^ 2)
              ((primalComparisonConstant h params.delta params.beta params.rho
                params.multiplierBound) ^ 2) * ‖run.baseStep k‖ ^ 2 +
            max ((primalConstant h params.delta params.beta params.rho) ^ 2)
              ((primalComparisonConstant h params.delta params.beta params.rho
                params.multiplierBound) ^ 2) * ‖run.baseStep (k - 1)‖ ^ 2) :=
        mul_le_mul_of_nonneg_left (add_le_add hcurrentTerm hpreviousTerm) (by norm_num)
      _ = 2 * max ((primalConstant h params.delta params.beta params.rho) ^ 2)
          ((primalComparisonConstant h params.delta params.beta params.rho
            params.multiplierBound) ^ 2) *
          (‖run.baseStep k‖ ^ 2 + ‖run.baseStep (k - 1)‖ ^ 2) := by ring
  have hmaxProductNonneg :
      0 ≤ max ((primalConstant h params.delta params.beta params.rho) ^ 2)
          ((primalComparisonConstant h params.delta params.beta params.rho
            params.multiplierBound) ^ 2) *
        (‖run.baseStep k‖ ^ 2 + ‖run.baseStep (k - 1)‖ ^ 2) :=
    mul_nonneg ((sq_nonneg _).trans (le_max_left _ _))
      (add_nonneg (sq_nonneg _) (sq_nonneg _))
  have hscaledFinal :
      (h.licqModulus : ℝ) ^ 2 *
          ‖run.multiplier (k + 1) - run.multiplier k‖ ^ 2 ≤
        4 * max ((primalConstant h params.delta params.beta params.rho) ^ 2)
          ((primalComparisonConstant h params.delta params.beta params.rho
            params.multiplierBound) ^ 2) *
          (‖run.baseStep k‖ ^ 2 + ‖run.baseStep (k - 1)‖ ^ 2) := by
    calc
      (h.licqModulus : ℝ) ^ 2 *
          ‖run.multiplier (k + 1) - run.multiplier k‖ ^ 2 =
          ((h.licqModulus : ℝ) *
            ‖run.multiplier (k + 1) - run.multiplier k‖) ^ 2 := by ring
      _ ≤ (primalConstant h params.delta params.beta params.rho * ‖run.baseStep k‖ +
          primalComparisonConstant h params.delta params.beta params.rho
            params.multiplierBound * ‖run.baseStep (k - 1)‖) ^ 2 := hscaledSquare
      _ ≤ 2 * max ((primalConstant h params.delta params.beta params.rho) ^ 2)
          ((primalComparisonConstant h params.delta params.beta params.rho
            params.multiplierBound) ^ 2) *
          (‖run.baseStep k‖ ^ 2 + ‖run.baseStep (k - 1)‖ ^ 2) := htwoTermSquare
      _ ≤ 4 * max ((primalConstant h params.delta params.beta params.rho) ^ 2)
          ((primalComparisonConstant h params.delta params.beta params.rho
            params.multiplierBound) ^ 2) *
          (‖run.baseStep k‖ ^ 2 + ‖run.baseStep (k - 1)‖ ^ 2) := by
        nlinarith
  have hlicqSquarePos : 0 < (h.licqModulus : ℝ) ^ 2 :=
    sq_pos_of_pos h.licqModulus_pos
  have hdivided :
      ‖run.multiplier (k + 1) - run.multiplier k‖ ^ 2 ≤
        (4 * max ((primalConstant h params.delta params.beta params.rho) ^ 2)
          ((primalComparisonConstant h params.delta params.beta params.rho
            params.multiplierBound) ^ 2) *
          (‖run.baseStep k‖ ^ 2 + ‖run.baseStep (k - 1)‖ ^ 2)) /
            (h.licqModulus : ℝ) ^ 2 := by
    rw [le_div_iff₀ hlicqSquarePos]
    simpa only [mul_comm] using hscaledFinal
  rw [multiplierPrimalConstant_def]
  calc
    ‖run.multiplier (k + 1) - run.multiplier k‖ ^ 2 ≤
        (4 * max ((primalConstant h params.delta params.beta params.rho) ^ 2)
          ((primalComparisonConstant h params.delta params.beta params.rho
            params.multiplierBound) ^ 2) *
          (‖run.baseStep k‖ ^ 2 + ‖run.baseStep (k - 1)‖ ^ 2)) /
            (h.licqModulus : ℝ) ^ 2 := hdivided
    _ = (4 / (h.licqModulus : ℝ) ^ 2) *
        max ((primalConstant h params.delta params.beta params.rho) ^ 2)
          ((primalComparisonConstant h params.delta params.beta params.rho
            params.multiplierBound) ^ 2) *
        (‖run.baseStep k‖ ^ 2 + ‖run.baseStep (k - 1)‖ ^ 2) := by ring

end LALM.Correction.Run

end
