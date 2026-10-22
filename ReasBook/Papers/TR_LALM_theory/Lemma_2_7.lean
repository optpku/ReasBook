/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@5bf5af722d85bd5c98368c41c4066124a15e8fd3:ReasBook/Papers/TR_LALM_theory/README.md (formalization contributor).
-/

module

public import TR_LALM_theory.Lemma_2_6

public section

open scoped InnerProductSpace LALM NNReal

namespace LALM.Run

variable {n m : ℕ}
variable {f : EuclideanSpace ℝ (Fin n) → ℝ}
variable {c : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m)}
variable {x₀ : EuclideanSpace ℝ (Fin n)}
variable {multiplier₀ : EuclideanSpace ℝ (Fin m)}

/-- Helper for Lemma 2.7: a segment in the regularity region gives the quadratic
upper Taylor estimate for the objective. -/
private lemma objectiveChange_le
    (h : EqualityConstrained.Regularity f c)
    (x y : EuclideanSpace ℝ (Fin n))
    (hsegment : segment ℝ x y ⊆ h.region) :
    f y - f x ≤
      ⟪gradient f x, y - x⟫_ℝ +
        (h.gradientLipschitz : ℝ) / 2 * ‖y - x‖ ^ 2 := by
  -- Bound the signed Taylor remainder by its norm, then use the segment estimate.
  have hremainder := norm_sub_sub_fderiv_le f h.gradientLipschitz h.region x y
    (fun _ hz ↦ h.differentiableAt_objective hz) h.lipschitzOn_objectiveFDeriv hsegment
  have hsigned :
      f y - f x - fderiv ℝ f x (y - x) ≤
        ‖f y - f x - fderiv ℝ f x (y - x)‖ := by
    simpa only [Real.norm_eq_abs] using
      (le_abs_self (f y - f x - fderiv ℝ f x (y - x)))
  rw [← inner_gradient_left] at hremainder hsigned
  linarith

/-- Helper for Lemma 2.7: bounds on a multiplier prefix control the effective
multiplier appearing in the primal model. -/
private lemma normEffectiveMultiplier_le
    (h : EqualityConstrained.Regularity f c)
    (params : Parameters h x₀ multiplier₀)
    (run : Run f c params.rho params.beta x₀ multiplier₀)
    (k : ℕ)
    (hMultiplier : ∀ j ≤ k, ‖run.multiplier j‖ ≤ params.multiplierBound) :
    ‖run.multiplier k + (params.rho : ℝ) • c (run.point k)‖ ≤
      3 * (params.multiplierBound : ℝ) := by
  cases k with
  | zero =>
      -- At initialization, the two parameter bounds control the two summands.
      rw [run.multiplier_zero, run.point_zero]
      calc
        ‖multiplier₀ + (params.rho : ℝ) • c x₀‖ ≤
            ‖multiplier₀‖ + ‖(params.rho : ℝ) • c x₀‖ := norm_add_le _ _
        _ = ‖multiplier₀‖ + params.rho * ‖c x₀‖ := by
          rw [norm_smul, Real.norm_eq_abs, abs_of_pos run.rho_pos]
        _ ≤ 3 * params.multiplierBound := by
          have hboundNonneg : (0 : ℝ) ≤ params.multiplierBound := by positivity
          linarith [params.norm_multiplier₀_le, params.initialResidual_le]
  | succ k =>
      -- The multiplier update identifies the effective multiplier with `2 λ_(k+1) - λ_k`.
      have heffective :
          run.multiplier (k + 1) + (params.rho : ℝ) • c (run.point (k + 1)) =
            (2 : ℝ) • run.multiplier (k + 1) - run.multiplier k := by
        rw [run.multiplier_succ k]
        module
      rw [heffective]
      calc
        ‖(2 : ℝ) • run.multiplier (k + 1) - run.multiplier k‖ ≤
            ‖(2 : ℝ) • run.multiplier (k + 1)‖ + ‖run.multiplier k‖ :=
          norm_sub_le _ _
        _ = 2 * ‖run.multiplier (k + 1)‖ + ‖run.multiplier k‖ := by
          rw [norm_smul, Real.norm_ofNat]
        _ ≤ 3 * params.multiplierBound := by
          have hnext := hMultiplier (k + 1) (Nat.le_refl _)
          have hprevious := hMultiplier k (Nat.le_succ k)
          have hboundNonneg : (0 : ℝ) ≤ params.multiplierBound := by positivity
          linarith

/-- Helper for Lemma 2.7: model optimality gives the exact change of the
linearized augmented-Lagrangian terms. -/
private lemma linearizedAugmentedLagrangianChange_eq
    (h : EqualityConstrained.Regularity f c)
    (params : Parameters h x₀ multiplier₀)
    (run : Run f c params.rho params.beta x₀ multiplier₀)
    (k : ℕ) :
    ⟪gradient f (run.point k), run.step k⟫_ℝ +
          ⟪run.multiplier k, fderiv ℝ c (run.point k) (run.step k)⟫_ℝ +
        (params.rho / 2) *
          (‖c (run.point k) + fderiv ℝ c (run.point k) (run.step k)‖ ^ 2 -
            ‖c (run.point k)‖ ^ 2) =
      -params.beta * ‖run.step k‖ ^ 2 -
        (params.rho / 2) *
          ‖fderiv ℝ c (run.point k) (run.step k)‖ ^ 2 := by
  -- Pair the exact vector optimality equation with the step.
  have hoptimal := congrArg (fun v ↦ ⟪v, run.step k⟫_ℝ) (run.optimality k)
  simp only [inner_add_left, inner_sub_left, inner_neg_left, inner_smul_left,
    starRingEnd_apply, star_trivial, ContinuousLinearMap.adjoint_inner_left,
    real_inner_self_eq_norm_sq] at hoptimal
  -- Expanding the penalty square turns the paired equation into the claimed identity.
  rw [norm_add_sq_real]
  nlinarith

/-- Helper for Lemma 2.7: the true constraint value is its linearized value plus
the stored nonlinear error. -/
private lemma constraintValue_eq_linearization_add_error
    (h : EqualityConstrained.Regularity f c)
    (params : Parameters h x₀ multiplier₀)
    (run : Run f c params.rho params.beta x₀ multiplier₀)
    (k : ℕ) :
    c (run.point (k + 1)) =
      c (run.point k) + fderiv ℝ c (run.point k) (run.step k) + run.error k := by
  -- Rearrange the definition of the stored linearization error.
  rw [run.error_def]
  module

/-- Helper for Lemma 2.7: one augmented-Lagrangian difference splits into its
linearized part, objective remainder, and constraint remainder. -/
private lemma augmentedLagrangianChange_eq_linearized
    (h : EqualityConstrained.Regularity f c)
    (params : Parameters h x₀ multiplier₀)
    (run : Run f c params.rho params.beta x₀ multiplier₀)
    (k : ℕ) :
    ℒ[f, c; params.rho](run.point (k + 1), run.multiplier k) -
        ℒ[f, c; params.rho](run.point k, run.multiplier k) =
      (f (run.point (k + 1)) - f (run.point k)) +
        ⟪run.multiplier k, fderiv ℝ c (run.point k) (run.step k)⟫_ℝ +
        (params.rho / 2) *
          (‖c (run.point k) + fderiv ℝ c (run.point k) (run.step k)‖ ^ 2 -
            ‖c (run.point k)‖ ^ 2) +
        ⟪run.multiplier k + (params.rho : ℝ) •
            (c (run.point k) + fderiv ℝ c (run.point k) (run.step k)),
          run.error k⟫_ℝ +
        (params.rho / 2) * ‖run.error k‖ ^ 2 := by
  -- Substitute the stable linearization-error interface and expand one norm square.
  rw [augmentedLagrangian_def, augmentedLagrangian_def,
    constraintValue_eq_linearization_add_error h params run k, norm_add_sq_real]
  simp only [inner_add_right, inner_add_left, inner_smul_left,
    starRingEnd_apply, star_trivial]
  ring

/-- Helper for Lemma 2.7: the constraint linearization error contributes at most
the constraint part of the model constant times the squared step norm. -/
private lemma constraintRemainderContribution_le
    (h : EqualityConstrained.Regularity f c)
    (params : Parameters h x₀ multiplier₀)
    (run : Run f c params.rho params.beta x₀ multiplier₀)
    (k : ℕ)
    (hsegment : segment ℝ (run.point k) (run.point (k + 1)) ⊆ h.region)
    (hstep : ‖run.step k‖ ≤ params.delta)
    (heffective :
      ‖run.multiplier k + (params.rho : ℝ) • c (run.point k)‖ ≤
        3 * (params.multiplierBound : ℝ)) :
    ⟪run.multiplier k + (params.rho : ℝ) •
          (c (run.point k) + fderiv ℝ c (run.point k) (run.step k)),
        run.error k⟫_ℝ +
        (params.rho / 2) * ‖run.error k‖ ^ 2 ≤
      (linearizationConstant h *
          (3 * params.multiplierBound +
            params.rho * h.constraintGradientBound * params.delta) +
        (params.rho / 2) * linearizationConstant h ^ 2 * params.delta ^ 2) *
          ‖run.step k‖ ^ 2 := by
  -- On the segment, the derivative norm is controlled through its adjoint.
  have hx : run.point k ∈ h.region :=
    hsegment (left_mem_segment ℝ _ _)
  have hderivativeNorm :
      ‖fderiv ℝ c (run.point k)‖ ≤ h.constraintGradientBound := by
    rw [← LinearIsometryEquiv.norm_map ContinuousLinearMap.adjoint]
    exact h.norm_constraintGradient_le (run.point k) hx
  have hlinearizedStep :
      ‖fderiv ℝ c (run.point k) (run.step k)‖ ≤
        h.constraintGradientBound * ‖run.step k‖ := by
    calc
      ‖fderiv ℝ c (run.point k) (run.step k)‖ ≤
          ‖fderiv ℝ c (run.point k)‖ * ‖run.step k‖ :=
        (fderiv ℝ c (run.point k)).le_opNorm (run.step k)
      _ ≤ h.constraintGradientBound * ‖run.step k‖ :=
        mul_le_mul_of_nonneg_right hderivativeNorm (norm_nonneg _)
  -- Add the derivative increment to the effective-multiplier bound.
  have heffectiveLinearized :
      ‖run.multiplier k + (params.rho : ℝ) •
          (c (run.point k) + fderiv ℝ c (run.point k) (run.step k))‖ ≤
        3 * params.multiplierBound +
          params.rho * h.constraintGradientBound * params.delta := by
    have hdecomposition :
        run.multiplier k + (params.rho : ℝ) •
            (c (run.point k) + fderiv ℝ c (run.point k) (run.step k)) =
          (run.multiplier k + (params.rho : ℝ) • c (run.point k)) +
            (params.rho : ℝ) •
              fderiv ℝ c (run.point k) (run.step k) := by
      module
    rw [hdecomposition]
    calc
      ‖(run.multiplier k + (params.rho : ℝ) • c (run.point k)) +
          (params.rho : ℝ) •
            fderiv ℝ c (run.point k) (run.step k)‖ ≤
          ‖run.multiplier k + (params.rho : ℝ) • c (run.point k)‖ +
            ‖(params.rho : ℝ) •
              fderiv ℝ c (run.point k) (run.step k)‖ := norm_add_le _ _
      _ ≤ 3 * params.multiplierBound +
          params.rho * (h.constraintGradientBound * ‖run.step k‖) := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos run.rho_pos]
        exact add_le_add heffective
          (mul_le_mul_of_nonneg_left hlinearizedStep run.rho_pos.le)
      _ ≤ 3 * params.multiplierBound +
          params.rho * h.constraintGradientBound * params.delta := by
        have hcoefficient :
            (0 : ℝ) ≤ params.rho * h.constraintGradientBound := by positivity
        nlinarith [mul_le_mul_of_nonneg_left hstep hcoefficient]
  -- The stored error estimate supplies the quadratic remainder scale.
  have herror := run.error_le h k hsegment
  have hlinearizedBoundNonneg :
      (0 : ℝ) ≤ 3 * params.multiplierBound +
        params.rho * h.constraintGradientBound * params.delta :=
    (norm_nonneg _).trans heffectiveLinearized
  have hinnerContribution :
      ⟪run.multiplier k + (params.rho : ℝ) •
            (c (run.point k) + fderiv ℝ c (run.point k) (run.step k)),
          run.error k⟫_ℝ ≤
        linearizationConstant h *
          (3 * params.multiplierBound +
            params.rho * h.constraintGradientBound * params.delta) *
              ‖run.step k‖ ^ 2 := by
    calc
      ⟪run.multiplier k + (params.rho : ℝ) •
            (c (run.point k) + fderiv ℝ c (run.point k) (run.step k)),
          run.error k⟫_ℝ ≤
          ‖run.multiplier k + (params.rho : ℝ) •
            (c (run.point k) + fderiv ℝ c (run.point k) (run.step k))‖ *
              ‖run.error k‖ := real_inner_le_norm _ _
      _ ≤ (3 * params.multiplierBound +
            params.rho * h.constraintGradientBound * params.delta) *
          (linearizationConstant h * ‖run.step k‖ ^ 2) :=
        mul_le_mul heffectiveLinearized herror (norm_nonneg _) hlinearizedBoundNonneg
      _ = linearizationConstant h *
          (3 * params.multiplierBound +
            params.rho * h.constraintGradientBound * params.delta) *
              ‖run.step k‖ ^ 2 := by ring
  -- Squaring the error estimate and the step-radius bound controls the penalty remainder.
  have hdeltaNonneg : (0 : ℝ) ≤ params.delta := by positivity
  have hstepSq :
      ‖run.step k‖ ^ 2 ≤ (params.delta : ℝ) ^ 2 :=
    (sq_le_sq₀ (norm_nonneg _) hdeltaNonneg).2 hstep
  have herrorSq :
      ‖run.error k‖ ^ 2 ≤
        linearizationConstant h ^ 2 * params.delta ^ 2 * ‖run.step k‖ ^ 2 := by
    have herrorBoundNonneg :
        (0 : ℝ) ≤ linearizationConstant h * ‖run.step k‖ ^ 2 := by positivity
    have hsquaredError :
        ‖run.error k‖ ^ 2 ≤
          (linearizationConstant h * ‖run.step k‖ ^ 2) ^ 2 :=
      (sq_le_sq₀ (norm_nonneg _) herrorBoundNonneg).2 herror
    calc
      ‖run.error k‖ ^ 2 ≤
          (linearizationConstant h * ‖run.step k‖ ^ 2) ^ 2 := hsquaredError
      _ = linearizationConstant h ^ 2 *
          ‖run.step k‖ ^ 2 * ‖run.step k‖ ^ 2 := by ring
      _ ≤ linearizationConstant h ^ 2 *
          (params.delta : ℝ) ^ 2 * ‖run.step k‖ ^ 2 := by
        gcongr
      _ = linearizationConstant h ^ 2 * params.delta ^ 2 *
          ‖run.step k‖ ^ 2 := by ring
  have hpenaltyContribution :
      (params.rho / 2) * ‖run.error k‖ ^ 2 ≤
        (params.rho / 2) * linearizationConstant h ^ 2 * params.delta ^ 2 *
          ‖run.step k‖ ^ 2 := by
    have hrhoHalf : (0 : ℝ) ≤ (params.rho : ℝ) / 2 := by positivity
    calc
      (params.rho / 2) * ‖run.error k‖ ^ 2 ≤
          (params.rho / 2) *
            (linearizationConstant h ^ 2 * params.delta ^ 2 *
              ‖run.step k‖ ^ 2) :=
        mul_le_mul_of_nonneg_left herrorSq hrhoHalf
      _ = (params.rho / 2) * linearizationConstant h ^ 2 * params.delta ^ 2 *
          ‖run.step k‖ ^ 2 := by ring
  -- Add the pairing and penalty estimates in the model-constant normal form.
  nlinarith

/-- Helper for Lemma 2.7: the true augmented-Lagrangian change is bounded by its
linearized change plus the model constant times the squared step norm. -/
private lemma augmentedLagrangianChange_le_modelConstant
    (h : EqualityConstrained.Regularity f c)
    (params : Parameters h x₀ multiplier₀)
    (run : Run f c params.rho params.beta x₀ multiplier₀)
    (k : ℕ)
    (hsegment : segment ℝ (run.point k) (run.point (k + 1)) ⊆ h.region)
    (hstep : ‖run.step k‖ ≤ params.delta)
    (heffective :
      ‖run.multiplier k + (params.rho : ℝ) • c (run.point k)‖ ≤
        3 * (params.multiplierBound : ℝ)) :
    ℒ[f, c; params.rho](run.point (k + 1), run.multiplier k) -
        ℒ[f, c; params.rho](run.point k, run.multiplier k) ≤
      (⟪gradient f (run.point k), run.step k⟫_ℝ +
          ⟪run.multiplier k, fderiv ℝ c (run.point k) (run.step k)⟫_ℝ +
        (params.rho / 2) *
          (‖c (run.point k) + fderiv ℝ c (run.point k) (run.step k)‖ ^ 2 -
            ‖c (run.point k)‖ ^ 2)) +
        modelConstant h params.delta params.rho params.multiplierBound *
          ‖run.step k‖ ^ 2 := by
  -- The objective Taylor estimate reduces to the stored step by the point update.
  have hobjective :
      f (run.point (k + 1)) - f (run.point k) ≤
        ⟪gradient f (run.point k), run.step k⟫_ℝ +
          (h.gradientLipschitz : ℝ) / 2 * ‖run.step k‖ ^ 2 := by
    have htaylor := objectiveChange_le h (run.point k) (run.point (k + 1)) hsegment
    rw [run.point_succ, add_sub_cancel_left] at htaylor
    rw [run.point_succ]
    exact htaylor
  have hconstraint :=
    constraintRemainderContribution_le h params run k hsegment hstep heffective
  -- Expand the exact difference once and combine both independent remainder bounds.
  rw [augmentedLagrangianChange_eq_linearized h params run k, modelConstant_def]
  nlinarith

/-- Lemma 2.7: every iteration in an admissible prefix decreases the fixed-penalty
augmented Lagrangian by at least `(params.beta / 2) * ‖run.step k‖ ^ 2`. -/
theorem augmentedLagrangianDescent (h : EqualityConstrained.Regularity f c)
    (params : Parameters h x₀ multiplier₀)
    (run : Run f c params.rho params.beta x₀ multiplier₀)
    {N k : ℕ} (h_admissible : run.IsAdmissiblePrefix h N) (hk : k < N) :
    ℒ[f, c; params.rho](run.point (k + 1), run.multiplier k) ≤
      ℒ[f, c; params.rho](run.point k, run.multiplier k) -
        (params.beta / 2) * ‖run.step k‖ ^ 2 := by
  -- Admissibility and Lemma 2.6 provide the segment, step, and multiplier invariants.
  have hsegment := (run.isAdmissiblePrefix_iff h N).1 h_admissible k hk
  have hstep := run.norm_step_le h params h_admissible hk
  have hMultiplier :
      ∀ j ≤ k, ‖run.multiplier j‖ ≤ params.multiplierBound := by
    intro j hj
    apply run.norm_multiplier_le h params h_admissible
    omega
  have heffective := normEffectiveMultiplier_le h params run k hMultiplier
  -- The model-constant interface and exact optimality identity give the full decrease.
  have hchange := augmentedLagrangianChange_le_modelConstant
    h params run k hsegment hstep heffective
  rw [linearizedAugmentedLagrangianChange_eq h params run k] at hchange
  have hmodelTerm :
      modelConstant h params.delta params.rho params.multiplierBound *
          ‖run.step k‖ ^ 2 ≤
        (3 * (params.beta : ℝ) / 8) * ‖run.step k‖ ^ 2 :=
    mul_le_mul_of_nonneg_right params.modelConstant_le (sq_nonneg _)
  have hpenaltyNonneg :
      (0 : ℝ) ≤ (params.rho / 2) *
        ‖fderiv ℝ c (run.point k) (run.step k)‖ ^ 2 := by positivity
  have hproximalNonneg :
      (0 : ℝ) ≤ params.beta * ‖run.step k‖ ^ 2 :=
    mul_nonneg run.beta_pos.le (sq_nonneg _)
  have hchangeFinal :
      ℒ[f, c; params.rho](run.point (k + 1), run.multiplier k) -
          ℒ[f, c; params.rho](run.point k, run.multiplier k) ≤
        -(params.beta / 2) * ‖run.step k‖ ^ 2 := by
    nlinarith
  -- Move the old augmented-Lagrangian value back to the right-hand side.
  linarith

end LALM.Run

end
