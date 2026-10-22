/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@5bf5af722d85bd5c98368c41c4066124a15e8fd3:ReasBook/Papers/TR_LALM_theory/README.md (formalization contributor).
-/

module

public import TR_LALM_theory.Algorithm_2_1
public import TR_LALM_theory.Assumption_2_3.Parameters

public section

open scoped InnerProductSpace NNReal

namespace LALM.Run

variable {n m : ℕ}
variable {f : EuclideanSpace ℝ (Fin n) → ℝ}
variable {c : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m)}
variable {x₀ : EuclideanSpace ℝ (Fin n)}
variable {multiplier₀ : EuclideanSpace ℝ (Fin m)}

/-- Helper for Lemma 2.6: a damped normal equation inherits the sharp bounds from
the primal and dual coercivity moduli. -/
private lemma normDampedNormalEquation_le
    {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [CompleteSpace E] [CompleteSpace F]
    [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
    (T : E →L[ℝ] F) {β ρ σ : ℝ}
    (hβ : 0 < β) (hρ : 0 ≤ ρ) (hσ : 0 < σ)
    (hT : ∀ u : F, σ * ‖u‖ ≤ ‖T.adjoint u‖)
    (p g : E) (z : F)
    (hequation : β • p + ρ • T.adjoint (T p) = -g - T.adjoint z) :
    ‖p‖ ≤ ‖g‖ / β + ‖T.adjoint‖ * ‖z‖ / (β + ρ * σ ^ 2) := by
  -- Split the forcing through the primal and dual damped normal operators.
  let primal : E →L[ℝ] E :=
    β • ContinuousLinearMap.id ℝ E + ρ • (T.adjoint.comp T)
  let dual : F →L[ℝ] F :=
    β • ContinuousLinearMap.id ℝ F + ρ • (T.comp T.adjoint)
  -- Normalize the dual energy before using coercivity in either later estimate.
  have hdualEnergy (v : F) :
      ⟪v, T (T.adjoint v)⟫_ℝ = ‖T.adjoint v‖ ^ 2 := by
    rw [real_inner_comm, ← T.adjoint_inner_right, real_inner_self_eq_norm_sq]
  have hprimalInjective : Function.Injective primal := by
    intro x y hxy
    have hzero : primal (x - y) = 0 := by
      rw [map_sub, hxy, sub_self]
    have hinner := congrArg (fun w ↦ ⟪x - y, w⟫_ℝ) hzero
    simp only [primal, add_apply, smul_apply,
      ContinuousLinearMap.id_apply, ContinuousLinearMap.comp_apply, inner_add_right,
      real_inner_smul_right, ContinuousLinearMap.adjoint_inner_right,
      real_inner_self_eq_norm_sq, inner_zero_right] at hinner
    have hnormSq : ‖x - y‖ ^ 2 = 0 := by
      nlinarith [sq_nonneg ‖T (x - y)‖]
    exact sub_eq_zero.mp (norm_eq_zero.mp (sq_eq_zero_iff.mp hnormSq))
  have hdualInjective : Function.Injective dual := by
    intro x y hxy
    have hzero : dual (x - y) = 0 := by
      rw [map_sub, hxy, sub_self]
    have hinner := congrArg (fun w ↦ ⟪x - y, w⟫_ℝ) hzero
    simp only [dual, add_apply, smul_apply,
      ContinuousLinearMap.id_apply, ContinuousLinearMap.comp_apply, inner_add_right,
      real_inner_smul_right, real_inner_self_eq_norm_sq, inner_zero_right] at hinner
    rw [hdualEnergy] at hinner
    have hlower := hT (x - y)
    have hlowerSq : (σ * ‖x - y‖) ^ 2 ≤ ‖T.adjoint (x - y)‖ ^ 2 :=
      (sq_le_sq₀ (mul_nonneg hσ.le (norm_nonneg _)) (norm_nonneg _)).2 hlower
    have hnormSq : ‖x - y‖ ^ 2 = 0 := by
      nlinarith [mul_le_mul_of_nonneg_left hlowerSq hρ]
    exact sub_eq_zero.mp (norm_eq_zero.mp (sq_eq_zero_iff.mp hnormSq))
  have hprimalSurjective : Function.Surjective primal :=
    LinearMap.surjective_of_injective (f := primal.toLinearMap) hprimalInjective
  have hdualSurjective : Function.Surjective dual :=
    LinearMap.surjective_of_injective (f := dual.toLinearMap) hdualInjective
  obtain ⟨q, hq⟩ := hprimalSurjective (-g)
  obtain ⟨u, hu⟩ := hdualSurjective (-z)
  -- Primal coercivity controls the objective-gradient component.
  have hqBound : ‖q‖ ≤ ‖g‖ / β := by
    by_cases hqzero : ‖q‖ = 0
    · rw [hqzero]
      exact div_nonneg (norm_nonneg g) hβ.le
    · have hqpos : 0 < ‖q‖ := lt_of_le_of_ne (norm_nonneg q) (Ne.symm hqzero)
      have hinner := congrArg (fun w ↦ ⟪q, w⟫_ℝ) hq
      simp only [primal, add_apply, smul_apply,
        ContinuousLinearMap.id_apply, ContinuousLinearMap.comp_apply, inner_add_right,
        real_inner_smul_right, ContinuousLinearMap.adjoint_inner_right,
        real_inner_self_eq_norm_sq] at hinner
      have hupper := real_inner_le_norm q (-g)
      simp only [norm_neg] at hupper
      have hlinear : β * ‖q‖ ≤ ‖g‖ := by
        nlinarith [sq_nonneg ‖T q‖]
      exact (le_div_iff₀ hβ).2 (by simpa only [mul_comm] using hlinear)
  -- Dual coercivity gains the penalty contribution in the constraint-forced term.
  have hdenom : 0 < β + ρ * σ ^ 2 := by positivity
  have huBound : ‖u‖ ≤ ‖z‖ / (β + ρ * σ ^ 2) := by
    by_cases huzero : ‖u‖ = 0
    · rw [huzero]
      exact div_nonneg (norm_nonneg z) hdenom.le
    · have hupos : 0 < ‖u‖ := lt_of_le_of_ne (norm_nonneg u) (Ne.symm huzero)
      have hinner := congrArg (fun w ↦ ⟪u, w⟫_ℝ) hu
      simp only [dual, add_apply, smul_apply,
        ContinuousLinearMap.id_apply, ContinuousLinearMap.comp_apply, inner_add_right,
        real_inner_smul_right, real_inner_self_eq_norm_sq] at hinner
      rw [hdualEnergy] at hinner
      have hlower := hT u
      have hlowerSq : σ ^ 2 * ‖u‖ ^ 2 ≤ ‖T.adjoint u‖ ^ 2 := by
        simpa only [mul_pow] using
          (sq_le_sq₀ (mul_nonneg hσ.le (norm_nonneg _)) (norm_nonneg _)).2 hlower
      have hupper := real_inner_le_norm u (-z)
      simp only [norm_neg] at hupper
      have hlinear : (β + ρ * σ ^ 2) * ‖u‖ ≤ ‖z‖ := by
        nlinarith [mul_le_mul_of_nonneg_left hlowerSq hρ]
      exact (le_div_iff₀ hdenom).2 (by simpa only [mul_comm] using hlinear)
  -- The intertwining identity reconstructs the original solution from both pieces.
  have hintertwine (v : F) : primal (T.adjoint v) = T.adjoint (dual v) := by
    simp only [primal, dual, add_apply,
      smul_apply, ContinuousLinearMap.id_apply,
      ContinuousLinearMap.comp_apply, map_add, map_smul]
  have hpEquation : primal p = -g - T.adjoint z := by
    simpa only [primal, add_apply, smul_apply,
      ContinuousLinearMap.id_apply, ContinuousLinearMap.comp_apply] using hequation
  have hcandidate : primal (q + T.adjoint u) = -g - T.adjoint z := by
    rw [map_add, hq, hintertwine, hu, map_neg]
    simp only [sub_eq_add_neg]
  have hpDecomposition : p = q + T.adjoint u :=
    hprimalInjective (hpEquation.trans hcandidate.symm)
  have hadjointBound :
      ‖T.adjoint u‖ ≤ ‖T.adjoint‖ * ‖z‖ / (β + ρ * σ ^ 2) := by
    calc
      ‖T.adjoint u‖ ≤ ‖T.adjoint‖ * ‖u‖ := T.adjoint.le_opNorm u
      _ ≤ ‖T.adjoint‖ * (‖z‖ / (β + ρ * σ ^ 2)) :=
        mul_le_mul_of_nonneg_left huBound (norm_nonneg _)
      _ = ‖T.adjoint‖ * ‖z‖ / (β + ρ * σ ^ 2) := by ring
  calc
    ‖p‖ = ‖q + T.adjoint u‖ := congrArg norm hpDecomposition
    _ ≤ ‖q‖ + ‖T.adjoint u‖ := norm_add_le _ _
    _ ≤ ‖g‖ / β + ‖T.adjoint‖ * ‖z‖ / (β + ρ * σ ^ 2) :=
      add_le_add hqBound hadjointBound

/-- Helper for Lemma 2.6: bounded multipliers control the effective multiplier in
the primal normal equation. -/
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
      -- At initialization the two defining parameter bounds control the two summands.
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
      -- The update rewrites the effective multiplier as `2 λ_{k+1} - λ_k`.
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

/-- Helper for Lemma 2.6: regularity and an effective-multiplier bound control one
primal step. -/
private lemma normStep_le_of_normEffectiveMultiplier_le
    (h : EqualityConstrained.Regularity f c)
    (params : Parameters h x₀ multiplier₀)
    (run : Run f c params.rho params.beta x₀ multiplier₀)
    (k : ℕ) (hx : run.point k ∈ h.region)
    (heffective :
      ‖run.multiplier k + (params.rho : ℝ) • c (run.point k)‖ ≤
        3 * params.multiplierBound) :
    ‖run.step k‖ ≤ params.delta := by
  -- Apply the damped estimate to the exact model-optimality equation.
  have hestimate := normDampedNormalEquation_le
    (fderiv ℝ c (run.point k)) run.beta_pos run.rho_pos.le h.licqModulus_pos
    (h.licqLowerBound (run.point k) hx) (run.step k) (gradient f (run.point k))
    (run.multiplier k + params.rho • c (run.point k)) (run.optimality k)
  have hgradient := h.norm_gradient_le (run.point k) hx
  -- Stay in the adjoint spelling used by the normal-equation estimate.
  have hoperator :
      ‖ContinuousLinearMap.adjoint (fderiv ℝ c (run.point k))‖ ≤
        h.constraintGradientBound := by
    simpa only [EqualityConstrained.constraintGradient_def] using
      h.norm_constraintGradient_le (run.point k) hx
  have hdenom :
      0 < (params.beta : ℝ) + params.rho * (h.licqModulus : ℝ) ^ 2 := by
    exact add_pos_of_pos_of_nonneg run.beta_pos
      (mul_nonneg run.rho_pos.le (sq_nonneg (h.licqModulus : ℝ)))
  have hgradientTerm :
      ‖gradient f (run.point k)‖ / params.beta ≤ h.gradientBound / params.beta :=
    (div_le_div_iff_of_pos_right run.beta_pos).2 hgradient
  have hproduct :
      ‖ContinuousLinearMap.adjoint (fderiv ℝ c (run.point k))‖ *
          ‖run.multiplier k + params.rho • c (run.point k)‖ ≤
        h.constraintGradientBound * (3 * params.multiplierBound) :=
    mul_le_mul hoperator heffective (norm_nonneg _)
      (NNReal.coe_nonneg h.constraintGradientBound)
  have hconstraintTerm :
      ‖ContinuousLinearMap.adjoint (fderiv ℝ c (run.point k))‖ *
          ‖run.multiplier k + params.rho • c (run.point k)‖ /
            (params.beta + params.rho * (h.licqModulus : ℝ) ^ 2) ≤
        3 * h.constraintGradientBound * params.multiplierBound /
            (params.beta + params.rho * (h.licqModulus : ℝ) ^ 2) := by
    rw [div_le_div_iff_of_pos_right hdenom]
    nlinarith
  calc
    ‖run.step k‖ ≤
        ‖gradient f (run.point k)‖ / params.beta +
          ‖ContinuousLinearMap.adjoint (fderiv ℝ c (run.point k))‖ *
            ‖run.multiplier k + params.rho • c (run.point k)‖ /
              (params.beta + params.rho * (h.licqModulus : ℝ) ^ 2) := by
      exact hestimate
    _ ≤ h.gradientBound / params.beta +
        3 * h.constraintGradientBound * params.multiplierBound /
          (params.beta + params.rho * (h.licqModulus : ℝ) ^ 2) :=
      add_le_add hgradientTerm hconstraintTerm
    _ ≤ params.delta := params.comparisonBound_le

/-- Helper for Lemma 2.6: an admissible bounded step propagates the multiplier
bound through one iteration. -/
private lemma normMultiplier_succ_le_of_normStep_le
    (h : EqualityConstrained.Regularity f c)
    (params : Parameters h x₀ multiplier₀)
    (run : Run f c params.rho params.beta x₀ multiplier₀)
    (k : ℕ)
    (hsegment : segment ℝ (run.point k) (run.point (k + 1)) ⊆ h.region)
    (hstep : ‖run.step k‖ ≤ params.delta) :
    ‖run.multiplier (k + 1)‖ ≤ params.multiplierBound := by
  -- LICQ converts the perturbed multiplier identity into a scalar norm estimate.
  have hx : run.point k ∈ h.region := hsegment (left_mem_segment ℝ _ _)
  have hidentity :
      EqualityConstrained.constraintGradient c (run.point k)
          (run.multiplier (k + 1)) =
        -gradient f (run.point k) - (params.beta : ℝ) • run.step k +
          (params.rho : ℝ) • EqualityConstrained.constraintGradient c (run.point k)
            (run.error k) := by
    linear_combination (norm := module) run.perturbedMultiplierIdentity k
  have hstepSq : ‖run.step k‖ ^ 2 ≤ (params.delta : ℝ) ^ 2 :=
    (sq_le_sq₀ (norm_nonneg _) (NNReal.coe_nonneg _)).2 hstep
  have herror := run.error_le h k hsegment
  have herrorBound :
      ‖run.error k‖ ≤ linearizationConstant h * (params.delta : ℝ) ^ 2 :=
    herror.trans (mul_le_mul_of_nonneg_left hstepSq (NNReal.coe_nonneg _))
  have hgradient := h.norm_gradient_le (run.point k) hx
  have hoperator := h.norm_constraintGradient_le (run.point k) hx
  have hperturbation :
      ‖(params.rho : ℝ) • EqualityConstrained.constraintGradient c (run.point k)
          (run.error k)‖ ≤
        params.rho * h.constraintGradientBound * linearizationConstant h *
          (params.delta : ℝ) ^ 2 := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos run.rho_pos]
    calc
      params.rho *
          ‖EqualityConstrained.constraintGradient c (run.point k) (run.error k)‖ ≤
          params.rho *
            (‖EqualityConstrained.constraintGradient c (run.point k)‖ *
              ‖run.error k‖) :=
        mul_le_mul_of_nonneg_left
          ((EqualityConstrained.constraintGradient c (run.point k)).le_opNorm
            (run.error k)) run.rho_pos.le
      _ ≤ params.rho *
          (h.constraintGradientBound *
            (linearizationConstant h * (params.delta : ℝ) ^ 2)) := by
        gcongr
      _ = params.rho * h.constraintGradientBound * linearizationConstant h *
          (params.delta : ℝ) ^ 2 := by ring
  have hnormalBound :
      ‖EqualityConstrained.constraintGradient c (run.point k)
          (run.multiplier (k + 1))‖ ≤
        h.gradientBound + params.beta * params.delta +
          params.rho * h.constraintGradientBound * linearizationConstant h *
            (params.delta : ℝ) ^ 2 := by
    rw [hidentity]
    calc
      ‖-gradient f (run.point k) - params.beta • run.step k +
          (params.rho : ℝ) • EqualityConstrained.constraintGradient c (run.point k)
            (run.error k)‖ ≤
          ‖-gradient f (run.point k) - params.beta • run.step k‖ +
            ‖(params.rho : ℝ) • EqualityConstrained.constraintGradient c (run.point k)
              (run.error k)‖ := norm_add_le _ _
      _ ≤ (‖gradient f (run.point k)‖ + params.beta * ‖run.step k‖) +
          ‖(params.rho : ℝ) • EqualityConstrained.constraintGradient c (run.point k)
            (run.error k)‖ := by
        gcongr
        calc
          ‖-gradient f (run.point k) - (params.beta : ℝ) • run.step k‖ ≤
              ‖-gradient f (run.point k)‖ + ‖(params.beta : ℝ) • run.step k‖ :=
            norm_sub_le _ _
          _ = ‖gradient f (run.point k)‖ + params.beta * ‖run.step k‖ := by
            rw [norm_neg, norm_smul, Real.norm_eq_abs, abs_of_pos run.beta_pos]
      _ ≤ h.gradientBound + params.beta * params.delta +
          params.rho * h.constraintGradientBound * linearizationConstant h *
            (params.delta : ℝ) ^ 2 := by
        nlinarith [mul_le_mul_of_nonneg_left hstep run.beta_pos.le]
  have hlicq := h.licqLowerBound (run.point k) hx (run.multiplier (k + 1))
  have hscaled :
      (h.licqModulus : ℝ) * ‖run.multiplier (k + 1)‖ ≤
        h.gradientBound + params.beta * params.delta +
          params.rho * h.constraintGradientBound * linearizationConstant h *
            (params.delta : ℝ) ^ 2 := hlicq.trans hnormalBound
  have hquotient :
      ‖run.multiplier (k + 1)‖ ≤
        (h.gradientBound + params.beta * params.delta +
          params.rho * h.constraintGradientBound * linearizationConstant h *
            (params.delta : ℝ) ^ 2) / h.licqModulus := by
    rw [le_div_iff₀ (NNReal.coe_pos.2 h.licqModulus_pos)]
    simpa only [mul_comm] using hscaled
  exact hquotient.trans params.parameterBound_le

/-- Helper for Lemma 2.6: admissibility propagates the step and multiplier bounds
simultaneously along every finite prefix. -/
private lemma admissiblePrefix_normBounds
    (h : EqualityConstrained.Regularity f c)
    (params : Parameters h x₀ multiplier₀)
    (run : Run f c params.rho params.beta x₀ multiplier₀)
    (N : ℕ) (h_admissible : run.IsAdmissiblePrefix h N) :
    (∀ k < N, ‖run.step k‖ ≤ params.delta) ∧
      (∀ k ≤ N, ‖run.multiplier k‖ ≤ params.multiplierBound) := by
  -- Induct on completed iterations while carrying both mutually supporting invariants.
  induction N with
  | zero =>
      constructor
      · intro k hk
        omega
      · intro k hk
        have hkzero : k = 0 := by omega
        subst k
        rw [run.multiplier_zero]
        exact params.norm_multiplier₀_le
  | succ N ih =>
      have hsegments := (run.isAdmissiblePrefix_iff h (N + 1)).1 h_admissible
      have hprefix : run.IsAdmissiblePrefix h N :=
        (run.isAdmissiblePrefix_iff h N).2 fun j hj ↦
          hsegments j (Nat.lt_succ_of_lt hj)
      have hbounds := ih hprefix
      have hsegment := hsegments N (Nat.lt_succ_self N)
      have hx : run.point N ∈ h.region := hsegment (left_mem_segment ℝ _ _)
      have heffective := normEffectiveMultiplier_le h params run N hbounds.2
      have hnewStep :=
        normStep_le_of_normEffectiveMultiplier_le h params run N hx heffective
      have hnewMultiplier :=
        normMultiplier_succ_le_of_normStep_le h params run N hsegment hnewStep
      constructor
      · intro k hk
        by_cases hkold : k < N
        · exact hbounds.1 k hkold
        · have hkeq : k = N := by omega
          simpa only [hkeq] using hnewStep
      · intro k hk
        by_cases hkold : k ≤ N
        · exact hbounds.2 k hkold
        · have hkeq : k = N + 1 := by omega
          simpa only [hkeq] using hnewMultiplier

/-- Lemma 2.6 (1): every primal step among the first `N` completed iterations of an
admissible prefix has norm at most the chosen step-radius parameter `Δ`. -/
theorem norm_step_le (h : EqualityConstrained.Regularity f c)
    (params : Parameters h x₀ multiplier₀)
    (run : Run f c params.rho params.beta x₀ multiplier₀)
    {N k : ℕ} (h_admissible : run.IsAdmissiblePrefix h N) (hk : k < N) :
    ‖run.step k‖ ≤ params.delta := by
  -- Project the primal half of the simultaneous prefix invariant.
  exact (admissiblePrefix_normBounds h params run N h_admissible).1 k hk

/-- Lemma 2.6 (2): every multiplier through index `N` of an admissible prefix has norm
at most the chosen multiplier bound `Λ`. -/
theorem norm_multiplier_le (h : EqualityConstrained.Regularity f c)
    (params : Parameters h x₀ multiplier₀)
    (run : Run f c params.rho params.beta x₀ multiplier₀)
    {N k : ℕ} (h_admissible : run.IsAdmissiblePrefix h N) (hk : k ≤ N) :
    ‖run.multiplier k‖ ≤ params.multiplierBound := by
  -- Project the dual half of the simultaneous prefix invariant.
  exact (admissiblePrefix_normBounds h params run N h_admissible).2 k hk

end LALM.Run

end
