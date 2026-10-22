/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@5bf5af722d85bd5c98368c41c4066124a15e8fd3:ReasBook/Papers/TR_LALM_theory/README.md (formalization contributor).
-/

module

import TR_LALM_theory.Lemma_3_3
public import TR_LALM_theory.Lemma_3_4.BatchSize
public import TR_LALM_theory.Lemma_3_4.Multiplier

public section

open MeasureTheory
open scoped InnerProductSpace LALM NNReal

namespace LALM.StochasticRun

universe u v

variable {n m : ℕ}
variable {Ξ : Type u} [MeasurableSpace Ξ] {ν : Measure Ξ} [IsProbabilityMeasure ν]
variable {Ω : Type v} [MeasurableSpace Ω] {ℙ : Measure Ω} [IsProbabilityMeasure ℙ]
variable {f : EuclideanSpace ℝ (Fin n) → ℝ}
variable {c : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m)}
variable {x₀ : EuclideanSpace ℝ (Fin n)}
variable {multiplier₀ : EuclideanSpace ℝ (Fin m)}
variable {h : EqualityConstrained.Regularity f c}
variable {oracle : EqualityConstrained.StochasticOracle f h.region ν}
variable {params : LALM.Parameters h x₀ multiplier₀} {Q B b : ℕ+}
variable (run : StochasticRun h oracle ℙ x₀ multiplier₀ params Q B b)

/-- Helper for Lemma 3.4: a damped normal equation inherits bounds from its
primal and dual coercivity moduli. -/
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
      have hlinearCommuted : ‖q‖ * β ≤ ‖g‖ := by
        simpa only [mul_comm] using hlinear
      exact (le_div_iff₀ hβ).2 hlinearCommuted
  -- Dual coercivity gains the penalty contribution in the constraint term.
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
      have hlinearCommuted : ‖u‖ * (β + ρ * σ ^ 2) ≤ ‖z‖ := by
        simpa only [mul_comm] using hlinear
      exact (le_div_iff₀ hdenom).2 hlinearCommuted
  -- Intertwining reconstructs the original solution from the two pieces.
  have hintertwine (v : F) : primal (T.adjoint v) = T.adjoint (dual v) := by
    simp only [primal, dual, add_apply, smul_apply, ContinuousLinearMap.id_apply,
      ContinuousLinearMap.comp_apply, map_add, map_smul]
  have hpEquation : primal p = -g - T.adjoint z := by
    simpa only [primal, add_apply, smul_apply, ContinuousLinearMap.id_apply,
      ContinuousLinearMap.comp_apply] using hequation
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

/-- Helper for Lemma 3.4: the derivative of the explicit-gradient step model
is represented by its canonical first-order vector. -/
private lemma hasFDerivAtStepModelWithGradient
    (c : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m))
    (g : EuclideanSpace ℝ (Fin n)) (ρ β : ℝ)
    (x : EuclideanSpace ℝ (Fin n))
    (multiplier : EuclideanSpace ℝ (Fin m))
    (p : EuclideanSpace ℝ (Fin n)) :
    HasFDerivAt (stepModelWithGradient c g ρ β x multiplier)
      (innerSL ℝ (g + EqualityConstrained.constraintGradient c x
        (multiplier + ρ • (c x + fderiv ℝ c x p)) + β • p)) p := by
  -- Differentiate the affine constraint model and reuse it in both quadratic terms.
  have haffine : HasFDerivAt
      (fun q ↦ c x + fderiv ℝ c x q) (fderiv ℝ c x) p := by
    fun_prop
  have hobjective : HasFDerivAt
      (fun q ↦ ⟪g, q⟫_ℝ) (innerSL ℝ g) p := by
    simpa only [coe_innerSL_apply] using (innerSL ℝ g).hasFDerivAt
  have hmultiplier : HasFDerivAt
      (fun q ↦ ⟪multiplier, c x + fderiv ℝ c x q⟫_ℝ)
      (innerSL ℝ (EqualityConstrained.constraintGradient c x multiplier)) p := by
    simpa only [Function.comp_def, innerSL_apply_apply,
      EqualityConstrained.constraintGradient_def,
      ContinuousLinearMap.innerSL_apply_comp] using
        (innerSL ℝ multiplier).hasFDerivAt.comp p haffine
  have hpenalty : HasFDerivAt
      (fun q ↦ (ρ / 2) * ‖c x + fderiv ℝ c x q‖ ^ 2)
      ((ρ / 2) • 2 • innerSL ℝ (EqualityConstrained.constraintGradient c x
        (c x + fderiv ℝ c x p))) p := by
    simpa only [EqualityConstrained.constraintGradient_def,
      ContinuousLinearMap.innerSL_apply_comp] using
        haffine.norm_sq.const_mul (ρ / 2)
  have hproximal : HasFDerivAt (fun q ↦ (β / 2) * ‖q‖ ^ 2)
      ((β / 2) • 2 • innerSL ℝ p) p := by
    simpa only [id_eq, ContinuousLinearMap.comp_id] using
      (hasFDerivAt_id p).norm_sq.const_mul (β / 2)
  -- Collect the four derivatives into the visible first-order normal form.
  let modelDerivative : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ :=
    ((innerSL ℝ g +
        innerSL ℝ (EqualityConstrained.constraintGradient c x multiplier)) +
      ((ρ / 2) • (2 • innerSL ℝ (EqualityConstrained.constraintGradient c x
        (c x + fderiv ℝ c x p))))) + ((β / 2) • (2 • innerSL ℝ p))
  have hsum : HasFDerivAt
      ((((fun q ↦ ⟪g, q⟫_ℝ) +
          fun q ↦ ⟪multiplier, c x + fderiv ℝ c x q⟫_ℝ) +
          fun q ↦ (ρ / 2) * ‖c x + fderiv ℝ c x q‖ ^ 2) +
        fun q ↦ (β / 2) * ‖q‖ ^ 2) modelDerivative p := by
    simpa only [modelDerivative] using
      ((hobjective.add hmultiplier).add hpenalty).add hproximal
  have hderivativeEq : modelDerivative =
      innerSL ℝ (g + EqualityConstrained.constraintGradient c x
        (multiplier + ρ • (c x + fderiv ℝ c x p)) + β • p) := by
    ext v
    simp only [map_add, map_smul, innerSL_apply_apply, add_apply, smul_apply,
      EqualityConstrained.constraintGradient_def, modelDerivative]
    ring
  have hfunctions : stepModelWithGradient c g ρ β x multiplier =ᶠ[nhds p]
      ((((fun q ↦ ⟪g, q⟫_ℝ) +
          fun q ↦ ⟪multiplier, c x + fderiv ℝ c x q⟫_ℝ) +
          fun q ↦ (ρ / 2) * ‖c x + fderiv ℝ c x q‖ ^ 2) +
        fun q ↦ (β / 2) * ‖q‖ ^ 2) := by
    filter_upwards with q
    exact stepModelWithGradient_def c g ρ β x multiplier q
  exact (hsum.congr_of_eventuallyEq hfunctions).congr_fderiv hderivativeEq

/-- Helper for Lemma 3.4: a minimizer of the explicit-gradient step model
satisfies its canonical first-order equation. -/
private lemma stepModelWithGradientOptimality
    (c : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m))
    (g : EuclideanSpace ℝ (Fin n)) (ρ β : ℝ)
    (x : EuclideanSpace ℝ (Fin n))
    (multiplier : EuclideanSpace ℝ (Fin m))
    (p : EuclideanSpace ℝ (Fin n))
    (hp : IsMinOn (stepModelWithGradient c g ρ β x multiplier) Set.univ p) :
    g + EqualityConstrained.constraintGradient c x
        (multiplier + ρ • (c x + fderiv ℝ c x p)) + β • p = 0 := by
  -- Fermat's rule annihilates the explicit derivative computed above.
  have hderiv : innerSL ℝ (g + EqualityConstrained.constraintGradient c x
      (multiplier + ρ • (c x + fderiv ℝ c x p)) + β • p) = 0 :=
    (hp.isLocalMin Filter.univ_mem).hasFDerivAt_eq_zero
      (hasFDerivAtStepModelWithGradient c g ρ β x multiplier p)
  have hnormSq :
      ‖g + EqualityConstrained.constraintGradient c x
        (multiplier + ρ • (c x + fderiv ℝ c x p)) + β • p‖ ^ 2 = 0 := by
    simpa only [innerSL_apply_apply, real_inner_self_eq_norm_sq, zero_apply] using
      congrArg (fun A ↦ A (g + EqualityConstrained.constraintGradient c x
        (multiplier + ρ • (c x + fderiv ℝ c x p)) + β • p)) hderiv
  exact norm_eq_zero.mp (sq_eq_zero_iff.mp hnormSq)

/-- Helper for Lemma 3.4: the stochastic constraint linearization error is the
nonlinear increment minus its first-order prediction. -/
private noncomputable def linearizationError
    (run : StochasticRun h oracle ℙ x₀ multiplier₀ params Q B b)
    (k : ℕ) (ω : Ω) : EuclideanSpace ℝ (Fin m) :=
  c (run.point (k + 1) ω) - c (run.point k ω) -
    fderiv ℝ c (run.point k ω) (run.step k ω)

/-- Helper for Lemma 3.4: an admissible stochastic segment has quadratically
small constraint linearization error. -/
private lemma normLinearizationError_le
    (run : StochasticRun h oracle ℙ x₀ multiplier₀ params Q B b)
    (k : ℕ) (ω : Ω)
    (hsegment : segment ℝ (run.point k ω) (run.point (k + 1) ω) ⊆ h.region) :
    ‖linearizationError run k ω‖ ≤
      linearizationConstant h * ‖run.step k ω‖ ^ 2 := by
  -- Apply the segmentwise Taylor estimate and identify the displacement by the update.
  have hremainder := norm_sub_sub_fderiv_le c h.constraintGradientLipschitz h.region
    (run.point k ω) (run.point (k + 1) ω)
    (fun _ hz ↦ h.differentiableAt_constraint hz)
    h.lipschitzOn_constraintFDeriv hsegment
  simpa only [linearizationError, run.point_succ, add_sub_cancel_left,
    linearizationConstant_def, NNReal.coe_div, NNReal.coe_ofNat] using hremainder

/-- Helper for Lemma 3.4: stochastic model optimality and the multiplier update
give the perturbed multiplier identity. -/
private lemma perturbedMultiplierIdentity
    (run : StochasticRun h oracle ℙ x₀ multiplier₀ params Q B b)
    (k : ℕ) (ω : Ω) :
    run.gradientEstimate k ω +
        EqualityConstrained.constraintGradient c (run.point k ω)
          (run.multiplier (k + 1) ω) +
        (params.beta : ℝ) • run.step k ω =
      (params.rho : ℝ) • EqualityConstrained.constraintGradient c (run.point k ω)
        (linearizationError run k ω) := by
  -- Normalize the run-facing estimator before rearranging the first-order equation.
  have hoptimal := stepModelWithGradientOptimality c
    (SPIDER.estimate h.gradientBound oracle run.point run.sample Q B b k ω)
    params.rho params.beta (run.point k ω) (run.multiplier k ω)
    (run.step k ω) (run.minimizes_step k ω)
  rw [← run.gradientEstimate_apply] at hoptimal
  have hupdate :
      run.multiplier (k + 1) ω = run.multiplier k ω +
        (params.rho : ℝ) • c (run.point (k + 1) ω) :=
    run.multiplier_succ k ω
  have hmultiplierDecomposition :
      run.multiplier (k + 1) ω =
        run.multiplier k ω + (params.rho : ℝ) •
          (c (run.point k ω) + fderiv ℝ c (run.point k ω) (run.step k ω)) +
        (params.rho : ℝ) • linearizationError run k ω := by
    rw [hupdate, linearizationError]
    module
  rw [hmultiplierDecomposition, map_add, map_smul]
  linear_combination (norm := module) hoptimal

/-- Helper for Lemma 3.4: bounded stochastic multipliers control the effective
multiplier in one pathwise normal equation. -/
lemma normEffectiveMultiplier_le
    (run : StochasticRun h oracle ℙ x₀ multiplier₀ params Q B b)
    (k : ℕ) (ω : Ω)
    (hMultiplier : ∀ j ≤ k, ‖run.multiplier j ω‖ ≤ params.multiplierBound) :
    ‖run.multiplier k ω + (params.rho : ℝ) • c (run.point k ω)‖ ≤
      3 * (params.multiplierBound : ℝ) := by
  cases k with
  | zero =>
      -- Initialization is controlled by the two defining parameter bounds.
      rw [run.multiplier_zero, run.point_zero]
      calc
        ‖multiplier₀ + (params.rho : ℝ) • c x₀‖ ≤
            ‖multiplier₀‖ + ‖(params.rho : ℝ) • c x₀‖ := norm_add_le _ _
        _ = ‖multiplier₀‖ + params.rho * ‖c x₀‖ := by
          rw [norm_smul, Real.norm_eq_abs]
          have hρ : 0 < (params.rho : ℝ) := params.spec.1.2.2.1
          rw [abs_of_pos hρ]
        _ ≤ 3 * params.multiplierBound := by
          have hboundNonneg : (0 : ℝ) ≤ params.multiplierBound := by positivity
          linarith [params.norm_multiplier₀_le, params.initialResidual_le]
  | succ k =>
      -- The update rewrites the effective multiplier as `2 λ_(k+1) - λ_k`.
      have hupdate :
          run.multiplier (k + 1) ω = run.multiplier k ω +
            (params.rho : ℝ) • c (run.point (k + 1) ω) :=
        run.multiplier_succ k ω
      have heffective :
          run.multiplier (k + 1) ω +
              (params.rho : ℝ) • c (run.point (k + 1) ω) =
            (2 : ℝ) • run.multiplier (k + 1) ω - run.multiplier k ω := by
        rw [hupdate]
        simp only [two_smul]
        abel
      rw [heffective]
      calc
        ‖(2 : ℝ) • run.multiplier (k + 1) ω - run.multiplier k ω‖ ≤
            ‖(2 : ℝ) • run.multiplier (k + 1) ω‖ +
              ‖run.multiplier k ω‖ := norm_sub_le _ _
        _ = 2 * ‖run.multiplier (k + 1) ω‖ + ‖run.multiplier k ω‖ := by
          rw [norm_smul, Real.norm_ofNat]
        _ ≤ 3 * params.multiplierBound := by
          have hnext := hMultiplier (k + 1) (Nat.le_refl _)
          have hprevious := hMultiplier k (Nat.le_succ k)
          have hboundNonneg : (0 : ℝ) ≤ params.multiplierBound := by positivity
          linarith

/-- Helper for Lemma 3.4: regularity, clipping, and an effective-multiplier
bound control one stochastic primal step. -/
lemma normStep_le_of_normEffectiveMultiplier_le
    (run : StochasticRun h oracle ℙ x₀ multiplier₀ params Q B b)
    (k : ℕ) (ω : Ω) (hx : run.point k ω ∈ h.region)
    (heffective :
      ‖run.multiplier k ω + (params.rho : ℝ) • c (run.point k ω)‖ ≤
        3 * params.multiplierBound) :
    ‖run.step k ω‖ ≤ params.delta := by
  -- Rearrange stochastic model optimality into the damped normal equation.
  have hoptimal := stepModelWithGradientOptimality c
    (SPIDER.estimate h.gradientBound oracle run.point run.sample Q B b k ω)
    params.rho params.beta (run.point k ω) (run.multiplier k ω)
    (run.step k ω) (run.minimizes_step k ω)
  rw [← run.gradientEstimate_apply] at hoptimal
  have hequation :
      (params.beta : ℝ) • run.step k ω +
          (params.rho : ℝ) • (fderiv ℝ c (run.point k ω)).adjoint
            (fderiv ℝ c (run.point k ω) (run.step k ω)) =
        -run.gradientEstimate k ω -
          (fderiv ℝ c (run.point k ω)).adjoint
            (run.multiplier k ω + (params.rho : ℝ) • c (run.point k ω)) := by
    simp only [EqualityConstrained.constraintGradient_def, map_add, map_smul] at hoptimal ⊢
    linear_combination (norm := module) hoptimal
  have hβ : 0 < (params.beta : ℝ) := params.spec.1.2.1
  have hρ : 0 ≤ (params.rho : ℝ) := params.spec.1.2.2.1.le
  have hestimate := normDampedNormalEquation_le
    (fderiv ℝ c (run.point k ω)) hβ hρ h.licqModulus_pos
    (h.licqLowerBound (run.point k ω) hx) (run.step k ω)
    (run.gradientEstimate k ω)
    (run.multiplier k ω + params.rho • c (run.point k ω)) hequation
  -- Clipping supplies the objective-gradient bound required by the parameter choice.
  have hgradient : ‖run.gradientEstimate k ω‖ ≤ h.gradientBound := by
    rw [run.gradientEstimate_apply, SPIDER.estimate_apply]
    exact SPIDER.norm_clip_le h.gradientBound _
  have hoperator :
      ‖ContinuousLinearMap.adjoint (fderiv ℝ c (run.point k ω))‖ ≤
        h.constraintGradientBound := by
    simpa only [EqualityConstrained.constraintGradient_def] using
      h.norm_constraintGradient_le (run.point k ω) hx
  have hdenom :
      0 < (params.beta : ℝ) + params.rho * (h.licqModulus : ℝ) ^ 2 := by
    exact add_pos_of_pos_of_nonneg hβ
      (mul_nonneg hρ (sq_nonneg (h.licqModulus : ℝ)))
  have hgradientTerm :
      ‖run.gradientEstimate k ω‖ / params.beta ≤ h.gradientBound / params.beta :=
    (div_le_div_iff_of_pos_right hβ).2 hgradient
  have hproduct :
      ‖ContinuousLinearMap.adjoint (fderiv ℝ c (run.point k ω))‖ *
          ‖run.multiplier k ω + params.rho • c (run.point k ω)‖ ≤
        h.constraintGradientBound * (3 * params.multiplierBound) :=
    mul_le_mul hoperator heffective (norm_nonneg _)
      (NNReal.coe_nonneg h.constraintGradientBound)
  have hconstraintTerm :
      ‖ContinuousLinearMap.adjoint (fderiv ℝ c (run.point k ω))‖ *
          ‖run.multiplier k ω + params.rho • c (run.point k ω)‖ /
            (params.beta + params.rho * (h.licqModulus : ℝ) ^ 2) ≤
        3 * h.constraintGradientBound * params.multiplierBound /
            (params.beta + params.rho * (h.licqModulus : ℝ) ^ 2) := by
    rw [div_le_div_iff_of_pos_right hdenom]
    nlinarith
  calc
    ‖run.step k ω‖ ≤
        ‖run.gradientEstimate k ω‖ / params.beta +
          ‖ContinuousLinearMap.adjoint (fderiv ℝ c (run.point k ω))‖ *
            ‖run.multiplier k ω + params.rho • c (run.point k ω)‖ /
              (params.beta + params.rho * (h.licqModulus : ℝ) ^ 2) := hestimate
    _ ≤ h.gradientBound / params.beta +
        3 * h.constraintGradientBound * params.multiplierBound /
          (params.beta + params.rho * (h.licqModulus : ℝ) ^ 2) :=
      add_le_add hgradientTerm hconstraintTerm
    _ ≤ params.delta := params.comparisonBound_le

/-- Helper for Lemma 3.4: an admissible bounded stochastic step propagates the
pathwise multiplier bound through one iteration. -/
lemma normMultiplier_succ_le_of_normStep_le
    (run : StochasticRun h oracle ℙ x₀ multiplier₀ params Q B b)
    (k : ℕ) (ω : Ω)
    (hsegment : segment ℝ (run.point k ω) (run.point (k + 1) ω) ⊆ h.region)
    (hstep : ‖run.step k ω‖ ≤ params.delta) :
    ‖run.multiplier (k + 1) ω‖ ≤ params.multiplierBound := by
  -- LICQ converts the perturbed multiplier identity into a scalar norm estimate.
  have hx : run.point k ω ∈ h.region := hsegment (left_mem_segment ℝ _ _)
  have hidentity :
      EqualityConstrained.constraintGradient c (run.point k ω)
          (run.multiplier (k + 1) ω) =
        -run.gradientEstimate k ω - (params.beta : ℝ) • run.step k ω +
          (params.rho : ℝ) • EqualityConstrained.constraintGradient c (run.point k ω)
            (linearizationError run k ω) := by
    linear_combination (norm := module) perturbedMultiplierIdentity run k ω
  have hstepSq : ‖run.step k ω‖ ^ 2 ≤ (params.delta : ℝ) ^ 2 :=
    (sq_le_sq₀ (norm_nonneg _) (NNReal.coe_nonneg _)).2 hstep
  have herror := normLinearizationError_le run k ω hsegment
  have herrorBound :
      ‖linearizationError run k ω‖ ≤
        linearizationConstant h * (params.delta : ℝ) ^ 2 :=
    herror.trans (mul_le_mul_of_nonneg_left hstepSq (NNReal.coe_nonneg _))
  have hgradient : ‖run.gradientEstimate k ω‖ ≤ h.gradientBound := by
    rw [run.gradientEstimate_apply, SPIDER.estimate_apply]
    exact SPIDER.norm_clip_le h.gradientBound _
  have hoperator := h.norm_constraintGradient_le (run.point k ω) hx
  have hρ : 0 < (params.rho : ℝ) := params.spec.1.2.2.1
  have hβ : 0 < (params.beta : ℝ) := params.spec.1.2.1
  have hperturbation :
      ‖(params.rho : ℝ) • EqualityConstrained.constraintGradient c (run.point k ω)
          (linearizationError run k ω)‖ ≤
        params.rho * h.constraintGradientBound * linearizationConstant h *
          (params.delta : ℝ) ^ 2 := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hρ]
    calc
      params.rho * ‖EqualityConstrained.constraintGradient c (run.point k ω)
          (linearizationError run k ω)‖ ≤
          params.rho *
            (‖EqualityConstrained.constraintGradient c (run.point k ω)‖ *
              ‖linearizationError run k ω‖) :=
        mul_le_mul_of_nonneg_left
          ((EqualityConstrained.constraintGradient c (run.point k ω)).le_opNorm
            (linearizationError run k ω)) hρ.le
      _ ≤ params.rho *
          (h.constraintGradientBound *
            (linearizationConstant h * (params.delta : ℝ) ^ 2)) := by
        gcongr
      _ = params.rho * h.constraintGradientBound * linearizationConstant h *
          (params.delta : ℝ) ^ 2 := by ring
  have hnormalBound :
      ‖EqualityConstrained.constraintGradient c (run.point k ω)
          (run.multiplier (k + 1) ω)‖ ≤
        h.gradientBound + params.beta * params.delta +
          params.rho * h.constraintGradientBound * linearizationConstant h *
            (params.delta : ℝ) ^ 2 := by
    rw [hidentity]
    calc
      ‖-run.gradientEstimate k ω - params.beta • run.step k ω +
          (params.rho : ℝ) • EqualityConstrained.constraintGradient c (run.point k ω)
            (linearizationError run k ω)‖ ≤
          ‖-run.gradientEstimate k ω - params.beta • run.step k ω‖ +
            ‖(params.rho : ℝ) • EqualityConstrained.constraintGradient c
              (run.point k ω) (linearizationError run k ω)‖ := norm_add_le _ _
      _ ≤ (‖run.gradientEstimate k ω‖ + params.beta * ‖run.step k ω‖) +
          ‖(params.rho : ℝ) • EqualityConstrained.constraintGradient c
            (run.point k ω) (linearizationError run k ω)‖ := by
        gcongr
        calc
          ‖-run.gradientEstimate k ω - (params.beta : ℝ) • run.step k ω‖ ≤
              ‖-run.gradientEstimate k ω‖ +
                ‖(params.beta : ℝ) • run.step k ω‖ := norm_sub_le _ _
          _ = ‖run.gradientEstimate k ω‖ + params.beta * ‖run.step k ω‖ := by
            rw [norm_neg, norm_smul, Real.norm_eq_abs, abs_of_pos hβ]
      _ ≤ h.gradientBound + params.beta * params.delta +
          params.rho * h.constraintGradientBound * linearizationConstant h *
            (params.delta : ℝ) ^ 2 := by
        nlinarith [mul_le_mul_of_nonneg_left hstep hβ.le]
  have hlicq := h.licqLowerBound (run.point k ω) hx (run.multiplier (k + 1) ω)
  have hscaled :
      (h.licqModulus : ℝ) * ‖run.multiplier (k + 1) ω‖ ≤
        h.gradientBound + params.beta * params.delta +
          params.rho * h.constraintGradientBound * linearizationConstant h *
            (params.delta : ℝ) ^ 2 := hlicq.trans hnormalBound
  have hquotient :
      ‖run.multiplier (k + 1) ω‖ ≤
        (h.gradientBound + params.beta * params.delta +
          params.rho * h.constraintGradientBound * linearizationConstant h *
            (params.delta : ℝ) ^ 2) / h.licqModulus := by
    rw [le_div_iff₀ (NNReal.coe_pos.2 h.licqModulus_pos)]
    simpa only [mul_comm] using hscaled
  exact hquotient.trans params.parameterBound_le

/-- Helper for Lemma 3.4: stochastic prefix admissibility propagates pathwise
step and multiplier bounds simultaneously. -/
private lemma admissiblePrefixNormBounds
    (run : StochasticRun h oracle ℙ x₀ multiplier₀ params Q B b)
    (N : ℕ) (h_admissible : run.IsAdmissiblePrefix N) :
    (∀ k < N, ∀ ω, ‖run.step k ω‖ ≤ params.delta) ∧
      (∀ k ≤ N, ∀ ω, ‖run.multiplier k ω‖ ≤ params.multiplierBound) := by
  -- Induct on completed iterations while carrying both mutually supporting bounds.
  induction N with
  | zero =>
      constructor
      · intro k hk
        omega
      · intro k hk ω
        have hkzero : k = 0 := by omega
        subst k
        rw [run.multiplier_zero]
        exact params.norm_multiplier₀_le
  | succ N ih =>
      have hsegments := (run.isAdmissiblePrefix_iff (N + 1)).1 h_admissible
      have hprefix : run.IsAdmissiblePrefix N :=
        (run.isAdmissiblePrefix_iff N).2 fun j hj ω ↦
          hsegments j (Nat.lt_succ_of_lt hj) ω
      have hbounds := ih hprefix
      have hnewStep (ω : Ω) : ‖run.step N ω‖ ≤ params.delta := by
        have hsegment := hsegments N (Nat.lt_succ_self N) ω
        have hx : run.point N ω ∈ h.region :=
          hsegment (left_mem_segment ℝ _ _)
        have heffective := normEffectiveMultiplier_le run N ω
          (fun j hj ↦ hbounds.2 j hj ω)
        exact normStep_le_of_normEffectiveMultiplier_le run N ω hx heffective
      have hnewMultiplier (ω : Ω) :
          ‖run.multiplier (N + 1) ω‖ ≤ params.multiplierBound := by
        exact normMultiplier_succ_le_of_normStep_le run N ω
          (hsegments N (Nat.lt_succ_self N) ω) (hnewStep ω)
      constructor
      · intro k hk ω
        by_cases hkold : k < N
        · exact hbounds.1 k hkold ω
        · have hkeq : k = N := by omega
          simpa only [hkeq] using hnewStep ω
      · intro k hk ω
        by_cases hkold : k ≤ N
        · exact hbounds.2 k hkold ω
        · have hkeq : k = N + 1 := by omega
          simpa only [hkeq] using hnewMultiplier ω

/-- Helper for Lemma 3.4: the squared primal step at every index of an
admissible finite prefix is integrable. -/
theorem integrableStepSquare
    (run : StochasticRun h oracle ℙ x₀ multiplier₀ params Q B b)
    {K k : ℕ} (h_admissible : run.IsAdmissiblePrefix K) (hk : k < K) :
    Integrable (fun ω ↦ ‖run.step k ω‖ ^ 2) ℙ := by
  have hsquareMeasurable :
      AEStronglyMeasurable (fun ω ↦ ‖run.step k ω‖ ^ 2) ℙ :=
    ((run.aemeasurable_step k).norm.pow_const 2).aestronglyMeasurable
  have hbound (ω : Ω) :
      ‖(‖run.step k ω‖ ^ 2 : ℝ)‖ ≤ (params.delta : ℝ) ^ 2 := by
    have hstep := (admissiblePrefixNormBounds run K h_admissible).1 k hk ω
    have hsquare :=
      (sq_le_sq₀ (norm_nonneg _) (NNReal.coe_nonneg params.delta)).2 hstep
    simpa only [Real.norm_of_nonneg (sq_nonneg _)] using hsquare
  exact Integrable.mono' (integrable_const _) hsquareMeasurable
    (ae_of_all ℙ hbound)

/-- Helper for Lemma 3.4: subtracting two stochastic perturbed-multiplier
identities exposes the multiplier increment and both gradient errors. -/
private lemma constraintGradientMultiplierIncrement
    (run : StochasticRun h oracle ℙ x₀ multiplier₀ params Q B b)
    (k : ℕ) (hk_pos : 1 ≤ k) (ω : Ω) :
    EqualityConstrained.constraintGradient c (run.point k ω)
        (run.multiplier (k + 1) ω - run.multiplier k ω) =
      (-(params.beta : ℝ) • run.step k ω +
          (params.rho : ℝ) • EqualityConstrained.constraintGradient c (run.point k ω)
            (linearizationError run k ω)) +
        ((params.beta : ℝ) • run.step (k - 1) ω -
          (params.rho : ℝ) • EqualityConstrained.constraintGradient c
            (run.point (k - 1) ω) (linearizationError run (k - 1) ω)) +
        (gradient f (run.point (k - 1) ω) - gradient f (run.point k ω)) +
        (EqualityConstrained.constraintGradient c (run.point (k - 1) ω) -
          EqualityConstrained.constraintGradient c (run.point k ω))
            (run.multiplier k ω) +
        (run.gradientError (k - 1) ω - run.gradientError k ω) := by
  -- Normalize the predecessor successor and expand each estimator error once.
  have hpred : k - 1 + 1 = k := Nat.sub_add_cancel hk_pos
  have hcurrent := perturbedMultiplierIdentity run k ω
  have hprevious := perturbedMultiplierIdentity run (k - 1) ω
  rw [hpred] at hprevious
  rw [run.gradientError_apply, run.gradientError_apply]
  simp only [map_sub, sub_apply]
  linear_combination (norm := module) hcurrent - hprevious

/-- Helper for Lemma 3.4: on an admissible stochastic segment, a bounded step
controls the penalty-scaled constraint-gradient image of its Taylor error. -/
private lemma normScaledConstraintGradientError_le
    (run : StochasticRun h oracle ℙ x₀ multiplier₀ params Q B b)
    (j : ℕ) (ω : Ω)
    (hsegment : segment ℝ (run.point j ω) (run.point (j + 1) ω) ⊆ h.region)
    (hstep : ‖run.step j ω‖ ≤ params.delta) :
    ‖(params.rho : ℝ) • EqualityConstrained.constraintGradient c (run.point j ω)
        (linearizationError run j ω)‖ ≤
      params.rho * h.constraintGradientBound * linearizationConstant h * params.delta *
        ‖run.step j ω‖ := by
  -- Pass from the operator norm to the quadratic Taylor bound, then linearize it.
  have hx : run.point j ω ∈ h.region := hsegment (left_mem_segment ℝ _ _)
  have hoperator := h.norm_constraintGradient_le (run.point j ω) hx
  have herror := normLinearizationError_le run j ω hsegment
  have happlication :
      ‖EqualityConstrained.constraintGradient c (run.point j ω)
          (linearizationError run j ω)‖ ≤
        h.constraintGradientBound * ‖linearizationError run j ω‖ :=
    (EqualityConstrained.constraintGradient c (run.point j ω)).le_opNorm
      (linearizationError run j ω) |>.trans
        (mul_le_mul_of_nonneg_right hoperator (norm_nonneg _))
  have hlinearized :
      ‖EqualityConstrained.constraintGradient c (run.point j ω)
          (linearizationError run j ω)‖ ≤
        h.constraintGradientBound *
          (linearizationConstant h * ‖run.step j ω‖ ^ 2) :=
    happlication.trans
      (mul_le_mul_of_nonneg_left herror (NNReal.coe_nonneg h.constraintGradientBound))
  have hstepProduct :
      ‖run.step j ω‖ * ‖run.step j ω‖ ≤ params.delta * ‖run.step j ω‖ :=
    mul_le_mul_of_nonneg_right hstep (norm_nonneg _)
  have hcoefficientNonneg :
      0 ≤ (params.rho : ℝ) * h.constraintGradientBound * linearizationConstant h := by
    positivity
  have hρ : 0 < (params.rho : ℝ) := params.spec.1.2.2.1
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos hρ]
  calc
    params.rho * ‖EqualityConstrained.constraintGradient c (run.point j ω)
        (linearizationError run j ω)‖ ≤
        params.rho *
          (h.constraintGradientBound *
            (linearizationConstant h * ‖run.step j ω‖ ^ 2)) :=
      mul_le_mul_of_nonneg_left hlinearized hρ.le
    _ = (params.rho * h.constraintGradientBound * linearizationConstant h) *
        (‖run.step j ω‖ * ‖run.step j ω‖) := by ring
    _ ≤ (params.rho * h.constraintGradientBound * linearizationConstant h) *
        (params.delta * ‖run.step j ω‖) :=
      mul_le_mul_of_nonneg_left hstepProduct hcoefficientNonneg
    _ = params.rho * h.constraintGradientBound * linearizationConstant h * params.delta *
        ‖run.step j ω‖ := by ring

/-- Helper for Lemma 3.4: the constraint-gradient image of a stochastic
multiplier increment is controlled by two steps and two gradient errors. -/
private lemma normConstraintGradientMultiplierIncrement_le
    (run : StochasticRun h oracle ℙ x₀ multiplier₀ params Q B b)
    {N k : ℕ} (h_admissible : run.IsAdmissiblePrefix N)
    (hk_pos : 1 ≤ k) (hk : k < N) (ω : Ω) :
    ‖EqualityConstrained.constraintGradient c (run.point k ω)
        (run.multiplier (k + 1) ω - run.multiplier k ω)‖ ≤
      primalConstant h params.delta params.beta params.rho * ‖run.step k ω‖ +
        primalComparisonConstant h params.delta params.beta params.rho
          params.multiplierBound * ‖run.step (k - 1) ω‖ +
        ‖run.gradientError k ω‖ + ‖run.gradientError (k - 1) ω‖ := by
  -- Extract both admissible segments and the uniform pathwise bounds.
  have hpred : k - 1 + 1 = k := Nat.sub_add_cancel hk_pos
  have hk_previous : k - 1 < N := by omega
  have hsegments := (run.isAdmissiblePrefix_iff N).1 h_admissible
  have hsegmentCurrent := hsegments k hk ω
  have hsegmentPrevious := hsegments (k - 1) hk_previous ω
  have hxCurrent : run.point k ω ∈ h.region :=
    hsegmentCurrent (left_mem_segment ℝ _ _)
  have hxPrevious : run.point (k - 1) ω ∈ h.region :=
    hsegmentPrevious (left_mem_segment ℝ _ _)
  have hbounds := admissiblePrefixNormBounds run N h_admissible
  have hstepCurrent := hbounds.1 k hk ω
  have hstepPrevious := hbounds.1 (k - 1) hk_previous ω
  have hk_le : k ≤ N := by omega
  have hmultiplier := hbounds.2 k hk_le ω
  have herrorCurrent :=
    normScaledConstraintGradientError_le run k ω hsegmentCurrent hstepCurrent
  have herrorPrevious :=
    normScaledConstraintGradientError_le run (k - 1) ω hsegmentPrevious hstepPrevious
  -- The point update identifies every regularity distance with the relevant step norm.
  have hpointDistance :
      dist (run.point (k - 1) ω) (run.point k ω) = ‖run.step (k - 1) ω‖ := by
    calc
      dist (run.point (k - 1) ω) (run.point k ω) =
          dist (run.point (k - 1) ω) (run.point (k - 1 + 1) ω) := by rw [hpred]
      _ = ‖run.step (k - 1) ω‖ := by
        rw [run.point_succ, dist_eq_norm, norm_sub_rev, add_sub_cancel_left]
  have hgradientDifference :
      ‖gradient f (run.point (k - 1) ω) - gradient f (run.point k ω)‖ ≤
        h.gradientLipschitz * ‖run.step (k - 1) ω‖ := by
    calc
      ‖gradient f (run.point (k - 1) ω) - gradient f (run.point k ω)‖ =
          dist (gradient f (run.point (k - 1) ω))
            (gradient f (run.point k ω)) := (dist_eq_norm _ _).symm
      _ ≤ h.gradientLipschitz * dist (run.point (k - 1) ω) (run.point k ω) :=
        h.lipschitzOn_gradient.dist_le_mul
          (run.point (k - 1) ω) hxPrevious (run.point k ω) hxCurrent
      _ = h.gradientLipschitz * ‖run.step (k - 1) ω‖ := by rw [hpointDistance]
  have hoperatorDifference :
      ‖EqualityConstrained.constraintGradient c (run.point (k - 1) ω) -
          EqualityConstrained.constraintGradient c (run.point k ω)‖ ≤
        h.constraintGradientLipschitz * ‖run.step (k - 1) ω‖ := by
    calc
      ‖EqualityConstrained.constraintGradient c (run.point (k - 1) ω) -
          EqualityConstrained.constraintGradient c (run.point k ω)‖ =
          dist (EqualityConstrained.constraintGradient c (run.point (k - 1) ω))
            (EqualityConstrained.constraintGradient c (run.point k ω)) :=
        (dist_eq_norm _ _).symm
      _ ≤ h.constraintGradientLipschitz *
          dist (run.point (k - 1) ω) (run.point k ω) :=
        h.lipschitzOn_constraintGradient.dist_le_mul
          (run.point (k - 1) ω) hxPrevious (run.point k ω) hxCurrent
      _ = h.constraintGradientLipschitz * ‖run.step (k - 1) ω‖ := by
        rw [hpointDistance]
  have hoperatorApplied :
      ‖(EqualityConstrained.constraintGradient c (run.point (k - 1) ω) -
          EqualityConstrained.constraintGradient c (run.point k ω))
            (run.multiplier k ω)‖ ≤
        h.constraintGradientLipschitz * params.multiplierBound *
          ‖run.step (k - 1) ω‖ := by
    calc
      ‖(EqualityConstrained.constraintGradient c (run.point (k - 1) ω) -
          EqualityConstrained.constraintGradient c (run.point k ω))
            (run.multiplier k ω)‖ ≤
          ‖EqualityConstrained.constraintGradient c (run.point (k - 1) ω) -
            EqualityConstrained.constraintGradient c (run.point k ω)‖ *
              ‖run.multiplier k ω‖ :=
        (EqualityConstrained.constraintGradient c (run.point (k - 1) ω) -
          EqualityConstrained.constraintGradient c (run.point k ω)).le_opNorm
            (run.multiplier k ω)
      _ ≤ (h.constraintGradientLipschitz * ‖run.step (k - 1) ω‖) *
          params.multiplierBound :=
        mul_le_mul hoperatorDifference hmultiplier (norm_nonneg _)
          (mul_nonneg (NNReal.coe_nonneg _) (norm_nonneg _))
      _ = h.constraintGradientLipschitz * params.multiplierBound *
          ‖run.step (k - 1) ω‖ := by ring
  have hβ : 0 < (params.beta : ℝ) := params.spec.1.2.1
  -- Combine each proximal/Taylor pair into the named primal coefficient.
  have hcurrentPair :
      ‖-(params.beta : ℝ) • run.step k ω +
          (params.rho : ℝ) • EqualityConstrained.constraintGradient c (run.point k ω)
            (linearizationError run k ω)‖ ≤
        primalConstant h params.delta params.beta params.rho * ‖run.step k ω‖ := by
    calc
      ‖-(params.beta : ℝ) • run.step k ω +
          (params.rho : ℝ) • EqualityConstrained.constraintGradient c (run.point k ω)
            (linearizationError run k ω)‖ ≤
          ‖-(params.beta : ℝ) • run.step k ω‖ +
            ‖(params.rho : ℝ) • EqualityConstrained.constraintGradient c
              (run.point k ω) (linearizationError run k ω)‖ := norm_add_le _ _
      _ = params.beta * ‖run.step k ω‖ +
          ‖(params.rho : ℝ) • EqualityConstrained.constraintGradient c
            (run.point k ω) (linearizationError run k ω)‖ := by
        rw [norm_smul, Real.norm_eq_abs, abs_neg, abs_of_pos hβ]
      _ ≤ params.beta * ‖run.step k ω‖ +
          params.rho * h.constraintGradientBound * linearizationConstant h * params.delta *
            ‖run.step k ω‖ := add_le_add_right herrorCurrent _
      _ = primalConstant h params.delta params.beta params.rho * ‖run.step k ω‖ := by
        rw [primalConstant_def]
        ring
  have hpreviousPair :
      ‖(params.beta : ℝ) • run.step (k - 1) ω -
          (params.rho : ℝ) • EqualityConstrained.constraintGradient c
            (run.point (k - 1) ω) (linearizationError run (k - 1) ω)‖ ≤
        primalConstant h params.delta params.beta params.rho *
          ‖run.step (k - 1) ω‖ := by
    calc
      ‖(params.beta : ℝ) • run.step (k - 1) ω -
          (params.rho : ℝ) • EqualityConstrained.constraintGradient c
            (run.point (k - 1) ω) (linearizationError run (k - 1) ω)‖ ≤
          ‖(params.beta : ℝ) • run.step (k - 1) ω‖ +
            ‖(params.rho : ℝ) • EqualityConstrained.constraintGradient c
              (run.point (k - 1) ω) (linearizationError run (k - 1) ω)‖ :=
        norm_sub_le _ _
      _ = params.beta * ‖run.step (k - 1) ω‖ +
          ‖(params.rho : ℝ) • EqualityConstrained.constraintGradient c
            (run.point (k - 1) ω) (linearizationError run (k - 1) ω)‖ := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos hβ]
      _ ≤ params.beta * ‖run.step (k - 1) ω‖ +
          params.rho * h.constraintGradientBound * linearizationConstant h * params.delta *
            ‖run.step (k - 1) ω‖ := add_le_add_right herrorPrevious _
      _ = primalConstant h params.delta params.beta params.rho *
          ‖run.step (k - 1) ω‖ := by
        rw [primalConstant_def]
        ring
  have hdeterministicCore :
      ‖(-(params.beta : ℝ) • run.step k ω +
          (params.rho : ℝ) • EqualityConstrained.constraintGradient c (run.point k ω)
            (linearizationError run k ω)) +
        ((params.beta : ℝ) • run.step (k - 1) ω -
          (params.rho : ℝ) • EqualityConstrained.constraintGradient c
            (run.point (k - 1) ω) (linearizationError run (k - 1) ω)) +
        (gradient f (run.point (k - 1) ω) - gradient f (run.point k ω)) +
        (EqualityConstrained.constraintGradient c (run.point (k - 1) ω) -
          EqualityConstrained.constraintGradient c (run.point k ω))
            (run.multiplier k ω)‖ ≤
        primalConstant h params.delta params.beta params.rho * ‖run.step k ω‖ +
          primalComparisonConstant h params.delta params.beta params.rho
            params.multiplierBound * ‖run.step (k - 1) ω‖ := by
    calc
      ‖(-(params.beta : ℝ) • run.step k ω +
            (params.rho : ℝ) • EqualityConstrained.constraintGradient c (run.point k ω)
              (linearizationError run k ω)) +
          ((params.beta : ℝ) • run.step (k - 1) ω -
            (params.rho : ℝ) • EqualityConstrained.constraintGradient c
              (run.point (k - 1) ω) (linearizationError run (k - 1) ω)) +
          (gradient f (run.point (k - 1) ω) - gradient f (run.point k ω)) +
          (EqualityConstrained.constraintGradient c (run.point (k - 1) ω) -
            EqualityConstrained.constraintGradient c (run.point k ω))
              (run.multiplier k ω)‖ ≤
          ‖-(params.beta : ℝ) • run.step k ω +
            (params.rho : ℝ) • EqualityConstrained.constraintGradient c (run.point k ω)
              (linearizationError run k ω)‖ +
          ‖(params.beta : ℝ) • run.step (k - 1) ω -
            (params.rho : ℝ) • EqualityConstrained.constraintGradient c
              (run.point (k - 1) ω) (linearizationError run (k - 1) ω)‖ +
          ‖gradient f (run.point (k - 1) ω) - gradient f (run.point k ω)‖ +
          ‖(EqualityConstrained.constraintGradient c (run.point (k - 1) ω) -
            EqualityConstrained.constraintGradient c (run.point k ω))
              (run.multiplier k ω)‖ := by
        have hfirst := norm_add_le
          (-(params.beta : ℝ) • run.step k ω +
            (params.rho : ℝ) • EqualityConstrained.constraintGradient c
              (run.point k ω) (linearizationError run k ω))
          ((params.beta : ℝ) • run.step (k - 1) ω -
            (params.rho : ℝ) • EqualityConstrained.constraintGradient c
              (run.point (k - 1) ω) (linearizationError run (k - 1) ω))
        have hsecond := norm_add_le
          ((-(params.beta : ℝ) • run.step k ω +
              (params.rho : ℝ) • EqualityConstrained.constraintGradient c
                (run.point k ω) (linearizationError run k ω)) +
            ((params.beta : ℝ) • run.step (k - 1) ω -
              (params.rho : ℝ) • EqualityConstrained.constraintGradient c
                (run.point (k - 1) ω) (linearizationError run (k - 1) ω)))
          (gradient f (run.point (k - 1) ω) - gradient f (run.point k ω))
        have hthird := norm_add_le
          (((-(params.beta : ℝ) • run.step k ω +
                (params.rho : ℝ) • EqualityConstrained.constraintGradient c
                  (run.point k ω) (linearizationError run k ω)) +
              ((params.beta : ℝ) • run.step (k - 1) ω -
                (params.rho : ℝ) • EqualityConstrained.constraintGradient c
                  (run.point (k - 1) ω) (linearizationError run (k - 1) ω))) +
            (gradient f (run.point (k - 1) ω) - gradient f (run.point k ω)))
          ((EqualityConstrained.constraintGradient c (run.point (k - 1) ω) -
            EqualityConstrained.constraintGradient c (run.point k ω))
              (run.multiplier k ω))
        linarith
      _ ≤ primalConstant h params.delta params.beta params.rho * ‖run.step k ω‖ +
          primalConstant h params.delta params.beta params.rho *
            ‖run.step (k - 1) ω‖ +
          h.gradientLipschitz * ‖run.step (k - 1) ω‖ +
          h.constraintGradientLipschitz * params.multiplierBound *
            ‖run.step (k - 1) ω‖ :=
        add_le_add (add_le_add (add_le_add hcurrentPair hpreviousPair)
          hgradientDifference) hoperatorApplied
      _ = primalConstant h params.delta params.beta params.rho * ‖run.step k ω‖ +
          primalComparisonConstant h params.delta params.beta params.rho
            params.multiplierBound * ‖run.step (k - 1) ω‖ := by
        rw [primalComparisonConstant_def]
        ring
  -- Add the remaining estimator-error difference after the deterministic core.
  rw [constraintGradientMultiplierIncrement run k hk_pos ω]
  calc
    ‖((-(params.beta : ℝ) • run.step k ω +
          (params.rho : ℝ) • EqualityConstrained.constraintGradient c (run.point k ω)
            (linearizationError run k ω)) +
        ((params.beta : ℝ) • run.step (k - 1) ω -
          (params.rho : ℝ) • EqualityConstrained.constraintGradient c
            (run.point (k - 1) ω) (linearizationError run (k - 1) ω)) +
        (gradient f (run.point (k - 1) ω) - gradient f (run.point k ω)) +
        (EqualityConstrained.constraintGradient c (run.point (k - 1) ω) -
          EqualityConstrained.constraintGradient c (run.point k ω))
            (run.multiplier k ω)) +
        (run.gradientError (k - 1) ω - run.gradientError k ω)‖ ≤
        ‖(-(params.beta : ℝ) • run.step k ω +
            (params.rho : ℝ) • EqualityConstrained.constraintGradient c (run.point k ω)
              (linearizationError run k ω)) +
          ((params.beta : ℝ) • run.step (k - 1) ω -
            (params.rho : ℝ) • EqualityConstrained.constraintGradient c
              (run.point (k - 1) ω) (linearizationError run (k - 1) ω)) +
          (gradient f (run.point (k - 1) ω) - gradient f (run.point k ω)) +
          (EqualityConstrained.constraintGradient c (run.point (k - 1) ω) -
            EqualityConstrained.constraintGradient c (run.point k ω))
              (run.multiplier k ω)‖ +
        ‖run.gradientError (k - 1) ω - run.gradientError k ω‖ := norm_add_le _ _
    _ ≤ (primalConstant h params.delta params.beta params.rho * ‖run.step k ω‖ +
          primalComparisonConstant h params.delta params.beta params.rho
            params.multiplierBound * ‖run.step (k - 1) ω‖) +
        (‖run.gradientError (k - 1) ω‖ + ‖run.gradientError k ω‖) :=
      add_le_add hdeterministicCore (norm_sub_le _ _)
    _ = primalConstant h params.delta params.beta params.rho * ‖run.step k ω‖ +
        primalComparisonConstant h params.delta params.beta params.rho
          params.multiplierBound * ‖run.step (k - 1) ω‖ +
        ‖run.gradientError k ω‖ + ‖run.gradientError (k - 1) ω‖ := by ring

/-- Helper for Lemma 3.4: the squared stochastic multiplier increment is
controlled by two step squares and two gradient-error squares. -/
private lemma normMultiplierIncrementSq_le
    (run : StochasticRun h oracle ℙ x₀ multiplier₀ params Q B b)
    {N k : ℕ} (h_admissible : run.IsAdmissiblePrefix N)
    (hk_pos : 1 ≤ k) (hk : k < N) (ω : Ω) :
    ‖run.multiplier (k + 1) ω - run.multiplier k ω‖ ^ 2 ≤
      multiplierPrimalConstant h params.delta params.beta params.rho
          params.multiplierBound *
        (‖run.step k ω‖ ^ 2 + ‖run.step (k - 1) ω‖ ^ 2) +
      multiplierErrorConstant h *
        (‖run.gradientError k ω‖ ^ 2 +
          ‖run.gradientError (k - 1) ω‖ ^ 2) := by
  -- LICQ lifts the comparison estimate from the constraint-gradient image.
  have hsegments := (run.isAdmissiblePrefix_iff N).1 h_admissible
  have hsegment := hsegments k hk ω
  have hx : run.point k ω ∈ h.region := hsegment (left_mem_segment ℝ _ _)
  have hcomparison :=
    normConstraintGradientMultiplierIncrement_le run h_admissible hk_pos hk ω
  have hlicq := h.licqLowerBound (run.point k ω) hx
    (run.multiplier (k + 1) ω - run.multiplier k ω)
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
  have hrightNonneg :
      0 ≤ primalConstant h params.delta params.beta params.rho * ‖run.step k ω‖ +
        primalComparisonConstant h params.delta params.beta params.rho
          params.multiplierBound * ‖run.step (k - 1) ω‖ +
        ‖run.gradientError k ω‖ + ‖run.gradientError (k - 1) ω‖ := by
    positivity
  have hleftNonneg :
      0 ≤ (h.licqModulus : ℝ) *
        ‖run.multiplier (k + 1) ω - run.multiplier k ω‖ := by positivity
  have hscaledSquare :
      ((h.licqModulus : ℝ) *
          ‖run.multiplier (k + 1) ω - run.multiplier k ω‖) ^ 2 ≤
        (primalConstant h params.delta params.beta params.rho * ‖run.step k ω‖ +
          primalComparisonConstant h params.delta params.beta params.rho
            params.multiplierBound * ‖run.step (k - 1) ω‖ +
          ‖run.gradientError k ω‖ + ‖run.gradientError (k - 1) ω‖) ^ 2 :=
    (sq_le_sq₀ hleftNonneg hrightNonneg).2 hscaled
  -- Apply the four-term square inequality and dominate both primal coefficients by a maximum.
  let a := primalConstant h params.delta params.beta params.rho * ‖run.step k ω‖
  let b := primalComparisonConstant h params.delta params.beta params.rho
    params.multiplierBound * ‖run.step (k - 1) ω‖
  let e₀ := ‖run.gradientError k ω‖
  let e₁ := ‖run.gradientError (k - 1) ω‖
  have hab : (a + b) ^ 2 ≤ 2 * (a ^ 2 + b ^ 2) := by
    nlinarith [sq_nonneg (a - b)]
  have he : (e₀ + e₁) ^ 2 ≤ 2 * (e₀ ^ 2 + e₁ ^ 2) := by
    nlinarith [sq_nonneg (e₀ - e₁)]
  have htwo : (0 : ℝ) ≤ 2 := by norm_num
  have hfourNonneg : (0 : ℝ) ≤ 4 := by norm_num
  have hfour :
      (a + b + e₀ + e₁) ^ 2 ≤
        4 * (a ^ 2 + b ^ 2 + e₀ ^ 2 + e₁ ^ 2) := by
    calc
      (a + b + e₀ + e₁) ^ 2 = ((a + b) + (e₀ + e₁)) ^ 2 := by ring
      _ ≤ 2 * ((a + b) ^ 2 + (e₀ + e₁) ^ 2) := by
        nlinarith [sq_nonneg ((a + b) - (e₀ + e₁))]
      _ ≤ 2 * (2 * (a ^ 2 + b ^ 2) + 2 * (e₀ ^ 2 + e₁ ^ 2)) :=
        mul_le_mul_of_nonneg_left (add_le_add hab he) htwo
      _ = 4 * (a ^ 2 + b ^ 2 + e₀ ^ 2 + e₁ ^ 2) := by ring
  have hprimalMax :
      primalConstant h params.delta params.beta params.rho ^ 2 ≤
        max (primalConstant h params.delta params.beta params.rho ^ 2)
          (primalComparisonConstant h params.delta params.beta params.rho
            params.multiplierBound ^ 2) := le_max_left _ _
  have hcomparisonMax :
      primalComparisonConstant h params.delta params.beta params.rho
          params.multiplierBound ^ 2 ≤
        max (primalConstant h params.delta params.beta params.rho ^ 2)
          (primalComparisonConstant h params.delta params.beta params.rho
            params.multiplierBound ^ 2) := le_max_right _ _
  have haSquare :
      a ^ 2 ≤
        max (primalConstant h params.delta params.beta params.rho ^ 2)
          (primalComparisonConstant h params.delta params.beta params.rho
            params.multiplierBound ^ 2) * ‖run.step k ω‖ ^ 2 := by
    dsimp only [a]
    rw [mul_pow]
    exact mul_le_mul_of_nonneg_right hprimalMax (sq_nonneg _)
  have hbSquare :
      b ^ 2 ≤
        max (primalConstant h params.delta params.beta params.rho ^ 2)
          (primalComparisonConstant h params.delta params.beta params.rho
            params.multiplierBound ^ 2) * ‖run.step (k - 1) ω‖ ^ 2 := by
    dsimp only [b]
    rw [mul_pow]
    exact mul_le_mul_of_nonneg_right hcomparisonMax (sq_nonneg _)
  have hsquares :
      a ^ 2 + b ^ 2 + e₀ ^ 2 + e₁ ^ 2 ≤
        max (primalConstant h params.delta params.beta params.rho ^ 2)
            (primalComparisonConstant h params.delta params.beta params.rho
              params.multiplierBound ^ 2) *
          (‖run.step k ω‖ ^ 2 + ‖run.step (k - 1) ω‖ ^ 2) +
        (‖run.gradientError k ω‖ ^ 2 +
          ‖run.gradientError (k - 1) ω‖ ^ 2) := by
    dsimp only [e₀, e₁]
    calc
      a ^ 2 + b ^ 2 + ‖run.gradientError k ω‖ ^ 2 +
          ‖run.gradientError (k - 1) ω‖ ^ 2 ≤
          (max (primalConstant h params.delta params.beta params.rho ^ 2)
              (primalComparisonConstant h params.delta params.beta params.rho
                params.multiplierBound ^ 2) * ‖run.step k ω‖ ^ 2 +
            max (primalConstant h params.delta params.beta params.rho ^ 2)
              (primalComparisonConstant h params.delta params.beta params.rho
                params.multiplierBound ^ 2) * ‖run.step (k - 1) ω‖ ^ 2) +
            ‖run.gradientError k ω‖ ^ 2 +
              ‖run.gradientError (k - 1) ω‖ ^ 2 := by
        exact add_le_add
          (add_le_add (add_le_add haSquare hbSquare) (le_refl _)) (le_refl _)
      _ = max (primalConstant h params.delta params.beta params.rho ^ 2)
            (primalComparisonConstant h params.delta params.beta params.rho
              params.multiplierBound ^ 2) *
          (‖run.step k ω‖ ^ 2 + ‖run.step (k - 1) ω‖ ^ 2) +
        (‖run.gradientError k ω‖ ^ 2 +
          ‖run.gradientError (k - 1) ω‖ ^ 2) := by ring
  have hscaledExpanded :
      (h.licqModulus : ℝ) ^ 2 *
          ‖run.multiplier (k + 1) ω - run.multiplier k ω‖ ^ 2 ≤
        4 *
          (max (primalConstant h params.delta params.beta params.rho ^ 2)
              (primalComparisonConstant h params.delta params.beta params.rho
                params.multiplierBound ^ 2) *
            (‖run.step k ω‖ ^ 2 + ‖run.step (k - 1) ω‖ ^ 2) +
          (‖run.gradientError k ω‖ ^ 2 +
            ‖run.gradientError (k - 1) ω‖ ^ 2)) := by
    calc
      (h.licqModulus : ℝ) ^ 2 *
          ‖run.multiplier (k + 1) ω - run.multiplier k ω‖ ^ 2 =
          ((h.licqModulus : ℝ) *
            ‖run.multiplier (k + 1) ω - run.multiplier k ω‖) ^ 2 := by ring
      _ ≤ (a + b + e₀ + e₁) ^ 2 := by
        simpa only [a, b, e₀, e₁] using hscaledSquare
      _ ≤ 4 * (a ^ 2 + b ^ 2 + e₀ ^ 2 + e₁ ^ 2) := hfour
      _ ≤ 4 *
          (max (primalConstant h params.delta params.beta params.rho ^ 2)
              (primalComparisonConstant h params.delta params.beta params.rho
                params.multiplierBound ^ 2) *
            (‖run.step k ω‖ ^ 2 + ‖run.step (k - 1) ω‖ ^ 2) +
          (‖run.gradientError k ω‖ ^ 2 +
            ‖run.gradientError (k - 1) ω‖ ^ 2)) :=
        mul_le_mul_of_nonneg_left hsquares hfourNonneg
  -- Divide by the positive LICQ modulus and unfold the two named coefficients.
  have hσsq : 0 < (h.licqModulus : ℝ) ^ 2 := sq_pos_of_pos h.licqModulus_pos
  have hscaledCommuted :
      ‖run.multiplier (k + 1) ω - run.multiplier k ω‖ ^ 2 *
          (h.licqModulus : ℝ) ^ 2 ≤
        4 *
          (max (primalConstant h params.delta params.beta params.rho ^ 2)
              (primalComparisonConstant h params.delta params.beta params.rho
                params.multiplierBound ^ 2) *
            (‖run.step k ω‖ ^ 2 + ‖run.step (k - 1) ω‖ ^ 2) +
          (‖run.gradientError k ω‖ ^ 2 +
            ‖run.gradientError (k - 1) ω‖ ^ 2)) := by
    simpa only [mul_comm] using hscaledExpanded
  calc
    ‖run.multiplier (k + 1) ω - run.multiplier k ω‖ ^ 2 ≤
        (4 *
          (max (primalConstant h params.delta params.beta params.rho ^ 2)
              (primalComparisonConstant h params.delta params.beta params.rho
                params.multiplierBound ^ 2) *
            (‖run.step k ω‖ ^ 2 + ‖run.step (k - 1) ω‖ ^ 2) +
          (‖run.gradientError k ω‖ ^ 2 +
            ‖run.gradientError (k - 1) ω‖ ^ 2))) /
          (h.licqModulus : ℝ) ^ 2 :=
      (le_div_iff₀ hσsq).2 hscaledCommuted
    _ = multiplierPrimalConstant h params.delta params.beta params.rho
          params.multiplierBound *
        (‖run.step k ω‖ ^ 2 + ‖run.step (k - 1) ω‖ ^ 2) +
      multiplierErrorConstant h *
        (‖run.gradientError k ω‖ ^ 2 +
          ‖run.gradientError (k - 1) ω‖ ^ 2) := by
      rw [multiplierPrimalConstant_def, multiplierErrorConstant_def]
      ring

/-- Helper for Lemma 3.4: a segment in the regularity region gives the
quadratic upper Taylor estimate for the objective. -/
private lemma objectiveChange_le
    (h : EqualityConstrained.Regularity f c)
    (x y : EuclideanSpace ℝ (Fin n))
    (hsegment : segment ℝ x y ⊆ h.region) :
    f y - f x ≤
      ⟪gradient f x, y - x⟫_ℝ +
        (h.gradientLipschitz : ℝ) / 2 * ‖y - x‖ ^ 2 := by
  have hremainder := norm_sub_sub_fderiv_le f h.gradientLipschitz h.region x y
    (fun _ hz ↦ h.differentiableAt_objective hz) h.lipschitzOn_objectiveFDeriv hsegment
  have hsigned :
      f y - f x - fderiv ℝ f x (y - x) ≤
        ‖f y - f x - fderiv ℝ f x (y - x)‖ := by
    simpa only [Real.norm_eq_abs] using
      (le_abs_self (f y - f x - fderiv ℝ f x (y - x)))
  rw [← inner_gradient_left] at hremainder hsigned
  linarith

/-- Helper for Lemma 3.4: stochastic model optimality gives the exact change
of the linearized augmented-Lagrangian terms. -/
private lemma linearizedAugmentedLagrangianChange_eq
    (run : StochasticRun h oracle ℙ x₀ multiplier₀ params Q B b)
    (k : ℕ) (ω : Ω) :
    ⟪run.gradientEstimate k ω, run.step k ω⟫_ℝ +
          ⟪run.multiplier k ω,
            fderiv ℝ c (run.point k ω) (run.step k ω)⟫_ℝ +
        (params.rho / 2) *
          (‖c (run.point k ω) +
              fderiv ℝ c (run.point k ω) (run.step k ω)‖ ^ 2 -
            ‖c (run.point k ω)‖ ^ 2) =
      -params.beta * ‖run.step k ω‖ ^ 2 -
        (params.rho / 2) *
          ‖fderiv ℝ c (run.point k ω) (run.step k ω)‖ ^ 2 := by
  have hminimizes := run.minimizes_step k ω
  rw [← run.gradientEstimate_apply] at hminimizes
  have hfirstOrder := stepModelWithGradientOptimality c
    (run.gradientEstimate k ω) params.rho params.beta
    (run.point k ω) (run.multiplier k ω) (run.step k ω) hminimizes
  have hoptimal := congrArg (fun v ↦ ⟪v, run.step k ω⟫_ℝ) hfirstOrder
  simp only [inner_add_left, inner_smul_left, starRingEnd_apply, star_trivial,
    ContinuousLinearMap.adjoint_inner_left, real_inner_self_eq_norm_sq,
    inner_zero_left] at hoptimal
  rw [norm_add_sq_real]
  nlinarith

/-- Helper for Lemma 3.4: the true constraint value is its linearized value
plus the stochastic linearization error. -/
private lemma constraintValue_eq_linearization_add_error
    (run : StochasticRun h oracle ℙ x₀ multiplier₀ params Q B b)
    (k : ℕ) (ω : Ω) :
    c (run.point (k + 1) ω) =
      c (run.point k ω) + fderiv ℝ c (run.point k ω) (run.step k ω) +
        linearizationError run k ω := by
  rw [linearizationError]
  module

/-- Helper for Lemma 3.4: one stochastic augmented-Lagrangian difference
splits into its linearized part and two Taylor remainders. -/
private lemma augmentedLagrangianChange_eq_linearized
    (run : StochasticRun h oracle ℙ x₀ multiplier₀ params Q B b)
    (k : ℕ) (ω : Ω) :
    ℒ[f, c; params.rho](run.point (k + 1) ω, run.multiplier k ω) -
        ℒ[f, c; params.rho](run.point k ω, run.multiplier k ω) =
      (f (run.point (k + 1) ω) - f (run.point k ω)) +
        ⟪run.multiplier k ω,
          fderiv ℝ c (run.point k ω) (run.step k ω)⟫_ℝ +
        (params.rho / 2) *
          (‖c (run.point k ω) +
              fderiv ℝ c (run.point k ω) (run.step k ω)‖ ^ 2 -
            ‖c (run.point k ω)‖ ^ 2) +
        ⟪run.multiplier k ω + (params.rho : ℝ) •
            (c (run.point k ω) +
              fderiv ℝ c (run.point k ω) (run.step k ω)),
          linearizationError run k ω⟫_ℝ +
        (params.rho / 2) * ‖linearizationError run k ω‖ ^ 2 := by
  rw [augmentedLagrangian_def, augmentedLagrangian_def,
    constraintValue_eq_linearization_add_error run k ω, norm_add_sq_real]
  simp only [inner_add_right, inner_add_left, inner_smul_left,
    starRingEnd_apply, star_trivial]
  ring

/-- Helper for Lemma 3.4: the stochastic constraint linearization error
contributes at most the constraint part of the model constant. -/
private lemma constraintRemainderContribution_le
    (run : StochasticRun h oracle ℙ x₀ multiplier₀ params Q B b)
    (k : ℕ) (ω : Ω)
    (hsegment : segment ℝ (run.point k ω) (run.point (k + 1) ω) ⊆ h.region)
    (hstep : ‖run.step k ω‖ ≤ params.delta)
    (heffective :
      ‖run.multiplier k ω + (params.rho : ℝ) • c (run.point k ω)‖ ≤
        3 * (params.multiplierBound : ℝ)) :
    ⟪run.multiplier k ω + (params.rho : ℝ) •
          (c (run.point k ω) +
            fderiv ℝ c (run.point k ω) (run.step k ω)),
        linearizationError run k ω⟫_ℝ +
        (params.rho / 2) * ‖linearizationError run k ω‖ ^ 2 ≤
      (linearizationConstant h *
          (3 * params.multiplierBound +
            params.rho * h.constraintGradientBound * params.delta) +
        (params.rho / 2) * linearizationConstant h ^ 2 * params.delta ^ 2) *
          ‖run.step k ω‖ ^ 2 := by
  have hx : run.point k ω ∈ h.region :=
    hsegment (left_mem_segment ℝ _ _)
  have hderivativeNorm :
      ‖fderiv ℝ c (run.point k ω)‖ ≤ h.constraintGradientBound := by
    rw [← LinearIsometryEquiv.norm_map ContinuousLinearMap.adjoint]
    exact h.norm_constraintGradient_le (run.point k ω) hx
  have hlinearizedStep :
      ‖fderiv ℝ c (run.point k ω) (run.step k ω)‖ ≤
        h.constraintGradientBound * ‖run.step k ω‖ := by
    calc
      ‖fderiv ℝ c (run.point k ω) (run.step k ω)‖ ≤
          ‖fderiv ℝ c (run.point k ω)‖ * ‖run.step k ω‖ :=
        (fderiv ℝ c (run.point k ω)).le_opNorm (run.step k ω)
      _ ≤ h.constraintGradientBound * ‖run.step k ω‖ :=
        mul_le_mul_of_nonneg_right hderivativeNorm (norm_nonneg _)
  have heffectiveLinearized :
      ‖run.multiplier k ω + (params.rho : ℝ) •
          (c (run.point k ω) +
            fderiv ℝ c (run.point k ω) (run.step k ω))‖ ≤
        3 * params.multiplierBound +
          params.rho * h.constraintGradientBound * params.delta := by
    have hdecomposition :
        run.multiplier k ω + (params.rho : ℝ) •
            (c (run.point k ω) +
              fderiv ℝ c (run.point k ω) (run.step k ω)) =
          (run.multiplier k ω + (params.rho : ℝ) • c (run.point k ω)) +
            (params.rho : ℝ) •
              fderiv ℝ c (run.point k ω) (run.step k ω) := by
      module
    rw [hdecomposition]
    have hρ : 0 < (params.rho : ℝ) := params.spec.1.2.2.1
    calc
      ‖(run.multiplier k ω + (params.rho : ℝ) • c (run.point k ω)) +
          (params.rho : ℝ) •
            fderiv ℝ c (run.point k ω) (run.step k ω)‖ ≤
          ‖run.multiplier k ω + (params.rho : ℝ) • c (run.point k ω)‖ +
            ‖(params.rho : ℝ) •
              fderiv ℝ c (run.point k ω) (run.step k ω)‖ := norm_add_le _ _
      _ ≤ 3 * params.multiplierBound +
          params.rho * (h.constraintGradientBound * ‖run.step k ω‖) := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos hρ]
        exact add_le_add heffective
          (mul_le_mul_of_nonneg_left hlinearizedStep hρ.le)
      _ ≤ 3 * params.multiplierBound +
          params.rho * h.constraintGradientBound * params.delta := by
        have hcoefficient :
            (0 : ℝ) ≤ params.rho * h.constraintGradientBound := by positivity
        nlinarith [mul_le_mul_of_nonneg_left hstep hcoefficient]
  have herror := normLinearizationError_le run k ω hsegment
  have hlinearizedBoundNonneg :
      (0 : ℝ) ≤ 3 * params.multiplierBound +
        params.rho * h.constraintGradientBound * params.delta :=
    (norm_nonneg _).trans heffectiveLinearized
  have hinnerContribution :
      ⟪run.multiplier k ω + (params.rho : ℝ) •
            (c (run.point k ω) +
              fderiv ℝ c (run.point k ω) (run.step k ω)),
          linearizationError run k ω⟫_ℝ ≤
        linearizationConstant h *
          (3 * params.multiplierBound +
            params.rho * h.constraintGradientBound * params.delta) *
              ‖run.step k ω‖ ^ 2 := by
    calc
      ⟪run.multiplier k ω + (params.rho : ℝ) •
            (c (run.point k ω) +
              fderiv ℝ c (run.point k ω) (run.step k ω)),
          linearizationError run k ω⟫_ℝ ≤
          ‖run.multiplier k ω + (params.rho : ℝ) •
            (c (run.point k ω) +
              fderiv ℝ c (run.point k ω) (run.step k ω))‖ *
              ‖linearizationError run k ω‖ := real_inner_le_norm _ _
      _ ≤ (3 * params.multiplierBound +
            params.rho * h.constraintGradientBound * params.delta) *
          (linearizationConstant h * ‖run.step k ω‖ ^ 2) :=
        mul_le_mul heffectiveLinearized herror (norm_nonneg _) hlinearizedBoundNonneg
      _ = linearizationConstant h *
          (3 * params.multiplierBound +
            params.rho * h.constraintGradientBound * params.delta) *
              ‖run.step k ω‖ ^ 2 := by ring
  have hdeltaNonneg : (0 : ℝ) ≤ params.delta := by positivity
  have hstepSq :
      ‖run.step k ω‖ ^ 2 ≤ (params.delta : ℝ) ^ 2 :=
    (sq_le_sq₀ (norm_nonneg _) hdeltaNonneg).2 hstep
  have herrorSq :
      ‖linearizationError run k ω‖ ^ 2 ≤
        linearizationConstant h ^ 2 * params.delta ^ 2 *
          ‖run.step k ω‖ ^ 2 := by
    have herrorBoundNonneg :
        (0 : ℝ) ≤ linearizationConstant h * ‖run.step k ω‖ ^ 2 := by
      positivity
    have hsquaredError :
        ‖linearizationError run k ω‖ ^ 2 ≤
          (linearizationConstant h * ‖run.step k ω‖ ^ 2) ^ 2 :=
      (sq_le_sq₀ (norm_nonneg _) herrorBoundNonneg).2 herror
    calc
      ‖linearizationError run k ω‖ ^ 2 ≤
          (linearizationConstant h * ‖run.step k ω‖ ^ 2) ^ 2 := hsquaredError
      _ = linearizationConstant h ^ 2 *
          ‖run.step k ω‖ ^ 2 * ‖run.step k ω‖ ^ 2 := by ring
      _ ≤ linearizationConstant h ^ 2 *
          (params.delta : ℝ) ^ 2 * ‖run.step k ω‖ ^ 2 := by
        gcongr
      _ = linearizationConstant h ^ 2 * params.delta ^ 2 *
          ‖run.step k ω‖ ^ 2 := by ring
  have hpenaltyContribution :
      (params.rho / 2) * ‖linearizationError run k ω‖ ^ 2 ≤
        (params.rho / 2) * linearizationConstant h ^ 2 * params.delta ^ 2 *
          ‖run.step k ω‖ ^ 2 := by
    have hrhoHalf : (0 : ℝ) ≤ (params.rho : ℝ) / 2 := by positivity
    calc
      (params.rho / 2) * ‖linearizationError run k ω‖ ^ 2 ≤
          (params.rho / 2) *
            (linearizationConstant h ^ 2 * params.delta ^ 2 *
              ‖run.step k ω‖ ^ 2) :=
        mul_le_mul_of_nonneg_left herrorSq hrhoHalf
      _ = (params.rho / 2) * linearizationConstant h ^ 2 * params.delta ^ 2 *
          ‖run.step k ω‖ ^ 2 := by ring
  nlinarith

/-- Helper for Lemma 3.4: the stochastic augmented-Lagrangian change is
bounded by its linearized change plus the model remainder. -/
private lemma augmentedLagrangianChange_le_modelConstant
    (run : StochasticRun h oracle ℙ x₀ multiplier₀ params Q B b)
    (k : ℕ) (ω : Ω)
    (hsegment : segment ℝ (run.point k ω) (run.point (k + 1) ω) ⊆ h.region)
    (hstep : ‖run.step k ω‖ ≤ params.delta)
    (heffective :
      ‖run.multiplier k ω + (params.rho : ℝ) • c (run.point k ω)‖ ≤
        3 * (params.multiplierBound : ℝ)) :
    ℒ[f, c; params.rho](run.point (k + 1) ω, run.multiplier k ω) -
        ℒ[f, c; params.rho](run.point k ω, run.multiplier k ω) ≤
      (⟪gradient f (run.point k ω), run.step k ω⟫_ℝ +
          ⟪run.multiplier k ω,
            fderiv ℝ c (run.point k ω) (run.step k ω)⟫_ℝ +
        (params.rho / 2) *
          (‖c (run.point k ω) +
              fderiv ℝ c (run.point k ω) (run.step k ω)‖ ^ 2 -
            ‖c (run.point k ω)‖ ^ 2)) +
        modelConstant h params.delta params.rho params.multiplierBound *
          ‖run.step k ω‖ ^ 2 := by
  have hobjective :
      f (run.point (k + 1) ω) - f (run.point k ω) ≤
        ⟪gradient f (run.point k ω), run.step k ω⟫_ℝ +
          (h.gradientLipschitz : ℝ) / 2 * ‖run.step k ω‖ ^ 2 := by
    have htaylor := objectiveChange_le h (run.point k ω) (run.point (k + 1) ω)
      hsegment
    rw [run.point_succ, add_sub_cancel_left] at htaylor
    rw [run.point_succ]
    exact htaylor
  have hconstraint :=
    constraintRemainderContribution_le run k ω hsegment hstep heffective
  rw [augmentedLagrangianChange_eq_linearized run k ω, modelConstant_def]
  nlinarith

/-- Lemma 3.4 (1): on an admissible stochastic prefix, one step decreases the
augmented Lagrangian up to the current projected-gradient error. -/
theorem augmentedLagrangianDescent
    {N k : ℕ} (h_admissible : run.IsAdmissiblePrefix N) (hk : k < N)
    (ω : Ω) :
    ℒ[f, c; params.rho](run.point (k + 1) ω, run.multiplier k ω) ≤
      ℒ[f, c; params.rho](run.point k ω, run.multiplier k ω) -
        (params.beta / 2) * ‖run.step k ω‖ ^ 2 +
          (2 / params.beta) * ‖run.gradientError k ω‖ ^ 2 := by
  have hsegment := (run.isAdmissiblePrefix_iff N).1 h_admissible k hk ω
  have hnormBounds := admissiblePrefixNormBounds run N h_admissible
  have hstep := hnormBounds.1 k hk ω
  have hMultiplier :
      ∀ j ≤ k, ‖run.multiplier j ω‖ ≤ params.multiplierBound := by
    intro j hj
    exact hnormBounds.2 j (le_trans hj (Nat.le_of_lt hk)) ω
  have heffective := normEffectiveMultiplier_le run k ω hMultiplier
  have hchange := augmentedLagrangianChange_le_modelConstant
    run k ω hsegment hstep heffective
  have hlinearized := linearizedAugmentedLagrangianChange_eq run k ω
  have hgradientIdentity :
      gradient f (run.point k ω) =
        run.gradientEstimate k ω - run.gradientError k ω := by
    rw [run.gradientError_apply]
    module
  have hbeta : 0 < (params.beta : ℝ) := params.spec.1.2.1
  have hquarterBeta : 0 < (params.beta : ℝ) / 4 := by positivity
  have hinverseQuarterBeta :
      ((params.beta : ℝ) / 4)⁻¹ = 4 / params.beta := by
    field_simp [hbeta.ne']
  have htwoProduct := two_mul_le_add_mul_sq
    (a := ‖run.step k ω‖) (b := ‖run.gradientError k ω‖) hquarterBeta
  rw [hinverseQuarterBeta] at htwoProduct
  have htwoNonneg : (0 : ℝ) ≤ 2 := by norm_num
  have hyoung :
      ‖run.step k ω‖ * ‖run.gradientError k ω‖ ≤
        (params.beta / 8) * ‖run.step k ω‖ ^ 2 +
          (2 / params.beta) * ‖run.gradientError k ω‖ ^ 2 := by
    calc
      ‖run.step k ω‖ * ‖run.gradientError k ω‖ =
          (2 * ‖run.step k ω‖ * ‖run.gradientError k ω‖) / 2 := by ring
      _ ≤ ((params.beta / 4) * ‖run.step k ω‖ ^ 2 +
          (4 / params.beta) * ‖run.gradientError k ω‖ ^ 2) / 2 :=
        div_le_div_of_nonneg_right htwoProduct htwoNonneg
      _ = (params.beta / 8) * ‖run.step k ω‖ ^ 2 +
          (2 / params.beta) * ‖run.gradientError k ω‖ ^ 2 := by ring
  have hinnerNorm := real_inner_le_norm
    (-run.gradientError k ω) (run.step k ω)
  simp only [inner_neg_left, norm_neg] at hinnerNorm
  have hyoungCommuted :
      ‖run.gradientError k ω‖ * ‖run.step k ω‖ ≤
        (params.beta / 8) * ‖run.step k ω‖ ^ 2 +
          (2 / params.beta) * ‖run.gradientError k ω‖ ^ 2 := by
    simpa only [mul_comm] using hyoung
  have hinner :
      -⟪run.gradientError k ω, run.step k ω⟫_ℝ ≤
        (params.beta / 8) * ‖run.step k ω‖ ^ 2 +
          (2 / params.beta) * ‖run.gradientError k ω‖ ^ 2 := by
    exact hinnerNorm.trans hyoungCommuted
  have hmodelTerm :
      modelConstant h params.delta params.rho params.multiplierBound *
          ‖run.step k ω‖ ^ 2 ≤
        (3 * (params.beta : ℝ) / 8) * ‖run.step k ω‖ ^ 2 :=
    mul_le_mul_of_nonneg_right params.modelConstant_le (sq_nonneg _)
  have hpenaltyNonneg :
      (0 : ℝ) ≤ (params.rho / 2) *
        ‖fderiv ℝ c (run.point k ω) (run.step k ω)‖ ^ 2 := by
    positivity
  rw [hgradientIdentity, inner_sub_left] at hchange
  have hchangeFinal :
      ℒ[f, c; params.rho](run.point (k + 1) ω, run.multiplier k ω) -
          ℒ[f, c; params.rho](run.point k ω, run.multiplier k ω) ≤
        -(params.beta / 2) * ‖run.step k ω‖ ^ 2 +
          (2 / params.beta) * ‖run.gradientError k ω‖ ^ 2 := by
    nlinarith
  linarith

/-- Lemma 3.4 (2): the squared multiplier increment is controlled by the
current and preceding primal steps and projected-gradient errors. -/
theorem norm_multiplier_succ_sub_sq_le
    {N k : ℕ} (h_admissible : run.IsAdmissiblePrefix N)
    (hk_pos : 1 ≤ k) (hk : k < N) (ω : Ω) :
    ‖run.multiplier (k + 1) ω - run.multiplier k ω‖ ^ 2 ≤
      multiplierPrimalConstant h params.delta params.beta params.rho
          params.multiplierBound *
        (‖run.step k ω‖ ^ 2 + ‖run.step (k - 1) ω‖ ^ 2) +
      LALM.multiplierErrorConstant h *
        (‖run.gradientError k ω‖ ^ 2 + ‖run.gradientError (k - 1) ω‖ ^ 2) := by
  exact normMultiplierIncrementSq_le run h_admissible hk_pos hk ω

/-- Helper for Lemma 3.4: a multiplier update increases the augmented
Lagrangian by the squared multiplier increment divided by the penalty. -/
private lemma augmentedLagrangianMultiplierSucc_eq
    (run : StochasticRun h oracle ℙ x₀ multiplier₀ params Q B b)
    (k : ℕ) (ω : Ω) :
    ℒ[f, c; params.rho](run.point (k + 1) ω, run.multiplier (k + 1) ω) =
      ℒ[f, c; params.rho](run.point (k + 1) ω, run.multiplier k ω) +
        ‖run.multiplier (k + 1) ω - run.multiplier k ω‖ ^ 2 / params.rho := by
  have hρ : 0 < (params.rho : ℝ) := params.spec.1.2.2.1
  have hupdate :
      run.multiplier (k + 1) ω = run.multiplier k ω +
        (params.rho : ℝ) • c (run.point (k + 1) ω) :=
    run.multiplier_succ k ω
  rw [augmentedLagrangian_def, augmentedLagrangian_def, hupdate,
    inner_add_left, inner_smul_left, add_sub_cancel_left, norm_smul,
    Real.norm_eq_abs, abs_of_pos hρ, real_inner_self_eq_norm_sq,
    starRingEnd_apply, star_trivial]
  field_simp [hρ.ne']
  ring

/-- Helper for Lemma 3.4: the admissible parameter inequality bounds the
multiplier-primal coefficient after division by the penalty. -/
private lemma multiplierPrimalConstant_div_rho_le_beta_div_eight
    (h : EqualityConstrained.Regularity f c)
    (params : Parameters h x₀ multiplier₀) :
    multiplierPrimalConstant h params.delta params.beta params.rho
          params.multiplierBound / params.rho ≤
      params.beta / 8 := by
  have hscaled :
      8 * multiplierPrimalConstant h params.delta params.beta params.rho
          params.multiplierBound ≤ params.rho * params.beta :=
    (div_le_iff₀ params.toAdmissibleParameters.spec.1.2.1).1
      params.multiplierPrimalConstant_le
  apply (div_le_iff₀ params.toAdmissibleParameters.spec.1.2.2.1).2
  nlinarith

/-- Lemma 3.4 (3): the pathwise stochastic Lyapunov value decreases by a
quarter-step term up to two consecutive projected-gradient errors. -/
theorem lyapunovDescent
    {N k : ℕ} (h_admissible : run.IsAdmissiblePrefix N)
    (hk_pos : 1 ≤ k) (hk : k < N) (ω : Ω) :
    run.lyapunov (k + 1) ω ≤
      run.lyapunov k ω - (params.beta / 4) * ‖run.step k ω‖ ^ 2 +
        lyapunovErrorConstant h params *
          (‖run.gradientError k ω‖ ^ 2 + ‖run.gradientError (k - 1) ω‖ ^ 2) := by
  have hlagrangian := run.augmentedLagrangianDescent h_admissible hk ω
  have hmultiplier :=
    run.norm_multiplier_succ_sub_sq_le h_admissible hk_pos hk ω
  have hρ : 0 < (params.rho : ℝ) := params.spec.1.2.2.1
  have hmultiplierDivided :=
    (div_le_div_iff_of_pos_right hρ).2 hmultiplier
  have hmultiplierDiv :
      ‖run.multiplier (k + 1) ω - run.multiplier k ω‖ ^ 2 / params.rho ≤
        (multiplierPrimalConstant h params.delta params.beta params.rho
            params.multiplierBound / params.rho) *
          (‖run.step k ω‖ ^ 2 + ‖run.step (k - 1) ω‖ ^ 2) +
        (multiplierErrorConstant h / params.rho) *
          (‖run.gradientError k ω‖ ^ 2 +
            ‖run.gradientError (k - 1) ω‖ ^ 2) := by
    calc
      ‖run.multiplier (k + 1) ω - run.multiplier k ω‖ ^ 2 / params.rho ≤
          (multiplierPrimalConstant h params.delta params.beta params.rho
              params.multiplierBound *
                (‖run.step k ω‖ ^ 2 + ‖run.step (k - 1) ω‖ ^ 2) +
            multiplierErrorConstant h *
              (‖run.gradientError k ω‖ ^ 2 +
                ‖run.gradientError (k - 1) ω‖ ^ 2)) / params.rho :=
        hmultiplierDivided
      _ = (multiplierPrimalConstant h params.delta params.beta params.rho
              params.multiplierBound / params.rho) *
            (‖run.step k ω‖ ^ 2 + ‖run.step (k - 1) ω‖ ^ 2) +
          (multiplierErrorConstant h / params.rho) *
            (‖run.gradientError k ω‖ ^ 2 +
              ‖run.gradientError (k - 1) ω‖ ^ 2) := by ring
  have hcoefficient := multiplierPrimalConstant_div_rho_le_beta_div_eight h params
  have hcurrent :
      2 * (multiplierPrimalConstant h params.delta params.beta params.rho
          params.multiplierBound / params.rho) * ‖run.step k ω‖ ^ 2 ≤
        (params.beta / 4) * ‖run.step k ω‖ ^ 2 := by
    have htwiceCoefficient :
        2 * (multiplierPrimalConstant h params.delta params.beta params.rho
          params.multiplierBound / params.rho) ≤ params.beta / 4 := by
      linarith
    exact mul_le_mul_of_nonneg_right htwiceCoefficient (sq_nonneg _)
  have herrorPreviousNonneg :
      (0 : ℝ) ≤ (2 / params.beta) * ‖run.gradientError (k - 1) ω‖ ^ 2 := by
    positivity
  rw [run.lyapunov_def, run.lyapunov_def,
    augmentedLagrangianMultiplierSucc_eq run, Nat.add_sub_cancel,
    lyapunovErrorConstant_def]
  nlinarith

/-- Helper for Lemma 3.4: a bounded multiplier gives the standard uniform
lower bound for the augmented Lagrangian on the regularity region. -/
private lemma augmentedLagrangianLowerBound_of_norm_multiplier_le
    (h : EqualityConstrained.Regularity f c) (rho : ℝ)
    (x : EuclideanSpace ℝ (Fin n))
    (multiplier : EuclideanSpace ℝ (Fin m)) (bound : ℝ)
    (hrho : 0 < rho) (hx : x ∈ h.region)
    (hmultiplier : ‖multiplier‖ ≤ bound) (hbound : 0 ≤ bound) :
    h.objectiveLower - bound ^ 2 / (2 * rho) ≤
      ℒ[f, c; rho](x, multiplier) := by
  have hinner : -(‖multiplier‖ * ‖c x‖) ≤ ⟪multiplier, c x⟫_ℝ :=
    neg_le_of_abs_le (abs_real_inner_le_norm multiplier (c x))
  have hyoung :
      2 * ‖c x‖ * ‖multiplier‖ ≤
        rho * ‖c x‖ ^ 2 + rho⁻¹ * ‖multiplier‖ ^ 2 :=
    two_mul_le_add_mul_sq hrho
  have htwoNonneg : (0 : ℝ) ≤ 2 := by norm_num
  have hyoungDivided := div_le_div_of_nonneg_right hyoung htwoNonneg
  have hyoungHalf :
      ‖multiplier‖ * ‖c x‖ ≤
        rho / 2 * ‖c x‖ ^ 2 + ‖multiplier‖ ^ 2 / (2 * rho) := by
    calc
      ‖multiplier‖ * ‖c x‖ = (2 * ‖c x‖ * ‖multiplier‖) / 2 := by ring
      _ ≤ (rho * ‖c x‖ ^ 2 + rho⁻¹ * ‖multiplier‖ ^ 2) / 2 :=
        hyoungDivided
      _ = rho / 2 * ‖c x‖ ^ 2 + ‖multiplier‖ ^ 2 / (2 * rho) := by
        field_simp [hrho.ne']
  have hmultiplierSq : ‖multiplier‖ ^ 2 ≤ bound ^ 2 :=
    (sq_le_sq₀ (norm_nonneg multiplier) hbound).2 hmultiplier
  have htwoRhoPos : 0 < 2 * rho := by positivity
  have hdiv :
      ‖multiplier‖ ^ 2 / (2 * rho) ≤ bound ^ 2 / (2 * rho) :=
    (div_le_div_iff_of_pos_right htwoRhoPos).2 hmultiplierSq
  rw [augmentedLagrangian_def]
  have hobjective := h.objectiveLower_le x hx
  linarith

/-- Helper for Lemma 3.4: every positive-index stochastic Lyapunov value in
an admissible prefix is at least the uniform lower bound. -/
private lemma lyapunovLowerBound_le
    (run : StochasticRun h oracle ℙ x₀ multiplier₀ params Q B b)
    {N k : ℕ} (h_admissible : run.IsAdmissiblePrefix N)
    (hk_pos : 1 ≤ k) (hk : k ≤ N) (ω : Ω) :
    LALM.lyapunovLowerBound h params ≤ run.lyapunov k ω := by
  have hkPrevious : k - 1 < N := by omega
  have hsegment :=
    (run.isAdmissiblePrefix_iff N).1 h_admissible (k - 1) hkPrevious ω
  have hx : run.point k ω ∈ h.region := by
    simpa only [Nat.sub_add_cancel hk_pos] using
      hsegment (right_mem_segment ℝ
        (run.point (k - 1) ω) (run.point ((k - 1) + 1) ω))
  have hnormBounds := admissiblePrefixNormBounds run N h_admissible
  have hmultiplier := hnormBounds.2 k hk ω
  have hρ : 0 < (params.rho : ℝ) := params.spec.1.2.2.1
  have hboundNonneg : (0 : ℝ) ≤ params.multiplierBound := by positivity
  have hlower := augmentedLagrangianLowerBound_of_norm_multiplier_le h params.rho
    (run.point k ω) (run.multiplier k ω) params.multiplierBound hρ hx
    hmultiplier hboundNonneg
  have hconstantNonneg :
      0 ≤ multiplierPrimalConstant h params.delta params.beta params.rho
        params.multiplierBound := by
    rw [multiplierPrimalConstant_def]
    positivity
  have hcorrectionNonneg :
      0 ≤ (multiplierPrimalConstant h params.delta params.beta params.rho
          params.multiplierBound / params.rho) * ‖run.step (k - 1) ω‖ ^ 2 :=
    mul_nonneg (div_nonneg hconstantNonneg hρ.le) (sq_nonneg _)
  rw [LALM.lyapunovLowerBound_def, run.lyapunov_def]
  linarith

/-- Helper for Lemma 3.4: the first stochastic Lyapunov value is bounded by
the deterministic initial potential on every admissible sample path. -/
private lemma lyapunovOne_le_initialPotentialBound
    (run : StochasticRun h oracle ℙ x₀ multiplier₀ params Q B b)
    {N : ℕ} (hN : 1 ≤ N) (h_admissible : run.IsAdmissiblePrefix N)
    (ω : Ω) :
    run.lyapunov 1 ω ≤ LALM.initialPotentialBound h params := by
  have hzeroLt : 0 < N := by omega
  have hsegment :=
    (run.isAdmissiblePrefix_iff N).1 h_admissible 0 hzeroLt ω
  have hnormBounds := admissiblePrefixNormBounds run N h_admissible
  have hstep := hnormBounds.1 0 hzeroLt ω
  have hmultiplierZero := hnormBounds.2 0 (Nat.zero_le N) ω
  have hmultiplierOne := hnormBounds.2 1 hN ω
  have hobjectiveIncrement :
      ‖f (run.point 1 ω) - f (run.point 0 ω)‖ ≤
        h.gradientBound * ‖run.point 1 ω - run.point 0 ω‖ := by
    apply (convex_segment (run.point 0 ω) (run.point 1 ω)).norm_image_sub_le_of_norm_fderiv_le
      (𝕜 := ℝ)
    · intro u hu
      exact h.differentiableAt_objective (hsegment hu)
    · intro u hu
      simpa only [← toDual_gradient, LinearIsometryEquiv.norm_map] using
        h.norm_gradient_le u (hsegment hu)
    · exact left_mem_segment ℝ (run.point 0 ω) (run.point 1 ω)
    · exact right_mem_segment ℝ (run.point 0 ω) (run.point 1 ω)
  have hdisplacement :
      ‖run.point 1 ω - run.point 0 ω‖ = ‖run.step 0 ω‖ := by
    rw [run.point_succ 0, add_sub_cancel_left]
  have hsignedObjective :
      f (run.point 1 ω) - f (run.point 0 ω) ≤
        ‖f (run.point 1 ω) - f (run.point 0 ω)‖ := by
    simpa only [Real.norm_eq_abs] using
      le_abs_self (f (run.point 1 ω) - f (run.point 0 ω))
  have hobjective :
      f (run.point 1 ω) ≤ f x₀ + h.gradientBound * params.delta := by
    have hgradientStep :
        (h.gradientBound : ℝ) * ‖run.step 0 ω‖ ≤
          h.gradientBound * params.delta :=
      mul_le_mul_of_nonneg_left hstep (NNReal.coe_nonneg h.gradientBound)
    rw [hdisplacement] at hobjectiveIncrement
    rw [run.point_zero] at hsignedObjective hobjectiveIncrement
    linarith
  have hresidualIdentity :
      (params.rho : ℝ) • c (run.point 1 ω) =
        run.multiplier 1 ω - run.multiplier 0 ω := by
    have hupdate :
        run.multiplier 1 ω = run.multiplier 0 ω +
          (params.rho : ℝ) • c (run.point 1 ω) :=
      run.multiplier_succ 0 ω
    rw [hupdate]
    module
  have hρ : 0 < (params.rho : ℝ) := params.spec.1.2.2.1
  have hscaledResidual :
      params.rho * ‖c (run.point 1 ω)‖ ≤ 2 * params.multiplierBound := by
    calc
      params.rho * ‖c (run.point 1 ω)‖ =
          ‖(params.rho : ℝ) • c (run.point 1 ω)‖ := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos hρ]
      _ = ‖run.multiplier 1 ω - run.multiplier 0 ω‖ :=
        congrArg norm hresidualIdentity
      _ ≤ ‖run.multiplier 1 ω‖ + ‖run.multiplier 0 ω‖ := norm_sub_le _ _
      _ ≤ 2 * params.multiplierBound := by linarith
  have hboundNonneg : (0 : ℝ) ≤ params.multiplierBound := by positivity
  have hinnerBound :
      ⟪run.multiplier 1 ω, c (run.point 1 ω)⟫_ℝ ≤
        params.multiplierBound * ‖c (run.point 1 ω)‖ := by
    calc
      ⟪run.multiplier 1 ω, c (run.point 1 ω)⟫_ℝ ≤
          ‖run.multiplier 1 ω‖ * ‖c (run.point 1 ω)‖ :=
        real_inner_le_norm _ _
      _ ≤ params.multiplierBound * ‖c (run.point 1 ω)‖ :=
        mul_le_mul_of_nonneg_right hmultiplierOne (norm_nonneg _)
  have hinnerScaled :
      params.rho * ⟪run.multiplier 1 ω, c (run.point 1 ω)⟫_ℝ ≤
        2 * params.multiplierBound ^ 2 := by
    have hinnerRho := mul_le_mul_of_nonneg_left hinnerBound hρ.le
    have hresidualBound := mul_le_mul_of_nonneg_left hscaledResidual hboundNonneg
    nlinarith
  have htwoNonneg : (0 : ℝ) ≤ 2 := by norm_num
  have hscaledResidualSq :
      (params.rho * ‖c (run.point 1 ω)‖) ^ 2 ≤
        (2 * params.multiplierBound) ^ 2 :=
    (sq_le_sq₀ (mul_nonneg hρ.le (norm_nonneg _))
      (mul_nonneg htwoNonneg hboundNonneg)).2 hscaledResidual
  have hconstraintContribution :
      ⟪run.multiplier 1 ω, c (run.point 1 ω)⟫_ℝ +
          params.rho / 2 * ‖c (run.point 1 ω)‖ ^ 2 ≤
        4 * params.multiplierBound ^ 2 / params.rho := by
    apply (le_div_iff₀ hρ).2
    nlinarith
  have hconstantNonneg :
      0 ≤ multiplierPrimalConstant h params.delta params.beta params.rho
        params.multiplierBound := by
    rw [multiplierPrimalConstant_def]
    positivity
  have hstepSq : ‖run.step 0 ω‖ ^ 2 ≤ (params.delta : ℝ) ^ 2 :=
    (sq_le_sq₀ (norm_nonneg _) (NNReal.coe_nonneg _)).2 hstep
  have hcorrection :
      (multiplierPrimalConstant h params.delta params.beta params.rho
          params.multiplierBound / params.rho) * ‖run.step 0 ω‖ ^ 2 ≤
        (multiplierPrimalConstant h params.delta params.beta params.rho
          params.multiplierBound / params.rho) * params.delta ^ 2 :=
    mul_le_mul_of_nonneg_left hstepSq (div_nonneg hconstantNonneg hρ.le)
  rw [run.lyapunov_def, augmentedLagrangian_def, LALM.initialPotentialBound_def]
  norm_num only [Nat.reduceSub]
  linarith

/-- Helper for Lemma 3.4: pathwise Lyapunov telescoping bounds all primal
step squares by the initial allowance and accumulated gradient errors. -/
private lemma sumStepSq_le_pathwise
    (run : StochasticRun h oracle ℙ x₀ multiplier₀ params Q B b)
    (K : ℕ) (hK : 2 ≤ K) (h_admissible : run.IsAdmissiblePrefix K)
    (ω : Ω) :
    ∑ k ∈ Finset.range K, ‖run.step k ω‖ ^ 2 ≤
      initialStepBound h params + errorStepConstant h params *
        ∑ k ∈ Finset.range K, ‖run.gradientError k ω‖ ^ 2 := by
  have hdescent :
      (∑ k ∈ Finset.Ico 1 K,
          (params.beta / 4) * ‖run.step k ω‖ ^ 2) ≤
        ∑ k ∈ Finset.Ico 1 K,
          ((run.lyapunov k ω - run.lyapunov (k + 1) ω) +
            lyapunovErrorConstant h params *
              (‖run.gradientError k ω‖ ^ 2 +
                ‖run.gradientError (k - 1) ω‖ ^ 2)) := by
    refine Finset.sum_le_sum fun k hk ↦ ?_
    have hkBounds := Finset.mem_Ico.mp hk
    have hstep := run.lyapunovDescent h_admissible hkBounds.1 hkBounds.2 ω
    linarith
  have htelescope :
      (∑ k ∈ Finset.Ico 1 K,
          (run.lyapunov k ω - run.lyapunov (k + 1) ω)) =
        run.lyapunov 1 ω - run.lyapunov K ω := by
    have hendpointLeft : 1 + (K - 1) = K := by omega
    have hendpointRight : K - 1 + 1 = K := by omega
    rw [Finset.sum_Ico_eq_sum_range]
    simpa only [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc,
      hendpointLeft, hendpointRight] using
      (Finset.sum_range_sub' (fun k ↦ run.lyapunov (k + 1) ω) (K - 1))
  have hcurrentSubset : Finset.Ico 1 K ⊆ Finset.range K := by
    intro k hk
    exact Finset.mem_range.mpr (Finset.mem_Ico.mp hk).2
  have hcurrentErrors :
      (∑ k ∈ Finset.Ico 1 K, ‖run.gradientError k ω‖ ^ 2) ≤
        ∑ k ∈ Finset.range K, ‖run.gradientError k ω‖ ^ 2 := by
    exact Finset.sum_le_sum_of_subset_of_nonneg hcurrentSubset
      (fun k _ _ ↦ sq_nonneg ‖run.gradientError k ω‖)
  have hpreviousErrorEq :
      (∑ k ∈ Finset.Ico 1 K, ‖run.gradientError (k - 1) ω‖ ^ 2) =
        ∑ j ∈ Finset.range (K - 1), ‖run.gradientError j ω‖ ^ 2 := by
    rw [Finset.sum_Ico_eq_sum_range]
    apply Finset.sum_congr rfl
    intro j hj
    have hindex : 1 + j - 1 = j := by omega
    rw [hindex]
  have hpreviousSubset : Finset.range (K - 1) ⊆ Finset.range K := by
    intro j hj
    simp only [Finset.mem_range] at hj ⊢
    omega
  have hpreviousErrors :
      (∑ k ∈ Finset.Ico 1 K, ‖run.gradientError (k - 1) ω‖ ^ 2) ≤
        ∑ k ∈ Finset.range K, ‖run.gradientError k ω‖ ^ 2 := by
    rw [hpreviousErrorEq]
    exact Finset.sum_le_sum_of_subset_of_nonneg hpreviousSubset
      (fun k _ _ ↦ sq_nonneg ‖run.gradientError k ω‖)
  have hadjacentErrors :
      (∑ k ∈ Finset.Ico 1 K,
          (‖run.gradientError k ω‖ ^ 2 +
            ‖run.gradientError (k - 1) ω‖ ^ 2)) ≤
        2 * ∑ k ∈ Finset.range K, ‖run.gradientError k ω‖ ^ 2 := by
    rw [Finset.sum_add_distrib]
    linarith
  rw [← Finset.mul_sum, Finset.sum_add_distrib, htelescope,
    ← Finset.mul_sum] at hdescent
  have hOne : 1 ≤ K := by omega
  have hzeroLt : 0 < K := by omega
  have hlower := lyapunovLowerBound_le run h_admissible hOne (Nat.le_refl K) ω
  have herrorCoefficientNonneg : 0 ≤ lyapunovErrorConstant h params := by
    rw [lyapunovErrorConstant_def, multiplierErrorConstant_def]
    positivity
  have herrorContribution :=
    mul_le_mul_of_nonneg_left hadjacentErrors herrorCoefficientNonneg
  have henergy :
      (params.beta / 4) *
          (∑ k ∈ Finset.Ico 1 K, ‖run.step k ω‖ ^ 2) ≤
        run.lyapunov 1 ω - LALM.lyapunovLowerBound h params +
          2 * lyapunovErrorConstant h params *
            ∑ k ∈ Finset.range K, ‖run.gradientError k ω‖ ^ 2 := by
    nlinarith
  have hbeta : 0 < (params.beta : ℝ) := params.spec.1.2.1
  have hscalingNonneg : 0 ≤ 4 / (params.beta : ℝ) := by positivity
  have hsumIco :
      (∑ k ∈ Finset.Ico 1 K, ‖run.step k ω‖ ^ 2) ≤
        4 * (run.lyapunov 1 ω - LALM.lyapunovLowerBound h params) / params.beta +
          (8 * lyapunovErrorConstant h params / params.beta) *
            ∑ k ∈ Finset.range K, ‖run.gradientError k ω‖ ^ 2 := by
    calc
      (∑ k ∈ Finset.Ico 1 K, ‖run.step k ω‖ ^ 2) =
          (4 / params.beta) *
            ((params.beta / 4) *
              ∑ k ∈ Finset.Ico 1 K, ‖run.step k ω‖ ^ 2) := by
        field_simp [hbeta.ne']
      _ ≤ (4 / params.beta) *
          (run.lyapunov 1 ω - LALM.lyapunovLowerBound h params +
            2 * lyapunovErrorConstant h params *
              ∑ k ∈ Finset.range K, ‖run.gradientError k ω‖ ^ 2) :=
        mul_le_mul_of_nonneg_left henergy hscalingNonneg
      _ = 4 * (run.lyapunov 1 ω - LALM.lyapunovLowerBound h params) /
            params.beta +
          (8 * lyapunovErrorConstant h params / params.beta) *
            ∑ k ∈ Finset.range K, ‖run.gradientError k ω‖ ^ 2 := by ring
  have hupper := lyapunovOne_le_initialPotentialBound run hOne h_admissible ω
  have hgap := sub_le_sub_right hupper (LALM.lyapunovLowerBound h params)
  have hgapScaled := mul_le_mul_of_nonneg_left hgap hscalingNonneg
  have hgapScaledNormalized :
      4 * (run.lyapunov 1 ω - LALM.lyapunovLowerBound h params) / params.beta ≤
        4 * (LALM.initialPotentialBound h params -
          LALM.lyapunovLowerBound h params) / params.beta := by
    calc
      4 * (run.lyapunov 1 ω - LALM.lyapunovLowerBound h params) / params.beta =
          (4 / params.beta) *
            (run.lyapunov 1 ω - LALM.lyapunovLowerBound h params) := by ring
      _ ≤ (4 / params.beta) *
          (LALM.initialPotentialBound h params -
            LALM.lyapunovLowerBound h params) := hgapScaled
      _ = 4 * (LALM.initialPotentialBound h params -
          LALM.lyapunovLowerBound h params) / params.beta := by ring
  have hnormBounds := admissiblePrefixNormBounds run K h_admissible
  have hstepZero := hnormBounds.1 0 hzeroLt ω
  have hstepZeroSq :
      ‖run.step 0 ω‖ ^ 2 ≤ (params.delta : ℝ) ^ 2 :=
    (sq_le_sq₀ (norm_nonneg _) (NNReal.coe_nonneg _)).2 hstepZero
  have hdecomposition :
      (∑ k ∈ Finset.range K, ‖run.step k ω‖ ^ 2) =
        ‖run.step 0 ω‖ ^ 2 +
          ∑ k ∈ Finset.Ico 1 K, ‖run.step k ω‖ ^ 2 := by
    rw [Finset.sum_Ico_eq_sub _ hOne]
    simp
  rw [hdecomposition, initialStepBound_def, errorStepConstant_def]
  linarith

/-- Helper for Lemma 3.4: radial clipping is a measurable map on Euclidean
space. -/
private lemma measurableClip (G : ℝ≥0) :
    Measurable (SPIDER.clip G :
      EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) := by
  unfold SPIDER.clip
  apply Measurable.ite
  · exact measurableSet_le continuous_norm.measurable measurable_const
  · exact measurable_id
  · exact (measurable_const.div continuous_norm.measurable).smul measurable_id

/-- Helper for Lemma 3.4: every squared projected-gradient error in an
admissible prefix is integrable. -/
private lemma integrableGradientErrorSquare
    (run : StochasticRun h oracle ℙ x₀ multiplier₀ params Q B b)
    {K k : ℕ} (h_admissible : run.IsAdmissiblePrefix K) (hk : k < K) :
    Integrable (fun ω ↦ ‖run.gradientError k ω‖ ^ 2) ℙ := by
  have hestimate : AEMeasurable (run.gradientEstimate k) ℙ := by
    have hcomposed := (measurableClip h.gradientBound).comp_aemeasurable
      (run.aemeasurable_rawEstimate k)
    have hestimateEq :
        run.gradientEstimate k =
          SPIDER.clip h.gradientBound ∘
            SPIDER.rawEstimate oracle run.point run.sample Q B b k := by
      funext ω
      rw [run.gradientEstimate_apply, SPIDER.estimate_apply]
      rfl
    rw [hestimateEq]
    exact hcomposed
  have hgradientExtension :
      AEMeasurable (fun ω ↦ h.objectiveGradientExtension (run.point k ω)) ℙ :=
    h.measurable_objectiveGradientExtension.comp_aemeasurable
      (run.aemeasurable_point k)
  have hgradient :
      AEMeasurable (fun ω ↦ gradient f (run.point k ω)) ℙ := by
    apply hgradientExtension.congr
    apply ae_of_all
    intro ω
    have hx :=
      (run.pointsInRegion_iff K).mp h_admissible.pointsInRegion k hk ω
    exact h.objectiveGradientExtension_eq hx
  have herror : AEMeasurable (run.gradientError k) ℙ := by
    have herrorEq :
        run.gradientError k =
          fun ω ↦ run.gradientEstimate k ω - gradient f (run.point k ω) := by
      funext ω
      exact run.gradientError_apply k ω
    rw [herrorEq]
    exact hestimate.sub hgradient
  have hsquareMeasurable :
      AEStronglyMeasurable (fun ω ↦ ‖run.gradientError k ω‖ ^ 2) ℙ :=
    (herror.norm.pow_const 2).aestronglyMeasurable
  have hbound (ω : Ω) :
      ‖(‖run.gradientError k ω‖ ^ 2 : ℝ)‖ ≤
        (2 * (h.gradientBound : ℝ)) ^ 2 := by
    have hx :=
      (run.pointsInRegion_iff K).mp h_admissible.pointsInRegion k hk ω
    have hestimateNorm : ‖run.gradientEstimate k ω‖ ≤ h.gradientBound := by
      rw [run.gradientEstimate_apply, SPIDER.estimate_apply]
      exact SPIDER.norm_clip_le h.gradientBound _
    have hgradientNorm : ‖gradient f (run.point k ω)‖ ≤ h.gradientBound :=
      h.norm_gradient_le _ hx
    have herrorNorm :
        ‖run.gradientError k ω‖ ≤ 2 * (h.gradientBound : ℝ) := by
      rw [run.gradientError_apply]
      calc
        ‖run.gradientEstimate k ω - gradient f (run.point k ω)‖ ≤
            ‖run.gradientEstimate k ω‖ + ‖gradient f (run.point k ω)‖ :=
          norm_sub_le _ _
        _ ≤ 2 * (h.gradientBound : ℝ) := by linarith
    have hclipBoundNonneg : 0 ≤ 2 * (h.gradientBound : ℝ) := by positivity
    have hsquare :=
      (sq_le_sq₀ (norm_nonneg _) hclipBoundNonneg).2 herrorNorm
    simpa only [Real.norm_of_nonneg (sq_nonneg _)] using hsquare
  exact Integrable.mono' (integrable_const _)
    hsquareMeasurable (ae_of_all ℙ hbound)

/-- Pointwise form of Lemma 3.4 (4): on an admissible prefix of length at least
two, accumulated step mean square is bounded by the initial allowance and
accumulated error. -/
theorem accumulatedStepMeanSquare_le_of_isAdmissiblePrefix
    (K : ℕ) (hK : 2 ≤ K) (h_admissible : run.IsAdmissiblePrefix K) :
    ∑ k ∈ Finset.range K, run.stepMeanSquare k ≤
      initialStepBound h params + errorStepConstant h params *
        ∑ k ∈ Finset.range K, run.gradientErrorMeanSquare k := by
  have hstepIntegrable :
      Integrable (fun ω ↦ ∑ k ∈ Finset.range K, ‖run.step k ω‖ ^ 2) ℙ :=
    integrable_finsetSum (Finset.range K)
      (fun k hk ↦ integrableStepSquare run h_admissible (Finset.mem_range.mp hk))
  have herrorIntegrable (k : ℕ) (hk : k ∈ Finset.range K) :
      Integrable (fun ω ↦ ‖run.gradientError k ω‖ ^ 2) ℙ :=
    integrableGradientErrorSquare run h_admissible (Finset.mem_range.mp hk)
  have herrorsIntegrable :
      Integrable (fun ω ↦
        ∑ k ∈ Finset.range K, ‖run.gradientError k ω‖ ^ 2) ℙ :=
    integrable_finsetSum (Finset.range K) herrorIntegrable
  have hrightIntegrable :
      Integrable (fun ω ↦ initialStepBound h params +
        errorStepConstant h params *
          ∑ k ∈ Finset.range K, ‖run.gradientError k ω‖ ^ 2) ℙ :=
    (integrable_const _).add
      (herrorsIntegrable.const_mul (errorStepConstant h params))
  have hintegral := integral_mono hstepIntegrable hrightIntegrable
    (sumStepSq_le_pathwise run K hK h_admissible)
  have hstepIntegral :
      (∫ ω, ∑ k ∈ Finset.range K, ‖run.step k ω‖ ^ 2 ∂ℙ) =
        ∑ k ∈ Finset.range K, run.stepMeanSquare k := by
    rw [integral_finsetSum (Finset.range K)
      (fun k hk ↦ integrableStepSquare run h_admissible (Finset.mem_range.mp hk))]
    rfl
  have herrorIntegral :
      (∫ ω, ∑ k ∈ Finset.range K, ‖run.gradientError k ω‖ ^ 2 ∂ℙ) =
        ∑ k ∈ Finset.range K, run.gradientErrorMeanSquare k := by
    rw [integral_finsetSum (Finset.range K) herrorIntegrable]
    rfl
  have hrightIntegral :
      (∫ ω, initialStepBound h params + errorStepConstant h params *
          ∑ k ∈ Finset.range K, ‖run.gradientError k ω‖ ^ 2 ∂ℙ) =
        initialStepBound h params + errorStepConstant h params *
          ∑ k ∈ Finset.range K, run.gradientErrorMeanSquare k := by
    rw [integral_add (integrable_const _)
      (herrorsIntegrable.const_mul (errorStepConstant h params)),
      integral_const, integral_const_mul, herrorIntegral]
    simp only [Measure.real, measure_univ, ENNReal.toReal_one, one_smul]
  rw [hstepIntegral, hrightIntegral] at hintegral
  exact hintegral

/-- Helper for Lemma 3.4: every projected-gradient-error mean square is
nonnegative. -/
private lemma gradientErrorMeanSquare_nonneg
    (run : StochasticRun h oracle ℙ x₀ multiplier₀ params Q B b) (k : ℕ) :
    0 ≤ run.gradientErrorMeanSquare k := by
  rw [run.gradientErrorMeanSquare_def]
  exact integral_nonneg fun ω ↦ sq_nonneg ‖run.gradientError k ω‖

/-- Helper for Lemma 3.4: every primal-step mean square is nonnegative. -/
private lemma stepMeanSquare_nonneg
    (run : StochasticRun h oracle ℙ x₀ multiplier₀ params Q B b) (k : ℕ) :
    0 ≤ run.stepMeanSquare k := by
  rw [run.stepMeanSquare_def]
  exact integral_nonneg fun ω ↦ sq_nonneg ‖run.step k ω‖

/-- Helper for Lemma 3.4: the coefficient transferring gradient error to
primal steps is strictly positive. -/
private lemma errorStepConstant_pos
    (h : EqualityConstrained.Regularity f c)
    (params : Parameters h x₀ multiplier₀) :
    0 < errorStepConstant h params := by
  have hbeta : 0 < (params.beta : ℝ) := params.spec.1.2.1
  have hrho : 0 < (params.rho : ℝ) := params.spec.1.2.2.1
  have hfirst : 0 < (2 : ℝ) / params.beta := by positivity
  have hsecond :
      0 ≤ ((4 : ℝ) / h.licqModulus ^ 2) / params.rho := by positivity
  have hsum :
      0 < (2 : ℝ) / params.beta +
        ((4 : ℝ) / h.licqModulus ^ 2) / params.rho :=
    add_pos_of_pos_of_nonneg hfirst hsecond
  rw [errorStepConstant_def, lyapunovErrorConstant_def,
    multiplierErrorConstant_def]
  positivity

/-- Helper for Lemma 3.4: the initial accumulated-step allowance is
nonnegative on every admissible prefix of length at least two. -/
private lemma initialStepBound_nonneg
    (run : StochasticRun h oracle ℙ x₀ multiplier₀ params Q B b)
    (K : ℕ) (hK : 2 ≤ K) (h_admissible : run.IsAdmissiblePrefix K) :
    0 ≤ initialStepBound h params := by
  obtain ⟨ω⟩ := nonempty_of_isProbabilityMeasure ℙ
  have hOne : 1 ≤ K := by omega
  have hlower := lyapunovLowerBound_le run h_admissible (Nat.le_refl 1) hOne ω
  have hupper := lyapunovOne_le_initialPotentialBound run hOne h_admissible ω
  have hgap :
      0 ≤ LALM.initialPotentialBound h params - LALM.lyapunovLowerBound h params := by
    linarith
  rw [initialStepBound_def]
  have hbeta : 0 < (params.beta : ℝ) := params.spec.1.2.1
  positivity

/-- Helper for Lemma 3.4: a sufficient inner batch makes the coupled
SPIDER error-step coefficient at most one half. -/
private lemma errorStepBatchCoefficient_le_half
    (h : EqualityConstrained.Regularity f c)
    (oracle : EqualityConstrained.StochasticOracle f h.region ν)
    (params : Parameters h x₀ multiplier₀) (Q b : ℕ+)
    (h_batch : SPIDER.IsSufficientInnerBatchSize h oracle params Q b) :
    errorStepConstant h params *
        ((Q : ℝ) * oracle.meanSquareLipschitz ^ 2 / (b : ℝ)) ≤
      (1 : ℝ) / 2 := by
  have hbatch :=
    (SPIDER.isSufficientInnerBatchSize_iff h oracle params Q b).mp h_batch
  have hb : 0 < (b : ℝ) := by positivity
  have hdivided :
      (2 * errorStepConstant h params * (Q : ℝ) *
          oracle.meanSquareLipschitz ^ 2) / (b : ℝ) ≤ 1 := by
    calc
      (2 * errorStepConstant h params * (Q : ℝ) *
          oracle.meanSquareLipschitz ^ 2) / (b : ℝ) ≤
          (b : ℝ) / (b : ℝ) :=
        (div_le_div_iff_of_pos_right hb).2 hbatch
      _ = 1 := div_self hb.ne'
  have htwoNonneg : (0 : ℝ) ≤ 2 := by norm_num
  calc
    errorStepConstant h params *
        ((Q : ℝ) * oracle.meanSquareLipschitz ^ 2 / (b : ℝ)) =
        ((2 * errorStepConstant h params * (Q : ℝ) *
          oracle.meanSquareLipschitz ^ 2) / (b : ℝ)) / 2 := by ring
    _ ≤ (1 : ℝ) / 2 := div_le_div_of_nonneg_right hdivided htwoNonneg

/-- Pointwise form of Lemma 3.4 (5): under
`SPIDER.IsSufficientInnerBatchSize`, the average projected-gradient-error mean
square has the stated variance and initial terms. -/
theorem averageGradientErrorMeanSquare_le_of_isAdmissiblePrefix
    (K : ℕ) (hK : 2 ≤ K) (h_admissible : run.IsAdmissiblePrefix K)
    (h_batch : SPIDER.IsSufficientInnerBatchSize h oracle params Q b) :
    (∑ k ∈ Finset.range K, run.gradientErrorMeanSquare k) / K ≤
      2 * oracle.noiseLevel ^ 2 / B +
        initialStepBound h params / (errorStepConstant h params * K) := by
  have hspider := run.accumulatedGradientErrorMeanSquare_le K h_admissible.isAE
    (fun k hk ↦ integrableStepSquare run h_admissible hk)
  have hsteps :=
    run.accumulatedStepMeanSquare_le_of_isAdmissiblePrefix K hK h_admissible
  have habsorb := errorStepBatchCoefficient_le_half h oracle params Q b h_batch
  have hDpos := errorStepConstant_pos h params
  have hDzero : errorStepConstant h params ≠ 0 := hDpos.ne'
  have hD0nonneg := initialStepBound_nonneg run K hK h_admissible
  have herrorSumNonneg :
      0 ≤ ∑ k ∈ Finset.range K, run.gradientErrorMeanSquare k :=
    Finset.sum_nonneg fun k _ ↦ gradientErrorMeanSquare_nonneg run k
  have hstepSumNonneg :
      0 ≤ ∑ k ∈ Finset.range K, run.stepMeanSquare k :=
    Finset.sum_nonneg fun k _ ↦ stepMeanSquare_nonneg run k
  have hcoefficientNonneg :
      0 ≤ (Q : ℝ) * oracle.meanSquareLipschitz ^ 2 / (b : ℝ) := by
    positivity
  have hstepsScaled :=
    mul_le_mul_of_nonneg_left hsteps hcoefficientNonneg
  have hspiderCombined :
      ∑ k ∈ Finset.range K, run.gradientErrorMeanSquare k ≤
        K * oracle.noiseLevel ^ 2 / B +
          ((Q : ℝ) * oracle.meanSquareLipschitz ^ 2 / (b : ℝ)) *
            (initialStepBound h params + errorStepConstant h params *
              ∑ k ∈ Finset.range K, run.gradientErrorMeanSquare k) := by
    exact hspider.trans (add_le_add (le_refl _) hstepsScaled)
  have habsorbCommuted :
      ((Q : ℝ) * oracle.meanSquareLipschitz ^ 2 / (b : ℝ)) *
          errorStepConstant h params ≤ (1 : ℝ) / 2 := by
    simpa only [mul_comm] using habsorb
  have habsorbError :=
    mul_le_mul_of_nonneg_right habsorbCommuted herrorSumNonneg
  have hcoefficientLe :
      (Q : ℝ) * oracle.meanSquareLipschitz ^ 2 / (b : ℝ) ≤
        ((1 : ℝ) / 2) / errorStepConstant h params :=
    (le_div_iff₀ hDpos).2 habsorbCommuted
  have hinitialContribution :=
    mul_le_mul_of_nonneg_right hcoefficientLe hD0nonneg
  have hspiderExpanded :
      ∑ k ∈ Finset.range K, run.gradientErrorMeanSquare k ≤
        K * oracle.noiseLevel ^ 2 / B +
          ((Q : ℝ) * oracle.meanSquareLipschitz ^ 2 / (b : ℝ)) *
            initialStepBound h params +
          (((Q : ℝ) * oracle.meanSquareLipschitz ^ 2 / (b : ℝ)) *
            errorStepConstant h params) *
              ∑ k ∈ Finset.range K, run.gradientErrorMeanSquare k := by
    calc
      ∑ k ∈ Finset.range K, run.gradientErrorMeanSquare k ≤
          K * oracle.noiseLevel ^ 2 / B +
            ((Q : ℝ) * oracle.meanSquareLipschitz ^ 2 / (b : ℝ)) *
              (initialStepBound h params + errorStepConstant h params *
                ∑ k ∈ Finset.range K, run.gradientErrorMeanSquare k) :=
        hspiderCombined
      _ = K * oracle.noiseLevel ^ 2 / B +
          ((Q : ℝ) * oracle.meanSquareLipschitz ^ 2 / (b : ℝ)) *
            initialStepBound h params +
          (((Q : ℝ) * oracle.meanSquareLipschitz ^ 2 / (b : ℝ)) *
            errorStepConstant h params) *
              ∑ k ∈ Finset.range K, run.gradientErrorMeanSquare k := by ring
  have hinitialNormalized :
      ((Q : ℝ) * oracle.meanSquareLipschitz ^ 2 / (b : ℝ)) *
          initialStepBound h params ≤
        initialStepBound h params / (2 * errorStepConstant h params) := by
    calc
      ((Q : ℝ) * oracle.meanSquareLipschitz ^ 2 / (b : ℝ)) *
          initialStepBound h params ≤
          ((1 : ℝ) / 2) / errorStepConstant h params *
            initialStepBound h params := hinitialContribution
      _ = initialStepBound h params /
          (2 * errorStepConstant h params) := by
        field_simp [hDzero]
  have hboundExpanded :
      ∑ k ∈ Finset.range K, run.gradientErrorMeanSquare k ≤
        K * oracle.noiseLevel ^ 2 / B +
          initialStepBound h params / (2 * errorStepConstant h params) +
          (1 / 2 : ℝ) *
            ∑ k ∈ Finset.range K, run.gradientErrorMeanSquare k :=
    hspiderExpanded.trans
      (add_le_add
        (add_le_add (le_refl _) hinitialNormalized) habsorbError)
  have hpretotal :
      ∑ k ∈ Finset.range K, run.gradientErrorMeanSquare k ≤
        2 * (K * oracle.noiseLevel ^ 2 / B) +
          2 * (initialStepBound h params /
            (2 * errorStepConstant h params)) := by
    linarith
  have htotal :
      ∑ k ∈ Finset.range K, run.gradientErrorMeanSquare k ≤
        2 * (K * oracle.noiseLevel ^ 2 / B) +
          initialStepBound h params / errorStepConstant h params := by
    calc
      ∑ k ∈ Finset.range K, run.gradientErrorMeanSquare k ≤
          2 * (K * oracle.noiseLevel ^ 2 / B) +
            2 * (initialStepBound h params /
              (2 * errorStepConstant h params)) := hpretotal
      _ = 2 * (K * oracle.noiseLevel ^ 2 / B) +
          initialStepBound h params / errorStepConstant h params := by
        field_simp [hDzero]
  have hKreal : 0 < (K : ℝ) := by positivity
  apply (div_le_iff₀ hKreal).2
  calc
    ∑ k ∈ Finset.range K, run.gradientErrorMeanSquare k ≤
        2 * (K * oracle.noiseLevel ^ 2 / B) +
          initialStepBound h params / errorStepConstant h params := htotal
    _ = (2 * oracle.noiseLevel ^ 2 / B +
        initialStepBound h params / (errorStepConstant h params * K)) * K := by
      field_simp [hDzero]

/-- Pointwise form of Lemma 3.4 (6): under
`SPIDER.IsSufficientInnerBatchSize`, the average primal step mean square has the
stated variance and initial terms. -/
theorem averageStepMeanSquare_le_of_isAdmissiblePrefix
    (K : ℕ) (hK : 2 ≤ K) (h_admissible : run.IsAdmissiblePrefix K)
    (h_batch : SPIDER.IsSufficientInnerBatchSize h oracle params Q b) :
    (∑ k ∈ Finset.range K, run.stepMeanSquare k) / K ≤
      2 * errorStepConstant h params * oracle.noiseLevel ^ 2 / B +
        2 * initialStepBound h params / K := by
  have hsteps :=
    run.accumulatedStepMeanSquare_le_of_isAdmissiblePrefix K hK h_admissible
  have herrors :=
    run.averageGradientErrorMeanSquare_le_of_isAdmissiblePrefix K hK
      h_admissible h_batch
  have hDpos := errorStepConstant_pos h params
  have hDzero : errorStepConstant h params ≠ 0 := hDpos.ne'
  have hKreal : 0 < (K : ℝ) := by positivity
  have hKzero : (K : ℝ) ≠ 0 := hKreal.ne'
  have hstepsDivided := (div_le_div_iff_of_pos_right hKreal).2 hsteps
  have hstepsNormalized :
      (∑ k ∈ Finset.range K, run.stepMeanSquare k) / K ≤
        initialStepBound h params / K + errorStepConstant h params *
          ((∑ k ∈ Finset.range K, run.gradientErrorMeanSquare k) / K) := by
    calc
      (∑ k ∈ Finset.range K, run.stepMeanSquare k) / K ≤
          (initialStepBound h params + errorStepConstant h params *
            ∑ k ∈ Finset.range K, run.gradientErrorMeanSquare k) / K :=
        hstepsDivided
      _ = initialStepBound h params / K + errorStepConstant h params *
          ((∑ k ∈ Finset.range K, run.gradientErrorMeanSquare k) / K) := by
        ring
  have herrorsScaledRaw :=
    mul_le_mul_of_nonneg_left herrors hDpos.le
  have herrorsScaled :
      errorStepConstant h params *
          ((∑ k ∈ Finset.range K, run.gradientErrorMeanSquare k) / K) ≤
        2 * errorStepConstant h params * oracle.noiseLevel ^ 2 / B +
          initialStepBound h params / K := by
    calc
      errorStepConstant h params *
          ((∑ k ∈ Finset.range K, run.gradientErrorMeanSquare k) / K) ≤
          errorStepConstant h params *
            (2 * oracle.noiseLevel ^ 2 / B +
              initialStepBound h params /
                (errorStepConstant h params * K)) := herrorsScaledRaw
      _ = 2 * errorStepConstant h params * oracle.noiseLevel ^ 2 / B +
          initialStepBound h params / K := by
        field_simp [hDzero, hKzero]
  calc
    (∑ k ∈ Finset.range K, run.stepMeanSquare k) / K ≤
        initialStepBound h params / K + errorStepConstant h params *
          ((∑ k ∈ Finset.range K, run.gradientErrorMeanSquare k) / K) :=
      hstepsNormalized
    _ ≤ initialStepBound h params / K +
        (2 * errorStepConstant h params * oracle.noiseLevel ^ 2 / B +
          initialStepBound h params / K) :=
      add_le_add (le_refl _) herrorsScaled
    _ = 2 * errorStepConstant h params * oracle.noiseLevel ^ 2 / B +
        2 * initialStepBound h params / K := by ring

/-- Lemma 3.4 (4): on an almost-surely admissible prefix of length at least two,
accumulated step mean square is bounded by the initial allowance and accumulated
error. -/
theorem accumulatedStepMeanSquare_le
    (K : ℕ) (hK : 2 ≤ K) (h_admissible : run.IsAEAdmissiblePrefix K) :
    ∑ k ∈ Finset.range K, run.stepMeanSquare k ≤
      initialStepBound h params + errorStepConstant h params *
        ∑ k ∈ Finset.range K, run.gradientErrorMeanSquare k := by
  obtain ⟨run', hrun'_admissible, _hpoint, _hmultiplier, hstep, herror⟩ :=
    h_admissible.exists_pathwiseVersion run K
  have hstepMeanSquare (k : ℕ) :
      run'.stepMeanSquare k = run.stepMeanSquare k := by
    rw [run'.stepMeanSquare_def, run.stepMeanSquare_def]
    exact integral_congr_ae ((hstep k).fun_comp fun p ↦ ‖p‖ ^ 2)
  have herrorMeanSquare (k : ℕ) :
      run'.gradientErrorMeanSquare k = run.gradientErrorMeanSquare k := by
    rw [run'.gradientErrorMeanSquare_def, run.gradientErrorMeanSquare_def]
    exact integral_congr_ae ((herror k).fun_comp fun e ↦ ‖e‖ ^ 2)
  have hbound := run'.accumulatedStepMeanSquare_le_of_isAdmissiblePrefix K hK
    hrun'_admissible
  simpa only [hstepMeanSquare, herrorMeanSquare] using hbound

/-- Lemma 3.4 (5): on an almost-surely admissible prefix and under
`SPIDER.IsSufficientInnerBatchSize`, the average projected-gradient-error mean
square has the stated variance and initial terms. -/
theorem averageGradientErrorMeanSquare_le
    (K : ℕ) (hK : 2 ≤ K) (h_admissible : run.IsAEAdmissiblePrefix K)
    (h_batch : SPIDER.IsSufficientInnerBatchSize h oracle params Q b) :
    (∑ k ∈ Finset.range K, run.gradientErrorMeanSquare k) / K ≤
      2 * oracle.noiseLevel ^ 2 / B +
        initialStepBound h params / (errorStepConstant h params * K) := by
  obtain ⟨run', hrun'_admissible, _hpoint, _hmultiplier, hstep, herror⟩ :=
    h_admissible.exists_pathwiseVersion run K
  have hstepMeanSquare (k : ℕ) :
      run'.stepMeanSquare k = run.stepMeanSquare k := by
    rw [run'.stepMeanSquare_def, run.stepMeanSquare_def]
    exact integral_congr_ae ((hstep k).fun_comp fun p ↦ ‖p‖ ^ 2)
  have herrorMeanSquare (k : ℕ) :
      run'.gradientErrorMeanSquare k = run.gradientErrorMeanSquare k := by
    rw [run'.gradientErrorMeanSquare_def, run.gradientErrorMeanSquare_def]
    exact integral_congr_ae ((herror k).fun_comp fun e ↦ ‖e‖ ^ 2)
  have hbound :=
    run'.averageGradientErrorMeanSquare_le_of_isAdmissiblePrefix K hK
      hrun'_admissible h_batch
  simpa only [hstepMeanSquare, herrorMeanSquare] using hbound

/-- Lemma 3.4 (6): on an almost-surely admissible prefix and under
`SPIDER.IsSufficientInnerBatchSize`, the average primal step mean square has the
stated variance and initial terms. -/
theorem averageStepMeanSquare_le
    (K : ℕ) (hK : 2 ≤ K) (h_admissible : run.IsAEAdmissiblePrefix K)
    (h_batch : SPIDER.IsSufficientInnerBatchSize h oracle params Q b) :
    (∑ k ∈ Finset.range K, run.stepMeanSquare k) / K ≤
      2 * errorStepConstant h params * oracle.noiseLevel ^ 2 / B +
        2 * initialStepBound h params / K := by
  obtain ⟨run', hrun'_admissible, _hpoint, _hmultiplier, hstep, herror⟩ :=
    h_admissible.exists_pathwiseVersion run K
  have hstepMeanSquare (k : ℕ) :
      run'.stepMeanSquare k = run.stepMeanSquare k := by
    rw [run'.stepMeanSquare_def, run.stepMeanSquare_def]
    exact integral_congr_ae ((hstep k).fun_comp fun p ↦ ‖p‖ ^ 2)
  have herrorMeanSquare (k : ℕ) :
      run'.gradientErrorMeanSquare k = run.gradientErrorMeanSquare k := by
    rw [run'.gradientErrorMeanSquare_def, run.gradientErrorMeanSquare_def]
    exact integral_congr_ae ((herror k).fun_comp fun e ↦ ‖e‖ ^ 2)
  have hbound := run'.averageStepMeanSquare_le_of_isAdmissiblePrefix K hK
    hrun'_admissible h_batch
  simpa only [hstepMeanSquare, herrorMeanSquare] using hbound

end LALM.StochasticRun

end
