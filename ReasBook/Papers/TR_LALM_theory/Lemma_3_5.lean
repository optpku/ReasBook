/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@5bf5af722d85bd5c98368c41c4066124a15e8fd3:ReasBook/Papers/TR_LALM_theory/README.md (formalization contributor).
-/

module

public import TR_LALM_theory.Definition_2_2.KKT
public import TR_LALM_theory.Lemma_3_3.Iteration
public import TR_LALM_theory.Lemma_3_5.Residual

public section

open MeasureTheory
open scoped InnerProductSpace NNReal

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
variable {params : Parameters h x₀ multiplier₀} {Q B b : ℕ+}

/-- Helper for Lemma 3.5: a damped normal equation inherits bounds from its
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

/-- Helper for Lemma 3.5: the derivative of the explicit-gradient step model
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

/-- Helper for Lemma 3.5: a minimizer of the explicit-gradient step model
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

/-- Helper for Lemma 3.5: the stochastic constraint linearization error is the
nonlinear increment minus its first-order prediction. -/
private noncomputable def linearizationError
    (run : StochasticRun h oracle ℙ x₀ multiplier₀ params Q B b)
    (k : ℕ) (ω : Ω) : EuclideanSpace ℝ (Fin m) :=
  c (run.point (k + 1) ω) - c (run.point k ω) -
    fderiv ℝ c (run.point k ω) (run.step k ω)

/-- Helper for Lemma 3.5: an admissible stochastic segment has quadratically
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

/-- Helper for Lemma 3.5: stochastic model optimality and the multiplier update
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

/-- Helper for Lemma 3.5: bounded stochastic multipliers control the effective
multiplier in one pathwise normal equation. -/
private lemma normEffectiveMultiplier_le
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

/-- Helper for Lemma 3.5: regularity, clipping, and an effective-multiplier
bound control one stochastic primal step. -/
private lemma normStep_le_of_normEffectiveMultiplier_le
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

/-- Helper for Lemma 3.5: an admissible bounded stochastic step propagates the
pathwise multiplier bound through one iteration. -/
private lemma normMultiplier_succ_le_of_normStep_le
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

/-- Helper for Lemma 3.5: stochastic prefix admissibility propagates pathwise
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

/-- Helper for Lemma 3.5: subtracting two stochastic perturbed-multiplier
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

/-- Helper for Lemma 3.5: on an admissible stochastic segment, a bounded step
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

/-- Helper for Lemma 3.5: the constraint-gradient image of a stochastic
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
  have hmultiplier := hbounds.2 k (show k ≤ N by omega) ω
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

/-- Helper for Lemma 3.5: the squared stochastic multiplier increment is
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

/-- Helper for Lemma 3.5: stochastic stationarity at the next iterate is
controlled by the current step and projected-gradient error. -/
private lemma normStationaritySucc_le
    (run : StochasticRun h oracle ℙ x₀ multiplier₀ params Q B b)
    {N k : ℕ} (h_admissible : run.IsAdmissiblePrefix N)
    (hk : k < N) (ω : Ω) :
    ‖KKT.stationarity f c (run.point (k + 1) ω) (run.multiplier (k + 1) ω)‖ ≤
      primalComparisonConstant h params.delta params.beta params.rho
          params.multiplierBound * ‖run.step k ω‖ +
        ‖run.gradientError k ω‖ := by
  -- Extract the segment endpoints and the simultaneous step/multiplier invariant.
  have hsegments := (run.isAdmissiblePrefix_iff N).1 h_admissible
  have hsegment := hsegments k hk ω
  have hxCurrent : run.point k ω ∈ h.region :=
    hsegment (left_mem_segment ℝ _ _)
  have hxNext : run.point (k + 1) ω ∈ h.region :=
    hsegment (right_mem_segment ℝ _ _)
  have hbounds := admissiblePrefixNormBounds run N h_admissible
  have hstep := hbounds.1 k hk ω
  have hmultiplier := hbounds.2 (k + 1) (show k + 1 ≤ N by omega) ω
  have herror := normScaledConstraintGradientError_le run k ω hsegment hstep
  -- Model optimality gives stationarity up to smooth variation and estimator error.
  have hstationarityIdentity :
      KKT.stationarity f c (run.point (k + 1) ω) (run.multiplier (k + 1) ω) =
        ((-(params.beta : ℝ) • run.step k ω +
            (params.rho : ℝ) • EqualityConstrained.constraintGradient c
              (run.point k ω) (linearizationError run k ω)) +
          (gradient f (run.point (k + 1) ω) - gradient f (run.point k ω)) +
          (EqualityConstrained.constraintGradient c (run.point (k + 1) ω) -
            EqualityConstrained.constraintGradient c (run.point k ω))
              (run.multiplier (k + 1) ω)) - run.gradientError k ω := by
    rw [KKT.stationarity_def, run.gradientError_apply]
    simp only [sub_apply]
    linear_combination (norm := module) perturbedMultiplierIdentity run k ω
  -- The point update turns both Lipschitz distances into the current step norm.
  have hpointDistance :
      dist (run.point (k + 1) ω) (run.point k ω) = ‖run.step k ω‖ := by
    rw [run.point_succ, dist_eq_norm, add_sub_cancel_left]
  have hgradientDifference :
      ‖gradient f (run.point (k + 1) ω) - gradient f (run.point k ω)‖ ≤
        h.gradientLipschitz * ‖run.step k ω‖ := by
    calc
      ‖gradient f (run.point (k + 1) ω) - gradient f (run.point k ω)‖ =
          dist (gradient f (run.point (k + 1) ω))
            (gradient f (run.point k ω)) := (dist_eq_norm _ _).symm
      _ ≤ h.gradientLipschitz *
          dist (run.point (k + 1) ω) (run.point k ω) :=
        h.lipschitzOn_gradient.dist_le_mul
          (run.point (k + 1) ω) hxNext (run.point k ω) hxCurrent
      _ = h.gradientLipschitz * ‖run.step k ω‖ := by rw [hpointDistance]
  have hoperatorDifference :
      ‖EqualityConstrained.constraintGradient c (run.point (k + 1) ω) -
          EqualityConstrained.constraintGradient c (run.point k ω)‖ ≤
        h.constraintGradientLipschitz * ‖run.step k ω‖ := by
    calc
      ‖EqualityConstrained.constraintGradient c (run.point (k + 1) ω) -
          EqualityConstrained.constraintGradient c (run.point k ω)‖ =
          dist (EqualityConstrained.constraintGradient c (run.point (k + 1) ω))
            (EqualityConstrained.constraintGradient c (run.point k ω)) :=
        (dist_eq_norm _ _).symm
      _ ≤ h.constraintGradientLipschitz *
          dist (run.point (k + 1) ω) (run.point k ω) :=
        h.lipschitzOn_constraintGradient.dist_le_mul
          (run.point (k + 1) ω) hxNext (run.point k ω) hxCurrent
      _ = h.constraintGradientLipschitz * ‖run.step k ω‖ := by
        rw [hpointDistance]
  have hoperatorApplied :
      ‖(EqualityConstrained.constraintGradient c (run.point (k + 1) ω) -
          EqualityConstrained.constraintGradient c (run.point k ω))
            (run.multiplier (k + 1) ω)‖ ≤
        h.constraintGradientLipschitz * params.multiplierBound *
          ‖run.step k ω‖ := by
    calc
      ‖(EqualityConstrained.constraintGradient c (run.point (k + 1) ω) -
          EqualityConstrained.constraintGradient c (run.point k ω))
            (run.multiplier (k + 1) ω)‖ ≤
          ‖EqualityConstrained.constraintGradient c (run.point (k + 1) ω) -
            EqualityConstrained.constraintGradient c (run.point k ω)‖ *
              ‖run.multiplier (k + 1) ω‖ :=
        (EqualityConstrained.constraintGradient c (run.point (k + 1) ω) -
          EqualityConstrained.constraintGradient c (run.point k ω)).le_opNorm
            (run.multiplier (k + 1) ω)
      _ ≤ (h.constraintGradientLipschitz * ‖run.step k ω‖) *
          params.multiplierBound :=
        mul_le_mul hoperatorDifference hmultiplier (norm_nonneg _)
          (mul_nonneg (NNReal.coe_nonneg _) (norm_nonneg _))
      _ = h.constraintGradientLipschitz * params.multiplierBound *
          ‖run.step k ω‖ := by ring
  have hβ : 0 < (params.beta : ℝ) := params.spec.1.2.1
  have hproximalError :
      ‖-(params.beta : ℝ) • run.step k ω +
          (params.rho : ℝ) • EqualityConstrained.constraintGradient c
            (run.point k ω) (linearizationError run k ω)‖ ≤
        primalConstant h params.delta params.beta params.rho *
          ‖run.step k ω‖ := by
    calc
      ‖-(params.beta : ℝ) • run.step k ω +
          (params.rho : ℝ) • EqualityConstrained.constraintGradient c
            (run.point k ω) (linearizationError run k ω)‖ ≤
          ‖-(params.beta : ℝ) • run.step k ω‖ +
            ‖(params.rho : ℝ) • EqualityConstrained.constraintGradient c
              (run.point k ω) (linearizationError run k ω)‖ := norm_add_le _ _
      _ = params.beta * ‖run.step k ω‖ +
          ‖(params.rho : ℝ) • EqualityConstrained.constraintGradient c
            (run.point k ω) (linearizationError run k ω)‖ := by
        rw [norm_smul, Real.norm_eq_abs, abs_neg, abs_of_pos hβ]
      _ ≤ params.beta * ‖run.step k ω‖ +
          params.rho * h.constraintGradientBound * linearizationConstant h *
            params.delta * ‖run.step k ω‖ := add_le_add_right herror _
      _ = primalConstant h params.delta params.beta params.rho *
          ‖run.step k ω‖ := by
        rw [primalConstant_def]
        ring
  -- Collect the three deterministic terms, then add the estimator error once.
  have hdeterministic :
      ‖(-(params.beta : ℝ) • run.step k ω +
          (params.rho : ℝ) • EqualityConstrained.constraintGradient c
            (run.point k ω) (linearizationError run k ω)) +
        (gradient f (run.point (k + 1) ω) - gradient f (run.point k ω)) +
        (EqualityConstrained.constraintGradient c (run.point (k + 1) ω) -
          EqualityConstrained.constraintGradient c (run.point k ω))
            (run.multiplier (k + 1) ω)‖ ≤
        primalComparisonConstant h params.delta params.beta params.rho
          params.multiplierBound * ‖run.step k ω‖ := by
    calc
      ‖(-(params.beta : ℝ) • run.step k ω +
          (params.rho : ℝ) • EqualityConstrained.constraintGradient c
            (run.point k ω) (linearizationError run k ω)) +
        (gradient f (run.point (k + 1) ω) - gradient f (run.point k ω)) +
        (EqualityConstrained.constraintGradient c (run.point (k + 1) ω) -
          EqualityConstrained.constraintGradient c (run.point k ω))
            (run.multiplier (k + 1) ω)‖ ≤
          ‖-(params.beta : ℝ) • run.step k ω +
            (params.rho : ℝ) • EqualityConstrained.constraintGradient c
              (run.point k ω) (linearizationError run k ω)‖ +
          ‖gradient f (run.point (k + 1) ω) - gradient f (run.point k ω)‖ +
          ‖(EqualityConstrained.constraintGradient c (run.point (k + 1) ω) -
            EqualityConstrained.constraintGradient c (run.point k ω))
              (run.multiplier (k + 1) ω)‖ := by
        have hfirst := norm_add_le
          (-(params.beta : ℝ) • run.step k ω +
            (params.rho : ℝ) • EqualityConstrained.constraintGradient c
              (run.point k ω) (linearizationError run k ω))
          (gradient f (run.point (k + 1) ω) - gradient f (run.point k ω))
        have hsecond := norm_add_le
          ((-(params.beta : ℝ) • run.step k ω +
              (params.rho : ℝ) • EqualityConstrained.constraintGradient c
                (run.point k ω) (linearizationError run k ω)) +
            (gradient f (run.point (k + 1) ω) - gradient f (run.point k ω)))
          ((EqualityConstrained.constraintGradient c (run.point (k + 1) ω) -
            EqualityConstrained.constraintGradient c (run.point k ω))
              (run.multiplier (k + 1) ω))
        linarith
      _ ≤ primalConstant h params.delta params.beta params.rho *
          ‖run.step k ω‖ + h.gradientLipschitz * ‖run.step k ω‖ +
          h.constraintGradientLipschitz * params.multiplierBound *
            ‖run.step k ω‖ :=
        add_le_add (add_le_add hproximalError hgradientDifference) hoperatorApplied
      _ = primalComparisonConstant h params.delta params.beta params.rho
          params.multiplierBound * ‖run.step k ω‖ := by
        rw [primalComparisonConstant_def]
        ring
  rw [hstationarityIdentity]
  calc
    ‖((-(params.beta : ℝ) • run.step k ω +
          (params.rho : ℝ) • EqualityConstrained.constraintGradient c
            (run.point k ω) (linearizationError run k ω)) +
        (gradient f (run.point (k + 1) ω) - gradient f (run.point k ω)) +
        (EqualityConstrained.constraintGradient c (run.point (k + 1) ω) -
          EqualityConstrained.constraintGradient c (run.point k ω))
            (run.multiplier (k + 1) ω)) - run.gradientError k ω‖ ≤
        ‖(-(params.beta : ℝ) • run.step k ω +
            (params.rho : ℝ) • EqualityConstrained.constraintGradient c
              (run.point k ω) (linearizationError run k ω)) +
          (gradient f (run.point (k + 1) ω) - gradient f (run.point k ω)) +
          (EqualityConstrained.constraintGradient c (run.point (k + 1) ω) -
            EqualityConstrained.constraintGradient c (run.point k ω))
              (run.multiplier (k + 1) ω)‖ + ‖run.gradientError k ω‖ :=
      norm_sub_le _ _
    _ ≤ primalComparisonConstant h params.delta params.beta params.rho
        params.multiplierBound * ‖run.step k ω‖ + ‖run.gradientError k ω‖ :=
      add_le_add hdeterministic (le_refl _)

/-- Helper for Lemma 3.5: the multiplier update identifies squared feasibility
with the penalty-scaled squared multiplier increment. -/
private lemma constraintNormSq_eq_multiplierIncrementNormSqDiv
    (run : StochasticRun h oracle ℙ x₀ multiplier₀ params Q B b)
    (k : ℕ) (ω : Ω) :
    ‖c (run.point (k + 1) ω)‖ ^ 2 =
      ‖run.multiplier (k + 1) ω - run.multiplier k ω‖ ^ 2 /
        (params.rho : ℝ) ^ 2 := by
  -- Normalize the update with an explicit real scalar, then cancel its positive square.
  have hρ : 0 < (params.rho : ℝ) := params.spec.1.2.2.1
  have hupdate :
      run.multiplier (k + 1) ω = run.multiplier k ω +
        (params.rho : ℝ) • c (run.point (k + 1) ω) :=
    run.multiplier_succ k ω
  rw [hupdate, add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_pos hρ]
  field_simp [hρ.ne']

/-- Pointwise form of Lemma 3.5: on every stochastic admissible prefix, the
squared KKT residual at iteration `k + 1` is bounded by the current and
preceding squared step and gradient-error norms. -/
theorem residual_sq_le_of_isAdmissiblePrefix
    (run : StochasticRun h oracle ℙ x₀ multiplier₀ params Q B b)
    {N k : ℕ} (h_admissible : run.IsAdmissiblePrefix N)
    (hk_pos : 1 ≤ k) (hk : k < N) (ω : Ω) :
    KKT.residual f c (run.point (k + 1) ω) (run.multiplier (k + 1) ω) ^ 2 ≤
      stochasticResidualConstant h params.delta params.beta params.rho
          params.multiplierBound *
        (‖run.step k ω‖ ^ 2 + ‖run.step (k - 1) ω‖ ^ 2 +
          ‖run.gradientError k ω‖ ^ 2 + ‖run.gradientError (k - 1) ω‖ ^ 2) := by
  -- Square the stochastic stationarity estimate and separate step and error terms.
  have hstationarity := normStationaritySucc_le run h_admissible hk ω
  have hcomparisonNonneg :
      0 ≤ primalComparisonConstant h params.delta params.beta params.rho
        params.multiplierBound := by
    rw [primalComparisonConstant_def, primalConstant_def]
    positivity
  have hstationarityRightNonneg :
      0 ≤ primalComparisonConstant h params.delta params.beta params.rho
          params.multiplierBound * ‖run.step k ω‖ +
        ‖run.gradientError k ω‖ := by
    exact add_nonneg
      (mul_nonneg hcomparisonNonneg (norm_nonneg _)) (norm_nonneg _)
  have hstationaritySquared :
      ‖KKT.stationarity f c (run.point (k + 1) ω)
          (run.multiplier (k + 1) ω)‖ ^ 2 ≤
        (primalComparisonConstant h params.delta params.beta params.rho
            params.multiplierBound * ‖run.step k ω‖ +
          ‖run.gradientError k ω‖) ^ 2 :=
    (sq_le_sq₀ (norm_nonneg _) hstationarityRightNonneg).2 hstationarity
  have hstationaritySquare :
      ‖KKT.stationarity f c (run.point (k + 1) ω)
          (run.multiplier (k + 1) ω)‖ ^ 2 ≤
        2 * primalComparisonConstant h params.delta params.beta params.rho
            params.multiplierBound ^ 2 * ‖run.step k ω‖ ^ 2 +
          2 * ‖run.gradientError k ω‖ ^ 2 := by
    calc
      ‖KKT.stationarity f c (run.point (k + 1) ω)
          (run.multiplier (k + 1) ω)‖ ^ 2 ≤
          (primalComparisonConstant h params.delta params.beta params.rho
              params.multiplierBound * ‖run.step k ω‖ +
            ‖run.gradientError k ω‖) ^ 2 := hstationaritySquared
      _ ≤ 2 *
          (primalComparisonConstant h params.delta params.beta params.rho
              params.multiplierBound * ‖run.step k ω‖) ^ 2 +
            2 * ‖run.gradientError k ω‖ ^ 2 := by
        nlinarith [sq_nonneg
          (primalComparisonConstant h params.delta params.beta params.rho
              params.multiplierBound * ‖run.step k ω‖ -
            ‖run.gradientError k ω‖)]
      _ = 2 * primalComparisonConstant h params.delta params.beta params.rho
          params.multiplierBound ^ 2 * ‖run.step k ω‖ ^ 2 +
        2 * ‖run.gradientError k ω‖ ^ 2 := by ring
  have htwo : (0 : ℝ) ≤ 2 := by norm_num
  have hstationarityExpanded :
      ‖KKT.stationarity f c (run.point (k + 1) ω)
          (run.multiplier (k + 1) ω)‖ ^ 2 ≤
        2 * primalComparisonConstant h params.delta params.beta params.rho
            params.multiplierBound ^ 2 *
          (‖run.step k ω‖ ^ 2 + ‖run.step (k - 1) ω‖ ^ 2) +
        2 * (‖run.gradientError k ω‖ ^ 2 +
          ‖run.gradientError (k - 1) ω‖ ^ 2) := by
    calc
      ‖KKT.stationarity f c (run.point (k + 1) ω)
          (run.multiplier (k + 1) ω)‖ ^ 2 ≤
          2 * primalComparisonConstant h params.delta params.beta params.rho
              params.multiplierBound ^ 2 * ‖run.step k ω‖ ^ 2 +
            2 * ‖run.gradientError k ω‖ ^ 2 := hstationaritySquare
      _ ≤ 2 * primalComparisonConstant h params.delta params.beta params.rho
              params.multiplierBound ^ 2 *
            (‖run.step k ω‖ ^ 2 + ‖run.step (k - 1) ω‖ ^ 2) +
          2 * (‖run.gradientError k ω‖ ^ 2 +
            ‖run.gradientError (k - 1) ω‖ ^ 2) := by
        have hstepCoefficientNonneg :
            0 ≤ 2 * primalComparisonConstant h params.delta params.beta params.rho
              params.multiplierBound ^ 2 :=
          mul_nonneg htwo (sq_nonneg _)
        exact add_le_add
          (mul_le_mul_of_nonneg_left
            (le_add_of_nonneg_right (sq_nonneg _)) hstepCoefficientNonneg)
          (mul_le_mul_of_nonneg_left
            (le_add_of_nonneg_right (sq_nonneg _)) htwo)
  -- The multiplier update transports the earlier increment estimate to feasibility.
  have hmultiplier :=
    normMultiplierIncrementSq_le run h_admissible hk_pos hk ω
  have hfeasibility :
      ‖c (run.point (k + 1) ω)‖ ^ 2 ≤
        multiplierPrimalConstant h params.delta params.beta params.rho
            params.multiplierBound / (params.rho : ℝ) ^ 2 *
          (‖run.step k ω‖ ^ 2 + ‖run.step (k - 1) ω‖ ^ 2) +
        multiplierErrorConstant h / (params.rho : ℝ) ^ 2 *
          (‖run.gradientError k ω‖ ^ 2 +
            ‖run.gradientError (k - 1) ω‖ ^ 2) := by
    calc
      ‖c (run.point (k + 1) ω)‖ ^ 2 =
          ‖run.multiplier (k + 1) ω - run.multiplier k ω‖ ^ 2 /
            (params.rho : ℝ) ^ 2 :=
        constraintNormSq_eq_multiplierIncrementNormSqDiv run k ω
      _ ≤ (multiplierPrimalConstant h params.delta params.beta params.rho
              params.multiplierBound *
            (‖run.step k ω‖ ^ 2 + ‖run.step (k - 1) ω‖ ^ 2) +
          multiplierErrorConstant h *
            (‖run.gradientError k ω‖ ^ 2 +
              ‖run.gradientError (k - 1) ω‖ ^ 2)) /
            (params.rho : ℝ) ^ 2 :=
        div_le_div_of_nonneg_right hmultiplier (sq_nonneg _)
      _ = multiplierPrimalConstant h params.delta params.beta params.rho
              params.multiplierBound / (params.rho : ℝ) ^ 2 *
            (‖run.step k ω‖ ^ 2 + ‖run.step (k - 1) ω‖ ^ 2) +
          multiplierErrorConstant h / (params.rho : ℝ) ^ 2 *
            (‖run.gradientError k ω‖ ^ 2 +
              ‖run.gradientError (k - 1) ω‖ ^ 2) := by ring
  -- Each grouped coefficient is dominated by the defining residual maximum.
  have hprimalCoefficient :
      2 * primalComparisonConstant h params.delta params.beta params.rho
            params.multiplierBound ^ 2 +
          multiplierPrimalConstant h params.delta params.beta params.rho
            params.multiplierBound / (params.rho : ℝ) ^ 2 ≤
        stochasticResidualConstant h params.delta params.beta params.rho
          params.multiplierBound := by
    rw [stochasticResidualConstant_def]
    exact le_max_left _ _
  have herrorCoefficient :
      2 + multiplierErrorConstant h / (params.rho : ℝ) ^ 2 ≤
        stochasticResidualConstant h params.delta params.beta params.rho
          params.multiplierBound := by
    rw [stochasticResidualConstant_def]
    exact le_max_right _ _
  have hstepSumNonneg :
      0 ≤ ‖run.step k ω‖ ^ 2 + ‖run.step (k - 1) ω‖ ^ 2 :=
    add_nonneg (sq_nonneg _) (sq_nonneg _)
  have herrorSumNonneg :
      0 ≤ ‖run.gradientError k ω‖ ^ 2 +
        ‖run.gradientError (k - 1) ω‖ ^ 2 :=
    add_nonneg (sq_nonneg _) (sq_nonneg _)
  calc
    KKT.residual f c (run.point (k + 1) ω) (run.multiplier (k + 1) ω) ^ 2 =
        ‖KKT.stationarity f c (run.point (k + 1) ω)
            (run.multiplier (k + 1) ω)‖ ^ 2 +
          ‖c (run.point (k + 1) ω)‖ ^ 2 := by
      rw [KKT.residual_def,
        Real.sq_sqrt (add_nonneg (sq_nonneg _) (sq_nonneg _))]
    _ ≤ (2 * primalComparisonConstant h params.delta params.beta params.rho
              params.multiplierBound ^ 2 +
            multiplierPrimalConstant h params.delta params.beta params.rho
              params.multiplierBound / (params.rho : ℝ) ^ 2) *
          (‖run.step k ω‖ ^ 2 + ‖run.step (k - 1) ω‖ ^ 2) +
        (2 + multiplierErrorConstant h / (params.rho : ℝ) ^ 2) *
          (‖run.gradientError k ω‖ ^ 2 +
            ‖run.gradientError (k - 1) ω‖ ^ 2) := by
      calc
        ‖KKT.stationarity f c (run.point (k + 1) ω)
            (run.multiplier (k + 1) ω)‖ ^ 2 +
            ‖c (run.point (k + 1) ω)‖ ^ 2 ≤
            (2 * primalComparisonConstant h params.delta params.beta params.rho
                params.multiplierBound ^ 2 *
              (‖run.step k ω‖ ^ 2 + ‖run.step (k - 1) ω‖ ^ 2) +
            2 * (‖run.gradientError k ω‖ ^ 2 +
              ‖run.gradientError (k - 1) ω‖ ^ 2)) +
            (multiplierPrimalConstant h params.delta params.beta params.rho
                params.multiplierBound / (params.rho : ℝ) ^ 2 *
              (‖run.step k ω‖ ^ 2 + ‖run.step (k - 1) ω‖ ^ 2) +
            multiplierErrorConstant h / (params.rho : ℝ) ^ 2 *
              (‖run.gradientError k ω‖ ^ 2 +
                ‖run.gradientError (k - 1) ω‖ ^ 2)) :=
          add_le_add hstationarityExpanded hfeasibility
        _ = (2 * primalComparisonConstant h params.delta params.beta params.rho
                params.multiplierBound ^ 2 +
              multiplierPrimalConstant h params.delta params.beta params.rho
                params.multiplierBound / (params.rho : ℝ) ^ 2) *
            (‖run.step k ω‖ ^ 2 + ‖run.step (k - 1) ω‖ ^ 2) +
          (2 + multiplierErrorConstant h / (params.rho : ℝ) ^ 2) *
            (‖run.gradientError k ω‖ ^ 2 +
              ‖run.gradientError (k - 1) ω‖ ^ 2) := by ring
    _ ≤ stochasticResidualConstant h params.delta params.beta params.rho
          params.multiplierBound *
        (‖run.step k ω‖ ^ 2 + ‖run.step (k - 1) ω‖ ^ 2) +
      stochasticResidualConstant h params.delta params.beta params.rho
          params.multiplierBound *
        (‖run.gradientError k ω‖ ^ 2 +
          ‖run.gradientError (k - 1) ω‖ ^ 2) :=
      add_le_add
        (mul_le_mul_of_nonneg_right hprimalCoefficient hstepSumNonneg)
        (mul_le_mul_of_nonneg_right herrorCoefficient herrorSumNonneg)
    _ = stochasticResidualConstant h params.delta params.beta params.rho
          params.multiplierBound *
        (‖run.step k ω‖ ^ 2 + ‖run.step (k - 1) ω‖ ^ 2 +
          ‖run.gradientError k ω‖ ^ 2 +
            ‖run.gradientError (k - 1) ω‖ ^ 2) := by ring

/-- Lemma 3.5: on an almost-surely admissible stochastic prefix, the squared
KKT residual at iteration `k + 1` obeys the stated pathwise bound almost
surely. -/
theorem residual_sq_le
    (run : StochasticRun h oracle ℙ x₀ multiplier₀ params Q B b)
    {N k : ℕ} (h_admissible : run.IsAEAdmissiblePrefix N)
    (hk_pos : 1 ≤ k) (hk : k < N) :
    ∀ᵐ ω ∂ℙ,
      KKT.residual f c (run.point (k + 1) ω) (run.multiplier (k + 1) ω) ^ 2 ≤
        stochasticResidualConstant h params.delta params.beta params.rho
            params.multiplierBound *
          (‖run.step k ω‖ ^ 2 + ‖run.step (k - 1) ω‖ ^ 2 +
            ‖run.gradientError k ω‖ ^ 2 +
              ‖run.gradientError (k - 1) ω‖ ^ 2) := by
  obtain ⟨run', hrun'_admissible, hpoint, hmultiplier, hstep, herror⟩ :=
    h_admissible.exists_pathwiseVersion run N
  filter_upwards [hpoint (k + 1), hmultiplier (k + 1), hstep k,
    hstep (k - 1), herror k, herror (k - 1)] with ω hpointSucc
      hmultiplierSucc hstepCurrent hstepPrevious herrorCurrent herrorPrevious
  have hbound := run'.residual_sq_le_of_isAdmissiblePrefix hrun'_admissible
    hk_pos hk ω
  simpa only [hpointSucc, hmultiplierSucc, hstepCurrent, hstepPrevious,
    herrorCurrent, herrorPrevious] using hbound

end LALM.StochasticRun

end
