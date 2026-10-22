/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@5bf5af722d85bd5c98368c41c4066124a15e8fd3:ReasBook/Papers/TR_LALM_theory/README.md (formalization contributor).
-/

module

import TR_LALM_theory.Lemma_2_6
public import TR_LALM_theory.Assumption_2_5.Region
public import TR_LALM_theory.Theorem_2_9
public import TR_LALM_theory.Theorem_2_10.Admissibility
public import TR_LALM_theory.Theorem_2_10.Uniqueness

public section

open scoped InnerProductSpace LALM NNReal

namespace LALM.Run

variable {n m : ℕ}
variable {f : EuclideanSpace ℝ (Fin n) → ℝ}
variable {c : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m)}
variable {ρ β : ℝ}
variable {x₀ : EuclideanSpace ℝ (Fin n)}
variable {multiplier₀ : EuclideanSpace ℝ (Fin m)}

/-- The structural uniqueness conclusion of Theorem 2.10: a fixed-penalty NR-LALM
run with the specified initial data is unique. This fact does not require the
later regularity assumptions. -/
theorem unique (run₁ run₂ : Run f c ρ β x₀ multiplier₀) : run₁ = run₂ :=
  eq run₁ run₂

/-- Helper for Theorem 2.10: the linear part of the step-model gradient is a
positive-definite endomorphism when the algorithmic coefficients are positive. -/
private noncomputable def deterministicModelOperator
    (c : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m))
    (rho beta : ℝ) (x : EuclideanSpace ℝ (Fin n)) :
    EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) :=
  beta • ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n)) +
    rho • (EqualityConstrained.constraintGradient c x).comp (fderiv ℝ c x)

/-- Helper for Theorem 2.10: positivity of the proximal coefficient makes the
deterministic model operator continuously invertible. -/
private lemma deterministicModelOperator_isInvertible
    (c : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m))
    (rho beta : ℝ) (x : EuclideanSpace ℝ (Fin n))
    (hrho : 0 < rho) (hbeta : 0 < beta) :
    (deterministicModelOperator c rho beta x).IsInvertible := by
  have hinjective : Function.Injective (deterministicModelOperator c rho beta x) := by
    intro p q hpq
    let v : EuclideanSpace ℝ (Fin n) := p - q
    have hvKernel : deterministicModelOperator c rho beta x v = 0 := by
      dsimp only [v]
      rw [map_sub, hpq, sub_self]
    have hpair :
        inner ℝ (deterministicModelOperator c rho beta x v) v =
          beta * ‖v‖ ^ 2 + rho * ‖fderiv ℝ c x v‖ ^ 2 := by
      simp only [deterministicModelOperator, add_apply, smul_apply,
        ContinuousLinearMap.id_apply, ContinuousLinearMap.comp_apply,
        EqualityConstrained.constraintGradient_def]
      rw [inner_add_left, real_inner_smul_left, real_inner_smul_left,
        ContinuousLinearMap.adjoint_inner_left,
        real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq]
    have hsum : beta * ‖v‖ ^ 2 + rho * ‖fderiv ℝ c x v‖ ^ 2 = 0 := by
      rw [← hpair, hvKernel, inner_zero_left]
    have hfirstNonnegative : 0 ≤ beta * ‖v‖ ^ 2 :=
      mul_nonneg hbeta.le (sq_nonneg _)
    have hsecondNonnegative : 0 ≤ rho * ‖fderiv ℝ c x v‖ ^ 2 :=
      mul_nonneg hrho.le (sq_nonneg _)
    have hfirst : beta * ‖v‖ ^ 2 = 0 := by
      linarith
    have hvNorm : ‖v‖ = 0 :=
      sq_eq_zero_iff.mp ((mul_eq_zero.mp hfirst).resolve_left hbeta.ne')
    exact sub_eq_zero.mp (norm_eq_zero.mp hvNorm)
  have hsurjective : Function.Surjective
      (deterministicModelOperator c rho beta x).toLinearMap :=
    LinearMap.surjective_of_injective hinjective
  let modelEquiv : EuclideanSpace ℝ (Fin n) ≃ₗ[ℝ]
      EuclideanSpace ℝ (Fin n) :=
    LinearEquiv.ofBijective (deterministicModelOperator c rho beta x).toLinearMap
      ⟨hinjective, hsurjective⟩
  refine ⟨modelEquiv.toContinuousLinearEquiv, ?_⟩
  ext p
  rfl

/-- Helper for Theorem 2.10: the canonical deterministic step solves the
positive-definite first-order equation of the quadratic model. -/
private noncomputable def canonicalDeterministicStep
    (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (c : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m))
    (rho beta : ℝ) (x : EuclideanSpace ℝ (Fin n))
    (multiplier : EuclideanSpace ℝ (Fin m)) : EuclideanSpace ℝ (Fin n) :=
  (deterministicModelOperator c rho beta x).inverse
    (-(gradient f x + EqualityConstrained.constraintGradient c x
      (multiplier + rho • c x)))

/-- Helper for Theorem 2.10: the canonical deterministic step satisfies the
explicit first-order stationarity equation. -/
private lemma canonicalDeterministicStep_stationarity
    (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (c : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m))
    (rho beta : ℝ) (x : EuclideanSpace ℝ (Fin n))
    (multiplier : EuclideanSpace ℝ (Fin m))
    (hrho : 0 < rho) (hbeta : 0 < beta) :
    gradient f x + EqualityConstrained.constraintGradient c x
        (multiplier + rho •
          (c x + fderiv ℝ c x
            (canonicalDeterministicStep f c rho beta x multiplier))) +
      beta • canonicalDeterministicStep f c rho beta x multiplier = 0 := by
  let p := canonicalDeterministicStep f c rho beta x multiplier
  have hoperator : deterministicModelOperator c rho beta x p =
      -(gradient f x + EqualityConstrained.constraintGradient c x
        (multiplier + rho • c x)) := by
    have hinverse :=
      ((deterministicModelOperator_isInvertible c rho beta x hrho hbeta).inverse_apply_eq).1
        (rfl : p = p)
    exact hinverse.symm
  simp only [deterministicModelOperator, add_apply, smul_apply,
    ContinuousLinearMap.id_apply, ContinuousLinearMap.comp_apply, map_add,
    map_smul] at hoperator ⊢
  linear_combination (norm := module) hoperator

/-- Helper for Theorem 2.10: at a stationary step, the quadratic model increase
is the sum of its penalty and proximal quadratic forms. -/
private lemma stepModel_sub_stepModel_eq_of_gradient_eq_zero
    (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (c : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m))
    (rho beta : ℝ) (x : EuclideanSpace ℝ (Fin n))
    (multiplier : EuclideanSpace ℝ (Fin m))
    (p q : EuclideanSpace ℝ (Fin n))
    (hstationary : gradient f x + EqualityConstrained.constraintGradient c x
        (multiplier + rho • (c x + fderiv ℝ c x p)) + beta • p = 0) :
    stepModel f c rho beta x multiplier q -
        stepModel f c rho beta x multiplier p =
      (rho / 2) * ‖fderiv ℝ c x (q - p)‖ ^ 2 +
        (beta / 2) * ‖q - p‖ ^ 2 := by
  have hq : q = p + (q - p) := by module
  have hconstraint :
      c x + fderiv ℝ c x q =
        (c x + fderiv ℝ c x p) + fderiv ℝ c x (q - p) := by
    rw [hq, map_add]
    simp only [add_sub_cancel_left]
    abel
  have hobjective :
      ⟪gradient f x, q⟫_ℝ =
        ⟪gradient f x, p⟫_ℝ + ⟪gradient f x, q - p⟫_ℝ := by
    rw [hq, inner_add_right]
    simp only [add_sub_cancel_left]
  have hmultiplier :
      ⟪multiplier, c x + fderiv ℝ c x q⟫_ℝ =
        ⟪multiplier, c x + fderiv ℝ c x p⟫_ℝ +
          ⟪multiplier, fderiv ℝ c x (q - p)⟫_ℝ := by
    rw [hconstraint, inner_add_right]
  have hpenalty :
      ‖c x + fderiv ℝ c x q‖ ^ 2 =
        ‖c x + fderiv ℝ c x p‖ ^ 2 +
          2 * ⟪c x + fderiv ℝ c x p, fderiv ℝ c x (q - p)⟫_ℝ +
            ‖fderiv ℝ c x (q - p)‖ ^ 2 := by
    rw [hconstraint, norm_add_sq_real]
  have hproximal :
      ‖q‖ ^ 2 = ‖p‖ ^ 2 + 2 * ⟪p, q - p⟫_ℝ + ‖q - p‖ ^ 2 := by
    rw [hq, norm_add_sq_real]
    simp only [add_sub_cancel_left]
  have hstationaryInner := congrArg (fun v ↦ ⟪v, q - p⟫_ℝ) hstationary
  simp only [inner_add_left, inner_smul_left,
    EqualityConstrained.constraintGradient_def,
    ContinuousLinearMap.adjoint_inner_left, inner_zero_left,
    starRingEnd_apply, star_trivial] at hstationaryInner
  rw [stepModel_def, stepModel_def, hobjective, hmultiplier, hpenalty, hproximal,
    inner_add_left]
  linear_combination hstationaryInner

/-- Helper for Theorem 2.10: the canonical deterministic step globally
minimizes its quadratic model. -/
private lemma canonicalDeterministicStep_minimizes
    (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (c : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m))
    (rho beta : ℝ) (x : EuclideanSpace ℝ (Fin n))
    (multiplier : EuclideanSpace ℝ (Fin m))
    (hrho : 0 < rho) (hbeta : 0 < beta) :
    IsMinOn (stepModel f c rho beta x multiplier) Set.univ
      (canonicalDeterministicStep f c rho beta x multiplier) := by
  intro q hq
  have hdifference := stepModel_sub_stepModel_eq_of_gradient_eq_zero f c rho beta x
    multiplier (canonicalDeterministicStep f c rho beta x multiplier) q
    (canonicalDeterministicStep_stationarity f c rho beta x multiplier hrho hbeta)
  have hpenalty : 0 ≤ (rho / 2) *
      ‖fderiv ℝ c x (q - canonicalDeterministicStep f c rho beta x multiplier)‖ ^ 2 :=
    mul_nonneg (div_nonneg hrho.le (by norm_num)) (sq_nonneg _)
  have hproximal : 0 ≤ (beta / 2) *
      ‖q - canonicalDeterministicStep f c rho beta x multiplier‖ ^ 2 :=
    mul_nonneg (div_nonneg hbeta.le (by norm_num)) (sq_nonneg _)
  have hdifferenceNonnegative : 0 ≤
      stepModel f c rho beta x multiplier q -
        stepModel f c rho beta x multiplier
          (canonicalDeterministicStep f c rho beta x multiplier) := by
    rw [hdifference]
    exact add_nonneg hpenalty hproximal
  exact sub_nonneg.mp hdifferenceNonnegative

/-- The positive-penalty quadratic NR-LALM step model has exactly one global
minimizer. -/
theorem existsUniqueStepModelMinimizer
    (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (c : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m))
    (rho beta : ℝ) (x : EuclideanSpace ℝ (Fin n))
    (multiplier : EuclideanSpace ℝ (Fin m))
    (hrho : 0 < rho) (hbeta : 0 < beta) :
    ∃! p : EuclideanSpace ℝ (Fin n),
      IsMinOn (stepModel f c rho beta x multiplier) Set.univ p := by
  let p := canonicalDeterministicStep f c rho beta x multiplier
  have hp : IsMinOn (stepModel f c rho beta x multiplier) Set.univ p :=
    canonicalDeterministicStep_minimizes f c rho beta x multiplier hrho hbeta
  refine ⟨p, hp, ?_⟩
  intro q hq
  have hqzero := stepModelGradient_eq_zero_of_minimizes
    f c rho beta x multiplier q hq
  have hpzero := stepModelGradient_eq_zero_of_minimizes
    f c rho beta x multiplier p hp
  have hpair := stepModelGradientPairing f c rho beta x multiplier q p
  rw [hqzero, hpzero, sub_self, inner_zero_left] at hpair
  have hpenaltyNonnegative :
      0 ≤ rho * ‖fderiv ℝ c x (q - p)‖ ^ 2 :=
    mul_nonneg hrho.le (sq_nonneg _)
  have hproximalZero : beta * ‖q - p‖ ^ 2 = 0 := by
    nlinarith
  have hstepNormSq : ‖q - p‖ ^ 2 = 0 :=
    (mul_eq_zero.mp hproximalZero).resolve_left hbeta.ne'
  exact sub_eq_zero.mp (norm_eq_zero.mp (sq_eq_zero_iff.mp hstepNormSq))

/-- Helper for Theorem 2.10: one deterministic state transition applies the
canonical minimizing step and then the primal and multiplier updates. -/
private noncomputable def canonicalDeterministicTransition
    (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (c : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m))
    (rho beta : ℝ)
    (state : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin m)) :
    EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin m) :=
  let step := canonicalDeterministicStep f c rho beta state.1 state.2
  let nextPoint := state.1 + step
  (nextPoint, state.2 + rho • c nextPoint)

/-- Theorem 2.10 (1), existence: admissible positive parameters determine at
least one infinite deterministic NR-LALM run from the prescribed initial data. -/
theorem nonempty_of_parameters
    (h : EqualityConstrained.Regularity f c)
    (params : Parameters h x₀ multiplier₀) :
    Nonempty (Run f c params.rho params.beta x₀ multiplier₀) := by
  let transition := canonicalDeterministicTransition f c
    (params.rho : ℝ) (params.beta : ℝ)
  let state : ℕ → EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin m) :=
    fun k ↦ transition^[k] (x₀, multiplier₀)
  let point : ℕ → EuclideanSpace ℝ (Fin n) := fun k ↦ (state k).1
  let multiplier : ℕ → EuclideanSpace ℝ (Fin m) := fun k ↦ (state k).2
  let step : ℕ → EuclideanSpace ℝ (Fin n) := fun k ↦
    canonicalDeterministicStep f c params.rho params.beta (point k) (multiplier k)
  have hstateZero : state 0 = (x₀, multiplier₀) := by
    simp only [state, Function.iterate_zero_apply]
  have hstateSucc (k : ℕ) : state (k + 1) = transition (state k) := by
    simp only [state, Function.iterate_succ_apply']
  refine ⟨Run.ofSequences f c params.rho params.beta x₀ multiplier₀
    params.spec.1.2.2.1 params.spec.1.2.1 point multiplier step ?_ ?_ ?_ ?_ ?_⟩
  · simpa only [point] using congrArg Prod.fst hstateZero
  · simpa only [multiplier] using congrArg Prod.snd hstateZero
  · intro k
    simpa only [step] using canonicalDeterministicStep_minimizes f c
      (params.rho : ℝ) (params.beta : ℝ) (point k) (multiplier k)
      params.spec.1.2.2.1 params.spec.1.2.1
  · intro k
    have hnext := congrArg Prod.fst (hstateSucc k)
    simpa only [point, step, transition, canonicalDeterministicTransition] using hnext
  · intro k
    have hnext := congrArg Prod.snd (hstateSucc k)
    have hpointNext := congrArg Prod.fst (hstateSucc k)
    simp only [transition, canonicalDeterministicTransition] at hnext hpointNext
    rw [← hpointNext] at hnext
    simpa only [point, multiplier] using hnext

/-- Theorem 2.10 (1): for admissible parameters and fixed initial data, there
exists exactly one infinite deterministic NR-LALM run. -/
theorem existsUnique
    (h : EqualityConstrained.Regularity f c)
    (params : Parameters h x₀ multiplier₀) :
    ∃! run : Run f c params.rho params.beta x₀ multiplier₀,
      run.point 0 = x₀ := by
  obtain ⟨run⟩ := nonempty_of_parameters h params
  refine ⟨run, run.point_zero, ?_⟩
  intro other hother
  exact unique other run

section

variable (h : EqualityConstrained.Regularity f c)
variable (params : Parameters h x₀ multiplier₀)
variable (h_region : DeterministicRegionCondition h params)
variable (run : Run f c params.rho params.beta x₀ multiplier₀)

/-- Helper for Theorem 2.10: a damped normal equation inherits bounds from its
primal and dual coercivity moduli. -/
theorem normDampedNormalEquation_le
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
  -- Normalize the dual energy before applying the coercivity hypothesis.
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
  -- Dual coercivity gains the penalty term in the constraint-forced component.
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
    simp only [primal, dual, add_apply, smul_apply, ContinuousLinearMap.id_apply,
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

/-- Helper for Theorem 2.10: multiplier bounds through one index control the
effective multiplier in the corresponding normal equation. -/
private lemma normEffectiveMultiplier_le_of_bounds
    (h : EqualityConstrained.Regularity f c)
    (params : Parameters h x₀ multiplier₀)
    (run : Run f c params.rho params.beta x₀ multiplier₀)
    (k : ℕ)
    (hMultiplier : ∀ j ≤ k, ‖run.multiplier j‖ ≤ params.multiplierBound) :
    ‖run.multiplier k + (params.rho : ℝ) • c (run.point k)‖ ≤
      3 * (params.multiplierBound : ℝ) := by
  cases k with
  | zero =>
      -- At initialization the two parameter bounds control the summands.
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

/-- Helper for Theorem 2.10: region membership and multiplier bounds through the
current index force the next primal step to stay within `params.delta`. -/
private lemma normStep_le_of_mem_region_of_multiplier_bounds
    (h : EqualityConstrained.Regularity f c)
    (params : Parameters h x₀ multiplier₀)
    (run : Run f c params.rho params.beta x₀ multiplier₀)
    (k : ℕ) (hx : run.point k ∈ h.region)
    (hMultiplier : ∀ j ≤ k, ‖run.multiplier j‖ ≤ params.multiplierBound) :
    ‖run.step k‖ ≤ params.delta := by
  -- Apply the damped estimate to the exact model-optimality equation.
  have heffective := normEffectiveMultiplier_le_of_bounds h params run k hMultiplier
  have hestimate := normDampedNormalEquation_le
    (fderiv ℝ c (run.point k)) run.beta_pos run.rho_pos.le h.licqModulus_pos
    (h.licqLowerBound (run.point k) hx) (run.step k) (gradient f (run.point k))
    (run.multiplier k + params.rho • c (run.point k)) (run.optimality k)
  have hgradient := h.norm_gradient_le (run.point k) hx
  have hoperator :
      ‖ContinuousLinearMap.adjoint (fderiv ℝ c (run.point k))‖ ≤
        h.constraintGradientBound := by
    simpa only [EqualityConstrained.constraintGradient_def] using
      h.norm_constraintGradient_le (run.point k) hx
  -- Bound the two terms in the generic estimate by Assumption 2.3.
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
              (params.beta + params.rho * (h.licqModulus : ℝ) ^ 2) := hestimate
    _ ≤ h.gradientBound / params.beta +
        3 * h.constraintGradientBound * params.multiplierBound /
          (params.beta + params.rho * (h.licqModulus : ℝ) ^ 2) :=
      add_le_add hgradientTerm hconstraintTerm
    _ ≤ params.delta := params.comparisonBound_le

/-- Helper for Theorem 2.10: every positive Lyapunov value in an admissible
finite prefix is bounded by the deterministic initial potential. -/
private lemma lyapunov_le_initialPotentialBound_of_prefix
    (h : EqualityConstrained.Regularity f c)
    (params : Parameters h x₀ multiplier₀)
    (run : Run f c params.rho params.beta x₀ multiplier₀)
    {N k : ℕ} (hPrefix : run.IsAdmissiblePrefix h N)
    (hk_pos : 1 ≤ k) (hk_le : k ≤ N) :
    run.lyapunov h params k ≤ initialPotentialBound h params := by
  have hOneLeN : 1 ≤ N := hk_pos.trans hk_le
  have hsegment :=
    (run.isAdmissiblePrefix_iff h N).1 hPrefix 0 (by omega)
  have hstep := run.norm_step_le h params hPrefix (k := 0) (by omega)
  have hmultiplierZero := run.norm_multiplier_le h params hPrefix (k := 0) (by omega)
  have hmultiplierOne := run.norm_multiplier_le h params hPrefix (k := 1) hOneLeN
  -- The mean-value bound controls the first objective increment by `G Δ`.
  have hobjectiveIncrement :
      ‖f (run.point 1) - f (run.point 0)‖ ≤
        h.gradientBound * ‖run.point 1 - run.point 0‖ := by
    apply (convex_segment (run.point 0) (run.point 1)).norm_image_sub_le_of_norm_fderiv_le
      (𝕜 := ℝ)
    · intro u hu
      exact h.differentiableAt_objective (hsegment hu)
    · intro u hu
      simpa only [← toDual_gradient, LinearIsometryEquiv.norm_map] using
        h.norm_gradient_le u (hsegment hu)
    · exact left_mem_segment ℝ (run.point 0) (run.point 1)
    · exact right_mem_segment ℝ (run.point 0) (run.point 1)
  have hdisplacement : ‖run.point 1 - run.point 0‖ = ‖run.step 0‖ := by
    rw [run.point_succ 0, add_sub_cancel_left]
  have hsignedObjective :
      f (run.point 1) - f (run.point 0) ≤
        ‖f (run.point 1) - f (run.point 0)‖ := by
    simpa only [Real.norm_eq_abs] using
      le_abs_self (f (run.point 1) - f (run.point 0))
  have hobjective :
      f (run.point 1) ≤ f x₀ + h.gradientBound * params.delta := by
    have hgradientStep :
        (h.gradientBound : ℝ) * ‖run.step 0‖ ≤
          h.gradientBound * params.delta :=
      mul_le_mul_of_nonneg_left hstep (NNReal.coe_nonneg h.gradientBound)
    rw [hdisplacement] at hobjectiveIncrement
    rw [run.point_zero] at hsignedObjective hobjectiveIncrement
    linarith
  -- The multiplier update bounds the scaled first residual by `2 Λ`.
  have hresidualIdentity :
      (params.rho : ℝ) • c (run.point 1) =
        run.multiplier 1 - run.multiplier 0 := by
    rw [run.multiplier_succ 0]
    module
  have hscaledResidual :
      params.rho * ‖c (run.point 1)‖ ≤ 2 * params.multiplierBound := by
    calc
      params.rho * ‖c (run.point 1)‖ =
          ‖(params.rho : ℝ) • c (run.point 1)‖ := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos run.rho_pos]
      _ = ‖run.multiplier 1 - run.multiplier 0‖ :=
        congrArg norm hresidualIdentity
      _ ≤ ‖run.multiplier 1‖ + ‖run.multiplier 0‖ := norm_sub_le _ _
      _ ≤ 2 * params.multiplierBound := by linarith
  have hboundNonneg : (0 : ℝ) ≤ params.multiplierBound := by positivity
  have hinnerBound :
      ⟪run.multiplier 1, c (run.point 1)⟫_ℝ ≤
        params.multiplierBound * ‖c (run.point 1)‖ := by
    calc
      ⟪run.multiplier 1, c (run.point 1)⟫_ℝ ≤
          ‖run.multiplier 1‖ * ‖c (run.point 1)‖ :=
        real_inner_le_norm _ _
      _ ≤ params.multiplierBound * ‖c (run.point 1)‖ :=
        mul_le_mul_of_nonneg_right hmultiplierOne (norm_nonneg _)
  have hinnerScaled :
      params.rho * ⟪run.multiplier 1, c (run.point 1)⟫_ℝ ≤
        2 * params.multiplierBound ^ 2 := by
    have hinnerRho := mul_le_mul_of_nonneg_left hinnerBound run.rho_pos.le
    have hresidualBound := mul_le_mul_of_nonneg_left hscaledResidual hboundNonneg
    nlinarith
  have hscaledResidualSq :
      (params.rho * ‖c (run.point 1)‖) ^ 2 ≤
        (2 * params.multiplierBound) ^ 2 :=
    (sq_le_sq₀ (mul_nonneg run.rho_pos.le (norm_nonneg _))
      (mul_nonneg (by norm_num) hboundNonneg)).2 hscaledResidual
  have hconstraintContribution :
      ⟪run.multiplier 1, c (run.point 1)⟫_ℝ +
          params.rho / 2 * ‖c (run.point 1)‖ ^ 2 ≤
        4 * params.multiplierBound ^ 2 / params.rho := by
    apply (le_div_iff₀ run.rho_pos).2
    nlinarith
  -- The nonnegative correction is bounded by its value at the step radius.
  have hconstantNonneg :
      0 ≤ multiplierPrimalConstant h params.delta params.beta params.rho
        params.multiplierBound := by
    rw [multiplierPrimalConstant_def]
    positivity
  have hstepSq : ‖run.step 0‖ ^ 2 ≤ (params.delta : ℝ) ^ 2 :=
    (sq_le_sq₀ (norm_nonneg _) (NNReal.coe_nonneg _)).2 hstep
  have hcorrection :
      (multiplierPrimalConstant h params.delta params.beta params.rho
          params.multiplierBound / params.rho) * ‖run.step 0‖ ^ 2 ≤
        (multiplierPrimalConstant h params.delta params.beta params.rho
          params.multiplierBound / params.rho) * params.delta ^ 2 :=
    mul_le_mul_of_nonneg_left hstepSq
      (div_nonneg hconstantNonneg run.rho_pos.le)
  have hbase :
      run.lyapunov h params 1 ≤ initialPotentialBound h params := by
    rw [run.lyapunov_def, augmentedLagrangian_def, initialPotentialBound_def]
    norm_num only [Nat.reduceSub]
    linarith
  -- Theorem 2.9 propagates the base bound across the rest of the prefix.
  revert hk_le
  induction k, hk_pos using Nat.le_induction with
  | base =>
      intro hk_le
      exact hbase
  | succ k hk_pos hprevious =>
      intro hkNextLe
      have hklt : k < N := by omega
      have hdescent := run.lyapunovDescent h params hPrefix hk_pos hklt
      have hdropNonneg :
          0 ≤ (params.beta / 4) * ‖run.step k‖ ^ 2 :=
        mul_nonneg (by positivity) (sq_nonneg _)
      have hpreviousBound := hprevious (by omega)
      linarith

/-- Helper for Theorem 2.10: every point in an admissible finite prefix obeys
the deterministic objective bound. -/
private lemma objective_le_deterministicBound_of_prefix
    (h : EqualityConstrained.Regularity f c)
    (params : Parameters h x₀ multiplier₀)
    (run : Run f c params.rho params.beta x₀ multiplier₀)
    {N k : ℕ} (hPrefix : run.IsAdmissiblePrefix h N) (hk : k ≤ N) :
    f (run.point k) ≤ deterministicObjectiveBound h params := by
  have hconstantNonneg :
      0 ≤ multiplierPrimalConstant h params.delta params.beta params.rho
        params.multiplierBound := by
    rw [multiplierPrimalConstant_def]
    positivity
  by_cases hkzero : k = 0
  · -- At index zero every added term in the deterministic bound is nonnegative.
    subst k
    rw [run.point_zero, deterministicObjectiveBound_def, initialPotentialBound_def]
    have hgradientTerm :
        0 ≤ (h.gradientBound : ℝ) * params.delta := by positivity
    have hresidualTerm :
        0 ≤ 4 * (params.multiplierBound : ℝ) ^ 2 / params.rho := by positivity
    have hcorrectionTerm :
        0 ≤ (multiplierPrimalConstant h params.delta params.beta params.rho
          params.multiplierBound / params.rho) * (params.delta : ℝ) ^ 2 :=
      mul_nonneg (div_nonneg hconstantNonneg run.rho_pos.le) (sq_nonneg _)
    have hmultiplierTerm :
        0 ≤ (params.multiplierBound : ℝ) ^ 2 / (2 * params.rho) := by positivity
    linarith
  · -- Complete the square in the augmented Lagrangian at a positive index.
    have hk_pos : 1 ≤ k := Nat.one_le_iff_ne_zero.2 hkzero
    have hphi :=
      lyapunov_le_initialPotentialBound_of_prefix h params run hPrefix hk_pos hk
    have hmultiplier := run.norm_multiplier_le h params hPrefix hk
    have hboundNonneg : (0 : ℝ) ≤ params.multiplierBound := by positivity
    have hinner :
        -(‖run.multiplier k‖ * ‖c (run.point k)‖) ≤
          ⟪run.multiplier k, c (run.point k)⟫_ℝ :=
      neg_le_of_abs_le (abs_real_inner_le_norm _ _)
    have hyoung :
        2 * ‖c (run.point k)‖ * ‖run.multiplier k‖ ≤
          params.rho * ‖c (run.point k)‖ ^ 2 +
            (params.rho : ℝ)⁻¹ * ‖run.multiplier k‖ ^ 2 :=
      two_mul_le_add_mul_sq run.rho_pos
    have hyoungDivided :=
      div_le_div_of_nonneg_right hyoung (by norm_num : (0 : ℝ) ≤ 2)
    have hyoungHalf :
        ‖run.multiplier k‖ * ‖c (run.point k)‖ ≤
          params.rho / 2 * ‖c (run.point k)‖ ^ 2 +
            ‖run.multiplier k‖ ^ 2 / (2 * params.rho) := by
      calc
        ‖run.multiplier k‖ * ‖c (run.point k)‖ =
            (2 * ‖c (run.point k)‖ * ‖run.multiplier k‖) / 2 := by ring
        _ ≤ (params.rho * ‖c (run.point k)‖ ^ 2 +
              (params.rho : ℝ)⁻¹ * ‖run.multiplier k‖ ^ 2) / 2 := hyoungDivided
        _ = params.rho / 2 * ‖c (run.point k)‖ ^ 2 +
              ‖run.multiplier k‖ ^ 2 / (2 * params.rho) := by
          field_simp [run.rho_pos.ne']
    have hmultiplierSq :
        ‖run.multiplier k‖ ^ 2 ≤ (params.multiplierBound : ℝ) ^ 2 :=
      (sq_le_sq₀ (norm_nonneg _) hboundNonneg).2 hmultiplier
    have hdiv :
        ‖run.multiplier k‖ ^ 2 / (2 * (params.rho : ℝ)) ≤
          (params.multiplierBound : ℝ) ^ 2 / (2 * (params.rho : ℝ)) :=
      (div_le_div_iff_of_pos_right (mul_pos (by norm_num) run.rho_pos)).2
        hmultiplierSq
    have hcorrectionNonneg :
        0 ≤ (multiplierPrimalConstant h params.delta params.beta params.rho
            params.multiplierBound / params.rho) * ‖run.step (k - 1)‖ ^ 2 :=
      mul_nonneg (div_nonneg hconstantNonneg run.rho_pos.le) (sq_nonneg _)
    rw [run.lyapunov_def, augmentedLagrangian_def] at hphi
    rw [deterministicObjectiveBound_def]
    linarith

/-- Helper for Theorem 2.10: every point in an admissible deterministic
prefix satisfies the feasibility bound used by the localization set. -/
private lemma constraintNorm_le_localizationBound_of_prefix
    (h : EqualityConstrained.Regularity f c)
    (params : Parameters h x₀ multiplier₀)
    (run : Run f c params.rho params.beta x₀ multiplier₀)
    {N k : ℕ} (hPrefix : run.IsAdmissiblePrefix h N) (hk : k ≤ N) :
    ‖c (run.point k)‖ ≤ 2 * params.multiplierBound / params.rho := by
  by_cases hkzero : k = 0
  · subst k
    rw [run.point_zero]
    apply (le_div_iff₀ run.rho_pos).2
    have hboundNonneg : (0 : ℝ) ≤ params.multiplierBound := by positivity
    linarith [params.initialResidual_le]
  · obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hkzero
    have hj : j ≤ N := by omega
    have hprevious := run.norm_multiplier_le h params hPrefix hj
    have hcurrent := run.norm_multiplier_le h params hPrefix hk
    have hresidualIdentity :
        (params.rho : ℝ) • c (run.point (j + 1)) =
          run.multiplier (j + 1) - run.multiplier j := by
      rw [run.multiplier_succ j]
      module
    apply (le_div_iff₀ run.rho_pos).2
    calc
      ‖c (run.point (j + 1))‖ * params.rho =
          params.rho * ‖c (run.point (j + 1))‖ := by ring
      _ = ‖(params.rho : ℝ) • c (run.point (j + 1))‖ := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos run.rho_pos]
      _ = ‖run.multiplier (j + 1) - run.multiplier j‖ :=
        congrArg norm hresidualIdentity
      _ ≤ ‖run.multiplier (j + 1)‖ + ‖run.multiplier j‖ := norm_sub_le _ _
      _ ≤ 2 * params.multiplierBound := by linarith

/-- Helper for Theorem 2.10: a deterministic-sublevel point with a bounded
outgoing step has its whole outgoing segment in the regularity region. -/
private lemma segment_subset_region_of_point_mem_sublevel
    (h : EqualityConstrained.Regularity f c)
    (params : Parameters h x₀ multiplier₀)
    (h_region : DeterministicRegionCondition h params)
    (run : Run f c params.rho params.beta x₀ multiplier₀)
    (k : ℕ) (hx : run.point k ∈ deterministicSublevel h params)
    (hstep : ‖run.step k‖ ≤ params.delta) :
    segment ℝ (run.point k) (run.point (k + 1)) ⊆ h.region := by
  have hstepDistance :
      dist (run.point k) (run.point (k + 1)) ≤ params.delta := by
    calc
      dist (run.point k) (run.point (k + 1)) =
          dist (run.point (k + 1)) (run.point k) := dist_comm _ _
      _ = ‖run.step k‖ := by
        rw [run.point_succ, dist_eq_norm, add_sub_cancel_left]
      _ ≤ params.delta := hstep
  -- Every segment point lies in the closed thickening around its left endpoint.
  intro y hy
  apply h_region
  apply Metric.mem_cthickening_of_dist_le y (run.point k) params.delta
    (deterministicSublevel h params) hx
  exact (Metric.mem_closedBall.mp
    (segment_subset_closedBall_left (run.point k) (run.point (k + 1)) hy)).trans
    hstepDistance

include h_region

/-- Theorem 2.10 (2): the deterministic NR-LALM run is globally admissible. -/
theorem admissible : run.IsAdmissible h := by
  -- Build global admissibility by extending one controlled finite prefix at a time.
  apply (run.isAdmissible_iff_allPrefixes h).2
  intro N
  induction N with
  | zero =>
      exact (run.isAdmissiblePrefix_iff h 0).2 fun k hk ↦ by omega
  | succ N hPrefix =>
      apply (run.isAdmissiblePrefix_iff h (N + 1)).2
      intro k hk
      by_cases hkOld : k < N
      · exact (run.isAdmissiblePrefix_iff h N).1 hPrefix k hkOld
      · have hkeq : k = N := by omega
        subst k
        -- The prefix invariant places the current point in the deterministic sublevel.
        have hobjective :=
          objective_le_deterministicBound_of_prefix h params run hPrefix
            (Nat.le_refl N)
        have hconstraint :=
          constraintNorm_le_localizationBound_of_prefix h params run hPrefix
            (Nat.le_refl N)
        have hsublevel : run.point N ∈ deterministicSublevel h params :=
          (mem_deterministicSublevel h params (run.point N)).2
            ⟨hobjective, hconstraint⟩
        have hxRegion : run.point N ∈ h.region := by
          apply h_region
          exact Metric.self_subset_cthickening
            (deterministicSublevel h params) hsublevel
        -- Past multiplier bounds give the non-circular bound on the new step.
        have hMultiplier :
            ∀ j ≤ N, ‖run.multiplier j‖ ≤ params.multiplierBound :=
          fun j hj ↦ run.norm_multiplier_le h params hPrefix hj
        have hstep :=
          normStep_le_of_mem_region_of_multiplier_bounds h params run N
            hxRegion hMultiplier
        exact segment_subset_region_of_point_mem_sublevel h params h_region run N
          hsublevel hstep

/-- Finite-prefix form of the global admissibility conclusion in Theorem 2.10. -/
theorem allPrefixesAdmissible (N : ℕ) : run.IsAdmissiblePrefix h N :=
  (admissible h params h_region run).prefix N

/-- The primal-step conclusion of Theorem 2.10: every generated step satisfies
the uniform bound `‖run.step k‖ ≤ params.delta`. -/
theorem norm_step_le_global (k : ℕ) : ‖run.step k‖ ≤ params.delta := by
  -- Apply the finite-prefix step estimate to the prefix ending after step `k`.
  exact run.norm_step_le h params
    (allPrefixesAdmissible h params h_region run (k + 1)) (Nat.lt_succ_self k)

/-- The multiplier conclusion of Theorem 2.10: every generated multiplier
satisfies the uniform bound `‖run.multiplier k‖ ≤ params.multiplierBound`. -/
theorem norm_multiplier_le_global (k : ℕ) :
    ‖run.multiplier k‖ ≤ params.multiplierBound := by
  -- The prefix ending at `k` already contains the required multiplier bound.
  exact run.norm_multiplier_le h params
    (allPrefixesAdmissible h params h_region run k) (Nat.le_refl k)

/-- The objective-value conclusion of Theorem 2.10: every generated value is at
most the deterministic objective threshold. -/
theorem objective_le_deterministicBound (k : ℕ) :
    f (run.point k) ≤ deterministicObjectiveBound h params := by
  -- Specialize the prefix objective invariant to its right endpoint.
  exact objective_le_deterministicBound_of_prefix h params run
    (allPrefixesAdmissible h params h_region run k) (Nat.le_refl k)

/-- Every generated primal point satisfies the deterministic localization
feasibility bound. -/
theorem constraintNorm_le_localizationBound (k : ℕ) :
    ‖c (run.point k)‖ ≤ 2 * params.multiplierBound / params.rho := by
  exact constraintNorm_le_localizationBound_of_prefix h params run
    (allPrefixesAdmissible h params h_region run k) (Nat.le_refl k)

/-- Every generated primal point belongs to the deterministic
objective--feasibility localization set. -/
theorem point_mem_deterministicSublevel (k : ℕ) :
    run.point k ∈ deterministicSublevel h params :=
  (mem_deterministicSublevel h params (run.point k)).2
    ⟨objective_le_deterministicBound h params h_region run k,
      constraintNorm_le_localizationBound h params h_region run k⟩

/-- The Lyapunov conclusion of Theorem 2.10: every positive-index value is at
most the initial potential bound. -/
theorem lyapunov_le_initialPotentialBound (k : ℕ) (hk : 1 ≤ k) :
    run.lyapunov h params k ≤ initialPotentialBound h params := by
  -- Specialize the prefix Lyapunov invariant to the positive endpoint `k`.
  exact lyapunov_le_initialPotentialBound_of_prefix h params run
    (allPrefixesAdmissible h params h_region run k) hk (Nat.le_refl k)

end

end LALM.Run

end
