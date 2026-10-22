/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@5bf5af722d85bd5c98368c41c4066124a15e8fd3:ReasBook/Papers/TR_LALM_theory/README.md (formalization contributor).
-/

module

public import TR_LALM_theory.Corollary_4_2.StoppedProcess

public section

open MeasureTheory
open scoped InnerProductSpace NNReal

namespace LALM.Correction

universe u

variable {n m : ℕ}
variable {f : EuclideanSpace ℝ (Fin n) → ℝ}
variable {c : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m)}

/-- Helper for Corollary 4.2: the Gram endomorphism as a continuous linear map. -/
noncomputable def gramOperator
    (c : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m))
    (z : EuclideanSpace ℝ (Fin n)) :
    EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin m) :=
  (ContinuousLinearMap.adjoint
    (EqualityConstrained.constraintGradient c z)).comp
      (EqualityConstrained.constraintGradient c z)

/-- Helper for Corollary 4.2: the continuous Gram operator has the same
underlying linear map as the correction API's Gram endomorphism. -/
theorem gramOperator_toLinearMap
    (c : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m))
    (z : EuclideanSpace ℝ (Fin n)) :
    (gramOperator c z).toLinearMap = gram c z := by
  -- Both spellings are the adjoint of the constraint gradient composed with it.
  rfl

/-- Helper for Corollary 4.2: LICQ makes the continuous Gram operator
continuously invertible at every point of the regularity region. -/
private lemma gramOperator_isInvertible
    (h : EqualityConstrained.Regularity f c)
    (z : EuclideanSpace ℝ (Fin n)) (hz : z ∈ h.region) :
    (gramOperator c z).IsInvertible := by
  -- Injectivity follows from the existing linear-map Gram argument.
  have hinjective : Function.Injective (gramOperator c z) := by
    intro p q hpq
    have hgramInjective : Function.Injective (gram c z) := by
      rw [gram_def, ← ContinuousLinearMap.adjoint_toLinearMap]
      simpa only [LinearMap.coe_comp, Function.comp_apply] using
        (LinearMap.adjoint_comp_self_injective_iff
          (EqualityConstrained.constraintGradient c z).toLinearMap).mpr
            (h.constraintGradientInjective z hz)
    exact hgramInjective hpq
  -- Finite dimensionality upgrades the operator to a continuous equivalence.
  have hsurjective : Function.Surjective (gramOperator c z).toLinearMap :=
    LinearMap.surjective_of_injective hinjective
  let gramEquiv : EuclideanSpace ℝ (Fin m) ≃ₗ[ℝ]
      EuclideanSpace ℝ (Fin m) :=
    LinearEquiv.ofBijective (gramOperator c z).toLinearMap
      ⟨hinjective, hsurjective⟩
  refine ⟨gramEquiv.toContinuousLinearEquiv, ?_⟩
  ext p
  rfl

/-- Helper for Corollary 4.2: a correction written using continuous-linear-map
inversion, before transport to the canonical `step` spelling. -/
private noncomputable def regularStep
    (c : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m))
    (x p : EuclideanSpace ℝ (Fin n)) : EuclideanSpace ℝ (Fin n) :=
  -EqualityConstrained.constraintGradient c (trialPoint x p)
    ((gramOperator c (trialPoint x p)).inverse (residual c x p))

/-- Helper for Corollary 4.2: on the LICQ region, continuous-map inversion
recovers the correction API's chosen Gram inverse. -/
private lemma regularStep_eq_step
    (h : EqualityConstrained.Regularity f c)
    (x p : EuclideanSpace ℝ (Fin n))
    (hz : trialPoint x p ∈ h.region) :
    regularStep c x p = step c x p := by
  have hinverse :
      (gramOperator c (trialPoint x p)).inverse (residual c x p) =
        gramInverse c (trialPoint x p) (residual c x p) := by
    -- The existing right-inverse equation uniquely identifies the continuous inverse.
    apply ((gramOperator_isInvertible h (trialPoint x p) hz).inverse_apply_eq).2
    simpa only [gramOperator, gram_def, ContinuousLinearMap.comp_apply,
      LinearMap.comp_apply, ContinuousLinearMap.coe_coe] using
        (comp_gramInverse h (trialPoint x p) hz (residual c x p)).symm
  -- Substitute the uniquely identified inverse into the two correction formulas.
  rw [regularStep, step_def, hinverse]

/-- Helper for Corollary 4.2: point--step data whose current and trial points
both lie in the regularity region. -/
def stepRegularityDomain (h : EqualityConstrained.Regularity f c) :
    Set (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)) :=
  {z | z.1 ∈ h.region ∧ trialPoint z.1 z.2 ∈ h.region}

/-- Helper for Corollary 4.2: membership in the corrected transition domain
is exactly regularity of the current and trial points. -/
theorem mem_stepRegularityDomain_iff
    (h : EqualityConstrained.Regularity f c)
    (z : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)) :
    z ∈ stepRegularityDomain h ↔
      z.1 ∈ h.region ∧ trialPoint z.1 z.2 ∈ h.region := Iff.rfl

/-- Helper for Corollary 4.2: the correction varies continuously while its
current and trial points remain in the regularity region. -/
theorem continuousOn_step (h : EqualityConstrained.Regularity f c) :
    ContinuousOn
      (fun z : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) ↦
        step c z.1 z.2)
      (stepRegularityDomain h) := by
  have htrial : Continuous
      (fun z : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) ↦
        trialPoint z.1 z.2) := by
    -- Keep the pointwise lambda spelling expected by the correction formulas.
    unfold trialPoint
    fun_prop
  have hregular : ContinuousOn
      (fun z : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) ↦
        regularStep c z.1 z.2)
      (stepRegularityDomain h) := by
    intro z hz
    have hConstraintCurrent : ContinuousAt
        (fun y : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) ↦
          c y.1) z :=
      (h.continuousAt_constraint hz.1).comp continuous_fst.continuousAt
    have hConstraintTrial : ContinuousAt
        (fun y : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) ↦
          c (trialPoint y.1 y.2)) z :=
      (h.continuousAt_constraint hz.2).comp'
        (f := fun y : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) ↦
          trialPoint y.1 y.2) htrial.continuousAt
    have hConstraintFDerivCurrent : ContinuousAt
        (fun y : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) ↦
          fderiv ℝ c y.1) z :=
      (h.continuousOn_constraintFDeriv.continuousAt
        (h.isOpen_region.mem_nhds hz.1)).comp continuous_fst.continuousAt
    have hConstraintGradientTrial : ContinuousAt
        (fun y : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) ↦
          EqualityConstrained.constraintGradient c (trialPoint y.1 y.2)) z :=
      (h.continuousAt_constraintGradient hz.2).comp'
        (f := fun y : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) ↦
          trialPoint y.1 y.2) htrial.continuousAt
    have hAdjointTrial : ContinuousAt
        (fun y : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) ↦
          ContinuousLinearMap.adjoint
            (EqualityConstrained.constraintGradient c (trialPoint y.1 y.2))) z :=
      ContinuousLinearMap.adjoint.continuous.continuousAt.comp
        hConstraintGradientTrial
    have hGramTrial : ContinuousAt
        (fun y : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) ↦
          gramOperator c (trialPoint y.1 y.2)) z := by
      unfold gramOperator
      exact hAdjointTrial.clm_comp hConstraintGradientTrial
    have hResidual : ContinuousAt
        (fun y : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) ↦
          residual c y.1 y.2) z := by
      simp only [residual_def]
      exact (hConstraintTrial.sub hConstraintCurrent).sub
        (hConstraintFDerivCurrent.clm_apply continuous_snd.continuousAt)
    have hinverseAt : ContinuousAt ContinuousLinearMap.inverse
        (gramOperator c (trialPoint z.1 z.2)) :=
      ((gramOperator_isInvertible h (trialPoint z.1 z.2) hz.2
        |>.contDiffAt_map_inverse (n := 0)).continuousAt)
    have hinversePair : ContinuousAt
        (fun y : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) ↦
          (gramOperator c (trialPoint y.1 y.2)).inverse) z :=
      hinverseAt.comp'
        (f := fun y : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) ↦
          gramOperator c (trialPoint y.1 y.2)) hGramTrial
    have hregularAt : ContinuousAt
        (fun y : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) ↦
          regularStep c y.1 y.2) z := by
      -- Apply the inverse to the residual, then the constraint gradient to that result.
      unfold regularStep
      exact (hConstraintGradientTrial.clm_apply
        (hinversePair.clm_apply hResidual)).neg
    exact hregularAt.continuousWithinAt
  -- The two formulas agree pointwise on the regularity domain.
  exact hregular.congr fun z hz ↦ (regularStep_eq_step h z.1 z.2 hz.2).symm

/-- Helper for Corollary 4.2: the corrected next point varies continuously
while its current and trial points remain in the regularity region. -/
theorem continuousOn_nextPoint (h : EqualityConstrained.Regularity f c) :
    ContinuousOn
      (fun z : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) ↦
        nextPoint c z.1 z.2)
      (stepRegularityDomain h) := by
  have htrial : Continuous
      (fun z : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) ↦
        trialPoint z.1 z.2) := by
    -- Keep the pointwise lambda spelling expected by `nextPoint`.
    unfold trialPoint
    fun_prop
  -- Add the globally continuous trial point to the localized correction.
  intro z hz
  unfold nextPoint
  have hpointwise :
      (fun y : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) ↦
        trialPoint y.1 y.2 + step c y.1 y.2) =
      (fun y ↦ trialPoint y.1 y.2) + (fun y ↦ step c y.1 y.2) := by
    funext y
    rfl
  rw [hpointwise]
  exact htrial.continuousAt.continuousWithinAt.add
    ((continuousOn_step h) z hz)

namespace StochasticRun

variable {x₀ : EuclideanSpace ℝ (Fin n)}
variable {multiplier₀ : EuclideanSpace ℝ (Fin m)}

/-- Helper for Corollary 4.2: the positive-definite operator in the corrected
stochastic base-step model. -/
private noncomputable def baseStepOperator
    (c : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m))
    (rho beta : ℝ) (x : EuclideanSpace ℝ (Fin n)) :
    EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) :=
  beta • ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n)) +
    rho • (EqualityConstrained.constraintGradient c x).comp (fderiv ℝ c x)

/-- Helper for Corollary 4.2: positive penalty and proximal coefficients make
the base-step operator continuously invertible. -/
private lemma baseStepOperator_isInvertible
    (c : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m))
    (rho beta : ℝ) (x : EuclideanSpace ℝ (Fin n))
    (hrho : 0 < rho) (hbeta : 0 < beta) :
    (baseStepOperator c rho beta x).IsInvertible := by
  have hinjective : Function.Injective (baseStepOperator c rho beta x) := by
    intro p q hpq
    let v : EuclideanSpace ℝ (Fin n) := p - q
    have hvKernel : baseStepOperator c rho beta x v = 0 := by
      dsimp only [v]
      rw [map_sub, hpq, sub_self]
    have hpair :
        inner ℝ (baseStepOperator c rho beta x v) v =
          beta * ‖v‖ ^ 2 + rho * ‖fderiv ℝ c x v‖ ^ 2 := by
      simp only [baseStepOperator, add_apply, smul_apply,
        ContinuousLinearMap.id_apply, ContinuousLinearMap.comp_apply,
        EqualityConstrained.constraintGradient_def]
      rw [inner_add_left, real_inner_smul_left, real_inner_smul_left,
        ContinuousLinearMap.adjoint_inner_left, real_inner_self_eq_norm_sq,
        real_inner_self_eq_norm_sq]
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
      (baseStepOperator c rho beta x).toLinearMap :=
    LinearMap.surjective_of_injective hinjective
  let baseStepEquiv : EuclideanSpace ℝ (Fin n) ≃ₗ[ℝ]
      EuclideanSpace ℝ (Fin n) :=
    LinearEquiv.ofBijective (baseStepOperator c rho beta x).toLinearMap
      ⟨hinjective, hsurjective⟩
  refine ⟨baseStepEquiv.toContinuousLinearEquiv, ?_⟩
  ext p
  rfl

/-- Helper for Corollary 4.2: the canonical corrected stochastic base step is
the inverse solution of its first-order equation. -/
noncomputable def canonicalBaseStep
    (c : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m))
    (rho beta : ℝ) (x g : EuclideanSpace ℝ (Fin n))
    (multiplier : EuclideanSpace ℝ (Fin m)) : EuclideanSpace ℝ (Fin n) :=
  (baseStepOperator c rho beta x).inverse
    (-(g + EqualityConstrained.constraintGradient c x
      (multiplier + rho • c x)))

/-- Helper for Corollary 4.2: every minimizing explicit-gradient model step
equals the canonical inverse-based base step. -/
theorem canonicalBaseStep_eq_of_minimizes
    (c : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m))
    (rho beta : ℝ) (x g : EuclideanSpace ℝ (Fin n))
    (multiplier : EuclideanSpace ℝ (Fin m))
    (p : EuclideanSpace ℝ (Fin n)) (hrho : 0 < rho) (hbeta : 0 < beta)
    (hp : IsMinOn (stepModelWithGradient c g rho beta x multiplier)
      Set.univ p) :
    canonicalBaseStep c rho beta x g multiplier = p := by
  -- Normalize model optimality into the canonical operator equation.
  have hoptimal := stepModelWithGradientOptimality g rho beta x multiplier p hp
  have hsum :
      (g + EqualityConstrained.constraintGradient c x
        (multiplier + rho • c x)) + baseStepOperator c rho beta x p = 0 := by
    simp only [baseStepOperator, add_apply, smul_apply,
      ContinuousLinearMap.id_apply, ContinuousLinearMap.comp_apply, map_add,
      map_smul] at hoptimal ⊢
    linear_combination (norm := module) hoptimal
  have hoperator : baseStepOperator c rho beta x p =
      -(g + EqualityConstrained.constraintGradient c x
        (multiplier + rho • c x)) :=
    eq_neg_of_add_eq_zero_right hsum
  -- Invertibility identifies the minimizer with the inverse solution.
  unfold canonicalBaseStep
  exact ((baseStepOperator_isInvertible c rho beta x hrho hbeta).inverse_apply_eq).2
    hoperator.symm

/-- Helper for Corollary 4.2: model inputs whose current point lies in the
regularity region. -/
def baseStepRegularityDomain (h : EqualityConstrained.Regularity f c) :
    Set (EuclideanSpace ℝ (Fin n) ×
      (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin m))) :=
  {z | z.1 ∈ h.region}

/-- Helper for Corollary 4.2: membership in the base-step regularity domain is
exactly regularity of the current point. -/
theorem mem_baseStepRegularityDomain_iff
    (h : EqualityConstrained.Regularity f c)
    (z : EuclideanSpace ℝ (Fin n) ×
      (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin m))) :
    z ∈ baseStepRegularityDomain h ↔ z.1 ∈ h.region := by
  rfl

/-- Helper for Corollary 4.2: the canonical base-step solver is continuous
where its current point lies in the regularity region. -/
theorem continuousOn_canonicalBaseStep
    (h : EqualityConstrained.Regularity f c)
    (rho beta : ℝ) (hrho : 0 < rho) (hbeta : 0 < beta) :
    ContinuousOn (fun z : EuclideanSpace ℝ (Fin n) ×
        (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin m)) ↦
      canonicalBaseStep c rho beta z.1 z.2.1 z.2.2)
      (baseStepRegularityDomain h) := by
  intro z hz
  change z.1 ∈ h.region at hz
  have hConstraintFDeriv : ContinuousAt (fderiv ℝ c) z.1 :=
    h.continuousOn_constraintFDeriv.continuousAt
      (h.isOpen_region.mem_nhds hz)
  have hConstraintGradient :
      ContinuousAt (EqualityConstrained.constraintGradient c) z.1 :=
    h.continuousAt_constraintGradient hz
  have hConstraint : ContinuousAt c z.1 :=
    h.continuousAt_constraint hz
  have hOperator : ContinuousAt (fun x ↦ baseStepOperator c rho beta x) z.1 := by
    unfold baseStepOperator
    exact (ContinuousAt.const_smul continuousAt_const beta).add
      (ContinuousAt.const_smul
        (hConstraintGradient.clm_comp hConstraintFDeriv) rho)
  have hInverse : ContinuousAt
      (fun x ↦ (baseStepOperator c rho beta x).inverse) z.1 :=
    ((baseStepOperator_isInvertible c rho beta z.1 hrho hbeta
      |>.contDiffAt_map_inverse (n := 0)).continuousAt.comp hOperator)
  have hRight : ContinuousAt (fun z : EuclideanSpace ℝ (Fin n) ×
      (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin m)) ↦
      -(z.2.1 + EqualityConstrained.constraintGradient c z.1
        (z.2.2 + rho • c z.1))) z := by
    exact (continuous_fst.continuousAt.comp continuous_snd.continuousAt).add
      ((hConstraintGradient.comp continuous_fst.continuousAt).clm_apply
        ((continuous_snd.continuousAt.comp continuous_snd.continuousAt).add
          (ContinuousAt.const_smul
            (hConstraint.comp continuous_fst.continuousAt) rho))) |>.neg
  unfold canonicalBaseStep
  exact ((hInverse.comp continuous_fst.continuousAt).clm_apply hRight).continuousWithinAt

/-- Helper for Corollary 4.2: the canonical base step depends measurably on
the point, clipped gradient, and multiplier. -/
theorem measurable_canonicalBaseStep
    (hcont : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) c)
    (rho beta : ℝ) (hrho : 0 < rho) (hbeta : 0 < beta) :
    Measurable (fun z : EuclideanSpace ℝ (Fin n) ×
        (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin m)) ↦
      canonicalBaseStep c rho beta z.1 z.2.1 z.2.2) := by
  have htopNonzero : ((⊤ : ℕ∞) : WithTop ℕ∞) ≠ 0 := by
    simp
  have hfderivContinuous : Continuous (fderiv ℝ c) :=
    hcont.continuous_fderiv htopNonzero
  have hconstraintGradientContinuous :
      Continuous (EqualityConstrained.constraintGradient c) :=
    ContinuousLinearMap.adjoint.continuous.comp hfderivContinuous
  have hoperatorContinuous :
      Continuous (fun x ↦ baseStepOperator c rho beta x) := by
    unfold baseStepOperator
    exact (Continuous.const_smul continuous_const beta).add
      (Continuous.const_smul
        (hconstraintGradientContinuous.clm_comp hfderivContinuous) rho)
  have hinverseContinuous : Continuous
      (fun x ↦ (baseStepOperator c rho beta x).inverse) := by
    rw [continuous_iff_continuousAt]
    intro x
    exact ((baseStepOperator_isInvertible c rho beta x hrho hbeta
      |>.contDiffAt_map_inverse (n := 0)).continuousAt.comp
        hoperatorContinuous.continuousAt)
  have hcContinuous : Continuous c := hcont.continuous
  have hrhsContinuous : Continuous (fun z : EuclideanSpace ℝ (Fin n) ×
      (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin m)) ↦
      -(z.2.1 + EqualityConstrained.constraintGradient c z.1
        (z.2.2 + rho • c z.1))) := by
    exact (continuous_fst.comp continuous_snd).add
      ((hconstraintGradientContinuous.comp continuous_fst).clm_apply
        ((continuous_snd.comp continuous_snd).add
          (Continuous.const_smul (hcContinuous.comp continuous_fst) rho))) |>.neg
  -- Apply the continuously varying inverse to the continuously varying right side.
  unfold canonicalBaseStep
  exact ((hinverseContinuous.comp continuous_fst).clm_apply
    hrhsContinuous).measurable

/-- Helper for Corollary 4.2: bounded clipped-gradient and effective-multiplier
data place the canonical base step inside the prescribed radius. -/
theorem norm_canonicalBaseStep_le
    (h : EqualityConstrained.Regularity f c)
    (params : Parameters h x₀ multiplier₀)
    (x g : EuclideanSpace ℝ (Fin n))
    (multiplier : EuclideanSpace ℝ (Fin m))
    (hx : x ∈ h.region) (hgradient : ‖g‖ ≤ h.gradientBound)
    (heffective :
      ‖multiplier + (params.rho : ℝ) • c x‖ ≤
        3 * params.multiplierBound) :
    ‖canonicalBaseStep c params.rho params.beta x g multiplier‖ ≤
      params.delta := by
  let p := canonicalBaseStep c params.rho params.beta x g multiplier
  have hoperator :
      baseStepOperator c params.rho params.beta x p =
        -(g + EqualityConstrained.constraintGradient c x
          (multiplier + (params.rho : ℝ) • c x)) := by
    have hinverse :=
      ((baseStepOperator_isInvertible c params.rho params.beta x
        params.spec.1.2.2.1 params.spec.1.2.1).inverse_apply_eq).1
          (rfl : p = p)
    exact hinverse.symm
  have hequation :
      (params.beta : ℝ) • p +
          (params.rho : ℝ) • (fderiv ℝ c x).adjoint (fderiv ℝ c x p) =
        -g - (fderiv ℝ c x).adjoint
          (multiplier + (params.rho : ℝ) • c x) := by
    simp only [baseStepOperator, add_apply, smul_apply,
      ContinuousLinearMap.id_apply, ContinuousLinearMap.comp_apply,
      EqualityConstrained.constraintGradient_def] at hoperator ⊢
    linear_combination (norm := module) hoperator
  have hbeta : 0 < (params.beta : ℝ) := params.spec.1.2.1
  have hrho : 0 ≤ (params.rho : ℝ) := params.spec.1.2.2.1.le
  have hestimate := Run.normDampedNormalEquation_le
    (fderiv ℝ c x) hbeta hrho h.licqModulus_pos
    (h.licqLowerBound x hx) p g
    (multiplier + params.rho • c x) hequation
  have hoperatorNorm :
      ‖ContinuousLinearMap.adjoint (fderiv ℝ c x)‖ ≤
        h.constraintGradientBound := by
    simpa only [EqualityConstrained.constraintGradient_def] using
      h.norm_constraintGradient_le x hx
  have hdenom :
      0 < (params.beta : ℝ) + params.rho * (h.licqModulus : ℝ) ^ 2 :=
    add_pos_of_pos_of_nonneg hbeta
      (mul_nonneg hrho (sq_nonneg (h.licqModulus : ℝ)))
  have hgradientTerm :
      ‖g‖ / params.beta ≤ h.gradientBound / params.beta :=
    (div_le_div_iff_of_pos_right hbeta).2 hgradient
  have hproduct :
      ‖ContinuousLinearMap.adjoint (fderiv ℝ c x)‖ *
          ‖multiplier + params.rho • c x‖ ≤
        h.constraintGradientBound * (3 * params.multiplierBound) :=
    mul_le_mul hoperatorNorm heffective (norm_nonneg _)
      (NNReal.coe_nonneg h.constraintGradientBound)
  have hconstraintTerm :
      ‖ContinuousLinearMap.adjoint (fderiv ℝ c x)‖ *
          ‖multiplier + params.rho • c x‖ /
            (params.beta + params.rho * (h.licqModulus : ℝ) ^ 2) ≤
        3 * h.constraintGradientBound * params.multiplierBound /
            (params.beta + params.rho * (h.licqModulus : ℝ) ^ 2) := by
    rw [div_le_div_iff_of_pos_right hdenom]
    nlinarith
  -- The parameter comparison bound absorbs the two normal-equation terms.
  calc
    ‖canonicalBaseStep c params.rho params.beta x g multiplier‖ = ‖p‖ := rfl
    _ ≤ ‖g‖ / params.beta +
        ‖ContinuousLinearMap.adjoint (fderiv ℝ c x)‖ *
          ‖multiplier + params.rho • c x‖ /
            (params.beta + params.rho * (h.licqModulus : ℝ) ^ 2) := hestimate
    _ ≤ h.gradientBound / params.beta +
        3 * h.constraintGradientBound * params.multiplierBound /
          (params.beta + params.rho * (h.licqModulus : ℝ) ^ 2) :=
      add_le_add hgradientTerm hconstraintTerm
    _ ≤ params.delta := params.comparisonBound_le

/-- Helper for Corollary 4.2: the canonical base step satisfies the explicit
first-order stationarity equation without reference to a chosen run. -/
theorem canonicalBaseStep_optimality
    (c : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m))
    (rho beta : ℝ) (x g : EuclideanSpace ℝ (Fin n))
    (multiplier : EuclideanSpace ℝ (Fin m))
    (hrho : 0 < rho) (hbeta : 0 < beta) :
    g + EqualityConstrained.constraintGradient c x
        (multiplier + rho •
          (c x + fderiv ℝ c x (canonicalBaseStep c rho beta x g multiplier))) +
        beta • canonicalBaseStep c rho beta x g multiplier = 0 := by
  let p := canonicalBaseStep c rho beta x g multiplier
  have hoperator : baseStepOperator c rho beta x p =
      -(g + EqualityConstrained.constraintGradient c x
        (multiplier + rho • c x)) := by
    have hinverse :=
      ((baseStepOperator_isInvertible c rho beta x hrho hbeta).inverse_apply_eq).1
        (rfl : p = p)
    exact hinverse.symm
  -- Expand the operator once and regroup its terms into model stationarity.
  simp only [baseStepOperator, add_apply, smul_apply,
    ContinuousLinearMap.id_apply, ContinuousLinearMap.comp_apply, map_add,
    map_smul] at hoperator ⊢
  linear_combination (norm := module) hoperator

/-- Helper for Corollary 4.2: canonical base-step stationarity gives the
corrected perturbed-multiplier identity. -/
theorem canonicalBaseStep_perturbedMultiplierIdentity
    (c : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m))
    (rho beta : ℝ) (x g : EuclideanSpace ℝ (Fin n))
    (multiplier : EuclideanSpace ℝ (Fin m))
    (hrho : 0 < rho) (hbeta : 0 < beta) :
    g + EqualityConstrained.constraintGradient c x
        (nextMultiplier c rho x multiplier
          (canonicalBaseStep c rho beta x g multiplier)) +
        beta • canonicalBaseStep c rho beta x g multiplier =
      rho • EqualityConstrained.constraintGradient c x
        (error c x (canonicalBaseStep c rho beta x g multiplier)) := by
  -- Expand the corrected update and eliminate its linearized part by stationarity.
  rw [nextMultiplier_def, error_def]
  simp only [map_add, map_sub, map_smul]
  have hstationary := canonicalBaseStep_optimality c rho beta x g multiplier
    hrho hbeta
  simp only [map_add, map_smul] at hstationary
  linear_combination (norm := module) hstationary

/-- Helper for Corollary 4.2: an admissible bounded canonical transition
preserves the corrected multiplier bound. -/
theorem norm_nextMultiplier_canonicalBaseStep_le
    (h : EqualityConstrained.Regularity f c)
    (params : Parameters h x₀ multiplier₀)
    (x g : EuclideanSpace ℝ (Fin n))
    (multiplier : EuclideanSpace ℝ (Fin m))
    (hadm : IsAdmissible h x
      (canonicalBaseStep c params.rho params.beta x g multiplier))
    (hstep : ‖canonicalBaseStep c params.rho params.beta x g multiplier‖ ≤
      params.delta)
    (hgradient : ‖g‖ ≤ h.gradientBound) :
    ‖nextMultiplier c params.rho x multiplier
        (canonicalBaseStep c params.rho params.beta x g multiplier)‖ ≤
      params.multiplierBound := by
  let p := canonicalBaseStep c params.rho params.beta x g multiplier
  have hperturbed := canonicalBaseStep_perturbedMultiplierIdentity c
    params.rho params.beta x g multiplier params.spec.1.2.2.1 params.spec.1.2.1
  have hidentity :
      EqualityConstrained.constraintGradient c x
          (nextMultiplier c params.rho x multiplier p) =
        -g - (params.beta : ℝ) • p +
          (params.rho : ℝ) • EqualityConstrained.constraintGradient c x
            (error c x p) := by
    linear_combination (norm := module) hperturbed
  have hperturbation := normScaledConstraintGradientError_le h params x p
    hadm hstep
  have hbeta : 0 < (params.beta : ℝ) := params.spec.1.2.1
  have hnormalBound :
      ‖EqualityConstrained.constraintGradient c x
          (nextMultiplier c params.rho x multiplier p)‖ ≤
        h.gradientBound + params.beta * params.delta +
          params.rho * h.constraintGradientBound * errorFactor h params.delta *
            (params.delta : ℝ) ^ 2 := by
    rw [hidentity]
    calc
      ‖-g - params.beta • p +
          (params.rho : ℝ) • EqualityConstrained.constraintGradient c x
            (error c x p)‖ ≤
          ‖-g - params.beta • p‖ +
            ‖(params.rho : ℝ) • EqualityConstrained.constraintGradient c x
              (error c x p)‖ := norm_add_le _ _
      _ ≤ (‖g‖ + params.beta * ‖p‖) +
          ‖(params.rho : ℝ) • EqualityConstrained.constraintGradient c x
            (error c x p)‖ := by
        gcongr
        calc
          ‖-g - (params.beta : ℝ) • p‖ ≤
              ‖-g‖ + ‖(params.beta : ℝ) • p‖ := norm_sub_le _ _
          _ = ‖g‖ + params.beta * ‖p‖ := by
            rw [norm_neg, norm_smul, Real.norm_eq_abs, abs_of_pos hbeta]
      _ ≤ h.gradientBound + params.beta * params.delta +
          params.rho * h.constraintGradientBound * errorFactor h params.delta *
            (params.delta : ℝ) ^ 2 := by
        nlinarith [mul_le_mul_of_nonneg_left hstep hbeta.le]
  have hx := base_mem_region h x p hadm
  have hlicq := h.licqLowerBound x hx
    (nextMultiplier c params.rho x multiplier p)
  have hscaled :
      (h.licqModulus : ℝ) *
          ‖nextMultiplier c params.rho x multiplier p‖ ≤
        h.gradientBound + params.beta * params.delta +
          params.rho * h.constraintGradientBound * errorFactor h params.delta *
            (params.delta : ℝ) ^ 2 :=
    hlicq.trans hnormalBound
  have hquotient :
      ‖nextMultiplier c params.rho x multiplier p‖ ≤
        (h.gradientBound + params.beta * params.delta +
          params.rho * h.constraintGradientBound * errorFactor h params.delta *
            (params.delta : ℝ) ^ 2) / h.licqModulus := by
    rw [le_div_iff₀ (NNReal.coe_pos.2 h.licqModulus_pos)]
    simpa only [mul_comm] using hscaled
  exact hquotient.trans params.parameterBound_le

end StochasticRun

end LALM.Correction

end
