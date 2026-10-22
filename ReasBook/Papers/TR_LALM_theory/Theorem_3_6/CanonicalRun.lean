/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@5bf5af722d85bd5c98368c41c4066124a15e8fd3:ReasBook/Papers/TR_LALM_theory/README.md (formalization contributor).
-/

module

public import Mathlib.Probability.HasLawExists
public import TR_LALM_theory.Theorem_2_10
public import TR_LALM_theory.Theorem_3_6.Schedule

public section

open MeasureTheory
open scoped InnerProductSpace NNReal

namespace LALM

universe u

variable {n m : ℕ}
variable {Ξ : Type u} [MeasurableSpace Ξ] {ν : Measure Ξ} [IsProbabilityMeasure ν]
variable {f : EuclideanSpace ℝ (Fin n) → ℝ}
variable {c : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m)}
variable {x₀ : EuclideanSpace ℝ (Fin n)}
variable {multiplier₀ : EuclideanSpace ℝ (Fin m)}
variable {h : EqualityConstrained.Regularity f c}
variable {oracle : EqualityConstrained.StochasticOracle f h.region ν}
variable {params : Parameters h x₀ multiplier₀}
variable {Q B b : ℕ+}

/-- Helper for Theorem 3.6: the canonical probability space carries one oracle
sample at every iteration and batch coordinate. -/
abbrev CanonicalSampleSpace (Ξ : Type u) := (ℕ × ℕ) → Ξ

/-- Helper for Theorem 3.6: the canonical sample-space law is the infinite
product of copies of the oracle law `ν`. -/
noncomputable def canonicalProductMeasure (ν : Measure Ξ) :
    Measure (CanonicalSampleSpace Ξ) :=
  Measure.infinitePi (fun _ : ℕ × ℕ ↦ ν)

/-- Helper for Theorem 3.6: the canonical product law is a probability
measure. -/
instance canonicalProductMeasure.instIsProbabilityMeasure :
    IsProbabilityMeasure (canonicalProductMeasure ν) := by
  unfold canonicalProductMeasure
  infer_instance

namespace CanonicalRun

/-- Helper for Theorem 3.6: coordinate projection provides the sample used at
iteration `k` and batch position `i`. -/
def sample (k i : ℕ) (omega : CanonicalSampleSpace Ξ) : Ξ :=
  omega (k, i)

/-- Helper for Theorem 3.6: every canonical coordinate projection is
measurable. -/
lemma measurable_sample (k i : ℕ) :
    Measurable (sample (Ξ := Ξ) k i) :=
  measurable_pi_apply (k, i)

/-- Helper for Theorem 3.6: every canonical coordinate sample has law `ν`. -/
lemma sample_hasLaw (k i : ℕ) :
    ProbabilityTheory.HasLaw (sample (Ξ := Ξ) k i) ν
      (canonicalProductMeasure ν) := by
  exact MeasurePreserving.hasLaw
    (measurePreserving_eval_infinitePi (fun _ : ℕ × ℕ ↦ ν) (k, i))

/-- Helper for Theorem 3.6: all canonical coordinate samples are mutually
independent. -/
lemma sample_iIndepFun :
    ProbabilityTheory.iIndepFun
      (fun ki : ℕ × ℕ ↦ sample (Ξ := Ξ) ki.1 ki.2)
      (canonicalProductMeasure ν) := by
  exact ProbabilityTheory.iIndepFun_infinitePi
    (P := fun _ : ℕ × ℕ ↦ ν) (X := fun _ xi ↦ xi)
    (fun _ ↦ measurable_id)

/-- Helper for Theorem 3.6: the positive-definite linear operator governing
the explicit-gradient quadratic model. -/
private noncomputable def modelStepOperator
    (c : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m))
    (rho beta : ℝ) (x : EuclideanSpace ℝ (Fin n)) :
    EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) :=
  beta • ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n)) +
    rho • (EqualityConstrained.constraintGradient c x).comp (fderiv ℝ c x)

/-- Helper for Theorem 3.6: positive penalty and proximal coefficients make
the model operator continuously invertible. -/
private lemma modelStepOperator_isInvertible
    (c : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m))
    (rho beta : ℝ) (x : EuclideanSpace ℝ (Fin n))
    (hrho : 0 < rho) (hbeta : 0 < beta) :
    (modelStepOperator c rho beta x).IsInvertible := by
  have hinjective : Function.Injective (modelStepOperator c rho beta x) := by
    intro p q hpq
    let v : EuclideanSpace ℝ (Fin n) := p - q
    have hvKernel : modelStepOperator c rho beta x v = 0 := by
      dsimp only [v]
      rw [map_sub, hpq, sub_self]
    have hpair :
        inner ℝ (modelStepOperator c rho beta x v) v =
          beta * ‖v‖ ^ 2 + rho * ‖fderiv ℝ c x v‖ ^ 2 := by
      simp only [modelStepOperator, add_apply, smul_apply,
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
    have hvNorm : ‖v‖ = 0 := by
      exact sq_eq_zero_iff.mp ((mul_eq_zero.mp hfirst).resolve_left hbeta.ne')
    exact sub_eq_zero.mp (norm_eq_zero.mp hvNorm)
  have hsurjective : Function.Surjective
      (modelStepOperator c rho beta x).toLinearMap :=
    LinearMap.surjective_of_injective hinjective
  let modelEquiv : EuclideanSpace ℝ (Fin n) ≃ₗ[ℝ]
      EuclideanSpace ℝ (Fin n) :=
    LinearEquiv.ofBijective (modelStepOperator c rho beta x).toLinearMap
      ⟨hinjective, hsurjective⟩
  refine ⟨modelEquiv.toContinuousLinearEquiv, ?_⟩
  ext p
  rfl

/-- Helper for Theorem 3.6: the canonical model step solves the explicit
positive-definite first-order equation. -/
private noncomputable def canonicalModelStep
    (c : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m))
    (rho beta : ℝ) (x g : EuclideanSpace ℝ (Fin n))
    (multiplier : EuclideanSpace ℝ (Fin m)) : EuclideanSpace ℝ (Fin n) :=
  (modelStepOperator c rho beta x).inverse
    (-(g + EqualityConstrained.constraintGradient c x
      (multiplier + rho • c x)))

/-- Helper for Theorem 3.6: the derivative of the explicit-gradient model is
represented by its first-order normal-equation vector. -/
private lemma hasFDerivAtExplicitGradientModel
    (c : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m))
    (g : EuclideanSpace ℝ (Fin n)) (rho beta : ℝ)
    (x : EuclideanSpace ℝ (Fin n))
    (multiplier : EuclideanSpace ℝ (Fin m))
    (p : EuclideanSpace ℝ (Fin n)) :
    HasFDerivAt (stepModelWithGradient c g rho beta x multiplier)
      (innerSL ℝ (g + EqualityConstrained.constraintGradient c x
        (multiplier + rho • (c x + fderiv ℝ c x p)) + beta • p)) p := by
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
      (fun q ↦ (rho / 2) * ‖c x + fderiv ℝ c x q‖ ^ 2)
      ((rho / 2) • 2 • innerSL ℝ (EqualityConstrained.constraintGradient c x
        (c x + fderiv ℝ c x p))) p := by
    simpa only [EqualityConstrained.constraintGradient_def,
      ContinuousLinearMap.innerSL_apply_comp] using
        haffine.norm_sq.const_mul (rho / 2)
  have hproximal : HasFDerivAt (fun q ↦ (beta / 2) * ‖q‖ ^ 2)
      ((beta / 2) • 2 • innerSL ℝ p) p := by
    simpa only [id_eq, ContinuousLinearMap.comp_id] using
      (hasFDerivAt_id p).norm_sq.const_mul (beta / 2)
  let modelDerivative : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ :=
    ((innerSL ℝ g +
        innerSL ℝ (EqualityConstrained.constraintGradient c x multiplier)) +
      ((rho / 2) • (2 • innerSL ℝ (EqualityConstrained.constraintGradient c x
        (c x + fderiv ℝ c x p))))) + ((beta / 2) • (2 • innerSL ℝ p))
  have hsum : HasFDerivAt
      ((((fun q ↦ ⟪g, q⟫_ℝ) +
          fun q ↦ ⟪multiplier, c x + fderiv ℝ c x q⟫_ℝ) +
          fun q ↦ (rho / 2) * ‖c x + fderiv ℝ c x q‖ ^ 2) +
        fun q ↦ (beta / 2) * ‖q‖ ^ 2) modelDerivative p := by
    simpa only [modelDerivative] using
      ((hobjective.add hmultiplier).add hpenalty).add hproximal
  have hderivativeEq : modelDerivative =
      innerSL ℝ (g + EqualityConstrained.constraintGradient c x
        (multiplier + rho • (c x + fderiv ℝ c x p)) + beta • p) := by
    ext v
    simp only [map_add, map_smul, innerSL_apply_apply, add_apply, smul_apply,
      EqualityConstrained.constraintGradient_def, modelDerivative]
    ring
  have hfunctions : stepModelWithGradient c g rho beta x multiplier =ᶠ[nhds p]
      ((((fun q ↦ ⟪g, q⟫_ℝ) +
          fun q ↦ ⟪multiplier, c x + fderiv ℝ c x q⟫_ℝ) +
          fun q ↦ (rho / 2) * ‖c x + fderiv ℝ c x q‖ ^ 2) +
        fun q ↦ (beta / 2) * ‖q‖ ^ 2) := by
    filter_upwards with q
    exact stepModelWithGradient_def c g rho beta x multiplier q
  exact (hsum.congr_of_eventuallyEq hfunctions).congr_fderiv hderivativeEq

/-- Helper for Theorem 3.6: a minimizer of the explicit-gradient model
satisfies its first-order normal equation. -/
private lemma explicitGradientModelOptimality
    (c : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m))
    (g : EuclideanSpace ℝ (Fin n)) (rho beta : ℝ)
    (x : EuclideanSpace ℝ (Fin n))
    (multiplier : EuclideanSpace ℝ (Fin m))
    (p : EuclideanSpace ℝ (Fin n))
    (hp : IsMinOn (stepModelWithGradient c g rho beta x multiplier) Set.univ p) :
    g + EqualityConstrained.constraintGradient c x
        (multiplier + rho • (c x + fderiv ℝ c x p)) + beta • p = 0 := by
  have hderiv : innerSL ℝ (g + EqualityConstrained.constraintGradient c x
      (multiplier + rho • (c x + fderiv ℝ c x p)) + beta • p) = 0 :=
    (hp.isLocalMin Filter.univ_mem).hasFDerivAt_eq_zero
      (hasFDerivAtExplicitGradientModel c g rho beta x multiplier p)
  have hnormSq :
      ‖g + EqualityConstrained.constraintGradient c x
        (multiplier + rho • (c x + fderiv ℝ c x p)) + beta • p‖ ^ 2 = 0 := by
    simpa only [innerSL_apply_apply, real_inner_self_eq_norm_sq, zero_apply] using
      congrArg (fun A ↦ A (g + EqualityConstrained.constraintGradient c x
        (multiplier + rho • (c x + fderiv ℝ c x p)) + beta • p)) hderiv
  exact norm_eq_zero.mp (sq_eq_zero_iff.mp hnormSq)

/-- Helper for Theorem 3.6: every minimizer of the explicit-gradient model is
the canonical inverse-based model step. -/
private lemma canonicalModelStep_eq_of_minimizes
    (c : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m))
    (rho beta : ℝ) (x g : EuclideanSpace ℝ (Fin n))
    (multiplier : EuclideanSpace ℝ (Fin m))
    (p : EuclideanSpace ℝ (Fin n)) (hrho : 0 < rho) (hbeta : 0 < beta)
    (hp : IsMinOn (stepModelWithGradient c g rho beta x multiplier)
      Set.univ p) :
    canonicalModelStep c rho beta x g multiplier = p := by
  have hoptimal := explicitGradientModelOptimality
    c g rho beta x multiplier p hp
  have hsum :
      (g + EqualityConstrained.constraintGradient c x
        (multiplier + rho • c x)) + modelStepOperator c rho beta x p = 0 := by
    simp only [modelStepOperator, add_apply, smul_apply,
      ContinuousLinearMap.id_apply,
      ContinuousLinearMap.comp_apply, map_add, map_smul] at hoptimal ⊢
    linear_combination (norm := module) hoptimal
  have hoperator : modelStepOperator c rho beta x p =
      -(g + EqualityConstrained.constraintGradient c x
        (multiplier + rho • c x)) :=
    eq_neg_of_add_eq_zero_right hsum
  unfold canonicalModelStep
  exact ((modelStepOperator_isInvertible c rho beta x hrho hbeta).inverse_apply_eq).2
    hoperator.symm

/-- Helper for Theorem 3.6: the canonical explicit-gradient step globally
minimizes its quadratic model. -/
private lemma canonicalModelStep_minimizes
    (c : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m))
    (rho beta : ℝ) (x g : EuclideanSpace ℝ (Fin n))
    (multiplier : EuclideanSpace ℝ (Fin m))
    (hrho : 0 < rho) (hbeta : 0 < beta) :
    IsMinOn (stepModelWithGradient c g rho beta x multiplier) Set.univ
      (canonicalModelStep c rho beta x g multiplier) := by
  let linearObjective : EuclideanSpace ℝ (Fin n) → ℝ :=
    fun y ↦ inner ℝ g y
  have hlinearDerivative :
      HasFDerivAt linearObjective (innerSL ℝ g) x := by
    simpa only [linearObjective, coe_innerSL_apply] using
      (innerSL ℝ g).hasFDerivAt
  have hlinearGradient : HasGradientAt linearObjective g x := by
    rw [hasGradientAt_iff_hasFDerivAt]
    exact hlinearDerivative
  have hgradient : gradient linearObjective x = g := hlinearGradient.gradient
  have hmodels :
      stepModel linearObjective c rho beta x multiplier =
        stepModelWithGradient c g rho beta x multiplier := by
    funext q
    rw [stepModel_eq_stepModelWithGradient, hgradient]
  obtain ⟨p, hp, _⟩ := LALM.Run.existsUniqueStepModelMinimizer
    linearObjective c rho beta x multiplier hrho hbeta
  have hpExplicit :
      IsMinOn (stepModelWithGradient c g rho beta x multiplier) Set.univ p := by
    simpa only [← hmodels] using hp
  have hcanonical : canonicalModelStep c rho beta x g multiplier = p :=
    canonicalModelStep_eq_of_minimizes c rho beta x g multiplier p
      hrho hbeta hpExplicit
  simpa only [hcanonical] using hpExplicit

/-- Helper for Theorem 3.6: the canonical model step depends measurably on its
point, gradient estimate, and multiplier. -/
private lemma measurable_canonicalModelStep
    (hc : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) c) (rho beta : ℝ)
    (hrho : 0 < rho) (hbeta : 0 < beta) :
    Measurable (fun z : EuclideanSpace ℝ (Fin n) ×
        (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin m)) ↦
      canonicalModelStep c rho beta z.1 z.2.1 z.2.2) := by
  have horderNe : ((⊤ : ℕ∞) : WithTop ℕ∞) ≠ 0 := by
    simp
  have hfderivContinuous : Continuous (fderiv ℝ c) :=
    hc.continuous_fderiv horderNe
  have hconstraintGradientContinuous :
      Continuous (EqualityConstrained.constraintGradient c) :=
    ContinuousLinearMap.adjoint.continuous.comp hfderivContinuous
  have hoperatorContinuous :
      Continuous (fun x ↦ modelStepOperator c rho beta x) := by
    unfold modelStepOperator
    exact (Continuous.const_smul continuous_const beta).add
      (Continuous.const_smul
        (hconstraintGradientContinuous.clm_comp hfderivContinuous) rho)
  have hinverseContinuous : Continuous
      (fun x ↦ (modelStepOperator c rho beta x).inverse) := by
    rw [continuous_iff_continuousAt]
    intro x
    exact ((modelStepOperator_isInvertible c rho beta x hrho hbeta)
      |>.contDiffAt_map_inverse (n := 0)).continuousAt.comp
        hoperatorContinuous.continuousAt
  have hrhsContinuous : Continuous (fun z : EuclideanSpace ℝ (Fin n) ×
      (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin m)) ↦
      -(z.2.1 + EqualityConstrained.constraintGradient c z.1
        (z.2.2 + rho • c z.1))) := by
    exact (continuous_fst.comp continuous_snd).add
      ((hconstraintGradientContinuous.comp continuous_fst).clm_apply
        ((continuous_snd.comp continuous_snd).add
          (Continuous.const_smul (hc.continuous.comp continuous_fst) rho))) |>.neg
  unfold canonicalModelStep
  exact ((hinverseContinuous.comp continuous_fst).clm_apply
    hrhsContinuous).measurable

/-- Helper for Theorem 3.6: a pre-batch state records the current and previous
points, the current multiplier, and the preceding raw estimate. -/
private abbrev PreBatchState :=
  EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) ×
    EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin n)

/-- Helper for Theorem 3.6: a pre-batch state and a fresh batch determine the
next raw SPIDER estimate. -/
private noncomputable def canonicalRawEstimateAt
    (oracle : EqualityConstrained.StochasticOracle f h.region ν)
    (Q B b : ℕ+) (k : ℕ)
    (point previousPoint previousRaw : EuclideanSpace ℝ (Fin n))
    (batch : ℕ → Ξ) : EuclideanSpace ℝ (Fin n) :=
  if k % Q = 0 then
    (B : ℝ)⁻¹ • ∑ i ∈ Finset.range B,
      oracle.sampleGradient point (batch i)
  else
    previousRaw + (b : ℝ)⁻¹ • ∑ i ∈ Finset.range b,
      (oracle.sampleGradient point (batch i) -
        oracle.sampleGradient previousPoint (batch i))

/-- Helper for Theorem 3.6: radial clipping is measurable on the
finite-dimensional gradient space. -/
private lemma measurable_spiderClip (G : ℝ≥0) :
    Measurable (SPIDER.clip G :
      EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) := by
  unfold SPIDER.clip
  apply Measurable.ite
  · exact measurableSet_le continuous_norm.measurable measurable_const
  · exact measurable_id
  · exact (measurable_const.div continuous_norm.measurable).smul measurable_id

/-- Helper for Theorem 3.6: the raw-estimate transition is measurable in the
pre-batch state and fresh batch. -/
private lemma measurable_canonicalRawEstimateAt
    (oracle : EqualityConstrained.StochasticOracle f h.region ν)
    (Q B b : ℕ+) (k : ℕ) :
    Measurable (fun z : PreBatchState (n := n) (m := m) × (ℕ → Ξ) ↦
      canonicalRawEstimateAt oracle Q B b k z.1.1 z.1.2.1
        z.1.2.2.2 z.2) := by
  have hpoint : Measurable (fun z :
      PreBatchState (n := n) (m := m) × (ℕ → Ξ) ↦ z.1.1) := by
    fun_prop
  have hpreviousPoint : Measurable (fun z :
      PreBatchState (n := n) (m := m) × (ℕ → Ξ) ↦ z.1.2.1) := by
    fun_prop
  have hpreviousRaw : Measurable (fun z :
      PreBatchState (n := n) (m := m) × (ℕ → Ξ) ↦ z.1.2.2.2) := by
    fun_prop
  have hsample (i : ℕ) : Measurable (fun z :
      PreBatchState (n := n) (m := m) × (ℕ → Ξ) ↦ z.2 i) :=
    (measurable_pi_apply i).comp measurable_snd
  by_cases hrefresh : k % Q = 0
  · simp only [canonicalRawEstimateAt, if_pos hrefresh]
    exact (Finset.measurable_sum (Finset.range B) fun i _ ↦
      oracle.measurable_sampleGradient.comp
        (hpoint.prodMk (hsample i))).const_smul ((B : ℝ)⁻¹)
  · simp only [canonicalRawEstimateAt, if_neg hrefresh]
    exact hpreviousRaw.add
      ((Finset.measurable_sum (Finset.range b) fun i _ ↦
        (oracle.measurable_sampleGradient.comp
            (hpoint.prodMk (hsample i))).sub
          (oracle.measurable_sampleGradient.comp
            (hpreviousPoint.prodMk (hsample i)))).const_smul ((b : ℝ)⁻¹))

/-- Helper for Theorem 3.6: the clipped estimate component is obtained from
the explicit raw-estimate transition. -/
private noncomputable def canonicalClippedEstimateAt
    (h : EqualityConstrained.Regularity f c)
    (oracle : EqualityConstrained.StochasticOracle f h.region ν)
    (Q B b : ℕ+) (k : ℕ)
    (z : PreBatchState (n := n) (m := m) × (ℕ → Ξ)) :
    EuclideanSpace ℝ (Fin n) :=
  SPIDER.clip h.gradientBound
    (canonicalRawEstimateAt oracle Q B b k z.1.1 z.1.2.1
      z.1.2.2.2 z.2)

/-- Helper for Theorem 3.6: the clipped-estimate component is measurable. -/
private lemma measurable_canonicalClippedEstimateAt (k : ℕ) :
    Measurable (canonicalClippedEstimateAt h oracle Q B b k) := by
  unfold canonicalClippedEstimateAt
  exact (measurable_spiderClip h.gradientBound).comp
    (measurable_canonicalRawEstimateAt oracle Q B b k)

/-- Helper for Theorem 3.6: the canonical model input groups the current
point, clipped estimate, and multiplier. -/
private noncomputable def canonicalModelInputAt
    (h : EqualityConstrained.Regularity f c)
    (oracle : EqualityConstrained.StochasticOracle f h.region ν)
    (Q B b : ℕ+) (k : ℕ)
    (z : PreBatchState (n := n) (m := m) × (ℕ → Ξ)) :
    EuclideanSpace ℝ (Fin n) ×
      (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin m)) :=
  (z.1.1, canonicalClippedEstimateAt h oracle Q B b k z,
    z.1.2.2.1)

/-- Helper for Theorem 3.6: the grouped canonical model input is measurable. -/
private lemma measurable_canonicalModelInputAt (k : ℕ) :
    Measurable (canonicalModelInputAt h oracle Q B b k) := by
  unfold canonicalModelInputAt
  have hpoint : Measurable (fun z :
      PreBatchState (n := n) (m := m) × (ℕ → Ξ) ↦ z.1.1) := by
    fun_prop
  have hmultiplier : Measurable (fun z :
      PreBatchState (n := n) (m := m) × (ℕ → Ξ) ↦ z.1.2.2.1) := by
    fun_prop
  exact hpoint.prodMk
    ((measurable_canonicalClippedEstimateAt k).prodMk hmultiplier)

/-- Helper for Theorem 3.6: the canonical step applies the measurable model
solver to the grouped pre-batch model input. -/
private noncomputable def canonicalStepAt
    (h : EqualityConstrained.Regularity f c)
    (oracle : EqualityConstrained.StochasticOracle f h.region ν)
    (params : Parameters h x₀ multiplier₀) (Q B b : ℕ+) (k : ℕ) :
    PreBatchState (n := n) (m := m) × (ℕ → Ξ) →
      EuclideanSpace ℝ (Fin n) :=
  (fun input : EuclideanSpace ℝ (Fin n) ×
      (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin m)) ↦
    canonicalModelStep c params.rho params.beta
      input.1 input.2.1 input.2.2) ∘
      canonicalModelInputAt h oracle Q B b k

/-- Helper for Theorem 3.6: the canonical step is measurable under the
explicit global smoothness hypothesis on `c`. -/
private lemma measurable_canonicalStepAt
    (hc : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) c) (k : ℕ) :
    Measurable (canonicalStepAt h oracle params Q B b k) := by
  unfold canonicalStepAt
  exact (measurable_canonicalModelStep hc params.rho params.beta
    params.spec.1.2.2.1 params.spec.1.2.1).comp
      (measurable_canonicalModelInputAt k)

/-- Helper for Theorem 3.6: the canonical next point adds the model step to
the current point. -/
private noncomputable def canonicalNextPointAt
    (h : EqualityConstrained.Regularity f c)
    (oracle : EqualityConstrained.StochasticOracle f h.region ν)
    (params : Parameters h x₀ multiplier₀) (Q B b : ℕ+) (k : ℕ)
    (z : PreBatchState (n := n) (m := m) × (ℕ → Ξ)) :
    EuclideanSpace ℝ (Fin n) :=
  z.1.1 + canonicalStepAt h oracle params Q B b k z

/-- Helper for Theorem 3.6: the canonical next-point component is measurable. -/
private lemma measurable_canonicalNextPointAt
    (hc : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) c) (k : ℕ) :
    Measurable (canonicalNextPointAt h oracle params Q B b k) := by
  unfold canonicalNextPointAt
  have hpoint : Measurable (fun z :
      PreBatchState (n := n) (m := m) × (ℕ → Ξ) ↦ z.1.1) := by
    fun_prop
  exact hpoint.add (measurable_canonicalStepAt hc k)

/-- Helper for Theorem 3.6: the canonical next multiplier performs the LALM
dual update at the new point. -/
private noncomputable def canonicalNextMultiplierAt
    (h : EqualityConstrained.Regularity f c)
    (oracle : EqualityConstrained.StochasticOracle f h.region ν)
    (params : Parameters h x₀ multiplier₀) (Q B b : ℕ+) (k : ℕ)
    (z : PreBatchState (n := n) (m := m) × (ℕ → Ξ)) :
    EuclideanSpace ℝ (Fin m) :=
  z.1.2.2.1 + (params.toAdmissibleParameters.rho : ℝ) •
    c (canonicalNextPointAt h oracle params Q B b k z)

/-- Helper for Theorem 3.6: the canonical next-multiplier component is
measurable under the explicit global smoothness hypothesis on `c`. -/
private lemma measurable_canonicalNextMultiplierAt
    (hc : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) c) (k : ℕ) :
    Measurable (canonicalNextMultiplierAt h oracle params Q B b k) := by
  unfold canonicalNextMultiplierAt
  have hmultiplier : Measurable (fun z :
      PreBatchState (n := n) (m := m) × (ℕ → Ξ) ↦ z.1.2.2.1) := by
    fun_prop
  exact hmultiplier.add
    ((hc.continuous.measurable.comp
      (measurable_canonicalNextPointAt hc k)).const_smul (params.rho : ℝ))

/-- Helper for Theorem 3.6: one fresh batch advances the complete numerical
pre-batch state. -/
private noncomputable def canonicalTransition
    (h : EqualityConstrained.Regularity f c)
    (oracle : EqualityConstrained.StochasticOracle f h.region ν)
    (params : Parameters h x₀ multiplier₀) (Q B b : ℕ+) (k : ℕ)
    (z : PreBatchState (n := n) (m := m) × (ℕ → Ξ)) :
    PreBatchState (n := n) (m := m) :=
  (canonicalNextPointAt h oracle params Q B b k z, z.1.1,
    canonicalNextMultiplierAt h oracle params Q B b k z,
    canonicalRawEstimateAt oracle Q B b k z.1.1 z.1.2.1
      z.1.2.2.2 z.2)

/-- Helper for Theorem 3.6: the complete one-batch numerical transition is
measurable under the explicit global smoothness hypothesis on `c`. -/
private lemma measurable_canonicalTransition
    (hc : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) c) (k : ℕ) :
    Measurable (canonicalTransition h oracle params Q B b k) := by
  unfold canonicalTransition
  have hpoint : Measurable (fun z :
      PreBatchState (n := n) (m := m) × (ℕ → Ξ) ↦ z.1.1) := by
    fun_prop
  exact (measurable_canonicalNextPointAt hc k).prodMk
    (hpoint.prodMk ((measurable_canonicalNextMultiplierAt hc k).prodMk
      (measurable_canonicalRawEstimateAt oracle Q B b k)))

/-- Helper for Theorem 3.6: the pre-batch state at time `k` is recursively
generated from exactly the batches with time index below `k`. -/
private noncomputable def canonicalPreBatchState
    (h : EqualityConstrained.Regularity f c)
    (oracle : EqualityConstrained.StochasticOracle f h.region ν)
    (params : Parameters h x₀ multiplier₀) (Q B b : ℕ+) :
    (k : ℕ) → (Fin k → ℕ → Ξ) → PreBatchState (n := n) (m := m)
  | 0, _ => (x₀, x₀, multiplier₀, 0)
  | k + 1, samples =>
      canonicalTransition h oracle params Q B b k
        (canonicalPreBatchState h oracle params Q B b k
          (fun t i ↦ samples t.castSucc i), samples (Fin.last k))

/-- Helper for Theorem 3.6: the canonical pre-batch state is measurable as a
function of its finite sample history. -/
private lemma measurable_canonicalPreBatchState
    (hc : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) c) (k : ℕ) :
    Measurable (canonicalPreBatchState h oracle params Q B b k) := by
  induction k with
  | zero =>
      simpa only [canonicalPreBatchState] using
        (measurable_const : Measurable (fun _ : Fin 0 → ℕ → Ξ ↦
          ((x₀, x₀, multiplier₀, 0) :
            PreBatchState (n := n) (m := m))))
  | succ k ih =>
      let restrictHistory : (Fin (k + 1) → ℕ → Ξ) → Fin k → ℕ → Ξ :=
        fun samples t i ↦ samples t.castSucc i
      have hrestrictHistory : Measurable restrictHistory := by
        apply measurable_pi_lambda
        intro t
        apply measurable_pi_lambda
        intro i
        exact (measurable_pi_apply i).comp (measurable_pi_apply t.castSucc)
      have hstate : Measurable (fun samples ↦
          canonicalPreBatchState h oracle params Q B b k
            (restrictHistory samples)) :=
        ih.comp hrestrictHistory
      have hbatch : Measurable (fun samples : Fin (k + 1) → ℕ → Ξ ↦
          samples (Fin.last k)) := measurable_pi_apply (Fin.last k)
      simpa only [canonicalPreBatchState, restrictHistory,
        Function.comp_def] using
        (measurable_canonicalTransition (h := h) (oracle := oracle)
          (params := params) (Q := Q) (B := B) (b := b) hc k).comp
            (hstate.prodMk hbatch)

/-- Helper for Theorem 3.6: the finite history at time `k` consists of the
canonical coordinate batches with time index below `k`. -/
private def sampleHistory (k : ℕ) (omega : CanonicalSampleSpace Ξ)
    (t : Fin k) (i : ℕ) : Ξ :=
  sample (Ξ := Ξ) t i omega

/-- Helper for Theorem 3.6: every finite canonical sample history is
measurable. -/
private lemma measurable_sampleHistory (k : ℕ) :
    Measurable (sampleHistory (Ξ := Ξ) k) := by
  apply measurable_pi_lambda
  intro t
  apply measurable_pi_lambda
  intro i
  exact measurable_pi_apply ((t : ℕ), i)

/-- Helper for Theorem 3.6: the fresh batch at time `k` is the corresponding
row of the canonical coordinate array. -/
private def sampleBatch (k : ℕ) (omega : CanonicalSampleSpace Ξ) (i : ℕ) : Ξ :=
  sample (Ξ := Ξ) k i omega

/-- Helper for Theorem 3.6: every fresh canonical sample batch is measurable. -/
private lemma measurable_sampleBatch (k : ℕ) :
    Measurable (sampleBatch (Ξ := Ξ) k) := by
  apply measurable_pi_lambda
  intro i
  exact measurable_pi_apply (k, i)

/-- Helper for Theorem 3.6: evaluating the finite-history recursion on the
canonical coordinate array gives the numerical pre-batch state. -/
private noncomputable def state
    (h : EqualityConstrained.Regularity f c)
    (oracle : EqualityConstrained.StochasticOracle f h.region ν)
    (params : Parameters h x₀ multiplier₀) (Q B b : ℕ+) (k : ℕ) :
    CanonicalSampleSpace Ξ → PreBatchState (n := n) (m := m) :=
  canonicalPreBatchState h oracle params Q B b k ∘ sampleHistory k

/-- Helper for Theorem 3.6: every canonical pre-batch state is measurable
under the explicit global smoothness hypothesis on `c`. -/
private lemma measurable_state
    (hc : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) c) (k : ℕ) :
    Measurable (state h oracle params Q B b k) := by
  unfold state
  exact (measurable_canonicalPreBatchState hc k).comp
    (measurable_sampleHistory k)

/-- Helper for Theorem 3.6: the canonical primal sequence is the current-point
projection of the pre-batch state. -/
private noncomputable def point
    (h : EqualityConstrained.Regularity f c)
    (oracle : EqualityConstrained.StochasticOracle f h.region ν)
    (params : Parameters h x₀ multiplier₀) (Q B b : ℕ+) (k : ℕ)
    (omega : CanonicalSampleSpace Ξ) : EuclideanSpace ℝ (Fin n) :=
  (state h oracle params Q B b k omega).1

/-- Helper for Theorem 3.6: the preceding-point projection stored in the
canonical pre-batch state. -/
private noncomputable def previousPoint
    (h : EqualityConstrained.Regularity f c)
    (oracle : EqualityConstrained.StochasticOracle f h.region ν)
    (params : Parameters h x₀ multiplier₀) (Q B b : ℕ+) (k : ℕ)
    (omega : CanonicalSampleSpace Ξ) : EuclideanSpace ℝ (Fin n) :=
  (state h oracle params Q B b k omega).2.1

/-- Helper for Theorem 3.6: the canonical multiplier sequence is the
multiplier projection of the pre-batch state. -/
private noncomputable def multiplier
    (h : EqualityConstrained.Regularity f c)
    (oracle : EqualityConstrained.StochasticOracle f h.region ν)
    (params : Parameters h x₀ multiplier₀) (Q B b : ℕ+) (k : ℕ)
    (omega : CanonicalSampleSpace Ξ) : EuclideanSpace ℝ (Fin m) :=
  (state h oracle params Q B b k omega).2.2.1

/-- Helper for Theorem 3.6: the preceding raw-estimate projection stored in
the canonical pre-batch state. -/
private noncomputable def previousRawEstimate
    (h : EqualityConstrained.Regularity f c)
    (oracle : EqualityConstrained.StochasticOracle f h.region ν)
    (params : Parameters h x₀ multiplier₀) (Q B b : ℕ+) (k : ℕ)
    (omega : CanonicalSampleSpace Ξ) : EuclideanSpace ℝ (Fin n) :=
  (state h oracle params Q B b k omega).2.2.2

/-- Helper for Theorem 3.6: the canonical primal step applies the model solver
to the pre-batch state and current sample batch. -/
private noncomputable def step
    (h : EqualityConstrained.Regularity f c)
    (oracle : EqualityConstrained.StochasticOracle f h.region ν)
    (params : Parameters h x₀ multiplier₀) (Q B b : ℕ+) (k : ℕ)
    (omega : CanonicalSampleSpace Ξ) : EuclideanSpace ℝ (Fin n) :=
  canonicalStepAt h oracle params Q B b k
    (state h oracle params Q B b k omega, sampleBatch k omega)

/-- Helper for Theorem 3.6: the canonical state at a successor time is the
one-batch transition from the preceding state. -/
private lemma state_succ (k : ℕ) (omega : CanonicalSampleSpace Ξ) :
    state h oracle params Q B b (k + 1) omega =
      canonicalTransition h oracle params Q B b k
        (state h oracle params Q B b k omega, sampleBatch k omega) := by
  have hhistory :
      (fun t : Fin k ↦ fun i ↦ sampleHistory (k + 1) omega t.castSucc i) =
        sampleHistory k omega := by
    funext t i
    rfl
  have hbatch : sampleHistory (k + 1) omega (Fin.last k) =
      sampleBatch k omega := by
    funext i
    simp only [sampleHistory, sampleBatch, sample, Fin.val_last]
  unfold state
  simp only [Function.comp_apply, canonicalPreBatchState]
  rw [hhistory, hbatch]

/-- Helper for Theorem 3.6: the explicit raw transition evaluated on the
canonical state equals the public recursive SPIDER raw estimate. -/
private lemma canonicalRawEstimate_eq_rawEstimate
    (k : ℕ) (omega : CanonicalSampleSpace Ξ) :
    canonicalRawEstimateAt oracle Q B b k
        (point h oracle params Q B b k omega)
        (previousPoint h oracle params Q B b k omega)
        (previousRawEstimate h oracle params Q B b k omega)
        (sampleBatch k omega) =
      SPIDER.rawEstimate oracle (point h oracle params Q B b)
        (sample (Ξ := Ξ)) Q B b k omega := by
  induction k with
  | zero =>
      simp only [canonicalRawEstimateAt, Nat.zero_mod, if_true,
        SPIDER.rawEstimate, point, state, sampleBatch, sample,
        canonicalPreBatchState, Function.comp_apply]
  | succ k ih =>
      by_cases hrefresh : (k + 1) % Q = 0
      · rw [canonicalRawEstimateAt, if_pos hrefresh,
          SPIDER.rawEstimate_of_refresh oracle (point h oracle params Q B b)
            (sample (Ξ := Ξ)) Q B b (k + 1) omega hrefresh]
        rfl
      · rw [canonicalRawEstimateAt, if_neg hrefresh,
          SPIDER.rawEstimate_of_update oracle (point h oracle params Q B b)
            (sample (Ξ := Ξ)) Q B b k omega hrefresh]
        have ihState :
            canonicalRawEstimateAt oracle Q B b k
                (state h oracle params Q B b k omega).1
                (state h oracle params Q B b k omega).2.1
                (state h oracle params Q B b k omega).2.2.2
                (sampleBatch k omega) =
              SPIDER.rawEstimate oracle (point h oracle params Q B b)
                (sample (Ξ := Ξ)) Q B b k omega := by
          simpa only [point, previousPoint, previousRawEstimate] using ih
        unfold previousRawEstimate previousPoint
        rw [state_succ]
        simp only [canonicalTransition, point]
        rw [ihState]
        rfl

/-- Helper for Theorem 3.6: the preceding-point state projection is the
previous member of the canonical primal sequence. -/
private lemma previousPoint_eq_point_pred
    (k : ℕ) (omega : CanonicalSampleSpace Ξ) :
    previousPoint h oracle params Q B b k omega =
      point h oracle params Q B b (k - 1) omega := by
  cases k with
  | zero =>
      rw [Nat.zero_sub]
      rfl
  | succ k =>
      rw [previousPoint, state_succ]
      simp only [canonicalTransition, point, Nat.add_sub_cancel]

/-- Helper for Theorem 3.6: the preceding raw-estimate state projection is
zero initially and otherwise equals the previous public SPIDER estimate. -/
private lemma previousRawEstimate_eq
    (k : ℕ) (omega : CanonicalSampleSpace Ξ) :
    previousRawEstimate h oracle params Q B b k omega =
      if k = 0 then 0 else
        SPIDER.rawEstimate oracle (point h oracle params Q B b)
          (sample (Ξ := Ξ)) Q B b (k - 1) omega := by
  cases k with
  | zero =>
      simp only [previousRawEstimate, state,
        canonicalPreBatchState, Function.comp_apply, if_true]
  | succ k =>
      rw [previousRawEstimate, state_succ]
      simp only [canonicalTransition, Nat.succ_ne_zero, if_false,
        Nat.add_sub_cancel]
      exact canonicalRawEstimate_eq_rawEstimate k omega

/-- Helper for Theorem 3.6: the canonical pre-batch state is exactly the tuple
required by `StochasticRun.independent_preBatchState_sample`. -/
private lemma state_eq_preBatchTuple
    (k : ℕ) (omega : CanonicalSampleSpace Ξ) :
    state h oracle params Q B b k omega =
      (point h oracle params Q B b k omega,
        point h oracle params Q B b (k - 1) omega,
        multiplier h oracle params Q B b k omega,
        if k = 0 then 0 else
          SPIDER.rawEstimate oracle (point h oracle params Q B b)
            (sample (Ξ := Ξ)) Q B b (k - 1) omega) := by
  rw [← previousPoint_eq_point_pred k omega,
    ← previousRawEstimate_eq k omega]
  rfl

/-- Helper for Theorem 3.6: the canonical primal sequence starts at `x₀`. -/
private lemma point_zero (omega : CanonicalSampleSpace Ξ) :
    point h oracle params Q B b 0 omega = x₀ := by
  rfl

/-- Helper for Theorem 3.6: the canonical multiplier sequence starts at
`multiplier₀`. -/
private lemma multiplier_zero (omega : CanonicalSampleSpace Ξ) :
    multiplier h oracle params Q B b 0 omega = multiplier₀ := by
  rfl

/-- Helper for Theorem 3.6: every canonical primal step minimizes the model
driven by the projected public SPIDER estimate. -/
private lemma minimizes_step (k : ℕ) (omega : CanonicalSampleSpace Ξ) :
    IsMinOn (stepModelWithGradient c
      (SPIDER.estimate h.gradientBound oracle
        (point h oracle params Q B b) (sample (Ξ := Ξ)) Q B b k omega)
      (PositivePenaltyParameters.rho params)
      (PositivePenaltyParameters.beta params)
      (point h oracle params Q B b k omega)
      (multiplier h oracle params Q B b k omega)) Set.univ
      (step h oracle params Q B b k omega) := by
  have hraw := canonicalRawEstimate_eq_rawEstimate
    (h := h) (oracle := oracle) (params := params) (Q := Q) (B := B) (b := b)
    k omega
  have hrawState :
      canonicalRawEstimateAt oracle Q B b k
          (state h oracle params Q B b k omega).1
          (state h oracle params Q B b k omega).2.1
          (state h oracle params Q B b k omega).2.2.2
          (sampleBatch k omega) =
        SPIDER.rawEstimate oracle (point h oracle params Q B b)
          (sample (Ξ := Ξ)) Q B b k omega := by
    simpa only [point, previousPoint, previousRawEstimate] using hraw
  unfold step canonicalStepAt canonicalModelInputAt canonicalClippedEstimateAt
  simp only [Function.comp_apply, point, multiplier,
    positivePenaltyParameters_rho, positivePenaltyParameters_beta,
    SPIDER.estimate_apply]
  rw [hrawState]
  exact canonicalModelStep_minimizes c params.rho params.beta
    _ _ _ params.spec.1.2.2.1 params.spec.1.2.1

/-- Helper for Theorem 3.6: the canonical primal sequence advances by its
stored step. -/
private lemma point_succ (k : ℕ) (omega : CanonicalSampleSpace Ξ) :
    point h oracle params Q B b (k + 1) omega =
      point h oracle params Q B b k omega +
        step h oracle params Q B b k omega := by
  rw [point, state_succ]
  rfl

/-- Helper for Theorem 3.6: the canonical multiplier sequence performs the
classical LALM dual update. -/
private lemma multiplier_succ (k : ℕ) (omega : CanonicalSampleSpace Ξ) :
    multiplier h oracle params Q B b (k + 1) omega =
      multiplier h oracle params Q B b k omega +
        PositivePenaltyParameters.rho params •
          c (point h oracle params Q B b (k + 1) omega) := by
  rw [multiplier, state_succ]
  simp only [canonicalTransition, canonicalNextMultiplierAt,
    positivePenaltyParameters_rho]
  rw [point_succ]
  rfl

/-- Helper for Theorem 3.6: every canonical primal point is measurable under
the explicit global smoothness hypothesis on `c`. -/
private lemma measurable_point
    (hc : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) c) (k : ℕ) :
    Measurable (point h oracle params Q B b k) := by
  unfold point
  exact measurable_fst.comp (measurable_state hc k)

/-- Helper for Theorem 3.6: every canonical multiplier is measurable under
the explicit global smoothness hypothesis on `c`. -/
private lemma measurable_multiplier
    (hc : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) c) (k : ℕ) :
    Measurable (multiplier h oracle params Q B b k) := by
  unfold multiplier
  exact (measurable_fst.comp (measurable_snd.comp measurable_snd)).comp
    (measurable_state hc k)

/-- Helper for Theorem 3.6: every canonical primal step is measurable under
the explicit global smoothness hypothesis on `c`. -/
private lemma measurable_step
    (hc : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) c) (k : ℕ) :
    Measurable (step h oracle params Q B b k) := by
  unfold step
  exact (measurable_canonicalStepAt hc k).comp
    ((measurable_state hc k).prodMk (measurable_sampleBatch k))

/-- Helper for Theorem 3.6: every public raw SPIDER estimate generated by the
canonical recursion is measurable. -/
private lemma measurable_rawEstimate
    (hc : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) c) (k : ℕ) :
    Measurable (SPIDER.rawEstimate oracle (point h oracle params Q B b)
      (sample (Ξ := Ξ)) Q B b k) := by
  induction k with
  | zero =>
      simp only [SPIDER.rawEstimate]
      exact (Finset.measurable_sum (Finset.range B) fun i _ ↦
        oracle.measurable_sampleGradient.comp
          ((measurable_point (h := h) (oracle := oracle) (params := params)
            (Q := Q) (B := B) (b := b) hc 0).prodMk
              (measurable_sample (Ξ := Ξ) 0 i))).const_smul ((B : ℝ)⁻¹)
  | succ k ih =>
      by_cases hrefresh : (k + 1) % Q = 0
      · simp only [SPIDER.rawEstimate, if_pos hrefresh]
        exact (Finset.measurable_sum (Finset.range B) fun i _ ↦
          oracle.measurable_sampleGradient.comp
            ((measurable_point (h := h) (oracle := oracle) (params := params)
              (Q := Q) (B := B) (b := b) hc (k + 1)).prodMk
                (measurable_sample (Ξ := Ξ) (k + 1) i))).const_smul ((B : ℝ)⁻¹)
      · simp only [SPIDER.rawEstimate, if_neg hrefresh]
        exact ih.add
          ((Finset.measurable_sum (Finset.range b) fun i _ ↦
            (oracle.measurable_sampleGradient.comp
                ((measurable_point (h := h) (oracle := oracle) (params := params)
                  (Q := Q) (B := B) (b := b) hc (k + 1)).prodMk
                    (measurable_sample (Ξ := Ξ) (k + 1) i))).sub
              (oracle.measurable_sampleGradient.comp
                ((measurable_point (h := h) (oracle := oracle) (params := params)
                  (Q := Q) (B := B) (b := b) hc k).prodMk
                    (measurable_sample (Ξ := Ξ) (k + 1) i)))).const_smul
              ((b : ℝ)⁻¹))

/-- Helper for Theorem 3.6: the sigma-algebra of one canonical coordinate is
the oracle sigma-algebra pulled back by its coordinate projection. -/
private abbrev sampleCoordinateSigma (ki : ℕ × ℕ) :
    MeasurableSpace (CanonicalSampleSpace Ξ) :=
  (inferInstance : MeasurableSpace Ξ).comap
    (sample (Ξ := Ξ) ki.1 ki.2)

/-- Helper for Theorem 3.6: every coordinate sigma-algebra lies below the
ambient product sigma-algebra. -/
private lemma sampleCoordinateSigma_le (ki : ℕ × ℕ) :
    sampleCoordinateSigma (Ξ := Ξ) ki ≤
      (inferInstance : MeasurableSpace (CanonicalSampleSpace Ξ)) := by
  unfold sampleCoordinateSigma
  exact (measurable_sample (Ξ := Ξ) ki.1 ki.2).comap_le

/-- Helper for Theorem 3.6: the coordinate sigma-algebras of the canonical
product space are mutually independent. -/
private lemma iIndep_sampleCoordinateSigma :
    ProbabilityTheory.iIndep
      (fun ki : ℕ × ℕ ↦ sampleCoordinateSigma (Ξ := Ξ) ki)
      (canonicalProductMeasure ν) := by
  simpa only [sampleCoordinateSigma] using
    (sample_iIndepFun (Ξ := Ξ) (ν := ν)).iIndep

/-- Helper for Theorem 3.6: the past coordinate set consists of all sample
indices whose time component is strictly below `k`. -/
private def pastSampleIndexSet (k : ℕ) : Set (ℕ × ℕ) :=
  {ki | ki.1 < k}

/-- Helper for Theorem 3.6: the current coordinate set consists of the entire
sample row at time `k`. -/
private def currentSampleIndexSet (k : ℕ) : Set (ℕ × ℕ) :=
  {ki | ki.1 = k}

/-- Helper for Theorem 3.6: past and current sample-coordinate sets are
disjoint. -/
private lemma pastSampleIndexSet_disjoint_currentSampleIndexSet (k : ℕ) :
    Disjoint (pastSampleIndexSet k) (currentSampleIndexSet k) := by
  rw [Set.disjoint_left]
  rintro ⟨t, i⟩ htPast htCurrent
  simp only [pastSampleIndexSet, Set.mem_setOf_eq] at htPast
  simp only [currentSampleIndexSet, Set.mem_setOf_eq] at htCurrent
  omega

/-- Helper for Theorem 3.6: the past sigma-algebra is generated by all
coordinate samples whose time index is below `k`. -/
private abbrev pastSampleSigma (k : ℕ) :
    MeasurableSpace (CanonicalSampleSpace Ξ) :=
  ⨆ ki ∈ pastSampleIndexSet k, sampleCoordinateSigma (Ξ := Ξ) ki

/-- Helper for Theorem 3.6: the current-batch sigma-algebra is generated by
all coordinate samples in the row at time `k`. -/
private abbrev currentSampleSigma (k : ℕ) :
    MeasurableSpace (CanonicalSampleSpace Ξ) :=
  ⨆ ki ∈ currentSampleIndexSet k, sampleCoordinateSigma (Ξ := Ξ) ki

/-- Helper for Theorem 3.6: the finite sample history is measurable with
respect to the sigma-algebra generated by past coordinates. -/
private lemma measurable_sampleHistory_past (k : ℕ) :
    Measurable[pastSampleSigma (Ξ := Ξ) k]
      (sampleHistory (Ξ := Ξ) k) := by
  apply Measurable.of_comap_le
  rw [MeasurableSpace.comap_process_pi]
  apply iSup_le
  intro t
  rw [MeasurableSpace.comap_process_pi]
  apply iSup_le
  intro i
  have hmem : ((t : ℕ), i) ∈ pastSampleIndexSet k := by
    simp only [pastSampleIndexSet, Set.mem_setOf_eq]
    exact t.isLt
  unfold sampleHistory pastSampleSigma sampleCoordinateSigma sample
  exact le_iSup_of_le ((t : ℕ), i) (le_iSup_of_le hmem le_rfl)

/-- Helper for Theorem 3.6: the fresh sample batch is measurable with respect
to the sigma-algebra generated by its current coordinate row. -/
private lemma measurable_sampleBatch_current (k : ℕ) :
    Measurable[currentSampleSigma (Ξ := Ξ) k]
      (sampleBatch (Ξ := Ξ) k) := by
  apply Measurable.of_comap_le
  rw [MeasurableSpace.comap_process_pi]
  apply iSup_le
  intro i
  have hmem : (k, i) ∈ currentSampleIndexSet k := by
    simp only [currentSampleIndexSet, Set.mem_setOf_eq]
  unfold sampleBatch currentSampleSigma sampleCoordinateSigma sample
  exact le_iSup_of_le (k, i) (le_iSup_of_le hmem le_rfl)

/-- Helper for Theorem 3.6: the canonical finite past history is independent
of the current fresh sample batch. -/
private lemma indepFun_sampleHistory_sampleBatch (k : ℕ) :
    ProbabilityTheory.IndepFun (sampleHistory (Ξ := Ξ) k)
      (sampleBatch (Ξ := Ξ) k) (canonicalProductMeasure ν) := by
  have hgrouped : ProbabilityTheory.Indep
      (pastSampleSigma (Ξ := Ξ) k) (currentSampleSigma (Ξ := Ξ) k)
      (canonicalProductMeasure ν) := by
    unfold pastSampleSigma currentSampleSigma
    exact ProbabilityTheory.indep_iSup_of_disjoint
      (sampleCoordinateSigma_le (Ξ := Ξ))
      (iIndep_sampleCoordinateSigma (Ξ := Ξ) (ν := ν))
      (pastSampleIndexSet_disjoint_currentSampleIndexSet k)
  unfold ProbabilityTheory.IndepFun
  exact ProbabilityTheory.indep_of_indep_of_le hgrouped
    (measurable_sampleHistory_past (Ξ := Ξ) k).comap_le
    (measurable_sampleBatch_current (Ξ := Ξ) k).comap_le

/-- Helper for Theorem 3.6: the canonical state determined by past batches is
independent of the fresh batch at time `k`. -/
private lemma indepFun_state_sampleBatch
    (hc : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) c) (k : ℕ) :
    ProbabilityTheory.IndepFun (state h oracle params Q B b k)
      (sampleBatch (Ξ := Ξ) k) (canonicalProductMeasure ν) := by
  have hindependent : ProbabilityTheory.IndepFun
      (canonicalPreBatchState h oracle params Q B b k ∘ sampleHistory k)
      (id ∘ sampleBatch k) (canonicalProductMeasure ν) :=
    (indepFun_sampleHistory_sampleBatch (Ξ := Ξ) (ν := ν) k).comp
      (measurable_canonicalPreBatchState hc k) measurable_id
  simpa only [state, Function.comp_def, id_eq] using hindependent

/-- Helper for Theorem 3.6: the exact pre-batch tuple required by a stochastic
run is independent of the fresh coordinate batch. -/
private lemma independent_preBatchState_sample
    (hc : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) c) (k : ℕ) :
    ProbabilityTheory.IndepFun
      (fun omega : CanonicalSampleSpace Ξ ↦
        (point h oracle params Q B b k omega,
          point h oracle params Q B b (k - 1) omega,
          multiplier h oracle params Q B b k omega,
          if k = 0 then 0 else
            SPIDER.rawEstimate oracle (point h oracle params Q B b)
              (sample (Ξ := Ξ)) Q B b (k - 1) omega))
      (fun omega i ↦ sample (Ξ := Ξ) k i omega)
      (canonicalProductMeasure ν) := by
  have hstate :
      (fun omega : CanonicalSampleSpace Ξ ↦
        (point h oracle params Q B b k omega,
          point h oracle params Q B b (k - 1) omega,
          multiplier h oracle params Q B b k omega,
          if k = 0 then 0 else
            SPIDER.rawEstimate oracle (point h oracle params Q B b)
              (sample (Ξ := Ξ)) Q B b (k - 1) omega)) =
        state h oracle params Q B b k := by
    funext omega
    exact (state_eq_preBatchTuple k omega).symm
  rw [hstate]
  exact indepFun_state_sampleBatch hc k

/-- Helper for Theorem 3.6: canonical raw estimates are almost everywhere
measurable under the product law. -/
private lemma aemeasurable_rawEstimate
    (hc : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) c) (k : ℕ) :
    AEMeasurable (SPIDER.rawEstimate oracle (point h oracle params Q B b)
      (sample (Ξ := Ξ)) Q B b k) (canonicalProductMeasure ν) :=
  (measurable_rawEstimate hc k).aemeasurable

/-- Helper for Theorem 3.6: canonical primal points are almost everywhere
measurable under the product law. -/
private lemma aemeasurable_point
    (hc : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) c) (k : ℕ) :
    AEMeasurable (point h oracle params Q B b k)
      (canonicalProductMeasure ν) :=
  (measurable_point hc k).aemeasurable

/-- Helper for Theorem 3.6: canonical multipliers are almost everywhere
measurable under the product law. -/
private lemma aemeasurable_multiplier
    (hc : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) c) (k : ℕ) :
    AEMeasurable (multiplier h oracle params Q B b k)
      (canonicalProductMeasure ν) :=
  (measurable_multiplier hc k).aemeasurable

/-- Helper for Theorem 3.6: canonical model steps are almost everywhere
measurable under the product law. -/
private lemma aemeasurable_step
    (hc : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) c) (k : ℕ) :
    AEMeasurable (step h oracle params Q B b k)
      (canonicalProductMeasure ν) :=
  (measurable_step hc k).aemeasurable

/-- Helper for Theorem 3.6: the explicit canonical finite-history stochastic
run on the product sample space. -/
noncomputable def stochasticRun
    (hc : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) c) :
    StochasticRun h oracle (canonicalProductMeasure ν)
      x₀ multiplier₀ params Q B b :=
  { sample := sample
    point := point h oracle params Q B b
    multiplier := multiplier h oracle params Q B b
    step := step h oracle params Q B b
    hasLaw_sample := sample_hasLaw
    independent_sample := sample_iIndepFun
    independent_preBatchState_sample :=
      independent_preBatchState_sample hc
    aemeasurable_rawEstimate := aemeasurable_rawEstimate hc
    aemeasurable_point := aemeasurable_point hc
    aemeasurable_multiplier := aemeasurable_multiplier hc
    aemeasurable_step := aemeasurable_step hc
    point_zero := point_zero
    multiplier_zero := multiplier_zero
    minimizes_step := minimizes_step
    point_succ := point_succ
    multiplier_succ := multiplier_succ }

/-- Helper for Theorem 3.6: the canonical run reads the corresponding product
coordinate at every iteration and batch position. -/
@[simp] theorem stochasticRun_sample
    (hc : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) c) :
    (stochasticRun (h := h) (oracle := oracle) (params := params)
      (Q := Q) (B := B) (b := b) hc).sample = sample := by
  rfl

/-- Helper for Theorem 3.6: the canonical product space supports a stochastic
run for arbitrary positive refresh and batch sizes. -/
theorem stochasticRun_nonempty
    (hc : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) c) :
    Nonempty (StochasticRun h oracle (canonicalProductMeasure ν)
      x₀ multiplier₀ params Q B b) := by
  exact ⟨stochasticRun hc⟩

end CanonicalRun

/-- Theorem 3.6: a canonical realization consists of the product probability
law on `(ℕ × ℕ) → Ξ` together with the measurable finite-history LALM run
driven by its iid coordinate samples. -/
structure CanonicalRealization
    (h : EqualityConstrained.Regularity f c)
    (oracle : EqualityConstrained.StochasticOracle f h.region ν)
    (x₀ : EuclideanSpace ℝ (Fin n))
    (multiplier₀ : EuclideanSpace ℝ (Fin m))
    (params : Parameters h x₀ multiplier₀) (Q B b : ℕ+) where
  /-- The LALM stochastic run on the canonical infinite-product sample space. -/
  run : StochasticRun h oracle (canonicalProductMeasure ν)
    x₀ multiplier₀ params Q B b

/-- Helper for Theorem 3.6: the canonical finite-history construction yields
a realization for arbitrary positive refresh and batch sizes. -/
noncomputable def canonicalRealization
    (hc : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) c) :
    CanonicalRealization h oracle x₀ multiplier₀ params Q B b :=
  CanonicalRealization.mk (CanonicalRun.stochasticRun hc)

/-- Helper for Theorem 3.6: the type of canonical realizations is nonempty
under the explicit global smoothness condition used by the solver. -/
theorem canonicalRealization_nonempty
    (hc : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) c) :
    Nonempty (CanonicalRealization h oracle x₀ multiplier₀ params Q B b) := by
  exact ⟨canonicalRealization hc⟩

/-- Helper for Theorem 3.6: specializing the generic construction to the
horizon-dependent SPIDER schedule gives a canonical scheduled run. -/
noncomputable def canonicalScheduledRun
    (hc : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) c) (K : ℕ) :
    SPIDER.ScheduledRun h oracle (canonicalProductMeasure ν)
      x₀ multiplier₀ params K :=
  CanonicalRun.stochasticRun
    (Q := SPIDER.refreshPeriod K)
    (B := SPIDER.refreshBatchSize K)
    (b := SPIDER.innerBatchSize h oracle params K) hc

/-- Helper for Theorem 3.6: the canonical scheduled run uses the canonical
product coordinate array as its sample field. -/
@[simp] theorem canonicalScheduledRun_sample
    (hc : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) c) (K : ℕ) :
    (canonicalScheduledRun (h := h) (oracle := oracle) (params := params)
      hc K).sample = CanonicalRun.sample := by
  simp only [canonicalScheduledRun, CanonicalRun.stochasticRun_sample]

/-- Helper for Theorem 3.6: a scheduled stochastic run exists on the explicit
canonical product probability space. -/
theorem scheduledRun_nonempty
    (hc : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) c) (K : ℕ) :
    Nonempty (SPIDER.ScheduledRun h oracle (canonicalProductMeasure ν)
      x₀ multiplier₀ params K) := by
  exact ⟨canonicalScheduledRun hc K⟩

end LALM

end
