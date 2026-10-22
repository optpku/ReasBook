/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@5bf5af722d85bd5c98368c41c4066124a15e8fd3:ReasBook/Papers/TR_LALM_theory/README.md (formalization contributor).
-/

module

public import TR_LALM_theory.Theorem_3_7

public section

open MeasureTheory
open scoped BigOperators InnerProductSpace NNReal

namespace LALM.FiniteStopped

universe u

variable {n m : ℕ}
variable {Ξ : Type u} [MeasurableSpace Ξ] {ν : Measure Ξ} [IsProbabilityMeasure ν]
variable {f : EuclideanSpace ℝ (Fin n) → ℝ}
variable {c : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m)}
variable {x₀ : EuclideanSpace ℝ (Fin n)}
variable {multiplier₀ : EuclideanSpace ℝ (Fin m)}
variable {h : EqualityConstrained.Regularity f c}
variable {oracle : EqualityConstrained.StochasticOracle f h.region ν}
variable {params : LALM.Parameters h x₀ multiplier₀}
variable {Q B b : ℕ+}

/-- Helper for Theorem 3.7: the positive-definite operator in the base
stochastic NR-LALM quadratic model. -/
noncomputable def modelStepOperator
    (c : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m))
    (rho beta : ℝ) (x : EuclideanSpace ℝ (Fin n)) :
    EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) :=
  beta • ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n)) +
    rho • (EqualityConstrained.constraintGradient c x).comp (fderiv ℝ c x)

/-- Helper for Theorem 3.7: positive penalty and proximal coefficients make
the base model operator continuously invertible. -/
theorem modelStepOperator_isInvertible
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

/-- Helper for Theorem 3.7: the canonical base stochastic model step solves
the positive-definite first-order equation. -/
noncomputable def canonicalModelStep
    (c : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m))
    (rho beta : ℝ) (x g : EuclideanSpace ℝ (Fin n))
    (multiplier : EuclideanSpace ℝ (Fin m)) : EuclideanSpace ℝ (Fin n) :=
  (modelStepOperator c rho beta x).inverse
    (-(g + EqualityConstrained.constraintGradient c x
      (multiplier + rho • c x)))

/-- Helper for Theorem 3.7: model inputs with a current point in the local
regularity region. -/
def modelStepRegularityDomain (h : EqualityConstrained.Regularity f c) :
    Set (EuclideanSpace ℝ (Fin n) ×
      (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin m))) :=
  {z | z.1 ∈ h.region}

/-- Helper for Theorem 3.7: the base model-step regularity domain is open. -/
theorem isOpen_modelStepRegularityDomain
    (h : EqualityConstrained.Regularity f c) :
    IsOpen (modelStepRegularityDomain h) :=
  h.isOpen_region.preimage continuous_fst

/-- Helper for Theorem 3.7: the canonical base stochastic model solver is
continuous while its current point remains in the regularity region. -/
theorem continuousOn_canonicalModelStep
    (h : EqualityConstrained.Regularity f c) (rho beta : ℝ)
    (hrho : 0 < rho) (hbeta : 0 < beta) :
    ContinuousOn (fun z : EuclideanSpace ℝ (Fin n) ×
        (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin m)) ↦
      canonicalModelStep c rho beta z.1 z.2.1 z.2.2)
      (modelStepRegularityDomain h) := by
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
  have hOperator : ContinuousAt (fun x ↦ modelStepOperator c rho beta x) z.1 := by
    unfold modelStepOperator
    exact (ContinuousAt.const_smul continuousAt_const beta).add
      (ContinuousAt.const_smul
        (hConstraintGradient.clm_comp hConstraintFDeriv) rho)
  have hInverse : ContinuousAt
      (fun x ↦ (modelStepOperator c rho beta x).inverse) z.1 :=
    ((modelStepOperator_isInvertible c rho beta z.1 hrho hbeta
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
  unfold canonicalModelStep
  exact ((hInverse.comp continuous_fst.continuousAt).clm_apply hRight).continuousWithinAt

/-- Helper for Theorem 3.7: zero extension makes the locally regular model
solver a globally defined measurable exact-real map. -/
noncomputable def canonicalModelStepExtension
    (h : EqualityConstrained.Regularity f c) (rho beta : ℝ) :
    EuclideanSpace ℝ (Fin n) ×
        (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin m)) →
      EuclideanSpace ℝ (Fin n) :=
  @Set.piecewise _ _ (modelStepRegularityDomain h)
    (fun z ↦ canonicalModelStep c rho beta z.1 z.2.1 z.2.2) (fun _ ↦ 0)
    (fun z ↦ Classical.propDecidable (z ∈ modelStepRegularityDomain h))

/-- Helper for Theorem 3.7: the extended solver agrees with the canonical
base solver at every regular current point. -/
theorem canonicalModelStepExtension_eq
    (h : EqualityConstrained.Regularity f c) (rho beta : ℝ)
    {z : EuclideanSpace ℝ (Fin n) ×
      (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin m))}
    (hz : z.1 ∈ h.region) :
    canonicalModelStepExtension h rho beta z =
      canonicalModelStep c rho beta z.1 z.2.1 z.2.2 := by
  classical
  have hzDomain : z ∈ modelStepRegularityDomain h := hz
  simp only [canonicalModelStepExtension, Set.piecewise, if_pos hzDomain]

/-- Helper for Theorem 3.7: the locally regular canonical model solver has a
globally measurable zero extension. -/
theorem measurable_canonicalModelStepExtension
    (h : EqualityConstrained.Regularity f c) (rho beta : ℝ)
    (hrho : 0 < rho) (hbeta : 0 < beta) :
    Measurable (canonicalModelStepExtension h rho beta) := by
  classical
  simpa only [canonicalModelStepExtension] using
    (continuousOn_canonicalModelStep h rho beta hrho hbeta).measurable_piecewise
      continuous_const.continuousOn
      (isOpen_modelStepRegularityDomain h).measurableSet

/-- Helper for Theorem 3.7: a finite stopped state stores its activity flag,
current and previous primal points, multiplier, and preceding raw estimate. -/
abbrev PreBatchState (n m : ℕ) :=
  ℝ × EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) ×
    EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin n)

/-- Helper for Theorem 3.7: a stopped numerical state is active exactly when
its activity coordinate is one. -/
abbrev activeState (state : PreBatchState n m) : Prop :=
  state.1 = 1

/-- Helper for Theorem 3.7: the initialized base state is active and carries
the prescribed primal and multiplier data. -/
abbrev initialState
    (x₀ : EuclideanSpace ℝ (Fin n))
    (multiplier₀ : EuclideanSpace ℝ (Fin m)) : PreBatchState n m :=
  (1, x₀, x₀, multiplier₀, 0)

/-- Helper for Theorem 3.7: one fresh batch determines the next base SPIDER
raw estimate from the finite pre-batch state. -/
noncomputable def rawEstimateAt
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

/-- Helper for Theorem 3.7: at a refresh index, the finite raw estimator is the
fresh `B`-sample average. -/
theorem rawEstimateAt_of_refresh
    (oracle : EqualityConstrained.StochasticOracle f h.region ν)
    (Q B b : ℕ+) (k : ℕ)
    (point previousPoint previousRaw : EuclideanSpace ℝ (Fin n))
    (batch : ℕ → Ξ) (hrefresh : k % Q = 0) :
    rawEstimateAt oracle Q B b k point previousPoint previousRaw batch =
      (B : ℝ)⁻¹ • ∑ i ∈ Finset.range B,
        oracle.sampleGradient point (batch i) := by
  rw [rawEstimateAt, if_pos hrefresh]

/-- Helper for Theorem 3.7: away from refresh indices, the finite raw
estimator applies the same-sample SPIDER difference update. -/
theorem rawEstimateAt_of_not_refresh
    (oracle : EqualityConstrained.StochasticOracle f h.region ν)
    (Q B b : ℕ+) (k : ℕ)
    (point previousPoint previousRaw : EuclideanSpace ℝ (Fin n))
    (batch : ℕ → Ξ) (hrefresh : k % Q ≠ 0) :
    rawEstimateAt oracle Q B b k point previousPoint previousRaw batch =
      previousRaw + (b : ℝ)⁻¹ • ∑ i ∈ Finset.range b,
        (oracle.sampleGradient point (batch i) -
          oracle.sampleGradient previousPoint (batch i)) := by
  rw [rawEstimateAt, if_neg hrefresh]

/-- Helper for Theorem 3.7: radial clipping is measurable on the base
finite-dimensional gradient space. -/
theorem measurable_spiderClip (G : ℝ≥0) :
    Measurable (SPIDER.clip G :
      EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) := by
  unfold SPIDER.clip
  apply Measurable.ite
  · exact measurableSet_le continuous_norm.measurable measurable_const
  · exact measurable_id
  · exact (measurable_const.div continuous_norm.measurable).smul measurable_id

/-- Helper for Theorem 3.7: the explicit finite raw-estimate update is
measurable in the numerical state and fresh batch. -/
theorem measurable_rawEstimateAt
    (oracle : EqualityConstrained.StochasticOracle f h.region ν)
    (Q B b : ℕ+) (k : ℕ) :
    Measurable (fun z : PreBatchState n m × (ℕ → Ξ) ↦
      rawEstimateAt oracle Q B b k z.1.2.1 z.1.2.2.1
        z.1.2.2.2.2 z.2) := by
  have hpoint : Measurable (fun z : PreBatchState n m × (ℕ → Ξ) ↦
      z.1.2.1) := by
    fun_prop
  have hpreviousPoint : Measurable (fun z : PreBatchState n m × (ℕ → Ξ) ↦
      z.1.2.2.1) := by
    fun_prop
  have hpreviousRaw : Measurable (fun z : PreBatchState n m × (ℕ → Ξ) ↦
      z.1.2.2.2.2) := by
    fun_prop
  have hsample (i : ℕ) : Measurable
      (fun z : PreBatchState n m × (ℕ → Ξ) ↦ z.2 i) :=
    (measurable_pi_apply i).comp measurable_snd
  by_cases hrefresh : k % Q = 0
  · simp only [rawEstimateAt, if_pos hrefresh]
    exact (Finset.measurable_sum (Finset.range B) fun i _ ↦
      oracle.measurable_sampleGradient.comp
        (hpoint.prodMk (hsample i))).const_smul ((B : ℝ)⁻¹)
  · simp only [rawEstimateAt, if_neg hrefresh]
    exact hpreviousRaw.add
      ((Finset.measurable_sum (Finset.range b) fun i _ ↦
        (oracle.measurable_sampleGradient.comp
            (hpoint.prodMk (hsample i))).sub
          (oracle.measurable_sampleGradient.comp
            (hpreviousPoint.prodMk (hsample i)))).const_smul ((b : ℝ)⁻¹))

/-- Helper for Theorem 3.7: the active branch computes the clipped gradient
estimate used by the base model. -/
noncomputable def clippedEstimateAt
    (h : EqualityConstrained.Regularity f c)
    (oracle : EqualityConstrained.StochasticOracle f h.region ν)
    (Q B b : ℕ+) (k : ℕ) (z : PreBatchState n m × (ℕ → Ξ)) :
    EuclideanSpace ℝ (Fin n) :=
  SPIDER.clip h.gradientBound
    (rawEstimateAt oracle Q B b k z.1.2.1 z.1.2.2.1 z.1.2.2.2.2 z.2)

/-- Helper for Theorem 3.7: the finite clipped estimator is radial clipping of
the raw estimator stored by the SPIDER recursion. -/
theorem clippedEstimateAt_def
    (h : EqualityConstrained.Regularity f c)
    (oracle : EqualityConstrained.StochasticOracle f h.region ν)
    (Q B b : ℕ+) (k : ℕ) (z : PreBatchState n m × (ℕ → Ξ)) :
    clippedEstimateAt h oracle Q B b k z =
      SPIDER.clip h.gradientBound
        (rawEstimateAt oracle Q B b k z.1.2.1 z.1.2.2.1 z.1.2.2.2.2 z.2) := by
  rfl

/-- Helper for Theorem 3.7: the active clipped-estimate component is
measurable. -/
theorem measurable_clippedEstimateAt (k : ℕ) :
    Measurable (clippedEstimateAt h oracle Q B b k) := by
  unfold clippedEstimateAt
  exact (measurable_spiderClip h.gradientBound).comp
    (measurable_rawEstimateAt oracle Q B b k)

/-- Helper for Theorem 3.7: the canonical base model input groups the current
point, clipped estimate, and multiplier. -/
noncomputable def modelInputAt
    (h : EqualityConstrained.Regularity f c)
    (oracle : EqualityConstrained.StochasticOracle f h.region ν)
    (Q B b : ℕ+) (k : ℕ) (z : PreBatchState n m × (ℕ → Ξ)) :
    EuclideanSpace ℝ (Fin n) ×
      (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin m)) :=
  (z.1.2.1, clippedEstimateAt h oracle Q B b k z, z.1.2.2.2.1)

/-- Helper for Theorem 3.7: the grouped base model input is measurable. -/
theorem measurable_modelInputAt (k : ℕ) :
    Measurable (modelInputAt h oracle Q B b k) := by
  unfold modelInputAt
  have hpoint : Measurable (fun z : PreBatchState n m × (ℕ → Ξ) ↦
      z.1.2.1) := by
    fun_prop
  have hmultiplier : Measurable (fun z : PreBatchState n m × (ℕ → Ξ) ↦
      z.1.2.2.2.1) := by
    fun_prop
  exact hpoint.prodMk ((measurable_clippedEstimateAt k).prodMk hmultiplier)

/-- Helper for Theorem 3.7: the active base step applies the locally regular
canonical solver to the finite model input. -/
noncomputable def baseStepAt
    (h : EqualityConstrained.Regularity f c)
    (oracle : EqualityConstrained.StochasticOracle f h.region ν)
    (params : LALM.Parameters h x₀ multiplier₀) (Q B b : ℕ+) (k : ℕ) :
    PreBatchState n m × (ℕ → Ξ) → EuclideanSpace ℝ (Fin n) :=
  canonicalModelStepExtension h params.rho params.beta ∘
    modelInputAt h oracle Q B b k

/-- Helper for Theorem 3.7: the active canonical base step is measurable in
the finite state and fresh batch. -/
theorem measurable_baseStepAt (k : ℕ) :
    Measurable (baseStepAt h oracle params Q B b k) := by
  unfold baseStepAt
  exact (measurable_canonicalModelStepExtension h params.rho params.beta
    params.spec.1.2.2.1 params.spec.1.2.1).comp (measurable_modelInputAt k)

/-- Helper for Theorem 3.7: the active transition endpoint adds the base
model step to the current primal point. -/
noncomputable def nextPointAt
    (h : EqualityConstrained.Regularity f c)
    (oracle : EqualityConstrained.StochasticOracle f h.region ν)
    (params : LALM.Parameters h x₀ multiplier₀) (Q B b : ℕ+) (k : ℕ)
    (z : PreBatchState n m × (ℕ → Ξ)) : EuclideanSpace ℝ (Fin n) :=
  z.1.2.1 + baseStepAt h oracle params Q B b k z

/-- Helper for Theorem 3.7: the active transition endpoint is measurable. -/
theorem measurable_nextPointAt (k : ℕ) :
    Measurable (nextPointAt h oracle params Q B b k) := by
  unfold nextPointAt
  have hpoint : Measurable (fun z : PreBatchState n m × (ℕ → Ξ) ↦
      z.1.2.1) := by
    fun_prop
  exact hpoint.add (measurable_baseStepAt k)

/-- Helper for Theorem 3.7: the active dual update is evaluated at the newly
computed base transition endpoint. -/
noncomputable def nextMultiplierAt
    (h : EqualityConstrained.Regularity f c)
    (oracle : EqualityConstrained.StochasticOracle f h.region ν)
    (params : LALM.Parameters h x₀ multiplier₀) (Q B b : ℕ+) (k : ℕ)
    (z : PreBatchState n m × (ℕ → Ξ)) : EuclideanSpace ℝ (Fin m) :=
  z.1.2.2.2.1 + (params.rho : ℝ) •
    h.constraintExtension (nextPointAt h oracle params Q B b k z)

/-- Helper for Theorem 3.7: the active base multiplier update is measurable. -/
theorem measurable_nextMultiplierAt (k : ℕ) :
    Measurable (nextMultiplierAt h oracle params Q B b k) := by
  unfold nextMultiplierAt
  have hmultiplier : Measurable (fun z : PreBatchState n m × (ℕ → Ξ) ↦
      z.1.2.2.2.1) := by
    fun_prop
  exact hmultiplier.add
    ((h.measurable_constraintExtension.comp
      (measurable_nextPointAt k)).const_smul (params.rho : ℝ))

/-- Theorem 3.7: when a finite transition endpoint remains in the regularity
region, the measurable zero-extension update is exactly the TeX multiplier
update using the original constraint map. -/
theorem nextMultiplierAt_eq_actual_of_nextPoint_mem_region
    (h : EqualityConstrained.Regularity f c)
    (oracle : EqualityConstrained.StochasticOracle f h.region ν)
    (params : LALM.Parameters h x₀ multiplier₀) (Q B b : ℕ+) (k : ℕ)
    (z : PreBatchState n m × (ℕ → Ξ))
    (hnext : nextPointAt h oracle params Q B b k z ∈ h.region) :
    nextMultiplierAt h oracle params Q B b k z =
      z.1.2.2.2.1 + (params.rho : ℝ) •
        c (nextPointAt h oracle params Q B b k z) := by
  unfold nextMultiplierAt
  rw [h.constraintExtension_eq hnext]

/-- Theorem 3.7: a current point in the localization set and a step bounded
by the buffer radius put the computed endpoint in the regularity region. -/
theorem nextPointAt_mem_region_of_mem_of_norm_baseStep_le
    (h : EqualityConstrained.Regularity f c)
    (oracle : EqualityConstrained.StochasticOracle f h.region ν)
    (params : LALM.Parameters h x₀ multiplier₀) (Q B b : ℕ+)
    (confidence : ℝ) (X : Set (EuclideanSpace ℝ (Fin n)))
    (h_region : LALM.StochasticRun.Localization.RegionCondition
      h oracle params confidence X)
    (k : ℕ) (z : PreBatchState n m × (ℕ → Ξ))
    (hx : z.1.2.1 ∈ X)
    (hstep : ‖baseStepAt h oracle params Q B b k z‖ ≤ params.delta) :
    nextPointAt h oracle params Q B b k z ∈ h.region := by
  apply h_region.thickening_subset
  apply Metric.mem_cthickening_of_dist_le
    (nextPointAt h oracle params Q B b k z) z.1.2.1 params.delta X hx
  rw [dist_eq_norm, nextPointAt, add_sub_cancel_left]
  exact hstep

/-- Helper for Theorem 3.7: an active transition stores the computed endpoint
even when that endpoint is the first point outside the localization set. -/
noncomputable def activeTransition
    (h : EqualityConstrained.Regularity f c)
    (oracle : EqualityConstrained.StochasticOracle f h.region ν)
    (params : LALM.Parameters h x₀ multiplier₀) (Q B b : ℕ+)
    (X : Set (EuclideanSpace ℝ (Fin n))) (k : ℕ)
    (z : PreBatchState n m × (ℕ → Ξ)) : PreBatchState n m :=
  let nextPoint := nextPointAt h oracle params Q B b k z
  let nextActive : ℝ :=
    @ite ℝ (nextPoint ∈ X) (Classical.propDecidable _) 1 0
  (nextActive, nextPoint, z.1.2.1,
    nextMultiplierAt h oracle params Q B b k z,
    rawEstimateAt oracle Q B b k z.1.2.1 z.1.2.2.1 z.1.2.2.2.2 z.2)

/-- Helper for Theorem 3.7: the active base stopped transition is measurable
when localization membership is measurable. -/
theorem measurable_activeTransition
    (X : Set (EuclideanSpace ℝ (Fin n))) (hX : MeasurableSet X) (k : ℕ) :
    Measurable (activeTransition h oracle params Q B b X k) := by
  unfold activeTransition
  have hpoint : Measurable (fun z : PreBatchState n m × (ℕ → Ξ) ↦
      z.1.2.1) := by
    fun_prop
  have hraw := measurable_rawEstimateAt oracle Q B b k
  have hnextPoint := measurable_nextPointAt
    (h := h) (oracle := oracle) (params := params) (Q := Q) (B := B) (b := b) k
  have hnextMultiplier := measurable_nextMultiplierAt
    (h := h) (oracle := oracle) (params := params) (Q := Q) (B := B) (b := b) k
  have hnextActive : Measurable (fun z : PreBatchState n m × (ℕ → Ξ) ↦
      @ite ℝ (nextPointAt h oracle params Q B b k z ∈ X)
        (Classical.propDecidable _) 1 0) := by
    apply Measurable.ite
    · exact hX.preimage hnextPoint
    · exact measurable_const
    · exact measurable_const
  exact hnextActive.prodMk
    (hnextPoint.prodMk (hpoint.prodMk (hnextMultiplier.prodMk hraw)))

/-- Theorem 3.7: one finite stopped base transition executes the numerical
update only while active and is the identity after the first exit. -/
noncomputable def transition
    (h : EqualityConstrained.Regularity f c)
    (oracle : EqualityConstrained.StochasticOracle f h.region ν)
    (params : LALM.Parameters h x₀ multiplier₀) (Q B b : ℕ+)
    (X : Set (EuclideanSpace ℝ (Fin n))) (k : ℕ)
    (z : PreBatchState n m × (ℕ → Ξ)) : PreBatchState n m :=
  @ite (PreBatchState n m) (z.1.1 = 1) (Classical.propDecidable _)
    (activeTransition h oracle params Q B b X k z) z.1

/-- Helper for Theorem 3.7: the absorbing finite base transition is globally
measurable. -/
theorem measurable_transition
    (X : Set (EuclideanSpace ℝ (Fin n))) (hX : MeasurableSet X) (k : ℕ) :
    Measurable (transition h oracle params Q B b X k) := by
  unfold transition
  apply Measurable.ite
  · exact (measurableSet_singleton (1 : ℝ)).preimage
      (measurable_fst.comp measurable_fst)
  · exact measurable_activeTransition X hX k
  · exact measurable_fst

/-- Helper for Theorem 3.7: an inactive stopped state is unchanged by every
later transition. -/
theorem transition_of_inactive
    (X : Set (EuclideanSpace ℝ (Fin n))) (k : ℕ)
    (z : PreBatchState n m × (ℕ → Ξ)) (hinactive : z.1.1 ≠ 1) :
    transition h oracle params Q B b X k z = z.1 := by
  simp only [transition, if_neg hinactive]

/-- Helper for Theorem 3.7: an active stopped state executes exactly the
base numerical transition, including a possible first-exit endpoint. -/
theorem transition_of_active
    (X : Set (EuclideanSpace ℝ (Fin n))) (k : ℕ)
    (z : PreBatchState n m × (ℕ → Ξ)) (hactive : z.1.1 = 1) :
    transition h oracle params Q B b X k z =
      activeTransition h oracle params Q B b X k z := by
  simp only [transition, if_pos hactive]

/-- Helper for Theorem 3.7: after an active transition, activity is
equivalent to localization of the newly computed endpoint. -/
theorem activeTransition_isActive_iff
    (X : Set (EuclideanSpace ℝ (Fin n))) (k : ℕ)
    (z : PreBatchState n m × (ℕ → Ξ)) :
    activeState (activeTransition h oracle params Q B b X k z) ↔
      nextPointAt h oracle params Q B b k z ∈ X := by
  classical
  unfold activeState activeTransition
  by_cases hmem : nextPointAt h oracle params Q B b k z ∈ X
  · simp [hmem]
  · simp only [if_neg hmem, zero_ne_one, false_iff]
    exact hmem

/-- Helper for Theorem 3.7: the active transition's stored endpoint differs
from its predecessor by exactly the computed base model step. -/
theorem activeTransition_point_displacement
    (h : EqualityConstrained.Regularity f c)
    (oracle : EqualityConstrained.StochasticOracle f h.region ν)
    (params : LALM.Parameters h x₀ multiplier₀) (Q B b : ℕ+)
    (X : Set (EuclideanSpace ℝ (Fin n))) (k : ℕ)
    (z : PreBatchState n m × (ℕ → Ξ)) :
    (activeTransition h oracle params Q B b X k z).2.1 - z.1.2.1 =
      baseStepAt h oracle params Q B b k z := by
  unfold activeTransition
  dsimp
  exact add_sub_cancel_left _ _

/-- Helper for Theorem 3.7: the active transition stores the endpoint
computed by `nextPointAt`. -/
theorem activeTransition_point
    (h : EqualityConstrained.Regularity f c)
    (oracle : EqualityConstrained.StochasticOracle f h.region ν)
    (params : LALM.Parameters h x₀ multiplier₀) (Q B b : ℕ+)
    (X : Set (EuclideanSpace ℝ (Fin n))) (k : ℕ)
    (z : PreBatchState n m × (ℕ → Ξ)) :
    (activeTransition h oracle params Q B b X k z).2.1 =
      nextPointAt h oracle params Q B b k z := by
  unfold activeTransition
  rfl

/-- Helper for Theorem 3.7: an active transition stores the predecessor point
as its previous-point component. -/
theorem activeTransition_previousPoint
    (h : EqualityConstrained.Regularity f c)
    (oracle : EqualityConstrained.StochasticOracle f h.region ν)
    (params : LALM.Parameters h x₀ multiplier₀) (Q B b : ℕ+)
    (X : Set (EuclideanSpace ℝ (Fin n))) (k : ℕ)
    (z : PreBatchState n m × (ℕ → Ξ)) :
    (activeTransition h oracle params Q B b X k z).2.2.1 = z.1.2.1 := by
  unfold activeTransition
  rfl

/-- Helper for Theorem 3.7: the active transition stores the dual update
computed by `nextMultiplierAt`. -/
theorem activeTransition_multiplier
    (h : EqualityConstrained.Regularity f c)
    (oracle : EqualityConstrained.StochasticOracle f h.region ν)
    (params : LALM.Parameters h x₀ multiplier₀) (Q B b : ℕ+)
    (X : Set (EuclideanSpace ℝ (Fin n))) (k : ℕ)
    (z : PreBatchState n m × (ℕ → Ξ)) :
    (activeTransition h oracle params Q B b X k z).2.2.2.1 =
      nextMultiplierAt h oracle params Q B b k z := by
  unfold activeTransition
  rfl

/-- Helper for Theorem 3.7: the active transition stores the raw estimator
computed from its predecessor state and fresh sample batch. -/
theorem activeTransition_rawEstimate
    (h : EqualityConstrained.Regularity f c)
    (oracle : EqualityConstrained.StochasticOracle f h.region ν)
    (params : LALM.Parameters h x₀ multiplier₀) (Q B b : ℕ+)
    (X : Set (EuclideanSpace ℝ (Fin n))) (k : ℕ)
    (z : PreBatchState n m × (ℕ → Ξ)) :
    (activeTransition h oracle params Q B b X k z).2.2.2.2 =
      rawEstimateAt oracle Q B b k z.1.2.1 z.1.2.2.1 z.1.2.2.2.2 z.2 := by
  unfold activeTransition
  rfl

/-- Theorem 3.7: the stopped base state at time `k` is generated from only
the `k` preceding sample batches. -/
noncomputable def state
    (h : EqualityConstrained.Regularity f c)
    (oracle : EqualityConstrained.StochasticOracle f h.region ν)
    (params : LALM.Parameters h x₀ multiplier₀) (Q B b : ℕ+)
    (X : Set (EuclideanSpace ℝ (Fin n))) :
    (k : ℕ) → (Fin k → ℕ → Ξ) → PreBatchState n m
  | 0, _ => initialState x₀ multiplier₀
  | k + 1, samples =>
      transition h oracle params Q B b X k
        (state h oracle params Q B b X k
          (fun t i ↦ samples t.castSucc i), samples (Fin.last k))

/-- Helper for Theorem 3.7: the finite base stopped state starts from the
prescribed active initialization. -/
theorem state_zero
    (X : Set (EuclideanSpace ℝ (Fin n))) (samples : Fin 0 → ℕ → Ξ) :
    state h oracle params Q B b X 0 samples = initialState x₀ multiplier₀ := by
  rfl

/-- Helper for Theorem 3.7: a successor finite state is one absorbing
transition from its preceding history and final fresh batch. -/
theorem state_succ
    (X : Set (EuclideanSpace ℝ (Fin n))) (k : ℕ)
    (samples : Fin (k + 1) → ℕ → Ξ) :
    state h oracle params Q B b X (k + 1) samples =
      transition h oracle params Q B b X k
        (state h oracle params Q B b X k
          (fun t i ↦ samples t.castSucc i), samples (Fin.last k)) := by
  rfl

/-- Helper for Theorem 3.7: every finite base stopped state is measurable as
a function of exactly its preceding sample history. -/
theorem measurable_state
    (X : Set (EuclideanSpace ℝ (Fin n))) (hX : MeasurableSet X) (k : ℕ) :
    Measurable (state h oracle params Q B b X k) := by
  induction k with
  | zero =>
      simpa only [state] using
        (measurable_const : Measurable (fun _ : Fin 0 → ℕ → Ξ ↦
          initialState x₀ multiplier₀))
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
          state h oracle params Q B b X k (restrictHistory samples)) :=
        ih.comp hrestrictHistory
      have hbatch : Measurable (fun samples : Fin (k + 1) → ℕ → Ξ ↦
          samples (Fin.last k)) := measurable_pi_apply (Fin.last k)
      simpa only [state, restrictHistory, Function.comp_def] using
        (measurable_transition (h := h) (oracle := oracle) (params := params)
          (Q := Q) (B := B) (b := b) X hX k).comp (hstate.prodMk hbatch)

end LALM.FiniteStopped

end
