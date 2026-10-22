/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@5bf5af722d85bd5c98368c41c4066124a15e8fd3:ReasBook/Papers/TR_LALM_theory/README.md (formalization contributor).
-/

module

public import TR_LALM_theory.Corollary_3_8
public import TR_LALM_theory.Theorem_3_6.CanonicalRun

/-!
# Canonical full-tail coupling realization

The canonical constructor in this module realizes the full-tail
`SafeguardedRestart` coupling surface.  Its global `ContDiff c` hypothesis is
needed only by this optional infinite-tail nonemptiness construction; it is not
an assumption of the finite-prefix localization and restart estimates.
-/

public section

open MeasureTheory
open LALM.StochasticRun.UniformOutput
open scoped NNReal

namespace LALM

universe u v w

variable {n m : ℕ}
variable {Ξ : Type u} [MeasurableSpace Ξ] {ν : Measure Ξ} [IsProbabilityMeasure ν]
variable {Ω : Type v} [MeasurableSpace Ω] {ℙ : Measure Ω} [IsProbabilityMeasure ℙ]
variable {Ω' : Type w} [MeasurableSpace Ω'] {ℙ' : Measure Ω'} [IsProbabilityMeasure ℙ']
variable {f : EuclideanSpace ℝ (Fin n) → ℝ}
variable {c : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m)}
variable {x₀ : EuclideanSpace ℝ (Fin n)}
variable {multiplier₀ : EuclideanSpace ℝ (Fin m)}
variable {h : EqualityConstrained.Regularity f c}
variable {oracle : EqualityConstrained.StochasticOracle f h.region ν}
variable {params : LALM.Parameters h x₀ multiplier₀}

/-- Helper for Corollary 3.8: independence of two random variables is
preserved by pullback along a measure-preserving map. -/
private lemma indepFun_comp_measurePreserving
    {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    {φ : Ω' → Ω} {U : Ω → A} {V : Ω → B}
    (hφ : MeasurePreserving φ ℙ' ℙ)
    (hU : AEMeasurable U ℙ) (hV : AEMeasurable V ℙ)
    (hUV : ProbabilityTheory.IndepFun U V ℙ) :
    ProbabilityTheory.IndepFun (fun ω ↦ U (φ ω)) (fun ω ↦ V (φ ω)) ℙ' := by
  let μU : Measure A := ℙ.map U
  let μV : Measure B := ℙ.map V
  have hLawU : ProbabilityTheory.HasLaw U μU ℙ := by
    exact ⟨hU, rfl⟩
  have hLawV : ProbabilityTheory.HasLaw V μV ℙ := by
    exact ⟨hV, rfl⟩
  have hLawφ : ProbabilityTheory.HasLaw φ ℙ ℙ' := hφ.hasLaw
  have hLawPullU : ProbabilityTheory.HasLaw (fun ω ↦ U (φ ω)) μU ℙ' := by
    simpa only [Function.comp_def] using hLawU.comp hLawφ
  have hLawPullV : ProbabilityTheory.HasLaw (fun ω ↦ V (φ ω)) μV ℙ' := by
    simpa only [Function.comp_def] using hLawV.comp hLawφ
  have hLawJoint : ProbabilityTheory.HasLaw (fun ω ↦ (U ω, V ω))
      (μU.prod μV) ℙ := hUV.hasLaw_prod hLawU hLawV
  have hLawPullJoint : ProbabilityTheory.HasLaw
      (fun ω ↦ (U (φ ω), V (φ ω))) (μU.prod μV) ℙ' := by
    simpa only [Function.comp_def] using hLawJoint.comp hLawφ
  exact (ProbabilityTheory.indepFun_iff_hasLaw_prodMk_prod
    hLawPullU hLawPullV).mpr hLawPullJoint

omit [IsProbabilityMeasure ℙ] in
/-- Helper for Corollary 3.8: mutual independence of an indexed family is
preserved by pullback along a measure-preserving map. -/
private lemma iIndepFun_comp_measurePreserving
    {ι : Type*} {A : ι → Type*} [mA : ∀ i, MeasurableSpace (A i)]
    {φ : Ω' → Ω} {U : (i : ι) → Ω → A i}
    (hφ : MeasurePreserving φ ℙ' ℙ)
    (hU : AEMeasurable (fun ω i ↦ U i ω) ℙ)
    (hIndep : ProbabilityTheory.iIndepFun U ℙ) :
    ProbabilityTheory.iIndepFun (fun i ω ↦ U i (φ ω)) ℙ' := by
  let μ : (i : ι) → Measure (A i) := fun i ↦ ℙ.map (U i)
  have hLaw (i : ι) : ProbabilityTheory.HasLaw (U i) (μ i) ℙ := by
    exact ⟨hU.eval i, rfl⟩
  have hLawφ : ProbabilityTheory.HasLaw φ ℙ ℙ' := hφ.hasLaw
  have hLawPull (i : ι) :
      ProbabilityTheory.HasLaw (fun ω ↦ U i (φ ω)) (μ i) ℙ' := by
    simpa only [Function.comp_def] using (hLaw i).comp hLawφ
  have hJointLaw : ProbabilityTheory.HasLaw (fun ω i ↦ U i ω)
      (Measure.infinitePi μ) ℙ :=
    hIndep.hasLaw_infinitePi hLaw hU
  have hPullJointLaw : ProbabilityTheory.HasLaw
      (fun ω i ↦ U i (φ ω)) (Measure.infinitePi μ) ℙ' := by
    simpa only [Function.comp_def] using hJointLaw.comp hLawφ
  have hPullMeasurable : AEMeasurable (fun ω i ↦ U i (φ ω)) ℙ' :=
    hU.comp_quasiMeasurePreserving hφ.quasiMeasurePreserving
  exact (ProbabilityTheory.iIndepFun_iff_hasLaw_Pi_infinitePi
    hLawPull hPullMeasurable).mpr hPullJointLaw

namespace StochasticRun

variable {Q B b : ℕ+}

/-- Helper for Corollary 3.8: pull back all oracle samples of a stochastic run
along a map of probability spaces. -/
def pullSample
    (run : StochasticRun h oracle ℙ x₀ multiplier₀ params Q B b)
    (φ : Ω' → Ω) (k j : ℕ) (ω : Ω') : Ξ :=
  run.sample k j (φ ω)

/-- Helper for Corollary 3.8: pull back all primal iterates of a stochastic run
along a map of probability spaces. -/
def pullPoint
    (run : StochasticRun h oracle ℙ x₀ multiplier₀ params Q B b)
    (φ : Ω' → Ω) (k : ℕ) (ω : Ω') : EuclideanSpace ℝ (Fin n) :=
  run.point k (φ ω)

/-- Helper for Corollary 3.8: pull back all multiplier iterates of a stochastic
run along a map of probability spaces. -/
def pullMultiplier
    (run : StochasticRun h oracle ℙ x₀ multiplier₀ params Q B b)
    (φ : Ω' → Ω) (k : ℕ) (ω : Ω') : EuclideanSpace ℝ (Fin m) :=
  run.multiplier k (φ ω)

/-- Helper for Corollary 3.8: pull back all primal steps of a stochastic run
along a map of probability spaces. -/
def pullStep
    (run : StochasticRun h oracle ℙ x₀ multiplier₀ params Q B b)
    (φ : Ω' → Ω) (k : ℕ) (ω : Ω') : EuclideanSpace ℝ (Fin n) :=
  run.step k (φ ω)

omit [MeasurableSpace Ω'] in
/-- Helper for Corollary 3.8: the recursive raw estimate formed from pulled
sequences is the pullback of the original raw estimate. -/
private lemma rawEstimate_pullback
    (run : StochasticRun h oracle ℙ x₀ multiplier₀ params Q B b)
    (φ : Ω' → Ω) (k : ℕ) (ω : Ω') :
    SPIDER.rawEstimate oracle (pullPoint run φ) (pullSample run φ)
        Q B b k ω =
      SPIDER.rawEstimate oracle run.point run.sample Q B b k (φ ω) := by
  induction k with
  | zero =>
      rfl
  | succ k ih =>
      simp only [SPIDER.rawEstimate, pullPoint, pullSample, ih]

omit [MeasurableSpace Ω'] in
/-- Helper for Corollary 3.8: the projected estimator formed from pulled
sequences is the pullback of the original projected estimator. -/
private lemma estimate_pullback
    (run : StochasticRun h oracle ℙ x₀ multiplier₀ params Q B b)
    (φ : Ω' → Ω) (k : ℕ) (ω : Ω') :
    SPIDER.estimate h.gradientBound oracle (pullPoint run φ) (pullSample run φ)
        Q B b k ω =
      SPIDER.estimate h.gradientBound oracle run.point run.sample Q B b k (φ ω) := by
  rw [SPIDER.estimate_apply, SPIDER.estimate_apply,
    rawEstimate_pullback run φ k ω]

omit [IsProbabilityMeasure ℙ'] in
/-- Helper for Corollary 3.8: pulled oracle samples retain the oracle law. -/
private lemma pullSample_hasLaw
    (run : StochasticRun h oracle ℙ x₀ multiplier₀ params Q B b)
    (φ : Ω' → Ω) (hφ : MeasurePreserving φ ℙ' ℙ) (k j : ℕ) :
    ProbabilityTheory.HasLaw (pullSample run φ k j) ν ℙ' := by
  unfold pullSample
  simpa only [Function.comp_def] using
    (run.hasLaw_sample k j).comp hφ.hasLaw

/-- Helper for Corollary 3.8: pulled oracle samples remain mutually
independent. -/
private lemma pullSample_iIndepFun
    (run : StochasticRun h oracle ℙ x₀ multiplier₀ params Q B b)
    (φ : Ω' → Ω) (hφ : MeasurePreserving φ ℙ' ℙ) :
    ProbabilityTheory.iIndepFun
      (fun ki : ℕ × ℕ ↦ pullSample run φ ki.1 ki.2) ℙ' := by
  have hMeasurable : AEMeasurable
      (fun (ω : Ω) (ki : ℕ × ℕ) ↦ run.sample ki.1 ki.2 ω) ℙ := by
    apply aemeasurable_pi_lambda
    intro ki
    exact (run.hasLaw_sample ki.1 ki.2).aemeasurable
  unfold pullSample
  exact iIndepFun_comp_measurePreserving
    hφ hMeasurable run.independent_sample

/-- Helper for Corollary 3.8: the pulled pre-batch state remains independent
of its pulled fresh sample batch. -/
private lemma pullPreBatchState_indep_sample
    (run : StochasticRun h oracle ℙ x₀ multiplier₀ params Q B b)
    (φ : Ω' → Ω) (hφ : MeasurePreserving φ ℙ' ℙ) (k : ℕ) :
    ProbabilityTheory.IndepFun
      (fun ω ↦
        (pullPoint run φ k ω, pullPoint run φ (k - 1) ω,
          pullMultiplier run φ k ω,
          if k = 0 then 0 else
            SPIDER.rawEstimate oracle (pullPoint run φ) (pullSample run φ)
              Q B b (k - 1) ω))
      (fun ω j ↦ pullSample run φ k j ω) ℙ' := by
  let U : Ω →
      EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) ×
        EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin n) :=
    fun ω ↦
      (run.point k ω, run.point (k - 1) ω, run.multiplier k ω,
        if k = 0 then 0 else
          SPIDER.rawEstimate oracle run.point run.sample Q B b (k - 1) ω)
  let V : Ω → (ℕ → Ξ) := fun ω j ↦ run.sample k j ω
  have hU : AEMeasurable U ℙ := by
    have hpointCurrent := run.aemeasurable_point k
    have hpointPrevious := run.aemeasurable_point (k - 1)
    have hmultiplier := run.aemeasurable_multiplier k
    have hraw : AEMeasurable
        (fun ω ↦ if k = 0 then 0 else
          SPIDER.rawEstimate oracle run.point run.sample Q B b (k - 1) ω) ℙ := by
      by_cases hk : k = 0
      · simp only [hk, if_true]
        exact aemeasurable_const
      · simp only [hk, if_false]
        exact run.aemeasurable_rawEstimate (k - 1)
    exact hpointCurrent.prodMk
      (hpointPrevious.prodMk (hmultiplier.prodMk hraw))
  have hV : AEMeasurable V ℙ := by
    apply aemeasurable_pi_lambda
    intro j
    exact (run.hasLaw_sample k j).aemeasurable
  have hIndep : ProbabilityTheory.IndepFun U V ℙ := by
    exact run.independent_preBatchState_sample k
  have hPull := indepFun_comp_measurePreserving hφ hU hV hIndep
  simpa only [U, V, pullPoint, pullMultiplier, pullSample,
    rawEstimate_pullback] using hPull

omit [IsProbabilityMeasure ℙ'] in
/-- Helper for Corollary 3.8: pulled raw estimates are almost everywhere
measurable. -/
private lemma pullRawEstimate_aemeasurable
    (run : StochasticRun h oracle ℙ x₀ multiplier₀ params Q B b)
    (φ : Ω' → Ω) (hφ : MeasurePreserving φ ℙ' ℙ) (k : ℕ) :
    AEMeasurable
      (SPIDER.rawEstimate oracle (pullPoint run φ) (pullSample run φ) Q B b k)
      ℙ' := by
  have hcomp := (run.aemeasurable_rawEstimate k).comp_quasiMeasurePreserving
    hφ.quasiMeasurePreserving
  have heq : SPIDER.rawEstimate oracle (pullPoint run φ) (pullSample run φ)
      Q B b k = fun ω ↦
        SPIDER.rawEstimate oracle run.point run.sample Q B b k (φ ω) := by
    funext ω
    exact rawEstimate_pullback run φ k ω
  rwa [heq]

omit [IsProbabilityMeasure ℙ'] in
/-- Helper for Corollary 3.8: pulled primal iterates are almost everywhere
measurable. -/
private lemma pullPoint_aemeasurable
    (run : StochasticRun h oracle ℙ x₀ multiplier₀ params Q B b)
    (φ : Ω' → Ω) (hφ : MeasurePreserving φ ℙ' ℙ) (k : ℕ) :
    AEMeasurable (pullPoint run φ k) ℙ' := by
  exact (run.aemeasurable_point k).comp_quasiMeasurePreserving
    hφ.quasiMeasurePreserving

omit [IsProbabilityMeasure ℙ'] in
/-- Helper for Corollary 3.8: pulled multiplier iterates are almost everywhere
measurable. -/
private lemma pullMultiplier_aemeasurable
    (run : StochasticRun h oracle ℙ x₀ multiplier₀ params Q B b)
    (φ : Ω' → Ω) (hφ : MeasurePreserving φ ℙ' ℙ) (k : ℕ) :
    AEMeasurable (pullMultiplier run φ k) ℙ' := by
  exact (run.aemeasurable_multiplier k).comp_quasiMeasurePreserving
    hφ.quasiMeasurePreserving

omit [IsProbabilityMeasure ℙ'] in
/-- Helper for Corollary 3.8: pulled primal steps are almost everywhere
measurable. -/
private lemma pullStep_aemeasurable
    (run : StochasticRun h oracle ℙ x₀ multiplier₀ params Q B b)
    (φ : Ω' → Ω) (hφ : MeasurePreserving φ ℙ' ℙ) (k : ℕ) :
    AEMeasurable (pullStep run φ k) ℙ' := by
  exact (run.aemeasurable_step k).comp_quasiMeasurePreserving
    hφ.quasiMeasurePreserving

omit [MeasurableSpace Ω'] in
/-- Helper for Corollary 3.8: a pulled run starts at the same prescribed
primal point. -/
private lemma pullPoint_zero
    (run : StochasticRun h oracle ℙ x₀ multiplier₀ params Q B b)
    (φ : Ω' → Ω) (ω : Ω') :
    pullPoint run φ 0 ω = x₀ := by
  exact run.point_zero (φ ω)

omit [MeasurableSpace Ω'] in
/-- Helper for Corollary 3.8: a pulled run starts at the same prescribed
multiplier. -/
private lemma pullMultiplier_zero
    (run : StochasticRun h oracle ℙ x₀ multiplier₀ params Q B b)
    (φ : Ω' → Ω) (ω : Ω') :
    pullMultiplier run φ 0 ω = multiplier₀ := by
  exact run.multiplier_zero (φ ω)

omit [MeasurableSpace Ω'] in
/-- Helper for Corollary 3.8: every pulled step minimizes the same pathwise
quadratic model as its source step. -/
private lemma pullStep_minimizes
    (run : StochasticRun h oracle ℙ x₀ multiplier₀ params Q B b)
    (φ : Ω' → Ω) (k : ℕ) (ω : Ω') :
    IsMinOn (stepModelWithGradient c
      (SPIDER.estimate h.gradientBound oracle (pullPoint run φ)
        (pullSample run φ) Q B b k ω)
      (PositivePenaltyParameters.rho params)
      (PositivePenaltyParameters.beta params)
      (pullPoint run φ k ω) (pullMultiplier run φ k ω))
      Set.univ (pullStep run φ k ω) := by
  simpa only [pullPoint, pullMultiplier, pullStep,
    estimate_pullback] using run.minimizes_step k (φ ω)

omit [MeasurableSpace Ω'] in
/-- Helper for Corollary 3.8: pulled primal iterates obey the original
pathwise point update. -/
private lemma pullPoint_succ
    (run : StochasticRun h oracle ℙ x₀ multiplier₀ params Q B b)
    (φ : Ω' → Ω) (k : ℕ) (ω : Ω') :
    pullPoint run φ (k + 1) ω =
      pullPoint run φ k ω + pullStep run φ k ω := by
  exact run.point_succ k (φ ω)

omit [MeasurableSpace Ω'] in
/-- Helper for Corollary 3.8: pulled multiplier iterates obey the original
pathwise multiplier update. -/
private lemma pullMultiplier_succ
    (run : StochasticRun h oracle ℙ x₀ multiplier₀ params Q B b)
    (φ : Ω' → Ω) (k : ℕ) (ω : Ω') :
    pullMultiplier run φ (k + 1) ω = pullMultiplier run φ k ω +
      PositivePenaltyParameters.rho params • c (pullPoint run φ (k + 1) ω) := by
  exact run.multiplier_succ k (φ ω)

/-- Helper for Corollary 3.8: a stochastic run can be transported to any
probability space mapping measure-preservingly to its original space. -/
noncomputable def pullback
    (run : StochasticRun h oracle ℙ x₀ multiplier₀ params Q B b)
    (φ : Ω' → Ω) (hφ : MeasurePreserving φ ℙ' ℙ) :
    StochasticRun h oracle ℙ' x₀ multiplier₀ params Q B b :=
  { sample := pullSample run φ
    point := pullPoint run φ
    multiplier := pullMultiplier run φ
    step := pullStep run φ
    hasLaw_sample := pullSample_hasLaw run φ hφ
    independent_sample := pullSample_iIndepFun run φ hφ
    independent_preBatchState_sample := pullPreBatchState_indep_sample run φ hφ
    aemeasurable_rawEstimate := pullRawEstimate_aemeasurable run φ hφ
    aemeasurable_point := pullPoint_aemeasurable run φ hφ
    aemeasurable_multiplier := pullMultiplier_aemeasurable run φ hφ
    aemeasurable_step := pullStep_aemeasurable run φ hφ
    point_zero := pullPoint_zero run φ
    multiplier_zero := pullMultiplier_zero run φ
    minimizes_step := pullStep_minimizes run φ
    point_succ := pullPoint_succ run φ
    multiplier_succ := pullMultiplier_succ run φ }

/-- Helper for Corollary 3.8: the sample projection of a pulled stochastic run
is the pulled sample sequence. -/
@[simp] private theorem pullback_sample
    (run : StochasticRun h oracle ℙ x₀ multiplier₀ params Q B b)
    (φ : Ω' → Ω) (hφ : MeasurePreserving φ ℙ' ℙ) :
    (pullback run φ hφ).sample = pullSample run φ := rfl

/-- Helper for Corollary 3.8: the point projection of a pulled stochastic run
is the pulled point sequence. -/
@[simp] private theorem pullback_point
    (run : StochasticRun h oracle ℙ x₀ multiplier₀ params Q B b)
    (φ : Ω' → Ω) (hφ : MeasurePreserving φ ℙ' ℙ) :
    (pullback run φ hφ).point = pullPoint run φ := rfl

/-- Helper for Corollary 3.8: the multiplier projection of a pulled stochastic
run is the pulled multiplier sequence. -/
@[simp] private theorem pullback_multiplier
    (run : StochasticRun h oracle ℙ x₀ multiplier₀ params Q B b)
    (φ : Ω' → Ω) (hφ : MeasurePreserving φ ℙ' ℙ) :
    (pullback run φ hφ).multiplier = pullMultiplier run φ := rfl

/-- Helper for Corollary 3.8: the step projection of a pulled stochastic run
is the pulled step sequence. -/
@[simp] private theorem pullback_step
    (run : StochasticRun h oracle ℙ x₀ multiplier₀ params Q B b)
    (φ : Ω' → Ω) (hφ : MeasurePreserving φ ℙ' ℙ) :
    (pullback run φ hφ).step = pullStep run φ := rfl

end StochasticRun

/-- Helper for Corollary 3.8: the complete observable trajectory of a
stochastic run records its samples, points, multipliers, and steps. -/
abbrev AttemptTrajectory (Ξ : Type u) (n m : ℕ) :=
  (ℕ → ℕ → Ξ) ×
    (ℕ → EuclideanSpace ℝ (Fin n)) ×
    (ℕ → EuclideanSpace ℝ (Fin m)) ×
    (ℕ → EuclideanSpace ℝ (Fin n))

namespace StochasticRun

variable {Q B b : ℕ+}

/-- Helper for Corollary 3.8: package every random component of one stochastic
run into its complete trajectory observable. -/
def trajectory
    (run : StochasticRun h oracle ℙ x₀ multiplier₀ params Q B b)
    (ω : Ω) : AttemptTrajectory Ξ n m :=
  (fun k j ↦ run.sample k j ω,
    fun k ↦ run.point k ω,
    fun k ↦ run.multiplier k ω,
    fun k ↦ run.step k ω)

/-- Helper for Corollary 3.8: the complete trajectory observable of a
stochastic run is almost everywhere measurable. -/
lemma aemeasurable_trajectory
    (run : StochasticRun h oracle ℙ x₀ multiplier₀ params Q B b) :
    AEMeasurable run.trajectory ℙ := by
  have hsample : AEMeasurable
      (fun ω k j ↦ run.sample k j ω) ℙ := by
    apply aemeasurable_pi_lambda
    intro k
    apply aemeasurable_pi_lambda
    intro j
    exact (run.hasLaw_sample k j).aemeasurable
  have hpoint : AEMeasurable (fun ω k ↦ run.point k ω) ℙ := by
    apply aemeasurable_pi_lambda
    exact run.aemeasurable_point
  have hmultiplier : AEMeasurable (fun ω k ↦ run.multiplier k ω) ℙ := by
    apply aemeasurable_pi_lambda
    exact run.aemeasurable_multiplier
  have hstep : AEMeasurable (fun ω k ↦ run.step k ω) ℙ := by
    apply aemeasurable_pi_lambda
    exact run.aemeasurable_step
  exact hsample.prodMk (hpoint.prodMk (hmultiplier.prodMk hstep))

end StochasticRun

/-- Helper for Corollary 3.8: one restart block consists of an output selector
and a complete canonical oracle-noise array. -/
abbrev CanonicalRestartBlock (Ξ : Type u) := ℕ × CanonicalSampleSpace Ξ

/-- Helper for Corollary 3.8: one restart block has the independent product law
of a uniform selector and a canonical oracle-noise array. -/
noncomputable def canonicalRestartBlockMeasure
    (ν : Measure Ξ) (K : ℕ) (hK : 2 ≤ K) :
    Measure (CanonicalRestartBlock Ξ) :=
  (indexLaw K hK).toMeasure.prod (canonicalProductMeasure ν)

/-- Helper for Corollary 3.8: each canonical restart block carries a
probability measure. -/
instance canonicalRestartBlockMeasure.instIsProbabilityMeasure
    (K : ℕ) (hK : 2 ≤ K) :
    IsProbabilityMeasure (canonicalRestartBlockMeasure ν K hK) := by
  unfold canonicalRestartBlockMeasure
  infer_instance

/-- Helper for Corollary 3.8: the canonical restart sample space contains one
independent selector-and-noise block for each attempt. -/
abbrev CanonicalRestartSampleSpace (Ξ : Type u) :=
  ℕ → CanonicalRestartBlock Ξ

/-- Helper for Corollary 3.8: the canonical restart law is the countable
product of independent selector-and-noise block laws. -/
noncomputable def canonicalRestartMeasure
    (ν : Measure Ξ) (K : ℕ) (hK : 2 ≤ K) :
    Measure (CanonicalRestartSampleSpace Ξ) :=
  Measure.infinitePi (fun _ : ℕ ↦ canonicalRestartBlockMeasure ν K hK)

/-- Helper for Corollary 3.8: the canonical restart product law is a
probability measure. -/
instance canonicalRestartMeasure.instIsProbabilityMeasure
    (K : ℕ) (hK : 2 ≤ K) :
    IsProbabilityMeasure (canonicalRestartMeasure ν K hK) := by
  unfold canonicalRestartMeasure
  infer_instance

namespace CanonicalRestart

variable {K : ℕ} {hK : 2 ≤ K}

/-- Helper for Corollary 3.8: expose the selector-and-noise block assigned to
attempt `i`. -/
def block (i : ℕ) (ω : CanonicalRestartSampleSpace Ξ) :
    CanonicalRestartBlock Ξ :=
  ω i

/-- Helper for Corollary 3.8: expose the uniform output selector assigned to
attempt `i`. -/
def outputIndex (i : ℕ) (ω : CanonicalRestartSampleSpace Ξ) : ℕ :=
  (ω i).1

/-- Helper for Corollary 3.8: expose the complete canonical oracle-noise array
assigned to attempt `i`. -/
def noise (i : ℕ) (ω : CanonicalRestartSampleSpace Ξ) :
    CanonicalSampleSpace Ξ :=
  (ω i).2

/-- Helper for Corollary 3.8: evaluation at one attempt coordinate preserves
the corresponding block law. -/
lemma measurePreserving_block (i : ℕ) :
    MeasurePreserving (block (Ξ := Ξ) i) (canonicalRestartMeasure ν K hK)
      (canonicalRestartBlockMeasure ν K hK) := by
  exact measurePreserving_eval_infinitePi
    (fun _ : ℕ ↦ canonicalRestartBlockMeasure ν K hK) i

/-- Helper for Corollary 3.8: every attempt selector has the required uniform
output-index law. -/
lemma outputIndex_hasLaw (i : ℕ) :
    ProbabilityTheory.HasLaw (outputIndex (Ξ := Ξ) i)
      (indexLaw K hK).toMeasure (canonicalRestartMeasure ν K hK) := by
  have hfst : MeasurePreserving Prod.fst
      (canonicalRestartBlockMeasure ν K hK) (indexLaw K hK).toMeasure := by
    exact measurePreserving_fst
  have hcomp := hfst.comp (measurePreserving_block (Ξ := Ξ) (ν := ν) i)
  unfold outputIndex
  simpa only [block, Function.comp_def] using hcomp.hasLaw

/-- Helper for Corollary 3.8: the noise projection of one attempt preserves
the canonical oracle product law. -/
lemma measurePreserving_noise (i : ℕ) :
    MeasurePreserving (noise (Ξ := Ξ) i) (canonicalRestartMeasure ν K hK)
      (canonicalProductMeasure ν) := by
  have hsnd : MeasurePreserving Prod.snd
      (canonicalRestartBlockMeasure ν K hK) (canonicalProductMeasure ν) := by
    exact measurePreserving_snd
  have hcomp := hsnd.comp (measurePreserving_block (Ξ := Ξ) (ν := ν) i)
  unfold noise
  simpa only [block, Function.comp_def] using hcomp

/-- Helper for Corollary 3.8: lift a scheduled run to the full-tail coupling
attempt `i` by feeding it only the oracle-noise array in that attempt's product
block. -/
noncomputable def attempt
    (run : SPIDER.ScheduledRun h oracle (canonicalProductMeasure ν)
      x₀ multiplier₀ params K)
    (i : ℕ) :
    SPIDER.ScheduledRun h oracle (canonicalRestartMeasure ν K hK)
      x₀ multiplier₀ params K :=
  StochasticRun.pullback run (noise (Ξ := Ξ) i)
    (measurePreserving_noise (Ξ := Ξ) (ν := ν) i)

/-- Helper for Corollary 3.8: the complete observable in one block consists of
its selector and the trajectory generated from its noise component. -/
noncomputable def blockObservable
    (run : SPIDER.ScheduledRun h oracle (canonicalProductMeasure ν)
      x₀ multiplier₀ params K)
    (z : CanonicalRestartBlock Ξ) : ℕ × AttemptTrajectory Ξ n m :=
  (z.1, run.trajectory z.2)

/-- Helper for Corollary 3.8: the complete observable attached to one product
block is almost everywhere measurable. -/
lemma aemeasurable_blockObservable
    (run : SPIDER.ScheduledRun h oracle (canonicalProductMeasure ν)
      x₀ multiplier₀ params K) :
    AEMeasurable (blockObservable run) (canonicalRestartBlockMeasure ν K hK) := by
  have hselector : AEMeasurable
      (fun z : CanonicalRestartBlock Ξ ↦ z.1)
      (canonicalRestartBlockMeasure ν K hK) := measurable_fst.aemeasurable
  have htrajectory : AEMeasurable
      (fun z : CanonicalRestartBlock Ξ ↦ run.trajectory z.2)
      (canonicalRestartBlockMeasure ν K hK) :=
    run.aemeasurable_trajectory.comp_quasiMeasurePreserving
      (measurePreserving_snd.quasiMeasurePreserving)
  exact hselector.prodMk htrajectory

/-- Helper for Corollary 3.8: within one block, its selector is independent of
the complete trajectory generated by its noise array. -/
lemma block_outputIndex_indep_trajectory
    (run : SPIDER.ScheduledRun h oracle (canonicalProductMeasure ν)
      x₀ multiplier₀ params K) :
    ProbabilityTheory.IndepFun
      (fun z : CanonicalRestartBlock Ξ ↦ z.1)
      (fun z : CanonicalRestartBlock Ξ ↦ run.trajectory z.2)
      (canonicalRestartBlockMeasure ν K hK) := by
  exact ProbabilityTheory.indepFun_prod₀ measurable_id.aemeasurable
    run.aemeasurable_trajectory

/-- Helper for Corollary 3.8: within every lifted attempt, the uniform selector
is independent of the complete run trajectory. -/
lemma outputIndex_indep_attempt
    (run : SPIDER.ScheduledRun h oracle (canonicalProductMeasure ν)
      x₀ multiplier₀ params K)
    (i : ℕ) :
    ProbabilityTheory.IndepFun (outputIndex (Ξ := Ξ) i)
      (fun ω ↦ (attempt (hK := hK) run i).trajectory ω)
      (canonicalRestartMeasure ν K hK) := by
  let U : CanonicalRestartBlock Ξ → ℕ := fun z ↦ z.1
  let V : CanonicalRestartBlock Ξ → AttemptTrajectory Ξ n m :=
    fun z ↦ run.trajectory z.2
  have hU : AEMeasurable U (canonicalRestartBlockMeasure ν K hK) :=
    measurable_fst.aemeasurable
  have hV : AEMeasurable V (canonicalRestartBlockMeasure ν K hK) :=
    run.aemeasurable_trajectory.comp_quasiMeasurePreserving
      measurePreserving_snd.quasiMeasurePreserving
  have hIndep : ProbabilityTheory.IndepFun U V
      (canonicalRestartBlockMeasure ν K hK) := by
    exact block_outputIndex_indep_trajectory (hK := hK) run
  have hPull := indepFun_comp_measurePreserving
    (measurePreserving_block (Ξ := Ξ) (ν := ν) i) hU hV hIndep
  unfold outputIndex
  simpa only [U, V, block, noise, attempt, StochasticRun.trajectory,
    StochasticRun.pullback_sample, StochasticRun.pullback_point,
    StochasticRun.pullback_multiplier, StochasticRun.pullback_step,
    StochasticRun.pullSample, StochasticRun.pullPoint,
    StochasticRun.pullMultiplier, StochasticRun.pullStep] using hPull

/-- Helper for Corollary 3.8: the complete lifted attempt observables are
mutually independent across the countable restart product. -/
lemma independent_attempt
    (run : SPIDER.ScheduledRun h oracle (canonicalProductMeasure ν)
      x₀ multiplier₀ params K) :
    ProbabilityTheory.iIndepFun
      (fun i ω ↦
        (outputIndex (Ξ := Ξ) i ω, (attempt (hK := hK) run i).trajectory ω))
      (canonicalRestartMeasure ν K hK) := by
  have hBlock : ProbabilityTheory.iIndepFun
      (fun i (ω : CanonicalRestartSampleSpace Ξ) ↦ ω i)
      (canonicalRestartMeasure ν K hK) := by
    exact ProbabilityTheory.iIndepFun_infinitePi
      (P := fun _ : ℕ ↦ canonicalRestartBlockMeasure ν K hK)
      (X := fun _ z ↦ z) (fun _ ↦ measurable_id)
  have hEval (i : ℕ) : AEMeasurable
      (fun ω : CanonicalRestartSampleSpace Ξ ↦ ω i)
      (canonicalRestartMeasure ν K hK) :=
    (measurable_pi_apply i).aemeasurable
  have hObservable (i : ℕ) : AEMeasurable (blockObservable run)
      ((canonicalRestartMeasure ν K hK).map
        (fun ω : CanonicalRestartSampleSpace Ξ ↦ ω i)) := by
    have hmap : (canonicalRestartMeasure ν K hK).map
        (fun ω : CanonicalRestartSampleSpace Ξ ↦ ω i) =
        canonicalRestartBlockMeasure ν K hK := by
      exact (measurePreserving_eval_infinitePi
        (fun _ : ℕ ↦ canonicalRestartBlockMeasure ν K hK) i).map_eq
    rw [hmap]
    exact aemeasurable_blockObservable (hK := hK) run
  have hComposed := hBlock.comp₀ (fun _ ↦ blockObservable run) hEval hObservable
  unfold outputIndex
  simpa only [blockObservable, noise, attempt, StochasticRun.trajectory,
    StochasticRun.pullback_sample, StochasticRun.pullback_point,
    StochasticRun.pullback_multiplier, StochasticRun.pullback_step,
    StochasticRun.pullSample, StochasticRun.pullPoint,
    StochasticRun.pullMultiplier, StochasticRun.pullStep,
    Function.comp_def] using hComposed

/-- Helper for Corollary 3.8: any scheduled run on the canonical oracle product
space induces a full-tail safeguarded restart coupling on the explicit countable
product space. -/
theorem safeguardedRestart_nonempty_of_scheduledRun
    (run : SPIDER.ScheduledRun h oracle (canonicalProductMeasure ν)
      x₀ multiplier₀ params K)
    (X : Set (EuclideanSpace ℝ (Fin n))) :
    Nonempty (SafeguardedRestart h oracle (canonicalRestartMeasure ν K hK)
      x₀ multiplier₀ params K hK X) := by
  exact ⟨SafeguardedRestart.mk
    (attempt (hK := hK) run)
    (outputIndex (Ξ := Ξ))
    (outputIndex_hasLaw (Ξ := Ξ) (ν := ν))
    (outputIndex_indep_attempt (hK := hK) run)
    (independent_attempt (hK := hK) run)⟩

end CanonicalRestart

/-- Corollary 3.8: under the explicit global smoothness hypothesis used by the
optional canonical full-tail solver, the countable product probability space supports
mutually independent full-tail restart witnesses with independent uniform
selectors. -/
theorem canonicalSafeguardedRestart_nonempty
    (hc : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) c)
    (K : ℕ) (hK : 2 ≤ K) (X : Set (EuclideanSpace ℝ (Fin n))) :
    Nonempty (SafeguardedRestart h oracle (canonicalRestartMeasure ν K hK)
      x₀ multiplier₀ params K hK X) := by
  exact CanonicalRestart.safeguardedRestart_nonempty_of_scheduledRun
    (canonicalScheduledRun hc K) X

/-- Helper for Corollary 3.8: choose the canonical full-tail restart coupling
carried by the explicit countable product probability space. -/
noncomputable def canonicalSafeguardedRestart
    (hc : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) c)
    (K : ℕ) (hK : 2 ≤ K) (X : Set (EuclideanSpace ℝ (Fin n))) :
    SafeguardedRestart h oracle (canonicalRestartMeasure ν K hK)
      x₀ multiplier₀ params K hK X :=
  Classical.choice (canonicalSafeguardedRestart_nonempty hc K hK X)

end LALM

end
