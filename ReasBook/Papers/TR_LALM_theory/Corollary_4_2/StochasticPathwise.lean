/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@5bf5af722d85bd5c98368c41c4066124a15e8fd3:ReasBook/Papers/TR_LALM_theory/README.md (formalization contributor).
-/

module

public import TR_LALM_theory.Corollary_4_2.Stochastic

public section

open MeasureTheory
open scoped ENNReal NNReal

namespace LALM.Correction.StochasticRun

universe u v

variable {n m : ℕ}
variable {f : EuclideanSpace ℝ (Fin n) → ℝ}
variable {c : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m)}
variable {x₀ : EuclideanSpace ℝ (Fin n)}
variable {multiplier₀ : EuclideanSpace ℝ (Fin m)}
variable {Ξ : Type u} [MeasurableSpace Ξ] {ν : Measure Ξ} [IsProbabilityMeasure ν]
variable {Ω : Type v} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
variable {h : EqualityConstrained.Regularity f c}
variable {oracle : EqualityConstrained.StochasticOracle f h.region ν}
variable {params : Parameters h x₀ multiplier₀}

/-- Helper for Corollary 4.2: the corrected run-facing estimator is the
clipped recursive SPIDER estimate. -/
noncomputable def gradientEstimate
    {Q B b : ℕ+}
    (run : StochasticRun h oracle P x₀ multiplier₀ params Q B b)
    (k : ℕ) (ω : Ω) : EuclideanSpace ℝ (Fin n) :=
  SPIDER.estimate h.gradientBound oracle run.point run.sample Q B b k ω

/-- Helper for Corollary 4.2: the corrected estimator evaluates to the
prescribed clipped raw estimate. -/
theorem gradientEstimate_apply
    {Q B b : ℕ+}
    (run : StochasticRun h oracle P x₀ multiplier₀ params Q B b)
    (k : ℕ) (ω : Ω) :
    run.gradientEstimate k ω =
      SPIDER.estimate h.gradientBound oracle run.point run.sample Q B b k ω := by
  -- Expose the proof-free estimator definition.
  rfl

/-- Helper for Corollary 4.2: the corrected stochastic gradient error is the
clipped estimator minus the objective gradient. -/
noncomputable def gradientError
    {Q B b : ℕ+}
    (run : StochasticRun h oracle P x₀ multiplier₀ params Q B b)
    (k : ℕ) (ω : Ω) : EuclideanSpace ℝ (Fin n) :=
  run.gradientEstimate k ω - gradient f (run.point k ω)

/-- Helper for Corollary 4.2: the corrected gradient error has its defining
pointwise subtraction formula. -/
theorem gradientError_apply
    {Q B b : ℕ+}
    (run : StochasticRun h oracle P x₀ multiplier₀ params Q B b)
    (k : ℕ) (ω : Ω) :
    run.gradientError k ω =
      run.gradientEstimate k ω - gradient f (run.point k ω) := by
  -- Expose the proof-free gradient-error definition.
  rfl

/-- Helper for Corollary 4.2: the corrected gradient-error mean square is its
Bochner integral under the run law. -/
noncomputable def gradientErrorMeanSquare
    {Q B b : ℕ+}
    (run : StochasticRun h oracle P x₀ multiplier₀ params Q B b)
    (k : ℕ) : ℝ :=
  ∫ ω, ‖run.gradientError k ω‖ ^ 2 ∂P

/-- Helper for Corollary 4.2: the corrected gradient-error mean square exposes
its defining integral. -/
theorem gradientErrorMeanSquare_def
    {Q B b : ℕ+}
    (run : StochasticRun h oracle P x₀ multiplier₀ params Q B b)
    (k : ℕ) :
    run.gradientErrorMeanSquare k =
      ∫ ω, ‖run.gradientError k ω‖ ^ 2 ∂P := by
  -- Expose the proof-free moment definition.
  rfl

/-- Helper for Corollary 4.2: the corrected base-step mean square is its
Bochner integral under the run law. -/
noncomputable def baseStepMeanSquare
    {Q B b : ℕ+}
    (run : StochasticRun h oracle P x₀ multiplier₀ params Q B b)
    (k : ℕ) : ℝ :=
  ∫ ω, ‖run.baseStep k ω‖ ^ 2 ∂P

/-- Helper for Corollary 4.2: the corrected base-step mean square exposes its
defining integral. -/
theorem baseStepMeanSquare_def
    {Q B b : ℕ+}
    (run : StochasticRun h oracle P x₀ multiplier₀ params Q B b)
    (k : ℕ) :
    run.baseStepMeanSquare k = ∫ ω, ‖run.baseStep k ω‖ ^ 2 ∂P := by
  -- Expose the proof-free moment definition.
  rfl

/-- Helper for Corollary 4.2: a corrected stochastic prefix is pathwise
admissible when every corrected transition is admissible on every sample path. -/
def IsAdmissiblePrefix
    {Q B b : ℕ+}
    (run : StochasticRun h oracle P x₀ multiplier₀ params Q B b)
    (K : ℕ) : Prop :=
  ∀ k < K, ∀ ω, IsAdmissible h (run.point k ω) (run.baseStep k ω)

/-- Helper for Corollary 4.2: pathwise corrected prefix admissibility is its
pointwise transition condition. -/
theorem isAdmissiblePrefix_iff
    {Q B b : ℕ+}
    (run : StochasticRun h oracle P x₀ multiplier₀ params Q B b)
    (K : ℕ) :
    run.IsAdmissiblePrefix K ↔
      ∀ k < K, ∀ ω, IsAdmissible h (run.point k ω) (run.baseStep k ω) := by
  -- Expose the proof-free pathwise-prefix predicate.
  rfl

/-- Helper for Corollary 4.2: pathwise corrected admissibility implies its
almost-sure counterpart. -/
theorem IsAdmissiblePrefix.isAE
    {Q B b : ℕ+}
    {run : StochasticRun h oracle P x₀ multiplier₀ params Q B b} {K : ℕ}
    (h_admissible : run.IsAdmissiblePrefix K) :
    run.IsAEAdmissiblePrefix K := by
  -- Rewrite through the owner API, then regard the pathwise certificate as an AE one.
  apply (isAEAdmissiblePrefix_iff run K).2
  filter_upwards [] with ω
  intro k hk
  exact (isAdmissible_iff h _ _).mp (h_admissible k hk ω)

/-- Helper for Corollary 4.2: fresh-batch adaptedness up to a horizon records
independence of each corrected pre-batch state from that iteration's samples. -/
def HasFreshBatches
    {Q B b : ℕ+}
    (run : StochasticRun h oracle P x₀ multiplier₀ params Q B b) (K : ℕ) : Prop :=
  ∀ k < K, ProbabilityTheory.IndepFun
    (fun ω ↦
      (run.point k ω, run.point (k - 1) ω, run.multiplier k ω,
        if k = 0 then 0 else
          SPIDER.rawEstimate oracle run.point run.sample Q B b (k - 1) ω))
    (fun ω i ↦ run.sample k i ω) P

/-- Helper for Corollary 4.2: corrected fresh-batch adaptedness exposes its
horizon-indexed pre-batch-state independence condition. -/
theorem hasFreshBatches_iff
    {Q B b : ℕ+}
    (run : StochasticRun h oracle P x₀ multiplier₀ params Q B b) (K : ℕ) :
    run.HasFreshBatches K ↔ ∀ k < K, ProbabilityTheory.IndepFun
      (fun ω ↦
        (run.point k ω, run.point (k - 1) ω, run.multiplier k ω,
          if k = 0 then 0 else
            SPIDER.rawEstimate oracle run.point run.sample Q B b (k - 1) ω))
      (fun ω i ↦ run.sample k i ω) P := by
  -- Expose the proof-free horizon-indexed adaptedness predicate.
  rfl

/-- Helper for Corollary 4.2: every corrected run has the fresh-batch
adaptedness stored by its owner contract at every finite horizon. -/
theorem hasFreshBatches
    {Q B b : ℕ+}
    (run : StochasticRun h oracle P x₀ multiplier₀ params Q B b) (K : ℕ) :
    run.HasFreshBatches K := by
  -- Project the owner-stored independence certificate at each requested index.
  intro k _
  exact run.independent_preBatchState_sample k

omit [MeasurableSpace Ω] in
/-- Helper for Corollary 4.2: the raw SPIDER estimate commutes with a common
reindexing of all sample-space-dependent inputs. -/
private lemma rawEstimate_comp_right
    {Q B b : ℕ+}
    (point : ℕ → Ω → EuclideanSpace ℝ (Fin n))
    (sample : ℕ → ℕ → Ω → Ξ) (redirect : Ω → Ω) (k : ℕ) (ω : Ω) :
    SPIDER.rawEstimate oracle
        (fun j ω' ↦ point j (redirect ω'))
        (fun j i ω' ↦ sample j i (redirect ω')) Q B b k ω =
      SPIDER.rawEstimate oracle point sample Q B b k (redirect ω) := by
  -- Follow the recursive estimator, with the update branch using the induction result.
  induction k with
  | zero => rfl
  | succ k ih =>
      simp only [SPIDER.rawEstimate]
      split
      · rfl
      · simp only [ih]

/-- Helper for Corollary 4.2: an almost-surely admissible corrected run has an
almost-everywhere equal version whose prefix is admissible on every sample path. -/
theorem IsAEAdmissiblePrefix.exists_pathwiseVersion
    {Q B b : ℕ+}
    (run : StochasticRun h oracle P x₀ multiplier₀ params Q B b)
    (K : ℕ) (h_admissible : run.IsAEAdmissiblePrefix K) :
    ∃ run' : StochasticRun h oracle P x₀ multiplier₀ params Q B b,
      run'.IsAdmissiblePrefix K ∧
      (∀ k, run'.point k =ᵐ[P] run.point k) ∧
      (∀ k, run'.multiplier k =ᵐ[P] run.multiplier k) ∧
      (∀ k, run'.baseStep k =ᵐ[P] run.baseStep k) ∧
      (∀ k, run'.gradientError k =ᵐ[P] run.gradientError k) := by
  classical
  -- Redirect exceptional sample paths to one path satisfying every prefix condition.
  let Good : Ω → Prop := fun ω ↦ ∀ k < K,
    IsAdmissible h (run.point k ω) (run.baseStep k ω)
  have hGoodAE : ∀ᵐ ω ∂P, Good ω := by
    filter_upwards [(isAEAdmissiblePrefix_iff run K).mp h_admissible] with ω hω
    intro k hk
    exact (isAdmissible_iff h _ _).mpr (hω k hk)
  obtain ⟨ω₀, hω₀⟩ := hGoodAE.exists
  let redirect : Ω → Ω := fun ω ↦ if Good ω then ω else ω₀
  have hredirectGood (ω : Ω) : Good (redirect ω) := by
    by_cases hω : Good ω
    · simp only [redirect, hω, if_true]
    · simpa only [redirect, hω, if_false] using hω₀
  have hredirectEq : ∀ᵐ ω ∂P, redirect ω = ω := by
    filter_upwards [hGoodAE] with ω hω
    simp only [redirect, hω, if_true]
  let sample' : ℕ → ℕ → Ω → Ξ :=
    fun k i ω ↦ run.sample k i (redirect ω)
  let point' : ℕ → Ω → EuclideanSpace ℝ (Fin n) :=
    fun k ω ↦ run.point k (redirect ω)
  let multiplier' : ℕ → Ω → EuclideanSpace ℝ (Fin m) :=
    fun k ω ↦ run.multiplier k (redirect ω)
  let baseStep' : ℕ → Ω → EuclideanSpace ℝ (Fin n) :=
    fun k ω ↦ run.baseStep k (redirect ω)
  -- Record simultaneous almost-everywhere equality for every redirected component.
  have hsampleAE (k i : ℕ) : sample' k i =ᵐ[P] run.sample k i := by
    filter_upwards [hredirectEq] with ω hω
    simp only [sample', hω]
  have hpointAE (k : ℕ) : point' k =ᵐ[P] run.point k := by
    filter_upwards [hredirectEq] with ω hω
    simp only [point', hω]
  have hmultiplierAE (k : ℕ) : multiplier' k =ᵐ[P] run.multiplier k := by
    filter_upwards [hredirectEq] with ω hω
    simp only [multiplier', hω]
  have hbaseStepAE (k : ℕ) : baseStep' k =ᵐ[P] run.baseStep k := by
    filter_upwards [hredirectEq] with ω hω
    simp only [baseStep', hω]
  -- Normalize the redirected recursive estimator once for measurability and independence.
  have hraw (k : ℕ) (ω : Ω) :
      SPIDER.rawEstimate oracle point' sample' Q B b k ω =
        SPIDER.rawEstimate oracle run.point run.sample Q B b k (redirect ω) := by
    exact rawEstimate_comp_right run.point run.sample redirect k ω
  have hrawAE (k : ℕ) :
      SPIDER.rawEstimate oracle point' sample' Q B b k =ᵐ[P]
        SPIDER.rawEstimate oracle run.point run.sample Q B b k := by
    filter_upwards [hredirectEq] with ω hω
    rw [hraw, hω]
  have hstateAE (k : ℕ) :
      (fun ω ↦
        (run.point k ω, run.point (k - 1) ω, run.multiplier k ω,
          if k = 0 then 0 else
            SPIDER.rawEstimate oracle run.point run.sample Q B b (k - 1) ω))
        =ᵐ[P]
      (fun ω ↦
        (point' k ω, point' (k - 1) ω, multiplier' k ω,
          if k = 0 then 0 else
            SPIDER.rawEstimate oracle point' sample' Q B b (k - 1) ω)) := by
    filter_upwards [hredirectEq] with ω hω
    simp only [point', multiplier', hω]
    split
    · rfl
    · rw [hraw, hω]
  have hbatchAE (k : ℕ) :
      (fun ω i ↦ run.sample k i ω) =ᵐ[P]
        (fun ω i ↦ sample' k i ω) := by
    filter_upwards [hredirectEq] with ω hω
    funext i
    simp only [sample', hω]
  have hminimizes (k : ℕ) (ω : Ω) :
      IsMinOn (LALM.stepModelWithGradient c
        (SPIDER.estimate h.gradientBound oracle point' sample' Q B b k ω)
        params.rho params.beta (point' k ω) (multiplier' k ω))
          Set.univ (baseStep' k ω) := by
    simpa only [point', multiplier', baseStep', SPIDER.estimate_apply, hraw] using
      run.minimizes_baseStep k (redirect ω)
  -- Reassemble a corrected run whose stochastic laws agree almost everywhere.
  let run' : StochasticRun h oracle P x₀ multiplier₀ params Q B b :=
    { sample := sample'
      point := point'
      multiplier := multiplier'
      baseStep := baseStep'
      hasLaw_sample := fun k i ↦
        (run.hasLaw_sample k i).congr (hsampleAE k i)
      independent_sample := ProbabilityTheory.iIndepFun.congr
        (fun ki ↦ (hsampleAE ki.1 ki.2).symm) run.independent_sample
      independent_preBatchState_sample := fun k ↦
        (run.independent_preBatchState_sample k).congr (hstateAE k) (hbatchAE k)
      aemeasurable_rawEstimate := fun k ↦
        (run.aemeasurable_rawEstimate k).congr (hrawAE k).symm
      aemeasurable_point := fun k ↦
        (run.aemeasurable_point k).congr (hpointAE k).symm
      aemeasurable_multiplier := fun k ↦
        (run.aemeasurable_multiplier k).congr (hmultiplierAE k).symm
      aemeasurable_baseStep := fun k ↦
        (run.aemeasurable_baseStep k).congr (hbaseStepAE k).symm
      point_zero := fun ω ↦ run.point_zero (redirect ω)
      multiplier_zero := fun ω ↦ run.multiplier_zero (redirect ω)
      minimizes_baseStep := hminimizes
      point_succ := fun k ω ↦ run.point_succ k (redirect ω)
      multiplier_succ := fun k ω ↦ run.multiplier_succ k (redirect ω) }
  have hgradientErrorAE (k : ℕ) :
      run'.gradientError k =ᵐ[P] run.gradientError k := by
    filter_upwards [hredirectEq] with ω hω
    rw [run'.gradientError_apply, run.gradientError_apply,
      run'.gradientEstimate_apply, run.gradientEstimate_apply]
    change SPIDER.clip h.gradientBound
        (SPIDER.rawEstimate oracle point' sample' Q B b k ω) -
          gradient f (point' k ω) =
      SPIDER.clip h.gradientBound
        (SPIDER.rawEstimate oracle run.point run.sample Q B b k ω) -
          gradient f (run.point k ω)
    rw [hraw, hω]
    simp only [point', hω]
  -- Package pathwise admissibility with all componentwise transport facts.
  refine ⟨run', ?_, ?_, ?_, ?_, hgradientErrorAE⟩
  · intro k hk ω
    exact hredirectGood ω k hk
  · intro k
    exact hpointAE k
  · intro k
    exact hmultiplierAE k
  · intro k
    exact hbaseStepAE k

end LALM.Correction.StochasticRun

end
