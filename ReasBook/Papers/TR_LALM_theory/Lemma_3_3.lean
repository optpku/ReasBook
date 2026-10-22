/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@5bf5af722d85bd5c98368c41c4066124a15e8fd3:ReasBook/Papers/TR_LALM_theory/README.md (formalization contributor).
-/

module

public import TR_LALM_theory.Lemma_3_3.Iteration
public import Mathlib.Probability.Independence.Integration

public section

open MeasureTheory

namespace LALM.StochasticRun

universe u v w x

variable {n m : ℕ}
variable {Ξ : Type u} [MeasurableSpace Ξ] {ν : Measure Ξ} [IsProbabilityMeasure ν]
variable {Ω : Type v} [MeasurableSpace Ω] {ℙ : Measure Ω} [IsProbabilityMeasure ℙ]
variable {f : EuclideanSpace ℝ (Fin n) → ℝ}
variable {c : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m)}
variable {x₀ : EuclideanSpace ℝ (Fin n)}
variable {multiplier₀ : EuclideanSpace ℝ (Fin m)}
variable {h : EqualityConstrained.Regularity f c}
variable {oracle : EqualityConstrained.StochasticOracle f h.region ν}
variable {Param : Type*} [PositivePenaltyParameters Param]
variable {params : Param} {Q B b : ℕ+}

/-- Helper for Lemma 3.3: sampled gradients are almost everywhere measurable
for the product of any point law on the regularity region and the sample law. -/
private lemma measurable_sampleGradient :
    Measurable (fun z : EuclideanSpace ℝ (Fin n) × Ξ ↦
      oracle.sampleGradient z.1 z.2) :=
  oracle.measurable_sampleGradient

/-- Every batch through a horizon is independent of the state fixed before
that batch is sampled. -/
def HasFreshBatches
    (run : StochasticRun h oracle ℙ x₀ multiplier₀ params Q B b)
    (K : ℕ) : Prop :=
  ∀ k < K, ProbabilityTheory.IndepFun
    (fun ω ↦
      (run.point k ω, run.point (k - 1) ω, run.multiplier k ω,
        if k = 0 then 0 else
          SPIDER.rawEstimate oracle run.point run.sample Q B b (k - 1) ω))
    (fun ω i ↦ run.sample k i ω) ℙ

/-- Freshness through a horizon means pre-batch-state independence at every
iteration below that horizon. -/
theorem hasFreshBatches_iff
    (run : StochasticRun h oracle ℙ x₀ multiplier₀ params Q B b)
    (K : ℕ) :
    run.HasFreshBatches K ↔
      ∀ k < K, ProbabilityTheory.IndepFun
        (fun ω ↦
          (run.point k ω, run.point (k - 1) ω, run.multiplier k ω,
            if k = 0 then 0 else
              SPIDER.rawEstimate oracle run.point run.sample Q B b (k - 1) ω))
        (fun ω i ↦ run.sample k i ω) ℙ := by
  -- Unfolding the named freshness predicate exposes exactly the stated condition.
  rfl

/-- The fresh-batch condition stored by a stochastic run holds through every
finite horizon. -/
theorem hasFreshBatches
    (run : StochasticRun h oracle ℙ x₀ multiplier₀ params Q B b)
    (K : ℕ) : run.HasFreshBatches K := by
  intro k hk
  exact run.independent_preBatchState_sample k

/-- Helper for Lemma 3.3: positivity of the proximal and penalty parameters
makes the explicit-gradient quadratic model's minimizer unique. -/
private lemma stepModelWithGradientMinimizerUnique
    (c : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m))
    (g : EuclideanSpace ℝ (Fin n)) (ρ β : ℝ)
    (x : EuclideanSpace ℝ (Fin n))
    (multiplier : EuclideanSpace ℝ (Fin m))
    (p q : EuclideanSpace ℝ (Fin n)) (hρ : 0 < ρ) (hβ : 0 < β)
    (hp : IsMinOn (stepModelWithGradient c g ρ β x multiplier) Set.univ p)
    (hq : IsMinOn (stepModelWithGradient c g ρ β x multiplier) Set.univ q) :
    p = q := by
  -- Represent the prescribed vector by a linear objective so the established
  -- deterministic stationarity and pairing lemmas apply without unfolding.
  let linearObjective : EuclideanSpace ℝ (Fin n) → ℝ := fun y ↦ inner ℝ g y
  have hlinearDerivative :
      HasFDerivAt linearObjective (innerSL ℝ g) x := by
    simpa only [linearObjective, coe_innerSL_apply] using (innerSL ℝ g).hasFDerivAt
  have hlinearGradient : HasGradientAt linearObjective g x := by
    rw [hasGradientAt_iff_hasFDerivAt]
    exact hlinearDerivative
  have hgradient : gradient linearObjective x = g := hlinearGradient.gradient
  have hmodels :
      stepModel linearObjective c ρ β x multiplier =
        stepModelWithGradient c g ρ β x multiplier := by
    funext r
    rw [stepModel_eq_stepModelWithGradient, hgradient]
  have hpLinear :
      IsMinOn (stepModel linearObjective c ρ β x multiplier) Set.univ p := by
    simpa only [hmodels] using hp
  have hqLinear :
      IsMinOn (stepModel linearObjective c ρ β x multiplier) Set.univ q := by
    simpa only [hmodels] using hq
  have hpzero := stepModelGradient_eq_zero_of_minimizes linearObjective c ρ β
    x multiplier p hpLinear
  have hqzero := stepModelGradient_eq_zero_of_minimizes linearObjective c ρ β
    x multiplier q hqLinear
  have hpair := stepModelGradientPairing linearObjective c ρ β x multiplier p q
  rw [hpzero, hqzero, sub_self, inner_zero_left] at hpair
  have hpenaltyNonneg : 0 ≤ ρ * ‖fderiv ℝ c x (p - q)‖ ^ 2 :=
    mul_nonneg hρ.le (sq_nonneg _)
  have hproximalNonneg : 0 ≤ β * ‖p - q‖ ^ 2 :=
    mul_nonneg hβ.le (sq_nonneg _)
  have hproximalZero : β * ‖p - q‖ ^ 2 = 0 := by
    linarith
  have hstepNormSq : ‖p - q‖ ^ 2 = 0 :=
    (mul_eq_zero.mp hproximalZero).resolve_left hβ.ne'
  -- The positive proximal coefficient forces the minimizers to coincide.
  exact sub_eq_zero.mp (norm_eq_zero.mp (sq_eq_zero_iff.mp hstepNormSq))

/-- Helper for Lemma 3.3: agreement of all samples used through iteration `k`
forces agreement of the recursive estimator and algorithmic state through that iteration. -/
private lemma state_eq_of_usedSamples_eq
    (run : StochasticRun h oracle ℙ x₀ multiplier₀ params Q B b)
    (k : ℕ) (ω ω' : Ω)
    (hsample : ∀ t ≤ k, ∀ i < max (B : ℕ) b,
      run.sample t i ω = run.sample t i ω') :
    SPIDER.rawEstimate oracle run.point run.sample Q B b k ω =
        SPIDER.rawEstimate oracle run.point run.sample Q B b k ω' ∧
      run.point k ω = run.point k ω' ∧
      run.multiplier k ω = run.multiplier k ω' ∧
      run.step k ω = run.step k ω' ∧
      run.point (k + 1) ω = run.point (k + 1) ω' ∧
      run.multiplier (k + 1) ω = run.multiplier (k + 1) ω' := by
  induction k with
  | zero =>
      -- At iteration zero the state is fixed, while the raw estimator only
      -- reads the first refresh batch.
      have hpoint : run.point 0 ω = run.point 0 ω' := by
        rw [run.point_zero, run.point_zero]
      have hmultiplier : run.multiplier 0 ω = run.multiplier 0 ω' := by
        rw [run.multiplier_zero, run.multiplier_zero]
      have hraw :
          SPIDER.rawEstimate oracle run.point run.sample Q B b 0 ω =
            SPIDER.rawEstimate oracle run.point run.sample Q B b 0 ω' := by
        rw [SPIDER.rawEstimate_of_refresh oracle run.point run.sample Q B b 0 ω (by simp),
          SPIDER.rawEstimate_of_refresh oracle run.point run.sample Q B b 0 ω' (by simp)]
        apply congrArg (fun z : EuclideanSpace ℝ (Fin n) ↦ (B : ℝ)⁻¹ • z)
        apply Finset.sum_congr rfl
        intro i hi
        have hiB : i < B := Finset.mem_range.mp hi
        rw [run.point_zero, run.point_zero,
          hsample 0 (Nat.zero_le 0) i
            (lt_of_lt_of_le hiB (Nat.le_max_left (B : ℕ) b))]
      have hestimate :
          SPIDER.estimate h.gradientBound oracle run.point run.sample Q B b 0 ω =
            SPIDER.estimate h.gradientBound oracle run.point run.sample Q B b 0 ω' := by
        rw [SPIDER.estimate_apply, SPIDER.estimate_apply, hraw]
      have hminimizesRight := run.minimizes_step 0 ω'
      rw [← hestimate, ← hpoint, ← hmultiplier] at hminimizesRight
      have hstep : run.step 0 ω = run.step 0 ω' :=
        stepModelWithGradientMinimizerUnique c _
          (PositivePenaltyParameters.rho params)
          (PositivePenaltyParameters.beta params) _ _ _ _
          (PositivePenaltyParameters.rho_pos params)
          (PositivePenaltyParameters.beta_pos params) (run.minimizes_step 0 ω)
          hminimizesRight
      have hpointSucc : run.point (0 + 1) ω = run.point (0 + 1) ω' := by
        calc
          run.point (0 + 1) ω = run.point 0 ω + run.step 0 ω := run.point_succ 0 ω
          _ = run.point 0 ω' + run.step 0 ω' := by rw [hpoint, hstep]
          _ = run.point (0 + 1) ω' := (run.point_succ 0 ω').symm
      have hmultiplierSucc :
          run.multiplier (0 + 1) ω = run.multiplier (0 + 1) ω' := by
        calc
          run.multiplier (0 + 1) ω =
              run.multiplier 0 ω + PositivePenaltyParameters.rho params •
                c (run.point (0 + 1) ω) :=
            run.multiplier_succ 0 ω
          _ = run.multiplier 0 ω' + PositivePenaltyParameters.rho params •
              c (run.point (0 + 1) ω') := by
            rw [hmultiplier, hpointSucc]
          _ = run.multiplier (0 + 1) ω' := (run.multiplier_succ 0 ω').symm
      exact ⟨hraw, hpoint, hmultiplier, hstep, hpointSucc, hmultiplierSucc⟩
  | succ k ih =>
      -- The induction hypothesis identifies the entire pre-batch state.
      have hsamplePrevious : ∀ t ≤ k, ∀ i < max (B : ℕ) b,
          run.sample t i ω = run.sample t i ω' := by
        intro t ht i hi
        exact hsample t (Nat.le.step ht) i hi
      obtain ⟨hrawPrevious, hpointPrevious, hmultiplierPrevious, hstepPrevious,
        hpoint, hmultiplier⟩ := ih hsamplePrevious
      have hraw :
          SPIDER.rawEstimate oracle run.point run.sample Q B b (k + 1) ω =
            SPIDER.rawEstimate oracle run.point run.sample Q B b (k + 1) ω' := by
        by_cases hrefresh : (k + 1) % Q = 0
        · rw [SPIDER.rawEstimate_of_refresh oracle run.point run.sample Q B b (k + 1) ω
              hrefresh,
            SPIDER.rawEstimate_of_refresh oracle run.point run.sample Q B b (k + 1) ω'
              hrefresh]
          apply congrArg (fun z : EuclideanSpace ℝ (Fin n) ↦ (B : ℝ)⁻¹ • z)
          apply Finset.sum_congr rfl
          intro i hi
          have hiB : i < B := Finset.mem_range.mp hi
          rw [hpoint,
            hsample (k + 1) (Nat.le_refl (k + 1)) i
              (lt_of_lt_of_le hiB (Nat.le_max_left (B : ℕ) b))]
        · have hbatch :
              ∑ i ∈ Finset.range b,
                  (oracle.sampleGradient (run.point (k + 1) ω) (run.sample (k + 1) i ω) -
                    oracle.sampleGradient (run.point k ω) (run.sample (k + 1) i ω)) =
                ∑ i ∈ Finset.range b,
                  (oracle.sampleGradient (run.point (k + 1) ω') (run.sample (k + 1) i ω') -
                    oracle.sampleGradient (run.point k ω') (run.sample (k + 1) i ω')) := by
            apply Finset.sum_congr rfl
            intro i hi
            have hib : i < b := Finset.mem_range.mp hi
            rw [hpoint, hpointPrevious,
              hsample (k + 1) (Nat.le_refl (k + 1)) i
                (lt_of_lt_of_le hib (Nat.le_max_right (B : ℕ) b))]
          rw [SPIDER.rawEstimate_of_update oracle run.point run.sample Q B b k ω hrefresh,
            SPIDER.rawEstimate_of_update oracle run.point run.sample Q B b k ω' hrefresh,
            hrawPrevious, hbatch]
      have hestimate :
          SPIDER.estimate h.gradientBound oracle run.point run.sample Q B b (k + 1) ω =
            SPIDER.estimate h.gradientBound oracle run.point run.sample Q B b (k + 1) ω' := by
        rw [SPIDER.estimate_apply, SPIDER.estimate_apply, hraw]
      have hminimizesRight := run.minimizes_step (k + 1) ω'
      rw [← hestimate, ← hpoint, ← hmultiplier] at hminimizesRight
      have hstep : run.step (k + 1) ω = run.step (k + 1) ω' :=
        stepModelWithGradientMinimizerUnique c _
          (PositivePenaltyParameters.rho params)
          (PositivePenaltyParameters.beta params) _ _ _ _
          (PositivePenaltyParameters.rho_pos params)
          (PositivePenaltyParameters.beta_pos params)
          (run.minimizes_step (k + 1) ω) hminimizesRight
      have hpointSucc :
          run.point ((k + 1) + 1) ω = run.point ((k + 1) + 1) ω' := by
        calc
          run.point ((k + 1) + 1) ω =
              run.point (k + 1) ω + run.step (k + 1) ω := run.point_succ (k + 1) ω
          _ = run.point (k + 1) ω' + run.step (k + 1) ω' := by rw [hpoint, hstep]
          _ = run.point ((k + 1) + 1) ω' := (run.point_succ (k + 1) ω').symm
      have hmultiplierSucc :
          run.multiplier ((k + 1) + 1) ω = run.multiplier ((k + 1) + 1) ω' := by
        calc
          run.multiplier ((k + 1) + 1) ω = run.multiplier (k + 1) ω +
              PositivePenaltyParameters.rho params •
                c (run.point ((k + 1) + 1) ω) :=
            run.multiplier_succ (k + 1) ω
          _ = run.multiplier (k + 1) ω' +
              PositivePenaltyParameters.rho params •
                c (run.point ((k + 1) + 1) ω') := by
            rw [hmultiplier, hpointSucc]
          _ = run.multiplier ((k + 1) + 1) ω' :=
            (run.multiplier_succ (k + 1) ω').symm
      exact ⟨hraw, hpoint, hmultiplier, hstep, hpointSucc, hmultiplierSucc⟩

/-- Helper for Lemma 3.3: the state immediately before iteration `k` depends
pointwise only on sample coordinates from iterations strictly before `k`. -/
private lemma preBatchState_eq_of_pastSamples_eq
    (run : StochasticRun h oracle ℙ x₀ multiplier₀ params Q B b)
    (k : ℕ) (ω ω' : Ω)
    (hsample : ∀ t < k, ∀ i < max (B : ℕ) b,
      run.sample t i ω = run.sample t i ω') :
    run.point k ω = run.point k ω' ∧
      run.point (k - 1) ω = run.point (k - 1) ω' ∧
      run.multiplier k ω = run.multiplier k ω' ∧
      (k = 0 ∨
        SPIDER.rawEstimate oracle run.point run.sample Q B b (k - 1) ω =
          SPIDER.rawEstimate oracle run.point run.sample Q B b (k - 1) ω') := by
  cases k with
  | zero =>
      -- Before the first batch every state component is the fixed initialization.
      exact ⟨by rw [run.point_zero, run.point_zero],
        by rw [run.point_zero, run.point_zero],
        by rw [run.multiplier_zero, run.multiplier_zero], Or.inl rfl⟩
  | succ k =>
      -- The finite-history congruence at `k` supplies the state entering `k + 1`.
      have hsampleThrough : ∀ t ≤ k, ∀ i < max (B : ℕ) b,
          run.sample t i ω = run.sample t i ω' := by
        intro t ht i hi
        exact hsample t (by omega) i hi
      obtain ⟨hraw, hpointPrevious, hmultiplierPrevious, hstepPrevious,
        hpoint, hmultiplier⟩ := state_eq_of_usedSamples_eq run k ω ω' hsampleThrough
      exact ⟨hpoint, by simpa using hpointPrevious, hmultiplier,
        Or.inr (by simpa using hraw)⟩

/-- Helper for Lemma 3.3: the finite rectangle of sample coordinates strictly
before iteration `k`. -/
private def pastSampleIndices (k width : ℕ) : Finset (ℕ × ℕ) :=
  Finset.range k ×ˢ Finset.range width

/-- Helper for Lemma 3.3: the finite rectangle forming a batch at iteration `k`. -/
private def currentSampleIndices (k width : ℕ) : Finset (ℕ × ℕ) :=
  ({k} : Finset ℕ) ×ˢ Finset.range width

/-- Helper for Lemma 3.3: coordinates strictly before iteration `k` are
disjoint from every coordinate in the batch at iteration `k`. -/
private lemma pastSampleIndices_disjoint_currentSampleIndices
    (k pastWidth currentWidth : ℕ) :
    Disjoint (pastSampleIndices k pastWidth)
      (currentSampleIndices k currentWidth) := by
  -- Membership in the past rectangle gives a first coordinate below `k`,
  -- whereas membership in the current rectangle fixes that coordinate to `k`.
  rw [Finset.disjoint_left]
  rintro ⟨t, i⟩ hkiPast hkiCurrent
  have htPast : t ∈ Finset.range k := by
    exact (Finset.mem_product.mp (by simpa only [pastSampleIndices] using hkiPast)).1
  have htCurrent : t ∈ ({k} : Finset ℕ) := by
    exact (Finset.mem_product.mp
      (by simpa only [currentSampleIndices] using hkiCurrent)).1
  have htLt : t < k := Finset.mem_range.mp htPast
  have htEq : t = k := Finset.mem_singleton.mp htCurrent
  omega

/-- Helper for Lemma 3.3: the finite tuple of all samples strictly before
iteration `k`. -/
private def pastSampleTuple
    (run : StochasticRun h oracle ℙ x₀ multiplier₀ params Q B b) (k : ℕ) :
    Ω → ((ki : pastSampleIndices k (max (B : ℕ) b)) → Ξ) :=
  fun ω ki ↦ run.sample ki.1.1 ki.1.2 ω

/-- Helper for Lemma 3.3: the points, multiplier, and preceding raw estimate
that are fixed before the fresh batch at iteration `k`. -/
private noncomputable def preBatchState
    (run : StochasticRun h oracle ℙ x₀ multiplier₀ params Q B b) (k : ℕ) :
    Ω → EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) ×
      EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin n) :=
  fun ω ↦
    (run.point k ω, run.point (k - 1) ω, run.multiplier k ω,
      if k = 0 then 0 else
        SPIDER.rawEstimate oracle run.point run.sample Q B b (k - 1) ω)

/-- Helper for Lemma 3.3: the finite past-sample tuple is almost everywhere
measurable. -/
private lemma aemeasurable_pastSampleTuple
    (run : StochasticRun h oracle ℙ x₀ multiplier₀ params Q B b) (k : ℕ) :
    AEMeasurable (pastSampleTuple run k) ℙ := by
  -- Coordinatewise sample measurability gives measurability of the finite tuple.
  exact aemeasurable_pi_lambda _
    (fun ki ↦ (run.hasLaw_sample ki.1.1 ki.1.2).aemeasurable)

/-- Helper for Lemma 3.3: the state entering a fresh batch is almost everywhere
measurable. -/
private lemma aemeasurable_preBatchState
    (run : StochasticRun h oracle ℙ x₀ multiplier₀ params Q B b) (k : ℕ) :
    AEMeasurable (preBatchState run k) ℙ := by
  have hpreviousRaw : AEMeasurable
      (fun ω ↦ if k = 0 then 0 else
        SPIDER.rawEstimate oracle run.point run.sample Q B b (k - 1) ω) ℙ := by
    by_cases hk : k = 0
    · simp only [hk, ite_true]
      exact aemeasurable_const
    · simp only [hk, ite_false]
      exact run.aemeasurable_rawEstimate (k - 1)
  -- Assemble the four measurable components without unfolding the recursion.
  unfold preBatchState
  exact (run.aemeasurable_point k).prodMk
    ((run.aemeasurable_point (k - 1)).prodMk
      ((run.aemeasurable_multiplier k).prodMk hpreviousRaw))

/-- Helper for Lemma 3.3: the pre-batch state is constant on fibers of the
finite past-sample tuple. -/
private lemma preBatchState_factorsThroughPastSamples
    (run : StochasticRun h oracle ℙ x₀ multiplier₀ params Q B b) (k : ℕ) :
    (preBatchState run k).FactorsThrough (pastSampleTuple run k) := by
  intro ω ω' htuple
  have hsample : ∀ t < k, ∀ i < max (B : ℕ) b,
      run.sample t i ω = run.sample t i ω' := by
    intro t ht i hi
    have hmem : (t, i) ∈ pastSampleIndices k (max (B : ℕ) b) := by
      simp only [pastSampleIndices, Finset.mem_product, Finset.mem_range]
      exact ⟨ht, hi⟩
    have hcoordinate := congrFun htuple
      (⟨(t, i), hmem⟩ : pastSampleIndices k (max (B : ℕ) b))
    simpa only [pastSampleTuple] using hcoordinate
  obtain ⟨hpoint, hpointPrevious, hmultiplier, hrawPrevious⟩ :=
    preBatchState_eq_of_pastSamples_eq run k ω ω' hsample
  have hraw :
      (if k = 0 then 0 else
          SPIDER.rawEstimate oracle run.point run.sample Q B b (k - 1) ω) =
        if k = 0 then 0 else
          SPIDER.rawEstimate oracle run.point run.sample Q B b (k - 1) ω' := by
    by_cases hk : k = 0
    · simp only [hk, ite_true]
    · simp only [hk, ite_false]
      exact hrawPrevious.resolve_left hk
  -- The causal congruence identifies every component of the packaged state.
  simp only [preBatchState]
  rw [hpoint, hpointPrevious, hmultiplier, hraw]

/-- Helper for Lemma 3.3: a canonical set-theoretic factor of the pre-batch
state through the finite past-sample tuple. -/
private noncomputable def preBatchStateFactor
    (run : StochasticRun h oracle ℙ x₀ multiplier₀ params Q B b) (k : ℕ) :
    (((ki : pastSampleIndices k (max (B : ℕ) b)) → Ξ) →
      EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) ×
        EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin n)) :=
  Function.extend (pastSampleTuple run k) (preBatchState run k)
    (fun _ ↦ (x₀, x₀, multiplier₀, 0))

/-- Helper for Lemma 3.3: the canonical factor reconstructs the pre-batch
state on every sample path. -/
private lemma preBatchStateFactor_comp_pastSampleTuple
    (run : StochasticRun h oracle ℙ x₀ multiplier₀ params Q B b) (k : ℕ) :
    preBatchState run k = preBatchStateFactor run k ∘ pastSampleTuple run k := by
  -- Fiberwise causality is exactly the specification of `Function.extend`.
  funext ω
  symm
  simpa only [preBatchStateFactor, Function.comp_apply] using
    (preBatchState_factorsThroughPastSamples run k).extend_apply
      (fun _ ↦ (x₀, x₀, multiplier₀, 0)) ω

/-- Helper for Lemma 3.3: the tuple of all samples in the finite past is
independent of the tuple forming a fresh batch at iteration `k`. -/
private lemma indepFun_pastSamples_freshBatch
    (run : StochasticRun h oracle ℙ x₀ multiplier₀ params Q B b)
    (k width : ℕ) :
    ProbabilityTheory.IndepFun
      (fun ω (ki : pastSampleIndices k (max (B : ℕ) b)) ↦
        run.sample ki.1.1 ki.1.2 ω)
      (fun ω (ki : currentSampleIndices k width) ↦
        run.sample ki.1.1 ki.1.2 ω) ℙ := by
  -- Mutual independence specializes to the two disjoint finite rectangles.
  exact run.independent_sample.indepFun_finset₀
    (pastSampleIndices k (max (B : ℕ) b))
    (currentSampleIndices k width)
    (pastSampleIndices_disjoint_currentSampleIndices k (max (B : ℕ) b) width)
    (fun ki ↦ (run.hasLaw_sample ki.1 ki.2).aemeasurable)

/-- Helper for Lemma 3.3: an almost-everywhere measurable factor of a state
through the finite past is independent of the fresh batch. -/
private lemma indepFun_of_factorsThroughPastSamples
    (run : StochasticRun h oracle ℙ x₀ multiplier₀ params Q B b)
    (k width : ℕ) {Z : Type w} [MeasurableSpace Z]
    (state : Ω → Z)
    (factor : ((ki : pastSampleIndices k (max (B : ℕ) b)) → Ξ) → Z)
    (hfactor : AEMeasurable factor
      (ℙ.map (fun ω (ki : pastSampleIndices k (max (B : ℕ) b)) ↦
        run.sample ki.1.1 ki.1.2 ω)))
    (hstate : state =ᵐ[ℙ]
      factor ∘ (fun ω (ki : pastSampleIndices k (max (B : ℕ) b)) ↦
        run.sample ki.1.1 ki.1.2 ω)) :
    ProbabilityTheory.IndepFun state
      (fun ω (ki : currentSampleIndices k width) ↦
        run.sample ki.1.1 ki.1.2 ω) ℙ := by
  have hpast : AEMeasurable
      (fun ω (ki : pastSampleIndices k (max (B : ℕ) b)) ↦
        run.sample ki.1.1 ki.1.2 ω) ℙ := by
    exact aemeasurable_pi_lambda _
      (fun ki ↦ (run.hasLaw_sample ki.1.1 ki.1.2).aemeasurable)
  have hcurrent : AEMeasurable
      (fun ω (ki : currentSampleIndices k width) ↦
        run.sample ki.1.1 ki.1.2 ω) ℙ := by
    exact aemeasurable_pi_lambda _
      (fun ki ↦ (run.hasLaw_sample ki.1.1 ki.1.2).aemeasurable)
  have hidentity : AEMeasurable
      (id : ((ki : currentSampleIndices k width) → Ξ) →
        ((ki : currentSampleIndices k width) → Ξ))
      (ℙ.map (fun ω (ki : currentSampleIndices k width) ↦
        run.sample ki.1.1 ki.1.2 ω)) := aemeasurable_id
  have hindependent := (indepFun_pastSamples_freshBatch run k width).comp₀
    hpast hcurrent hfactor hidentity
  have hcurrentIdentity :
      id ∘ (fun ω (ki : currentSampleIndices k width) ↦
        run.sample ki.1.1 ki.1.2 ω) =ᵐ[ℙ]
      (fun ω (ki : currentSampleIndices k width) ↦
        run.sample ki.1.1 ki.1.2 ω) := Filter.EventuallyEq.rfl
  -- Replace the factored spelling by the original state using its a.e. identity.
  exact hindependent.congr hstate.symm hcurrentIdentity

/-- Helper for Lemma 3.3: the packaged state before iteration `k` is
independent of the fresh batch once its canonical finite-past factor is
almost everywhere measurable for the law of the past tuple. -/
private lemma indepFun_preBatchState_freshBatch
    (run : StochasticRun h oracle ℙ x₀ multiplier₀ params Q B b)
    (k width : ℕ)
    (hfactor : AEMeasurable (preBatchStateFactor run k)
      (ℙ.map (pastSampleTuple run k))) :
    ProbabilityTheory.IndepFun (preBatchState run k)
      (fun ω (ki : currentSampleIndices k width) ↦
        run.sample ki.1.1 ki.1.2 ω) ℙ := by
  -- The pointwise factor specification supplies the a.e. composition required
  -- by the generic independence transport lemma.
  apply indepFun_of_factorsThroughPastSamples run k width
    (preBatchState run k) (preBatchStateFactor run k) hfactor
  have htuple :
      (fun ω (ki : pastSampleIndices k (max (B : ℕ) b)) ↦
        run.sample ki.1.1 ki.1.2 ω) = pastSampleTuple run k := rfl
  rw [htuple]
  exact Filter.Eventually.of_forall fun ω ↦
    congrFun (preBatchStateFactor_comp_pastSampleTuple run k) ω

/-- Helper for Lemma 3.3: an integrable nonnegative function of two independent
random variables can be bounded by integrating a pointwise conditional bound. -/
private lemma independentPair_integrable_integral_le
    {A : Type w} {D : Type x} [MeasurableSpace A] [MeasurableSpace D]
    (X : Ω → A) (Y : Ω → D) (φ : A × D → ℝ) (C : A → ℝ)
    (h_independent : ProbabilityTheory.IndepFun X Y ℙ)
    (hX : AEMeasurable X ℙ) (hY : AEMeasurable Y ℙ)
    (hφ : AEMeasurable φ ((ℙ.map X).prod (ℙ.map Y)))
    (hφ_nonnegative : ∀ z, 0 ≤ φ z)
    (hsection : ∀ᵐ a ∂ℙ.map X, Integrable (fun d ↦ φ (a, d)) (ℙ.map Y))
    (hC : Integrable C (ℙ.map X))
    (hbound : ∀ᵐ a ∂ℙ.map X, (∫ d, φ (a, d) ∂ℙ.map Y) ≤ C a) :
    Integrable (fun ω ↦ φ (X ω, Y ω)) ℙ ∧
      (∫ ω, φ (X ω, Y ω) ∂ℙ) ≤ ∫ a, C a ∂ℙ.map X := by
  have hφStrong := hφ.aestronglyMeasurable
  have hinnerMeasurable : AEStronglyMeasurable
      (fun a ↦ ∫ d, ‖φ (a, d)‖ ∂ℙ.map Y) (ℙ.map X) :=
    hφStrong.norm.integral_prod_right'
  have hinnerIntegrable : Integrable
      (fun a ↦ ∫ d, ‖φ (a, d)‖ ∂ℙ.map Y) (ℙ.map X) := by
    apply Integrable.mono' hC hinnerMeasurable
    exact hbound.mono fun a ha ↦ by
      have hinnerNonnegative : 0 ≤ ∫ d, ‖φ (a, d)‖ ∂ℙ.map Y :=
        integral_nonneg fun d ↦ norm_nonneg _
      have hnormIntegral :
          (∫ d, ‖φ (a, d)‖ ∂ℙ.map Y) = ∫ d, φ (a, d) ∂ℙ.map Y := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall fun d ↦ by
          simp only [Real.norm_eq_abs, abs_of_nonneg (hφ_nonnegative (a, d))]
      rw [Real.norm_eq_abs, abs_of_nonneg hinnerNonnegative, hnormIntegral]
      exact ha
  have hprod : Integrable φ ((ℙ.map X).prod (ℙ.map Y)) := by
    exact (integrable_prod_iff hφStrong).2
      ⟨hsection, hinnerIntegrable⟩
  have hpairMeasurable : AEMeasurable (fun ω ↦ (X ω, Y ω)) ℙ := hX.prodMk hY
  have hmap :
      ℙ.map (fun ω ↦ (X ω, Y ω)) = (ℙ.map X).prod (ℙ.map Y) :=
    h_independent.map_prod_eq_prod_map_map hX hY
  have hφMap : AEStronglyMeasurable φ (ℙ.map fun ω ↦ (X ω, Y ω)) := by
    rw [hmap]
    exact hφStrong
  have hprodMap : Integrable φ (ℙ.map fun ω ↦ (X ω, Y ω)) := by
    rw [hmap]
    exact hprod
  have hcomp : Integrable (fun ω ↦ φ (X ω, Y ω)) ℙ :=
    (integrable_map_measure hφMap hpairMeasurable).1 hprodMap
  refine ⟨hcomp, ?_⟩
  calc
    (∫ ω, φ (X ω, Y ω) ∂ℙ) =
        ∫ z, φ z ∂ℙ.map (fun ω ↦ (X ω, Y ω)) := by
      exact (integral_map hpairMeasurable hφMap).symm
    _ = ∫ z, φ z ∂(ℙ.map X).prod (ℙ.map Y) := by rw [hmap]
    _ = ∫ a, ∫ d, φ (a, d) ∂ℙ.map Y ∂ℙ.map X := integral_prod φ hprod
    _ ≤ ∫ a, C a ∂ℙ.map X :=
      integral_mono_ae hprod.integral_prod_left hC
        hbound

omit [IsProbabilityMeasure ν] [IsProbabilityMeasure ℙ] in
/-- Helper for Lemma 3.3: the mean square of an average of independent,
identically distributed centered Euclidean vectors is at most the common
second-moment bound divided by the batch size. -/
private lemma independentBatchMeanSquare_le
    (value : Ξ → EuclideanSpace ℝ (Fin n))
    (sample : ℕ → Ω → Ξ) (batch : ℕ+)
    (hlaw : ∀ i, ProbabilityTheory.HasLaw (sample i) ν ℙ)
    (hindependent : ProbabilityTheory.iIndepFun sample ℙ)
    (hvalue : Integrable value ν) (hmean : ∫ ξ, value ξ ∂ν = 0)
    (hsquare : Integrable (fun ξ ↦ ‖value ξ‖ ^ 2) ν)
    (secondMoment : ℝ)
    (hsecond : (∫ ξ, ‖value ξ‖ ^ 2 ∂ν) ≤ secondMoment) :
    Integrable (fun ω ↦
      ‖(batch : ℝ)⁻¹ • ∑ i ∈ Finset.range batch, value (sample i ω)‖ ^ 2) ℙ ∧
      (∫ ω, ‖(batch : ℝ)⁻¹ •
        ∑ i ∈ Finset.range batch, value (sample i ω)‖ ^ 2 ∂ℙ) ≤
          secondMoment / (batch : ℝ) := by
  classical
  have hvalueRandom (i : ℕ) : Integrable (fun ω ↦ value (sample i ω)) ℙ := by
    have hmap : Integrable value (ℙ.map (sample i)) := by
      rwa [(hlaw i).map_eq]
    exact hmap.comp_aemeasurable (hlaw i).aemeasurable
  have hsquareRandom (i : ℕ) :
      Integrable (fun ω ↦ ‖value (sample i ω)‖ ^ 2) ℙ := by
    have hmap : Integrable (fun ξ ↦ ‖value ξ‖ ^ 2) (ℙ.map (sample i)) := by
      rwa [(hlaw i).map_eq]
    exact hmap.comp_aemeasurable (hlaw i).aemeasurable
  have hmeanRandom (i : ℕ) : (∫ ω, value (sample i ω) ∂ℙ) = 0 := by
    -- Transport the centering identity along the common sample law.
    simpa only [Function.comp_apply, hmean] using
      (hlaw i).integral_comp hvalue.aestronglyMeasurable
  have hsecondRandom (i : ℕ) :
      (∫ ω, ‖value (sample i ω)‖ ^ 2 ∂ℙ) ≤ secondMoment := by
    calc
      (∫ ω, ‖value (sample i ω)‖ ^ 2 ∂ℙ) =
          ∫ ξ, ‖value ξ‖ ^ 2 ∂ν := by
        simpa only [Function.comp_apply] using
          (hlaw i).integral_comp hsquare.aestronglyMeasurable
      _ ≤ secondMoment := hsecond
  have hindependentValue :
      ProbabilityTheory.iIndepFun (fun i ω ↦ value (sample i ω)) ℙ := by
    apply hindependent.comp₀ (fun _ ↦ value)
    · exact fun i ↦ (hlaw i).aemeasurable
    · intro i
      rw [(hlaw i).map_eq]
      exact hvalue.aemeasurable
  have hcrossIntegrable (i j : ℕ) :
      Integrable (fun ω ↦ inner ℝ (value (sample i ω)) (value (sample j ω))) ℙ := by
    by_cases hij : i = j
    · subst j
      simpa only [real_inner_self_eq_norm_sq] using hsquareRandom i
    · have hbilinear := (hindependentValue.indepFun hij).integrable_bilin
        (hvalueRandom i) (hvalueRandom j)
        (innerSL ℝ)
      exact hbilinear.congr (Filter.Eventually.of_forall fun ω ↦
        innerSL_apply_apply ℝ (value (sample i ω)) (value (sample j ω)))
  have hcrossIntegral (i j : ℕ) (hij : i ≠ j) :
      (∫ ω, inner ℝ (value (sample i ω)) (value (sample j ω)) ∂ℙ) = 0 := by
    have hbilinear := (hindependentValue.indepFun hij).integral_bilin
      (hvalueRandom i) (hvalueRandom j)
      (innerSL ℝ)
    calc
      (∫ ω, inner ℝ (value (sample i ω)) (value (sample j ω)) ∂ℙ) =
          ∫ ω, innerSL ℝ (value (sample i ω)) (value (sample j ω)) ∂ℙ := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall fun ω ↦
          (innerSL_apply_apply ℝ
            (value (sample i ω)) (value (sample j ω))).symm
      _ = innerSL ℝ (∫ ω, value (sample i ω) ∂ℙ)
            (∫ ω, value (sample j ω) ∂ℙ) := hbilinear
      _ =
          inner ℝ (∫ ω, value (sample i ω) ∂ℙ)
            (∫ ω, value (sample j ω) ∂ℙ) := by
        exact innerSL_apply_apply ℝ _ _
      _ = 0 := by rw [hmeanRandom i, hmeanRandom j, inner_zero_left]
  have havgIdentity (ω : Ω) :
      ‖(batch : ℝ)⁻¹ • ∑ i ∈ Finset.range batch, value (sample i ω)‖ ^ 2 =
        (batch : ℝ)⁻¹ ^ 2 *
          ∑ i ∈ Finset.range batch, ∑ j ∈ Finset.range batch,
            inner ℝ (value (sample j ω)) (value (sample i ω)) := by
    -- Bilinearity expands the squared norm into diagonal and cross terms.
    rw [← real_inner_self_eq_norm_sq]
    simp only [inner_smul_left, inner_smul_right, inner_sum, sum_inner,
      starRingEnd_apply, star_trivial]
    calc
      (batch : ℝ)⁻¹ * ∑ i ∈ Finset.range batch,
          (batch : ℝ)⁻¹ * ∑ j ∈ Finset.range batch,
            inner ℝ (value (sample j ω)) (value (sample i ω)) =
          ∑ i ∈ Finset.range batch,
            (batch : ℝ)⁻¹ * ((batch : ℝ)⁻¹ *
              ∑ j ∈ Finset.range batch,
                inner ℝ (value (sample j ω)) (value (sample i ω))) := by
        rw [Finset.mul_sum]
      _ = ∑ i ∈ Finset.range batch, (batch : ℝ)⁻¹ ^ 2 *
            ∑ j ∈ Finset.range batch,
              inner ℝ (value (sample j ω)) (value (sample i ω)) := by
        apply Finset.sum_congr rfl
        intro i hi
        ring
      _ = (batch : ℝ)⁻¹ ^ 2 *
          ∑ i ∈ Finset.range batch, ∑ j ∈ Finset.range batch,
            inner ℝ (value (sample j ω)) (value (sample i ω)) := by
        symm
        rw [Finset.mul_sum]
  have hdoubleIntegrable : Integrable (fun ω ↦
      ∑ i ∈ Finset.range batch, ∑ j ∈ Finset.range batch,
        inner ℝ (value (sample j ω)) (value (sample i ω))) ℙ := by
    exact integrable_finsetSum _ fun i _ ↦
      integrable_finsetSum _ fun j _ ↦ hcrossIntegrable j i
  have havgIntegrable : Integrable (fun ω ↦
      ‖(batch : ℝ)⁻¹ • ∑ i ∈ Finset.range batch, value (sample i ω)‖ ^ 2) ℙ := by
    exact ((hdoubleIntegrable.const_mul ((batch : ℝ)⁻¹ ^ 2)).congr
      (Filter.Eventually.of_forall fun ω ↦ (havgIdentity ω).symm))
  refine ⟨havgIntegrable, ?_⟩
  -- Cross terms vanish by independence and centering; only one second moment
  -- remains for each of the `batch` diagonal terms.
  calc
    (∫ ω, ‖(batch : ℝ)⁻¹ •
        ∑ i ∈ Finset.range batch, value (sample i ω)‖ ^ 2 ∂ℙ) =
        (batch : ℝ)⁻¹ ^ 2 *
          ∑ i ∈ Finset.range batch, ∑ j ∈ Finset.range batch,
            ∫ ω, inner ℝ (value (sample j ω)) (value (sample i ω)) ∂ℙ := by
      rw [integral_congr_ae (Filter.Eventually.of_forall havgIdentity),
        integral_const_mul, integral_finsetSum _ (fun i _ ↦
          integrable_finsetSum _ fun j _ ↦ hcrossIntegrable j i)]
      apply congrArg ((batch : ℝ)⁻¹ ^ 2 * ·)
      apply Finset.sum_congr rfl
      intro i hi
      rw [integral_finsetSum _ (fun j _ ↦ hcrossIntegrable j i)]
    _ = (batch : ℝ)⁻¹ ^ 2 *
          ∑ i ∈ Finset.range batch,
            ∫ ω, ‖value (sample i ω)‖ ^ 2 ∂ℙ := by
      apply congrArg ((batch : ℝ)⁻¹ ^ 2 * ·)
      apply Finset.sum_congr rfl
      intro i hi
      rw [Finset.sum_eq_single i]
      · apply integral_congr_ae
        exact Filter.Eventually.of_forall fun ω ↦
          real_inner_self_eq_norm_sq (value (sample i ω))
      · intro j hj hji
        exact hcrossIntegral j i hji
      · exact fun hiMissing ↦ (hiMissing hi).elim
    _ ≤ (batch : ℝ)⁻¹ ^ 2 *
          ∑ _i ∈ Finset.range batch, secondMoment := by
      exact mul_le_mul_of_nonneg_left
        (Finset.sum_le_sum fun i _ ↦ hsecondRandom i) (sq_nonneg _)
    _ = secondMoment / (batch : ℝ) := by
      rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      have hbatch : (batch : ℝ) ≠ 0 := by positivity
      field_simp

omit [IsProbabilityMeasure ν] in
/-- Helper for Lemma 3.3: adding a deterministic vector to a centered batch
average adds exactly its squared norm to the batch mean square. -/
private lemma independentBatchShiftedMeanSquare_le
    (value : Ξ → EuclideanSpace ℝ (Fin n))
    (sample : ℕ → Ω → Ξ) (batch : ℕ+)
    (hlaw : ∀ i, ProbabilityTheory.HasLaw (sample i) ν ℙ)
    (hindependent : ProbabilityTheory.iIndepFun sample ℙ)
    (hvalue : Integrable value ν) (hmean : ∫ ξ, value ξ ∂ν = 0)
    (hsquare : Integrable (fun ξ ↦ ‖value ξ‖ ^ 2) ν)
    (secondMoment : ℝ)
    (hsecond : (∫ ξ, ‖value ξ‖ ^ 2 ∂ν) ≤ secondMoment)
    (a : EuclideanSpace ℝ (Fin n)) :
    Integrable (fun ω ↦
      ‖a + (batch : ℝ)⁻¹ • ∑ i ∈ Finset.range batch, value (sample i ω)‖ ^ 2) ℙ ∧
      (∫ ω, ‖a + (batch : ℝ)⁻¹ •
        ∑ i ∈ Finset.range batch, value (sample i ω)‖ ^ 2 ∂ℙ) ≤
          ‖a‖ ^ 2 + secondMoment / (batch : ℝ) := by
  classical
  let average : Ω → EuclideanSpace ℝ (Fin n) := fun ω ↦
    (batch : ℝ)⁻¹ • ∑ i ∈ Finset.range batch, value (sample i ω)
  have hvalueRandom (i : ℕ) : Integrable (fun ω ↦ value (sample i ω)) ℙ := by
    have hmap : Integrable value (ℙ.map (sample i)) := by
      rwa [(hlaw i).map_eq]
    exact hmap.comp_aemeasurable (hlaw i).aemeasurable
  have hmeanRandom (i : ℕ) : (∫ ω, value (sample i ω) ∂ℙ) = 0 := by
    simpa only [Function.comp_apply, hmean] using
      (hlaw i).integral_comp hvalue.aestronglyMeasurable
  have hsum : Integrable
      (fun ω ↦ ∑ i ∈ Finset.range batch, value (sample i ω)) ℙ :=
    integrable_finsetSum _ fun i _ ↦ hvalueRandom i
  have haverage : Integrable average ℙ := by
    unfold average
    change Integrable
      ((batch : ℝ)⁻¹ •
        (fun ω ↦ ∑ i ∈ Finset.range batch, value (sample i ω))) ℙ
    exact hsum.smul ((batch : ℝ)⁻¹)
  have haverageMean : (∫ ω, average ω ∂ℙ) = 0 := by
    simp only [average]
    rw [integral_smul, integral_finsetSum _ (fun i _ ↦ hvalueRandom i)]
    simp only [hmeanRandom, Finset.sum_const_zero, smul_zero]
  have hbatch := independentBatchMeanSquare_le value sample batch hlaw hindependent
    hvalue hmean hsquare secondMoment hsecond
  have haverageSquare : Integrable (fun ω ↦ ‖average ω‖ ^ 2) ℙ := by
    simpa only [average] using hbatch.1
  have hinner : Integrable (fun ω ↦ inner ℝ a (average ω)) ℙ :=
    haverage.const_inner a
  have hexpanded : Integrable (fun ω ↦
      ‖a‖ ^ 2 + 2 * inner ℝ a (average ω) + ‖average ω‖ ^ 2) ℙ :=
    ((integrable_const _).add (hinner.const_mul 2)).add haverageSquare
  have hshifted : Integrable (fun ω ↦ ‖a + average ω‖ ^ 2) ℙ := by
    exact hexpanded.congr (Filter.Eventually.of_forall fun ω ↦
      (norm_add_sq_real a (average ω)).symm)
  refine ⟨by simpa only [average] using hshifted, ?_⟩
  calc
    (∫ ω, ‖a + (batch : ℝ)⁻¹ •
        ∑ i ∈ Finset.range batch, value (sample i ω)‖ ^ 2 ∂ℙ) =
        ∫ ω, (‖a‖ ^ 2 + 2 * inner ℝ a (average ω)) +
          ‖average ω‖ ^ 2 ∂ℙ := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun ω ↦ by
        simp only [average, norm_add_sq_real]
    _ = ‖a‖ ^ 2 + 2 * inner ℝ a (∫ ω, average ω ∂ℙ) +
          ∫ ω, ‖average ω‖ ^ 2 ∂ℙ := by
      calc
        (∫ ω, (‖a‖ ^ 2 + 2 * inner ℝ a (average ω)) +
            ‖average ω‖ ^ 2 ∂ℙ) =
            (∫ ω, ‖a‖ ^ 2 + 2 * inner ℝ a (average ω) ∂ℙ) +
              ∫ ω, ‖average ω‖ ^ 2 ∂ℙ :=
          integral_add ((integrable_const _).add (hinner.const_mul 2)) haverageSquare
        _ = ((∫ _ω, ‖a‖ ^ 2 ∂ℙ) +
              ∫ ω, 2 * inner ℝ a (average ω) ∂ℙ) +
              ∫ ω, ‖average ω‖ ^ 2 ∂ℙ := by
          rw [integral_add (integrable_const _) (hinner.const_mul 2)]
        _ = ‖a‖ ^ 2 + 2 * inner ℝ a (∫ ω, average ω ∂ℙ) +
              ∫ ω, ‖average ω‖ ^ 2 ∂ℙ := by
          rw [integral_const, integral_const_mul, integral_inner haverage a]
          simp only [Measure.real, measure_univ, ENNReal.toReal_one, one_smul]
    _ = ‖a‖ ^ 2 + ∫ ω, ‖average ω‖ ^ 2 ∂ℙ := by rw [haverageMean]; simp
    _ ≤ ‖a‖ ^ 2 + secondMoment / (batch : ℝ) := by
      exact add_le_add le_rfl (by simpa only [average] using hbatch.2)

/-- Helper for Lemma 3.3: centering an integrable square-integrable Euclidean
random vector cannot increase its second moment. -/
private lemma centeredMeanSquare_le
    (value : Ξ → EuclideanSpace ℝ (Fin n))
    (mean : EuclideanSpace ℝ (Fin n))
    (hvalue : Integrable value ν) (hmean : ∫ ξ, value ξ ∂ν = mean)
    (hsquare : Integrable (fun ξ ↦ ‖value ξ‖ ^ 2) ν)
    (secondMoment : ℝ)
    (hsecond : (∫ ξ, ‖value ξ‖ ^ 2 ∂ν) ≤ secondMoment) :
    Integrable (fun ξ ↦ ‖value ξ - mean‖ ^ 2) ν ∧
      (∫ ξ, ‖value ξ - mean‖ ^ 2 ∂ν) ≤ secondMoment := by
  have hinner : Integrable (fun ξ ↦ inner ℝ (value ξ) mean) ν :=
    hvalue.inner_const mean
  have hexpanded : Integrable (fun ξ ↦
      ‖value ξ‖ ^ 2 - 2 * inner ℝ (value ξ) mean + ‖mean‖ ^ 2) ν :=
    (hsquare.sub (hinner.const_mul 2)).add (integrable_const _)
  have hcentered : Integrable (fun ξ ↦ ‖value ξ - mean‖ ^ 2) ν := by
    exact hexpanded.congr (Filter.Eventually.of_forall fun ξ ↦
      (norm_sub_sq_real (value ξ) mean).symm)
  refine ⟨hcentered, ?_⟩
  have hinnerIntegral :
      (∫ ξ, inner ℝ (value ξ) mean ∂ν) = ‖mean‖ ^ 2 := by
    calc
      (∫ ξ, inner ℝ (value ξ) mean ∂ν) =
          ∫ ξ, inner ℝ mean (value ξ) ∂ν := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall fun ξ ↦ real_inner_comm _ _
      _ = inner ℝ mean (∫ ξ, value ξ ∂ν) := integral_inner hvalue mean
      _ = ‖mean‖ ^ 2 := by rw [hmean, real_inner_self_eq_norm_sq]
  calc
    (∫ ξ, ‖value ξ - mean‖ ^ 2 ∂ν) =
        (∫ ξ, ‖value ξ‖ ^ 2 ∂ν) - ‖mean‖ ^ 2 := by
      rw [integral_congr_ae (Filter.Eventually.of_forall fun ξ ↦
          norm_sub_sq_real (value ξ) mean)]
      calc
        (∫ ξ, (‖value ξ‖ ^ 2 - 2 * inner ℝ (value ξ) mean) +
            ‖mean‖ ^ 2 ∂ν) =
            (∫ ξ, ‖value ξ‖ ^ 2 - 2 * inner ℝ (value ξ) mean ∂ν) +
              ∫ _ξ, ‖mean‖ ^ 2 ∂ν :=
          integral_add (hsquare.sub (hinner.const_mul 2)) (integrable_const _)
        _ = ((∫ ξ, ‖value ξ‖ ^ 2 ∂ν) -
              ∫ ξ, 2 * inner ℝ (value ξ) mean ∂ν) +
              ∫ _ξ, ‖mean‖ ^ 2 ∂ν := by
          rw [integral_sub hsquare (hinner.const_mul 2)]
        _ = (∫ ξ, ‖value ξ‖ ^ 2 ∂ν) - ‖mean‖ ^ 2 := by
          rw [integral_const_mul, hinnerIntegral, integral_const]
          simp only [Measure.real, measure_univ, ENNReal.toReal_one, one_smul]
          ring
    _ ≤ ∫ ξ, ‖value ξ‖ ^ 2 ∂ν := sub_le_self _ (sq_nonneg _)
    _ ≤ secondMoment := hsecond

/-- Helper for Lemma 3.3: subtracting a constant inside a positive-size batch
average is the same as subtracting it from the average. -/
private lemma batchAverage_sub
    (batch : ℕ+) (value : ℕ → EuclideanSpace ℝ (Fin n))
    (a : EuclideanSpace ℝ (Fin n)) :
    (batch : ℝ)⁻¹ • ∑ i ∈ Finset.range batch, (value i - a) =
      (batch : ℝ)⁻¹ • ∑ i ∈ Finset.range batch, value i - a := by
  rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range, smul_sub]
  have hbatch : (batch : ℝ) ≠ 0 := by positivity
  rw [← Nat.cast_smul_eq_nsmul ℝ, ← mul_smul, inv_mul_cancel₀ hbatch, one_smul]

omit [IsProbabilityMeasure ℙ] in
/-- Helper for Lemma 3.3: at a fixed point in the regularity region, an
independent refresh batch has integrable squared centered error bounded by the
oracle noise variance divided by the batch size. -/
private lemma fixedPointRefreshBatchMeanSquare_le
    (x : EuclideanSpace ℝ (Fin n)) (hx : x ∈ h.region)
    (sample : ℕ → Ω → Ξ) (batch : ℕ+)
    (hlaw : ∀ i, ProbabilityTheory.HasLaw (sample i) ν ℙ)
    (hindependent : ProbabilityTheory.iIndepFun sample ℙ) :
    Integrable (fun ω ↦
      ‖(batch : ℝ)⁻¹ • ∑ i ∈ Finset.range batch,
        (oracle.sampleGradient x (sample i ω) - gradient f x)‖ ^ 2) ℙ ∧
      (∫ ω, ‖(batch : ℝ)⁻¹ • ∑ i ∈ Finset.range batch,
        (oracle.sampleGradient x (sample i ω) - gradient f x)‖ ^ 2 ∂ℙ) ≤
          (oracle.noiseLevel : ℝ) ^ 2 / (batch : ℝ) := by
  have hunbiased := oracle.unbiased_spec x hx
  have hvariance := oracle.variance_spec x hx
  have hcentered : Integrable
      (fun ξ ↦ oracle.sampleGradient x ξ - gradient f x) ν :=
    hunbiased.1.sub (integrable_const _)
  have hcenteredMean :
      (∫ ξ, oracle.sampleGradient x ξ - gradient f x ∂ν) = 0 := by
    -- Unbiasedness centers each sample-gradient error.
    rw [integral_sub hunbiased.1 (integrable_const _), hunbiased.2, integral_const]
    simp
  -- The abstract batch calculation supplies both integrability and the sharp
  -- inverse-batch second-moment bound.
  exact independentBatchMeanSquare_le
    (fun ξ ↦ oracle.sampleGradient x ξ - gradient f x) sample batch
      hlaw hindependent hcentered hcenteredMean hvariance.1
        ((oracle.noiseLevel : ℝ) ^ 2) hvariance.2

/-- Helper for Lemma 3.3: at two fixed points in the regularity region, a
fresh update batch adds a centered innovation whose mean square is controlled
by the oracle mean-square Lipschitz constant. -/
private lemma fixedPointUpdateBatchMeanSquare_le
    (x : EuclideanSpace ℝ (Fin n)) (hx : x ∈ h.region)
    (y : EuclideanSpace ℝ (Fin n)) (hy : y ∈ h.region)
    (a : EuclideanSpace ℝ (Fin n))
    (sample : ℕ → Ω → Ξ) (batch : ℕ+)
    (hlaw : ∀ i, ProbabilityTheory.HasLaw (sample i) ν ℙ)
    (hindependent : ProbabilityTheory.iIndepFun sample ℙ) :
    Integrable (fun ω ↦
      ‖a + (batch : ℝ)⁻¹ • ∑ i ∈ Finset.range batch,
        ((oracle.sampleGradient x (sample i ω) -
            oracle.sampleGradient y (sample i ω)) -
          (gradient f x - gradient f y))‖ ^ 2) ℙ ∧
      (∫ ω, ‖a + (batch : ℝ)⁻¹ • ∑ i ∈ Finset.range batch,
        ((oracle.sampleGradient x (sample i ω) -
            oracle.sampleGradient y (sample i ω)) -
          (gradient f x - gradient f y))‖ ^ 2 ∂ℙ) ≤
        ‖a‖ ^ 2 + (oracle.meanSquareLipschitz : ℝ) ^ 2 / (batch : ℝ) *
          ‖x - y‖ ^ 2 := by
  let difference : Ξ → EuclideanSpace ℝ (Fin n) := fun ξ ↦
    oracle.sampleGradient x ξ - oracle.sampleGradient y ξ
  let meanDifference : EuclideanSpace ℝ (Fin n) := gradient f x - gradient f y
  let centered : Ξ → EuclideanSpace ℝ (Fin n) := fun ξ ↦
    difference ξ - meanDifference
  have hxUnbiased := oracle.unbiased_spec x hx
  have hyUnbiased := oracle.unbiased_spec y hy
  have hdifference : Integrable difference ν := by
    exact hxUnbiased.1.sub hyUnbiased.1
  have hdifferenceMean : (∫ ξ, difference ξ ∂ν) = meanDifference := by
    simp only [difference, meanDifference]
    rw [integral_sub hxUnbiased.1 hyUnbiased.1, hxUnbiased.2, hyUnbiased.2]
  have hlipschitz := oracle.meanSquareLipschitz_spec x hx y hy
  have hcenteredSquare := centeredMeanSquare_le difference meanDifference
    hdifference hdifferenceMean hlipschitz.1
      ((oracle.meanSquareLipschitz : ℝ) ^ 2 * ‖x - y‖ ^ 2) hlipschitz.2
  have hcentered : Integrable centered ν := by
    exact hdifference.sub (integrable_const _)
  have hcenteredMean : (∫ ξ, centered ξ ∂ν) = 0 := by
    simp only [centered]
    rw [integral_sub hdifference (integrable_const _), hdifferenceMean, integral_const]
    simp only [Measure.real, measure_univ, ENNReal.toReal_one, one_smul, sub_self]
  have hshifted := independentBatchShiftedMeanSquare_le centered sample batch hlaw
    hindependent hcentered hcenteredMean hcenteredSquare.1
      ((oracle.meanSquareLipschitz : ℝ) ^ 2 * ‖x - y‖ ^ 2)
      hcenteredSquare.2 a
  refine ⟨by simpa only [centered, difference, meanDifference] using hshifted.1, ?_⟩
  calc
    (∫ ω, ‖a + (batch : ℝ)⁻¹ • ∑ i ∈ Finset.range batch,
        ((oracle.sampleGradient x (sample i ω) -
            oracle.sampleGradient y (sample i ω)) -
          (gradient f x - gradient f y))‖ ^ 2 ∂ℙ) ≤
        ‖a‖ ^ 2 + ((oracle.meanSquareLipschitz : ℝ) ^ 2 * ‖x - y‖ ^ 2) /
          (batch : ℝ) := by
      simpa only [centered, difference, meanDifference] using hshifted.2
    _ = ‖a‖ ^ 2 + (oracle.meanSquareLipschitz : ℝ) ^ 2 / (batch : ℝ) *
          ‖x - y‖ ^ 2 := by ring

/-- Helper for Lemma 3.3: the mean square of the unprojected SPIDER estimation error. -/
private noncomputable def rawGradientErrorMeanSquare
    (run : StochasticRun h oracle ℙ x₀ multiplier₀ params Q B b) (k : ℕ) : ℝ :=
  ∫ ω, ‖SPIDER.rawEstimate oracle run.point run.sample Q B b k ω -
    gradient f (run.point k ω)‖ ^ 2 ∂ℙ

/-- Helper for Lemma 3.3: every step mean square is nonnegative. -/
private lemma stepMeanSquare_nonneg
    (run : StochasticRun h oracle ℙ x₀ multiplier₀ params Q B b) (k : ℕ) :
    0 ≤ run.stepMeanSquare k := by
  -- Unfold the expectation and use pointwise nonnegativity of squared norms.
  rw [run.stepMeanSquare_def]
  exact integral_nonneg fun ω ↦ sq_nonneg ‖run.step k ω‖

/-- Helper for Lemma 3.3: summing prefixes since the latest refresh counts each
nonnegative summand at most `q` times. -/
private lemma sum_lastRefresh_le (a : ℕ → ℝ) (ha : ∀ j, 0 ≤ a j)
    (q K : ℕ) (hq : 0 < q) :
    ∑ k ∈ Finset.range K, ∑ j ∈ Finset.Ico (k - k % q) k, a j ≤
      q * ∑ j ∈ Finset.range K, a j := by
  classical
  -- Rewrite every block prefix as a filtered sum over the common horizon.
  have interval_eq_filter (k : ℕ) (hk : k ∈ Finset.range K) :
      Finset.Ico (k - k % q) k =
        (Finset.range K).filter (fun j ↦ j ∈ Finset.Ico (k - k % q) k) := by
    have hk' : k < K := Finset.mem_range.mp hk
    ext j
    simp only [Finset.mem_Ico, Finset.mem_filter, Finset.mem_range]
    omega
  calc
    ∑ k ∈ Finset.range K, ∑ j ∈ Finset.Ico (k - k % q) k, a j =
        ∑ k ∈ Finset.range K, ∑ j ∈ Finset.range K,
          if j ∈ Finset.Ico (k - k % q) k then a j else 0 := by
      apply Finset.sum_congr rfl
      intro k hk
      calc
        ∑ j ∈ Finset.Ico (k - k % q) k, a j =
            ∑ j ∈ (Finset.range K).filter
              (fun j ↦ j ∈ Finset.Ico (k - k % q) k), a j :=
          congrArg (fun s : Finset ℕ ↦ ∑ j ∈ s, a j) (interval_eq_filter k hk)
        _ = ∑ j ∈ Finset.range K,
              if j ∈ Finset.Ico (k - k % q) k then a j else 0 := by
          exact Finset.sum_filter (fun j ↦ j ∈ Finset.Ico (k - k % q) k) a
    _ = ∑ j ∈ Finset.range K, ∑ k ∈ Finset.range K,
          if j ∈ Finset.Ico (k - k % q) k then a j else 0 := by
      rw [Finset.sum_comm]
    _ ≤ ∑ j ∈ Finset.range K, q * a j := by
      apply Finset.sum_le_sum
      intro j hj
      -- Membership forces `j < k < j + q + 1`, so at most `q` indices contribute.
      have hsubset :
          (Finset.range K).filter (fun k ↦ j ∈ Finset.Ico (k - k % q) k) ⊆
            Finset.Ioc j (j + q) := by
        intro k hk
        simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico,
          Finset.mem_Ioc] at hk ⊢
        have hmod : k % q < q := Nat.mod_lt k hq
        omega
      have hcard :
          ((Finset.range K).filter
            (fun k ↦ j ∈ Finset.Ico (k - k % q) k)).card ≤ q := by
        calc
          ((Finset.range K).filter
              (fun k ↦ j ∈ Finset.Ico (k - k % q) k)).card ≤
              (Finset.Ioc j (j + q)).card := Finset.card_le_card hsubset
          _ = q := by simp
      rw [← Finset.sum_filter]
      simp only [Finset.sum_const, nsmul_eq_mul]
      exact mul_le_mul_of_nonneg_right (Nat.cast_le.2 hcard) (ha j)
    _ = q * ∑ j ∈ Finset.range K, a j := by
      rw [Finset.mul_sum]

/-- Helper for Lemma 3.3: radial clipping cannot increase the mean-square
gradient error when the raw squared error is integrable. -/
private lemma gradientErrorMeanSquare_le_rawGradientErrorMeanSquare
    (run : StochasticRun h oracle ℙ x₀ multiplier₀ params Q B b)
    (K k : ℕ) (h_region : run.PointsInRegion K) (hk : k < K)
    (hraw : Integrable (fun ω ↦
      ‖SPIDER.rawEstimate oracle run.point run.sample Q B b k ω -
        gradient f (run.point k ω)‖ ^ 2) ℙ) :
    run.gradientErrorMeanSquare k ≤ run.rawGradientErrorMeanSquare k := by
  -- The true gradient lies in the clipping ball at every point in the prefix.
  have hpointwise (ω : Ω) :
      ‖run.gradientError k ω‖ ^ 2 ≤
        ‖SPIDER.rawEstimate oracle run.point run.sample Q B b k ω -
          gradient f (run.point k ω)‖ ^ 2 := by
    rw [run.gradientError_apply, run.gradientEstimate_apply, SPIDER.estimate_apply]
    exact pow_le_pow_left₀ (norm_nonneg _)
      (SPIDER.norm_clip_sub_le h.gradientBound _ _
        (h.norm_gradient_le _ ((run.pointsInRegion_iff K).mp h_region k hk ω))) 2
  -- Monotonicity of the integral now transfers the pointwise projection estimate.
  rw [run.gradientErrorMeanSquare_def, rawGradientErrorMeanSquare]
  exact integral_mono_of_nonneg (ae_of_all ℙ (fun ω ↦ sq_nonneg _)) hraw
    (ae_of_all ℙ hpointwise)

/-- Helper for Lemma 3.3: one SPIDER iteration is either a fresh variance
reset or adds one centered mean-square-Lipschitz innovation to the preceding
raw gradient error. -/
private lemma rawGradientErrorMeanSquare_refreshOrUpdate
    (run : StochasticRun h oracle ℙ x₀ multiplier₀ params Q B b)
    (K k : ℕ) (h_region : run.PointsInRegion K)
    (h_freshBatches : run.HasFreshBatches K)
    (h_step_integrable : ∀ j < K,
      Integrable (fun ω ↦ ‖run.step j ω‖ ^ 2) ℙ)
    (hprevious_integrable : k % Q ≠ 0 →
      Integrable (fun ω ↦
        ‖SPIDER.rawEstimate oracle run.point run.sample Q B b (k - 1) ω -
          gradient f (run.point (k - 1) ω)‖ ^ 2) ℙ)
    (hk : k < K) :
    Integrable (fun ω ↦
      ‖SPIDER.rawEstimate oracle run.point run.sample Q B b k ω -
        gradient f (run.point k ω)‖ ^ 2) ℙ ∧
      ((k % Q = 0 →
          run.rawGradientErrorMeanSquare k ≤
            (oracle.noiseLevel : ℝ) ^ 2 / (B : ℝ)) ∧
        (k % Q ≠ 0 →
          run.rawGradientErrorMeanSquare k ≤
            run.rawGradientErrorMeanSquare (k - 1) +
              (oracle.meanSquareLipschitz : ℝ) ^ 2 / (b : ℝ) *
                run.stepMeanSquare (k - 1))) := by
  classical
  let state := preBatchState run k
  let freshBatch : Ω → (ℕ → Ξ) := fun ω i ↦ run.sample k i ω
  have hstate : AEMeasurable state ℙ := by
    simpa only [state] using aemeasurable_preBatchState run k
  have hfreshBatch : AEMeasurable freshBatch ℙ := by
    exact aemeasurable_pi_lambda _
      (fun i ↦ (run.hasLaw_sample k i).aemeasurable)
  have hindependent : ProbabilityTheory.IndepFun state freshBatch ℙ := by
    dsimp only [state, freshBatch]
    unfold preBatchState
    exact h_freshBatches k hk
  have hbatchIndependent : ProbabilityTheory.iIndepFun (run.sample k) ℙ := by
    have hinjective : Function.Injective (fun i : ℕ ↦ (k, i)) := by
      intro i j hij
      exact congrArg Prod.snd hij
    simpa only using run.independent_sample.precomp hinjective
  by_cases hrefresh : k % Q = 0
  · let φ :
        ((EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) ×
            EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin n)) ×
          (ℕ → Ξ)) → ℝ := fun z ↦
        if z.1.1 ∈ h.region then
          ‖(B : ℝ)⁻¹ • ∑ i ∈ Finset.range B,
            (oracle.sampleGradient z.1.1 (z.2 i) -
              h.objectiveGradientExtension z.1.1)‖ ^ 2
        else 0
    let C :
        (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) ×
          EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin n)) → ℝ :=
      fun _ ↦ (oracle.noiseLevel : ℝ) ^ 2 / (B : ℝ)
    have hφ : Measurable φ := by
      unfold φ
      apply Measurable.ite
      · exact h.isOpen_region.measurableSet.preimage
          (measurable_fst.comp measurable_fst)
      · have hsampled (i : ℕ) : Measurable (fun z :
            ((EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) ×
                EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin n)) ×
              (ℕ → Ξ)) ↦
              oracle.sampleGradient z.1.1 (z.2 i)) := by
          exact measurable_sampleGradient.comp
            ((measurable_fst.comp measurable_fst).prodMk
              (measurable_pi_apply i |>.comp measurable_snd))
        have hgradient : Measurable (fun z :
            ((EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) ×
                EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin n)) ×
              (ℕ → Ξ)) ↦ h.objectiveGradientExtension z.1.1) :=
          h.measurable_objectiveGradientExtension.comp
            (measurable_fst.comp measurable_fst)
        have hsum : Measurable (fun z :
            ((EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) ×
                EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin n)) ×
              (ℕ → Ξ)) ↦
              ∑ i ∈ Finset.range B,
                (oracle.sampleGradient z.1.1 (z.2 i) -
                  h.objectiveGradientExtension z.1.1)) := by
          exact Finset.measurable_sum _ fun i _ ↦ (hsampled i).sub hgradient
        exact (hsum.const_smul ((B : ℝ)⁻¹)).norm.pow_const 2
      · fun_prop
    have hsection : ∀ s, Integrable (fun d ↦ φ (s, d)) (ℙ.map freshBatch) := by
      intro s
      have hsectionMeasurable : Measurable (fun d ↦ φ (s, d)) :=
        hφ.comp (measurable_const.prodMk measurable_id)
      by_cases hs : s.1 ∈ h.region
      · have hfixed := fixedPointRefreshBatchMeanSquare_le
          (oracle := oracle) s.1 hs (run.sample k) B
          (run.hasLaw_sample k) hbatchIndependent
        refine (integrable_map_measure hsectionMeasurable.aestronglyMeasurable
          hfreshBatch).2 ?_
        simpa only [Function.comp_def, freshBatch, φ, if_pos hs,
          h.objectiveGradientExtension_eq hs] using hfixed.1
      · have hzero : Integrable (fun _ω : Ω ↦ (0 : ℝ)) ℙ := integrable_const _
        refine (integrable_map_measure hsectionMeasurable.aestronglyMeasurable
          hfreshBatch).2 ?_
        simpa only [Function.comp_def, φ, if_neg hs] using hzero
    have hbound : ∀ s,
        (∫ d, φ (s, d) ∂ℙ.map freshBatch) ≤ C s := by
      intro s
      have hsectionMeasurable : Measurable (fun d ↦ φ (s, d)) :=
        hφ.comp (measurable_const.prodMk measurable_id)
      rw [integral_map hfreshBatch hsectionMeasurable.aestronglyMeasurable]
      by_cases hs : s.1 ∈ h.region
      · have hfixed := fixedPointRefreshBatchMeanSquare_le
          (oracle := oracle) s.1 hs (run.sample k) B
          (run.hasLaw_sample k) hbatchIndependent
        simpa only [Function.comp_apply, φ, C, if_pos hs,
          h.objectiveGradientExtension_eq hs] using hfixed.2
      · simp only [φ, C, if_neg hs, integral_zero]
        positivity
    have hpair := independentPair_integrable_integral_le state freshBatch φ C
      hindependent hstate hfreshBatch hφ.aemeasurable
      (fun z ↦ by unfold φ; split <;> positivity)
      (Filter.Eventually.of_forall hsection) (integrable_const _)
      (Filter.Eventually.of_forall hbound)
    have hidentify ( ω : Ω) :
        φ (state ω, freshBatch ω) =
          ‖SPIDER.rawEstimate oracle run.point run.sample Q B b k ω -
            gradient f (run.point k ω)‖ ^ 2 := by
      have hx : run.point k ω ∈ h.region :=
        (run.pointsInRegion_iff K).mp h_region k hk ω
      simp only [φ, state, freshBatch, preBatchState, hx, if_pos,
        h.objectiveGradientExtension_eq hx]
      rw [SPIDER.rawEstimate_of_refresh oracle run.point run.sample Q B b k ω hrefresh,
        batchAverage_sub]
    have hintegrable : Integrable (fun ω ↦
        ‖SPIDER.rawEstimate oracle run.point run.sample Q B b k ω -
          gradient f (run.point k ω)‖ ^ 2) ℙ :=
      hpair.1.congr (Filter.Eventually.of_forall hidentify)
    have hrefreshBound : run.rawGradientErrorMeanSquare k ≤
        (oracle.noiseLevel : ℝ) ^ 2 / (B : ℝ) := by
      rw [rawGradientErrorMeanSquare,
        ← integral_congr_ae (Filter.Eventually.of_forall hidentify)]
      calc
        (∫ ω, φ (state ω, freshBatch ω) ∂ℙ) ≤
            ∫ s, C s ∂ℙ.map state := hpair.2
        _ = (oracle.noiseLevel : ℝ) ^ 2 / (B : ℝ) := by
          rw [integral_const, Measure.real,
            Measure.map_apply_of_aemeasurable hstate MeasurableSet.univ]
          simp only [Set.preimage_univ, measure_univ,
            ENNReal.toReal_one, one_smul]
    exact ⟨hintegrable, ⟨fun _ ↦ hrefreshBound, fun hupdate ↦ (hupdate hrefresh).elim⟩⟩
  · have hkPositive : 0 < k := by
      exact Nat.pos_of_ne_zero fun hkZero ↦ hrefresh (by simp only [hkZero, Nat.zero_mod])
    have hkPredSucc : k - 1 + 1 = k := by omega
    have hkPredLt : k - 1 < K := by
      omega
    let φ :
        ((EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) ×
            EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin n)) ×
          (ℕ → Ξ)) → ℝ := fun z ↦
      if z.1.1 ∈ h.region ∧ z.1.2.1 ∈ h.region then
        ‖(z.1.2.2.2 - h.objectiveGradientExtension z.1.2.1) +
          (b : ℝ)⁻¹ • ∑ i ∈ Finset.range b,
            ((oracle.sampleGradient z.1.1 (z.2 i) -
                oracle.sampleGradient z.1.2.1 (z.2 i)) -
              (h.objectiveGradientExtension z.1.1 -
                h.objectiveGradientExtension z.1.2.1))‖ ^ 2
      else 0
    let C :
        (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) ×
          EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin n)) → ℝ :=
      fun s ↦ ‖s.2.2.2 - h.objectiveGradientExtension s.2.1‖ ^ 2 +
        (oracle.meanSquareLipschitz : ℝ) ^ 2 / (b : ℝ) *
          ‖s.1 - s.2.1‖ ^ 2
    have hxMeasurable : Measurable (fun z :
        ((EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) ×
            EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin n)) ×
          (ℕ → Ξ)) ↦ z.1.1) := measurable_fst.comp measurable_fst
    have hyMeasurable : Measurable (fun z :
        ((EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) ×
            EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin n)) ×
          (ℕ → Ξ)) ↦ z.1.2.1) :=
      measurable_fst.comp (measurable_snd.comp measurable_fst)
    have hgradientX : Measurable (fun z :
        ((EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) ×
            EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin n)) ×
          (ℕ → Ξ)) ↦ h.objectiveGradientExtension z.1.1) :=
      h.measurable_objectiveGradientExtension.comp hxMeasurable
    have hgradientY : Measurable (fun z :
        ((EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) ×
            EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin n)) ×
          (ℕ → Ξ)) ↦ h.objectiveGradientExtension z.1.2.1) :=
      h.measurable_objectiveGradientExtension.comp hyMeasurable
    have hφ : Measurable φ := by
      unfold φ
      apply Measurable.ite
      · exact (h.isOpen_region.measurableSet.preimage hxMeasurable).inter
          (h.isOpen_region.measurableSet.preimage hyMeasurable)
      · have hsampledX (i : ℕ) : Measurable (fun z :
            ((EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) ×
                EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin n)) ×
              (ℕ → Ξ)) ↦ oracle.sampleGradient z.1.1 (z.2 i)) :=
          measurable_sampleGradient.comp
            (hxMeasurable.prodMk (measurable_pi_apply i |>.comp measurable_snd))
        have hsampledY (i : ℕ) : Measurable (fun z :
            ((EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) ×
                EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin n)) ×
              (ℕ → Ξ)) ↦ oracle.sampleGradient z.1.2.1 (z.2 i)) :=
          measurable_sampleGradient.comp
            (hyMeasurable.prodMk (measurable_pi_apply i |>.comp measurable_snd))
        have hsum : Measurable (fun z :
            ((EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) ×
                EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin n)) ×
              (ℕ → Ξ)) ↦
              ∑ i ∈ Finset.range b,
                ((oracle.sampleGradient z.1.1 (z.2 i) -
                    oracle.sampleGradient z.1.2.1 (z.2 i)) -
                  (h.objectiveGradientExtension z.1.1 -
                    h.objectiveGradientExtension z.1.2.1))) := by
          exact Finset.measurable_sum _ fun i _ ↦
            ((hsampledX i).sub (hsampledY i)).sub (hgradientX.sub hgradientY)
        have hprevious : Measurable (fun z :
            ((EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) ×
                EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin n)) ×
              (ℕ → Ξ)) ↦ z.1.2.2.2) := by fun_prop
        exact ((hprevious.sub hgradientY).add
          (hsum.const_smul ((b : ℝ)⁻¹))).norm.pow_const 2
      · fun_prop
    have hC : Measurable C := by
      unfold C
      have hxState : Measurable (fun s :
          (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) ×
            EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin n)) ↦ s.1) :=
        measurable_fst
      have hyState : Measurable (fun s :
          (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) ×
            EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin n)) ↦ s.2.1) :=
        measurable_fst.comp measurable_snd
      have hgradientState : Measurable (fun s :
          (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) ×
            EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin n)) ↦
          h.objectiveGradientExtension s.2.1) :=
        h.measurable_objectiveGradientExtension.comp hyState
      have hpreviousState : Measurable (fun s :
          (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) ×
            EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin n)) ↦ s.2.2.2) := by
        fun_prop
      exact ((hpreviousState.sub hgradientState).norm.pow_const 2).add
        (((hxState.sub hyState).norm.pow_const 2).const_mul
          ((oracle.meanSquareLipschitz : ℝ) ^ 2 / (b : ℝ)))
    have hsection : ∀ s, Integrable (fun d ↦ φ (s, d)) (ℙ.map freshBatch) := by
      intro s
      have hsectionMeasurable : Measurable (fun d ↦ φ (s, d)) :=
        hφ.comp (measurable_const.prodMk measurable_id)
      by_cases hs : s.1 ∈ h.region ∧ s.2.1 ∈ h.region
      · have hfixed := fixedPointUpdateBatchMeanSquare_le
          (oracle := oracle) s.1 hs.1 s.2.1 hs.2
          (s.2.2.2 - h.objectiveGradientExtension s.2.1) (run.sample k) b
          (run.hasLaw_sample k) hbatchIndependent
        refine (integrable_map_measure hsectionMeasurable.aestronglyMeasurable
          hfreshBatch).2 ?_
        simpa only [Function.comp_def, freshBatch, φ, if_pos hs,
          h.objectiveGradientExtension_eq hs.1,
          h.objectiveGradientExtension_eq hs.2] using hfixed.1
      · have hzero : Integrable (fun _ω : Ω ↦ (0 : ℝ)) ℙ := integrable_const _
        refine (integrable_map_measure hsectionMeasurable.aestronglyMeasurable
          hfreshBatch).2 ?_
        simpa only [Function.comp_def, φ, if_neg hs] using hzero
    have hbound : ∀ s, (∫ d, φ (s, d) ∂ℙ.map freshBatch) ≤ C s := by
      intro s
      have hsectionMeasurable : Measurable (fun d ↦ φ (s, d)) :=
        hφ.comp (measurable_const.prodMk measurable_id)
      rw [integral_map hfreshBatch hsectionMeasurable.aestronglyMeasurable]
      by_cases hs : s.1 ∈ h.region ∧ s.2.1 ∈ h.region
      · have hfixed := fixedPointUpdateBatchMeanSquare_le
          (oracle := oracle) s.1 hs.1 s.2.1 hs.2
          (s.2.2.2 - h.objectiveGradientExtension s.2.1) (run.sample k) b
          (run.hasLaw_sample k) hbatchIndependent
        simpa only [Function.comp_apply, freshBatch, φ, C, if_pos hs,
          h.objectiveGradientExtension_eq hs.1,
          h.objectiveGradientExtension_eq hs.2] using hfixed.2
      · simp only [φ, if_neg hs, integral_zero]
        unfold C
        positivity
    have hprevious := hprevious_integrable hrefresh
    have hstep := h_step_integrable (k - 1) hkPredLt
    have hpointSucc (ω : Ω) :
        run.point k ω = run.point (k - 1) ω + run.step (k - 1) ω := by
      simpa only [hkPredSucc] using run.point_succ (k - 1) ω
    have hCidentify (ω : Ω) : C (state ω) =
        ‖SPIDER.rawEstimate oracle run.point run.sample Q B b (k - 1) ω -
          gradient f (run.point (k - 1) ω)‖ ^ 2 +
        (oracle.meanSquareLipschitz : ℝ) ^ 2 / (b : ℝ) *
          ‖run.step (k - 1) ω‖ ^ 2 := by
      have hy : run.point (k - 1) ω ∈ h.region :=
        (run.pointsInRegion_iff K).mp h_region (k - 1) hkPredLt ω
      simp only [C, state, preBatchState, ne_of_gt hkPositive, if_false,
        hpointSucc, add_sub_cancel_left, h.objectiveGradientExtension_eq hy]
    have hcoefficientStep : Integrable (fun ω ↦
        (oracle.meanSquareLipschitz : ℝ) ^ 2 / (b : ℝ) *
          ‖run.step (k - 1) ω‖ ^ 2) ℙ :=
      hstep.const_mul ((oracle.meanSquareLipschitz : ℝ) ^ 2 / (b : ℝ))
    have hCcomp : Integrable (fun ω ↦ C (state ω)) ℙ := by
      exact (hprevious.add hcoefficientStep).congr
        (Filter.Eventually.of_forall fun ω ↦ (hCidentify ω).symm)
    have hCmap : Integrable C (ℙ.map state) :=
      (integrable_map_measure hC.aestronglyMeasurable hstate).2 hCcomp
    have hpair := independentPair_integrable_integral_le state freshBatch φ C
      hindependent hstate hfreshBatch hφ.aemeasurable
      (fun z ↦ by unfold φ; split <;> positivity)
      (Filter.Eventually.of_forall hsection) hCmap
      (Filter.Eventually.of_forall hbound)
    have hidentify (ω : Ω) :
        φ (state ω, freshBatch ω) =
          ‖SPIDER.rawEstimate oracle run.point run.sample Q B b k ω -
            gradient f (run.point k ω)‖ ^ 2 := by
      have hx : run.point k ω ∈ h.region :=
        (run.pointsInRegion_iff K).mp h_region k hk ω
      have hy : run.point (k - 1) ω ∈ h.region :=
        (run.pointsInRegion_iff K).mp h_region (k - 1) hkPredLt ω
      have hnonrefreshPred : (k - 1 + 1) % Q ≠ 0 := by
        simpa only [hkPredSucc] using hrefresh
      simp only [φ, state, freshBatch, preBatchState, ne_of_gt hkPositive, if_false,
        hx, hy, and_self, if_pos, h.objectiveGradientExtension_eq hx,
        h.objectiveGradientExtension_eq hy]
      rw [← hkPredSucc,
        SPIDER.rawEstimate_of_update oracle run.point run.sample Q B b (k - 1) ω
          hnonrefreshPred,
        batchAverage_sub]
      simp only [hkPredSucc]
      apply congrArg (fun z : EuclideanSpace ℝ (Fin n) ↦ ‖z‖ ^ 2)
      module
    have hintegrable : Integrable (fun ω ↦
        ‖SPIDER.rawEstimate oracle run.point run.sample Q B b k ω -
          gradient f (run.point k ω)‖ ^ 2) ℙ :=
      hpair.1.congr (Filter.Eventually.of_forall hidentify)
    have hupdateBound : run.rawGradientErrorMeanSquare k ≤
        run.rawGradientErrorMeanSquare (k - 1) +
          (oracle.meanSquareLipschitz : ℝ) ^ 2 / (b : ℝ) *
            run.stepMeanSquare (k - 1) := by
      rw [rawGradientErrorMeanSquare,
        ← integral_congr_ae (Filter.Eventually.of_forall hidentify)]
      calc
        (∫ ω, φ (state ω, freshBatch ω) ∂ℙ) ≤
            ∫ s, C s ∂ℙ.map state := hpair.2
        _ = ∫ ω, C (state ω) ∂ℙ :=
          integral_map hstate hC.aestronglyMeasurable
        _ = ∫ ω,
            (‖SPIDER.rawEstimate oracle run.point run.sample Q B b (k - 1) ω -
                gradient f (run.point (k - 1) ω)‖ ^ 2 +
              (oracle.meanSquareLipschitz : ℝ) ^ 2 / (b : ℝ) *
                ‖run.step (k - 1) ω‖ ^ 2) ∂ℙ := by
          exact integral_congr_ae (Filter.Eventually.of_forall hCidentify)
        _ = run.rawGradientErrorMeanSquare (k - 1) +
            (oracle.meanSquareLipschitz : ℝ) ^ 2 / (b : ℝ) *
              run.stepMeanSquare (k - 1) := by
          rw [integral_add hprevious hcoefficientStep, integral_const_mul]
          rfl
    exact ⟨hintegrable, ⟨fun hzero ↦ (hrefresh hzero).elim,
      fun _ ↦ hupdateBound⟩⟩

/-- Helper for Lemma 3.3: the raw SPIDER error accumulates only the update
variance since the most recent refresh. -/
private lemma rawGradientErrorMeanSquare_le_lastRefresh
    (run : StochasticRun h oracle ℙ x₀ multiplier₀ params Q B b)
    (K k : ℕ) (h_region : run.PointsInRegion K)
    (h_freshBatches : run.HasFreshBatches K)
    (h_step_integrable : ∀ j < K,
      Integrable (fun ω ↦ ‖run.step j ω‖ ^ 2) ℙ)
    (hk : k < K) :
    Integrable (fun ω ↦
      ‖SPIDER.rawEstimate oracle run.point run.sample Q B b k ω -
        gradient f (run.point k ω)‖ ^ 2) ℙ ∧
      run.rawGradientErrorMeanSquare k ≤
        (oracle.noiseLevel : ℝ) ^ 2 / (B : ℝ) +
          (oracle.meanSquareLipschitz : ℝ) ^ 2 / (b : ℝ) *
            ∑ j ∈ Finset.Ico (k - k % Q) k, run.stepMeanSquare j := by
  -- Strong induction iterates the one-step estimate only within the current
  -- block, resetting the accumulated term at refresh indices.
  induction k using Nat.strong_induction_on with
  | h k ih =>
      by_cases hrefresh : k % Q = 0
      · have hone := rawGradientErrorMeanSquare_refreshOrUpdate run K k h_region
          h_freshBatches h_step_integrable (fun hupdate ↦ (hupdate hrefresh).elim) hk
        refine ⟨hone.1, ?_⟩
        simpa only [hrefresh, Nat.sub_zero, Finset.Ico_self, Finset.sum_empty,
          mul_zero, add_zero] using hone.2.1 hrefresh
      · have hkPositive : 0 < k := by
          exact Nat.pos_of_ne_zero fun hkZero ↦ hrefresh (by simp only [hkZero, Nat.zero_mod])
        have hkPredSucc : k - 1 + 1 = k := by omega
        have hprevious := ih (k - 1) (by omega) (by omega)
        have hone := rawGradientErrorMeanSquare_refreshOrUpdate run K k h_region
          h_freshBatches h_step_integrable (fun _ ↦ hprevious.1) hk
        refine ⟨hone.1, ?_⟩
        have hQGtOne : 1 < (Q : ℕ) := by
          have hQPositive : 0 < (Q : ℕ) := Q.pos
          by_contra hnot
          have hQeq : (Q : ℕ) = 1 := by omega
          exact hrefresh (by rw [hQeq, Nat.mod_one])
        have hmodSucc :
            k % Q = ((k - 1) % Q + 1) % Q := by
          conv_lhs => rw [← hkPredSucc]
          rw [Nat.add_mod, Nat.mod_eq_of_lt hQGtOne]
        have hpreviousRemainderSucc : (k - 1) % Q + 1 < Q := by
          have hpreviousModLt : (k - 1) % Q < Q := Nat.mod_lt (k - 1) Q.pos
          by_contra hnot
          have heq : (k - 1) % Q + 1 = Q := by omega
          apply hrefresh
          rw [hmodSucc, heq, Nat.mod_self]
        have hkModSucc : k % Q = (k - 1) % Q + 1 := by
          rw [hmodSucc, Nat.mod_eq_of_lt hpreviousRemainderSucc]
        have hblockStart :
            k - k % Q = (k - 1) - (k - 1) % Q := by
          omega
        have hstart_le : k - k % Q ≤ k - 1 := by
          have hkModPositive : 0 < k % Q := Nat.pos_of_ne_zero hrefresh
          omega
        have hblockSum :
            (∑ j ∈ Finset.Ico (k - k % Q) k, run.stepMeanSquare j) =
              (∑ j ∈ Finset.Ico ((k - 1) - (k - 1) % Q) (k - 1),
                run.stepMeanSquare j) + run.stepMeanSquare (k - 1) := by
          calc
            (∑ j ∈ Finset.Ico (k - k % Q) k, run.stepMeanSquare j) =
                ∑ j ∈ Finset.Ico (k - k % Q) ((k - 1) + 1),
                  run.stepMeanSquare j := by rw [hkPredSucc]
            _ = (∑ j ∈ Finset.Ico (k - k % Q) (k - 1),
                  run.stepMeanSquare j) + run.stepMeanSquare (k - 1) :=
              Finset.sum_Ico_succ_top hstart_le run.stepMeanSquare
            _ = (∑ j ∈ Finset.Ico ((k - 1) - (k - 1) % Q) (k - 1),
                  run.stepMeanSquare j) + run.stepMeanSquare (k - 1) := by
              rw [hblockStart]
        calc
          run.rawGradientErrorMeanSquare k ≤
              run.rawGradientErrorMeanSquare (k - 1) +
                (oracle.meanSquareLipschitz : ℝ) ^ 2 / (b : ℝ) *
                  run.stepMeanSquare (k - 1) := hone.2.2 hrefresh
          _ ≤ ((oracle.noiseLevel : ℝ) ^ 2 / (B : ℝ) +
                (oracle.meanSquareLipschitz : ℝ) ^ 2 / (b : ℝ) *
                  ∑ j ∈ Finset.Ico ((k - 1) - (k - 1) % Q) (k - 1),
                    run.stepMeanSquare j) +
              (oracle.meanSquareLipschitz : ℝ) ^ 2 / (b : ℝ) *
                run.stepMeanSquare (k - 1) := by
            exact add_le_add hprevious.2 le_rfl
          _ = (oracle.noiseLevel : ℝ) ^ 2 / (B : ℝ) +
                (oracle.meanSquareLipschitz : ℝ) ^ 2 / (b : ℝ) *
                  ∑ j ∈ Finset.Ico (k - k % Q) k, run.stepMeanSquare j := by
            rw [hblockSum]
            ring

/-- The accumulated SPIDER error estimate under the pointwise region condition
used by the estimator argument. -/
theorem accumulatedGradientErrorMeanSquare_le_of_pointsInRegion
    (run : StochasticRun h oracle ℙ x₀ multiplier₀ params Q B b)
    (K : ℕ) (h_region : run.PointsInRegion K)
    (h_step_integrable : run.HasIntegrableStepSquares K) :
    ∑ k ∈ Finset.range K, run.gradientErrorMeanSquare k ≤
      K * oracle.noiseLevel ^ 2 / B +
        (Q * oracle.meanSquareLipschitz ^ 2 / b) *
          ∑ k ∈ Finset.range K, run.stepMeanSquare k := by
  classical
  have hrawBound (k : ℕ) (hk : k < K) :
      run.gradientErrorMeanSquare k ≤
        (oracle.noiseLevel : ℝ) ^ 2 / (B : ℝ) +
          (oracle.meanSquareLipschitz : ℝ) ^ 2 / (b : ℝ) *
            ∑ j ∈ Finset.Ico (k - k % Q) k, run.stepMeanSquare j := by
    have hraw := rawGradientErrorMeanSquare_le_lastRefresh run K k h_region
      (hasFreshBatches run K) h_step_integrable hk
    exact (gradientErrorMeanSquare_le_rawGradientErrorMeanSquare run K k h_region hk
      hraw.1).trans hraw.2
  -- The generic block count applies because each step mean square is nonnegative.
  have hblockCount := sum_lastRefresh_le run.stepMeanSquare
    (stepMeanSquare_nonneg run)
    Q K Q.pos
  have hcoefficientNonnegative :
      0 ≤ (oracle.meanSquareLipschitz : ℝ) ^ 2 / (b : ℝ) := by
    positivity
  -- Sum the pointwise last-refresh bounds and then count each step at most `Q` times.
  calc
    ∑ k ∈ Finset.range K, run.gradientErrorMeanSquare k ≤
        ∑ k ∈ Finset.range K,
          ((oracle.noiseLevel : ℝ) ^ 2 / (B : ℝ) +
            (oracle.meanSquareLipschitz : ℝ) ^ 2 / (b : ℝ) *
              ∑ j ∈ Finset.Ico (k - k % Q) k,
                run.stepMeanSquare j) := by
      exact Finset.sum_le_sum fun k hk ↦ hrawBound k (Finset.mem_range.mp hk)
    _ = K * (oracle.noiseLevel : ℝ) ^ 2 / (B : ℝ) +
          (oracle.meanSquareLipschitz : ℝ) ^ 2 / (b : ℝ) *
            ∑ k ∈ Finset.range K,
              ∑ j ∈ Finset.Ico (k - k % Q) k,
                run.stepMeanSquare j := by
      rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range,
        nsmul_eq_mul, Finset.mul_sum]
      ring
    _ ≤ K * (oracle.noiseLevel : ℝ) ^ 2 / (B : ℝ) +
          (oracle.meanSquareLipschitz : ℝ) ^ 2 / (b : ℝ) *
            ((Q : ℕ) * ∑ k ∈ Finset.range K, run.stepMeanSquare k) := by
      exact add_le_add_right
        (mul_le_mul_of_nonneg_left hblockCount hcoefficientNonnegative) _
    _ = K * oracle.noiseLevel ^ 2 / B +
          (Q * oracle.meanSquareLipschitz ^ 2 / b) *
            ∑ k ∈ Finset.range K, run.stepMeanSquare k := by
      ring

/-- Lemma 3.3: On an almost-surely admissible length-`K` prefix whose squared
steps are integrable, the independent-batch stochastic NR-LALM run satisfies
the accumulated expected squared projected SPIDER gradient-error bound. -/
theorem accumulatedGradientErrorMeanSquare_le
    (run : StochasticRun h oracle ℙ x₀ multiplier₀ params Q B b)
    (K : ℕ) (h_admissible : run.IsAEAdmissiblePrefix K)
    (h_step_integrable : run.HasIntegrableStepSquares K) :
    ∑ k ∈ Finset.range K, run.gradientErrorMeanSquare k ≤
      K * oracle.noiseLevel ^ 2 / B +
        (Q * oracle.meanSquareLipschitz ^ 2 / b) *
          ∑ k ∈ Finset.range K, run.stepMeanSquare k := by
  obtain ⟨run', hrun'_admissible, _hpoint, _hmultiplier, hstep, herror⟩ :=
    h_admissible.exists_pathwiseVersion run K
  have herrorMeanSquare (k : ℕ) :
      run'.gradientErrorMeanSquare k = run.gradientErrorMeanSquare k := by
    rw [run'.gradientErrorMeanSquare_def, run.gradientErrorMeanSquare_def]
    exact integral_congr_ae ((herror k).fun_comp fun e ↦ ‖e‖ ^ 2)
  have hstepMeanSquare (k : ℕ) :
      run'.stepMeanSquare k = run.stepMeanSquare k := by
    rw [run'.stepMeanSquare_def, run.stepMeanSquare_def]
    exact integral_congr_ae ((hstep k).fun_comp fun p ↦ ‖p‖ ^ 2)
  have hstepIntegrable' : run'.HasIntegrableStepSquares K := by
    intro k hk
    exact (h_step_integrable k hk).congr
      ((hstep k).symm.fun_comp (fun p ↦ ‖p‖ ^ 2))
  have hbound := accumulatedGradientErrorMeanSquare_le_of_pointsInRegion run' K
    hrun'_admissible.pointsInRegion hstepIntegrable'
  simpa only [herrorMeanSquare, hstepMeanSquare] using hbound

end LALM.StochasticRun
