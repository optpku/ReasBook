/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@5bf5af722d85bd5c98368c41c4066124a15e8fd3:ReasBook/Papers/TR_LALM_theory/README.md (formalization contributor).
-/

module

public import TR_LALM_theory.Corollary_4_2.StochasticEstimator
public import TR_LALM_theory.Corollary_4_2.StochasticEstimatorProbability

public section

open MeasureTheory
open scoped BigOperators NNReal

namespace LALM.Correction.StochasticRun

open EstimatorProbability

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
variable {Q B b : ℕ+}

/-- Helper for Corollary 4.2: sampled gradients are measurable jointly in the
point and oracle sample. -/
private lemma measurable_sampleGradient :
    Measurable (fun z : EuclideanSpace ℝ (Fin n) × Ξ ↦
      oracle.sampleGradient z.1 z.2) :=
  oracle.measurable_sampleGradient

/-- Helper for Corollary 4.2: the corrected state fixed before iteration `k`
contains both points, the multiplier, and the preceding raw estimate. -/
private noncomputable def preBatchState
    (run : StochasticRun h oracle P x₀ multiplier₀ params Q B b) (k : ℕ) :
    Ω → EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) ×
      EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin n) :=
  fun ω ↦
    (run.point k ω, run.point (k - 1) ω, run.multiplier k ω,
      if k = 0 then 0 else
        SPIDER.rawEstimate oracle run.point run.sample Q B b (k - 1) ω)

/-- Helper for Corollary 4.2: the corrected pre-batch state is almost
everywhere measurable. -/
private lemma aemeasurable_preBatchState
    (run : StochasticRun h oracle P x₀ multiplier₀ params Q B b) (k : ℕ) :
    AEMeasurable (preBatchState run k) P := by
  have hpreviousRaw : AEMeasurable
      (fun ω ↦ if k = 0 then 0 else
        SPIDER.rawEstimate oracle run.point run.sample Q B b (k - 1) ω) P := by
    by_cases hk : k = 0
    · simp only [hk, ite_true]
      exact aemeasurable_const
    · simp only [hk, ite_false]
      exact run.aemeasurable_rawEstimate (k - 1)
  -- Assemble the four stored components without unfolding the estimator recursion.
  unfold preBatchState
  exact (run.aemeasurable_point k).prodMk
    ((run.aemeasurable_point (k - 1)).prodMk
      ((run.aemeasurable_multiplier k).prodMk hpreviousRaw))

/-- Helper for Corollary 4.2: the mean square of the corrected run's
unprojected SPIDER estimation error. -/
private noncomputable def rawGradientErrorMeanSquare
    (run : StochasticRun h oracle P x₀ multiplier₀ params Q B b) (k : ℕ) : ℝ :=
  ∫ ω, ‖SPIDER.rawEstimate oracle run.point run.sample Q B b k ω -
    gradient f (run.point k ω)‖ ^ 2 ∂P

/-- Helper for Corollary 4.2: clipping cannot increase corrected mean-square
gradient error when the raw squared error is integrable. -/
private lemma gradientErrorMeanSquare_le_rawGradientErrorMeanSquare
    (run : StochasticRun h oracle P x₀ multiplier₀ params Q B b)
    (K k : ℕ) (h_admissible : run.IsAdmissiblePrefix K) (hk : k < K)
    (hraw : Integrable (fun ω ↦
      ‖SPIDER.rawEstimate oracle run.point run.sample Q B b k ω -
        gradient f (run.point k ω)‖ ^ 2) P) :
    run.gradientErrorMeanSquare k ≤ run.rawGradientErrorMeanSquare k := by
  -- Admissibility puts the true gradient in the clipping ball.
  have hpointwise (ω : Ω) :
      ‖run.gradientError k ω‖ ^ 2 ≤
        ‖SPIDER.rawEstimate oracle run.point run.sample Q B b k ω -
          gradient f (run.point k ω)‖ ^ 2 := by
    have hx := base_mem_region h (run.point k ω) (run.baseStep k ω)
      ((run.isAdmissiblePrefix_iff K).mp h_admissible k hk ω)
    rw [run.gradientError_apply, run.gradientEstimate_apply, SPIDER.estimate_apply]
    exact pow_le_pow_left₀ (norm_nonneg _)
      (SPIDER.norm_clip_sub_le h.gradientBound _ _
        (h.norm_gradient_le _ hx)) 2
  -- Integrate the pointwise projection estimate.
  rw [run.gradientErrorMeanSquare_def, rawGradientErrorMeanSquare]
  exact integral_mono_of_nonneg (ae_of_all P (fun ω ↦ sq_nonneg _)) hraw
    (ae_of_all P hpointwise)

/-- Helper for Corollary 4.2: the fixed-state nonrefresh integrand records the
preceding raw error plus one centered batch innovation. -/
private noncomputable def updateIntegrand
    (h : EqualityConstrained.Regularity f c)
    (oracle : EqualityConstrained.StochasticOracle f h.region ν) (b : ℕ+)
    (z : ((EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) ×
        EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin n)) × (ℕ → Ξ))) : ℝ :=
  @ite ℝ (z.1.1 ∈ h.region ∧ z.1.2.1 ∈ h.region)
    (Classical.propDecidable _)
    (‖(z.1.2.2.2 - h.objectiveGradientExtension z.1.2.1) +
      (b : ℝ)⁻¹ • ∑ i ∈ Finset.range b,
        ((oracle.sampleGradient z.1.1 (z.2 i) -
            oracle.sampleGradient z.1.2.1 (z.2 i)) -
          (h.objectiveGradientExtension z.1.1 -
            h.objectiveGradientExtension z.1.2.1))‖ ^ 2)
    0

/-- Helper for Corollary 4.2: the nonrefresh conditional moment bound keeps
the actual displacement between the two stored points. -/
private noncomputable def updateConditionalBound
    (h : EqualityConstrained.Regularity f c)
    (oracle : EqualityConstrained.StochasticOracle f h.region ν) (b : ℕ+)
    (s : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) ×
      EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin n)) : ℝ :=
  ‖s.2.2.2 - h.objectiveGradientExtension s.2.1‖ ^ 2 +
    (oracle.meanSquareLipschitz : ℝ) ^ 2 / (b : ℝ) * ‖s.1 - s.2.1‖ ^ 2

/-- Helper for Corollary 4.2: the fixed-state nonrefresh integrand is measurable. -/
private lemma measurable_updateIntegrand
    (h : EqualityConstrained.Regularity f c)
    (oracle : EqualityConstrained.StochasticOracle f h.region ν) (b : ℕ+) :
    Measurable (updateIntegrand h oracle b) := by
  -- Assemble measurability from the two stored points and every batch coordinate.
  unfold updateIntegrand
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
          (ℕ → Ξ)) ↦ z.1.2.2.2) := by
      fun_prop
    exact ((hprevious.sub hgradientY).add
      (hsum.const_smul ((b : ℝ)⁻¹))).norm.pow_const 2
  · fun_prop

/-- Helper for Corollary 4.2: the fixed-state nonrefresh conditional bound is
measurable. -/
private lemma measurable_updateConditionalBound
    (h : EqualityConstrained.Regularity f c)
    (oracle : EqualityConstrained.StochasticOracle f h.region ν) (b : ℕ+) :
    Measurable (updateConditionalBound h oracle b) := by
  -- Both stored-point terms are continuous-measurable expressions.
  unfold updateConditionalBound
  have hx : Measurable (fun s :
      EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) ×
        EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin n) ↦ s.1) :=
    measurable_fst
  have hy : Measurable (fun s :
      EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) ×
        EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin n) ↦ s.2.1) :=
    measurable_fst.comp measurable_snd
  have hgradient : Measurable (fun s :
      EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) ×
        EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin n) ↦
        h.objectiveGradientExtension s.2.1) :=
    h.measurable_objectiveGradientExtension.comp hy
  have hprevious : Measurable (fun s :
      EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) ×
        EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin n) ↦ s.2.2.2) := by
    fun_prop
  exact ((hprevious.sub hgradient).norm.pow_const 2).add
    (((hx.sub hy).norm.pow_const 2).const_mul
      ((oracle.meanSquareLipschitz : ℝ) ^ 2 / (b : ℝ)))

/-- Helper for Corollary 4.2: the globally measurable nonrefresh integrand is
pointwise nonnegative. -/
private lemma updateIntegrand_nonneg
    (h : EqualityConstrained.Regularity f c)
    (oracle : EqualityConstrained.StochasticOracle f h.region ν) (b : ℕ+)
    (z : ((EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) ×
        EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin n)) × (ℕ → Ξ))) :
    0 ≤ updateIntegrand h oracle b z := by
  unfold updateIntegrand
  split
  · positivity
  · exact le_rfl

/-- Helper for Corollary 4.2: each fixed pre-batch state gives an integrable
nonrefresh update integrand under the fresh-batch image law. -/
private lemma integrable_updateIntegrand_section
    (run : StochasticRun h oracle P x₀ multiplier₀ params Q B b)
    (k : ℕ) (hbatchIndependent : ProbabilityTheory.iIndepFun (run.sample k) P)
    (s : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) ×
      EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin n)) :
    Integrable (fun d ↦ updateIntegrand h oracle b (s, d))
      (P.map fun ω i ↦ run.sample k i ω) := by
  have hfresh : AEMeasurable (fun ω i ↦ run.sample k i ω) P :=
    aemeasurable_pi_lambda _ fun i ↦ (run.hasLaw_sample k i).aemeasurable
  have hsectionMeasurable : Measurable (fun d ↦
      updateIntegrand h oracle b (s, d)) :=
    (measurable_updateIntegrand h oracle b).comp
      (measurable_const.prodMk measurable_id)
  by_cases hs : s.1 ∈ h.region ∧ s.2.1 ∈ h.region
  · have hfixed := fixedPointUpdateBatchMeanSquare_le
      (oracle := oracle) s.1 hs.1 s.2.1 hs.2
      (s.2.2.2 - gradient f s.2.1) (run.sample k) b
      (run.hasLaw_sample k) hbatchIndependent
    refine (integrable_map_measure hsectionMeasurable.aestronglyMeasurable hfresh).2 ?_
    simpa only [Function.comp_def, updateIntegrand, if_pos hs,
      h.objectiveGradientExtension_eq hs.1,
      h.objectiveGradientExtension_eq hs.2] using hfixed.1
  · have hzero : Integrable (fun _ω : Ω ↦ (0 : ℝ)) P := integrable_const _
    refine (integrable_map_measure hsectionMeasurable.aestronglyMeasurable hfresh).2 ?_
    simpa only [Function.comp_def, updateIntegrand, if_neg hs] using hzero

/-- Helper for Corollary 4.2: each fixed-state nonrefresh section satisfies
the oracle mean-square-Lipschitz conditional bound. -/
private lemma integral_updateIntegrand_section_le
    (run : StochasticRun h oracle P x₀ multiplier₀ params Q B b)
    (k : ℕ) (hbatchIndependent : ProbabilityTheory.iIndepFun (run.sample k) P)
    (s : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) ×
      EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin n)) :
    (∫ d, updateIntegrand h oracle b (s, d)
        ∂P.map fun ω i ↦ run.sample k i ω) ≤
      updateConditionalBound h oracle b s := by
  have hfresh : AEMeasurable (fun ω i ↦ run.sample k i ω) P :=
    aemeasurable_pi_lambda _ fun i ↦ (run.hasLaw_sample k i).aemeasurable
  have hsectionMeasurable : Measurable (fun d ↦
      updateIntegrand h oracle b (s, d)) :=
    (measurable_updateIntegrand h oracle b).comp
      (measurable_const.prodMk measurable_id)
  rw [integral_map hfresh hsectionMeasurable.aestronglyMeasurable]
  by_cases hs : s.1 ∈ h.region ∧ s.2.1 ∈ h.region
  · have hfixed := fixedPointUpdateBatchMeanSquare_le
      (oracle := oracle) s.1 hs.1 s.2.1 hs.2
      (s.2.2.2 - gradient f s.2.1) (run.sample k) b
      (run.hasLaw_sample k) hbatchIndependent
    simpa only [Function.comp_apply, updateIntegrand, updateConditionalBound,
      if_pos hs, h.objectiveGradientExtension_eq hs.1,
      h.objectiveGradientExtension_eq hs.2] using hfixed.2
  · simp only [updateIntegrand, updateConditionalBound, if_neg hs, integral_zero]
    positivity

/-- Helper for Corollary 4.2: the abstract nonrefresh integrand computes to
the corrected run's next raw squared error. -/
private lemma updateIntegrand_eq_rawError
    (run : StochasticRun h oracle P x₀ multiplier₀ params Q B b)
    (k : ℕ) (hkPositive : 0 < k) (hrefresh : k % Q ≠ 0)
    (ω : Ω) (hx : run.point k ω ∈ h.region)
    (hy : run.point (k - 1) ω ∈ h.region) :
    updateIntegrand h oracle b
        (preBatchState run k ω, fun i ↦ run.sample k i ω) =
      ‖SPIDER.rawEstimate oracle run.point run.sample Q B b k ω -
        gradient f (run.point k ω)‖ ^ 2 := by
  have hkPredSucc : k - 1 + 1 = k := by omega
  have hnonrefreshPred : (k - 1 + 1) % Q ≠ 0 := by
    simpa only [hkPredSucc] using hrefresh
  -- Normalize the recursive raw estimate at the predecessor index.
  simp only [updateIntegrand, preBatchState, ne_of_gt hkPositive, if_false,
    hx, hy, and_self, if_pos, h.objectiveGradientExtension_eq hx,
    h.objectiveGradientExtension_eq hy]
  rw [← hkPredSucc,
    SPIDER.rawEstimate_of_update oracle run.point run.sample Q B b (k - 1) ω
      hnonrefreshPred,
    batchAverage_sub]
  simp only [hkPredSucc]
  apply congrArg (fun z : EuclideanSpace ℝ (Fin n) ↦ ‖z‖ ^ 2)
  module

/-- Helper for Corollary 4.2: the abstract conditional bound computes to the
preceding raw error plus the actual corrected displacement square. -/
private lemma updateConditionalBound_preBatchState
    (run : StochasticRun h oracle P x₀ multiplier₀ params Q B b)
    (k : ℕ) (hkPositive : 0 < k) (ω : Ω)
    (hpreviousRegion : run.point (k - 1) ω ∈ h.region) :
    updateConditionalBound h oracle b (preBatchState run k ω) =
      ‖SPIDER.rawEstimate oracle run.point run.sample Q B b (k - 1) ω -
        gradient f (run.point (k - 1) ω)‖ ^ 2 +
      (oracle.meanSquareLipschitz : ℝ) ^ 2 / (b : ℝ) *
        ‖run.point k ω - run.point (k - 1) ω‖ ^ 2 := by
  -- Expose only the stored pre-batch projections.
  simp only [updateConditionalBound, preBatchState, ne_of_gt hkPositive, if_false,
    h.objectiveGradientExtension_eq hpreviousRegion]

/-- Helper for Corollary 4.2: a corrected SPIDER refresh has integrable
raw squared error bounded by the refresh-batch variance. -/
private lemma rawGradientErrorMeanSquare_refresh
    (run : StochasticRun h oracle P x₀ multiplier₀ params Q B b)
    (K k : ℕ) (h_admissible : run.IsAdmissiblePrefix K)
    (h_freshBatches : run.HasFreshBatches K)
    (hk : k < K) (hrefresh : k % Q = 0) :
    Integrable (fun ω ↦
      ‖SPIDER.rawEstimate oracle run.point run.sample Q B b k ω -
        gradient f (run.point k ω)‖ ^ 2) P ∧
      run.rawGradientErrorMeanSquare k ≤
        (oracle.noiseLevel : ℝ) ^ 2 / (B : ℝ) := by
  classical
  let state := preBatchState run k
  let freshBatch : Ω → (ℕ → Ξ) := fun ω i ↦ run.sample k i ω
  have hstate : AEMeasurable state P := by
    simpa only [state] using aemeasurable_preBatchState run k
  have hfreshBatch : AEMeasurable freshBatch P := by
    exact aemeasurable_pi_lambda _
      (fun i ↦ (run.hasLaw_sample k i).aemeasurable)
  have hindependent : ProbabilityTheory.IndepFun state freshBatch P := by
    dsimp only [state, freshBatch]
    unfold preBatchState
    exact (run.hasFreshBatches_iff K).mp h_freshBatches k hk
  have hbatchIndependent : ProbabilityTheory.iIndepFun (run.sample k) P := by
    have hinjective : Function.Injective (fun i : ℕ ↦ (k, i)) := by
      intro i j hij
      exact congrArg Prod.snd hij
    simpa only using run.independent_sample.precomp hinjective
  let φ :
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
  have hsection : ∀ s, Integrable (fun d ↦ φ (s, d)) (P.map freshBatch) := by
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
    · have hzero : Integrable (fun _ω : Ω ↦ (0 : ℝ)) P := integrable_const _
      refine (integrable_map_measure hsectionMeasurable.aestronglyMeasurable
        hfreshBatch).2 ?_
      simpa only [Function.comp_def, φ, if_neg hs] using hzero
  have hbound : ∀ s,
      (∫ d, φ (s, d) ∂P.map freshBatch) ≤ C s := by
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
  have hφNonnegative (z :
      ((EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) ×
          EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin n)) ×
        (ℕ → Ξ))) : 0 ≤ φ z := by
    unfold φ
    split
    · positivity
    · exact le_rfl
  have hpair := independentPair_integrable_integral_le state freshBatch φ C
    hindependent hstate hfreshBatch hφ.aemeasurable
    hφNonnegative
    (Filter.Eventually.of_forall hsection) (integrable_const _)
    (Filter.Eventually.of_forall hbound)
  have hidentify ( ω : Ω) :
      φ (state ω, freshBatch ω) =
        ‖SPIDER.rawEstimate oracle run.point run.sample Q B b k ω -
          gradient f (run.point k ω)‖ ^ 2 := by
    have hx : run.point k ω ∈ h.region :=
      base_mem_region h (run.point k ω) (run.baseStep k ω)
        ((run.isAdmissiblePrefix_iff K).mp h_admissible k hk ω)
    simp only [φ, state, freshBatch, preBatchState, hx, if_pos,
      h.objectiveGradientExtension_eq hx]
    rw [SPIDER.rawEstimate_of_refresh oracle run.point run.sample Q B b k ω hrefresh,
      batchAverage_sub]
  have hintegrable : Integrable (fun ω ↦
      ‖SPIDER.rawEstimate oracle run.point run.sample Q B b k ω -
        gradient f (run.point k ω)‖ ^ 2) P :=
    hpair.1.congr (Filter.Eventually.of_forall hidentify)
  have hrefreshBound : run.rawGradientErrorMeanSquare k ≤
      (oracle.noiseLevel : ℝ) ^ 2 / (B : ℝ) := by
    rw [rawGradientErrorMeanSquare,
      ← integral_congr_ae (Filter.Eventually.of_forall hidentify)]
    calc
      (∫ ω, φ (state ω, freshBatch ω) ∂P) ≤
          ∫ s, C s ∂P.map state := hpair.2
      _ = (oracle.noiseLevel : ℝ) ^ 2 / (B : ℝ) := by
        rw [integral_const, Measure.real,
          Measure.map_apply_of_aemeasurable hstate MeasurableSet.univ]
        simp only [Set.preimage_univ, measure_univ,
          ENNReal.toReal_one, one_smul]
  exact ⟨hintegrable, hrefreshBound⟩

/-- Helper for Corollary 4.2: fresh-batch independence turns the abstract
nonrefresh integrand into an integrable pair with its conditional bound. -/
private lemma updateIndependentPair_integrable_integral_le
    (run : StochasticRun h oracle P x₀ multiplier₀ params Q B b)
    (K k : ℕ) (h_freshBatches : run.HasFreshBatches K)
    (hCmap : Integrable (updateConditionalBound h oracle b)
      (P.map (preBatchState run k))) (hk : k < K) :
    Integrable (fun ω ↦ updateIntegrand h oracle b
      (preBatchState run k ω, fun i ↦ run.sample k i ω)) P ∧
      (∫ ω, updateIntegrand h oracle b
          (preBatchState run k ω, fun i ↦ run.sample k i ω) ∂P) ≤
        ∫ s, updateConditionalBound h oracle b s ∂P.map (preBatchState run k) := by
  classical
  have hstate : AEMeasurable (preBatchState run k) P :=
    aemeasurable_preBatchState run k
  have hfreshBatch : AEMeasurable (fun ω i ↦ run.sample k i ω) P :=
    aemeasurable_pi_lambda _ fun i ↦ (run.hasLaw_sample k i).aemeasurable
  have hindependent : ProbabilityTheory.IndepFun (preBatchState run k)
      (fun ω i ↦ run.sample k i ω) P := by
    unfold preBatchState
    exact (run.hasFreshBatches_iff K).mp h_freshBatches k hk
  have hbatchIndependent : ProbabilityTheory.iIndepFun (run.sample k) P := by
    have hinjective : Function.Injective (fun i : ℕ ↦ (k, i)) := by
      intro i j hij
      exact congrArg Prod.snd hij
    simpa only using run.independent_sample.precomp hinjective
  have hsection : ∀ s, Integrable
      (fun d ↦ updateIntegrand h oracle b (s, d))
      (P.map fun ω i ↦ run.sample k i ω) :=
    fun s ↦ integrable_updateIntegrand_section run k hbatchIndependent s
  have hbound : ∀ s,
      (∫ d, updateIntegrand h oracle b (s, d)
        ∂P.map fun ω i ↦ run.sample k i ω) ≤
          updateConditionalBound h oracle b s :=
    fun s ↦ integral_updateIntegrand_section_le run k hbatchIndependent s
  -- Apply the generic independent-pair integration theorem in one spelling.
  exact independentPair_integrable_integral_le
    (preBatchState run k) (fun ω i ↦ run.sample k i ω)
    (updateIntegrand h oracle b) (updateConditionalBound h oracle b)
    hindependent hstate hfreshBatch
    (measurable_updateIntegrand h oracle b).aemeasurable
    (updateIntegrand_nonneg h oracle b)
    (Filter.Eventually.of_forall hsection) hCmap
    (Filter.Eventually.of_forall hbound)

/-- Helper for Corollary 4.2: integrability of the preceding raw error and
actual displacement transports to the conditional bound's state law. -/
private lemma integrable_updateConditionalBound_map_preBatchState
    (run : StochasticRun h oracle P x₀ multiplier₀ params Q B b) (k : ℕ)
    (hprevious : Integrable (fun ω ↦
      ‖SPIDER.rawEstimate oracle run.point run.sample Q B b (k - 1) ω -
        gradient f (run.point (k - 1) ω)‖ ^ 2) P)
    (hdisplacement : Integrable (fun ω ↦
      ‖run.point k ω - run.point (k - 1) ω‖ ^ 2) P)
    (hpreviousRegion : ∀ ω, run.point (k - 1) ω ∈ h.region)
    (hkPositive : 0 < k) :
    Integrable (updateConditionalBound h oracle b)
      (P.map (preBatchState run k)) := by
  have hstate : AEMeasurable (preBatchState run k) P :=
    aemeasurable_preBatchState run k
  have hidentify (ω : Ω) :
      updateConditionalBound h oracle b (preBatchState run k ω) =
        ‖SPIDER.rawEstimate oracle run.point run.sample Q B b (k - 1) ω -
          gradient f (run.point (k - 1) ω)‖ ^ 2 +
        (oracle.meanSquareLipschitz : ℝ) ^ 2 / (b : ℝ) *
          ‖run.point k ω - run.point (k - 1) ω‖ ^ 2 :=
    updateConditionalBound_preBatchState run k hkPositive ω
      (hpreviousRegion ω)
  have hscaled : Integrable (fun ω ↦
      (oracle.meanSquareLipschitz : ℝ) ^ 2 / (b : ℝ) *
        ‖run.point k ω - run.point (k - 1) ω‖ ^ 2) P :=
    hdisplacement.const_mul ((oracle.meanSquareLipschitz : ℝ) ^ 2 / (b : ℝ))
  have hcomp : Integrable
      (fun ω ↦ updateConditionalBound h oracle b (preBatchState run k ω)) P :=
    (hprevious.add hscaled).congr
      (Filter.Eventually.of_forall fun ω ↦ (hidentify ω).symm)
  -- Push the integrable composite through the pre-batch state map.
  exact (integrable_map_measure
    (measurable_updateConditionalBound h oracle b).aestronglyMeasurable hstate).2 hcomp

/-- Helper for Corollary 4.2: integrating the conditional bound gives the
preceding raw moment plus the actual-displacement moment. -/
private lemma integral_updateConditionalBound_map_preBatchState
    (run : StochasticRun h oracle P x₀ multiplier₀ params Q B b) (k : ℕ)
    (hprevious : Integrable (fun ω ↦
      ‖SPIDER.rawEstimate oracle run.point run.sample Q B b (k - 1) ω -
        gradient f (run.point (k - 1) ω)‖ ^ 2) P)
    (hdisplacement : Integrable (fun ω ↦
      ‖run.point k ω - run.point (k - 1) ω‖ ^ 2) P)
    (hpreviousRegion : ∀ ω, run.point (k - 1) ω ∈ h.region)
    (hkPositive : 0 < k) :
    (∫ s, updateConditionalBound h oracle b s ∂P.map (preBatchState run k)) =
      run.rawGradientErrorMeanSquare (k - 1) +
        (oracle.meanSquareLipschitz : ℝ) ^ 2 / (b : ℝ) *
          run.pointDisplacementMeanSquare (k - 1) := by
  have hstate : AEMeasurable (preBatchState run k) P :=
    aemeasurable_preBatchState run k
  rw [integral_map hstate
    (measurable_updateConditionalBound h oracle b).aestronglyMeasurable]
  have hidentify (ω : Ω) :
      updateConditionalBound h oracle b (preBatchState run k ω) =
        ‖SPIDER.rawEstimate oracle run.point run.sample Q B b (k - 1) ω -
          gradient f (run.point (k - 1) ω)‖ ^ 2 +
        (oracle.meanSquareLipschitz : ℝ) ^ 2 / (b : ℝ) *
          ‖run.point k ω - run.point (k - 1) ω‖ ^ 2 :=
    updateConditionalBound_preBatchState run k hkPositive ω
      (hpreviousRegion ω)
  have hscaled : Integrable (fun ω ↦
      (oracle.meanSquareLipschitz : ℝ) ^ 2 / (b : ℝ) *
        ‖run.point k ω - run.point (k - 1) ω‖ ^ 2) P :=
    hdisplacement.const_mul ((oracle.meanSquareLipschitz : ℝ) ^ 2 / (b : ℝ))
  have hkPredSucc : k - 1 + 1 = k := by omega
  calc
    (∫ ω, updateConditionalBound h oracle b (preBatchState run k ω) ∂P) =
        ∫ ω,
          (‖SPIDER.rawEstimate oracle run.point run.sample Q B b (k - 1) ω -
              gradient f (run.point (k - 1) ω)‖ ^ 2 +
            (oracle.meanSquareLipschitz : ℝ) ^ 2 / (b : ℝ) *
              ‖run.point k ω - run.point (k - 1) ω‖ ^ 2) ∂P := by
      exact integral_congr_ae (Filter.Eventually.of_forall hidentify)
    _ = run.rawGradientErrorMeanSquare (k - 1) +
        (oracle.meanSquareLipschitz : ℝ) ^ 2 / (b : ℝ) *
          run.pointDisplacementMeanSquare (k - 1) := by
      rw [integral_add hprevious hscaled, integral_const_mul,
        rawGradientErrorMeanSquare, run.pointDisplacementMeanSquare_def,
        hkPredSucc]

/-- Helper for Corollary 4.2: a corrected nonrefresh SPIDER update adds one
actual-displacement innovation to the preceding raw mean square. -/
private lemma rawGradientErrorMeanSquare_update
    (run : StochasticRun h oracle P x₀ multiplier₀ params Q B b)
    (K k : ℕ) (h_admissible : run.IsAdmissiblePrefix K)
    (h_freshBatches : run.HasFreshBatches K)
    (h_displacement_integrable : ∀ j < K,
      Integrable (fun ω ↦ ‖run.point (j + 1) ω - run.point j ω‖ ^ 2) P)
    (hprevious_integrable :
      Integrable (fun ω ↦
        ‖SPIDER.rawEstimate oracle run.point run.sample Q B b (k - 1) ω -
          gradient f (run.point (k - 1) ω)‖ ^ 2) P)
    (hk : k < K) (hrefresh : k % Q ≠ 0) :
    Integrable (fun ω ↦
      ‖SPIDER.rawEstimate oracle run.point run.sample Q B b k ω -
        gradient f (run.point k ω)‖ ^ 2) P ∧
      run.rawGradientErrorMeanSquare k ≤
        run.rawGradientErrorMeanSquare (k - 1) +
          (oracle.meanSquareLipschitz : ℝ) ^ 2 / (b : ℝ) *
            run.pointDisplacementMeanSquare (k - 1) := by
  have hkPositive : 0 < k := by
    apply Nat.pos_of_ne_zero
    intro hkZero
    apply hrefresh
    simp only [hkZero, Nat.zero_mod]
  have hkPredSucc : k - 1 + 1 = k := by omega
  have hkPredLt : k - 1 < K := by omega
  have hpreviousRegion (ω : Ω) : run.point (k - 1) ω ∈ h.region := by
    exact base_mem_region h (run.point (k - 1) ω)
      (run.baseStep (k - 1) ω)
      ((run.isAdmissiblePrefix_iff K).mp h_admissible (k - 1) hkPredLt ω)
  have hdisplacement : Integrable (fun ω ↦
      ‖run.point k ω - run.point (k - 1) ω‖ ^ 2) P := by
    simpa only [hkPredSucc] using
      h_displacement_integrable (k - 1) hkPredLt
  have hCmap := integrable_updateConditionalBound_map_preBatchState
    run k hprevious_integrable hdisplacement hpreviousRegion hkPositive
  have hpair := updateIndependentPair_integrable_integral_le
    run K k h_freshBatches hCmap hk
  have hidentify (ω : Ω) :
      updateIntegrand h oracle b
          (preBatchState run k ω, fun i ↦ run.sample k i ω) =
        ‖SPIDER.rawEstimate oracle run.point run.sample Q B b k ω -
          gradient f (run.point k ω)‖ ^ 2 := by
    have hx := base_mem_region h (run.point k ω) (run.baseStep k ω)
      ((run.isAdmissiblePrefix_iff K).mp h_admissible k hk ω)
    exact updateIntegrand_eq_rawError run k hkPositive hrefresh ω hx
      (hpreviousRegion ω)
  have hintegrable : Integrable (fun ω ↦
      ‖SPIDER.rawEstimate oracle run.point run.sample Q B b k ω -
        gradient f (run.point k ω)‖ ^ 2) P :=
    hpair.1.congr (Filter.Eventually.of_forall hidentify)
  have hupdateBound : run.rawGradientErrorMeanSquare k ≤
      run.rawGradientErrorMeanSquare (k - 1) +
        (oracle.meanSquareLipschitz : ℝ) ^ 2 / (b : ℝ) *
          run.pointDisplacementMeanSquare (k - 1) := by
    rw [rawGradientErrorMeanSquare,
      ← integral_congr_ae (Filter.Eventually.of_forall hidentify)]
    calc
      (∫ ω, updateIntegrand h oracle b
          (preBatchState run k ω, fun i ↦ run.sample k i ω) ∂P) ≤
          ∫ s, updateConditionalBound h oracle b s
            ∂P.map (preBatchState run k) := hpair.2
      _ = run.rawGradientErrorMeanSquare (k - 1) +
          (oracle.meanSquareLipschitz : ℝ) ^ 2 / (b : ℝ) *
            run.pointDisplacementMeanSquare (k - 1) :=
        integral_updateConditionalBound_map_preBatchState
          run k hprevious_integrable hdisplacement hpreviousRegion hkPositive
  exact ⟨hintegrable, hupdateBound⟩

/-- Helper for Corollary 4.2: one corrected SPIDER iteration is either a
variance refresh or a displacement-controlled recursive update. -/
private lemma rawGradientErrorMeanSquare_refreshOrUpdate
    (run : StochasticRun h oracle P x₀ multiplier₀ params Q B b)
    (K k : ℕ) (h_admissible : run.IsAdmissiblePrefix K)
    (h_freshBatches : run.HasFreshBatches K)
    (h_displacement_integrable : ∀ j < K,
      Integrable (fun ω ↦ ‖run.point (j + 1) ω - run.point j ω‖ ^ 2) P)
    (hprevious_integrable : k % Q ≠ 0 →
      Integrable (fun ω ↦
        ‖SPIDER.rawEstimate oracle run.point run.sample Q B b (k - 1) ω -
          gradient f (run.point (k - 1) ω)‖ ^ 2) P)
    (hk : k < K) :
    Integrable (fun ω ↦
      ‖SPIDER.rawEstimate oracle run.point run.sample Q B b k ω -
        gradient f (run.point k ω)‖ ^ 2) P ∧
      ((k % Q = 0 →
          run.rawGradientErrorMeanSquare k ≤
            (oracle.noiseLevel : ℝ) ^ 2 / (B : ℝ)) ∧
        (k % Q ≠ 0 →
          run.rawGradientErrorMeanSquare k ≤
            run.rawGradientErrorMeanSquare (k - 1) +
              (oracle.meanSquareLipschitz : ℝ) ^ 2 / (b : ℝ) *
                run.pointDisplacementMeanSquare (k - 1))) := by
  -- Dispatch to declarations whose probability calculations have separate budgets.
  by_cases hrefresh : k % Q = 0
  · have hbound := rawGradientErrorMeanSquare_refresh run K k h_admissible
      h_freshBatches hk hrefresh
    exact ⟨hbound.1, ⟨fun _ ↦ hbound.2, fun hupdate ↦ (hupdate hrefresh).elim⟩⟩
  · have hbound := rawGradientErrorMeanSquare_update run K k h_admissible
      h_freshBatches h_displacement_integrable
      (hprevious_integrable hrefresh) hk hrefresh
    exact ⟨hbound.1, ⟨fun hzero ↦ (hrefresh hzero).elim, fun _ ↦ hbound.2⟩⟩

/-- Helper for Corollary 4.2: the raw SPIDER error accumulates only the update
variance since the most recent refresh. -/
private lemma rawGradientErrorMeanSquare_le_lastRefresh
    (run : StochasticRun h oracle P x₀ multiplier₀ params Q B b)
    (K k : ℕ) (h_admissible : run.IsAdmissiblePrefix K)
    (h_freshBatches : run.HasFreshBatches K)
    (h_displacement_integrable : ∀ j < K,
      Integrable (fun ω ↦ ‖run.point (j + 1) ω - run.point j ω‖ ^ 2) P)
    (hk : k < K) :
    Integrable (fun ω ↦
      ‖SPIDER.rawEstimate oracle run.point run.sample Q B b k ω -
        gradient f (run.point k ω)‖ ^ 2) P ∧
      run.rawGradientErrorMeanSquare k ≤
        (oracle.noiseLevel : ℝ) ^ 2 / (B : ℝ) +
          (oracle.meanSquareLipschitz : ℝ) ^ 2 / (b : ℝ) *
            ∑ j ∈ Finset.Ico (k - k % Q) k, run.pointDisplacementMeanSquare j := by
  -- Strong induction iterates the one-step estimate only within the current
  -- block, resetting the accumulated term at refresh indices.
  induction k using Nat.strong_induction_on with
  | h k ih =>
      by_cases hrefresh : k % Q = 0
      · have hone := rawGradientErrorMeanSquare_refreshOrUpdate run K k h_admissible
          h_freshBatches h_displacement_integrable (fun hupdate ↦ (hupdate hrefresh).elim) hk
        refine ⟨hone.1, ?_⟩
        simpa only [hrefresh, Nat.sub_zero, Finset.Ico_self, Finset.sum_empty,
          mul_zero, add_zero] using hone.2.1 hrefresh
      · have hkPositive : 0 < k := by
          apply Nat.pos_of_ne_zero
          intro hkZero
          apply hrefresh
          simp only [hkZero, Nat.zero_mod]
        have hkPredSucc : k - 1 + 1 = k := by omega
        have hkPredLt : k - 1 < k := by omega
        have hkPredK : k - 1 < K := by omega
        have hprevious := ih (k - 1) hkPredLt hkPredK
        have hone := rawGradientErrorMeanSquare_refreshOrUpdate run K k h_admissible
          h_freshBatches h_displacement_integrable (fun _ ↦ hprevious.1) hk
        refine ⟨hone.1, ?_⟩
        have hQGtOne : 1 < (Q : ℕ) := by
          have hQPositive : 0 < (Q : ℕ) := Q.pos
          by_contra hnot
          have hQeq : (Q : ℕ) = 1 := by omega
          apply hrefresh
          rw [hQeq, Nat.mod_one]
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
            (∑ j ∈ Finset.Ico (k - k % Q) k, run.pointDisplacementMeanSquare j) =
              (∑ j ∈ Finset.Ico ((k - 1) - (k - 1) % Q) (k - 1),
                run.pointDisplacementMeanSquare j) + run.pointDisplacementMeanSquare (k - 1) := by
          calc
            (∑ j ∈ Finset.Ico (k - k % Q) k, run.pointDisplacementMeanSquare j) =
                ∑ j ∈ Finset.Ico (k - k % Q) ((k - 1) + 1),
                  run.pointDisplacementMeanSquare j := by rw [hkPredSucc]
            _ = (∑ j ∈ Finset.Ico (k - k % Q) (k - 1),
                  run.pointDisplacementMeanSquare j) + run.pointDisplacementMeanSquare (k - 1) :=
              Finset.sum_Ico_succ_top hstart_le run.pointDisplacementMeanSquare
            _ = (∑ j ∈ Finset.Ico ((k - 1) - (k - 1) % Q) (k - 1),
                  run.pointDisplacementMeanSquare j) + run.pointDisplacementMeanSquare (k - 1) := by
              rw [hblockStart]
        calc
          run.rawGradientErrorMeanSquare k ≤
              run.rawGradientErrorMeanSquare (k - 1) +
                (oracle.meanSquareLipschitz : ℝ) ^ 2 / (b : ℝ) *
                  run.pointDisplacementMeanSquare (k - 1) := hone.2.2 hrefresh
          _ ≤ ((oracle.noiseLevel : ℝ) ^ 2 / (B : ℝ) +
                (oracle.meanSquareLipschitz : ℝ) ^ 2 / (b : ℝ) *
                  ∑ j ∈ Finset.Ico ((k - 1) - (k - 1) % Q) (k - 1),
                    run.pointDisplacementMeanSquare j) +
              (oracle.meanSquareLipschitz : ℝ) ^ 2 / (b : ℝ) *
                run.pointDisplacementMeanSquare (k - 1) := by
            exact add_le_add hprevious.2 le_rfl
          _ = (oracle.noiseLevel : ℝ) ^ 2 / (B : ℝ) +
                (oracle.meanSquareLipschitz : ℝ) ^ 2 / (b : ℝ) *
                  ∑ j ∈ Finset.Ico (k - k % Q) k, run.pointDisplacementMeanSquare j := by
            rw [hblockSum]
            ring

/-- Corollary 4.2 estimator invariant: a pathwise admissible corrected prefix
satisfies the accumulated SPIDER error bound with one corrected displacement
factor. -/
theorem accumulatedGradientErrorMeanSquare_le
    (run : StochasticRun h oracle P x₀ multiplier₀ params Q B b)
    (K : ℕ) (h_admissible : run.IsAdmissiblePrefix K) :
    ∑ k ∈ Finset.range K, run.gradientErrorMeanSquare k ≤
      (K : ℝ) * (oracle.noiseLevel : ℝ) ^ 2 / (B : ℝ) +
        ((Q : ℝ) * (oracle.meanSquareLipschitz : ℝ) ^ 2 *
            displacementFactor h params.delta ^ 2 / (b : ℝ)) *
          ∑ k ∈ Finset.range K, run.baseStepMeanSquare k := by
  -- Establish each last-refresh raw bound using actual corrected displacement.
  have hlastRefresh (k : ℕ) (hk : k < K) :
      run.gradientErrorMeanSquare k ≤
        (oracle.noiseLevel : ℝ) ^ 2 / (B : ℝ) +
          (oracle.meanSquareLipschitz : ℝ) ^ 2 / (b : ℝ) *
            ∑ j ∈ Finset.Ico (k - k % Q) k,
              run.pointDisplacementMeanSquare j := by
    have hraw := rawGradientErrorMeanSquare_le_lastRefresh run K k h_admissible
      (run.hasFreshBatches K)
      (fun j hj ↦ run.integrable_pointDisplacementSquare h_admissible hj) hk
    exact (gradientErrorMeanSquare_le_rawGradientErrorMeanSquare
      run K k h_admissible hk hraw.1).trans hraw.2
  -- The stable displacement/block interface performs the sole conversion to base steps.
  exact run.accumulatedGradientErrorMeanSquare_le_of_lastRefresh
    K h_admissible hlastRefresh

end LALM.Correction.StochasticRun

end
