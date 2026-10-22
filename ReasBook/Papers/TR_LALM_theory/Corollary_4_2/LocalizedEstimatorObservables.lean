/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@5bf5af722d85bd5c98368c41c4066124a15e8fd3:ReasBook/Papers/TR_LALM_theory/README.md (formalization contributor).
-/

module

public import TR_LALM_theory.Corollary_4_2.LocalizedEstimatorState
public import TR_LALM_theory.Corollary_4_2.StochasticEstimatorProbability

public section

open MeasureTheory
open scoped BigOperators NNReal

namespace LALM.Correction.StochasticRun.Localization

universe u v

variable {n m : ℕ}
variable {Ξ : Type u} [MeasurableSpace Ξ] {ν : Measure Ξ} [IsProbabilityMeasure ν]
variable {Ω : Type v} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
variable {f : EuclideanSpace ℝ (Fin n) → ℝ}
variable {c : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m)}
variable {x₀ : EuclideanSpace ℝ (Fin n)}
variable {multiplier₀ : EuclideanSpace ℝ (Fin m)}
variable {h : EqualityConstrained.Regularity f c}
variable {oracle : EqualityConstrained.StochasticOracle f h.region ν}
variable {params : Parameters h x₀ multiplier₀}
variable {Q B b : ℕ+} {confidence : ℝ}

/-- Helper for Corollary 4.2: the measurable sum-product equivalence computes
on the inactive branch. -/
private theorem measurableSumProdDistrib_apply_left
    {α β γ : Type*} [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSpace γ] (a : α) (c : γ) :
    MeasurableEquiv.sumProdDistrib α β γ (Sum.inl a, c) = Sum.inl (a, c) := by
  -- Expose the underlying ordinary equivalence at this single adapter boundary.
  rfl

/-- Helper for Corollary 4.2: the measurable sum-product equivalence computes
on the active branch. -/
private theorem measurableSumProdDistrib_apply_right
    {α β γ : Type*} [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSpace γ] (b : β) (c : γ) :
    MeasurableEquiv.sumProdDistrib α β γ (Sum.inr b, c) = Sum.inr (b, c) := by
  -- Expose the underlying ordinary equivalence at this single adapter boundary.
  rfl

/-- Helper for Corollary 4.2: the survival-masked squared raw SPIDER error at
one corrected iteration. -/
noncomputable def activeRawGradientErrorIntegrand
    (run : StochasticRun h oracle P x₀ multiplier₀ params Q B b)
    (X : Set (EuclideanSpace ℝ (Fin n))) (k : ℕ) : Ω → ℝ :=
  (survivalEvent run X k).indicator (fun omega ↦
    ‖SPIDER.rawEstimate oracle run.point run.sample Q B b k omega -
      gradient f (run.point k omega)‖ ^ 2)

/-- Helper for Corollary 4.2: on the survival event, the active raw-error
integrand is the squared raw SPIDER error. -/
theorem activeRawGradientErrorIntegrand_of_mem
    (run : StochasticRun h oracle P x₀ multiplier₀ params Q B b)
    (X : Set (EuclideanSpace ℝ (Fin n))) (k : ℕ) (omega : Ω)
    (homega : omega ∈ survivalEvent run X k) :
    activeRawGradientErrorIntegrand run X k omega =
      ‖SPIDER.rawEstimate oracle run.point run.sample Q B b k omega -
        gradient f (run.point k omega)‖ ^ 2 := by
  -- Select the active indicator branch at its definition owner.
  unfold activeRawGradientErrorIntegrand
  rw [Set.indicator_of_mem homega]

/-- Helper for Corollary 4.2: off the survival event, the active raw-error
integrand vanishes. -/
theorem activeRawGradientErrorIntegrand_of_not_mem
    (run : StochasticRun h oracle P x₀ multiplier₀ params Q B b)
    (X : Set (EuclideanSpace ℝ (Fin n))) (k : ℕ) (omega : Ω)
    (homega : omega ∉ survivalEvent run X k) :
    activeRawGradientErrorIntegrand run X k omega = 0 := by
  -- Select the inactive indicator branch at its definition owner.
  unfold activeRawGradientErrorIntegrand
  simp only [Set.indicator_of_notMem homega]

/-- Helper for Corollary 4.2: the expected survival-masked squared raw SPIDER
error at one corrected iteration. -/
noncomputable def activeRawGradientErrorMeanSquare
    (run : StochasticRun h oracle P x₀ multiplier₀ params Q B b)
    (X : Set (EuclideanSpace ℝ (Fin n))) (k : ℕ) : ℝ :=
  ∫ omega, activeRawGradientErrorIntegrand run X k omega ∂P

/-- Helper for Corollary 4.2: the active raw-error mean square is the integral
of its canonical masked integrand. -/
theorem activeRawGradientErrorMeanSquare_def
    (run : StochasticRun h oracle P x₀ multiplier₀ params Q B b)
    (X : Set (EuclideanSpace ℝ (Fin n))) (k : ℕ) :
    activeRawGradientErrorMeanSquare run X k =
      ∫ omega, activeRawGradientErrorIntegrand run X k omega ∂P := by
  -- Expose the defining integral once for downstream normalization.
  rfl

/-- Helper for Corollary 4.2: the survival-masked squared displacement between
two consecutive corrected points. -/
noncomputable def activePointDisplacementIntegrand
    (run : StochasticRun h oracle P x₀ multiplier₀ params Q B b)
    (X : Set (EuclideanSpace ℝ (Fin n))) (k : ℕ) : Ω → ℝ :=
  (survivalEvent run X k).indicator (fun omega ↦
    ‖run.point (k + 1) omega - run.point k omega‖ ^ 2)

/-- Helper for Corollary 4.2: on the survival event, the active displacement
integrand is the squared corrected point displacement. -/
theorem activePointDisplacementIntegrand_of_mem
    (run : StochasticRun h oracle P x₀ multiplier₀ params Q B b)
    (X : Set (EuclideanSpace ℝ (Fin n))) (k : ℕ) (omega : Ω)
    (homega : omega ∈ survivalEvent run X k) :
    activePointDisplacementIntegrand run X k omega =
      ‖run.point (k + 1) omega - run.point k omega‖ ^ 2 := by
  -- Select the active indicator branch at its definition owner.
  unfold activePointDisplacementIntegrand
  rw [Set.indicator_of_mem homega]

/-- Helper for Corollary 4.2: off the survival event, the active displacement
integrand vanishes. -/
theorem activePointDisplacementIntegrand_of_not_mem
    (run : StochasticRun h oracle P x₀ multiplier₀ params Q B b)
    (X : Set (EuclideanSpace ℝ (Fin n))) (k : ℕ) (omega : Ω)
    (homega : omega ∉ survivalEvent run X k) :
    activePointDisplacementIntegrand run X k omega = 0 := by
  -- Select the inactive indicator branch at its definition owner.
  unfold activePointDisplacementIntegrand
  simp only [Set.indicator_of_notMem homega]

/-- Helper for Corollary 4.2: the expected survival-masked squared corrected
point displacement. -/
noncomputable def activePointDisplacementMeanSquare
    (run : StochasticRun h oracle P x₀ multiplier₀ params Q B b)
    (X : Set (EuclideanSpace ℝ (Fin n))) (k : ℕ) : ℝ :=
  ∫ omega, activePointDisplacementIntegrand run X k omega ∂P

/-- Helper for Corollary 4.2: the active displacement mean square is the
integral of its canonical masked integrand. -/
theorem activePointDisplacementMeanSquare_def
    (run : StochasticRun h oracle P x₀ multiplier₀ params Q B b)
    (X : Set (EuclideanSpace ℝ (Fin n))) (k : ℕ) :
    activePointDisplacementMeanSquare run X k =
      ∫ omega, activePointDisplacementIntegrand run X k omega ∂P := by
  -- Expose the defining integral once for downstream normalization.
  rfl

/-- Helper for Corollary 4.2: the canonical raw-error observable is zero on an
inactive localized state and uses the explicit raw transition on an active state. -/
noncomputable def localizedRawGradientErrorObservable
    (h : EqualityConstrained.Regularity f c)
    (oracle : EqualityConstrained.StochasticOracle f h.region ν)
    (params : Parameters h x₀ multiplier₀) (Q B b : ℕ+)
    (X : Set (EuclideanSpace ℝ (Fin n))) (k : ℕ) :
    LocalizedPreBatchState h params X × (ℕ → Ξ) → ℝ :=
  Sum.elim
      (fun _ : Unit × (ℕ → Ξ) ↦ 0)
      (fun z : ActivePreBatchState h params X × (ℕ → Ξ) ↦
        ‖canonicalRawEstimateAt oracle Q B b k z.1.1 z.2 -
          h.objectiveGradientExtension z.1.1.1‖ ^ 2) ∘
    MeasurableEquiv.sumProdDistrib Unit (ActivePreBatchState h params X) (ℕ → Ξ)

/-- Helper for Corollary 4.2: the canonical localized raw-error observable is
measurable in the adapted state and fresh batch. -/
theorem measurable_localizedRawGradientErrorObservable
    (h : EqualityConstrained.Regularity f c)
    (oracle : EqualityConstrained.StochasticOracle f h.region ν)
    (params : Parameters h x₀ multiplier₀) (Q B b : ℕ+)
    (X : Set (EuclideanSpace ℝ (Fin n))) (k : ℕ) :
    Measurable (localizedRawGradientErrorObservable h oracle params Q B b X k) := by
  have hinput : Measurable (fun z :
      ActivePreBatchState h params X × (ℕ → Ξ) ↦ (z.1.1, z.2)) := by
    fun_prop
  have hpoint : Measurable (fun z :
      ActivePreBatchState h params X × (ℕ → Ξ) ↦ z.1.1.1) := by
    fun_prop
  have hactive : Measurable (fun z :
      ActivePreBatchState h params X × (ℕ → Ξ) ↦
        ‖canonicalRawEstimateAt oracle Q B b k z.1.1 z.2 -
          h.objectiveGradientExtension z.1.1.1‖ ^ 2) :=
    (((measurable_canonicalRawEstimateAt oracle Q B b k).comp hinput).sub
      (h.measurable_objectiveGradientExtension.comp hpoint)).norm.pow_const 2
  have hinactive : Measurable (fun _ : Unit × (ℕ → Ξ) ↦ (0 : ℝ)) :=
    measurable_const
  -- Distribute the batch across the sum and prove the two branches separately.
  unfold localizedRawGradientErrorObservable
  exact (hinactive.sumElim hactive).comp
    (MeasurableEquiv.sumProdDistrib Unit
      (ActivePreBatchState h params X) (ℕ → Ξ)).measurable

/-- Helper for Corollary 4.2: the localized raw-error observable computes by
matching on the inactive or active adapted state. -/
theorem localizedRawGradientErrorObservable_apply
    (s : LocalizedPreBatchState h params X) (batch : ℕ → Ξ) (k : ℕ) :
    localizedRawGradientErrorObservable h oracle params Q B b X k (s, batch) =
      match s with
      | Sum.inl _ => 0
      | Sum.inr active =>
          ‖canonicalRawEstimateAt oracle Q B b k active.1 batch -
            h.objectiveGradientExtension active.1.1‖ ^ 2 := by
  -- Push the batch through the measurable sum-product equivalence once.
  cases s with
  | inl inactive =>
      unfold localizedRawGradientErrorObservable
      simp only [Function.comp_apply, measurableSumProdDistrib_apply_left,
        Sum.elim_inl]
  | inr active =>
      unfold localizedRawGradientErrorObservable
      simp only [Function.comp_apply, measurableSumProdDistrib_apply_right,
        Sum.elim_inr]

/-- Helper for Corollary 4.2: at a refresh index, the active canonical
observable is the squared centered large-batch average. -/
theorem localizedRawGradientErrorObservable_of_refresh
    (s : ActivePreBatchState h params X) (batch : ℕ → Ξ) (k : ℕ)
    (hrefresh : k % Q = 0) :
    localizedRawGradientErrorObservable h oracle params Q B b X k
        (Sum.inr s, batch) =
      ‖(B : ℝ)⁻¹ • ∑ i ∈ Finset.range B,
        (oracle.sampleGradient s.1.1 (batch i) -
          h.objectiveGradientExtension s.1.1)‖ ^ 2 := by
  -- Select the active sum branch and center the refresh average once.
  unfold localizedRawGradientErrorObservable
  simp only [Function.comp_apply, measurableSumProdDistrib_apply_right, Sum.elim_inr]
  rw [canonicalRawEstimateAt_of_refresh oracle Q B b k s.1 batch hrefresh,
    ← EstimatorProbability.batchAverage_sub]

/-- Helper for Corollary 4.2: at an update index, the active canonical
observable is the preceding error plus one centered difference-batch innovation. -/
theorem localizedRawGradientErrorObservable_of_update
    (s : ActivePreBatchState h params X) (batch : ℕ → Ξ) (k : ℕ)
    (hupdate : k % Q ≠ 0) :
    localizedRawGradientErrorObservable h oracle params Q B b X k
        (Sum.inr s, batch) =
      ‖(s.1.2.2.2 - gradient f s.1.2.1) +
        (b : ℝ)⁻¹ • ∑ i ∈ Finset.range b,
          ((oracle.sampleGradient s.1.1 (batch i) -
            oracle.sampleGradient s.1.2.1 (batch i)) -
            (h.objectiveGradientExtension s.1.1 - gradient f s.1.2.1))‖ ^ 2 := by
  -- Normalize the update average and rearrange its deterministic centering term.
  unfold localizedRawGradientErrorObservable
  simp only [Function.comp_apply, measurableSumProdDistrib_apply_right, Sum.elim_inr]
  rw [canonicalRawEstimateAt_of_update oracle Q B b k s.1 batch hupdate,
    EstimatorProbability.batchAverage_sub]
  apply congrArg (fun z : EuclideanSpace ℝ (Fin n) ↦ ‖z‖ ^ 2)
  module

/-- Helper for Corollary 4.2: applying the canonical observable to the actual
localized state and fresh batch gives the survival-masked run error. -/
theorem localizedRawGradientErrorObservable_apply_run
    (run : StochasticRun h oracle P x₀ multiplier₀ params Q B b)
    (X : Set (EuclideanSpace ℝ (Fin n))) (initial_mem : x₀ ∈ X)
    (h_region : RegionCondition h oracle params confidence X)
    (k : ℕ) (omega : Ω) :
    localizedRawGradientErrorObservable h oracle params Q B b X k
        (localizedPreBatchState run X initial_mem h_region k omega,
          fun i ↦ run.sample k i omega) =
      activeRawGradientErrorIntegrand run X k omega := by
  -- Split on survival, then expose only the actual-state projection equations.
  classical
  by_cases homega : omega ∈ survivalEvent run X k
  · have hcurrentX : run.point k omega ∈ X :=
      currentPoint_mem_of_survival run X initial_mem k omega homega
    have hcurrentRegion : run.point k omega ∈ h.region :=
      h_region.thickening_subset
        (Metric.self_subset_cthickening X hcurrentX)
    simp only [localizedRawGradientErrorObservable, Function.comp_apply,
      localizedPreBatchState_of_mem run X initial_mem h_region k omega homega,
      measurableSumProdDistrib_apply_right, Sum.elim_inr,
      activeRawGradientErrorIntegrand,
      Set.indicator_of_mem homega]
    rw [actualActivePreBatchState_coe, canonicalRawEstimateAt_apply_samples,
      actualPreBatchData_current, h.objectiveGradientExtension_eq hcurrentRegion]
  · simp only [localizedRawGradientErrorObservable, Function.comp_apply,
      localizedPreBatchState_of_not_mem run X initial_mem h_region k omega homega,
      measurableSumProdDistrib_apply_left, Sum.elim_inl,
      activeRawGradientErrorIntegrand,
      Set.indicator_of_notMem homega]

/-- Helper for Corollary 4.2: the statewise update bound is zero when inactive
and otherwise adds the corrected displacement contribution to the preceding error. -/
noncomputable def localizedUpdateConditionalBound
    (h : EqualityConstrained.Regularity f c)
    (oracle : EqualityConstrained.StochasticOracle f h.region ν)
    (params : Parameters h x₀ multiplier₀) (b : ℕ+)
    (X : Set (EuclideanSpace ℝ (Fin n))) :
    LocalizedPreBatchState h params X → ℝ :=
  Sum.elim (fun _ : Unit ↦ 0) (fun s : ActivePreBatchState h params X ↦
    ‖s.1.2.2.2 - gradient f s.1.2.1‖ ^ 2 +
      (oracle.meanSquareLipschitz : ℝ) ^ 2 / (b : ℝ) *
        ‖s.1.1 - s.1.2.1‖ ^ 2)

/-- Helper for Corollary 4.2: the localized update bound computes by matching
on the inactive or active adapted state. -/
theorem localizedUpdateConditionalBound_apply
    (s : LocalizedPreBatchState h params X) :
    localizedUpdateConditionalBound h oracle params b X s =
      match s with
      | Sum.inl _ => 0
      | Sum.inr active =>
          ‖active.1.2.2.2 - gradient f active.1.2.1‖ ^ 2 +
            (oracle.meanSquareLipschitz : ℝ) ^ 2 / (b : ℝ) *
              ‖active.1.1 - active.1.2.1‖ ^ 2 := by
  -- Expose the sum eliminator without unfolding it in downstream proofs.
  cases s with
  | inl inactive =>
      unfold localizedUpdateConditionalBound
      simp only [Sum.elim_inl]
  | inr active =>
      unfold localizedUpdateConditionalBound
      simp only [Sum.elim_inr]

/-- Helper for Corollary 4.2: the localized statewise update bound is
nonnegative. -/
theorem localizedUpdateConditionalBound_nonneg
    (s : LocalizedPreBatchState h params X) :
    0 ≤ localizedUpdateConditionalBound h oracle params b X s := by
  -- The inactive branch is zero, while both terms in the active branch are nonnegative.
  cases s with
  | inl inactive =>
      unfold localizedUpdateConditionalBound
      simp only [Sum.elim_inl]
      exact le_rfl
  | inr active =>
      unfold localizedUpdateConditionalBound
      simp only [Sum.elim_inr]
      positivity

/-- Helper for Corollary 4.2: the localized statewise update bound is
measurable. -/
theorem measurable_localizedUpdateConditionalBound
    (h : EqualityConstrained.Regularity f c)
    (oracle : EqualityConstrained.StochasticOracle f h.region ν)
    (params : Parameters h x₀ multiplier₀) (b : ℕ+)
    (X : Set (EuclideanSpace ℝ (Fin n))) :
    Measurable (localizedUpdateConditionalBound h oracle params b X) := by
  have hcurrent : Measurable (fun s : ActivePreBatchState h params X ↦ s.1.1) := by
    fun_prop
  have hprevious : Measurable (fun s : ActivePreBatchState h params X ↦ s.1.2.1) := by
    fun_prop
  have hraw : Measurable (fun s : ActivePreBatchState h params X ↦ s.1.2.2.2) := by
    fun_prop
  have hgradientPrevious : Measurable (fun s : ActivePreBatchState h params X ↦
      gradient f s.1.2.1) := by
    have hgradientExtension : Measurable
        (fun s : ActivePreBatchState h params X ↦
          h.objectiveGradientExtension s.1.2.1) :=
      h.measurable_objectiveGradientExtension.comp hprevious
    have hgradientEq :
        (fun s : ActivePreBatchState h params X ↦ gradient f s.1.2.1) =
          fun s : ActivePreBatchState h params X ↦
            h.objectiveGradientExtension s.1.2.1 := by
      funext s
      exact (h.objectiveGradientExtension_eq s.previous_mem_region).symm
    rw [hgradientEq]
    exact hgradientExtension
  have hactive : Measurable (fun s : ActivePreBatchState h params X ↦
      ‖s.1.2.2.2 - gradient f s.1.2.1‖ ^ 2 +
        (oracle.meanSquareLipschitz : ℝ) ^ 2 / (b : ℝ) *
          ‖s.1.1 - s.1.2.1‖ ^ 2) :=
    ((hraw.sub hgradientPrevious).norm.pow_const 2).add
      (((hcurrent.sub hprevious).norm.pow_const 2).const_mul
        ((oracle.meanSquareLipschitz : ℝ) ^ 2 / (b : ℝ)))
  -- The sum eliminator combines the constant inactive branch and active formula.
  unfold localizedUpdateConditionalBound
  exact measurable_const.sumElim hactive

/-- Helper for Corollary 4.2: on the actual state at a positive iteration,
the statewise update bound is the current survival mask applied to the
preceding raw error and corrected point displacement. -/
theorem localizedUpdateConditionalBound_apply_run
    (run : StochasticRun h oracle P x₀ multiplier₀ params Q B b)
    (X : Set (EuclideanSpace ℝ (Fin n))) (initial_mem : x₀ ∈ X)
    (h_region : RegionCondition h oracle params confidence X)
    (k : ℕ) (hk : 0 < k) (omega : Ω) :
    localizedUpdateConditionalBound h oracle params b X
        (localizedPreBatchState run X initial_mem h_region k omega) =
      (survivalEvent run X k).indicator (fun omega' ↦
        ‖SPIDER.rawEstimate oracle run.point run.sample Q B b (k - 1) omega' -
          gradient f (run.point (k - 1) omega')‖ ^ 2 +
        (oracle.meanSquareLipschitz : ℝ) ^ 2 / (b : ℝ) *
          ‖run.point k omega' - run.point (k - 1) omega'‖ ^ 2) omega := by
  -- Survival selects the actual active package; its four projections give the formula.
  classical
  by_cases homega : omega ∈ survivalEvent run X k
  · simp only [localizedUpdateConditionalBound,
      localizedPreBatchState_of_mem run X initial_mem h_region k omega homega,
      Sum.elim_inr, Set.indicator_of_mem homega]
    rw [actualActivePreBatchState_coe, actualPreBatchData_rawEstimate,
      if_neg (ne_of_gt hk), actualPreBatchData_previous,
      actualPreBatchData_current]
  · simp only [localizedUpdateConditionalBound,
      localizedPreBatchState_of_not_mem run X initial_mem h_region k omega homega,
      Sum.elim_inl, Set.indicator_of_notMem homega]

/-- Helper for Corollary 4.2: on survival, one corrected point-displacement
square is bounded by the corrected displacement factor times the base-step square. -/
theorem pointDisplacementSquare_le_baseStep_of_survival
    (run : StochasticRun h oracle P x₀ multiplier₀ params Q B b)
    (X : Set (EuclideanSpace ℝ (Fin n))) (initial_mem : x₀ ∈ X)
    (h_region : RegionCondition h oracle params confidence X)
    (k : ℕ) (omega : Ω) (homega : omega ∈ survivalEvent run X k) :
    ‖run.point (k + 1) omega - run.point k omega‖ ^ 2 ≤
      displacementFactor h params.delta ^ 2 * ‖run.baseStep k omega‖ ^ 2 := by
  have hadmissible := preExitAdmissible run X initial_mem h_region omega k homega
  have hstep := preExitBaseStepNorm_le run X initial_mem h_region omega k homega
  have hdisplacement := displacement_le h params.delta
    (run.point k omega) (run.baseStep k omega) hadmissible hstep
  rw [← run.point_succ k omega] at hdisplacement
  have hfactorNonneg : 0 ≤ displacementFactor h params.delta := by
    rw [displacementFactor_def]
    have hstepConstantNonneg : 0 ≤ stepConstant h := by
      rw [stepConstant_def]
      positivity
    exact add_nonneg (by norm_num)
      (mul_nonneg hstepConstantNonneg (NNReal.coe_nonneg params.delta))
  have hrightNonneg :
      0 ≤ displacementFactor h params.delta * ‖run.baseStep k omega‖ :=
    mul_nonneg hfactorNonneg (norm_nonneg _)
  -- Square the pathwise displacement comparison and normalize the product.
  calc
    ‖run.point (k + 1) omega - run.point k omega‖ ^ 2 ≤
        (displacementFactor h params.delta * ‖run.baseStep k omega‖) ^ 2 :=
      (sq_le_sq₀ (norm_nonneg _) hrightNonneg).2 hdisplacement
    _ = displacementFactor h params.delta ^ 2 * ‖run.baseStep k omega‖ ^ 2 := by
      ring

/-- Helper for Corollary 4.2: the survival-masked corrected point-displacement
square is integrable. -/
theorem integrable_activePointDisplacementIntegrand
    (run : StochasticRun h oracle P x₀ multiplier₀ params Q B b)
    (X : Set (EuclideanSpace ℝ (Fin n))) (hX : MeasurableSet X)
    (initial_mem : x₀ ∈ X)
    (h_region : RegionCondition h oracle params confidence X) (k : ℕ) :
    Integrable (activePointDisplacementIntegrand run X k) P := by
  have hsurvival := nullMeasurableSet_survivalEvent run X hX k
  have hbase := integrableOn_baseStepSquare_preExit
    run X hX initial_mem h_region k
  have hmajorant : Integrable (fun omega ↦
      displacementFactor h params.delta ^ 2 * ‖run.baseStep k omega‖ ^ 2)
      (P.restrict (survivalEvent run X k)) :=
    hbase.const_mul (displacementFactor h params.delta ^ 2)
  have hmeasurable : AEStronglyMeasurable (fun omega ↦
      ‖run.point (k + 1) omega - run.point k omega‖ ^ 2)
      (P.restrict (survivalEvent run X k)) :=
    (((run.aemeasurable_point (k + 1)).sub
      (run.aemeasurable_point k)).norm.pow_const 2).aestronglyMeasurable.restrict
  have hrestricted : IntegrableOn (fun omega ↦
      ‖run.point (k + 1) omega - run.point k omega‖ ^ 2)
      (survivalEvent run X k) P := by
    refine Integrable.mono' hmajorant hmeasurable ?_
    filter_upwards [ae_restrict_mem₀ hsurvival] with omega homega
    have hbound := pointDisplacementSquare_le_baseStep_of_survival
      run X initial_mem h_region k omega homega
    have hleftNonneg :
        0 ≤ ‖run.point (k + 1) omega - run.point k omega‖ ^ 2 := sq_nonneg _
    have hrightNonneg :
        0 ≤ displacementFactor h params.delta ^ 2 * ‖run.baseStep k omega‖ ^ 2 :=
      mul_nonneg (sq_nonneg _) (sq_nonneg _)
    simpa only [Real.norm_of_nonneg hleftNonneg,
      Real.norm_of_nonneg hrightNonneg] using hbound
  -- Convert restricted integrability to the indicator spelling used by the moment.
  unfold activePointDisplacementIntegrand
  exact hrestricted.integrable_indicator₀ hsurvival

/-- Helper for Corollary 4.2: every survival-masked corrected displacement
moment is nonnegative. -/
theorem activePointDisplacementMeanSquare_nonneg
    (run : StochasticRun h oracle P x₀ multiplier₀ params Q B b)
    (X : Set (EuclideanSpace ℝ (Fin n))) (k : ℕ) :
    0 ≤ activePointDisplacementMeanSquare run X k := by
  -- The masked integrand is either zero or a squared norm.
  rw [activePointDisplacementMeanSquare]
  exact integral_nonneg fun omega ↦ by
    unfold activePointDisplacementIntegrand
    by_cases homega : omega ∈ survivalEvent run X k
    · simp only [Set.indicator_of_mem homega]
      positivity
    · simp only [Set.indicator_of_notMem homega, Pi.zero_apply]
      exact le_rfl

/-- Helper for Corollary 4.2: the active corrected displacement moment is
bounded by the corresponding stopped base-step moment. -/
theorem activePointDisplacementMeanSquare_le_baseStep
    (run : StochasticRun h oracle P x₀ multiplier₀ params Q B b)
    (X : Set (EuclideanSpace ℝ (Fin n))) (hX : MeasurableSet X)
    (initial_mem : x₀ ∈ X)
    (h_region : RegionCondition h oracle params confidence X) (k : ℕ) :
    activePointDisplacementMeanSquare run X k ≤
      displacementFactor h params.delta ^ 2 *
        ∫ omega in survivalEvent run X k, ‖run.baseStep k omega‖ ^ 2 ∂P := by
  have hsurvival := nullMeasurableSet_survivalEvent run X hX k
  have hbase := integrableOn_baseStepSquare_preExit
    run X hX initial_mem h_region k
  have hmajorant : Integrable (fun omega ↦
      displacementFactor h params.delta ^ 2 * ‖run.baseStep k omega‖ ^ 2)
      (P.restrict (survivalEvent run X k)) :=
    hbase.const_mul (displacementFactor h params.delta ^ 2)
  have hbound : ∀ᵐ omega ∂P.restrict (survivalEvent run X k),
      ‖run.point (k + 1) omega - run.point k omega‖ ^ 2 ≤
        displacementFactor h params.delta ^ 2 * ‖run.baseStep k omega‖ ^ 2 := by
    filter_upwards [ae_restrict_mem₀ hsurvival] with omega homega
    exact pointDisplacementSquare_le_baseStep_of_survival
      run X initial_mem h_region k omega homega
  -- Integrate the pathwise bridge on the survival event and pull out its constant.
  rw [activePointDisplacementMeanSquare, activePointDisplacementIntegrand,
    integral_indicator₀ hsurvival]
  calc
    (∫ omega in survivalEvent run X k,
        ‖run.point (k + 1) omega - run.point k omega‖ ^ 2 ∂P) ≤
        ∫ omega in survivalEvent run X k,
          displacementFactor h params.delta ^ 2 * ‖run.baseStep k omega‖ ^ 2 ∂P :=
      integral_mono_of_nonneg
        (Filter.Eventually.of_forall fun omega ↦ sq_nonneg _)
        hmajorant hbound
    _ = displacementFactor h params.delta ^ 2 *
        ∫ omega in survivalEvent run X k, ‖run.baseStep k omega‖ ^ 2 ∂P := by
      rw [integral_const_mul]

end LALM.Correction.StochasticRun.Localization

end
