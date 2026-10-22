/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@5bf5af722d85bd5c98368c41c4066124a15e8fd3:ReasBook/Papers/TR_LALM_theory/README.md (formalization contributor).
-/

module

public import TR_LALM_theory.Corollary_4_2.LocalizedEstimatorTransition

public section

open MeasureTheory
open scoped BigOperators NNReal

namespace LALM.Correction.StochasticRun.Localization

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
variable {Q B b : ℕ+} {confidence : ℝ}

/-- Helper for Corollary 4.2: the numerical state fixed before a localized
batch stores the current point, preceding point, multiplier, and preceding raw estimate. -/
abbrev PreBatchData :=
  EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) ×
    EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin n)

/-- Helper for Corollary 4.2: an active numerical state carries exactly the
localization and multiplier bounds needed by the corrected transition. -/
def ActivePreBatchInvariant
    (h : EqualityConstrained.Regularity f c)
    (params : Parameters h x₀ multiplier₀)
    (X : Set (EuclideanSpace ℝ (Fin n)))
    (s : PreBatchData (n := n) (m := m)) : Prop :=
  s.1 ∈ X ∧ s.2.1 ∈ h.region ∧
    ‖s.2.2.1‖ ≤ params.multiplierBound ∧
      ‖s.2.2.1 + (params.rho : ℝ) • c s.1‖ ≤
        3 * params.multiplierBound

/-- Helper for Corollary 4.2: the active pre-batch state is numerical data
bundled with its corrected localization invariant. -/
abbrev ActivePreBatchState
    (h : EqualityConstrained.Regularity f c)
    (params : Parameters h x₀ multiplier₀)
    (X : Set (EuclideanSpace ℝ (Fin n))) :=
  {s : PreBatchData (n := n) (m := m) // ActivePreBatchInvariant h params X s}

/-- Helper for Corollary 4.2: a localized state is either inactive or carries
an active pre-batch state. -/
abbrev LocalizedPreBatchState
    (h : EqualityConstrained.Regularity f c)
    (params : Parameters h x₀ multiplier₀)
    (X : Set (EuclideanSpace ℝ (Fin n))) :=
  Unit ⊕ ActivePreBatchState h params X

namespace ActivePreBatchState

/-- Helper for Corollary 4.2: an active state exposes current localization
membership. -/
theorem current_mem
    {X : Set (EuclideanSpace ℝ (Fin n))}
    (s : ActivePreBatchState h params X) : s.1.1 ∈ X := by
  -- Project the first clause of the bundled invariant.
  exact s.2.1

/-- Helper for Corollary 4.2: an active state's preceding point lies in the
regularity region. -/
theorem previous_mem_region
    {X : Set (EuclideanSpace ℝ (Fin n))}
    (s : ActivePreBatchState h params X) : s.1.2.1 ∈ h.region := by
  -- Project the second clause of the bundled invariant.
  exact s.2.2.1

/-- Helper for Corollary 4.2: an active state exposes its multiplier bound. -/
theorem norm_multiplier_le
    {X : Set (EuclideanSpace ℝ (Fin n))}
    (s : ActivePreBatchState h params X) :
    ‖s.1.2.2.1‖ ≤ params.multiplierBound := by
  -- Project the third clause of the bundled invariant.
  exact s.2.2.2.1

/-- Helper for Corollary 4.2: an active state exposes the effective-multiplier
bound needed by the canonical base-step estimate. -/
theorem norm_effectiveMultiplier_le
    {X : Set (EuclideanSpace ℝ (Fin n))}
    (s : ActivePreBatchState h params X) :
    ‖s.1.2.2.1 + (params.rho : ℝ) • c s.1.1‖ ≤
      3 * params.multiplierBound := by
  -- Project the final clause of the bundled invariant.
  exact s.2.2.2.2

end ActivePreBatchState

/-- Helper for Corollary 4.2: a fresh batch and numerical pre-batch state
determine the next raw SPIDER estimate. -/
noncomputable def canonicalRawEstimateAt
    (oracle : EqualityConstrained.StochasticOracle f h.region ν)
    (Q B b : ℕ+) (k : ℕ)
    (s : PreBatchData (n := n) (m := m)) (batch : ℕ → Ξ) :
    EuclideanSpace ℝ (Fin n) :=
  if k % Q = 0 then
    (B : ℝ)⁻¹ • ∑ i ∈ Finset.range B,
      oracle.sampleGradient s.1 (batch i)
  else
    s.2.2.2 + (b : ℝ)⁻¹ • ∑ i ∈ Finset.range b,
      (oracle.sampleGradient s.1 (batch i) -
        oracle.sampleGradient s.2.1 (batch i))

/-- Helper for Corollary 4.2: at a refresh index, the explicit transition is
the fresh large-batch average. -/
theorem canonicalRawEstimateAt_of_refresh
    (oracle : EqualityConstrained.StochasticOracle f h.region ν)
    (Q B b : ℕ+) (k : ℕ) (s : PreBatchData (n := n) (m := m))
    (batch : ℕ → Ξ) (hrefresh : k % Q = 0) :
    canonicalRawEstimateAt oracle Q B b k s batch =
      (B : ℝ)⁻¹ • ∑ i ∈ Finset.range B,
        oracle.sampleGradient s.1 (batch i) := by
  -- Select the refresh branch of the owner definition once.
  unfold canonicalRawEstimateAt
  rw [if_pos hrefresh]

/-- Helper for Corollary 4.2: away from refresh indices, the explicit
transition adds the fresh difference-batch average to the stored raw estimate. -/
theorem canonicalRawEstimateAt_of_update
    (oracle : EqualityConstrained.StochasticOracle f h.region ν)
    (Q B b : ℕ+) (k : ℕ) (s : PreBatchData (n := n) (m := m))
    (batch : ℕ → Ξ) (hnonrefresh : k % Q ≠ 0) :
    canonicalRawEstimateAt oracle Q B b k s batch =
      s.2.2.2 + (b : ℝ)⁻¹ • ∑ i ∈ Finset.range b,
        (oracle.sampleGradient s.1 (batch i) -
          oracle.sampleGradient s.2.1 (batch i)) := by
  -- Select the update branch of the owner definition once.
  unfold canonicalRawEstimateAt
  rw [if_neg hnonrefresh]

/-- Helper for Corollary 4.2: the explicit raw-estimate transition is
measurable in the numerical state and fresh batch. -/
theorem measurable_canonicalRawEstimateAt
    (oracle : EqualityConstrained.StochasticOracle f h.region ν)
    (Q B b : ℕ+) (k : ℕ) :
    Measurable (fun z : PreBatchData (n := n) (m := m) × (ℕ → Ξ) ↦
      canonicalRawEstimateAt oracle Q B b k z.1 z.2) := by
  have hpoint : Measurable (fun z :
      PreBatchData (n := n) (m := m) × (ℕ → Ξ) ↦ z.1.1) := by
    fun_prop
  have hpreviousPoint : Measurable (fun z :
      PreBatchData (n := n) (m := m) × (ℕ → Ξ) ↦ z.1.2.1) := by
    fun_prop
  have hpreviousRaw : Measurable (fun z :
      PreBatchData (n := n) (m := m) × (ℕ → Ξ) ↦ z.1.2.2.2) := by
    fun_prop
  have hsample (i : ℕ) : Measurable (fun z :
      PreBatchData (n := n) (m := m) × (ℕ → Ξ) ↦ z.2 i) :=
    (measurable_pi_apply i).comp measurable_snd
  -- Split only the deterministic refresh schedule; each branch is a finite sum.
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

/-- Helper for Corollary 4.2: radial clipping is measurable on the
finite-dimensional gradient space. -/
private lemma measurable_spiderClip (G : ℝ≥0) :
    Measurable (SPIDER.clip G :
      EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) := by
  -- Both formulas are measurable and the norm comparison is a measurable set.
  unfold SPIDER.clip
  apply Measurable.ite
  · exact measurableSet_le continuous_norm.measurable measurable_const
  · exact measurable_id
  · exact (measurable_const.div continuous_norm.measurable).smul measurable_id

/-- Helper for Corollary 4.2: the clipped estimate attached to explicit
pre-batch data. -/
noncomputable def canonicalClippedEstimateAt
    (h : EqualityConstrained.Regularity f c)
    (oracle : EqualityConstrained.StochasticOracle f h.region ν)
    (Q B b : ℕ+) (k : ℕ)
    (z : PreBatchData (n := n) (m := m) × (ℕ → Ξ)) :
    EuclideanSpace ℝ (Fin n) :=
  SPIDER.clip h.gradientBound (canonicalRawEstimateAt oracle Q B b k z.1 z.2)

/-- Helper for Corollary 4.2: the explicit clipped estimate is measurable. -/
theorem measurable_canonicalClippedEstimateAt
    (h : EqualityConstrained.Regularity f c)
    (oracle : EqualityConstrained.StochasticOracle f h.region ν)
    (Q B b : ℕ+) (k : ℕ) :
    Measurable (canonicalClippedEstimateAt h oracle Q B b k) := by
  -- Compose measurable clipping with the explicit raw-estimate transition.
  unfold canonicalClippedEstimateAt
  exact (measurable_spiderClip h.gradientBound).comp
    (measurable_canonicalRawEstimateAt oracle Q B b k)

/-- Helper for Corollary 4.2: the canonical model input groups the current
point, clipped estimate, and multiplier. -/
noncomputable def canonicalModelInputAt
    (h : EqualityConstrained.Regularity f c)
    (oracle : EqualityConstrained.StochasticOracle f h.region ν)
    (Q B b : ℕ+) (k : ℕ)
    (z : PreBatchData (n := n) (m := m) × (ℕ → Ξ)) :
    EuclideanSpace ℝ (Fin n) ×
      (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin m)) :=
  (z.1.1, canonicalClippedEstimateAt h oracle Q B b k z, z.1.2.2.1)

/-- Helper for Corollary 4.2: the grouped canonical model input is measurable. -/
theorem measurable_canonicalModelInputAt
    (h : EqualityConstrained.Regularity f c)
    (oracle : EqualityConstrained.StochasticOracle f h.region ν)
    (Q B b : ℕ+) (k : ℕ) :
    Measurable (canonicalModelInputAt h oracle Q B b k) := by
  have hpoint : Measurable (fun z :
      PreBatchData (n := n) (m := m) × (ℕ → Ξ) ↦ z.1.1) := by
    fun_prop
  have hmultiplier : Measurable (fun z :
      PreBatchData (n := n) (m := m) × (ℕ → Ξ) ↦ z.1.2.2.1) := by
    fun_prop
  -- Assemble the three fields in the solver's expected product order.
  unfold canonicalModelInputAt
  exact hpoint.prodMk
    ((measurable_canonicalClippedEstimateAt h oracle Q B b k).prodMk hmultiplier)

/-- Helper for Corollary 4.2: the canonical base-step component solves the
model determined by explicit pre-batch data. -/
noncomputable def canonicalBaseStepAt
    (h : EqualityConstrained.Regularity f c)
    (oracle : EqualityConstrained.StochasticOracle f h.region ν)
    (params : Parameters h x₀ multiplier₀) (Q B b : ℕ+) (k : ℕ) :
    PreBatchData (n := n) (m := m) × (ℕ → Ξ) →
      EuclideanSpace ℝ (Fin n) :=
  (fun input : EuclideanSpace ℝ (Fin n) ×
      (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin m)) ↦
    canonicalBaseStep c params.rho params.beta input.1 input.2.1 input.2.2) ∘
      canonicalModelInputAt h oracle Q B b k

/-- Helper for Corollary 4.2: forget the active invariant while retaining the
fresh batch paired with its numerical state. -/
def activeNumericalInput
    {X : Set (EuclideanSpace ℝ (Fin n))}
    (z : ActivePreBatchState h params X × (ℕ → Ξ)) :
    PreBatchData (n := n) (m := m) × (ℕ → Ξ) :=
  (z.1.1, z.2)

/-- Helper for Corollary 4.2: forgetting the active invariant is measurable. -/
theorem measurable_activeNumericalInput
    {X : Set (EuclideanSpace ℝ (Fin n))} :
    Measurable (activeNumericalInput
      (h := h) (params := params) (Ξ := Ξ) (X := X)) := by
  -- Subtype coercion and the fresh-batch projection are both measurable.
  exact (measurable_subtype_coe.comp measurable_fst).prodMk measurable_snd

/-- Helper for Corollary 4.2: the active canonical base step uses the
numerical state underlying the invariant subtype. -/
noncomputable def canonicalActiveBaseStepAt
    (h : EqualityConstrained.Regularity f c)
    (oracle : EqualityConstrained.StochasticOracle f h.region ν)
    (params : Parameters h x₀ multiplier₀) (Q B b : ℕ+)
    {X : Set (EuclideanSpace ℝ (Fin n))} (k : ℕ) :
    ActivePreBatchState h params X × (ℕ → Ξ) →
      EuclideanSpace ℝ (Fin n) :=
  canonicalBaseStepAt h oracle params Q B b k ∘ activeNumericalInput

/-- Helper for Corollary 4.2: the current point of an active canonical state
lies in the regularity region. -/
theorem canonicalActivePoint_mem_region
    (h_region : RegionCondition h oracle params confidence X)
    (z : ActivePreBatchState h params X × (ℕ → Ξ)) :
    z.1.1.1 ∈ h.region :=
  h_region.thickening_subset
    (Metric.self_subset_cthickening X z.1.current_mem)

/-- Helper for Corollary 4.2: an active model input belongs to the local
base-step regularity domain. -/
theorem canonicalActiveModelInput_mem_baseStepRegularityDomain
    (h_region : RegionCondition h oracle params confidence X)
    (k : ℕ) (z : ActivePreBatchState h params X × (ℕ → Ξ)) :
    canonicalModelInputAt h oracle Q B b k (activeNumericalInput z) ∈
      baseStepRegularityDomain h := by
  apply (mem_baseStepRegularityDomain_iff h _).2
  exact canonicalActivePoint_mem_region h_region z

/-- Helper for Corollary 4.2: package an active model input in the local
base-step regularity domain. -/
noncomputable def canonicalActiveRegularModelInput
    (h_region : RegionCondition h oracle params confidence X) (k : ℕ)
    (z : ActivePreBatchState h params X × (ℕ → Ξ)) :
    baseStepRegularityDomain h :=
  ⟨canonicalModelInputAt h oracle Q B b k (activeNumericalInput z),
    canonicalActiveModelInput_mem_baseStepRegularityDomain h_region k z⟩

/-- Helper for Corollary 4.2: the active canonical base step is measurable. -/
theorem measurable_canonicalActiveBaseStepAt
    (h_region : RegionCondition h oracle params confidence X) (k : ℕ) :
    Measurable
      (canonicalActiveBaseStepAt h oracle params Q B b (X := X) k) := by
  have hinput : Measurable
      (canonicalActiveRegularModelInput
        (Q := Q) (B := B) (b := b) h_region k) :=
    ((measurable_canonicalModelInputAt h oracle Q B b k).comp
      measurable_activeNumericalInput).subtype_mk
  let solver := Set.restrict (baseStepRegularityDomain h)
    (fun input ↦ canonicalBaseStep c params.rho params.beta
      input.1 input.2.1 input.2.2)
  have hsolver : Continuous solver :=
    (continuousOn_canonicalBaseStep h params.rho params.beta
      params.spec.1.2.2.1 params.spec.1.2.1).restrict
  change Measurable
    (solver ∘ canonicalActiveRegularModelInput
      (Q := Q) (B := B) (b := b) h_region k)
  exact hsolver.measurable.comp hinput

/-- Helper for Corollary 4.2: every active canonical base step satisfies the
localization radius bound. -/
theorem norm_canonicalActiveBaseStepAt_le
    (h_region : RegionCondition h oracle params confidence X)
    (k : ℕ) (z : ActivePreBatchState h params X × (ℕ → Ξ)) :
    ‖canonicalActiveBaseStepAt h oracle params Q B b k z‖ ≤ params.delta := by
  have hxRegion : z.1.1.1 ∈ h.region :=
    canonicalActivePoint_mem_region h_region z
  have hgradient :
      ‖canonicalClippedEstimateAt h oracle Q B b k
        (activeNumericalInput z)‖ ≤ h.gradientBound := by
    unfold canonicalClippedEstimateAt
    exact SPIDER.norm_clip_le h.gradientBound _
  -- Apply the state-free canonical bound with the stored effective multiplier.
  simpa only [canonicalActiveBaseStepAt, canonicalBaseStepAt,
    canonicalModelInputAt, Function.comp_apply, activeNumericalInput] using
      norm_canonicalBaseStep_le h params z.1.1.1
        (canonicalClippedEstimateAt h oracle Q B b k (activeNumericalInput z))
        z.1.1.2.2.1 hxRegion hgradient z.1.norm_effectiveMultiplier_le

/-- Helper for Corollary 4.2: an active canonical transition is admissible. -/
theorem canonicalActiveBaseStepAt_isAdmissible
    (h_region : RegionCondition h oracle params confidence X)
    (k : ℕ) (z : ActivePreBatchState h params X × (ℕ → Ξ)) :
    IsAdmissible h z.1.1.1
      (canonicalActiveBaseStepAt h oracle params Q B b k z) := by
  -- Region membership and the canonical radius bound invoke the localization geometry API.
  exact h_region.isAdmissible_of_mem_of_norm_le z.1.1.1
    (canonicalActiveBaseStepAt h oracle params Q B b k z)
    z.1.current_mem (norm_canonicalActiveBaseStepAt_le h_region k z)

/-- Helper for Corollary 4.2: the active canonical trial point lies in the
regularity region. -/
theorem canonicalActiveTrialPoint_mem_region
    (h_region : RegionCondition h oracle params confidence X)
    (k : ℕ) (z : ActivePreBatchState h params X × (ℕ → Ξ)) :
    trialPoint z.1.1.1 (canonicalActiveBaseStepAt h oracle params Q B b k z) ∈
      h.region := by
  -- Project trial-point membership from corrected admissibility.
  exact trialPoint_mem_region h z.1.1.1
    (canonicalActiveBaseStepAt h oracle params Q B b k z)
    (canonicalActiveBaseStepAt_isAdmissible h_region k z)

/-- Helper for Corollary 4.2: the corrected point produced by an active
canonical transition lies in the regularity region. -/
theorem canonicalActiveNextPoint_mem_region
    (h_region : RegionCondition h oracle params confidence X)
    (k : ℕ) (z : ActivePreBatchState h params X × (ℕ → Ξ)) :
    nextPoint c z.1.1.1
        (canonicalActiveBaseStepAt h oracle params Q B b k z) ∈ h.region := by
  exact nextPoint_mem_region h z.1.1.1
    (canonicalActiveBaseStepAt h oracle params Q B b k z)
    (canonicalActiveBaseStepAt_isAdmissible h_region k z)

/-- Helper for Corollary 4.2: active canonical point--step data belong to the
domain where both inputs needed by the corrected transition are regular. -/
theorem canonicalActiveTrialData_mem_stepRegularityDomain
    (h_region : RegionCondition h oracle params confidence X)
    (k : ℕ) (z : ActivePreBatchState h params X × (ℕ → Ξ)) :
    (z.1.1.1, canonicalActiveBaseStepAt h oracle params Q B b k z) ∈
      stepRegularityDomain h := by
  apply (mem_stepRegularityDomain_iff h _).2
  exact ⟨canonicalActivePoint_mem_region h_region z,
    canonicalActiveTrialPoint_mem_region h_region k z⟩

/-- Helper for Corollary 4.2: package the active point and base step in the
domain on which the corrected point map is continuous. -/
noncomputable def canonicalActiveTrialData
    (h_region : RegionCondition h oracle params confidence X) (k : ℕ)
    (z : ActivePreBatchState h params X × (ℕ → Ξ)) :
    {xp : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) //
      xp ∈ stepRegularityDomain h} :=
  ⟨(z.1.1.1, canonicalActiveBaseStepAt h oracle params Q B b k z),
    canonicalActiveTrialData_mem_stepRegularityDomain h_region k z⟩

/-- Helper for Corollary 4.2: the packaged active trial data is measurable. -/
theorem measurable_canonicalActiveTrialData
    (h_region : RegionCondition h oracle params confidence X) (k : ℕ) :
    Measurable (canonicalActiveTrialData h_region (Q := Q) (B := B) (b := b) k) := by
  have hpoint : Measurable (fun z :
      ActivePreBatchState h params X × (ℕ → Ξ) ↦ z.1.1.1) := by
    fun_prop
  have hpair : Measurable (fun z :
      ActivePreBatchState h params X × (ℕ → Ξ) ↦
        (z.1.1.1, canonicalActiveBaseStepAt h oracle params Q B b k z)) :=
    hpoint.prodMk (measurable_canonicalActiveBaseStepAt h_region k)
  -- The proof field is ignored by the subtype measurable space.
  exact hpair.subtype_mk

/-- Helper for Corollary 4.2: the next corrected point of an active state. -/
noncomputable def canonicalActiveNextPointAt
    (h : EqualityConstrained.Regularity f c)
    (oracle : EqualityConstrained.StochasticOracle f h.region ν)
    (params : Parameters h x₀ multiplier₀) (Q B b : ℕ+)
    {X : Set (EuclideanSpace ℝ (Fin n))} (k : ℕ)
    (z : ActivePreBatchState h params X × (ℕ → Ξ)) :
    EuclideanSpace ℝ (Fin n) :=
  nextPoint c z.1.1.1 (canonicalActiveBaseStepAt h oracle params Q B b k z)

/-- Helper for Corollary 4.2: the direct active next-point spelling agrees
with correction restricted to its regularity domain. -/
theorem canonicalActiveNextPointAt_eq_restrict
    (h_region : RegionCondition h oracle params confidence X) (k : ℕ) :
    canonicalActiveNextPointAt h oracle params Q B b (X := X) k =
      Set.restrict
          (stepRegularityDomain h)
          (fun xp ↦ nextPoint c xp.1 xp.2) ∘
        canonicalActiveTrialData h_region (Q := Q) (B := B) (b := b) k := by
  -- Both sides compute the same corrected point; only the right side carries domain evidence.
  funext z
  rfl

/-- Helper for Corollary 4.2: the active corrected next point is measurable. -/
theorem measurable_canonicalActiveNextPointAt
    (h_region : RegionCondition h oracle params confidence X) (k : ℕ) :
    Measurable (canonicalActiveNextPointAt h oracle params Q B b (X := X) k) := by
  have hrestricted : Continuous
      (Set.restrict
        (stepRegularityDomain h)
        (fun xp ↦ nextPoint c xp.1 xp.2)) :=
    (continuousOn_nextPoint h).restrict
  -- Compose the continuous restricted correction with measurable active trial data.
  rw [canonicalActiveNextPointAt_eq_restrict h_region k]
  exact hrestricted.measurable.comp
    (measurable_canonicalActiveTrialData h_region (Q := Q) (B := B) (b := b) k)

/-- Helper for Corollary 4.2: the next multiplier of an active canonical state. -/
noncomputable def canonicalActiveNextMultiplierAt
    (h : EqualityConstrained.Regularity f c)
    (oracle : EqualityConstrained.StochasticOracle f h.region ν)
    (params : Parameters h x₀ multiplier₀) (Q B b : ℕ+)
    {X : Set (EuclideanSpace ℝ (Fin n))} (k : ℕ)
    (z : ActivePreBatchState h params X × (ℕ → Ξ)) :
    EuclideanSpace ℝ (Fin m) :=
  nextMultiplier c params.rho z.1.1.1 z.1.1.2.2.1
    (canonicalActiveBaseStepAt h oracle params Q B b k z)

/-- Helper for Corollary 4.2: the active canonical next multiplier is measurable. -/
theorem measurable_canonicalActiveNextMultiplierAt
    (h_region : RegionCondition h oracle params confidence X) (k : ℕ) :
    Measurable
      (canonicalActiveNextMultiplierAt h oracle params Q B b (X := X) k) := by
  have hmultiplier : Measurable (fun z :
      ActivePreBatchState h params X × (ℕ → Ξ) ↦ z.1.1.2.2.1) := by
    fun_prop
  -- Use the corrected-point formula after its restricted measurability is established.
  unfold canonicalActiveNextMultiplierAt nextMultiplier
  have hconstraintExtension : Measurable (fun z :
      ActivePreBatchState h params X × (ℕ → Ξ) ↦
      h.constraintExtension
        (canonicalActiveNextPointAt h oracle params Q B b k z)) :=
    h.measurable_constraintExtension.comp
      (measurable_canonicalActiveNextPointAt h_region k)
  have hconstraint : Measurable (fun z :
      ActivePreBatchState h params X × (ℕ → Ξ) ↦
      c (canonicalActiveNextPointAt h oracle params Q B b k z)) := by
    have hfunctions :
        (fun z : ActivePreBatchState h params X × (ℕ → Ξ) ↦
          c (canonicalActiveNextPointAt h oracle params Q B b k z)) =
        (fun z ↦ h.constraintExtension
          (canonicalActiveNextPointAt h oracle params Q B b k z)) := by
      funext z
      exact (h.constraintExtension_eq
        (canonicalActiveNextPoint_mem_region h_region k z)).symm
    rw [hfunctions]
    exact hconstraintExtension
  exact hmultiplier.add (hconstraint.const_smul (params.rho : ℝ))

/-- Helper for Corollary 4.2: assemble the four mathematical components of a
pre-batch state without exposing product association at each use. -/
def preBatchDataOfComponents
    (current previous : EuclideanSpace ℝ (Fin n))
    (multiplier : EuclideanSpace ℝ (Fin m))
    (rawEstimate : EuclideanSpace ℝ (Fin n)) :
    PreBatchData (n := n) (m := m) :=
  (current, previous, multiplier, rawEstimate)

/-- Helper for Corollary 4.2: the assembled state's current-point projection. -/
theorem preBatchDataOfComponents_current
    (current previous : EuclideanSpace ℝ (Fin n))
    (multiplier : EuclideanSpace ℝ (Fin m))
    (rawEstimate : EuclideanSpace ℝ (Fin n)) :
    (preBatchDataOfComponents current previous multiplier rawEstimate).1 =
      current := by
  -- Compute the first product projection at the constructor boundary.
  rfl

/-- Helper for Corollary 4.2: the assembled state's preceding-point projection. -/
theorem preBatchDataOfComponents_previous
    (current previous : EuclideanSpace ℝ (Fin n))
    (multiplier : EuclideanSpace ℝ (Fin m))
    (rawEstimate : EuclideanSpace ℝ (Fin n)) :
    (preBatchDataOfComponents current previous multiplier rawEstimate).2.1 =
      previous := by
  -- Compute the second product projection at the constructor boundary.
  rfl

/-- Helper for Corollary 4.2: the assembled state's multiplier projection. -/
theorem preBatchDataOfComponents_multiplier
    (current previous : EuclideanSpace ℝ (Fin n))
    (multiplier : EuclideanSpace ℝ (Fin m))
    (rawEstimate : EuclideanSpace ℝ (Fin n)) :
    (preBatchDataOfComponents current previous multiplier rawEstimate).2.2.1 =
      multiplier := by
  -- Compute the third product projection at the constructor boundary.
  rfl

/-- Helper for Corollary 4.2: the assembled state's raw-estimate projection. -/
theorem preBatchDataOfComponents_rawEstimate
    (current previous : EuclideanSpace ℝ (Fin n))
    (multiplier : EuclideanSpace ℝ (Fin m))
    (rawEstimate : EuclideanSpace ℝ (Fin n)) :
    (preBatchDataOfComponents current previous multiplier rawEstimate).2.2.2 =
      rawEstimate := by
  -- Compute the final product projection at the constructor boundary.
  rfl

/-- Helper for Corollary 4.2: the active invariant of assembled data is
exactly the four localization and multiplier conditions on its components. -/
theorem activePreBatchInvariant_preBatchDataOfComponents_iff
    (h : EqualityConstrained.Regularity f c)
    (params : Parameters h x₀ multiplier₀)
    (X : Set (EuclideanSpace ℝ (Fin n)))
    (current previous : EuclideanSpace ℝ (Fin n))
    (multiplier : EuclideanSpace ℝ (Fin m))
    (rawEstimate : EuclideanSpace ℝ (Fin n)) :
    ActivePreBatchInvariant h params X
        (preBatchDataOfComponents current previous multiplier rawEstimate) ↔
      current ∈ X ∧ previous ∈ h.region ∧
        ‖multiplier‖ ≤ params.multiplierBound ∧
          ‖multiplier + (params.rho : ℝ) • c current‖ ≤
            3 * params.multiplierBound := by
  -- Unfold the predicate and product constructor together at their owner boundary.
  rfl

/-- Helper for Corollary 4.2: the numerical successor of an active canonical
state stores the corrected point, old point, new multiplier, and new raw estimate. -/
noncomputable def canonicalActiveNextDataAt
    (h : EqualityConstrained.Regularity f c)
    (oracle : EqualityConstrained.StochasticOracle f h.region ν)
    (params : Parameters h x₀ multiplier₀) (Q B b : ℕ+)
    {X : Set (EuclideanSpace ℝ (Fin n))} (k : ℕ)
    (z : ActivePreBatchState h params X × (ℕ → Ξ)) :
    PreBatchData (n := n) (m := m) :=
  preBatchDataOfComponents (n := n) (m := m)
    (canonicalActiveNextPointAt h oracle params Q B b (X := X) k z)
    z.1.1.1
    (canonicalActiveNextMultiplierAt h oracle params Q B b (X := X) k z)
    (canonicalRawEstimateAt oracle Q B b k z.1.1 z.2)

/-- Helper for Corollary 4.2: if the corrected successor remains in the
localization set, its numerical data satisfy the active invariant. -/
theorem canonicalActiveNextDataAt_invariant
    (h_region : RegionCondition h oracle params confidence X) (k : ℕ)
    (z : ActivePreBatchState h params X × (ℕ → Ξ))
    (hnext : canonicalActiveNextPointAt h oracle params Q B b k z ∈ X) :
    ActivePreBatchInvariant h params X
      (canonicalActiveNextDataAt h oracle params Q B b k z) := by
  have hstep := norm_canonicalActiveBaseStepAt_le
    (Q := Q) (B := B) (b := b) h_region k z
  have hadmissible := canonicalActiveBaseStepAt_isAdmissible
    (Q := Q) (B := B) (b := b) h_region k z
  have hgradient :
      ‖canonicalClippedEstimateAt h oracle Q B b k
        (activeNumericalInput z)‖ ≤ h.gradientBound := by
    unfold canonicalClippedEstimateAt
    exact SPIDER.norm_clip_le h.gradientBound _
  have hnewMultiplier :
      ‖canonicalActiveNextMultiplierAt h oracle params Q B b k z‖ ≤
        params.multiplierBound := by
    simpa only [canonicalActiveNextMultiplierAt, canonicalActiveBaseStepAt,
      canonicalBaseStepAt, canonicalModelInputAt, Function.comp_apply,
      activeNumericalInput] using
        norm_nextMultiplier_canonicalBaseStep_le h params z.1.1.1
          (canonicalClippedEstimateAt h oracle Q B b k (activeNumericalInput z))
          z.1.1.2.2.1 hadmissible hstep hgradient
  have hupdate :
      canonicalActiveNextMultiplierAt h oracle params Q B b k z =
        z.1.1.2.2.1 + (params.rho : ℝ) • c
          (canonicalActiveNextPointAt h oracle params Q B b k z) := by
    rw [canonicalActiveNextMultiplierAt, nextMultiplier_def,
      canonicalActiveNextPointAt]
  have heffectiveIdentity :
      canonicalActiveNextMultiplierAt h oracle params Q B b k z +
          (params.rho : ℝ) • c
            (canonicalActiveNextPointAt h oracle params Q B b k z) =
        (2 : ℝ) • canonicalActiveNextMultiplierAt h oracle params Q B b k z -
          z.1.1.2.2.1 := by
    rw [hupdate]
    module
  have hnewEffective :
      ‖canonicalActiveNextMultiplierAt h oracle params Q B b k z +
          (params.rho : ℝ) • c
            (canonicalActiveNextPointAt h oracle params Q B b k z)‖ ≤
        3 * params.multiplierBound := by
    rw [heffectiveIdentity]
    calc
      ‖(2 : ℝ) • canonicalActiveNextMultiplierAt h oracle params Q B b k z -
          z.1.1.2.2.1‖ ≤
        ‖(2 : ℝ) • canonicalActiveNextMultiplierAt h oracle params Q B b k z‖ +
          ‖z.1.1.2.2.1‖ := norm_sub_le _ _
      _ = 2 * ‖canonicalActiveNextMultiplierAt h oracle params Q B b k z‖ +
          ‖z.1.1.2.2.1‖ := by rw [norm_smul, Real.norm_ofNat]
      _ ≤ 3 * params.multiplierBound := by
        have hboundNonneg : (0 : ℝ) ≤ params.multiplierBound := by positivity
        linarith [z.1.norm_multiplier_le]
  -- Route correction: the effective-multiplier clause is stored explicitly;
  -- multiplier boundedness alone cannot control the next canonical base step.
  exact ⟨hnext,
    h_region.thickening_subset
      (Metric.self_subset_cthickening X z.1.current_mem),
    hnewMultiplier, hnewEffective⟩

/-- Helper for Corollary 4.2: one fresh batch advances an active state, or
marks it inactive when the corrected point leaves the localization set. -/
noncomputable def canonicalActiveTransition
    (h : EqualityConstrained.Regularity f c)
    (oracle : EqualityConstrained.StochasticOracle f h.region ν)
    (params : Parameters h x₀ multiplier₀) (Q B b : ℕ+)
    (X : Set (EuclideanSpace ℝ (Fin n)))
    (h_region : RegionCondition h oracle params confidence X) (k : ℕ)
    (z : ActivePreBatchState h params X × (ℕ → Ξ)) :
    LocalizedPreBatchState h params X :=
  @dite (LocalizedPreBatchState h params X)
    (canonicalActiveNextPointAt h oracle params Q B b k z ∈ X)
    (Classical.propDecidable _)
    (fun hnext ↦ Sum.inr
      ⟨canonicalActiveNextDataAt h oracle params Q B b k z,
        canonicalActiveNextDataAt_invariant h_region k z hnext⟩)
    (fun _ ↦ Sum.inl ())

/-- Helper for Corollary 4.2: the active localized transition is measurable. -/
theorem measurable_canonicalActiveTransition
    (X : Set (EuclideanSpace ℝ (Fin n))) (hX : MeasurableSet X)
    (h_region : RegionCondition h oracle params confidence X) (k : ℕ) :
    Measurable
      (canonicalActiveTransition h oracle params Q B b X h_region k) := by
  let S : Set (ActivePreBatchState h params X × (ℕ → Ξ)) :=
    canonicalActiveNextPointAt h oracle params Q B b k ⁻¹' X
  have hS : MeasurableSet S :=
    hX.preimage (measurable_canonicalActiveNextPointAt h_region k)
  have htrue : Measurable (fun z : S ↦
      (Sum.inr
        (⟨canonicalActiveNextDataAt h oracle params Q B b k z.1,
          canonicalActiveNextDataAt_invariant h_region k z.1 z.2⟩ :
          ActivePreBatchState h params X) :
        LocalizedPreBatchState h params X)) := by
    have hnextPoint : Measurable (fun z : S ↦
        canonicalActiveNextPointAt h oracle params Q B b k z.1) :=
      (measurable_canonicalActiveNextPointAt
        (Q := Q) (B := B) (b := b) h_region k).comp measurable_subtype_coe
    have hpoint : Measurable (fun z : S ↦ z.1.1.1.1) := by
      fun_prop
    have hnextMultiplier : Measurable (fun z : S ↦
        canonicalActiveNextMultiplierAt h oracle params Q B b k z.1) :=
      (measurable_canonicalActiveNextMultiplierAt
        (Q := Q) (B := B) (b := b) h_region k).comp measurable_subtype_coe
    have hraw : Measurable (fun z : S ↦
        canonicalRawEstimateAt oracle Q B b k z.1.1.1 z.1.2) :=
      ((measurable_canonicalRawEstimateAt oracle Q B b k).comp
        measurable_activeNumericalInput).comp measurable_subtype_coe
    apply measurable_inr.comp
    apply Measurable.subtype_mk
    -- Assemble product measurability only after entering the active branch.
    unfold canonicalActiveNextDataAt preBatchDataOfComponents
    exact hnextPoint.prodMk
      (hpoint.prodMk (hnextMultiplier.prodMk hraw))
  have hfalse : Measurable (fun _ : (Sᶜ : Set
      (ActivePreBatchState h params X × (ℕ → Ξ))) ↦
      (Sum.inl () : LocalizedPreBatchState h params X)) :=
    measurable_const
  -- Local instance justification: `Measurable.dite` requires a decidable
  -- membership family for the arbitrary measurable preimage `S`.
  letI : ∀ z, Decidable (z ∈ S) := fun z ↦ Classical.propDecidable (z ∈ S)
  let branch : ActivePreBatchState h params X × (ℕ → Ξ) →
      LocalizedPreBatchState h params X := fun z ↦
    if hnext : z ∈ S then
      Sum.inr
        ⟨canonicalActiveNextDataAt h oracle params Q B b k z,
          canonicalActiveNextDataAt_invariant h_region k z hnext⟩
    else Sum.inl ()
  have hbranch : Measurable branch := by
    -- Apply the measurable dependent branch over corrected localization membership.
    unfold branch
    exact Measurable.dite htrue hfalse hS
  have heq :
      canonicalActiveTransition h oracle params Q B b X h_region k = branch := by
    -- Normalize both branch spellings pointwise; proof irrelevance identifies invariant witnesses.
    funext z
    unfold canonicalActiveTransition branch
    by_cases hnext :
        canonicalActiveNextPointAt h oracle params Q B b k z ∈ X
    · simp only [hnext, dite_true, S, Set.mem_preimage]
    · simp only [hnext, dite_false, S, Set.mem_preimage]
  rw [heq]
  exact hbranch

/-- Helper for Corollary 4.2: the full localized transition leaves an inactive
state inactive and otherwise applies the active corrected transition. -/
noncomputable def canonicalLocalizedTransition
    (h : EqualityConstrained.Regularity f c)
    (oracle : EqualityConstrained.StochasticOracle f h.region ν)
    (params : Parameters h x₀ multiplier₀) (Q B b : ℕ+)
    (X : Set (EuclideanSpace ℝ (Fin n)))
    (h_region : RegionCondition h oracle params confidence X) (k : ℕ) :
    LocalizedPreBatchState h params X × (ℕ → Ξ) →
      LocalizedPreBatchState h params X :=
  Sum.elim
      (fun _ : Unit × (ℕ → Ξ) ↦
        (Sum.inl () : LocalizedPreBatchState h params X))
      (canonicalActiveTransition h oracle params Q B b X h_region k) ∘
    MeasurableEquiv.sumProdDistrib Unit (ActivePreBatchState h params X) (ℕ → Ξ)

/-- Helper for Corollary 4.2: the full localized corrected transition is
measurable in the prior state and fresh batch. -/
theorem measurable_canonicalLocalizedTransition
    (X : Set (EuclideanSpace ℝ (Fin n))) (hX : MeasurableSet X)
    (h_region : RegionCondition h oracle params confidence X) (k : ℕ) :
    Measurable
      (canonicalLocalizedTransition h oracle params Q B b X h_region k) := by
  -- Distribute the fresh batch across the inactive/active sum, then handle both branches.
  unfold canonicalLocalizedTransition
  exact (measurable_const.sumElim
    (measurable_canonicalActiveTransition X hX h_region k)).comp
      (MeasurableEquiv.sumProdDistrib Unit
        (ActivePreBatchState h params X) (ℕ → Ξ)).measurable

/-- Helper for Corollary 4.2: the active canonical step computes directly
from the state's current point, multiplier, raw transition, and fresh batch. -/
theorem canonicalActiveBaseStepAt_apply
    (s : ActivePreBatchState h params X) (batch : ℕ → Ξ) (k : ℕ) :
    canonicalActiveBaseStepAt h oracle params Q B b k (s, batch) =
      canonicalBaseStep c params.rho params.beta s.1.1
        (SPIDER.clip h.gradientBound
          (canonicalRawEstimateAt oracle Q B b k s.1 batch)) s.1.2.2.1 := by
  -- Normalize the grouped model input once at the active-state owner.
  rfl

/-- Helper for Corollary 4.2: the active canonical next point applies the
corrected point update to the canonical base step. -/
theorem canonicalActiveNextPointAt_apply
    (s : ActivePreBatchState h params X) (batch : ℕ → Ξ) (k : ℕ) :
    canonicalActiveNextPointAt h oracle params Q B b k (s, batch) =
      nextPoint c s.1.1
        (canonicalActiveBaseStepAt h oracle params Q B b k (s, batch)) := by
  -- Expose the corrected point owner equation without unfolding it downstream.
  rfl

/-- Helper for Corollary 4.2: the active canonical next multiplier applies the
corrected multiplier update to the same canonical base step. -/
theorem canonicalActiveNextMultiplierAt_apply
    (s : ActivePreBatchState h params X) (batch : ℕ → Ξ) (k : ℕ) :
    canonicalActiveNextMultiplierAt h oracle params Q B b k (s, batch) =
      nextMultiplier c params.rho s.1.1 s.1.2.2.1
        (canonicalActiveBaseStepAt h oracle params Q B b k (s, batch)) := by
  -- Expose the corrected multiplier owner equation without unfolding it downstream.
  rfl

/-- Helper for Corollary 4.2: the active successor data stores the corrected
next point in its current-point field. -/
theorem canonicalActiveNextDataAt_current
    (s : ActivePreBatchState h params X) (batch : ℕ → Ξ) (k : ℕ) :
    (canonicalActiveNextDataAt h oracle params Q B b k (s, batch)).1 =
      canonicalActiveNextPointAt h oracle params Q B b k (s, batch) := by
  -- Project the first component of the opaque successor package.
  unfold canonicalActiveNextDataAt
  exact preBatchDataOfComponents_current _ _ _ _

/-- Helper for Corollary 4.2: the active successor data retains the old point
as its preceding-point field. -/
theorem canonicalActiveNextDataAt_previous
    (s : ActivePreBatchState h params X) (batch : ℕ → Ξ) (k : ℕ) :
    (canonicalActiveNextDataAt h oracle params Q B b k (s, batch)).2.1 =
      s.1.1 := by
  -- Project the second component of the opaque successor package.
  unfold canonicalActiveNextDataAt
  exact preBatchDataOfComponents_previous _ _ _ _

/-- Helper for Corollary 4.2: the active successor data stores the corrected
next multiplier. -/
theorem canonicalActiveNextDataAt_multiplier
    (s : ActivePreBatchState h params X) (batch : ℕ → Ξ) (k : ℕ) :
    (canonicalActiveNextDataAt h oracle params Q B b k (s, batch)).2.2.1 =
      canonicalActiveNextMultiplierAt h oracle params Q B b k (s, batch) := by
  -- Project the third component of the opaque successor package.
  unfold canonicalActiveNextDataAt
  exact preBatchDataOfComponents_multiplier _ _ _ _

/-- Helper for Corollary 4.2: the active successor data stores the raw
estimate computed from its fresh batch. -/
theorem canonicalActiveNextDataAt_rawEstimate
    (s : ActivePreBatchState h params X) (batch : ℕ → Ξ) (k : ℕ) :
    (canonicalActiveNextDataAt h oracle params Q B b k (s, batch)).2.2.2 =
      canonicalRawEstimateAt oracle Q B b k s.1 batch := by
  -- Project the final component of the opaque successor package.
  unfold canonicalActiveNextDataAt
  exact preBatchDataOfComponents_rawEstimate _ _ _ _

/-- Helper for Corollary 4.2: an inactive localized state remains inactive
after every fresh batch. -/
theorem canonicalLocalizedTransition_inactive
    (X : Set (EuclideanSpace ℝ (Fin n)))
    (h_region : RegionCondition h oracle params confidence X)
    (k : ℕ) (batch : ℕ → Ξ) :
    canonicalLocalizedTransition h oracle params Q B b X h_region k
        (Sum.inl (), batch) =
      (Sum.inl () : LocalizedPreBatchState h params X) := by
  -- The sum-product distributivity map sends the inactive branch to its left summand.
  rfl

/-- Helper for Corollary 4.2: an active transition whose corrected point
remains localized returns the bundled numerical successor. -/
theorem canonicalLocalizedTransition_active_of_mem
    (X : Set (EuclideanSpace ℝ (Fin n)))
    (h_region : RegionCondition h oracle params confidence X)
    (k : ℕ) (s : ActivePreBatchState h params X) (batch : ℕ → Ξ)
    (hnext : canonicalActiveNextPointAt h oracle params Q B b k (s, batch) ∈ X) :
    canonicalLocalizedTransition h oracle params Q B b X h_region k
        (Sum.inr s, batch) =
      Sum.inr
        ⟨canonicalActiveNextDataAt h oracle params Q B b k (s, batch),
          canonicalActiveNextDataAt_invariant h_region k (s, batch) hnext⟩ := by
  -- Select the active and successful localization branches of the owner definitions.
  unfold canonicalLocalizedTransition canonicalActiveTransition
  have hdistrib :
      (MeasurableEquiv.sumProdDistrib Unit (ActivePreBatchState h params X) (ℕ → Ξ))
          (Sum.inr s, batch) = Sum.inr (s, batch) := rfl
  rw [Function.comp_apply, hdistrib, Sum.elim_inr, dif_pos hnext]

/-- Helper for Corollary 4.2: an active transition whose corrected point
leaves the localization set becomes inactive. -/
theorem canonicalLocalizedTransition_active_of_not_mem
    (X : Set (EuclideanSpace ℝ (Fin n)))
    (h_region : RegionCondition h oracle params confidence X)
    (k : ℕ) (s : ActivePreBatchState h params X) (batch : ℕ → Ξ)
    (hnext : canonicalActiveNextPointAt h oracle params Q B b k (s, batch) ∉ X) :
    canonicalLocalizedTransition h oracle params Q B b X h_region k
        (Sum.inr s, batch) =
      (Sum.inl () : LocalizedPreBatchState h params X) := by
  -- Select the active but failed localization branch of the owner definitions.
  unfold canonicalLocalizedTransition canonicalActiveTransition
  have hdistrib :
      (MeasurableEquiv.sumProdDistrib Unit (ActivePreBatchState h params X) (ℕ → Ξ))
          (Sum.inr s, batch) = Sum.inr (s, batch) := rfl
  rw [Function.comp_apply, hdistrib, Sum.elim_inr, dif_neg hnext]

end LALM.Correction.StochasticRun.Localization

end
