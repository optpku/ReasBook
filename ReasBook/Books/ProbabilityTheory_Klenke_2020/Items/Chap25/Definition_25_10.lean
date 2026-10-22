/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib
import Books.ProbabilityTheory_Klenke_2020.Items.Chap25.Definition_25_2
import Books.ProbabilityTheory_Klenke_2020.Items.Chap25.Definition_25_3

-- Declarations for this item will be appended below by the statement pipeline.

/- Definition 25.2: the textbook vector space `𝓔` of predictable simple integrands is the
canonical submodule `MeasureTheory.predictableSimpleProcesses`. Definition 25.10 below uses the
actual `L²(μ ⊗ dt)` image of this source-facing owner and its closure from Theorem 25.9. -/
recall MeasureTheory.predictableSimpleProcesses
recall MeasureTheory.PredictableStepRepresentation.brownianElementaryIntegralAtInfinity
recall MeasureTheory.brownianElementaryIntegralAtInfinity

open Filter MeasureTheory
open scoped ENNReal

noncomputable section

universe u

namespace MeasureTheory

variable {Ω : Type u} [MeasurableSpace Ω]

local notation "ContinuousFiltration" => Filtration NNReal (inferInstance : MeasurableSpace Ω)
local notation "Process" => NNReal → Ω → ℝ

/-- Helper for Definition 25.10: the realized closure `\overline{\mathcal E}` of the canonical
`L²(μ ⊗ dt)` subspace of predictable simple integrands. -/
def PredictableSimpleProcessL2Closure (ℱ : ContinuousFiltration) (μ : Measure Ω) :=
  Submodule.topologicalClosure (predictableSimpleProcessL2 ℱ μ)

end MeasureTheory

namespace ProbabilityTheory

variable {Ω : Type u} [mΩ : MeasurableSpace Ω]

local notation "TimeFiltration" => Filtration NNReal mΩ
local notation "Process" => NNReal → Ω → ℝ

private def predictableSimpleProcessL2ToClosure
    {ℱ : TimeFiltration} {μ : Measure Ω}
    (H : MeasureTheory.predictableSimpleProcessL2 ℱ μ) :
    PredictableSimpleProcessL2Closure ℱ μ :=
  ⟨(H : Lp ℝ 2 (MeasureTheory.processMeasure μ)),
    Submodule.le_topologicalClosure (MeasureTheory.predictableSimpleProcessL2 ℱ μ) H.2⟩

private def processLpCutoffSet (t : NNReal) : Set (Ω × ℝ) :=
  {x | x.2 ≤ (t : ℝ)}

private theorem measurableSet_processLpCutoffSet (t : NNReal) :
    MeasurableSet (processLpCutoffSet (Ω := Ω) t) := by
  simpa [processLpCutoffSet] using measurableSet_le measurable_snd measurable_const

/-- Helper for Definition 25.10: the deterministic-time cutoff process
`(s, ω) ↦ H s ω 1_{ {s ≤ t} }`. -/
private def cutoffBeforeDeterministicTime (t : NNReal) (H : Process) : Process :=
  fun s ω ↦ if s ≤ t then H s ω else 0

omit mΩ in
/-- Helper for Definition 25.10: realizing the deterministic-time cutoff on `Ω × ℝ` is exactly
the ambient indicator cutoff used in the `L²(μ ⊗ dt)` operator. -/
private theorem processToTimeSpaceFun_cutoffBeforeDeterministicTime
    (t : NNReal) (H : Process) :
    MeasureTheory.processToTimeSpaceFun (cutoffBeforeDeterministicTime t H) =
      Set.indicator (processLpCutoffSet (Ω := Ω) t) (MeasureTheory.processToTimeSpaceFun H) := by
  funext x
  by_cases hx : x.2 ≤ (t : ℝ)
  · have hx' : x.2.toNNReal ≤ t := Real.toNNReal_le_iff_le_coe.2 hx
    rw [Set.indicator_of_mem (by simpa [processLpCutoffSet] using hx)]
    simp [Function.uncurry, MeasureTheory.processToTimeSpaceFun, cutoffBeforeDeterministicTime, hx']
  · have hx' : ¬ x.2.toNNReal ≤ t := by
      intro hx'
      exact hx (Real.toNNReal_le_iff_le_coe.1 hx')
    rw [Set.indicator_of_notMem (by simpa [processLpCutoffSet] using hx)]
    simp [Function.uncurry, MeasureTheory.processToTimeSpaceFun, cutoffBeforeDeterministicTime, hx']

omit mΩ in
/-- Helper for Definition 25.10: a point of a finite ordered subset of `NNReal` cannot lie
strictly between two consecutive points in its `orderEmbOfFin` enumeration. -/
private theorem not_mem_Ioo_between_orderEmbOfFin_consecutive
    (B : Finset NNReal) {n : ℕ} (hB : B.card = n + 1) (i : Fin n) {x : NNReal} (hx : x ∈ B) :
    x ∉ Set.Ioo (B.orderEmbOfFin hB i.castSucc) (B.orderEmbOfFin hB i.succ) := by
  intro hxIoo
  let j : Fin (n + 1) := (B.orderIsoOfFin hB).symm ⟨x, hx⟩
  have hjx : B.orderEmbOfFin hB j = x := by
    change (((B.orderIsoOfFin hB) j : B) : NNReal) = x
    simp [j]
  have hij_left : i.castSucc < j := by
    exact (B.orderEmbOfFin hB).lt_iff_lt.mp (by simpa [hjx] using hxIoo.1)
  have hij_right : j < i.succ := by
    exact (B.orderEmbOfFin hB).lt_iff_lt.mp (by simpa [hjx] using hxIoo.2)
  have hij_left' : i.1 < j.1 := by
    simpa using hij_left
  have hij_right' : j.1 < i.1 + 1 := by
    exact hij_right
  exact (Nat.not_lt_of_ge (Nat.succ_le_of_lt hij_left')) hij_right'

omit mΩ in
/-- Helper for Definition 25.10: every point of a finite ordered subset of `NNReal` is bounded
above by the last point of its `orderEmbOfFin` enumeration. -/
private theorem le_orderEmbOfFin_last_of_mem
    (B : Finset NNReal) {n : ℕ} (hB : B.card = n + 1) {x : NNReal} (hx : x ∈ B) :
    x ≤ B.orderEmbOfFin hB (Fin.last n) := by
  let j : Fin (n + 1) := (B.orderIsoOfFin hB).symm ⟨x, hx⟩
  have hjx : B.orderEmbOfFin hB j = x := by
    change (((B.orderIsoOfFin hB) j : B) : NNReal) = x
    simp [j]
  exact hjx ▸ (B.orderEmbOfFin hB).monotone (Fin.le_last j)

/-- Helper for Definition 25.10: once a refined predictable-step partition is fixed, truncating
its coefficients after time `t` realizes the deterministic cutoff process. -/
private theorem exists_cutoffRepresentation_of_refinedPartition
    {ℱ : TimeFiltration}
    (representation : MeasureTheory.PredictableStepRepresentation ℱ)
    {nRef : ℕ}
    (times : Fin (nRef + 1) → NNReal)
    (hTimesZero : times 0 = 0)
    (hTimesStrictMono : StrictMono times)
    (coeff : Fin nRef → Ω → ℝ)
    (hCoeffMeasurable : ∀ i : Fin nRef, Measurable[ℱ (times i.castSucc)] (coeff i))
    (hCoeffBounded : ∀ i : Fin nRef, ∃ C : ℝ, ∀ ω, |coeff i ω| ≤ C)
    (hCoeffEq :
      ∀ i : Fin nRef, ∀ ⦃s : NNReal⦄, s ∈ Set.Ioc (times i.castSucc) (times i.succ) →
        representation.toProcess s = coeff i)
    (t : NNReal)
    (hLastGeT : t ≤ times (Fin.last nRef))
    (hLeftOfCutoff : ∀ i : Fin nRef, ¬ times i.succ ≤ t → t ≤ times i.castSucc) :
    ∃ cutoff : MeasureTheory.PredictableStepRepresentation ℱ,
      cutoff.toProcess = cutoffBeforeDeterministicTime t representation.toProcess := by
  let coeffCut : Fin nRef → Ω → ℝ := fun i ω ↦ if times i.succ ≤ t then coeff i ω else 0
  have hCoeffCutMeasurable :
      ∀ i : Fin nRef, Measurable[ℱ (times i.castSucc)] (coeffCut i) := by
    intro i
    by_cases hi : times i.succ ≤ t
    · simp [coeffCut, hi, hCoeffMeasurable i]
    · simp [coeffCut, hi]
  have hCoeffCutBounded : ∀ i : Fin nRef, ∃ C : ℝ, ∀ ω, |coeffCut i ω| ≤ C := by
    intro i
    by_cases hi : times i.succ ≤ t
    · rcases hCoeffBounded i with ⟨C, hC⟩
      exact ⟨C, by
        intro ω
        simpa [coeffCut, hi] using hC ω⟩
    · refine ⟨0, ?_⟩
      intro ω
      simp [coeffCut, hi]
  let cutoff : MeasureTheory.PredictableStepRepresentation ℱ :=
    { n := nRef
      times := times
      coeff := coeffCut
      times_zero := hTimesZero
      times_strictMono := hTimesStrictMono
      coeff_bounded := hCoeffCutBounded
      coeff_measurable := hCoeffCutMeasurable }
  refine ⟨cutoff, ?_⟩
  funext s ω
  by_cases hAfter : times (Fin.last nRef) < s
  · have hCutZero : cutoff.toProcess s ω = 0 := by
      exact cutoff.toProcess_eq_zero_of_last_lt hAfter ω
    have hsNotLe : ¬ s ≤ t := by
      exact not_le_of_gt (lt_of_le_of_lt hLastGeT hAfter)
    simp [cutoffBeforeDeterministicTime, hCutZero, hsNotLe]
  · by_cases hs0 : s = 0
    · subst hs0
      simp [MeasureTheory.PredictableStepRepresentation.toProcess_apply,
        cutoffBeforeDeterministicTime]
    · have hsPos : 0 < s := by
        exact lt_of_le_of_ne bot_le (by simpa [eq_comm] using hs0)
      have hsLast : s ≤ times (Fin.last nRef) := le_of_not_gt hAfter
      obtain ⟨i, hsi⟩ := cutoff.exists_mem_interval_of_pos_le_last hsPos hsLast
      have hCutCoeff : cutoff.toProcess s ω = coeffCut i ω := by
        exact cutoff.toProcess_eq_coeff_of_mem_interval i hsi ω
      by_cases hi : times i.succ ≤ t
      · have hsLeT : s ≤ t := le_trans hsi.2 hi
        have hRepCoeff : representation.toProcess s ω = coeff i ω := by
          exact congrFun (hCoeffEq i hsi) ω
        simp [cutoffBeforeDeterministicTime, hCutCoeff, coeffCut, hi, hsLeT, hRepCoeff]
      · have hsNotLe : ¬ s ≤ t := by
          exact not_le_of_gt (lt_of_le_of_lt (hLeftOfCutoff i hi) hsi.1)
        simp [cutoffBeforeDeterministicTime, hCutCoeff, coeffCut, hi, hsNotLe]

/-- Helper for Definition 25.10: inserting a deterministic time `t` into a predictable-step
partition yields a predictable-step representation of the cutoff process `H · 1_[0,t]`. -/
private theorem exists_predictableStepRepresentation_cutoffBefore
    {ℱ : TimeFiltration}
    (representation : MeasureTheory.PredictableStepRepresentation ℱ)
    (t : NNReal) :
    ∃ cutoff : MeasureTheory.PredictableStepRepresentation ℱ,
      cutoff.toProcess = cutoffBeforeDeterministicTime t representation.toProcess := by
  let B : Finset NNReal := insert t (Finset.image representation.times Finset.univ)
  have hBt : t ∈ B := Finset.mem_insert_self t _
  have hB0 : (0 : NNReal) ∈ B := by
    exact Finset.mem_insert_of_mem
      (Finset.mem_image.2 ⟨0, Finset.mem_univ _, representation.times_zero⟩)
  have hBpos : 0 < B.card := Finset.card_pos.mpr ⟨0, hB0⟩
  let nRef : ℕ := B.card - 1
  have hBcard : B.card = nRef + 1 := by
    have hcard : B.card = (B.card - 1) + 1 := by
      omega
    simpa [nRef] using hcard
  let times : Fin (nRef + 1) → NNReal := B.orderEmbOfFin hBcard
  have hTimesZero : times 0 = 0 := by
    have hBpos' : 0 < nRef + 1 := by
      simp [hBcard] at hBpos ⊢
    have hBmin : B.min' (Finset.card_pos.mp hBpos) = 0 := by
      refine (Finset.min'_eq_iff (s := B) (H := Finset.card_pos.mp hBpos) 0).2 ?_
      constructor
      · exact hB0
      · intro b hb
        exact bot_le
    calc
      times 0 = B.min' (Finset.card_pos.mp hBpos) := by
        simpa [times] using Finset.orderEmbOfFin_zero (s := B) hBcard hBpos'
      _ = 0 := hBmin
  have hTimesStrictMono : StrictMono times := (B.orderEmbOfFin hBcard).strictMono
  have hStrip :
      ∀ i : Fin nRef,
        ∃ g : Ω → ℝ,
          Measurable[ℱ (times i.castSucc)] g ∧
          (∃ C : ℝ, ∀ ω, |g ω| ≤ C) ∧
          ∀ ⦃s : NNReal⦄, s ∈ Set.Ioc (times i.castSucc) (times i.succ) →
            representation.toProcess s = g := by
    intro i
    have huv : times i.castSucc < times i.succ := hTimesStrictMono i.castSucc_lt_succ
    have hboundary :
        ∀ j : Fin representation.n,
          representation.times j.succ ∉ Set.Ioo (times i.castSucc) (times i.succ) := by
      intro j
      apply not_mem_Ioo_between_orderEmbOfFin_consecutive (B := B) (hB := hBcard) (i := i)
      exact Finset.mem_insert_of_mem (Finset.mem_image.2 ⟨j.succ, Finset.mem_univ _, rfl⟩)
    exact representation.exists_bddMeasurable_eq_on_Ioc_of_no_boundary huv hboundary
  let coeff : Fin nRef → Ω → ℝ := fun i ↦ Classical.choose (hStrip i)
  have hCoeffMeasurable : ∀ i : Fin nRef, Measurable[ℱ (times i.castSucc)] (coeff i) := by
    intro i
    exact (Classical.choose_spec (hStrip i)).1
  have hCoeffBounded : ∀ i : Fin nRef, ∃ C : ℝ, ∀ ω, |coeff i ω| ≤ C := by
    intro i
    exact (Classical.choose_spec (hStrip i)).2.1
  have hCoeffEq :
      ∀ i : Fin nRef, ∀ ⦃s : NNReal⦄, s ∈ Set.Ioc (times i.castSucc) (times i.succ) →
        representation.toProcess s = coeff i := by
    intro i s hs
    exact (Classical.choose_spec (hStrip i)).2.2 hs
  have hLastGeT : t ≤ times (Fin.last nRef) := by
    exact le_orderEmbOfFin_last_of_mem (B := B) (hB := hBcard) hBt
  have hLeftOfCutoff : ∀ i : Fin nRef, ¬ times i.succ ≤ t → t ≤ times i.castSucc := by
    intro i hi
    have hNotMem :=
      not_mem_Ioo_between_orderEmbOfFin_consecutive (B := B) (hB := hBcard) (i := i) hBt
    have htLtRight : t < times i.succ := lt_of_not_ge hi
    exact le_of_not_gt fun htLeftLt ↦ hNotMem ⟨htLeftLt, htLtRight⟩
  exact
    exists_cutoffRepresentation_of_refinedPartition representation times hTimesZero
      hTimesStrictMono coeff hCoeffMeasurable hCoeffBounded hCoeffEq t hLastGeT hLeftOfCutoff

/-- Helper for Definition 25.10: a predictable simple process admits a predictable simple
deterministic-time cutoff with process formula `H · 1_[0,t]`. -/
private noncomputable def predictableSimpleProcessCutoffBefore
    {ℱ : TimeFiltration} (K : MeasureTheory.PredictableSimpleProcess ℱ) (t : NNReal) :
    MeasureTheory.PredictableSimpleProcess ℱ :=
  let representation : MeasureTheory.PredictableStepRepresentation ℱ :=
    Classical.choose (MeasureTheory.PredictableSimpleProcess.exists_representation K)
  let cutoff : MeasureTheory.PredictableStepRepresentation ℱ :=
    Classical.choose (exists_predictableStepRepresentation_cutoffBefore representation t)
  cutoff.toPredictableSimpleProcess

/-- Helper for Definition 25.10: the cutoff simple process realizes the deterministic-time
truncation `(s, ω) ↦ H s ω 1_{ {s ≤ t} }`. -/
private theorem predictableSimpleProcessCutoffBefore_coe
    {ℱ : TimeFiltration} (K : MeasureTheory.PredictableSimpleProcess ℱ) (t : NNReal) :
    ((predictableSimpleProcessCutoffBefore K t : MeasureTheory.PredictableSimpleProcess ℱ) :
      Process) = cutoffBeforeDeterministicTime t (K : Process) := by
  let representation : MeasureTheory.PredictableStepRepresentation ℱ :=
    Classical.choose (MeasureTheory.PredictableSimpleProcess.exists_representation K)
  let cutoff : MeasureTheory.PredictableStepRepresentation ℱ :=
    Classical.choose (exists_predictableStepRepresentation_cutoffBefore representation t)
  have hRepresentation :
      (K : Process) = representation.toProcess :=
    Classical.choose_spec (MeasureTheory.PredictableSimpleProcess.exists_representation K)
  have hCutoff :
      cutoff.toProcess = cutoffBeforeDeterministicTime t representation.toProcess :=
    (Classical.choose_spec (exists_predictableStepRepresentation_cutoffBefore representation t))
  change cutoff.toProcess = cutoffBeforeDeterministicTime t (K : Process)
  simpa [hRepresentation] using hCutoff

/-- The ambient `L²(μ ⊗ dt)` cutoff operator corresponding to the textbook integrand truncation
`H^(t) = H · 1_[0,t]`. -/
private theorem memLp_processLpCutoffBefore
    (μ : Measure Ω) (t : NNReal)
    (f : Lp ℝ 2 (MeasureTheory.processMeasure μ)) :
    MemLp
      (Set.indicator (processLpCutoffSet (Ω := Ω) t) fun x ↦ f x)
      (2 : ℝ≥0∞) (MeasureTheory.processMeasure μ) :=
  (Lp.memLp f).indicator (measurableSet_processLpCutoffSet (Ω := Ω) t)

private noncomputable def processLpCutoffBeforeFun
    (μ : Measure Ω) (t : NNReal)
    (f : Lp ℝ 2 (MeasureTheory.processMeasure μ)) :
    Lp ℝ 2 (MeasureTheory.processMeasure μ) :=
  (memLp_processLpCutoffBefore μ t f).toLp
    (Set.indicator (processLpCutoffSet (Ω := Ω) t) fun x ↦ f x)

/-- Helper for Definition 25.10: the ambient deterministic-time cutoff is additive on
`L²(μ ⊗ dt)`. -/
private theorem processLpCutoffBeforeFun_add
    (μ : Measure Ω) (t : NNReal)
    (f g : Lp ℝ 2 (MeasureTheory.processMeasure μ)) :
    processLpCutoffBeforeFun μ t (f + g) =
      processLpCutoffBeforeFun μ t f + processLpCutoffBeforeFun μ t g := by
  rw [processLpCutoffBeforeFun, processLpCutoffBeforeFun, processLpCutoffBeforeFun]
  rw [← MemLp.toLp_add (memLp_processLpCutoffBefore μ t f)
    (memLp_processLpCutoffBefore μ t g)]
  apply (MemLp.toLp_eq_toLp_iff _ _).2
  filter_upwards [Lp.coeFn_add f g] with x hx
  by_cases hxt : x ∈ processLpCutoffSet (Ω := Ω) t
  · simpa [hxt] using hx
  · simp [hxt]

/-- Helper for Definition 25.10: the ambient deterministic-time cutoff commutes with scalar
multiplication. -/
private theorem processLpCutoffBeforeFun_smul
    (μ : Measure Ω) (t : NNReal) (a : ℝ)
    (f : Lp ℝ 2 (MeasureTheory.processMeasure μ)) :
    processLpCutoffBeforeFun μ t (a • f) =
      a • processLpCutoffBeforeFun μ t f := by
  rw [processLpCutoffBeforeFun, processLpCutoffBeforeFun]
  rw [← MemLp.toLp_const_smul a (memLp_processLpCutoffBefore μ t f)]
  apply (MemLp.toLp_eq_toLp_iff _ _).2
  filter_upwards [Lp.coeFn_smul a f] with x hx
  by_cases hxt : x ∈ processLpCutoffSet (Ω := Ω) t
  · simp [hxt, hx]
  · simp [hxt]

/-- Helper for Definition 25.10: the deterministic-time cutoff is a contraction on ambient
`L²(μ ⊗ dt)`. -/
private theorem norm_processLpCutoffBeforeFun_le
    (μ : Measure Ω) (t : NNReal)
    (f : Lp ℝ 2 (MeasureTheory.processMeasure μ)) :
    ‖processLpCutoffBeforeFun μ t f‖ ≤ 1 * ‖f‖ := by
  rw [processLpCutoffBeforeFun, Lp.norm_toLp, Lp.norm_def]
  simpa [one_mul] using ENNReal.toReal_mono (Lp.eLpNorm_ne_top f)
    (eLpNorm_indicator_le (s := processLpCutoffSet (Ω := Ω) t) (fun x ↦ f x))

/-- Helper for Definition 25.10: the ambient deterministic-time cutoff as a continuous linear map
on `L²(μ ⊗ dt)`. -/
private def processLpCutoffBeforeLinearMap
    (μ : Measure Ω) (t : NNReal) :
    Lp ℝ 2 (MeasureTheory.processMeasure μ) →ₗ[ℝ]
      Lp ℝ 2 (MeasureTheory.processMeasure μ) where
  toFun := processLpCutoffBeforeFun μ t
  map_add' := processLpCutoffBeforeFun_add μ t
  map_smul' := processLpCutoffBeforeFun_smul μ t

/-- The ambient `L²(μ ⊗ dt)` cutoff operator corresponding to the textbook integrand truncation
`H^(t) = H · 1_[0,t]`. -/
private noncomputable def processLpCutoffBefore (μ : Measure Ω) (t : NNReal) :
    Lp ℝ 2 (MeasureTheory.processMeasure μ) →L[ℝ] Lp ℝ 2 (MeasureTheory.processMeasure μ) :=
  LinearMap.mkContinuous
    (processLpCutoffBeforeLinearMap μ t)
    1
    (norm_processLpCutoffBeforeFun_le μ t)

/-- Helper for Definition 25.10: coercing the ambient cutoff operator to functions recovers the
indicator cutoff almost everywhere. -/
private theorem processLpCutoffBefore_coeFn
    (μ : Measure Ω) (t : NNReal)
    (f : Lp ℝ 2 (MeasureTheory.processMeasure μ)) :
    ((
        processLpCutoffBefore μ t f :
          Lp ℝ 2 (MeasureTheory.processMeasure μ)
      ) : Ω × ℝ → ℝ) =ᵐ[MeasureTheory.processMeasure μ]
      Set.indicator (processLpCutoffSet (Ω := Ω) t) (fun x ↦ f x) := by
  -- Proof comment: the ambient operator was defined as the `Lp` class of this indicator
  -- function, so the almost-everywhere statement is the canonical `toLp` coercion formula.
  simpa [processLpCutoffBefore, processLpCutoffBeforeLinearMap, processLpCutoffBeforeFun] using
    MemLp.coeFn_toLp (memLp_processLpCutoffBefore μ t f)

/-- Helper for Definition 25.10: cutting off a globally square-integrable predictable simple
process before a deterministic time stays in ambient `L²(μ ⊗ dt)`. -/
private theorem memLp_predictableSimpleProcessCutoffBefore
    {ℱ : TimeFiltration} {μ : Measure Ω} (t : NNReal)
    (K : MeasureTheory.PredictableSimpleProcess ℱ)
    (hK_memLp :
      MemLp (MeasureTheory.processToTimeSpaceFun (K : Process)) (2 : ℝ≥0∞)
        (MeasureTheory.processMeasure μ)) :
    MemLp
      (MeasureTheory.processToTimeSpaceFun
        ((predictableSimpleProcessCutoffBefore K t :
            MeasureTheory.PredictableSimpleProcess ℱ) : Process))
      (2 : ℝ≥0∞) (MeasureTheory.processMeasure μ) := by
  have hCut_memLp :
      MemLp
        (MeasureTheory.processToTimeSpaceFun
          (cutoffBeforeDeterministicTime t (K : Process)))
        (2 : ℝ≥0∞) (MeasureTheory.processMeasure μ) := by
    -- Proof comment: on `Ω × ℝ`, the deterministic cutoff is exactly the indicator cutoff.
    simpa [processToTimeSpaceFun_cutoffBeforeDeterministicTime] using
      hK_memLp.indicator (measurableSet_processLpCutoffSet (Ω := Ω) t)
  rw [predictableSimpleProcessCutoffBefore_coe (K := K) (t := t)]
  exact hCut_memLp

/-- Helper for Definition 25.10: the ambient deterministic-time cutoff agrees in `L²(μ ⊗ dt)`
with the cutoff predictable simple process. -/
private theorem processLpCutoffBefore_eq_predictableSimpleProcessToL2
    {ℱ : TimeFiltration} {μ : Measure Ω} (t : NNReal)
    (K : MeasureTheory.PredictableSimpleProcess ℱ)
    (hK_memLp :
      MemLp (MeasureTheory.processToTimeSpaceFun (K : Process)) (2 : ℝ≥0∞)
        (MeasureTheory.processMeasure μ))
    (hCut_simple_memLp :
      MemLp
        (MeasureTheory.processToTimeSpaceFun
          ((predictableSimpleProcessCutoffBefore K t :
              MeasureTheory.PredictableSimpleProcess ℱ) : Process))
        (2 : ℝ≥0∞) (MeasureTheory.processMeasure μ)) :
    processLpCutoffBefore μ t
        (hK_memLp.toLp (MeasureTheory.processToTimeSpaceFun (K : Process))) =
      ((MeasureTheory.predictableSimpleProcessToL2
          (predictableSimpleProcessCutoffBefore K t) hCut_simple_memLp :
          MeasureTheory.predictableSimpleProcessL2 ℱ μ) :
        Lp ℝ 2 (MeasureTheory.processMeasure μ)) := by
  apply MeasureTheory.Lp.ext
  have hIndicatorToK :
      Set.indicator (processLpCutoffSet (Ω := Ω) t)
          (fun x ↦
            ((hK_memLp.toLp (MeasureTheory.processToTimeSpaceFun (K : Process)) :
                Lp ℝ 2 (MeasureTheory.processMeasure μ)) :
                Ω × ℝ → ℝ) x) =ᵐ[MeasureTheory.processMeasure μ]
        Set.indicator (processLpCutoffSet (Ω := Ω) t)
          (MeasureTheory.processToTimeSpaceFun (K : Process)) := by
    filter_upwards [MeasureTheory.MemLp.coeFn_toLp hK_memLp] with x hx
    by_cases hxt : x ∈ processLpCutoffSet (Ω := Ω) t
    · simp [hxt, hx]
    · simp [hxt]
  have hKToCut :
      Set.indicator (processLpCutoffSet (Ω := Ω) t)
          (MeasureTheory.processToTimeSpaceFun (K : Process)) =ᵐ[MeasureTheory.processMeasure μ]
        MeasureTheory.processToTimeSpaceFun
          ((predictableSimpleProcessCutoffBefore K t :
              MeasureTheory.PredictableSimpleProcess ℱ) : Process) := by
    exact Filter.EventuallyEq.of_eq <| by
      funext x
      simp [predictableSimpleProcessCutoffBefore_coe,
        processToTimeSpaceFun_cutoffBeforeDeterministicTime]
  have hCutToLp :
      ((((MeasureTheory.predictableSimpleProcessToL2
            (predictableSimpleProcessCutoffBefore K t) hCut_simple_memLp :
            MeasureTheory.predictableSimpleProcessL2 ℱ μ) :
          Lp ℝ 2 (MeasureTheory.processMeasure μ)) : Ω × ℝ → ℝ)) =ᵐ[MeasureTheory.processMeasure μ]
        MeasureTheory.processToTimeSpaceFun
          ((predictableSimpleProcessCutoffBefore K t :
              MeasureTheory.PredictableSimpleProcess ℱ) : Process) := by
    simpa [MeasureTheory.predictableSimpleProcessToL2_coe] using
      MeasureTheory.MemLp.coeFn_toLp hCut_simple_memLp
  exact (processLpCutoffBefore_coeFn μ t
    (hK_memLp.toLp (MeasureTheory.processToTimeSpaceFun (K : Process)))).trans
      (hIndicatorToK.trans (hKToCut.trans hCutToLp.symm))

/-- Helper for Definition 25.10: on globally square-integrable predictable simple integrands, the
ambient deterministic-time cutoff stays inside the canonical `L²(μ ⊗ dt)` subspace. -/
private theorem processLpCutoffBefore_map_le_predictableSimpleProcessL2
    {ℱ : TimeFiltration} {μ : Measure Ω} (t : NNReal) :
    (MeasureTheory.predictableSimpleProcessL2 ℱ μ).map
        (processLpCutoffBefore μ t).toLinearMap ≤
      MeasureTheory.predictableSimpleProcessL2 ℱ μ := by
  intro H hH
  rcases hH with ⟨H', hH', rfl⟩
  rcases hH' with ⟨K, hK_memLp, rfl⟩
  have hCut_simple_memLp :
      MemLp
        (MeasureTheory.processToTimeSpaceFun
          ((predictableSimpleProcessCutoffBefore K t :
              MeasureTheory.PredictableSimpleProcess ℱ) : Process))
        (2 : ℝ≥0∞) (MeasureTheory.processMeasure μ) :=
    memLp_predictableSimpleProcessCutoffBefore t K hK_memLp
  have hCut_eq :
      processLpCutoffBefore μ t
          (hK_memLp.toLp (MeasureTheory.processToTimeSpaceFun (K : Process))) =
        ((MeasureTheory.predictableSimpleProcessToL2
            (predictableSimpleProcessCutoffBefore K t) hCut_simple_memLp :
            MeasureTheory.predictableSimpleProcessL2 ℱ μ) :
          Lp ℝ 2 (MeasureTheory.processMeasure μ)) :=
    processLpCutoffBefore_eq_predictableSimpleProcessToL2 t K hK_memLp hCut_simple_memLp
  have hCut_mem :
      (((MeasureTheory.predictableSimpleProcessToL2
            (predictableSimpleProcessCutoffBefore K t) hCut_simple_memLp :
            MeasureTheory.predictableSimpleProcessL2 ℱ μ) :
          Lp ℝ 2 (MeasureTheory.processMeasure μ))) ∈
        (MeasureTheory.predictableSimpleProcessL2 ℱ μ :
          Set (Lp ℝ 2 (MeasureTheory.processMeasure μ))) :=
    (MeasureTheory.predictableSimpleProcessToL2
      (predictableSimpleProcessCutoffBefore K t) hCut_simple_memLp).2
  exact hCut_eq ▸ hCut_mem

/-- Helper for Definition 25.10: the realized closure of globally square-integrable predictable
simple integrands is invariant under the ambient deterministic-time cutoff. -/
private theorem processLpCutoffBefore_closure_invtSubmodule
    {ℱ : TimeFiltration} {μ : Measure Ω} (t : NNReal) :
    PredictableSimpleProcessL2Closure ℱ μ ∈
      Module.End.invtSubmodule (processLpCutoffBefore μ t) := by
  have hsimple :
      predictableSimpleProcessL2 ℱ μ ∈ Module.End.invtSubmodule (processLpCutoffBefore μ t) := by
    rw [Module.End.mem_invtSubmodule_iff_map_le]
    exact processLpCutoffBefore_map_le_predictableSimpleProcessL2 (μ := μ) (ℱ := ℱ) t
  exact Submodule.topologicalClosure_mem_invtSubmodule hsimple

/-- Helper for Definition 25.10: the ambient deterministic-time cutoff of a closure point stays
in the realized closure of predictable simple integrands. -/
private theorem processLpCutoffBefore_mem_closure
    {ℱ : TimeFiltration} {μ : Measure Ω} (t : NNReal)
    (H : PredictableSimpleProcessL2Closure ℱ μ) :
    processLpCutoffBefore μ t H ∈ PredictableSimpleProcessL2Closure ℱ μ := by
  have hclosure :
      PredictableSimpleProcessL2Closure ℱ μ ≤
        (PredictableSimpleProcessL2Closure ℱ μ).comap
          (processLpCutoffBefore μ t).toLinearMap :=
    processLpCutoffBefore_closure_invtSubmodule (μ := μ) (ℱ := ℱ) t
  exact hclosure H.2

/-- The canonical deterministic cutoff operator `H ↦ H^(t)` on the realized closure
`\overline{\mathcal E} ⊆ L²(μ ⊗ dt)`. -/
noncomputable def _root_.MeasureTheory.PredictableSimpleProcessL2Closure.cutoffBefore
    {ℱ : TimeFiltration} {μ : Measure Ω} (t : NNReal) :
    PredictableSimpleProcessL2Closure ℱ μ →L[ℝ]
      PredictableSimpleProcessL2Closure ℱ μ :=
  ((processLpCutoffBefore μ t).comp (PredictableSimpleProcessL2Closure ℱ μ).subtypeL).codRestrict
    (PredictableSimpleProcessL2Closure ℱ μ)
    (processLpCutoffBefore_mem_closure t)

/-- Coercing the canonical cutoff operator on the closure to ambient `L²(μ ⊗ dt)` gives the
actual time-indicator cutoff `H · 1_[0,t]`. -/
theorem _root_.MeasureTheory.PredictableSimpleProcessL2Closure.cutoffBefore_coeFn
    {ℱ : TimeFiltration} {μ : Measure Ω} (t : NNReal)
    (H : PredictableSimpleProcessL2Closure ℱ μ) :
    (((MeasureTheory.PredictableSimpleProcessL2Closure.cutoffBefore t H :
          PredictableSimpleProcessL2Closure ℱ μ) :
        Lp ℝ 2 (processMeasure μ)) : Ω × ℝ → ℝ) =ᵐ[processMeasure μ]
      Set.indicator {x : Ω × ℝ | x.2 ≤ (t : ℝ)} fun x ↦
        (((H : PredictableSimpleProcessL2Closure ℱ μ) : Lp ℝ 2 (processMeasure μ)) x) := by
  -- Proof comment: the closure-side cutoff only packages the closure-membership proof; its
  -- ambient `L²` representative is exactly the cutoff image from the ambient operator.
  simpa [MeasureTheory.PredictableSimpleProcessL2Closure.cutoffBefore, processLpCutoffSet] using
    processLpCutoffBefore_coeFn μ t
      (((H : PredictableSimpleProcessL2Closure ℱ μ) : Lp ℝ 2 (processMeasure μ)))

/-- Definition 25.10: a Brownian Itô integral is the canonical terminal continuous linear map on
`\overline{\mathcal E}` extending the terminal Brownian elementary integral from Definition 25.3
on globally square-integrable predictable simple processes. -/
class BrownianItoIntegral
    (μ : Measure Ω) (ℱ : TimeFiltration) (W : Process)
    extends PredictableSimpleProcessL2Closure ℱ μ →L[ℝ] Lp ℝ 2 μ where
  /-- On an actual globally square-integrable predictable simple process, the closure-side
  terminal map agrees almost everywhere with the Brownian elementary integral from
  Definition 25.3. -/
  ae_eq_brownianElementaryIntegralAtInfinity
      (H : MeasureTheory.PredictableSimpleProcess ℱ)
      (hH : MemLp (MeasureTheory.processToTimeSpaceFun (H : Process)) (2 : ℝ≥0∞)
        (MeasureTheory.processMeasure μ)) :
      ((toContinuousLinearMap
        (predictableSimpleProcessL2ToClosure
          (predictableSimpleProcessToL2 H hH))) :
        Ω → ℝ) =ᵐ[μ]
      MeasureTheory.brownianElementaryIntegralAtInfinity W H

section ItoIntegral

variable {μ : Measure Ω}

/-- Source-facing bridge for Definition 25.10: if a sequence of globally square-integrable
predictable simple processes converges in the canonical closure of
`MeasureTheory.predictableSimpleProcessL2 ℱ μ`, then their terminal Brownian integrals converge
to the Brownian Itô integral of the limit closure point. -/
theorem brownianItoIntegral_tendsto_of_closureApproximation
    {ℱ : TimeFiltration} {W : Process}
    [hIto : BrownianItoIntegral μ ℱ W]
    {Hbar : PredictableSimpleProcessL2Closure ℱ μ}
    {Hs : ℕ → MeasureTheory.PredictableSimpleProcess ℱ}
    {hHs_mem :
      ∀ n,
        MemLp (MeasureTheory.processToTimeSpaceFun ((Hs n : Process))) (2 : ℝ≥0∞)
          (MeasureTheory.processMeasure μ)}
    (hHs :
      Tendsto
        (fun n ↦
          predictableSimpleProcessL2ToClosure
            (predictableSimpleProcessToL2 (Hs n) (hHs_mem n)))
        atTop (nhds Hbar)) :
    Tendsto
      (fun n ↦
        hIto.toContinuousLinearMap
          (predictableSimpleProcessL2ToClosure
            (predictableSimpleProcessToL2 (Hs n) (hHs_mem n))))
      atTop (nhds (hIto.toContinuousLinearMap Hbar)) :=
  (hIto.toContinuousLinearMap.continuous.tendsto Hbar).comp hHs

/-- The textbook process `\tilde I^W(H)` on the canonical closure, defined by
`\tilde I_t^W(H) = I_∞^W(H^(t))`. -/
noncomputable def brownianItoIntegralTruncatedProcess
    {ℱ : TimeFiltration} (W : Process)
    [hIto : BrownianItoIntegral μ ℱ W]
    (H : PredictableSimpleProcessL2Closure ℱ μ) :
    NNReal → Ω → ℝ :=
  fun t ↦ hIto.toContinuousLinearMap
    (PredictableSimpleProcessL2Closure.cutoffBefore t H)

/-- The truncation `H^(τ)` of a process `H` before a stopping time `τ`, given by
`H_t 1_{ {t ≤ τ} }`. This is not the stopped process `t ↦ H (min t τ)`. -/
def processBeforeStoppingTime (H : NNReal → Ω → ℝ) (τ : Ω → ENNReal) :
    NNReal → Ω → ℝ :=
  fun t ↦ Set.indicator {ω | (t : ENNReal) ≤ τ ω} (H t)

omit mΩ in
/-- Evaluating `processBeforeStoppingTime H τ` gives the textbook truncation formula
`H_t 1_{ {t ≤ τ} }`. -/
theorem processBeforeStoppingTime_apply (H : NNReal → Ω → ℝ) (τ : Ω → ENNReal)
    (t : NNReal) (ω : Ω) :
    processBeforeStoppingTime H τ t ω = if (t : ENNReal) ≤ τ ω then H t ω else 0 := by
  by_cases h : (t : ENNReal) ≤ τ ω
  · simp [processBeforeStoppingTime, h]
  · simp [processBeforeStoppingTime, h]

omit mΩ in
/-- If two processes agree at all times up to the stopping time `τ`, then their cutoff
integrands before `τ` coincide. -/
theorem processBeforeStoppingTime_congr
    {H G : NNReal → Ω → ℝ} {τ : Ω → ENNReal}
    (hEq : ∀ (t : NNReal) ω, (t : ENNReal) ≤ τ ω → H t ω = G t ω) :
    processBeforeStoppingTime H τ = processBeforeStoppingTime G τ := by
  funext t ω
  by_cases h : (t : ENNReal) ≤ τ ω
  · simp [processBeforeStoppingTime, h, hEq t ω h]
  · simp [processBeforeStoppingTime, h]

end ItoIntegral

end ProbabilityTheory
