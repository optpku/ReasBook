/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Books.ProbabilityTheory_Klenke_2020.Items.Chap09.Definition_9_10
import Books.ProbabilityTheory_Klenke_2020.Items.Chap12.Definition_12_20
import Books.ProbabilityTheory_Klenke_2020.Items.Chap08.Equation_8_6

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory

noncomputable section

universe u v w

namespace ProbabilityTheory

variable {Ω : Type u} [mΩ : MeasurableSpace Ω]
variable {T : Type v} [LinearOrder T]
variable {E : Type w} [mE : MeasurableSpace E]

/-- Helper for Remark 17.2: a process has the natural Markov property under `μ` if every
coordinate is measurable and, for each measurable one-time future event, conditioning on the
whole history up to `s` agrees almost surely with conditioning only on the present state `X s`. -/
def HasNaturalMarkovProperty
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : T → Ω → E) : Prop :=
  (∀ t : T, Measurable (X t)) ∧
    ∀ ⦃s u : T⦄, s ≤ u → ∀ ⦃A : Set E⦄, MeasurableSet A →
      μ⟦X u ⁻¹' A | generatedFiltrationSpace X s⟧ =ᵐ[μ]
        μ⟦X u ⁻¹' A | MeasurableSpace.comap (X s) ‹MeasurableSpace E›⟧

/-- Helper for Remark 17.2: the present-state sigma-algebra is contained in the history
sigma-algebra at the same time. -/
lemma present_le_generatedFiltrationSpace (X : T → Ω → E) (t : T) :
    MeasurableSpace.comap (X t) ‹MeasurableSpace E› ≤ generatedFiltrationSpace X t := by
  -- Proof comment: the defining supremum for `generatedFiltrationSpace X t` already contains the
  -- present coordinate `σ(X t)`.
  exact le_iSup₂_of_le t le_rfl le_rfl

/-- Helper for Remark 17.2: if every coordinate is ambient-measurable, then the generated history
sigma-algebra is an ambient sub-sigma-algebra. -/
lemma generatedFiltrationSpace_le_ambient
    (X : T → Ω → E) (hX : ∀ t : T, Measurable (X t)) (t : T) :
    generatedFiltrationSpace X t ≤ ‹MeasurableSpace Ω› := by
  -- Proof comment: every coordinate sigma-algebra appearing in the history supremum is ambient
  -- because the corresponding coordinate map is measurable.
  refine iSup_le fun s ↦ iSup_le fun hs ↦ ?_
  exact (hX s).comap_le

/-- The event that a process realizes the prescribed finite history `states` at the times
`times`. -/
def finiteHistoryEvent {n : ℕ} (X : T → Ω → E) (times : Fin (n + 1) → T)
    (states : Fin (n + 1) → E) : Set Ω :=
  {ω | ∀ k, X (times k) ω = states k}

/-- In a countable state space, the remark's formulation of the Markov property says that for every
strictly increasing finite history with positive probability, the conditional probability of the
future state depends only on the last observed state. -/
def HasFiniteHistoryMarkovProperty (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : T → Ω → E) : Prop :=
  (∀ t, Measurable (X t)) ∧
    ∀ {n : ℕ} (times : Fin (n + 1) → T), StrictMono times → ∀ {t : T}, times (Fin.last n) < t →
      ∀ (states : Fin (n + 1) → E) (i : E),
        0 < μ (finiteHistoryEvent X times states) →
          μ[{ω | X t ω = i} | finiteHistoryEvent X times states] =
            μ[{ω | X t ω = i} | {ω | X (times (Fin.last n)) ω = states (Fin.last n)}]

/-- Helper for Remark 17.2: `finiteHistoryEvent X times states` is the singleton fiber of the
history tuple `ω ↦ (k ↦ X (times k) ω)`. -/
lemma finiteHistoryEvent_eq_preimage_historyTuple {n : ℕ} (X : T → Ω → E)
    (times : Fin (n + 1) → T) (states : Fin (n + 1) → E) :
    finiteHistoryEvent X times states = (fun ω k ↦ X (times k) ω) ⁻¹' {states} := by
  -- Proof comment: prescribing the whole finite history is exactly requiring the history tuple to
  -- hit the singleton value `states`.
  ext ω
  simp [finiteHistoryEvent, funext_iff]

/-- Helper for Remark 17.2: the finite-history tuple is measurable once each process coordinate is
measurable. -/
lemma measurable_historyTuple {n : ℕ} (X : T → Ω → E) (times : Fin (n + 1) → T)
    (hX : ∀ t, Measurable (X t)) :
    Measurable (fun ω k ↦ X (times k) ω) := by
  -- Proof comment: a map into a finite product is measurable once each coordinate is measurable.
  refine measurable_pi_lambda _ fun k ↦ ?_
  exact hX (times k)

/-- Helper for Remark 17.2: the last observed state is a measurable factor of the whole history
tuple. -/
lemma lastState_comap_le_historyTuple {n : ℕ} (X : T → Ω → E) (times : Fin (n + 1) → T) :
    MeasurableSpace.comap (X (times (Fin.last n))) inferInstance ≤
      MeasurableSpace.comap (fun ω k ↦ X (times k) ω) inferInstance := by
  -- Proof comment: the last observed state is the last coordinate projection of the history tuple.
  let _ : MeasurableSpace Ω := MeasurableSpace.comap (fun ω k ↦ X (times k) ω) inferInstance
  have hproj :
      Measurable[MeasurableSpace.comap (fun ω k ↦ X (times k) ω) inferInstance]
        (fun ω ↦ X (times (Fin.last n)) ω) := by
    simpa using
      ((measurable_pi_apply (Fin.last n) :
        Measurable fun z : Fin (n + 1) → E ↦ z (Fin.last n)).comp
        (Measurable.of_comap_le le_rfl))
  simpa using hproj.comap_le

/-- Helper for Remark 17.2: the finite-history tuple is measurable with respect to the generated
filtration at its terminal time. -/
lemma historyTuple_comap_le_generatedFiltrationSpace {n : ℕ} (X : T → Ω → E)
    (times : Fin (n + 1) → T) (htimes : StrictMono times) :
    MeasurableSpace.comap (fun ω k ↦ X (times k) ω) inferInstance ≤
      generatedFiltrationSpace X (times (Fin.last n)) := by
  -- Proof comment: every coordinate of the history tuple comes from a time at most the terminal
  -- time `times (Fin.last n)`, so the tuple is measurable for that generated filtration.
  let _ : MeasurableSpace Ω := generatedFiltrationSpace X (times (Fin.last n))
  have hmeas :
      Measurable[generatedFiltrationSpace X (times (Fin.last n))]
        (fun ω k ↦ X (times k) ω) := by
    refine measurable_pi_iff.2 fun k ↦ ?_
    refine measurable_iff_comap_le.mpr ?_
    exact le_iSup_of_le (times k) <| le_iSup_of_le
      (htimes.monotone (Fin.le_last k)) le_rfl
  simpa using hmeas.comap_le

/-- Helper for Remark 17.2: a finite-history atom is measurable once every process coordinate is
measurable. -/
lemma measurableSet_finiteHistoryEvent {n : ℕ} (X : T → Ω → E)
    [MeasurableSingletonClass E]
    (times : Fin (n + 1) → T) (states : Fin (n + 1) → E) (hX : ∀ t, Measurable (X t)) :
    MeasurableSet (finiteHistoryEvent X times states) := by
  -- Proof comment: the history event is the preimage of the measurable singleton `{states}`
  -- under the finite intersection of coordinate singleton fibers.
  simpa [finiteHistoryEvent, Set.setOf_forall] using
    MeasurableSet.iInter fun k ↦ (hX (times k)) (measurableSet_singleton (states k))

/-- Helper for Remark 17.2: every finite-history atom lies inside the fiber of its terminal
observed state. -/
lemma finiteHistoryEvent_subset_terminalFiber {n : ℕ} (X : T → Ω → E)
    (times : Fin (n + 1) → T) (states : Fin (n + 1) → E) :
    finiteHistoryEvent X times states ⊆
      {ω | X (times (Fin.last n)) ω = states (Fin.last n)} := by
  -- Proof comment: any realization of the whole history in particular realizes the terminal
  -- coordinate of that history.
  intro ω hω
  exact hω (Fin.last n)

/-- Helper for Remark 17.2: on a countable measurable-singleton state space, the sigma-algebra on
`E` is generated by singleton sets. -/
lemma generateFrom_range_singleton_eq_self [Countable E] [MeasurableSingletonClass E] :
    MeasurableSpace.generateFrom (Set.range fun x : E ↦ ({x} : Set E)) = ‹MeasurableSpace E› :=
  by
  -- Proof comment: on a countable state space, every set is a countable union of measurable
  -- singletons, so the singleton generator already recovers the whole measurable space.
  refine le_antisymm ?_ ?_
  · refine MeasurableSpace.generateFrom_le ?_
    rintro s ⟨x, rfl⟩
    exact measurableSet_singleton x
  · intro s hs
    have hs_union : s = ⋃ x : s, ({x.1} : Set E) := by
      ext y
      simp
    rw [hs_union]
    refine MeasurableSet.iUnion fun x ↦ ?_
    exact MeasurableSpace.measurableSet_generateFrom ⟨x.1, rfl⟩

/-- Helper for Remark 17.2: `σ(Y)` can be rewritten as the `generateFrom` of the singleton fibers
`{ω | Y ω = x}` when the state space is countable with measurable singletons. -/
lemma comap_eq_generateFrom_singletonFibers [Countable E] [MeasurableSingletonClass E]
    (Y : Ω → E) :
    MeasurableSpace.comap Y ‹MeasurableSpace E› =
      MeasurableSpace.generateFrom (Set.range fun x : E ↦ {ω | Y ω = x}) := by
  -- Proof comment: pull back the singleton-generated sigma-algebra on `E` along `Y`.
  calc
    MeasurableSpace.comap Y ‹MeasurableSpace E›
      = MeasurableSpace.comap Y
          (MeasurableSpace.generateFrom (Set.range fun x : E ↦ ({x} : Set E))) := by
            rw [generateFrom_range_singleton_eq_self]
    _ = MeasurableSpace.generateFrom (Set.range fun x : E ↦ {ω | Y ω = x}) := by
          rw [MeasurableSpace.comap_generateFrom]
          congr 1
          ext s
          constructor
          · rintro ⟨t, ⟨x, rfl⟩, rfl⟩
            exact ⟨x, rfl⟩
          · rintro ⟨x, rfl⟩
            exact ⟨{x}, ⟨x, rfl⟩, rfl⟩

/-- Helper for Remark 17.2: the history sigma-algebra up to `s` is generated by the singleton
coordinate fibers `{ω | X r ω = j}` over past times `r ≤ s`, with `∅` inserted so the family is a
`π`-system componentwise. -/
lemma generatedFiltrationSpace_eq_generateFromPastSingletonFiberEvents
    [Countable E] [MeasurableSingletonClass E]
    (X : T → Ω → E) (s : T) :
    generatedFiltrationSpace X s =
      MeasurableSpace.generateFrom
        (⋃ r : {r : T // r ≤ s},
          insert ∅ (Set.range fun j : E ↦ {ω | X r.1 ω = j})) := by
  -- Proof comment: each past coordinate sigma-algebra is generated by its singleton fibers, and
  -- the history sigma-algebra is the supremum of those past coordinate sigma-algebras.
  calc
    generatedFiltrationSpace X s
      = ⨆ r : {r : T // r ≤ s}, MeasurableSpace.comap (X r.1) inferInstance := by
          simp [generatedFiltrationSpace, iSup_subtype]
    _ = ⨆ r : {r : T // r ≤ s},
          MeasurableSpace.generateFrom
            (insert ∅ (Set.range fun j : E ↦ {ω | X r.1 ω = j})) := by
          refine iSup_congr fun r ↦ ?_
          rw [comap_eq_generateFrom_singletonFibers]
          rw [MeasurableSpace.generateFrom_insert_empty]
    _ = MeasurableSpace.generateFrom
          (⋃ r : {r : T // r ≤ s},
            insert ∅ (Set.range fun j : E ↦ {ω | X r.1 ω = j})) := by
          rw [MeasurableSpace.iSup_generateFrom]

/-- Helper for Remark 17.2: for a fixed past time `r ≤ s`, the family consisting of `∅` together
with the singleton fibers `{ω | X r ω = j}` is a `π`-system. -/
lemma isPiSystem_insert_empty_singletonFibers (X : T → Ω → E) {s : T}
    (r : {r : T // r ≤ s}) :
    IsPiSystem (insert ∅ (Set.range fun j : E ↦ {ω | X r.1 ω = j})) := by
  -- Proof comment: two singleton fibers either coincide, giving the same fiber, or are disjoint,
  -- giving the explicitly inserted empty set.
  intro A hA B hB hAB
  rcases hA with rfl | ⟨i, rfl⟩
  · simp
  · rcases hB with rfl | ⟨j, rfl⟩
    · simp [Set.inter_comm]
    · by_cases hij : i = j
      · subst hij
        refine Or.inr ?_
        exact ⟨i, by ext ω; simp⟩
      · refine Or.inl ?_
        ext ω
        constructor
        · intro hω
          rcases hω with ⟨hi, hj⟩
          exact (hij (hi.symm.trans hj)).elim
        · intro hω
          exact False.elim hω

/-- Helper for Remark 17.2: every element of the generated past singleton-fiber `π`-system is
either empty or a finite intersection of singleton fibers over finitely many past times. -/
lemma mem_pastSingletonFiberPiSystem_elim [Nonempty E] (X : T → Ω → E) (s : T) {D : Set Ω}
    (hD :
      D ∈ generatePiSystem
        (⋃ r : {r : T // r ≤ s},
          insert ∅ (Set.range fun j : E ↦ {ω | X r.1 ω = j}))) :
    D = ∅ ∨
      ∃ S : Finset {r : T // r ≤ s}, ∃ ξ : {r : T // r ≤ s} → E,
        D = ⋂ r ∈ S, {ω | X r.1 ω = ξ r} := by
  classical
  have hPi :
      ∀ r : {r : T // r ≤ s},
        IsPiSystem (insert ∅ (Set.range fun j : E ↦ {ω | X r.1 ω = j})) :=
    fun r ↦ isPiSystem_insert_empty_singletonFibers X r
  rcases
      @mem_generatePiSystem_iUnion_elim Ω {r : T // r ≤ s}
        (fun r : {r : T // r ≤ s} ↦
          insert ∅ (Set.range fun j : E ↦ {ω | X r.1 ω = j}))
        hPi D hD with
    ⟨S, F, hEq, hF⟩
  by_cases hEmpty : ∃ r ∈ S, F r = ∅
  · left
    rcases hEmpty with ⟨r, hrS, hrEmpty⟩
    ext ω
    constructor
    · intro hω
      have hω' : ω ∈ ⋂ b ∈ S, F b := by simpa [hEq] using hω
      have hFr : ω ∈ F r := by
        have hω'' : ∀ a (ha : a ≤ s), ⟨a, ha⟩ ∈ S → ω ∈ F ⟨a, ha⟩ := by
          simpa [Set.mem_iInter] using hω'
        exact hω'' r.1 r.2 hrS
      simp [hrEmpty] at hFr
    · intro hω
      simp at hω
  · right
    have hRange :
        ∀ r ∈ S, ∃ j : E, F r = {ω | X r.1 ω = j} := by
      intro r hrS
      rcases hF r hrS with hr | hr
      · exact False.elim (hEmpty ⟨r, hrS, hr⟩)
      · rcases hr with ⟨j, hj⟩
        exact ⟨j, hj.symm⟩
    let ξ : {r : T // r ≤ s} → E := fun r ↦
      if hrS : r ∈ S then Classical.choose (hRange r hrS) else Classical.arbitrary E
    have hξ :
        ∀ r ∈ S, F r = {ω | X r.1 ω = ξ r} := by
      intro r hrS
      have hchoice := Classical.choose_spec (hRange r hrS)
      have hξr : ξ r = Classical.choose (hRange r hrS) := by
        simp [ξ, hrS]
      rw [hξr]
      exact hchoice
    refine ⟨S, ξ, ?_⟩
    ext ω
    constructor
    · intro hω
      have hω' : ω ∈ ⋂ b ∈ S, F b := by simpa [hEq] using hω
      have hω'' : ∀ r, r ∈ S → ω ∈ F r := by
        intro r hrS
        have hω''' : ∀ a (ha : a ≤ s), ⟨a, ha⟩ ∈ S → ω ∈ F ⟨a, ha⟩ := by
          simpa [Set.mem_iInter] using hω'
        exact hω''' r.1 r.2 hrS
      have : ∀ r, r ∈ S → X r.1 ω = ξ r := by
        intro r hrS
        simpa [hξ r hrS] using hω'' r hrS
      simpa [Set.mem_iInter] using this
    · intro hω
      have hω' : ∀ r, r ∈ S → X r.1 ω = ξ r := by
        simpa [Set.mem_iInter] using hω
      have : ∀ r, r ∈ S → ω ∈ F r := by
        intro r hrS
        simpa [hξ r hrS] using hω' r hrS
      have hmem : ω ∈ ⋂ b ∈ S, F b := by
        simpa [Set.mem_iInter] using this
      simpa [hEq] using hmem

/-- Helper for Remark 17.2: a finite intersection of singleton fibers over past times is either
`Set.univ` (for the empty intersection) or one finite-history event in increasing time order. -/
lemma pastSingletonFiberInter_eq_univ_or_finiteHistoryEvent [Nonempty E] (X : T → Ω → E) {s : T}
    (S : Finset {r : T // r ≤ s}) (ξ : {r : T // r ≤ s} → E) :
    (⋂ r ∈ S, {ω | X r.1 ω = ξ r}) = Set.univ ∨
      ∃ n : ℕ, ∃ times : Fin (n + 1) → T, StrictMono times ∧
        ∃ states : Fin (n + 1) → E,
          times (Fin.last n) ≤ s ∧
            (⋂ r ∈ S, {ω | X r.1 ω = ξ r}) = finiteHistoryEvent X times states := by
  classical
  by_cases hS : S = ∅
  · left
    subst hS
    ext ω
    simp
  · right
    have hcardPos : 0 < S.card :=
      Finset.card_pos.2 (Finset.nonempty_iff_ne_empty.mpr hS)
    let e :
        Fin (Nat.succ (S.card - 1)) ≃o ↥S :=
      S.orderIsoOfFin (Nat.succ_pred_eq_of_pos hcardPos).symm
    let times : Fin (Nat.succ (S.card - 1)) → T := fun k ↦ (e k).1.1
    let states : Fin (Nat.succ (S.card - 1)) → E := fun k ↦ ξ (e k).1
    refine ⟨S.card - 1, times, ?_, states, ?_, ?_⟩
    · -- Proof comment: the order is inherited from the order isomorphism enumerating `S`.
      intro i j hij
      exact (e.strictMono hij : (e i).1 < (e j).1)
    · -- Proof comment: the last enumerated time still lies in the past-time subtype `{r // r ≤ s}`.
      exact (e (Fin.last (S.card - 1))).1.2
    · -- Proof comment: the finite intersection is exactly the finite-history atom indexed by the
      -- increasing enumeration of `S`.
      ext ω
      constructor
      · intro hω
        have hω' : ∀ r, r ∈ S → X r.1 ω = ξ r := by
          simpa [Set.mem_iInter] using hω
        intro k
        exact hω' ((e k).1) ((e k).2)
      · intro hω
        have hω' : ∀ k, X (times k) ω = states k := hω
        have : ∀ r, r ∈ S → X r.1 ω = ξ r := by
          intro r hrS
          obtain ⟨k, hk⟩ := e.surjective ⟨r, hrS⟩
          have hk' : (e k).1 = r := by
            simpa using congrArg Subtype.val hk
          simpa [times, states, hk'] using hω' k
        simpa [Set.mem_iInter] using this

/-- Helper for Remark 17.2: averaging the indicator of a measurable event over the conditioning
fiber set `s` gives the scalar conditional probability of that event under `μ[|s]`. -/
lemma setAverage_indicator_eq_condReal
    (μ : Measure Ω) [IsProbabilityMeasure μ] {s t : Set Ω} (ht : MeasurableSet t) :
    ⨍ x in s, t.indicator (fun _ ↦ (1 : ℝ)) x ∂μ = (μ[|s]).real t := by
  by_cases hs0 : μ s = 0
  · -- Proof comment: when the conditioning event has zero mass, both the normalized average and
    -- the conditional probability are definitionally zero.
    have hcond0 : μ[|s] = 0 := ProbabilityTheory.cond_eq_zero_of_meas_eq_zero hs0
    have hsreal0 : μ.real s = 0 := by
      simp [MeasureTheory.measureReal_def, hs0]
    simp [MeasureTheory.setAverage_eq, hsreal0, hcond0]
  · -- Proof comment: otherwise both sides reduce to the same normalized mass
    -- `μ(s ∩ t) / μ(s)`.
    have hIndicator :
        ∫ x in s, t.indicator (fun _ ↦ (1 : ℝ)) x ∂μ =
          ∫ x in s ∩ t, (fun _ ↦ (1 : ℝ)) x ∂μ := by
      exact MeasureTheory.setIntegral_indicator ht
    rw [MeasureTheory.setAverage_eq,
      hIndicator,
      MeasureTheory.setIntegral_const, smul_eq_mul, smul_eq_mul, mul_one,
      MeasureTheory.measureReal_def]
    change (μ s).toReal⁻¹ * μ.real (s ∩ t) = ((μ[|s]) t).toReal
    rw [ProbabilityTheory.cond_apply' ht μ]
    rw [ENNReal.toReal_mul, ENNReal.toReal_inv, MeasureTheory.measureReal_def]

/-- Helper for Remark 17.2: integrating the `σ(X s)`-conditional expectation of a future event
over a measurable subset of the fiber `{X s = j}` collapses to the fiberwise conditional
probability times the mass of that subset. -/
lemma condExp_futureEvent_eq_condProb_on_presentFiber [Countable E] [MeasurableSingletonClass E]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : T → Ω → E)
    {s t : T} (hXs : Measurable (X s)) (hXt : Measurable (X t))
    {A : Set E} (hA : MeasurableSet A) (j : E) {C : Set Ω} (hC : MeasurableSet C)
    (hCsub : C ⊆ {ω | X s ω = j}) :
    (∫ ω in C, (μ⟦X t ⁻¹' A | MeasurableSpace.comap (X s) ‹MeasurableSpace E›⟧) ω ∂μ) =
      μ.real C * (μ[|{ω | X s ω = j}]).real (X t ⁻¹' A) := by
  -- Route correction: the earlier restricted-AE route was too strong. Equation 8.6 is only used
  -- here through its set-integral consequence on one measurable subset of a present-state fiber.
  let B : E → Set Ω := fun i ↦ X s ⁻¹' ({i} : Set E)
  let event : Set Ω := X t ⁻¹' A
  have hEvent : MeasurableSet event := by
    simpa [event] using hXt hA
  have hEventInt : Integrable (event.indicator (fun _ ↦ (1 : ℝ))) μ :=
    (integrable_const (1 : ℝ)).indicator hEvent
  have hPartition :
      μ⟦event | MeasurableSpace.comap (X s) ‹MeasurableSpace E›⟧ =ᵐ[μ]
        fun ω ↦
          ∑' i, (B i).indicator
            (fun _ ↦ ⨍ x in B i, event.indicator (fun _ ↦ (1 : ℝ)) x ∂μ) ω := by
    -- Proof comment: rewrite `σ(X s)` as the singleton-fiber partition and invoke Equation 8.6.
    simpa [event, B, comap_eq_generateFrom_singletonFibers (X s)] using
      (condExp_generateFrom_ae_eq_countable_partition_formula
        μ B
        (fun i ↦ by simpa [B] using hXs (measurableSet_singleton i))
        (fun i k hik ↦ by
          refine Set.disjoint_left.2 ?_
          intro ω hωi hωk
          exact hik (hωi.symm.trans hωk))
        (by
          ext ω
          simp [B])
        hEventInt)
  have hCollapse :
      ∀ᵐ ω ∂μ,
        ω ∈ C →
          (∑' i, (B i).indicator
              (fun _ ↦ ⨍ x in B i, event.indicator (fun _ ↦ (1 : ℝ)) x ∂μ) ω) =
            ⨍ x in B j, event.indicator (fun _ ↦ (1 : ℝ)) x ∂μ := by
    -- Proof comment: on `C`, the point lies in the `j`-th singleton fiber, so every other atom
    -- in the partition formula vanishes.
    filter_upwards with ω hωC
    have hωj : ω ∈ B j := by
      simpa [B] using hCsub hωC
    rw [tsum_eq_single j]
    · simp [B, hωj]
    · intro i hij
      have hωi : ω ∉ B i := by
        intro hωi
        have hωi' : X s ω = i := by
          simpa [B] using hωi
        have hωj' : X s ω = j := by
          simpa [B] using hωj
        exact hij (hωi'.symm.trans hωj')
      simp [B, hωi]
  calc
    ∫ ω in C, (μ⟦X t ⁻¹' A | MeasurableSpace.comap (X s) ‹MeasurableSpace E›⟧) ω ∂μ
        =
          ∫ ω in C,
            (∑' i, (B i).indicator
              (fun _ ↦ ⨍ x in B i, event.indicator (fun _ ↦ (1 : ℝ)) x ∂μ) ω) ∂μ := by
            exact setIntegral_congr_ae hC (hPartition.mono fun _ hω _ ↦ hω)
    _ = ∫ ω in C, (⨍ x in B j, event.indicator (fun _ ↦ (1 : ℝ)) x ∂μ) ∂μ := by
          exact setIntegral_congr_ae hC hCollapse
    _ = μ.real C * (⨍ x in B j, event.indicator (fun _ ↦ (1 : ℝ)) x ∂μ) := by
          rw [MeasureTheory.setIntegral_const, smul_eq_mul]
    _ = μ.real C * (μ[|B j]).real event := by
          rw [setAverage_indicator_eq_condReal μ hEvent]
    _ = μ.real C * (μ[|{ω | X s ω = j}]).real (X t ⁻¹' A) := by
          rfl

/-- Helper for Remark 17.2: intersecting a finite-history event with the present-state fiber
`{X s = j}` appends the observation `(s, j)` to the history. -/
lemma finiteHistoryEvent_inter_present_eq_snoc {n : ℕ} (X : T → Ω → E)
    (times : Fin (n + 1) → T) (states : Fin (n + 1) → E) (s : T) (j : E) :
    finiteHistoryEvent X times states ∩ {ω | X s ω = j} =
      finiteHistoryEvent X (Fin.snoc times s) (Fin.snoc states j) := by
  -- Proof comment: intersecting with the present-state fiber appends one more coordinate
  -- condition to the existing finite history.
  ext ω
  constructor
  · rintro ⟨hω, hsω⟩ k
    rcases Fin.eq_castSucc_or_eq_last k with ⟨k', rfl⟩ | rfl
    · simpa [Fin.snoc_castSucc] using hω k'
    · simpa [Fin.snoc_last] using hsω
  · intro hω
    refine ⟨?_, ?_⟩
    · intro k
      simpa [Fin.snoc_castSucc] using hω k.castSucc
    · simpa [Fin.snoc_last] using hω (Fin.last (n + 1))

/-- Helper for Remark 17.2: on a positive-probability finite-history atom, the singleton-state
version of the remark determines the full conditional law of `X u` on every measurable set
`A ⊆ E`. -/
lemma finiteHistory_conditionalProb_eq_present_of_measurableSet
    [Countable E] [MeasurableSingletonClass E]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : T → Ω → E)
    (hFin : HasFiniteHistoryMarkovProperty μ X)
    {n : ℕ} (times : Fin (n + 1) → T) (htimes : StrictMono times) {u : T}
    (htu : times (Fin.last n) < u) (states : Fin (n + 1) → E)
    {A : Set E} (hA : MeasurableSet A)
    (hμHist : 0 < μ (finiteHistoryEvent X times states)) :
    μ[X u ⁻¹' A | finiteHistoryEvent X times states] =
      μ[X u ⁻¹' A | {ω | X (times (Fin.last n)) ω = states (Fin.last n)}] := by
  -- Proof comment: compare the conditioned laws of `X u` on the countable state space `E`; the
  -- singleton-state hypothesis from `hFin` identifies every singleton mass of those laws.
  let H : Set Ω := finiteHistoryEvent X times states
  let F : Set Ω := {ω | X (times (Fin.last n)) ω = states (Fin.last n)}
  let νH : Measure E := (μ[|H]).map (X u)
  let νF : Measure E := (μ[|F]).map (X u)
  have hXu : Measurable (X u) := hFin.1 u
  have hMapEq : νH = νF := by
    -- Proof comment: on a countable state space, equality of measures is determined by
    -- singleton masses, which are exactly the singleton conditional probabilities from `hFin`.
    apply (MeasureTheory.ext_iff_measureReal_singleton).2
    intro i
    rw [MeasureTheory.map_measureReal_apply hXu (measurableSet_singleton i)]
    rw [MeasureTheory.map_measureReal_apply hXu (measurableSet_singleton i)]
    simpa [H, F, MeasureTheory.measureReal_def] using
      congrArg ENNReal.toReal (hFin.2 times htimes htu states i hμHist)
  -- Proof comment: evaluate the now-equal conditioned laws on the measurable event `A`.
  have hApplyEq : νH A = νF A := by
    exact congrArg (fun ν : Measure E ↦ ν A) hMapEq
  simpa [νH, νF, H, F, Measure.map_apply hXu hA] using hApplyEq

/-- Helper for Remark 17.2: the present-fiber set-integral identity specializes to singleton
future events. -/
lemma condExp_singletonFutureEvent_eq_condProb_on_presentFiber
    [Countable E] [MeasurableSingletonClass E]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : T → Ω → E)
    {s t : T} (hXs : Measurable (X s)) (hXt : Measurable (X t)) (i j : E)
    {C : Set Ω} (hC : MeasurableSet C) (hCsub : C ⊆ {ω | X s ω = j}) :
    (∫ ω in C, (μ⟦{ω | X t ω = i} | MeasurableSpace.comap (X s) ‹MeasurableSpace E›⟧) ω ∂μ) =
      μ.real C * (μ[|{ω | X s ω = j}]).real {ω | X t ω = i} := by
  -- Proof comment: this is the singleton specialization of the measurable-set present-fiber
  -- integral identity.
  simpa using
    condExp_futureEvent_eq_condProb_on_presentFiber
      μ X hXs hXt (measurableSet_singleton i) j hC hCsub

/-- Helper for Remark 17.2: the natural Markov property implies the finite-history conditional
probability identity. -/
lemma hasFiniteHistoryMarkovProperty_of_hasNaturalMarkovProperty
    [Countable E] [MeasurableSingletonClass E]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : T → Ω → E)
    (hNat : HasNaturalMarkovProperty μ X) :
    HasFiniteHistoryMarkovProperty μ X := by
  refine ⟨hNat.1, ?_⟩
  intro n times htimes t hlt states i hμHist
  let s : T := times (Fin.last n)
  let H : Set Ω := finiteHistoryEvent X times states
  let F : Set Ω := {ω | X s ω = states (Fin.last n)}
  let event : Set Ω := X t ⁻¹' ({i} : Set E)
  have hHmeas : MeasurableSet H := by
    simpa [H] using measurableSet_finiteHistoryEvent X times states hNat.1
  have hEvent : MeasurableSet event := by
    simpa [event] using hNat.1 t (measurableSet_singleton i)
  have hEventInt : Integrable (event.indicator (fun _ ↦ (1 : ℝ))) μ :=
    (integrable_const (1 : ℝ)).indicator hEvent
  have hmPast : generatedFiltrationSpace X s ≤ ‹MeasurableSpace Ω› := by
    exact generatedFiltrationSpace_le_ambient X hNat.1 s
  have hHpast : MeasurableSet[generatedFiltrationSpace X s] H := by
    -- Proof comment: the finite-history atom is measurable for the generated history at its
    -- terminal time because it is the preimage of a singleton under the history tuple.
    have hTupleMeas :
        Measurable[generatedFiltrationSpace X s] (fun ω k ↦ X (times k) ω) := by
      rw [measurable_iff_comap_le]
      simpa [s] using
        historyTuple_comap_le_generatedFiltrationSpace X times htimes
    simpa [H, finiteHistoryEvent_eq_preimage_historyTuple] using
      hTupleMeas (measurableSet_singleton states)
  have hNatEvent :
      μ⟦event | generatedFiltrationSpace X s⟧ =ᵐ[μ]
        μ⟦event | MeasurableSpace.comap (X s) ‹MeasurableSpace E›⟧ := by
    -- Proof comment: specialize the natural Markov property to the singleton future event.
    simpa [s, event] using
      hNat.2 (le_of_lt hlt) (measurableSet_singleton i)
  have hHsub : H ⊆ F := by
    simpa [H, F, s] using finiteHistoryEvent_subset_terminalFiber X times states
  have hPresentIntegral :
      ∫ ω in H, (μ⟦event | MeasurableSpace.comap (X s) ‹MeasurableSpace E›⟧) ω ∂μ =
        μ.real H * (μ[|F]).real event := by
    -- Proof comment: on the history atom, the present-state conditional expectation is constant
    -- because the whole atom sits inside the terminal-state fiber.
    simpa [H, F, s, event] using
      condExp_singletonFutureEvent_eq_condProb_on_presentFiber
        μ X (hNat.1 s) (hNat.1 t) i (states (Fin.last n)) hHmeas hHsub
  have hEventIntegral :
      ∫ ω in H, (event.indicator (fun _ ↦ (1 : ℝ))) ω ∂μ =
        μ.real H * (μ[|H]).real event := by
    -- Proof comment: the indicator integral on the history atom is the atom mass times the
    -- conditional probability on that atom.
      have hAverage :
          μ.real H • ⨍ ω in H, event.indicator (fun _ ↦ (1 : ℝ)) ω ∂μ =
            ∫ ω in H, (event.indicator (fun _ ↦ (1 : ℝ))) ω ∂μ := by
        exact MeasureTheory.measure_smul_setAverage
          (event.indicator (fun _ ↦ (1 : ℝ))) (measure_ne_top μ H)
      calc
        ∫ ω in H, (event.indicator (fun _ ↦ (1 : ℝ))) ω ∂μ
            = μ.real H * ⨍ ω in H, event.indicator (fun _ ↦ (1 : ℝ)) ω ∂μ := by
                rw [← hAverage, smul_eq_mul]
      _ = μ.real H * (μ[|H]).real event := by
            rw [setAverage_indicator_eq_condReal μ hEvent]
  have hRealEq : (μ[|H]).real event = (μ[|F]).real event := by
    have hHrealPos : 0 < μ.real H := by
      exact ENNReal.toReal_pos (ne_of_gt hμHist) (measure_ne_top μ H)
    apply mul_left_cancel₀ hHrealPos.ne'
    calc
      μ.real H * (μ[|H]).real event
          = ∫ ω in H, (event.indicator (fun _ ↦ (1 : ℝ))) ω ∂μ := hEventIntegral.symm
      _ = ∫ ω in H, (μ⟦event | generatedFiltrationSpace X s⟧) ω ∂μ := by
            symm
            exact MeasureTheory.setIntegral_condExp hmPast hEventInt hHpast
      _ = ∫ ω in H, (μ⟦event | MeasurableSpace.comap (X s) ‹MeasurableSpace E›⟧) ω ∂μ := by
            exact setIntegral_congr_ae hHmeas (hNatEvent.mono fun _ hω _ ↦ hω)
      _ = μ.real H * (μ[|F]).real event := hPresentIntegral
  have hMeasureEq :
      μ[event | H] = μ[event | F] := by
    have hMeasureEq' : (μ[|H]) event = (μ[|F]) event := by
      exact (MeasureTheory.measureReal_eq_measureReal_iff).mp hRealEq
    simpa using hMeasureEq'
  simpa [H, F, s, event] using hMeasureEq

/-- Helper for Remark 17.2: appending a later observation preserves strict monotonicity of the
time index. -/
lemma strictMono_snoc_of_last_lt {n : ℕ} {times : Fin (n + 1) → T}
    (htimes : StrictMono times) {s : T} (hs : times (Fin.last n) < s) :
    StrictMono (Fin.snoc times s) := by
  -- Proof comment: the old coordinates keep their strict order, and the new last coordinate is
  -- strictly larger than the previous terminal one.
  intro i j hij
  rcases Fin.eq_castSucc_or_eq_last j with ⟨j', rfl⟩ | rfl
  · rcases Fin.eq_castSucc_or_eq_last i with ⟨i', rfl⟩ | rfl
    · simpa using htimes hij
    · exact False.elim ((not_lt_of_ge (Fin.castSucc_lt_last j').le) hij)
  · rcases Fin.eq_castSucc_or_eq_last i with ⟨i', rfl⟩ | rfl
    · simpa [Fin.snoc_castSucc, Fin.snoc_last] using
        (lt_of_le_of_lt (htimes.monotone (Fin.le_last i')) hs)
    · exact (lt_irrefl _ hij).elim

/-- Helper for Remark 17.2: a history atom can be partitioned by the present-state fibers at time
`s`. -/
lemma finiteHistoryEvent_eq_iUnion_presentSlices {n : ℕ} (X : T → Ω → E)
    (times : Fin (n + 1) → T) (states : Fin (n + 1) → E) (s : T) :
    finiteHistoryEvent X times states =
      ⋃ j : E, finiteHistoryEvent X times states ∩ {ω | X s ω = j} := by
  -- Proof comment: every realization belongs to the slice determined by its present state, and
  -- every such slice is contained in the original history event.
  ext ω
  constructor
  · intro hω
    refine Set.mem_iUnion.2 ⟨X s ω, ?_⟩
    exact ⟨hω, rfl⟩
  · intro hω
    rcases Set.mem_iUnion.1 hω with ⟨j, hj⟩
    exact hj.1

/-- Helper for Remark 17.2: if a finite history already ends at time `s`, then the
`σ(X s)`-conditional expectation of the future event has the correct set integral on that history
atom. -/
lemma futureEvent_setIntegral_eq_onTerminalHistory
    [Countable E] [MeasurableSingletonClass E]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : T → Ω → E)
    (hFin : HasFiniteHistoryMarkovProperty μ X)
    {n : ℕ} (times : Fin (n + 1) → T) (htimes : StrictMono times) {s u : T}
    (hlast : times (Fin.last n) = s) (hsu : s < u) (states : Fin (n + 1) → E)
    {A : Set E} (hA : MeasurableSet A) :
    (∫ ω in finiteHistoryEvent X times states,
        (μ⟦X u ⁻¹' A | MeasurableSpace.comap (X s) ‹MeasurableSpace E›⟧) ω ∂μ) =
      ∫ ω in finiteHistoryEvent X times states,
        (X u ⁻¹' A).indicator (fun _ ↦ (1 : ℝ)) ω ∂μ := by
  let H : Set Ω := finiteHistoryEvent X times states
  let F : Set Ω := {ω | X s ω = states (Fin.last n)}
  let event : Set Ω := X u ⁻¹' A
  have hHmeas : MeasurableSet H := by
    simpa [H] using measurableSet_finiteHistoryEvent X times states hFin.1
  have hEvent : MeasurableSet event := by
    simpa [event] using hFin.1 u hA
  have hHsub : H ⊆ F := by
    simpa [H, F, hlast] using finiteHistoryEvent_subset_terminalFiber X times states
  by_cases hμHist0 : μ H = 0
  · -- Proof comment: on a null history atom both set integrals vanish.
    rw [MeasureTheory.setIntegral_measure_zero _ hμHist0,
      MeasureTheory.setIntegral_measure_zero _ hμHist0]
  · have hμHist : 0 < μ H := by
      simpa using (bot_lt_iff_ne_bot.mpr hμHist0)
    have hCond :
        μ[event | H] = μ[event | F] := by
      -- Proof comment: the measurable-set conditional law of `X u` depends only on the present
      -- state once the history atom has positive probability.
      simpa [H, F, event, hlast] using
        finiteHistory_conditionalProb_eq_present_of_measurableSet
          μ X hFin times htimes (by simpa [hlast] using hsu) states hA hμHist
    have hCondReal : (μ[|H]).real event = (μ[|F]).real event := by
      exact congrArg ENNReal.toReal hCond
    have hPresentIntegral :
        ∫ ω in H, (μ⟦event | MeasurableSpace.comap (X s) ‹MeasurableSpace E›⟧) ω ∂μ =
          μ.real H * (μ[|F]).real event := by
      -- Proof comment: the present-state conditional expectation is constant on the terminal
      -- history atom because that atom lies in one present-state fiber.
      simpa [H, F, event] using
        condExp_futureEvent_eq_condProb_on_presentFiber
          μ X (by simpa [← hlast] using hFin.1 (times (Fin.last n)))
          (hFin.1 u) hA (states (Fin.last n)) hHmeas hHsub
    have hEventIntegral :
        ∫ ω in H, (event.indicator (fun _ ↦ (1 : ℝ))) ω ∂μ =
          μ.real H * (μ[|H]).real event := by
      -- Proof comment: rewrite the indicator integral through the normalized average on `H`.
      have hAverage :
          μ.real H • ⨍ ω in H, event.indicator (fun _ ↦ (1 : ℝ)) ω ∂μ =
            ∫ ω in H, (event.indicator (fun _ ↦ (1 : ℝ))) ω ∂μ := by
        exact MeasureTheory.measure_smul_setAverage
          (event.indicator (fun _ ↦ (1 : ℝ))) (measure_ne_top μ H)
      calc
        ∫ ω in H, (event.indicator (fun _ ↦ (1 : ℝ))) ω ∂μ
            = μ.real H * ⨍ ω in H, event.indicator (fun _ ↦ (1 : ℝ)) ω ∂μ := by
                rw [← hAverage, smul_eq_mul]
        _ = μ.real H * (μ[|H]).real event := by
              rw [setAverage_indicator_eq_condReal μ hEvent]
    calc
      ∫ ω in finiteHistoryEvent X times states,
          (μ⟦X u ⁻¹' A | MeasurableSpace.comap (X s) ‹MeasurableSpace E›⟧) ω ∂μ
          = μ.real H * (μ[|F]).real event := hPresentIntegral
      _ = μ.real H * (μ[|H]).real event := by rw [hCondReal.symm]
      _ = ∫ ω in H, (event.indicator (fun _ ↦ (1 : ℝ))) ω ∂μ := hEventIntegral.symm
      _ = ∫ ω in finiteHistoryEvent X times states,
            (X u ⁻¹' A).indicator (fun _ ↦ (1 : ℝ)) ω ∂μ := by
              rfl

/-- Helper for Remark 17.2: once a strict-before-`s` history slice is rewritten as an appended
history ending at `s`, the terminal-history integral identity applies directly. -/
lemma futureEvent_setIntegral_eq_onHistorySlice
    [Countable E] [MeasurableSingletonClass E]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : T → Ω → E)
    (hFin : HasFiniteHistoryMarkovProperty μ X)
    {n : ℕ} (times : Fin (n + 1) → T) (htimes : StrictMono times) {s u : T}
    (hlast_lt : times (Fin.last n) < s) (hsu : s < u) (states : Fin (n + 1) → E)
    {A : Set E} (hA : MeasurableSet A) (j : E) :
    (∫ ω in finiteHistoryEvent X times states ∩ {ω | X s ω = j},
        (μ⟦X u ⁻¹' A | MeasurableSpace.comap (X s) ‹MeasurableSpace E›⟧) ω ∂μ) =
      ∫ ω in finiteHistoryEvent X times states ∩ {ω | X s ω = j},
        (X u ⁻¹' A).indicator (fun _ ↦ (1 : ℝ)) ω ∂μ := by
  -- Proof comment: rewrite the slice as the snoc-extended finite-history atom ending at `s`,
  -- then invoke the terminal-history integral identity on that appended history.
  simpa [finiteHistoryEvent_inter_present_eq_snoc] using
    futureEvent_setIntegral_eq_onTerminalHistory
      μ X hFin (Fin.snoc times s) (strictMono_snoc_of_last_lt htimes hlast_lt)
      (by simp [Fin.snoc_last]) hsu (Fin.snoc states j) hA

/-- Helper for Remark 17.2: the future-event conditional expectation and the future-event
indicator have the same set integral on every finite-history atom ending no later than `s`. -/
lemma futureEvent_setIntegral_eq_onFiniteHistoryEvent
    [Countable E] [MeasurableSingletonClass E]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : T → Ω → E)
    (hFin : HasFiniteHistoryMarkovProperty μ X)
    {n : ℕ} (times : Fin (n + 1) → T) (htimes : StrictMono times) {s u : T}
    (hlast_le : times (Fin.last n) ≤ s) (hsu : s < u) (states : Fin (n + 1) → E)
    {A : Set E} (hA : MeasurableSet A) :
    (∫ ω in finiteHistoryEvent X times states,
        (μ⟦X u ⁻¹' A | MeasurableSpace.comap (X s) ‹MeasurableSpace E›⟧) ω ∂μ) =
      ∫ ω in finiteHistoryEvent X times states,
        (X u ⁻¹' A).indicator (fun _ ↦ (1 : ℝ)) ω ∂μ := by
  by_cases hlast : times (Fin.last n) = s
  · -- Proof comment: if the history already ends at `s`, this is the terminal-history case.
    exact futureEvent_setIntegral_eq_onTerminalHistory
      μ X hFin times htimes hlast hsu states hA
  · have hlast_lt : times (Fin.last n) < s := lt_of_le_of_ne hlast_le hlast
    let H : Set Ω := finiteHistoryEvent X times states
    let event : Set Ω := X u ⁻¹' A
    have hHmeas : MeasurableSet H := by
      simpa [H] using measurableSet_finiteHistoryEvent X times states hFin.1
    have hSliceMeas :
        ∀ j : E, MeasurableSet (H ∩ {ω | X s ω = j}) := by
      intro j
      exact hHmeas.inter (hFin.1 s (measurableSet_singleton j))
    have hSliceDisjoint :
        Pairwise fun i j : E ↦ Disjoint (H ∩ {ω | X s ω = i}) (H ∩ {ω | X s ω = j}) := by
      intro i j hij
      refine Set.disjoint_left.2 ?_
      intro ω hωi hωj
      exact hij (hωi.2.symm.trans hωj.2)
    have hCondInt :
        Integrable (μ⟦event | MeasurableSpace.comap (X s) ‹MeasurableSpace E›⟧) μ := by
      simpa [event] using
        (integrable_condExp :
          Integrable (μ⟦event | MeasurableSpace.comap (X s) ‹MeasurableSpace E›⟧) μ)
    have hEventMeas : MeasurableSet event := by
      simpa [event] using hFin.1 u hA
    have hEventInt : Integrable (event.indicator (fun _ ↦ (1 : ℝ))) μ :=
      (integrable_const (1 : ℝ)).indicator hEventMeas
    have hUnionEq : H = ⋃ j : E, H ∩ {ω | X s ω = j} := by
      simpa [H] using finiteHistoryEvent_eq_iUnion_presentSlices X times states s
    calc
      ∫ ω in finiteHistoryEvent X times states,
          (μ⟦X u ⁻¹' A | MeasurableSpace.comap (X s) ‹MeasurableSpace E›⟧) ω ∂μ
          = ∫ ω in ⋃ j : E, H ∩ {ω | X s ω = j},
              (μ⟦event | MeasurableSpace.comap (X s) ‹MeasurableSpace E›⟧) ω ∂μ := by
              rw [← hUnionEq]
      _ = ∑' j : E,
            ∫ ω in H ∩ {ω | X s ω = j},
              (μ⟦event | MeasurableSpace.comap (X s) ‹MeasurableSpace E›⟧) ω ∂μ := by
            exact integral_iUnion hSliceMeas hSliceDisjoint
              (hCondInt.integrableOn.mono_set <| Set.iUnion_subset fun _ ↦ Set.subset_univ _)
      _ = ∑' j : E,
            ∫ ω in H ∩ {ω | X s ω = j},
              (event.indicator (fun _ ↦ (1 : ℝ))) ω ∂μ := by
            refine tsum_congr fun j ↦ ?_
            simpa [H, event] using
              futureEvent_setIntegral_eq_onHistorySlice
                μ X hFin times htimes hlast_lt hsu states hA j
      _ = ∫ ω in ⋃ j : E, H ∩ {ω | X s ω = j},
            (event.indicator (fun _ ↦ (1 : ℝ))) ω ∂μ := by
            symm
            exact integral_iUnion hSliceMeas hSliceDisjoint
              (hEventInt.integrableOn.mono_set <| Set.iUnion_subset fun _ ↦ Set.subset_univ _)
      _ = ∫ ω in finiteHistoryEvent X times states,
            (X u ⁻¹' A).indicator (fun _ ↦ (1 : ℝ)) ω ∂μ := by
            rw [← hUnionEq]

/-- Helper for Remark 17.2: the finite-history conditional-probability identity implies the
natural Markov property once the past sigma-algebra is normalized to singleton-fiber history
atoms. -/
lemma hasNaturalMarkovProperty_of_hasFiniteHistoryMarkovProperty
    [Countable E] [MeasurableSingletonClass E]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : T → Ω → E)
    (hFin : HasFiniteHistoryMarkovProperty μ X) :
    HasNaturalMarkovProperty μ X := by
  classical
  rcases isEmpty_or_nonempty E with hE | hE
  · letI : IsEmpty E := hE
    refine ⟨hFin.1, ?_⟩
    intro s u hsu A hA
    have hAempty : A = ∅ := by
      ext x
      exact (hE.false x).elim
    -- Proof comment: on an empty state space every measurable state event is empty, so both
    -- conditional expectations are almost surely the zero function.
    have hZero :
        μ[(fun _ : Ω ↦ (0 : ℝ)) | generatedFiltrationSpace X s] =ᵐ[μ]
          μ[(fun _ : Ω ↦ (0 : ℝ)) | MeasurableSpace.comap (X s) ‹MeasurableSpace E›] := by
      have hZeroLeft :
          μ[(fun _ : Ω ↦ (0 : ℝ)) | generatedFiltrationSpace X s] = 0 := by
        exact
          (MeasureTheory.condExp_zero :
            μ[(fun _ : Ω ↦ (0 : ℝ)) | generatedFiltrationSpace X s] = 0)
      have hZeroRight :
          μ[(fun _ : Ω ↦ (0 : ℝ)) | MeasurableSpace.comap (X s) ‹MeasurableSpace E›] = 0 := by
        exact
          (MeasureTheory.condExp_zero :
            μ[(fun _ : Ω ↦ (0 : ℝ)) | MeasurableSpace.comap (X s) ‹MeasurableSpace E›] = 0)
      exact Filter.EventuallyEq.of_eq (hZeroLeft.trans hZeroRight.symm)
    simpa [hAempty, Set.preimage_empty] using hZero
  · letI : Nonempty E := hE
    refine ⟨hFin.1, ?_⟩
    intro s u hsu A hA
    by_cases hsu_eq : u = s
    · subst u
      let event : Set Ω := X s ⁻¹' A
      have hmPresent :
          MeasurableSpace.comap (X s) ‹MeasurableSpace E› ≤ ‹MeasurableSpace Ω› :=
        (hFin.1 s).comap_le
      have hmPast : generatedFiltrationSpace X s ≤ ‹MeasurableSpace Ω› := by
        exact generatedFiltrationSpace_le_ambient X hFin.1 s
      have hmPresentPast :
          MeasurableSpace.comap (X s) ‹MeasurableSpace E› ≤ generatedFiltrationSpace X s :=
        present_le_generatedFiltrationSpace X s
      have hEventPresent :
          MeasurableSet[MeasurableSpace.comap (X s) ‹MeasurableSpace E›] event := by
        exact MeasurableSpace.measurableSet_comap.2 ⟨A, hA, rfl⟩
      have hEventPast : MeasurableSet[generatedFiltrationSpace X s] event := by
        exact hmPresentPast event hEventPresent
      have hEventInt : Integrable (event.indicator (fun _ ↦ (1 : ℝ))) μ :=
        (integrable_const (1 : ℝ)).indicator (hmPresent event hEventPresent)
      -- Proof comment: when `u = s`, the future event is already measurable with respect to both
      -- sigma-algebras, so each conditional expectation equals the event indicator.
      have hPastEq :
          μ⟦event | generatedFiltrationSpace X s⟧ = event.indicator (fun _ ↦ (1 : ℝ)) := by
        exact
          MeasureTheory.condExp_of_stronglyMeasurable hmPast
            (stronglyMeasurable_const.indicator hEventPast) hEventInt
      have hPresentEq :
          μ⟦event | MeasurableSpace.comap (X s) ‹MeasurableSpace E›⟧ =
            event.indicator (fun _ ↦ (1 : ℝ)) := by
        exact
          MeasureTheory.condExp_of_stronglyMeasurable hmPresent
            (stronglyMeasurable_const.indicator hEventPresent) hEventInt
      exact Filter.EventuallyEq.of_eq <| hPastEq.trans hPresentEq.symm
    · have hsu_lt : s < u := by
        exact lt_of_le_of_ne hsu (Ne.symm hsu_eq)
      let event : Set Ω := X u ⁻¹' A
      let pastSingletonFibers : Set (Set Ω) :=
        ⋃ r : {r : T // r ≤ s},
          insert ∅ (Set.range fun j : E ↦ {ω | X r.1 ω = j})
      have hmPast : generatedFiltrationSpace X s ≤ ‹MeasurableSpace Ω› := by
        exact generatedFiltrationSpace_le_ambient X hFin.1 s
      have hmPresent :
          MeasurableSpace.comap (X s) ‹MeasurableSpace E› ≤ ‹MeasurableSpace Ω› :=
        (hFin.1 s).comap_le
      have hmPresentPast :
          MeasurableSpace.comap (X s) ‹MeasurableSpace E› ≤ generatedFiltrationSpace X s :=
        present_le_generatedFiltrationSpace X s
      have hEvent : MeasurableSet event := by
        simpa [event] using hFin.1 u hA
      have hEventInt : Integrable (event.indicator (fun _ ↦ (1 : ℝ))) μ :=
        (integrable_const (1 : ℝ)).indicator hEvent
      have hCondInt :
          Integrable
            (μ⟦event | MeasurableSpace.comap (X s) ‹MeasurableSpace E›⟧) μ := by
        simpa [event] using
          (integrable_condExp :
            Integrable
              (μ⟦event | MeasurableSpace.comap (X s) ‹MeasurableSpace E›⟧) μ)
      have hGenerated :
          generatedFiltrationSpace X s =
            MeasurableSpace.generateFrom (generatePiSystem pastSingletonFibers) := by
        rw [generatedFiltrationSpace_eq_generateFromPastSingletonFiberEvents X s]
        rw [generateFrom_generatePiSystem_eq]
      -- Proof comment: identify the history conditional expectation by testing the candidate
      -- `μ⟦event | σ(X s)⟧` on all history-measurable sets and reducing the generator sets to
      -- finite-history atoms.
      refine
        (MeasureTheory.ae_eq_condExp_of_forall_setIntegral_eq hmPast hEventInt
          (fun C _ _ ↦ hCondInt.integrableOn)
          (fun C hC _ ↦ ?_) ?_).symm
      · refine
          MeasurableSpace.induction_on_inter hGenerated
            (isPiSystem_generatePiSystem pastSingletonFibers) ?_ ?_ ?_ ?_ C hC
        · simp
        · intro D hD
          rcases mem_pastSingletonFiberPiSystem_elim X s hD with hDempty |
              ⟨S, ξ, hDrepr⟩
          · subst hDempty
            simp
          · rcases pastSingletonFiberInter_eq_univ_or_finiteHistoryEvent X S ξ with hDuniv |
              ⟨n, times, htimes, states, hlast_le, hDhist⟩
            · have hDuniv' : D = Set.univ := hDrepr.trans hDuniv
              -- Proof comment: on the whole space, the integral identity is just the defining
              -- integral property of the present-state conditional expectation.
              calc
                ∫ ω in D,
                    (μ⟦event | MeasurableSpace.comap (X s) ‹MeasurableSpace E›⟧) ω ∂μ
                    = ∫ ω,
                        (μ⟦event | MeasurableSpace.comap (X s) ‹MeasurableSpace E›⟧) ω ∂μ := by
                          rw [hDuniv', MeasureTheory.setIntegral_univ]
                _ = ∫ ω, (event.indicator (fun _ ↦ (1 : ℝ))) ω ∂μ := by
                      exact
                        MeasureTheory.integral_condExp hmPresent
                _ = ∫ ω in D, (event.indicator (fun _ ↦ (1 : ℝ))) ω ∂μ := by
                      rw [hDuniv', MeasureTheory.setIntegral_univ]
            · have hDhist' : D = finiteHistoryEvent X times states := hDrepr.trans hDhist
              -- Proof comment: the generator normalization has reduced the test set to one
              -- finite-history atom, so the atomwise integral identity closes the basic case.
              simpa [event, hDhist'] using
                futureEvent_setIntegral_eq_onFiniteHistoryEvent
                  μ X hFin times htimes hlast_le hsu_lt states hA
        · intro D hDm hInd
          have hDmeas : MeasurableSet D := hmPast D hDm
          have hWhole :
              ∫ ω, (μ⟦event | MeasurableSpace.comap (X s) ‹MeasurableSpace E›⟧) ω ∂μ =
                ∫ ω, (event.indicator (fun _ ↦ (1 : ℝ))) ω ∂μ := by
            exact
              MeasureTheory.integral_condExp hmPresent
          -- Proof comment: pass from a set to its complement by subtracting the already-known
          -- set integral from the whole-space identity for both functions.
          calc
            ∫ ω in Dᶜ,
                (μ⟦event | MeasurableSpace.comap (X s) ‹MeasurableSpace E›⟧) ω ∂μ
                = ∫ ω,
                    (μ⟦event | MeasurableSpace.comap (X s) ‹MeasurableSpace E›⟧) ω ∂μ -
                    ∫ ω in D,
                      (μ⟦event | MeasurableSpace.comap (X s) ‹MeasurableSpace E›⟧) ω ∂μ := by
                        exact
                          MeasureTheory.setIntegral_compl hDmeas hCondInt
            _ = ∫ ω, (event.indicator (fun _ ↦ (1 : ℝ))) ω ∂μ -
                  ∫ ω in D,
                    (μ⟦event | MeasurableSpace.comap (X s) ‹MeasurableSpace E›⟧) ω ∂μ := by
                    rw [hWhole]
            _ = ∫ ω, (event.indicator (fun _ ↦ (1 : ℝ))) ω ∂μ -
                  ∫ ω in D, (event.indicator (fun _ ↦ (1 : ℝ))) ω ∂μ := by
                    rw [hInd]
            _ = ∫ ω in Dᶜ, (event.indicator (fun _ ↦ (1 : ℝ))) ω ∂μ := by
                  exact (MeasureTheory.setIntegral_compl hDmeas hEventInt).symm
        · intro f hfd hfm hf
          have hfm' : ∀ n, MeasurableSet (f n) := fun n ↦ hmPast (f n) (hfm n)
          -- Proof comment: extend the identity from disjoint pieces to their countable union by
          -- summing both set integrals termwise.
          calc
            ∫ ω in ⋃ n, f n,
                (μ⟦event | MeasurableSpace.comap (X s) ‹MeasurableSpace E›⟧) ω ∂μ
                = ∑' n, ∫ ω in f n,
                    (μ⟦event | MeasurableSpace.comap (X s) ‹MeasurableSpace E›⟧) ω ∂μ := by
                      exact MeasureTheory.integral_iUnion hfm' hfd
                        (hCondInt.integrableOn.mono_set <|
                          Set.iUnion_subset fun _ ↦ Set.subset_univ _)
            _ = ∑' n, ∫ ω in f n, (event.indicator (fun _ ↦ (1 : ℝ))) ω ∂μ := by
                  exact tsum_congr hf
            _ = ∫ ω in ⋃ n, f n, (event.indicator (fun _ ↦ (1 : ℝ))) ω ∂μ := by
                  symm
                  exact MeasureTheory.integral_iUnion hfm' hfd
                    (hEventInt.integrableOn.mono_set <|
                      Set.iUnion_subset fun _ ↦ Set.subset_univ _)
      · exact (stronglyMeasurable_condExp.mono hmPresentPast).aestronglyMeasurable

-- Semantic recall: the relevant owner API is the generated-filtration/natural-Markov surface from
-- Exercise 17.1.1, while the source remark itself fixes the stronger chain `s₁ < ⋯ < sₙ < t`.
-- Proof sketch: use the countability of the state space to reduce measurable state events to
-- countable unions of singleton events, then apply the Definition 17.1 conditional-probability
-- identity to singleton state events and conversely recover the full conditional-expectation
-- identity from equality on positive-probability finite history atoms.
/-- Remark 17.2: for a countable state space, the Markov property is equivalent to the statement
that on every positive-probability finite history, the conditional probability of `X_t = i`
depends only on the last state in that history. The source remark assumes a strict chain
`s₁ < ⋯ < sₙ < t`; here that source requirement is recorded by the ambient `[LinearOrder T]`
hypothesis, which makes every past observation time comparable with the terminal history time. -/
theorem hasNaturalMarkovProperty_iff_conditionalProb_eq_given_finite_history_of_countable
    [Countable E] [MeasurableSingletonClass E]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : T → Ω → E) :
    HasNaturalMarkovProperty μ X ↔ HasFiniteHistoryMarkovProperty μ X := by
  -- Proof comment: the remark is exactly the conjunction of the two implication lemmas proved on
  -- the natural-Markov and finite-history interfaces.
  constructor
  · exact hasFiniteHistoryMarkovProperty_of_hasNaturalMarkovProperty μ X
  · exact hasNaturalMarkovProperty_of_hasFiniteHistoryMarkovProperty μ X

end ProbabilityTheory
