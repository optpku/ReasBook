/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open Set MeasureTheory ProbabilityTheory

open scoped ENNReal

noncomputable section

/-- The six outcomes of a single fair die, modeled by `Fin 6`. -/
abbrev Die := Fin 6

/-- The uniform law of a single fair die roll. -/
abbrev dieMeasure : Measure Die :=
  (PMF.uniformOfFintype Die).toMeasure

/-- The sample space of three successive die rolls. -/
abbrev ThreeRolls := Fin 3 → Die

/-- The law of three independent fair die rolls. -/
abbrev threeRollsMeasure : Measure ThreeRolls :=
  Measure.pi fun _ : Fin 3 ↦ dieMeasure

/-- The three coordinate projections on the product space of die rolls are independent. -/
theorem threeRolls_iIndepFun :
    iIndepFun Function.eval threeRollsMeasure := by
  simpa [Function.eval, threeRollsMeasure] using
    (iIndepFun_pi (fun _ : Fin 3 ↦ measurable_id.aemeasurable) :
      iIndepFun (fun i (ω : ThreeRolls) ↦ ω i) (Measure.pi fun _ : Fin 3 ↦ dieMeasure))

/-- The three diagonal events `ω₀ = ω₁`, `ω₁ = ω₂`, and `ω₀ = ω₂`. -/
def diagonalEqualityEvents : Fin 3 → Set ThreeRolls
  | 0 => {ω : ThreeRolls | ω 0 = ω 1}
  | 1 => {ω : ThreeRolls | ω 1 = ω 2}
  | 2 => {ω : ThreeRolls | ω 0 = ω 2}

/-- Helper for Example 2.2: the event that all three rolls coincide. -/
def allEqualEvent : Set ThreeRolls :=
  {ω : ThreeRolls | ω 0 = ω 1 ∧ ω 1 = ω 2}

/-- Helper for Example 2.2: the cylinder event that the `i`th roll equals the value `a`. -/
def rollEq (i : Fin 3) (a : Die) : Set ThreeRolls :=
  Function.eval i ⁻¹' {a}

/-- Helper for Example 2.2: two coordinates agree exactly when they lie in a common singleton
cylinder. -/
lemma exists_rollEq_pair_iff {i j : Fin 3} (ω : ThreeRolls) :
    (∃ a : Die, ω ∈ rollEq i a ∧ ω ∈ rollEq j a) ↔ ω i = ω j := by
  constructor
  · rintro ⟨a, hi, hj⟩
    have hi' : ω i = a := by
      simpa [rollEq] using hi
    have hj' : ω j = a := by
      simpa [rollEq] using hj
    exact hi'.trans hj'.symm
  · intro hij
    refine ⟨ω i, ?_⟩
    constructor
    · simpa [rollEq]
    · change ω j = ω i
      exact hij.symm

/-- Helper for Example 2.2: all three coordinates agree exactly when they lie in a common
singleton cylinder. -/
lemma exists_rollEq_triple_iff (ω : ThreeRolls) :
    (∃ a : Die, ω ∈ rollEq 0 a ∧ ω ∈ rollEq 1 a ∧ ω ∈ rollEq 2 a) ↔
      (ω 0 = ω 1 ∧ ω 1 = ω 2) := by
  constructor
  · rintro ⟨a, h0, h1, h2⟩
    have h0' : ω 0 = a := by
      simpa [rollEq] using h0
    have h1' : ω 1 = a := by
      simpa [rollEq] using h1
    have h2' : ω 2 = a := by
      simpa [rollEq] using h2
    exact ⟨h0'.trans h1'.symm, h1'.trans h2'.symm⟩
  · rintro ⟨h01, h12⟩
    refine ⟨ω 0, ?_, ?_, ?_⟩
    · simpa [rollEq]
    · change ω 1 = ω 0
      exact h01.symm
    · change ω 2 = ω 0
      exact (h01.trans h12).symm

/-- Helper for Example 2.2: `(6 : ℝ≥0∞)⁻¹ ^ 2 = (36 : ℝ≥0∞)⁻¹`. -/
lemma invSixSq_eq_invThirtySix :
    ((6 : ℝ≥0∞)⁻¹) ^ 2 = (36 : ℝ≥0∞)⁻¹ := by
  -- Rewrite the square as a product and then collapse the product of inverses.
  have h36 : (36 : ℝ≥0∞) = 6 * 6 := by
    norm_num
  simp [pow_two, h36, ENNReal.mul_inv]

/-- Helper for Example 2.2: `(36 : ℝ≥0∞)⁻¹ * (6 : ℝ≥0∞)⁻¹ = (216 : ℝ≥0∞)⁻¹`. -/
lemma invThirtySix_mul_invSix_eq_invTwoHundredSixteen :
    (36 : ℝ≥0∞)⁻¹ * (6 : ℝ≥0∞)⁻¹ = (216 : ℝ≥0∞)⁻¹ := by
  -- Collapse the product of inverses to the inverse of the product `36 * 6 = 216`.
  have h216 : (216 : ℝ≥0∞) = 36 * 6 := by
    norm_num
  simp [h216, ENNReal.mul_inv]

/-- Helper for Example 2.2: `(6 : ℝ≥0∞)⁻¹ ^ 3 = (216 : ℝ≥0∞)⁻¹`. -/
lemma invSixCube_eq_invTwoHundredSixteen :
    ((6 : ℝ≥0∞)⁻¹) ^ 3 = (216 : ℝ≥0∞)⁻¹ := by
  rw [pow_succ, invSixSq_eq_invThirtySix]
  simpa [mul_comm] using invThirtySix_mul_invSix_eq_invTwoHundredSixteen

/-- Helper for Example 2.2: `6 * (36 : ℝ≥0∞)⁻¹ = (6 : ℝ≥0∞)⁻¹`. -/
lemma six_mul_invThirtySix_eq_invSix :
    (6 : ℝ≥0∞) * (36 : ℝ≥0∞)⁻¹ = (6 : ℝ≥0∞)⁻¹ := by
  -- Rewrite `36⁻¹` as `(6 * 6)⁻¹` and cancel the leading factor `6`.
  have h36 : (36 : ℝ≥0∞) = 6 * 6 := by
    norm_num
  rw [h36]
  simpa [ENNReal.mul_inv] using
    ENNReal.mul_inv_cancel_left (a := (6 : ℝ≥0∞)) (b := (6 : ℝ≥0∞)⁻¹)
      (by norm_num) (by simp)

/-- Helper for Example 2.2: `6 * (216 : ℝ≥0∞)⁻¹ = (36 : ℝ≥0∞)⁻¹`. -/
lemma six_mul_invTwoHundredSixteen_eq_invThirtySix :
    (6 : ℝ≥0∞) * (216 : ℝ≥0∞)⁻¹ = (36 : ℝ≥0∞)⁻¹ := by
  -- Rewrite `216⁻¹` as `(6 * 36)⁻¹` and cancel the leading factor `6`.
  have h216 : (216 : ℝ≥0∞) = 6 * 36 := by
    norm_num
  rw [h216]
  simpa [ENNReal.mul_inv] using
    ENNReal.mul_inv_cancel_left (a := (6 : ℝ≥0∞)) (b := (36 : ℝ≥0∞)⁻¹)
      (by norm_num) (by simp)

/-- Helper for Example 2.2: intersecting all singleton cylinders equals the explicit threefold
intersection. -/
lemma iInter_rollEq_eq_threefoldInter (a : Die) :
    (⋂ i, rollEq i a) = rollEq 0 a ∩ rollEq 1 a ∩ rollEq 2 a := by
  -- Identify the indexed intersection by checking membership coordinate-by-coordinate.
  ext ω
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · exact ⟨Set.mem_iInter.mp h 0, Set.mem_iInter.mp h 1⟩
    · exact Set.mem_iInter.mp h 2
  · intro h
    refine Set.mem_iInter.mpr ?_
    intro i
    fin_cases i
    · exact h.1.1
    · exact h.1.2
    · exact h.2

-- Proof sketch: `threeRollsMeasure` is a product measure, so the coordinate maps are independent;
-- apply this to the measurable sets `S i`.
/-- Events depending separately on the first, second, and third die roll are independent. -/
theorem coordinatePreimage_iIndepSet (S : Fin 3 → Set Die) :
    iIndepSet (fun i ↦ Function.eval i ⁻¹' S i) threeRollsMeasure := by
  rw [iIndepSet_iff_meas_biInter]
  · intro s
    simpa [Function.eval] using
      threeRolls_iIndepFun.measure_inter_preimage_eq_mul s
        (fun i _ ↦ (Set.toFinite (S i)).measurableSet)
  · intro i
    exact (measurable_pi_apply i) ((Set.toFinite (S i)).measurableSet)

/-- Helper for Example 2.2: each diagonal equality event is measurable. -/
lemma measurableSet_diagonalEqualityEvents (i : Fin 3) :
    MeasurableSet (diagonalEqualityEvents i) := by
  -- `ThreeRolls` is finite, so every subset is measurable.
  exact (Set.toFinite (diagonalEqualityEvents i)).measurableSet

/-- Helper for Example 2.2: each coordinate takes a fixed die value with probability `1 / 6`. -/
lemma threeRollsMeasure_eval_preimage_singleton (i : Fin 3) (a : Die) :
    threeRollsMeasure (rollEq i a) = (6 : ℝ≥0∞)⁻¹ := by
  -- Push the cylinder event along the evaluation map and use the uniform die law.
  have hEval : MeasurePreserving (Function.eval i) threeRollsMeasure dieMeasure := by
    simpa [threeRollsMeasure] using
      (measurePreserving_eval (μ := fun _ : Fin 3 ↦ dieMeasure) i)
  calc
    threeRollsMeasure (rollEq i a) = dieMeasure {a} := by
          rw [← hEval.map_eq]
          simpa [rollEq] using
            (Measure.map_apply hEval.measurable (measurableSet_singleton a)).symm
    _ = (6 : ℝ≥0∞)⁻¹ := by
      simp [dieMeasure]

/-- Helper for Example 2.2: fixing two distinct coordinates to the same die value has probability
`1 / 36`. -/
lemma threeRollsMeasure_twoCoordinateSingletonSlice {i j : Fin 3} (hij : i ≠ j) (a : Die) :
    threeRollsMeasure (rollEq i a ∩ rollEq j a) = (36 : ℝ≥0∞)⁻¹ := by
  -- Apply the product formula to the two singleton cylinders.
  have hIndep : iIndepSet (fun k : Fin 3 ↦ rollEq k a) threeRollsMeasure := by
    simpa [rollEq] using coordinatePreimage_iIndepSet (fun _ : Fin 3 ↦ ({a} : Set Die))
  have hMeasure :
      threeRollsMeasure (rollEq i a ∩ rollEq j a) =
        ((6 : ℝ≥0∞)⁻¹) ^ 2 := by
    simpa [hij, threeRollsMeasure_eval_preimage_singleton] using
      hIndep.meas_biInter ({i, j} : Finset (Fin 3))
  calc
    threeRollsMeasure (rollEq i a ∩ rollEq j a) = ((6 : ℝ≥0∞)⁻¹) ^ 2 := hMeasure
    _ = (36 : ℝ≥0∞)⁻¹ := invSixSq_eq_invThirtySix

/-- Helper for Example 2.2: fixing all three coordinates to the same die value has probability
`1 / 216`. -/
lemma threeRollsMeasure_allEqualSingletonSlice (a : Die) :
    threeRollsMeasure (rollEq 0 a ∩ rollEq 1 a ∩ rollEq 2 a) = (216 : ℝ≥0∞)⁻¹ := by
  -- Use independence of all three coordinate singleton cylinders.
  have hIndep : iIndepSet (fun k : Fin 3 ↦ rollEq k a) threeRollsMeasure := by
    simpa [rollEq] using coordinatePreimage_iIndepSet (fun _ : Fin 3 ↦ ({a} : Set Die))
  have hMeasure :
      threeRollsMeasure (rollEq 0 a ∩ rollEq 1 a ∩ rollEq 2 a) =
        ((6 : ℝ≥0∞)⁻¹) ^ 3 := by
    rw [← iInter_rollEq_eq_threefoldInter a]
    simpa [threeRollsMeasure_eval_preimage_singleton] using
      hIndep.meas_biInter (Finset.univ : Finset (Fin 3))
  calc
    threeRollsMeasure (rollEq 0 a ∩ rollEq 1 a ∩ rollEq 2 a) = ((6 : ℝ≥0∞)⁻¹) ^ 3 := hMeasure
    _ = (216 : ℝ≥0∞)⁻¹ := invSixCube_eq_invTwoHundredSixteen

/-- Helper for Example 2.2: any pair of distinct diagonal events cuts out the all-equal event. -/
lemma diagonalEqualityEvents_inter_eq_allEqual {i j : Fin 3} (hij : i ≠ j) :
    diagonalEqualityEvents i ∩ diagonalEqualityEvents j = allEqualEvent := by
  -- There are only three diagonal events, so a case split identifies each pairwise intersection.
  fin_cases i <;> fin_cases j
  · contradiction
  · ext ω
    simp [diagonalEqualityEvents, allEqualEvent]
  · ext ω
    constructor
    · intro h
      simp [diagonalEqualityEvents, allEqualEvent] at h ⊢
      exact ⟨h.1, h.1.symm.trans h.2⟩
    · intro h
      simp [diagonalEqualityEvents, allEqualEvent] at h ⊢
      exact ⟨h.1, h.1.trans h.2⟩
  · ext ω
    constructor
    · intro h
      simp [diagonalEqualityEvents, allEqualEvent] at h ⊢
      exact ⟨h.2, h.1⟩
    · intro h
      simp [diagonalEqualityEvents, allEqualEvent] at h ⊢
      exact ⟨h.2, h.1⟩
  · contradiction
  · ext ω
    constructor
    · intro h
      simp [diagonalEqualityEvents, allEqualEvent] at h ⊢
      exact ⟨h.2.trans h.1.symm, h.1⟩
    · intro h
      simp [diagonalEqualityEvents, allEqualEvent] at h ⊢
      exact ⟨h.2, h.1.trans h.2⟩
  · ext ω
    constructor
    · intro h
      simp [diagonalEqualityEvents, allEqualEvent] at h ⊢
      exact ⟨h.2, h.2.symm.trans h.1⟩
    · intro h
      simp [diagonalEqualityEvents, allEqualEvent] at h ⊢
      exact ⟨h.1.trans h.2, h.1⟩
  · ext ω
    constructor
    · intro h
      simp [diagonalEqualityEvents, allEqualEvent] at h ⊢
      exact ⟨h.1.trans h.2.symm, h.2⟩
    · intro h
      simp [diagonalEqualityEvents, allEqualEvent] at h ⊢
      exact ⟨h.1.trans h.2, h.2⟩
  · contradiction

/-- Helper for Example 2.2: the common intersection of the three diagonal events is the all-equal
event. -/
lemma iInter_diagonalEqualityEvents_eq_allEqual :
    (⋂ i, diagonalEqualityEvents i) = allEqualEvent := by
  -- The third diagonal equality follows from the first two.
  ext ω
  constructor
  · intro h
    have h0 : ω ∈ diagonalEqualityEvents (0 : Fin 3) := by
      exact Set.mem_iInter.mp h (0 : Fin 3)
    have h1 : ω ∈ diagonalEqualityEvents (1 : Fin 3) := by
      exact Set.mem_iInter.mp h (1 : Fin 3)
    have h01 : ω 0 = ω 1 := by
      simpa [diagonalEqualityEvents] using h0
    have h12 : ω 1 = ω 2 := by
      simpa [diagonalEqualityEvents] using h1
    simpa [allEqualEvent] using And.intro h01 h12
  · intro h
    have hEq : ω 0 = ω 1 ∧ ω 1 = ω 2 := by
      simpa [allEqualEvent] using h
    refine Set.mem_iInter.mpr ?_
    intro i
    fin_cases i
    · simpa [diagonalEqualityEvents] using hEq.1
    · simpa [diagonalEqualityEvents] using hEq.2
    · simpa [diagonalEqualityEvents] using hEq.1.trans hEq.2

/-- Helper for Example 2.2: each diagonal equality event has probability `1 / 6`. -/
lemma threeRollsMeasure_diagonalEqualityEvent (i : Fin 3) :
    threeRollsMeasure (diagonalEqualityEvents i) = (6 : ℝ≥0∞)⁻¹ := by
  fin_cases i
  ·
    -- Rewrite `ω 0 = ω 1` as a disjoint union over the common face value.
    have hUnion :
        diagonalEqualityEvents 0 =
          ⋃ a ∈ (Finset.univ : Finset Die),
            rollEq 0 a ∩ rollEq 1 a := by
      ext ω
      simpa [diagonalEqualityEvents] using (exists_rollEq_pair_iff (i := 0) (j := 1) ω).symm
    have hDisjoint : PairwiseDisjoint (↑(Finset.univ : Finset Die)) fun a ↦
        rollEq 0 a ∩ rollEq 1 a := by
      intro a ha b hb hab
      refine Set.disjoint_left.2 ?_
      intro ω hωa hωb
      have h0a : ω 0 = a := by
        simpa using hωa.1
      have h0b : ω 0 = b := by
        simpa using hωb.1
      exact hab (h0a.symm.trans h0b)
    calc
      threeRollsMeasure (diagonalEqualityEvents 0) =
          ∑ a ∈ (Finset.univ : Finset Die),
            threeRollsMeasure (rollEq 0 a ∩ rollEq 1 a) := by
        rw [hUnion, measure_biUnion_finset hDisjoint]
        intro a ha
        exact ((measurable_pi_apply 0) (measurableSet_singleton a)).inter
          ((measurable_pi_apply 1) (measurableSet_singleton a))
      _ = ∑ a ∈ (Finset.univ : Finset Die), (36 : ℝ≥0∞)⁻¹ := by
        refine Finset.sum_congr rfl ?_
        intro a ha
        rw [threeRollsMeasure_twoCoordinateSingletonSlice (by decide : (0 : Fin 3) ≠ 1) a]
      _ = (6 : ℝ≥0∞)⁻¹ := by
        simpa using six_mul_invThirtySix_eq_invSix
  ·
    -- Rewrite `ω 1 = ω 2` as a disjoint union over the common face value.
    have hUnion :
        diagonalEqualityEvents 1 =
          ⋃ a ∈ (Finset.univ : Finset Die),
            rollEq 1 a ∩ rollEq 2 a := by
      ext ω
      simpa [diagonalEqualityEvents] using (exists_rollEq_pair_iff (i := 1) (j := 2) ω).symm
    have hDisjoint : PairwiseDisjoint (↑(Finset.univ : Finset Die)) fun a ↦
        rollEq 1 a ∩ rollEq 2 a := by
      intro a ha b hb hab
      refine Set.disjoint_left.2 ?_
      intro ω hωa hωb
      have h1a : ω 1 = a := by
        simpa using hωa.1
      have h1b : ω 1 = b := by
        simpa using hωb.1
      exact hab (h1a.symm.trans h1b)
    calc
      threeRollsMeasure (diagonalEqualityEvents 1) =
          ∑ a ∈ (Finset.univ : Finset Die),
            threeRollsMeasure (rollEq 1 a ∩ rollEq 2 a) := by
        rw [hUnion, measure_biUnion_finset hDisjoint]
        intro a ha
        exact ((measurable_pi_apply 1) (measurableSet_singleton a)).inter
          ((measurable_pi_apply 2) (measurableSet_singleton a))
      _ = ∑ a ∈ (Finset.univ : Finset Die), (36 : ℝ≥0∞)⁻¹ := by
        refine Finset.sum_congr rfl ?_
        intro a ha
        rw [threeRollsMeasure_twoCoordinateSingletonSlice (by decide : (1 : Fin 3) ≠ 2) a]
      _ = (6 : ℝ≥0∞)⁻¹ := by
        simpa using six_mul_invThirtySix_eq_invSix
  ·
    -- Rewrite `ω 0 = ω 2` as a disjoint union over the common face value.
    have hUnion :
        diagonalEqualityEvents 2 =
          ⋃ a ∈ (Finset.univ : Finset Die),
            rollEq 0 a ∩ rollEq 2 a := by
      ext ω
      simpa [diagonalEqualityEvents] using (exists_rollEq_pair_iff (i := 0) (j := 2) ω).symm
    have hDisjoint : PairwiseDisjoint (↑(Finset.univ : Finset Die)) fun a ↦
        rollEq 0 a ∩ rollEq 2 a := by
      intro a ha b hb hab
      refine Set.disjoint_left.2 ?_
      intro ω hωa hωb
      have h0a : ω 0 = a := by
        simpa using hωa.1
      have h0b : ω 0 = b := by
        simpa using hωb.1
      exact hab (h0a.symm.trans h0b)
    calc
      threeRollsMeasure (diagonalEqualityEvents 2) =
          ∑ a ∈ (Finset.univ : Finset Die),
            threeRollsMeasure (rollEq 0 a ∩ rollEq 2 a) := by
        rw [hUnion, measure_biUnion_finset hDisjoint]
        intro a ha
        exact ((measurable_pi_apply 0) (measurableSet_singleton a)).inter
          ((measurable_pi_apply 2) (measurableSet_singleton a))
      _ = ∑ a ∈ (Finset.univ : Finset Die), (36 : ℝ≥0∞)⁻¹ := by
        refine Finset.sum_congr rfl ?_
        intro a ha
        rw [threeRollsMeasure_twoCoordinateSingletonSlice (by decide : (0 : Fin 3) ≠ 2) a]
      _ = (6 : ℝ≥0∞)⁻¹ := by
        simpa using six_mul_invThirtySix_eq_invSix

/-- Helper for Example 2.2: the all-equal event has probability `1 / 36`. -/
lemma threeRollsMeasure_allEqualEvent :
    threeRollsMeasure allEqualEvent = (36 : ℝ≥0∞)⁻¹ := by
  -- Rewrite the all-equal event as a disjoint union over the common face value.
  have hUnion :
      allEqualEvent =
        ⋃ a ∈ (Finset.univ : Finset Die),
          rollEq 0 a ∩ rollEq 1 a ∩ rollEq 2 a := by
    ext ω
    simpa [allEqualEvent, and_assoc] using (exists_rollEq_triple_iff ω).symm
  have hDisjoint : PairwiseDisjoint (↑(Finset.univ : Finset Die)) fun a ↦
      rollEq 0 a ∩ rollEq 1 a ∩ rollEq 2 a := by
    intro a ha b hb hab
    refine Set.disjoint_left.2 ?_
    intro ω hωa hωb
    have h0a : ω 0 = a := by
      simpa using hωa.1.1
    have h0b : ω 0 = b := by
      simpa using hωb.1.1
    exact hab (h0a.symm.trans h0b)
  calc
    threeRollsMeasure allEqualEvent =
        ∑ a ∈ (Finset.univ : Finset Die),
          threeRollsMeasure (rollEq 0 a ∩ rollEq 1 a ∩ rollEq 2 a) := by
      rw [hUnion, measure_biUnion_finset hDisjoint]
      intro a ha
      exact (((measurable_pi_apply 0) (measurableSet_singleton a)).inter
        ((measurable_pi_apply 1) (measurableSet_singleton a))).inter
          ((measurable_pi_apply 2) (measurableSet_singleton a))
    _ = ∑ a ∈ (Finset.univ : Finset Die), (216 : ℝ≥0∞)⁻¹ := by
      refine Finset.sum_congr rfl ?_
      intro a ha
      rw [threeRollsMeasure_allEqualSingletonSlice a]
    _ = (36 : ℝ≥0∞)⁻¹ := by
      simpa using six_mul_invTwoHundredSixteen_eq_invThirtySix

-- Proof sketch: compute the probabilities of the pairwise intersections by counting outcomes in
-- the `216`-point sample space.
/-- The three diagonal equality events are pairwise independent. -/
theorem diagonalEqualityEvents_pairwise :
    Pairwise fun i j ↦ IndepSet (diagonalEqualityEvents i) (diagonalEqualityEvents j)
      threeRollsMeasure := by
  intro i j hij
  -- Rewrite independence as the product formula for the intersection measure.
  refine (indepSet_iff_measure_inter_eq_mul (measurableSet_diagonalEqualityEvents i)
    (measurableSet_diagonalEqualityEvents j) threeRollsMeasure).2 ?_
  calc
    threeRollsMeasure (diagonalEqualityEvents i ∩ diagonalEqualityEvents j) =
        threeRollsMeasure allEqualEvent := by
          rw [diagonalEqualityEvents_inter_eq_allEqual hij]
    _ = (36 : ℝ≥0∞)⁻¹ := threeRollsMeasure_allEqualEvent
    _ = (6 : ℝ≥0∞)⁻¹ * (6 : ℝ≥0∞)⁻¹ := by
      symm
      simpa [pow_two] using invSixSq_eq_invThirtySix
    _ = threeRollsMeasure (diagonalEqualityEvents i) *
        threeRollsMeasure (diagonalEqualityEvents j) := by
          rw [threeRollsMeasure_diagonalEqualityEvent i, threeRollsMeasure_diagonalEqualityEvent j]

-- Proof sketch: all three diagonal equalities hold exactly when all three rolls coincide, so the
-- probability of the triple intersection is `1 / 36`, whereas the product of the three marginal
-- probabilities is `1 / 216`.
/-- The three diagonal equality events are not independent as a family. -/
theorem diagonalEqualityEvents_not_iIndep :
    ¬ iIndepSet diagonalEqualityEvents threeRollsMeasure := by
  intro hIndep
  -- Compare the triple intersection probability with the product of the marginals.
  have hMeasure :
      threeRollsMeasure allEqualEvent =
        ∏ i ∈ (Finset.univ : Finset (Fin 3)),
          threeRollsMeasure (diagonalEqualityEvents i) := by
    simpa [iInter_diagonalEqualityEvents_eq_allEqual] using
      hIndep.meas_biInter (Finset.univ : Finset (Fin 3))
  have hContradiction : (36 : ℝ≥0∞)⁻¹ = (216 : ℝ≥0∞)⁻¹ := by
    calc
      (36 : ℝ≥0∞)⁻¹ = threeRollsMeasure allEqualEvent := by
        symm
        exact threeRollsMeasure_allEqualEvent
      _ = ∏ i ∈ (Finset.univ : Finset (Fin 3)),
          threeRollsMeasure (diagonalEqualityEvents i) := hMeasure
      _ = (216 : ℝ≥0∞)⁻¹ := by
        have hProd :
            (∏ i ∈ (Finset.univ : Finset (Fin 3)),
              threeRollsMeasure (diagonalEqualityEvents i)) = ((6 : ℝ≥0∞)⁻¹) ^ 3 := by
          simp [threeRollsMeasure_diagonalEqualityEvent]
        rw [hProd]
        exact invSixCube_eq_invTwoHundredSixteen
  norm_num at hContradiction

-- Proof sketch: for the first clause, use that `threeRollsMeasure` is the uniform product measure
-- on `Fin 3 → Fin 6`, so events depending on disjoint coordinates are independent. For the second
-- clause, compute the probabilities of the three diagonal events and of their intersections by
-- counting outcomes.
/-- Example 2.2: For three fair die rolls, events depending separately on the first, second, and
third coordinate are independent, while the events `ω₁ = ω₂`, `ω₂ = ω₃`, and `ω₁ = ω₃` are
pairwise independent but not independent as a triple. -/
theorem roll_three_times_independence_examples :
    (∀ S : Fin 3 → Set Die,
      iIndepSet (fun i ↦ Function.eval i ⁻¹' S i) threeRollsMeasure) ∧
    Pairwise (fun i j ↦ IndepSet (diagonalEqualityEvents i) (diagonalEqualityEvents j)
      threeRollsMeasure) ∧
    ¬ iIndepSet diagonalEqualityEvents threeRollsMeasure := by
  exact ⟨coordinatePreimage_iIndepSet, diagonalEqualityEvents_pairwise,
    diagonalEqualityEvents_not_iIndep⟩
