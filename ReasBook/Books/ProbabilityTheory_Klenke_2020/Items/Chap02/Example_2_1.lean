/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open Set MeasureTheory ProbabilityTheory

noncomputable section

/-- The six outcomes of a single fair die, modeled by `Fin 6`. -/
abbrev Die := Fin 6

/-- The sample space of two successive die rolls. -/
abbrev TwoRolls := Die × Die

/-- The uniform law of a single fair die roll. -/
noncomputable abbrev dieMeasure : Measure Die :=
  (PMF.uniformOfFintype Die).toMeasure

/-- The law of two independent fair die rolls. -/
noncomputable abbrev twoRollMeasure : Measure TwoRolls :=
  dieMeasure.prod dieMeasure

/-- The event that the sum of the two rolls is odd. With the `Fin 6` encoding of die faces by
`0, 1, ..., 5`, this is equivalent to oddness of the textbook face sum after adding `1` to each
coordinate. -/
def oddSumEvent : Set TwoRolls :=
  {ω | Odd ((ω.1 : ℕ) + (ω.2 : ℕ))}

/-- The event that the first roll is at most three. In the `Fin 6` encoding this is the condition
`ω.1 < 3`, corresponding to the textbook faces `{1, 2, 3}`. -/
def firstRollAtMostThreeEvent : Set TwoRolls :=
  {ω | (ω.1 : ℕ) < 3}

-- Proof sketch: under the product law `twoRollMeasure`, the coordinate projections are
-- independent; apply this to the preimages of `A` and `B` under `Prod.fst` and `Prod.snd`.
/-- Item (i) of Example 2.1. Under the uniform distribution on two die rolls, an event depending
only on the first roll is independent of an event depending only on the second roll. -/
theorem firstRollCylinder_indep_secondRollCylinder (A B : Set Die) :
    IndepSet (Prod.fst ⁻¹' A) (Prod.snd ⁻¹' B) twoRollMeasure := by
  -- The two coordinate projections are independent under the product law.
  have hprod : (fun ω : TwoRolls ↦ ω.1) ⟂ᵢ[twoRollMeasure] (fun ω ↦ ω.2) := by
    simpa [twoRollMeasure] using
      (ProbabilityTheory.indepFun_prod (μ := dieMeasure) (ν := dieMeasure)
        (X := fun x : Die ↦ x) (Y := fun y : Die ↦ y) measurable_id measurable_id)
  -- Specialize independence of the coordinate maps to the chosen cylinder events.
  rw [ProbabilityTheory.indepFun_iff_indepSet_preimage measurable_fst measurable_snd] at hprod
  simpa using hprod A B (by simp) (by simp)

-- Proof sketch: compute the uniform probabilities of `oddSumEvent`,
-- `firstRollAtMostThreeEvent`, and their intersection by counting favorable outcomes in the `36`
-- point sample space, then conclude with the characterization of independence by
-- `μ (A ∩ B) = μ A * μ B`.
/-- Example 2.1: Item (ii) of the rolling-two-dice example. The event that the sum is odd is
independent of the event that the first roll is at most three. -/
theorem oddSumEvent_indep_firstRollAtMostThreeEvent :
    IndepSet oddSumEvent firstRollAtMostThreeEvent twoRollMeasure := by
  let oddFaces : Set Die := {i | Odd (i : ℕ)}
  let evenFaces : Set Die := {i | Even (i : ℕ)}
  let smallFaces : Set Die := {i | (i : ℕ) < 3}
  -- Split oddness of a sum into the two complementary parity cases.
  have odd_add_iff {a b : ℕ} : Odd (a + b) ↔ Odd a ∧ Even b ∨ Even a ∧ Odd b := by
    constructor
    · intro hab
      have hparity : Odd a ↔ Even b := (Nat.odd_add.mp hab)
      by_cases ha : Odd a
      · exact Or.inl ⟨ha, hparity.mp ha⟩
      · have haEven : Even a := Nat.not_odd_iff_even.mp ha
        have hbOdd : Odd b := by
          apply Nat.not_even_iff_odd.mp
          intro hbEven
          exact ha (hparity.mpr hbEven)
        exact Or.inr ⟨haEven, hbOdd⟩
    · intro hab
      rcases hab with ⟨haOdd, hbEven⟩ | ⟨haEven, hbOdd⟩
      · exact Nat.odd_add.mpr ⟨fun _ ↦ hbEven, fun _ ↦ haOdd⟩
      · exact Nat.odd_add.mpr
          ⟨fun haOdd ↦ False.elim ((Nat.not_odd_iff_even.mpr haEven) haOdd),
            fun hbEven ↦ False.elim ((Nat.not_even_iff_odd.mpr hbOdd) hbEven)⟩
  -- Rewrite the odd-sum event as the union of the two parity rectangles.
  have oddSumEvent_eq_parityRectangles :
      oddSumEvent = (oddFaces ×ˢ evenFaces) ∪ (evenFaces ×ˢ oddFaces) := by
    ext ω
    simpa [oddSumEvent, oddFaces, evenFaces, Set.mem_union, Set.mem_prod, Set.mem_setOf_eq] using
      (odd_add_iff (a := (ω.1 : ℕ)) (b := (ω.2 : ℕ)))
  -- Intersecting with `firstRollAtMostThreeEvent` only restricts the first coordinate.
  have oddSumEvent_inter_firstRollAtMostThreeEvent_eq_restrictedParityRectangles :
      oddSumEvent ∩ firstRollAtMostThreeEvent =
        ((smallFaces ∩ oddFaces) ×ˢ evenFaces) ∪ ((smallFaces ∩ evenFaces) ×ˢ oddFaces) := by
    ext ω
    simp only [oddSumEvent, firstRollAtMostThreeEvent, oddFaces, evenFaces, smallFaces,
      Set.mem_inter_iff, Set.mem_union, Set.mem_prod, Set.mem_setOf_eq]
    constructor
    · rintro ⟨hOddSum, hSmall⟩
      rcases odd_add_iff.mp hOddSum with hParity | hParity
      · exact Or.inl ⟨⟨hSmall, hParity.1⟩, hParity.2⟩
      · exact Or.inr ⟨⟨hSmall, hParity.1⟩, hParity.2⟩
    · rintro (⟨⟨hSmall, hOdd⟩, hEven⟩ | ⟨⟨hSmall, hEven⟩, hOdd⟩)
      · exact ⟨odd_add_iff.mpr (Or.inl ⟨hOdd, hEven⟩), hSmall⟩
      · exact ⟨odd_add_iff.mpr (Or.inr ⟨hEven, hOdd⟩), hSmall⟩
  -- The two parity rectangles are disjoint because a die face cannot be both odd and even.
  have parityRectangles_disjoint :
      Disjoint (oddFaces ×ˢ evenFaces) (evenFaces ×ˢ oddFaces) := by
    rw [Set.disjoint_left]
    intro ω h₁ h₂
    have h₁' : ω.1 ∈ oddFaces ∧ ω.2 ∈ evenFaces := by
      simpa [Set.mem_prod] using h₁
    have h₂' : ω.1 ∈ evenFaces ∧ ω.2 ∈ oddFaces := by
      simpa [Set.mem_prod] using h₂
    have hodd : Odd (ω.1 : ℕ) := by
      simpa [oddFaces] using h₁'.1
    have heven : Even (ω.1 : ℕ) := by
      simpa [evenFaces] using h₂'.1
    exact (Nat.not_odd_iff_even.mpr heven) hodd
  -- The same argument gives disjointness after restricting the first coordinate.
  have restrictedParityRectangles_disjoint :
      Disjoint ((smallFaces ∩ oddFaces) ×ˢ evenFaces) ((smallFaces ∩ evenFaces) ×ˢ oddFaces) := by
    rw [Set.disjoint_left]
    intro ω h₁ h₂
    have h₁' : ω.1 ∈ smallFaces ∩ oddFaces ∧ ω.2 ∈ evenFaces := by
      simpa [Set.mem_prod] using h₁
    have h₂' : ω.1 ∈ smallFaces ∩ evenFaces ∧ ω.2 ∈ oddFaces := by
      simpa [Set.mem_prod] using h₂
    have hodd : Odd (ω.1 : ℕ) := by
      simpa [oddFaces] using h₁'.1.2
    have heven : Even (ω.1 : ℕ) := by
      simpa [evenFaces] using h₂'.1.2
    exact (Nat.not_odd_iff_even.mpr heven) hodd
  -- `firstRollAtMostThreeEvent` is the cylinder over `smallFaces`.
  have firstRollAtMostThreeEvent_eq_smallCylinder :
      firstRollAtMostThreeEvent = smallFaces ×ˢ (Set.univ : Set Die) := by
    ext ω
    simp [firstRollAtMostThreeEvent, smallFaces]
  -- On a finite uniform space, the measure is cardinality divided by six.
  have dieMeasure_apply_eq_card (s : Set Die) [Fintype s] :
      dieMeasure s = (Fintype.card s : ENNReal) / 6 := by
    simpa [dieMeasure] using
      (PMF.toMeasure_uniformOfFintype_apply (α := Die) (s := s) (by simp : MeasurableSet s))
  -- Record the small ENNReal identities needed after counting.
  have half_ne_top : ((1 : ENNReal) / 2) ≠ ⊤ :=
    ENNReal.div_ne_top (by simp) (by norm_num)
  have third_ne_top : ((1 : ENNReal) / 3) ≠ ⊤ :=
    ENNReal.div_ne_top (by simp) (by norm_num)
  have quarter_ne_top : ((1 : ENNReal) / 4) ≠ ⊤ :=
    ENNReal.div_ne_top (by simp) (by norm_num)
  have sixth_ne_top : ((1 : ENNReal) / 6) ≠ ⊤ :=
    ENNReal.div_ne_top (by simp) (by norm_num)
  have half_toReal : ((1 : ENNReal) / 2).toReal = (1 : ℝ) / 2 := by
    rw [ENNReal.toReal_div]
    norm_num
  have third_toReal : ((1 : ENNReal) / 3).toReal = (1 : ℝ) / 3 := by
    rw [ENNReal.toReal_div]
    norm_num
  have quarter_toReal : ((1 : ENNReal) / 4).toReal = (1 : ℝ) / 4 := by
    rw [ENNReal.toReal_div]
    norm_num
  have sixth_toReal : ((1 : ENNReal) / 6).toReal = (1 : ℝ) / 6 := by
    rw [ENNReal.toReal_div]
    norm_num
  have threeSixths_eq_half : (3 : ENNReal) / 6 = (1 : ENNReal) / 2 := by
    apply (ENNReal.toReal_eq_toReal_iff'
      (ENNReal.div_ne_top (by simp) (by norm_num)) half_ne_top).mp
    rw [ENNReal.toReal_div, ENNReal.toReal_div]
    norm_num
  have twoSixths_eq_third : (2 : ENNReal) / 6 = (1 : ENNReal) / 3 := by
    apply (ENNReal.toReal_eq_toReal_iff'
      (ENNReal.div_ne_top (by simp) (by norm_num)) third_ne_top).mp
    rw [ENNReal.toReal_div, ENNReal.toReal_div]
    norm_num
  have half_mul_half_add_half_mul_half :
      (1 : ENNReal) / 2 * ((1 : ENNReal) / 2) +
          (1 : ENNReal) / 2 * ((1 : ENNReal) / 2) =
        (1 : ENNReal) / 2 := by
    apply (ENNReal.toReal_eq_toReal_iff'
      (by
        refine ENNReal.add_ne_top.2 ?_
        constructor <;> exact ENNReal.mul_ne_top half_ne_top half_ne_top)
      half_ne_top).mp
    rw [ENNReal.toReal_add]
    · norm_num
    · exact ENNReal.mul_ne_top half_ne_top half_ne_top
    · exact ENNReal.mul_ne_top half_ne_top half_ne_top
  have sixth_mul_half_add_third_mul_half :
      (1 : ENNReal) / 6 * ((1 : ENNReal) / 2) +
          (1 : ENNReal) / 3 * ((1 : ENNReal) / 2) =
        (1 : ENNReal) / 4 := by
    apply (ENNReal.toReal_eq_toReal_iff'
      (by
        refine ENNReal.add_ne_top.2 ?_
        constructor
        · exact ENNReal.mul_ne_top sixth_ne_top half_ne_top
        · exact ENNReal.mul_ne_top third_ne_top half_ne_top)
      quarter_ne_top).mp
    rw [ENNReal.toReal_add]
    · norm_num
    · exact ENNReal.mul_ne_top sixth_ne_top half_ne_top
    · exact ENNReal.mul_ne_top third_ne_top half_ne_top
  have quarter_eq_half_mul_half :
      (1 : ENNReal) / 4 = ((1 : ENNReal) / 2) * ((1 : ENNReal) / 2) := by
    apply (ENNReal.toReal_eq_toReal_iff'
      quarter_ne_top (ENNReal.mul_ne_top half_ne_top half_ne_top)).mp
    norm_num
  -- Count the one-dimensional events needed for the rectangle probabilities.
  have oddFaces_measure : dieMeasure oddFaces = (1 : ENNReal) / 2 := by
    have hcard : Fintype.card oddFaces = 3 := by
      decide
    rw [dieMeasure_apply_eq_card oddFaces, hcard]
    simpa [ENNReal.div_eq_inv_mul, mul_comm, mul_left_comm, mul_assoc] using threeSixths_eq_half
  have evenFaces_measure : dieMeasure evenFaces = (1 : ENNReal) / 2 := by
    have hcard : Fintype.card evenFaces = 3 := by
      decide
    rw [dieMeasure_apply_eq_card evenFaces, hcard]
    simpa [ENNReal.div_eq_inv_mul, mul_comm, mul_left_comm, mul_assoc] using threeSixths_eq_half
  have smallFaces_measure : dieMeasure smallFaces = (1 : ENNReal) / 2 := by
    have hcard : Fintype.card smallFaces = 3 := by
      decide
    rw [dieMeasure_apply_eq_card smallFaces, hcard]
    simpa [ENNReal.div_eq_inv_mul, mul_comm, mul_left_comm, mul_assoc] using threeSixths_eq_half
  have smallOdd_measure : dieMeasure (smallFaces ∩ oddFaces) = (1 : ENNReal) / 6 := by
    have hcard : Fintype.card ↥(smallFaces ∩ oddFaces) = 1 := by
      decide
    rw [dieMeasure_apply_eq_card (smallFaces ∩ oddFaces), hcard]
    norm_num
  have smallEven_measure : dieMeasure (smallFaces ∩ evenFaces) = (1 : ENNReal) / 3 := by
    have hcard : Fintype.card ↥(smallFaces ∩ evenFaces) = 2 := by
      decide
    rw [dieMeasure_apply_eq_card (smallFaces ∩ evenFaces), hcard]
    simpa [ENNReal.div_eq_inv_mul, mul_comm, mul_left_comm, mul_assoc] using twoSixths_eq_third
  -- The decompositions also supply measurability of the two events.
  have oddSumEvent_measurable : MeasurableSet oddSumEvent := by
    rw [oddSumEvent_eq_parityRectangles]
    apply MeasurableSet.union
    · apply MeasurableSet.prod <;> simp [oddFaces, evenFaces]
    · apply MeasurableSet.prod <;> simp [oddFaces, evenFaces]
  have firstRollAtMostThreeEvent_measurable : MeasurableSet firstRollAtMostThreeEvent := by
    rw [firstRollAtMostThreeEvent_eq_smallCylinder]
    apply MeasurableSet.prod <;> simp [smallFaces]
  -- Evaluate the three probabilities in the independence criterion.
  have oddSumEvent_measure : twoRollMeasure oddSumEvent = (1 : ENNReal) / 2 := by
    rw [oddSumEvent_eq_parityRectangles]
    rw [measure_union parityRectangles_disjoint]
    · simp [twoRollMeasure, oddFaces_measure, evenFaces_measure]
      simpa [ENNReal.div_eq_inv_mul, mul_comm, mul_left_comm, mul_assoc] using
        half_mul_half_add_half_mul_half
    · apply MeasurableSet.prod <;> simp [oddFaces, evenFaces]
  have firstRollAtMostThreeEvent_measure :
      twoRollMeasure firstRollAtMostThreeEvent = (1 : ENNReal) / 2 := by
    rw [firstRollAtMostThreeEvent_eq_smallCylinder]
    simp [twoRollMeasure, smallFaces_measure]
  have intersection_measure :
      twoRollMeasure (oddSumEvent ∩ firstRollAtMostThreeEvent) = (1 : ENNReal) / 4 := by
    rw [oddSumEvent_inter_firstRollAtMostThreeEvent_eq_restrictedParityRectangles]
    rw [measure_union restrictedParityRectangles_disjoint]
    · simp [twoRollMeasure, smallOdd_measure, smallEven_measure, oddFaces_measure,
        evenFaces_measure]
      simpa [ENNReal.div_eq_inv_mul, mul_comm, mul_left_comm, mul_assoc] using
        sixth_mul_half_add_third_mul_half
    · apply MeasurableSet.prod <;> simp [oddFaces, evenFaces, smallFaces]
  -- Conclude from the measure characterization of independence on probability spaces.
  refine (ProbabilityTheory.indepSet_iff_measure_inter_eq_mul
    (s := oddSumEvent) (t := firstRollAtMostThreeEvent) (μ := twoRollMeasure)
    oddSumEvent_measurable firstRollAtMostThreeEvent_measurable).2 ?_
  rw [intersection_measure, oddSumEvent_measure, firstRollAtMostThreeEvent_measure]
  simpa [ENNReal.div_eq_inv_mul, mul_comm, mul_left_comm, mul_assoc] using quarter_eq_half_mul_half
