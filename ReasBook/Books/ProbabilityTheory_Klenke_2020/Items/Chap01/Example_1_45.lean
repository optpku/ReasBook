/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib

open MeasureTheory
open scoped ENNReal

/-- The first generating set in Example 1.45 (i), modeled on `Fin 4`. -/
def firstGeneratorOne : Set (Fin 4) := {0, 1}

/-- The second generating set in Example 1.45 (i), modeled on `Fin 4`. -/
def firstGeneratorTwo : Set (Fin 4) := {1, 2}

/-- The family `{{0, 1}, {1, 2}}` used in Example 1.45 (i). -/
def firstGeneratingFamily : Set (Set (Fin 4)) := {firstGeneratorOne, firstGeneratorTwo}

/-- The measure `1 / 2 * δ_0 + 1 / 2 * δ_2` from Example 1.45 (i). -/
noncomputable def firstCounterexampleMeasureOne : Measure (Fin 4) :=
  (1 / 2 : ℝ≥0∞) • Measure.dirac 0 + (1 / 2 : ℝ≥0∞) • Measure.dirac 2

/-- The measure `1 / 2 * δ_1 + 1 / 2 * δ_3` from Example 1.45 (i). -/
noncomputable def firstCounterexampleMeasureTwo : Measure (Fin 4) :=
  (1 / 2 : ℝ≥0∞) • Measure.dirac 1 + (1 / 2 : ℝ≥0∞) • Measure.dirac 3

/-- The singleton generator `{0}` used in Example 1.45 (ii), modeling `{1}` on `Fin 2`. -/
def secondGenerator : Set (Fin 2) := {0}

/-- The family `{{0}}` used in Example 1.45 (ii). -/
def secondGeneratingFamily : Set (Set (Fin 2)) := {secondGenerator}

/-- The Dirac measure `δ_1` used in Example 1.45 (ii). -/
noncomputable def secondCounterexampleMeasure : Measure (Fin 2) := Measure.dirac 1

-- Proof sketch: on `Fin 4`, the two generators separate points, so the measurable space they
-- generate is the full sigma-algebra on the finite ambient type.
/-- Example 1.45 (1): Part (i). On the four-point space modeled by `Fin 4`, the family
`{{0, 1}, {1, 2}}` generates the full sigma-algebra. -/
theorem firstGeneratingFamily_generateFrom_eq_top :
    MeasurableSpace.generateFrom firstGeneratingFamily = ⊤ := by
  rw [eq_top_iff]
  intro s hs
  have h_one :
      MeasurableSet[MeasurableSpace.generateFrom firstGeneratingFamily] firstGeneratorOne :=
    MeasurableSpace.measurableSet_generateFrom <| by simp [firstGeneratingFamily]
  have h_two :
      MeasurableSet[MeasurableSpace.generateFrom firstGeneratingFamily] firstGeneratorTwo :=
    MeasurableSpace.measurableSet_generateFrom <| by simp [firstGeneratingFamily]
  have h_zero_singleton :
      MeasurableSet[MeasurableSpace.generateFrom firstGeneratingFamily] ({0} : Set (Fin 4)) := by
    convert h_one.diff h_two using 1
    ext x <;> fin_cases x <;> simp [firstGeneratorOne, firstGeneratorTwo]
  have h_one_singleton :
      MeasurableSet[MeasurableSpace.generateFrom firstGeneratingFamily] ({1} : Set (Fin 4)) := by
    convert h_one.inter h_two using 1
    ext x <;> fin_cases x <;> simp [firstGeneratorOne, firstGeneratorTwo]
  have h_two_singleton :
      MeasurableSet[MeasurableSpace.generateFrom firstGeneratingFamily] ({2} : Set (Fin 4)) := by
    convert h_two.diff h_one using 1
    ext x <;> fin_cases x <;> simp [firstGeneratorOne, firstGeneratorTwo]
  have h_three_singleton :
      MeasurableSet[MeasurableSpace.generateFrom firstGeneratingFamily] ({3} : Set (Fin 4)) := by
    convert (h_one.union h_two).compl using 1
    ext x <;> fin_cases x <;> simp [firstGeneratorOne, firstGeneratorTwo]
  have h_singleton :
      ∀ x : Fin 4,
        MeasurableSet[MeasurableSpace.generateFrom firstGeneratingFamily] ({x} : Set (Fin 4)) := by
    intro x
    fin_cases x
    · simpa using h_zero_singleton
    · simpa using h_one_singleton
    · simpa using h_two_singleton
    · simpa using h_three_singleton
  simpa using (Set.toFinite s).measurableSet_biUnion (fun x hx ↦ h_singleton x)

-- Proof sketch: the two generators intersect in the singleton `{1}`, which is nonempty but does
-- not belong to `{{0, 1}, {1, 2}}`.
/-- Example 1.45 (2): Part (i). The family `{{0, 1}, {1, 2}}` is not a pi-system. -/
theorem firstGeneratingFamily_not_isPiSystem :
    ¬ IsPiSystem firstGeneratingFamily := by
  intro h_pi
  have h_inter_mem :
      firstGeneratorOne ∩ firstGeneratorTwo ∈ firstGeneratingFamily := by
    have h_nonempty : (firstGeneratorOne ∩ firstGeneratorTwo : Set (Fin 4)).Nonempty := by
      refine ⟨1, by simp [firstGeneratorOne, firstGeneratorTwo]⟩
    exact h_pi firstGeneratorOne (by simp [firstGeneratingFamily]) firstGeneratorTwo
      (by simp [firstGeneratingFamily]) h_nonempty
  have h_mem :
      ({1} : Set (Fin 4)) ∈ firstGeneratingFamily := by
    have h_inter :
        firstGeneratorOne ∩ firstGeneratorTwo = ({1} : Set (Fin 4)) := by
      ext x <;> fin_cases x <;> simp [firstGeneratorOne, firstGeneratorTwo]
    simpa [h_inter] using h_inter_mem
  rcases (by simpa [firstGeneratingFamily] using h_mem :
      ({1} : Set (Fin 4)) = firstGeneratorOne ∨ ({1} : Set (Fin 4)) = firstGeneratorTwo) with
    h_eq | h_eq
  · have : (0 : Fin 4) ∈ ({1} : Set (Fin 4)) := by
      exact h_eq.symm ▸ by simp [firstGeneratorOne]
    simp at this
  · have : (2 : Fin 4) ∈ ({1} : Set (Fin 4)) := by
      exact h_eq.symm ▸ by simp [firstGeneratorTwo]
    simp at this

-- Proof sketch: compute the total mass of the convex combination
-- `1 / 2 * δ_0 + 1 / 2 * δ_2` on `univ`.
/-- Example 1.45 (3): Part (i). The measure `1 / 2 * δ_0 + 1 / 2 * δ_2` is a probability
measure. -/
instance : IsProbabilityMeasure firstCounterexampleMeasureOne :=
by
  refine ⟨by simpa [firstCounterexampleMeasureOne, one_div] using ENNReal.inv_two_add_inv_two⟩

-- Proof sketch: compute the total mass of the convex combination
-- `1 / 2 * δ_1 + 1 / 2 * δ_3` on `univ`.
/-- Example 1.45 (4): Part (i). The measure `1 / 2 * δ_1 + 1 / 2 * δ_3` is a probability
measure. -/
instance : IsProbabilityMeasure firstCounterexampleMeasureTwo :=
by
  refine ⟨by simpa [firstCounterexampleMeasureTwo, one_div] using ENNReal.inv_two_add_inv_two⟩

-- Proof sketch: evaluate both measures on a singleton such as `{0}` or `{1}` to distinguish
-- them.
/-- Example 1.45 (5): Part (i). The two displayed probability measures on `Fin 4` are distinct. -/
theorem firstCounterexampleMeasures_ne :
    firstCounterexampleMeasureOne ≠ firstCounterexampleMeasureTwo := by
  intro h_eq
  have h_apply :
      firstCounterexampleMeasureOne ({0} : Set (Fin 4)) =
        firstCounterexampleMeasureTwo ({0} : Set (Fin 4)) :=
    congrArg (fun μ : Measure (Fin 4) ↦ μ ({0} : Set (Fin 4))) h_eq
  simp [firstCounterexampleMeasureOne, firstCounterexampleMeasureTwo] at h_apply

-- Proof sketch: evaluate the two Dirac summands on `{0, 1}` and use additivity of measures on
-- this finite space.
/-- Example 1.45 (6): Part (i). The measure `1 / 2 * δ_0 + 1 / 2 * δ_2` assigns mass `1 / 2` to
the generator `{0, 1}`. -/
theorem firstCounterexampleMeasureOne_apply_firstGeneratorOne :
    firstCounterexampleMeasureOne firstGeneratorOne = (1 / 2 : ℝ≥0∞) := by
  simp [firstCounterexampleMeasureOne, firstGeneratorOne]

-- Proof sketch: only the Dirac mass at `1` contributes on the set `{0, 1}`.
/-- Example 1.45 (7): Part (i). The measure `1 / 2 * δ_1 + 1 / 2 * δ_3` assigns mass `1 / 2` to
the generator `{0, 1}`. -/
theorem firstCounterexampleMeasureTwo_apply_firstGeneratorOne :
    firstCounterexampleMeasureTwo firstGeneratorOne = (1 / 2 : ℝ≥0∞) := by
  simp [firstCounterexampleMeasureTwo, firstGeneratorOne]

-- Proof sketch: only the Dirac mass at `2` contributes on the set `{1, 2}`.
/-- Example 1.45 (8): Part (i). The measure `1 / 2 * δ_0 + 1 / 2 * δ_2` assigns mass `1 / 2` to
the generator `{1, 2}`. -/
theorem firstCounterexampleMeasureOne_apply_firstGeneratorTwo :
    firstCounterexampleMeasureOne firstGeneratorTwo = (1 / 2 : ℝ≥0∞) := by
  simp [firstCounterexampleMeasureOne, firstGeneratorTwo]

-- Proof sketch: only the Dirac mass at `1` contributes on the set `{1, 2}`.
/-- Example 1.45 (9): Part (i). The measure `1 / 2 * δ_1 + 1 / 2 * δ_3` assigns mass `1 / 2` to
the generator `{1, 2}`. -/
theorem firstCounterexampleMeasureTwo_apply_firstGeneratorTwo :
    firstCounterexampleMeasureTwo firstGeneratorTwo = (1 / 2 : ℝ≥0∞) := by
  simp [firstCounterexampleMeasureTwo, firstGeneratorTwo]

-- Proof sketch: a singleton family is automatically closed under nonempty binary intersections,
-- since any two members are equal.
/-- Example 1.45 (10): Part (ii). On the two-point space modeled by `Fin 2`, the family `{{0}}`
is a pi-system. -/
theorem secondGeneratingFamily_isPiSystem :
    IsPiSystem secondGeneratingFamily := by
  simpa [secondGeneratingFamily] using IsPiSystem.singleton secondGenerator

-- Proof sketch: the generator `{0}` separates the two points of `Fin 2`, so the generated
-- measurable space is the full sigma-algebra.
/-- Example 1.45 (11): Part (ii). On `Fin 2`, the family `{{0}}` generates the full
sigma-algebra. -/
theorem secondGeneratingFamily_generateFrom_eq_top :
    MeasurableSpace.generateFrom secondGeneratingFamily = ⊤ := by
  rw [eq_top_iff]
  intro s hs
  have h_zero :
      MeasurableSet[MeasurableSpace.generateFrom secondGeneratingFamily] secondGenerator :=
    MeasurableSpace.measurableSet_generateFrom <| by simp [secondGeneratingFamily]
  have h_one :
      MeasurableSet[MeasurableSpace.generateFrom secondGeneratingFamily] ({1} : Set (Fin 2)) := by
    convert h_zero.compl using 1
    ext x <;> fin_cases x <;> simp [secondGenerator]
  have h_singleton :
      ∀ x : Fin 2,
        MeasurableSet[MeasurableSpace.generateFrom secondGeneratingFamily] ({x} : Set (Fin 2)) := by
    intro x
    fin_cases x
    · simpa [secondGenerator] using h_zero
    · simpa using h_one
  simpa using (Set.toFinite s).measurableSet_biUnion (fun x hx ↦ h_singleton x)

-- Proof sketch: a probability measure on `Fin 2` is determined by the mass of `{0}`, because the
-- complementary singleton has mass `1 - μ {0}`.
/-- Example 1.45 (12): Part (ii). Probability measures on `Fin 2` are determined by their value
on the generator `{0}`. -/
theorem probabilityMeasure_eq_of_apply_secondGenerator_eq
    (μ ν : Measure (Fin 2)) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (h_apply : μ secondGenerator = ν secondGenerator) :
    μ = ν := by
  have h_generate :
      (inferInstance : MeasurableSpace (Fin 2)) =
        MeasurableSpace.generateFrom secondGeneratingFamily := by
    exact rfl.trans secondGeneratingFamily_generateFrom_eq_top.symm
  refine ext_of_generate_finite secondGeneratingFamily h_generate secondGeneratingFamily_isPiSystem ?_ ?_
  · intro s hs
    simp [secondGeneratingFamily] at hs
    simpa [hs] using h_apply
  · simp

-- Proof sketch: the zero measure has total mass `0`, hence finite total mass.
/-- Example 1.45 (13): Part (ii). The zero measure on `Fin 2` is finite. -/
instance : IsFiniteMeasure (0 : Measure (Fin 2)) := by
  infer_instance

-- Proof sketch: every Dirac measure has finite total mass, in particular `δ_1`.
/-- Example 1.45 (14): Part (ii). The measure `δ_1` on `Fin 2` is finite. -/
instance : IsFiniteMeasure secondCounterexampleMeasure := by
  simpa [secondCounterexampleMeasure] using
    (inferInstance : IsFiniteMeasure (Measure.dirac (1 : Fin 2)))

-- Proof sketch: the zero measure and `δ_1` differ, for instance on the singleton `{1}`.
/-- Example 1.45 (15): Part (ii). The finite measures `0` and `δ_1` on `Fin 2` are distinct. -/
theorem zero_measure_ne_secondCounterexampleMeasure :
    (0 : Measure (Fin 2)) ≠ secondCounterexampleMeasure := by
  intro h_eq
  have h_apply :
      (0 : Measure (Fin 2)) ({1} : Set (Fin 2)) = secondCounterexampleMeasure ({1} : Set (Fin 2)) :=
    congrArg (fun μ : Measure (Fin 2) ↦ μ ({1} : Set (Fin 2))) h_eq
  simp [secondCounterexampleMeasure] at h_apply

-- Proof sketch: both measures assign mass `0` to the singleton `{0}`.
/-- Example 1.45 (16): Part (ii). The measures `0` and `δ_1` agree on the generator `{0}`. -/
theorem zero_measure_apply_secondGenerator_eq :
    (0 : Measure (Fin 2)) secondGenerator = secondCounterexampleMeasure secondGenerator := by
  simp [secondGenerator, secondCounterexampleMeasure]
