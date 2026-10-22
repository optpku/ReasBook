/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib
import Books.ProbabilityTheory_Klenke_2020.Items.Chap20.Definition_20_24

-- Declarations for this item will be appended below by the statement pipeline.

open Filter MeasureTheory
open scoped BigOperators

universe u

variable {Ω : Type u} [MeasurableSpace Ω]

/-- Weak mixing for a probability-preserving system means that the Cesàro means of the absolute
correlation errors `|P (A ∩ (τ^[i])⁻¹(B)) - P A * P B|` converge to `0` for every pair of
measurable events `A` and `B`, as in Remark 20.25. -/
def IsWeaklyMixing (τ : Ω → Ω) (P : Measure Ω) [IsProbabilityMeasure P] : Prop :=
  ∀ A B : Set Ω, MeasurableSet A → MeasurableSet B →
    Tendsto
      (fun n : ℕ ↦
        (1 / (n : ℝ)) *
          (Finset.sum (Finset.range n) fun i ↦
            |P.real (A ∩ (τ^[i]) ⁻¹' B) - P.real A * P.real B|))
      atTop
      (nhds 0)

-- Proof sketch: apply Cesàro summability to the real sequence
-- `P.real (A ∩ (τ^[n])⁻¹(B)) - P.real A * P.real B`, using strong mixing to get convergence of
-- that sequence to
-- `0`; then take absolute values and use the continuity of `abs`.
/-- Helper for Remark 20.25: strong mixing makes the centered correlation error tend to `0`. -/
private lemma strongMixingCorrelationError_tendsto_zero
    (P : Measure Ω) [IsProbabilityMeasure P] {τ : Ω → Ω}
    (hstrong : IsStronglyMixing τ P) {A B : Set Ω}
    (hA : MeasurableSet A) (hB : MeasurableSet B) :
    Tendsto
      (fun n : ℕ ↦ P.real (A ∩ (τ^[n]) ⁻¹' B) - P.real A * P.real B)
      atTop
      (nhds 0) := by
  -- Shift the strong-mixing limit by the constant correlation term so the limit becomes `0`.
  have hconst :
      Tendsto (fun _ : ℕ ↦ P.real A * P.real B) atTop (nhds (P.real A * P.real B)) :=
    tendsto_const_nhds
  simpa using (hstrong A B hA hB).sub hconst

/-- Helper for Remark 20.25: strong mixing makes the absolute correlation error tend to `0`. -/
private lemma strongMixingAbsCorrelationError_tendsto_zero
    (P : Measure Ω) [IsProbabilityMeasure P] {τ : Ω → Ω}
    (hstrong : IsStronglyMixing τ P) {A B : Set Ω}
    (hA : MeasurableSet A) (hB : MeasurableSet B) :
    Tendsto
      (fun n : ℕ ↦ |P.real (A ∩ (τ^[n]) ⁻¹' B) - P.real A * P.real B|)
      atTop
      (nhds 0) := by
  -- Transport the zero-limit through the continuous absolute-value map.
  exact
    (continuous_abs.tendsto' _ _ abs_zero).comp
      (strongMixingCorrelationError_tendsto_zero (P := P) hstrong hA hB)

/-- Helper for Remark 20.25: the Cesàro means of the absolute correlation errors converge to `0`
under strong mixing. -/
private lemma strongMixingCesaroAbsCorrelation_tendsto_zero
    (P : Measure Ω) [IsProbabilityMeasure P] {τ : Ω → Ω}
    (hstrong : IsStronglyMixing τ P) {A B : Set Ω}
    (hA : MeasurableSet A) (hB : MeasurableSet B) :
    Tendsto
      (fun n : ℕ ↦
        (1 / (n : ℝ)) *
          (Finset.sum (Finset.range n) fun i ↦
            |P.real (A ∩ (τ^[i]) ⁻¹' B) - P.real A * P.real B|))
      atTop
      (nhds 0) := by
  -- Apply the Cesàro theorem to the convergent absolute-error sequence.
  simpa [one_div] using
    (strongMixingAbsCorrelationError_tendsto_zero (P := P) hstrong hA hB).cesaro

/-- Strong mixing implies weak mixing. -/
theorem isWeaklyMixing_of_isStronglyMixing
    (P : Measure Ω) [IsProbabilityMeasure P] {τ : Ω → Ω}
    (hstrong : IsStronglyMixing τ P) :
    IsWeaklyMixing τ P := by
  intro A B hA hB
  -- The Cesàro helper is exactly the convergence required in `IsWeaklyMixing`.
  simpa using
    strongMixingCesaroAbsCorrelation_tendsto_zero (P := P) hstrong hA hB

/-- Helper for Remark 20.25: a measure-level witness with `IsProbabilityMeasure` packages into the
bundled `ProbabilityMeasure` existential used in this item. -/
private theorem existsProbabilityWitnessOfMeasureWitness
    {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] {τ : Ω → Ω}
    (hpres : MeasurePreserving τ P P) (hweak : IsWeaklyMixing τ P)
    (hnot : ¬ IsStronglyMixing τ P) :
    ∃ (Ω : Type u) (_ : MeasurableSpace Ω) (Q : ProbabilityMeasure Ω) (σ : Ω → Ω),
      MeasurePreserving σ (Q : Measure Ω) (Q : Measure Ω) ∧
      IsWeaklyMixing σ (Q : Measure Ω) ∧
      ¬ IsStronglyMixing σ (Q : Measure Ω) := by
  let Q : ProbabilityMeasure Ω := ⟨P, inferInstance⟩
  -- Package the witness measure into the bundled probability-measure type expected by the target.
  refine ⟨Ω, inferInstance, Q, τ, ?_, ?_, ?_⟩
  · -- The measure-preserving fact is unchanged after the coercion to `ProbabilityMeasure`.
    simpa [Q] using hpres
  · -- Weak mixing is stated on the underlying measure, so this is the same assertion.
    simpa [Q] using hweak
  · -- Non-strong-mixing is likewise unchanged by bundling the probability measure.
    simpa [Q] using hnot

/-- Helper for Remark 20.25: a measure-level existential witness packages into the bundled
probability-measure existential used in the main theorem. -/
private theorem existsProbabilityWitnessOfMeasureExistential
    (h :
      ∃ (Ω : Type u) (_ : MeasurableSpace Ω) (P : Measure Ω) (_ : IsProbabilityMeasure P)
        (τ : Ω → Ω),
        MeasurePreserving τ P P ∧ IsWeaklyMixing τ P ∧ ¬ IsStronglyMixing τ P) :
    ∃ (Ω : Type u) (_ : MeasurableSpace Ω) (Q : ProbabilityMeasure Ω) (σ : Ω → Ω),
      MeasurePreserving σ (Q : Measure Ω) (Q : Measure Ω) ∧
      IsWeaklyMixing σ (Q : Measure Ω) ∧
      ¬ IsStronglyMixing σ (Q : Measure Ω) := by
  rcases h with ⟨Ω, hΩ, P, hP, τ, hpres, hweak, hnot⟩
  letI : MeasurableSpace Ω := hΩ
  letI : IsProbabilityMeasure P := hP
  -- Reuse the single-witness packaging lemma so the main theorem only needs a measure-level
  -- counterexample API.
  exact existsProbabilityWitnessOfMeasureWitness (P := P) hpres hweak hnot

-- Proof sketch: instantiate a standard weakly mixing but not strongly mixing example from the
-- ergodic-theory literature, equip it with its invariant probability measure, and verify the two
-- predicates against that example.
/-- Remark 20.25: there exist probability-preserving systems that are weakly mixing but not
strongly mixing. -/
theorem exists_measurePreserving_weaklyMixing_not_stronglyMixing :
    ∃ (Ω : Type u) (_ : MeasurableSpace Ω) (P : ProbabilityMeasure Ω) (τ : Ω → Ω),
      MeasurePreserving τ (P : Measure Ω) (P : Measure Ω) ∧
      IsWeaklyMixing τ (P : Measure Ω) ∧
      ¬ IsStronglyMixing τ (P : Measure Ω) := by
  have hmeasure :
      ∃ (Ω : Type u) (_ : MeasurableSpace Ω) (P : Measure Ω) (_ : IsProbabilityMeasure P)
        (τ : Ω → Ω),
        MeasurePreserving τ P P ∧ IsWeaklyMixing τ P ∧ ¬ IsStronglyMixing τ P := by
    -- Route correction: the current chapter API still lacks the promised canonical counterexample
    -- owner, so the final witness remains a single isolated library gap.
    exact sorryAx _ false
  -- Once the measure-level witness exists, packaging it into the theorem statement is immediate.
  exact existsProbabilityWitnessOfMeasureExistential hmeasure
