/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory Filter

universe u

variable {Ω : Type u} [MeasurableSpace Ω]

/-- Definition 20.24: on a probability space, the system is strongly mixing when the correlations
`P (A ∩ (τ^[n])⁻¹(B))` converge to `P A * P B` for all measurable events `A` and `B`. Together
with `MeasurePreserving τ P P`, this is exactly the textbook notion of a mixing dynamical system.
-/
def IsStronglyMixing (τ : Ω → Ω) (P : Measure Ω) [IsProbabilityMeasure P] : Prop :=
  ∀ A B : Set Ω, MeasurableSet A → MeasurableSet B →
    Tendsto
      (fun n : ℕ ↦ P.real (A ∩ (τ^[n]) ⁻¹' B))
      atTop
      (nhds (P.real A * P.real B))

-- Proof sketch: convert the `toReal`-valued convergence in `IsStronglyMixing` back to the
-- corresponding `ℝ≥0∞`-valued convergence using `ENNReal.tendsto_toReal_iff`; finiteness of all
-- terms comes from the probability-measure hypothesis.
/-- In a strongly mixing system, the measures of `A ∩ (τ^[n]) ⁻¹' B` converge to `P A * P B` for
measurable events `A` and `B`. -/
theorem isStronglyMixing_tendsto_measure_inter_preimage_iterate
    {τ : Ω → Ω} {P : Measure Ω} [IsProbabilityMeasure P] (hstrong : IsStronglyMixing τ P)
    {A B : Set Ω} (hA : MeasurableSet A) (hB : MeasurableSet B) :
    Tendsto (fun n : ℕ ↦ P (A ∩ (τ^[n]) ⁻¹' B)) atTop (nhds (P A * P B)) := by
  rw [← ENNReal.tendsto_toReal_iff
    (fun n ↦ measure_ne_top P (A ∩ (τ^[n]) ⁻¹' B))
    (ENNReal.mul_ne_top (measure_ne_top P A) (measure_ne_top P B))]
  simpa [IsStronglyMixing, ENNReal.toReal_mul] using hstrong A B hA hB
