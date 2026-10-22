/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory

universe u

/- Definition 1.38 (1): A measurable space is the canonical mathlib notion `MeasurableSpace Ω`,
whose measurable sets are the members of the underlying `σ`-algebra. -/
recall MeasurableSpace

variable (Ω : Type u) [MeasurableSpace Ω]

/-- A measurable space is discrete in the textbook sense exactly when the ambient type is countable
and every subset is measurable. This is the textbook wording of the canonical
`DiscreteMeasurableSpace Ω` condition. -/
theorem isCountableDiscreteMeasurableSpace_iff :
    (Countable Ω ∧ DiscreteMeasurableSpace Ω) ↔ Countable Ω ∧ ∀ s : Set Ω, MeasurableSet s := by
  constructor
  · rintro ⟨hΩ, hdiscrete⟩
    exact ⟨hΩ, fun s ↦ @MeasurableSet.of_discrete Ω _ hdiscrete s⟩
  · rintro ⟨hΩ, hs⟩
    exact ⟨hΩ, ⟨hs⟩⟩

/- Definition 1.38 (3): A measure space over a measurable space `Ω` is given by a measure
`μ : Measure Ω` on the canonical measurable space structure. -/
recall Measure

/- Definition 1.38 (4): A probability space is a measure space whose measure is a probability
measure, recorded in mathlib by `IsProbabilityMeasure μ`. Its measurable sets are the events. -/
recall IsProbabilityMeasure

/-- Definition 1.38 (5): `M_f(Ω)` is the textbook notation for the set
`{μ : Measure Ω | IsFiniteMeasure μ}` of finite measures on `Ω`. -/
theorem mem_finiteMeasures_iff {μ : Measure Ω} :
    μ ∈ {ν : Measure Ω | IsFiniteMeasure ν} ↔ IsFiniteMeasure μ :=
  Iff.rfl

/-- Definition 1.38 (6): `M_1(Ω)` is the textbook notation for the set
`{μ : Measure Ω | IsProbabilityMeasure μ}` of probability measures on `Ω`. -/
theorem mem_probabilityMeasures_iff {μ : Measure Ω} :
    μ ∈ {ν : Measure Ω | IsProbabilityMeasure ν} ↔ IsProbabilityMeasure μ :=
  Iff.rfl

/-- Definition 1.38 (7): `M_σ(Ω)` is the textbook notation for the set
`{μ : Measure Ω | SigmaFinite μ}` of σ-finite measures on `Ω`. -/
theorem mem_sigmaFiniteMeasures_iff {μ : Measure Ω} :
    μ ∈ {ν : Measure Ω | SigmaFinite ν} ↔ SigmaFinite μ :=
  Iff.rfl
