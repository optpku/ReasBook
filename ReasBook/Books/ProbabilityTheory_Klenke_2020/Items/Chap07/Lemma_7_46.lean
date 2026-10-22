/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory MeasureTheory.Measure

universe u

variable {Ω : Type u} [MeasurableSpace Ω]

-- Proof sketch: apply the stronger mathlib lemma
-- `MeasureTheory.Measure.exists_positive_of_not_mutuallySingular` to the swapped pair `(ν, μ)`.
-- It yields
-- a measurable set `A` with `μ A > 0` and `ε > 0` such that
-- `ε * μ (E ∩ A) ≤ ν (E ∩ A)` for every measurable `E`; then specialize to measurable subsets
-- `E ⊆ A`, so `E ∩ A = E`.
/-- Lemma 7.46: if finite measures `μ`, `ν` are not mutually singular, then some measurable set
`A` has `μ A > 0`, plus a constant `ε > 0` such that each measurable subset `E ⊆ A` satisfies
`ε * μ E ≤ ν E`. -/
theorem exists_pos_measure_le_on_measurableSubsets_of_not_mutuallySingular
    (μ ν : Measure Ω) [IsFiniteMeasure μ] [IsFiniteMeasure ν] (h : ¬ μ ⟂ₘ ν) :
    ∃ A : Set Ω, MeasurableSet A ∧ 0 < μ A ∧
      ∃ ε : NNReal, 0 < ε ∧
        ∀ E : Set Ω, MeasurableSet E → E ⊆ A → ε * μ E ≤ ν E := by
  obtain ⟨ε, hε, A, hAmeas, hApos, hA⟩ :=
    exists_positive_of_not_mutuallySingular ν μ (by
      simpa [MutuallySingular.comm] using h)
  refine ⟨A, hAmeas, hApos, ε, hε, ?_⟩
  intro E hEmeas hEA
  simpa [Set.inter_eq_left.mpr hEA] using hA E hEmeas
