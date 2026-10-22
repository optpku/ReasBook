/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Books.ProbabilityTheory_Klenke_2020.Items.Chap12.Definition_12_20

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory ProbabilityTheory
open scoped BigOperators

universe u v

variable {Ω : Type u} {ι : Type v} [mΩ : MeasurableSpace Ω]

private theorem condProb_bot_eq_const {μ : Measure Ω} [IsProbabilityMeasure μ]
    {s : Set Ω} (hs : MeasurableSet s) :
    μ⟦s | (⊥ : MeasurableSpace Ω)⟧ = fun _ ↦ μ.real s := by
  let f : Ω → ℝ := s.indicator (fun _ ↦ 1)
  have hbot : μ[f | (⊥ : MeasurableSpace Ω)] = fun _ ↦ ∫ x, f x ∂μ := condExp_bot f
  calc
    μ[f | (⊥ : MeasurableSpace Ω)] = fun _ ↦ ∫ x, f x ∂μ := hbot
    _ = fun _ ↦ μ.real s := by
      ext ω
      simp [f, hs]

/- Source/core/bridge triage:
the main textbook content here is the source-facing Chapter 12 notion
`IsConditionallyIndependent (⊥ : MeasurableSpace Ω) m μ`. Under the stronger owner-side
assumption `[StandardBorelSpace Ω]`, the companion theorem below recovers mathlib's core owner
abstraction `ProbabilityTheory.iCondIndep`. -/

/-- Example 12.22: An independent family of sub-`σ`-algebras is conditionally independent given
the trivial `σ`-algebra. -/
theorem isConditionallyIndependent_bot_of_iIndep {μ : Measure Ω}
    {m : ι → MeasurableSpace Ω} (hm : ∀ i, m i ≤ mΩ) (h_indep : iIndep m μ) :
    letI : IsProbabilityMeasure μ := h_indep.isProbabilityMeasure
    IsConditionallyIndependent (⊥ : MeasurableSpace Ω) m μ := by
  letI : IsProbabilityMeasure μ := h_indep.isProbabilityMeasure
  refine ⟨bot_le, hm, ?_⟩
  intro s f hf
  have h_inter :
      μ⟦⋂ i ∈ s, f i | (⊥ : MeasurableSpace Ω)⟧ = fun _ ↦ μ.real (⋂ i ∈ s, f i) :=
    condProb_bot_eq_const <| s.measurableSet_biInter fun i hi ↦ hm i _ (hf i hi)
  have h_term :
      ∀ i ∈ s, μ⟦f i | (⊥ : MeasurableSpace Ω)⟧ = fun _ ↦ μ.real (f i) := by
    intro i hi
    exact condProb_bot_eq_const (hm i _ (hf i hi))
  have h_indep_real : μ.real (⋂ i ∈ s, f i) = ∏ i ∈ s, μ.real (f i) := by
    simpa [measureReal_def] using congrArg ENNReal.toReal (h_indep.meas_biInter hf)
  have h_prod :
      ∏ i ∈ s, μ⟦f i | (⊥ : MeasurableSpace Ω)⟧ = fun _ ↦ ∏ i ∈ s, μ.real (f i) := by
    ext ω
    rw [Finset.prod_apply]
    exact Finset.prod_congr rfl fun i hi ↦ congrFun (h_term i hi) ω
  exact Filter.EventuallyEq.of_eq <|
    calc
      μ⟦⋂ i ∈ s, f i | (⊥ : MeasurableSpace Ω)⟧ = fun _ ↦ μ.real (⋂ i ∈ s, f i) := h_inter
      _ = fun _ ↦ ∏ i ∈ s, μ.real (f i) := by simp [h_indep_real]
      _ = ∏ i ∈ s, μ⟦f i | (⊥ : MeasurableSpace Ω)⟧ := h_prod.symm

/-- Bridge/view: under the owner-side standard-Borel hypothesis, Example 12.22 also yields
mathlib's conditional-independence owner abstraction. -/
theorem iCondIndep_bot_of_iIndep [StandardBorelSpace Ω]
    {μ : Measure Ω} {m : ι → MeasurableSpace Ω} (hm : ∀ i, m i ≤ mΩ) (h_indep : iIndep m μ) :
    letI : IsProbabilityMeasure μ := h_indep.isProbabilityMeasure
    iCondIndep (⊥ : MeasurableSpace Ω) bot_le m μ := by
  letI : IsProbabilityMeasure μ := h_indep.isProbabilityMeasure
  rw [iCondIndep_iff (⊥ : MeasurableSpace Ω) bot_le m hm μ]
  exact (isConditionallyIndependent_bot_of_iIndep hm h_indep).2.2
