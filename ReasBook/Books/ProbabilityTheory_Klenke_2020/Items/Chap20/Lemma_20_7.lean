/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open scoped MeasureTheory
open MeasureTheory

universe u

/-- Lemma 20.7 (1): a measurable real-valued map is `I`-measurable, with `I` the invariant
σ-algebra of `τ`, if and only if it is pointwise invariant under `τ`. -/
-- Proof sketch: use the characterization of measurability with respect to
-- `MeasurableSpace.invariants τ` by measurable invariant preimages; for real-valued maps, the
-- singleton fibers detect pointwise equality, and conversely pointwise invariance makes every
-- measurable preimage strictly invariant.
theorem measurable_invariants_real_iff_comp_eq
    {Ω : Type u} [MeasurableSpace Ω] {τ : Ω → Ω} {f : Ω → ℝ}
    (hf : Measurable f) :
    Measurable[MeasurableSpace.invariants τ] f ↔ f ∘ τ = f := by
  constructor
  · exact MeasurableSpace.comp_eq_of_measurable_invariants
  · intro hcomp
    rw [MeasurableSpace.measurable_invariants_dom]
    refine ⟨hf, ?_⟩
    intro s hs
    simp [hcomp]

/-- Lemma 20.7 (2): for a measure-preserving transformation `τ` on a probability space,
ergodicity is equivalent to the statement that every real-valued `I`-measurable function, where
`I` is the invariant σ-algebra of `τ`, is almost surely constant. -/
-- Proof sketch: if `τ` is ergodic, combine part (1) with the standard mathlib theorem that an
-- ergodic invariant real-valued measurable function is almost surely constant. Conversely, test
-- the hypothesis on indicator functions of invariant measurable sets to recover the zero-one
-- characterization of ergodicity.
theorem ergodic_iff_ae_eq_const_of_measurable_invariants_real
    {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] {τ : Ω → Ω}
    (hτ : MeasurePreserving τ P P) :
    Ergodic τ P ↔
      ∀ ⦃f : Ω → ℝ⦄, Measurable[MeasurableSpace.invariants τ] f →
        ∃ c : ℝ, f =ᵐ[P] fun _ ↦ c := by
  constructor
  · intro h_ergodic f hf_inv
    have hf : Measurable f := (MeasurableSpace.measurable_invariants_dom.mp hf_inv).1
    exact h_ergodic.toPreErgodic.ae_eq_const_of_ae_eq_comp hf <|
      MeasurableSpace.comp_eq_of_measurable_invariants hf_inv
  · intro h_const
    refine ⟨hτ, ?_⟩
    refine ⟨?_⟩
    intro s hs hs_inv
    let g : Ω → ℝ := s.indicator (fun _ ↦ (1 : ℝ))
    have hg_meas : Measurable g := Measurable.indicator measurable_const hs
    have hg_comp : g ∘ τ = g := by
      ext x
      have hmem : τ x ∈ s ↔ x ∈ s := by
        change x ∈ τ ⁻¹' s ↔ x ∈ s
        simp [hs_inv]
      by_cases hx : x ∈ s
      · have hτx : τ x ∈ s := by
          exact hmem.mpr hx
        simp [g, hx, hτx]
      · have hτx : τ x ∉ s := by
          intro hτx
          exact hx (hmem.mp hτx)
        simp [g, hx, hτx]
    obtain ⟨c, hc⟩ := h_const ((measurable_invariants_real_iff_comp_eq hg_meas).2 hg_comp)
    rw [Filter.eventuallyConst_set]
    by_cases hc1 : c = 1
    · left
      filter_upwards [hc] with x hx
      by_contra hx'
      have : (0 : ℝ) = 1 := by
        simp [g, hc1, hx'] at hx
      norm_num at this
    · right
      filter_upwards [hc] with x hx hx'
      exact hc1 <| by simpa [g, hx'] using hx.symm
