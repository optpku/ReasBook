/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open Filter MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory symmDiff

universe u

variable {Ω : Type u} [MeasurableSpace Ω]
variable {μ : Measure Ω} [IsFiniteMeasure μ]
variable {ℱ : Filtration ℕ ‹MeasurableSpace Ω›}

section

variable {A : ℕ → Set Ω}

/- Exercise 11.2.7 is `bridge/view`: the `core/canonical` owner is the almost-everywhere event
equality from `MeasureTheory.ae_mem_limsup_atTop_iff`, while the textbook symmetric-difference
formulation is the derived measure-level view given by `measure_symmDiff_eq_zero_iff`. The recall
below records that owner theorem directly, and the subsequent declarations keep only the thin
source-facing companions needed in this file. -/
-- Proof sketch: pad the event sequence by the dummy initial term `∅`, apply
-- `MeasureTheory.ae_mem_limsup_atTop_iff` to that padded sequence, and use the fact that changing
-- finitely many initial terms does not change `limsup`. This identifies `limsup A atTop` almost
-- everywhere with the event that the partial sums of the conditional probabilities
-- `μ⟦A (k + 1) | ℱ k⟧` tend to `+∞`. Then rewrite that almost everywhere equivalence as vanishing
-- symmetric-difference measure using
-- `MeasureTheory.measure_symmDiff_eq_zero_iff`.
recall MeasureTheory.ae_mem_limsup_atTop_iff

/-- Exercise 11.2.7, source-facing AE form: the divergence event for
`∑ μ⟦A (n + 1) | ℱ n⟧` is almost surely equivalent to `limsup A atTop`. Only the tail
measurability assumptions `A (n + 1) ∈ ℱ (n + 1)` are needed; the finite initial term `A 0`
plays no role. -/
theorem conditionalBorelCantelliEvent_ae_iff_mem_limsup
    (hA : ∀ n, MeasurableSet[ℱ (n + 1)] (A (n + 1))) :
    ∀ᵐ ω ∂μ, Tendsto
      (fun n ↦ ∑ k ∈ Finset.range n, (μ⟦A (k + 1) | ℱ k⟧) ω)
      atTop atTop ↔ ω ∈ limsup A atTop := by
  let s : ℕ → Set Ω
    | 0 => ∅
    | n + 1 => A (n + 1)
  have hs : ∀ n, MeasurableSet[ℱ n] (s n) := by
    intro n
    cases n with
    | zero =>
        simp [s]
    | succ n =>
        simpa [s] using hA n
  have hs_shift : (fun n ↦ s (n + 1)) = fun n ↦ A (n + 1) := by
    funext n
    simp [s]
  have hlimsup : limsup s atTop = limsup A atTop := by
    rw [← limsup_nat_add s 1, ← limsup_nat_add A 1, hs_shift]
  filter_upwards [ae_mem_limsup_atTop_iff μ hs] with ω hω
  simpa [hlimsup, s] using hω.symm

/-- Exercise 11.2.7: for a filtration `(ℱ n)` and events `A n ∈ ℱ n`, the event that the series
of conditional probabilities `∑ μ⟦A (n + 1) | ℱ n⟧` diverges to `+∞` agrees almost surely with
the tail event `limsup A atTop`; equivalently, their symmetric difference has measure zero. -/
theorem measure_conditionalBorelCantelliEvent_symmDiff_limsup_eq_zero
    (hA : ∀ n, MeasurableSet[ℱ (n + 1)] (A (n + 1))) :
    μ
      ({ω | Tendsto
          (fun n ↦ ∑ k ∈ Finset.range n, (μ⟦A (k + 1) | ℱ k⟧) ω)
          atTop atTop} ∆
        limsup A atTop) = 0 := by
  exact measure_symmDiff_eq_zero_iff.mpr <|
    eventuallyEq_set.2 (conditionalBorelCantelliEvent_ae_iff_mem_limsup hA)

end
