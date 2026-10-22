/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Books.ProbabilityTheory_Klenke_2020.Items.Chap17.Exercise_17_6_6
import Books.ProbabilityTheory_Klenke_2020.Items.Chap17.Theorem_17_11
import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory ProbabilityTheory ProbabilityTheory.Kernel
open scoped ENNReal ProbabilityTheory

noncomputable section

universe u v

/- Remark 19.9 (1): the first claim is the canonical reversibility theorem
`IsReversible.invariant`, saying that a reversible Markov kernel leaves the reversing measure
invariant. -/
recall IsReversible.invariant

namespace ProbabilityTheory

variable {E : Type u} [MeasurableSpace E] [DiscreteMeasurableSpace E]
variable {Ω : Type v} [MeasurableSpace Ω]

/- Layering for Remark 19.9:
- `IsReversible.invariant` and
  `invariantMeasures_unique_up_to_scale_of_irreducible_recurrent` are the core/canonical owner
  declarations.
- `reversibleMeasure_unique_up_to_scale_of_irreducible_recurrent` is the source-facing bridge/view
  that specializes uniqueness of invariant measures to a reversible comparison measure. -/

-- Proof sketch: the realization hypothesis induces the owner semigroup
-- `IsMarkovSemigroup (fun n ↦ discreteMatrixKernel p ^ n)`, whose time-one kernel is
-- `discreteMatrixKernel p`. Then `Kernel.IsReversible.invariant` turns reversibility of `π` into
-- invariance, and `invariantMeasures_unique_up_to_scale_of_irreducible_recurrent` compares this
-- nonzero invariant measure with any other nonzero invariant measure `ν`.
/-- For an irreducible recurrent discrete-time chain, every nonzero invariant measure is
proportional to any nonzero reversible measure `π`; equivalently, `π` is unique up to
multiplication by a positive constant. -/
theorem reversibleMeasure_unique_up_to_scale_of_irreducible_recurrent
    {p : E → E → ℝ≥0∞}
    {P : E → ProbabilityMeasure Ω} {X : ℕ → Ω → E}
    [IsMarkovProcessRealization (fun n ↦ discreteMatrixKernel p ^ n) P X]
    (hirr : IsIrreducibleMarkovChain P X) (hrec : IsRecurrentMarkovChain P X) {π ν : Measure E}
    (hπ_rev : IsReversible (discreteMatrixKernel p) π)
    (hν_inv : Invariant (discreteMatrixKernel p) ν)
    (hπ_ne : π ≠ 0) (hν_ne : ν ≠ 0) :
    ∃ c : ℝ≥0∞, 0 < c ∧ ν = c • π :=
  by
    have hrealization :
        IsMarkovProcessRealization (fun n ↦ discreteMatrixKernel p ^ n) P X := inferInstance
    have hsemigroup : IsMarkovSemigroup (fun n : ℕ ↦ discreteMatrixKernel p ^ n) := by
      exact @isMarkovSemigroup_of_markovProcessRealization ℕ inferInstance E ‹_› inferInstance Ω
        ‹_› (fun n : ℕ ↦ discreteMatrixKernel p ^ n) P X hrealization
    let _ : IsMarkovKernel (discreteMatrixKernel p) :=
      by simpa using hsemigroup.isMarkovKernel 1
    exact invariantMeasures_unique_up_to_scale_of_irreducible_recurrent hirr hrec
      hπ_rev.invariant hν_inv hπ_ne hν_ne

end ProbabilityTheory
