/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Books.ProbabilityTheory_Klenke_2020.Items.Chap12.Definition_12_6

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory

universe u v

variable {Ω : Type u}
variable {E : Type v} [MeasurableSpace E]

/-
Remark 12.7 is a `bridge/view` statement: the owner abstractions are the chapter's
`nSymmetricSequenceSigmaAlgebra n` on sequence space and its pullback
`nExchangeableSigmaAlgebra X n`. The theorem below simply transports the owner-level measurable-set
criterion across `MeasurableSpace.comap`.
-/
-- Proof sketch: unfold `nExchangeableSigmaAlgebra` as a pullback along `X`, then identify the
-- representing measurable sets via `MeasurableSpace.measurableSet_comap`, using the owner-level
-- characterization of measurable sets in `nSymmetricSequenceSigmaAlgebra`.
/-- Remark 12.7: an event belongs to the `n`-exchangeable `σ`-algebra of the sequence-valued map
`X` exactly when it admits a measurable representation `A = X ⁻¹' B` by an `n`-symmetric
measurable set of sequences. -/
theorem measurableSet_nExchangeableSigmaAlgebra_iff
    (n : ℕ) (X : Ω → ℕ → E) (A : Set Ω) :
    MeasurableSet[nExchangeableSigmaAlgebra X n] A ↔
      ∃ B : Set (ℕ → E), MeasurableSet B ∧ IsNSymmetricSequenceSet n B ∧ A = X ⁻¹' B := by
  rw [nExchangeableSigmaAlgebra, MeasurableSpace.measurableSet_comap]
  simp_rw [measurableSet_nSymmetricSequenceSigmaAlgebra_iff]
  simp [and_assoc, eq_comm]
