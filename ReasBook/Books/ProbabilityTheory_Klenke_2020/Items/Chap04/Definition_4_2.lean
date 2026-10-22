/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open MeasureTheory
open scoped BigOperators

variable {Ω : Type u} [MeasurableSpace Ω]

/- Definition 4.2: The textbook map `I : E⁺ → [0, ∞]` is the canonical integral of a nonnegative
simple function, namely `MeasureTheory.SimpleFunc.lintegral`. -/
recall MeasureTheory.SimpleFunc.lintegral

-- Proof sketch: use additivity of `SimpleFunc.lintegral` over a finite sum of restricted constant
-- simple functions, then evaluate each summand with `SimpleFunc.restrict_const_lintegral`.
/-- Canonical finite-sum form of Definition 4.2: a finite sum of restricted constant simple
functions integrates to the corresponding weighted sum of the measures of its measurable pieces. -/
theorem simpleFunc_lintegral_finset_sum_restrict_const
    (μ : Measure Ω) {ι : Type*} (s : Finset ι) (A : ι → Set Ω) (α : ι → ENNReal)
    (hA : ∀ i, MeasurableSet (A i)) :
    (∑ i ∈ s, (SimpleFunc.const Ω (α i)).restrict (A i)).lintegral μ =
      ∑ i ∈ s, α i * μ (A i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simp
  | insert i s hi hs =>
      simp [hi, hs, hA i, SimpleFunc.add_lintegral, SimpleFunc.restrict_const_lintegral]

/-- `Fin n`-indexed textbook form of Definition 4.2, obtained from
`simpleFunc_lintegral_finset_sum_restrict_const` by taking `s = Finset.univ`. -/
theorem simpleFunc_lintegral_eq_sum_of_indicator
    (μ : Measure Ω) {n : ℕ} (A : Fin n → Set Ω) (α : Fin n → ENNReal)
    (hA : ∀ i, MeasurableSet (A i)) :
    (∑ i, (SimpleFunc.const Ω (α i)).restrict (A i)).lintegral μ = ∑ i, α i * μ (A i) := by
  simpa using simpleFunc_lintegral_finset_sum_restrict_const μ Finset.univ A α hA
