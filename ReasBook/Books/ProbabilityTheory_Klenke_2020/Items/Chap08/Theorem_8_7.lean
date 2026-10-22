/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Books.ProbabilityTheory_Klenke_2020.Items.Chap08.Theorem_8_6

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory ProbabilityTheory
open scoped BigOperators ProbabilityTheory

universe u v

variable {Ω : Type u} {I : Type v} [MeasurableSpace Ω] [Countable I]

-- Proof sketch: apply the canonical Bayes identity `cond_eq_inv_mul_cond_mul` to the pair of
-- events `A` and `B k`, then rewrite the denominator with the countable law of total probability
-- from Theorem 8.6.
/-- Theorem 8.7: for a countable measurable partition `(B i)` of full `P`-measure and a
measurable event `A`, Bayes' formula expresses `P[B_k | A]` as the normalized term
`P[A | B_k] * P[B_k]` divided by the total-probability sum over the partition. -/
theorem bayes_formula_countable_partition
    (P : Measure Ω) [IsProbabilityMeasure P] {A : Set Ω} (hA : MeasurableSet A)
    (B : I → Set Ω) (hB : ∀ i, MeasurableSet (B i))
    (hdisj : Pairwise fun i j ↦ Disjoint (B i) (B j)) (hcover : P (⋃ i, B i) = 1) (k : I) :
    P[B k | A] = (P[A | B k] * P (B k)) / (∑' i, P[A | B i] * P (B i)) := by
  -- Route correction: the denominator is not recomputed from scratch; it is imported directly
  -- from Theorem 8.6 and substituted into the two-event Bayes identity.
  have htotal : P A = ∑' i, P[A | B i] * P (B i) :=
    probability_eq_tsum_cond_mul_of_countable_partition P A B hA hB hdisj hcover
  -- Rewrite the numerator with the canonical Bayes identity, then substitute the total-probability
  -- expansion of `P A`.
  rw [cond_eq_inv_mul_cond_mul hA (hB k) P, htotal]
  simp [div_eq_mul_inv, mul_assoc, mul_comm]
