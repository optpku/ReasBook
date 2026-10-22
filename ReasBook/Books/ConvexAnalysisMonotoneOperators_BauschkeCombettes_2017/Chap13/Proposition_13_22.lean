/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap13.Proposition_13_10

-- Declarations for this item will be appended below by the statement pipeline.

open scoped InnerProductSpace

universe u

namespace ERealFunction

section Conjugation

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

-- Proof sketch: Proposition 13.10 identifies `f*(0)` with the negative infimum of `f`. The
-- minimum assumptions imply `⨅ x, f x = 0`, so the value at the origin is `0`.
/-- The conjugate of a function that attains its minimum value `0` at the origin also vanishes at
the origin. -/
theorem conjugate_zero_eq_zero_of_minimum_at_zero
    (f : H → EReal) (h_min : ∀ x : H, f 0 ≤ f x) (h_zero : f 0 = 0) :
    f∗ 0 = 0 := by
  have h_iInf : (⨅ x : H, f x) = 0 := by
    apply le_antisymm
    · simpa [h_zero] using (iInf_le f (0 : H))
    · refine le_iInf ?_
      intro x
      simpa [h_zero] using h_min x
  rw [conjugate_zero_eq_neg_iInf, h_iInf]
  simp

-- Proof sketch: first prove the companion lemma that `conjugate f 0 = 0` from the hypothesis
-- that `0` minimizes `f` and `f 0 = 0`. Then combine that identity with the lower bound obtained
-- by testing the defining supremum of `conjugate f u` at `x = 0`.
/-- Proposition 13.22: if `f` attains its minimum value `0` at the origin, then the conjugate is
bounded below by its value at the origin: `f*(0) ≤ f*(u)` for every `u`. -/
theorem conjugate_zero_le_conjugate_of_minimum_at_zero
    (f : H → EReal) (h_min : ∀ x : H, f 0 ≤ f x) (h_zero : f 0 = 0) (u : H) :
    f∗ 0 ≤ f∗ u := by
  have hconj0 : f∗ 0 = 0 := conjugate_zero_eq_zero_of_minimum_at_zero f h_min h_zero
  rw [hconj0]
  rw [conjugate_apply]
  simpa [h_zero] using
    (le_iSup (fun x : H ↦ ((⟪x, u⟫_ℝ : ℝ) : EReal) - f x) (0 : H))

end Conjugation

end ERealFunction
