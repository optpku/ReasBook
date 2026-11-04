/-
Authors: Ziyu Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@cd8690514e91159fccb6bfdf14ab167259196471:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization lead, confirmed by the submitter on 2026-11-04.
-/

import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap10.section_10_4.ch10_sec10_4_1_theorem_10_11

-- Declarations for this item will be appended below by the statement pipeline.

-- This source-facing theorem reuses the Section 10.4 monotone-iterate bridge built on
-- mathlib's `Monotone.seq_le_seq`.

section Theorem1014

variable {n : ℕ}

/-- Theorem 10.14. Let `P ⊆ ℝ^n`, let `Nplus` denote the positive-semidefinite lift-and-project
operator, and let `L t` denote the `t`th Lasserre relaxation. If `Nplus` is monotone, if
`L 1 ⊆ Nplus P`, and if every higher Lasserre level satisfies
`L (t + 1) ⊆ Nplus (L t)`, then each positive Lasserre level is contained in the corresponding
iterate `(Nplus^[t]) P`, i.e. in the textbook notation `N_+^t`. -/
theorem lasserre_relaxation_subset_positive_semidefinite_iterate
    (P : Set (Fin n → ℝ))
    (Nplus : Set (Fin n → ℝ) → Set (Fin n → ℝ))
    (L : ℕ → Set (Fin n → ℝ))
    (hNplus_mono : Monotone Nplus)
    (hL_one : L 1 ⊆ Nplus P)
    (hL_step : ∀ t : ℕ, 1 ≤ t → L (t + 1) ⊆ Nplus (L t))
    {t : ℕ}
    (ht : 1 ≤ t) :
    L t ⊆ (Nplus^[t]) P :=
  hNplus_mono.seq_le_iterate_of_succ hL_one hL_step ht

end Theorem1014
