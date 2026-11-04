/-
Authors: Ziyu Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@cd8690514e91159fccb6bfdf14ab167259196471:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization lead, confirmed by the submitter on 2026-11-04.
-/

import Mathlib.Tactic.Recall
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap10.section_10_1.ch10_sec10_1_proposition_10_2

/- Source/core/bridge triage for Exercise 10.2:
* `source-facing`: the exercise recalls the two textbook equivalences for positive semidefinite
  real matrices.
* `core/canonical`: Chapter 10 Proposition 10.2 already owns those source-facing theorems as
  `posSemidef_iff_exists_transpose_mul_self` and
  `symmetric_posSemidef_iff_nonneg_det_principal_submatrix`.
* `bridge/view`: this file is therefore recall-only, exports the canonical owner declarations
  directly, and keeps no parallel local wrapper API or debug-only `#check` surface. -/

/-- Exercise 10.2. Proposition 10.2 is already available in the canonical owner file through the
two standard positive-semidefinite matrix equivalences recalled below. -/
theorem Exercise10_2RecallSurface
    {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.IsSymm) :
    (A.PosSemidef ↔
      ∃ d : ℕ, d ≤ n ∧ ∃ U : Matrix (Fin d) (Fin n) ℝ, A = U.transpose * U) ∧
      (A.PosSemidef ↔ ∀ ⦃d : ℕ⦄ (e : Fin d ↪ Fin n), 0 ≤ (A.submatrix e e).det) := by
  constructor
  · -- The first recalled equivalence is imported directly from the Proposition 10.2 owner file.
    simpa using posSemidef_iff_exists_transpose_mul_self A
  · -- The symmetric principal-minor criterion is likewise available without a local reproving step.
    simpa using symmetric_posSemidef_iff_nonneg_det_principal_submatrix A hA

recall posSemidef_iff_exists_transpose_mul_self
recall symmetric_posSemidef_iff_nonneg_det_principal_submatrix
