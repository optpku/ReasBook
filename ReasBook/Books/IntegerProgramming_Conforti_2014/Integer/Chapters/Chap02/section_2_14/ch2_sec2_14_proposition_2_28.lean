/-
Authors: Ziyu Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@cd8690514e91159fccb6bfdf14ab167259196471:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization lead, confirmed by the submitter on 2026-11-04.
-/

import Mathlib.Data.Matrix.Mul
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap02.section_2_14.ch2_sec2_14_exercise_2_26
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap09.section_9_5.ch9_sec9_5_zero_one

/-- Helper for remote integer-programming sorry cleanup
Integer/Chapters/Chap02/section_2_14/ch2_sec2_14_proposition_2_28.lean: a signed-unit
linear system can be presented with at least one row without changing its solution set. -/
private lemma signedUnitLinearSystemWithPositiveRowCount
    {p n : ℕ} (D : Matrix (Fin p) (Fin n) ℝ) (d : Fin p → ℝ)
    (hD : has_signed_unit_entries D) :
    ∃ q : ℕ, 1 ≤ q ∧ ∃ E : Matrix (Fin q) (Fin n) ℝ, ∃ e : Fin q → ℝ,
      has_signed_unit_entries E ∧
        {x : Fin n → ℝ | D.mulVec x ≤ d} = {x : Fin n → ℝ | E.mulVec x ≤ e} := by
  by_cases hp : p = 0
  · -- An empty system is equivalent to the single tautological inequality `0 ≤ 0`.
    subst p
    let E : Matrix (Fin 1) (Fin n) ℝ := 0
    let e : Fin 1 → ℝ := 0
    have hq : 1 ≤ 1 := le_rfl
    have hE : has_signed_unit_entries E := by
      intro i j
      right
      left
      simp only [E, Matrix.zero_apply]
    have hsystems :
        {x : Fin n → ℝ | D.mulVec x ≤ d} = {x : Fin n → ℝ | E.mulVec x ≤ e} := by
      ext x
      constructor
      · intro hx i
        simp only [E, e, Matrix.mulVec, dotProduct, Pi.zero_apply, Matrix.zero_apply,
          zero_mul, Finset.sum_const_zero, le_refl]
      · intro hx i
        exact Fin.elim0 i
    exact ⟨1, hq, E, e, hE, hsystems⟩
  · -- A nonempty system already has a positive row count, so retain it unchanged.
    have hq : 1 ≤ p := Nat.one_le_iff_ne_zero.mpr hp
    have hsystems :
        {x : Fin n → ℝ | D.mulVec x ≤ d} = {x : Fin n → ℝ | D.mulVec x ≤ d} := rfl
    exact ⟨p, hq, D, d, hD, hsystems⟩

/-- remote integer-programming sorry cleanup Integer/Chapters/Chap02/section_2_14/ch2_sec2_14_proposition_2_28.lean — Proposition 2.28.
For a real system `A x ≤ b`, the binary feasible set `{x ∈ {0,1}^n | A x ≤ b}` also admits a
description by a system `D x ≤ d` whose matrix entries all lie in `{ -1, 0, 1 }`, with a positive
number of inequalities. -/
theorem zeroOneSystemHasSignedUnitRepresentation
    {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) :
    ∃ p : ℕ, ∃ h_p : 1 ≤ p, ∃ D : Matrix (Fin p) (Fin n) ℝ, ∃ d : Fin p → ℝ,
      (∀ i j, D i j = -1 ∨ D i j = 0 ∨ D i j = 1) ∧
        ({x : Fin n → ℝ | is_zero_one_vector x} ∩ {x : Fin n → ℝ | A.mulVec x ≤ b}) =
          ({x : Fin n → ℝ | is_zero_one_vector x} ∩ {x : Fin n → ℝ | D.mulVec x ≤ d}) := by
  -- First use Exercise 2.26 to obtain the signed-unit description without a row-count condition.
  rcases zero_one_set_has_signed_unit_matrix_representation A b with
    ⟨p, D, d, hD, hrepresentation⟩
  -- Pad only the degenerate zero-row case, preserving the represented linear-system set.
  rcases signedUnitLinearSystemWithPositiveRowCount D d hD with
    ⟨q, hq, E, e, hE, hsystems⟩
  have hrepresentationIntersection :
      ({x : Fin n → ℝ | is_zero_one_vector x} ∩ {x : Fin n → ℝ | A.mulVec x ≤ b}) =
        ({x : Fin n → ℝ | is_zero_one_vector x} ∩ {x : Fin n → ℝ | D.mulVec x ≤ d}) := by
    exact hrepresentation
  have hpaddedIntersection :
      ({x : Fin n → ℝ | is_zero_one_vector x} ∩ {x : Fin n → ℝ | D.mulVec x ≤ d}) =
        ({x : Fin n → ℝ | is_zero_one_vector x} ∩ {x : Fin n → ℝ | E.mulVec x ≤ e}) := by
    exact congrArg (fun s : Set (Fin n → ℝ) ↦ {x | is_zero_one_vector x} ∩ s) hsystems
  have hentries : ∀ i j, E i j = -1 ∨ E i j = 0 ∨ E i j = 1 := hE
  have hfinal :
      ({x : Fin n → ℝ | is_zero_one_vector x} ∩ {x : Fin n → ℝ | A.mulVec x ≤ b}) =
        ({x : Fin n → ℝ | is_zero_one_vector x} ∩ {x : Fin n → ℝ | E.mulVec x ≤ e}) :=
    hrepresentationIntersection.trans hpaddedIntersection
  -- The padded witnesses now satisfy both the positivity and entrywise signed-unit requirements.
  exact ⟨q, hq, E, e, hentries, hfinal⟩

#print axioms zeroOneSystemHasSignedUnitRepresentation
