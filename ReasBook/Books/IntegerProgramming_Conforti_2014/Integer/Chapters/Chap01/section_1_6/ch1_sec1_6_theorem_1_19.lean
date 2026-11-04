/-
Authors: Ziyu Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@cd8690514e91159fccb6bfdf14ab167259196471:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization lead, confirmed by the submitter on 2026-11-04.
-/

module

public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap01.section_1_5.ch1_sec1_5_1_theorem_1_8
public import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap01.section_1_5.ch1_sec1_5_2_lemma_1_3

public section

open scoped Matrix

variable {n : ℕ}

/-- Helper for Theorem 1.19: if `a` is sent to the first basis row by `T` and `V` is a right
inverse of `T`, then the first row of `V` is `a`. -/
private lemma row_eq_of_vecMul_eq_single_of_mul_eq_one
    (hn : 0 < n)
    (a : Fin n → ℤ)
    {T V : Matrix (Fin n) (Fin n) ℤ}
    (hTV : T * V = 1)
    (hform : a ᵥ* T = Pi.single ⟨0, hn⟩ 1) :
    V ⟨0, hn⟩ = a := by
  -- Right-multiplying the normalized row identity by `V` collapses `T * V` to the identity.
  have hvec : (Pi.single ⟨0, hn⟩ 1 : Fin n → ℤ) ᵥ* V = a := by
    calc
      (Pi.single ⟨0, hn⟩ 1 : Fin n → ℤ) ᵥ* V = (a ᵥ* T) ᵥ* V := by rw [hform]
      _ = a ᵥ* (T * V) := by rw [Matrix.vecMul_vecMul]
      _ = a := by simp [hTV]
  -- The basis row action is exactly evaluation at the first row.
  calc
    V ⟨0, hn⟩ = V.row ⟨0, hn⟩ := rfl
    _ = (Pi.single ⟨0, hn⟩ 1 : Fin n → ℤ) ᵥ* V := by
      symm
      exact Matrix.single_one_vecMul ⟨0, hn⟩ V
    _ = a := hvec

/-- Theorem 1.19: if an integer row `a : Fin n → ℤ` is primitive, encoded as
`coefficientGcd a = 1`, and `n > 0`, then `a` occurs as the first row of an integer square matrix
`U` with `IsUnit U.det`, the canonical formalization of `det(U) = ±1`. -/
theorem exists_unimodular_matrix_with_first_row_of_coefficientGcd_one
    (hn : 0 < n)
    (a : Fin n → ℤ)
    (hgcd : coefficientGcd a = 1) :
    ∃ U : Matrix (Fin n) (Fin n) ℤ, IsUnit U.det ∧ U ⟨0, hn⟩ = a := by
  rcases exists_unimodular_normalForm a with ⟨T, hTdet, hTform⟩
  -- Rewrite the normal form as the first basis row to match the matrix row API.
  have hsingle : a ᵥ* T = Pi.single ⟨0, hn⟩ 1 := by
    rw [hTform, coefficientGcdNormalFormRow_eq_single hn a, hgcd]
  rcases (Matrix.isUnit_det_iff_exists_int_inverse T).1 hTdet with ⟨V, hTV, hVT⟩
  -- The integral inverse is again unimodular, and its first row recovers `a`.
  have hVdet : IsUnit V.det := (Matrix.isUnit_det_iff_inverse_isUnit_det hTV hVT).1 hTdet
  refine ⟨V, hVdet, ?_⟩
  exact row_eq_of_vecMul_eq_single_of_mul_eq_one hn a hTV hsingle

/-- Canonical bundled form of Theorem 1.19: the unimodular completion can be chosen as an element
of `GL (Fin n) ℤ`. -/
theorem exists_GL_with_first_row_of_coefficientGcd_one
    (hn : 0 < n)
    (a : Fin n → ℤ)
    (hgcd : coefficientGcd a = 1) :
    ∃ U : GL (Fin n) ℤ, U ⟨0, hn⟩ = a := by
  rcases exists_unimodular_matrix_with_first_row_of_coefficientGcd_one hn a hgcd with
    ⟨U, hU, hrow⟩
  refine ⟨Matrix.GeneralLinearGroup.mk'' U hU, ?_⟩
  simpa using hrow

end
