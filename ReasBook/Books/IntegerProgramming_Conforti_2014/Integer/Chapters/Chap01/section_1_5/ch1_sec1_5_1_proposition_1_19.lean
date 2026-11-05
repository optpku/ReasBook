/-
Authors: Ziyu Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@d380aaa277a7a97379616d8bd2809e751c1052f4:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization contributors, confirmed by the submitter on 2026-11-04.
-/

module

public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap01.section_1_5.ch1_sec1_5_1_definition_1_35

@[expose] public section

open scoped Matrix

namespace Int

/-- remote integer-programming sorry cleanup Integer/Chapters/Chap01/section_1_5/ch1_sec1_5_1_proposition_1_19.lean.
Proposition 1.19 (Integrality of the inverse Euclidean step matrix). For integers `a` and `b` with
`b ≠ 0`, the inverse of `euclideanStepMatrix a b` is the integer matrix
`!![Int.fdiv a b, 1; 1, 0]`. -/
theorem euclideanStepMatrix_inv
    (a b : ℤ)
    (hb : b ≠ 0) :
    (euclideanStepMatrix a b)⁻¹ = (!![Int.fdiv a b, 1; 1, 0] : Matrix (Fin 2) (Fin 2) ℤ) := by
  -- Dispose of the excluded zero case, making the stated hypothesis explicit in the proof.
  by_cases hzero : b = 0
  · exact (hb hzero).elim
  · -- Identify the inverse by checking that the displayed matrix is a left inverse.
    apply Matrix.inv_eq_left_inv
    -- The matrix identity reduces to four elementary integer calculations.
    ext i j
    fin_cases i
    · fin_cases j
      · simp [euclideanStepMatrix, Matrix.mul_apply, Fin.sum_univ_two]
      · simp [euclideanStepMatrix, Matrix.mul_apply, Fin.sum_univ_two]
    · fin_cases j
      · simp [euclideanStepMatrix, Matrix.mul_apply, Fin.sum_univ_two]
      · simp [euclideanStepMatrix, Matrix.mul_apply, Fin.sum_univ_two]

end Int

end

#print axioms Int.euclideanStepMatrix_inv
