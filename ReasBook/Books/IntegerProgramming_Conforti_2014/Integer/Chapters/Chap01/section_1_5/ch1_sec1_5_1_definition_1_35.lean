/-
Authors: Ziyu Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@cd8690514e91159fccb6bfdf14ab167259196471:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization lead, confirmed by the submitter on 2026-11-04.
-/

module

public import Mathlib.RingTheory.Int.Basic
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

@[expose] public section

open scoped Matrix

namespace Int

/-- The Euclidean-step remainder attached to integers `a` and `b`, given by
`a - Int.fdiv a b * b`. -/
def euclideanStepRemainder (a b : ℤ) : ℤ :=
  a - Int.fdiv a b * b

/-- remote integer-programming sorry cleanup Integer/Chapters/Chap01/section_1_5/ch1_sec1_5_1_definition_1_35.lean.
Definition 1.35 (Euclidean step matrix). The Euclidean-step matrix attached to integers `a` and
`b` is the `2 × 2` integer matrix `!![0, 1; 1, -Int.fdiv a b]`. -/
def euclideanStepMatrix (a b : ℤ) : Matrix (Fin 2) (Fin 2) ℤ :=
  !![0, 1; 1, -Int.fdiv a b]

/-- The Euclidean-step remainder agrees with the canonical floor remainder `Int.fmod`. -/
theorem euclideanStepRemainder_eq_fmod (a b : ℤ) :
    euclideanStepRemainder a b = Int.fmod a b := by
  -- Unfold both remainders and normalize the order of the integer factors.
  rw [euclideanStepRemainder, Int.fmod_def]
  ring

/-- Right multiplication by `euclideanStepMatrix a b` sends the row `![a, b]` to
`![b, euclideanStepRemainder a b]`. -/
theorem vecMul_euclideanStepMatrix (a b : ℤ) (_hb : b ≠ 0) :
    (![a, b] : Fin 2 → ℤ) ᵥ* euclideanStepMatrix a b = ![b, euclideanStepRemainder a b] := by
  -- Evaluate the row product separately at the two coordinates.
  ext i
  fin_cases i
  · simp [Matrix.vecMul, dotProduct, euclideanStepMatrix, Fin.sum_univ_two]
  · simp [Matrix.vecMul, dotProduct, euclideanStepMatrix, euclideanStepRemainder,
      Fin.sum_univ_two]
    ring

/-- The determinant of `euclideanStepMatrix a b` is a unit in `ℤ`. -/
theorem isUnit_det_euclideanStepMatrix (a b : ℤ) :
    IsUnit (euclideanStepMatrix a b).det := by
  -- The explicit determinant is `-1`, which is a unit in `ℤ`.
  simp [euclideanStepMatrix, Matrix.det_fin_two_of]

end Int

end
