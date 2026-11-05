/-
Authors: Ziyu Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@d380aaa277a7a97379616d8bd2809e751c1052f4:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization contributors, confirmed by the submitter on 2026-11-04.
-/

module

public import Mathlib.Data.Matrix.Mul
public import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap01.section_1_5.ch1_sec1_5_1_definition_1_35

@[expose] public section

open scoped Matrix

namespace Int

/-- A finite Euclidean-step sequence from `(a, b)` starts at `(a, b)`, has nonzero second
component at each preterminal state, follows the Euclidean update
`(x, y) ↦ (y, euclideanStepRemainder x y)` at every step, and ends with second component `0`. -/
def IsEuclideanStepSequence
    (a b : ℤ)
    (n : ℕ)
    (ab : Fin (n + 1) → ℤ × ℤ) : Prop :=
  ab 0 = (a, b) ∧
    (∀ i : Fin n, (ab i.castSucc).2 ≠ 0) ∧
    (∀ i : Fin n,
      ab i.succ =
        ((ab i.castSucc).2,
          Int.euclideanStepRemainder (ab i.castSucc).1 (ab i.castSucc).2)) ∧
    (ab (Fin.last n)).2 = 0

/-- The ordered product of the Euclidean-step matrices attached to the preterminal states of
`ab`. -/
def euclideanStepProduct
    (n : ℕ)
    (ab : Fin (n + 1) → ℤ × ℤ) : Matrix (Fin 2) (Fin 2) ℤ :=
  (List.ofFn fun i : Fin n =>
    Int.euclideanStepMatrix (ab i.castSucc).1 (ab i.castSucc).2).prod

/-- remote integer-programming sorry cleanup Integer/Chapters/Chap01/section_1_5/ch1_sec1_5_1_theorem_1_6/EuclideanProduct.lean.
Expanding `euclideanStepProduct` gives the ordered `List.ofFn` product of the step matrices
along `ab`. -/
theorem euclideanStepProduct_def
    (n : ℕ)
    (ab : Fin (n + 1) → ℤ × ℤ) :
    Int.euclideanStepProduct n ab =
      (List.ofFn fun i : Fin n =>
        Int.euclideanStepMatrix (ab i.castSucc).1 (ab i.castSucc).2).prod := by
  -- This companion theorem is exactly the defining formula of `euclideanStepProduct`.
  rfl

/-- Each Euclidean-step matrix has determinant `-1`. -/
theorem euclideanStepMatrix_det_eq_neg_one
    (a b : ℤ) :
    (Int.euclideanStepMatrix a b).det = -1 := by
  -- Expand to the explicit `2 × 2` matrix and apply the closed determinant formula.
  rw [Int.euclideanStepMatrix, Matrix.det_fin_two_of]
  -- The remaining goal is a direct integer simplification.
  simp

end Int

end
