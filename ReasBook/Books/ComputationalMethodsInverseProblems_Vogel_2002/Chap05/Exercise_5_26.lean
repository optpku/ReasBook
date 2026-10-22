/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

import Mathlib.Algebra.BigOperators.Fin
public import ComputationalMethodsInverseProblems_Vogel_2002.Chap05.Definition_5_11.Toeplitz

public section

open scoped Matrix

namespace Matrix

/-- The lower-bidiagonal Toeplitz matrix used in the Exercise 5.26 counterexample. -/
def toeplitzCounterexampleLower : Matrix (Fin 2) (Fin 2) ℤ :=
  toeplitzByDiag 2 (fun k : ℤ ↦ if k = 1 then 1 else if k = 0 then 1 else 0)

/-- The upper-bidiagonal Toeplitz matrix used in the Exercise 5.26 counterexample. -/
def toeplitzCounterexampleUpper : Matrix (Fin 2) (Fin 2) ℤ :=
  toeplitzByDiag 2 (fun k : ℤ ↦ if k = -1 then 1 else if k = 0 then 1 else 0)

/-- The `(0,0)` entry of the Exercise 5.26 counterexample product is `1`. -/
theorem toeplitzCounterexample_mul_apply_zero_zero :
    (toeplitzCounterexampleLower * toeplitzCounterexampleUpper) 0 0 = 1 := by
  simp [Matrix.mul_apply, toeplitzCounterexampleLower, toeplitzCounterexampleUpper,
    toeplitzByDiag_apply]

/-- The `(1,1)` entry of the Exercise 5.26 counterexample product is `2`. -/
theorem toeplitzCounterexample_mul_apply_one_one :
    (toeplitzCounterexampleLower * toeplitzCounterexampleUpper) 1 1 = 2 := by
  simp [Matrix.mul_apply, toeplitzCounterexampleLower, toeplitzCounterexampleUpper,
    toeplitzByDiag_apply, Fin.sum_univ_two]

/-- Exercise 5.26. A concrete `2 × 2` counterexample showing that the product of
Toeplitz matrices need not be Toeplitz. -/
theorem toeplitzByDiag_mul_not_toeplitzByDiag :
    ¬ ∃ t : ℤ → ℤ,
      toeplitzCounterexampleLower * toeplitzCounterexampleUpper = toeplitzByDiag 2 t := by
  rintro ⟨t, ht⟩
  have h00 :
      (toeplitzCounterexampleLower * toeplitzCounterexampleUpper) 0 0 =
        toeplitzByDiag 2 t 0 0 :=
    congrArg (fun M : Matrix (Fin 2) (Fin 2) ℤ ↦ M 0 0) ht
  have h11 :
      (toeplitzCounterexampleLower * toeplitzCounterexampleUpper) 1 1 =
        toeplitzByDiag 2 t 1 1 :=
    congrArg (fun M : Matrix (Fin 2) (Fin 2) ℤ ↦ M 1 1) ht
  have h00' : (1 : ℤ) = t 0 := by
    simpa [toeplitzCounterexample_mul_apply_zero_zero, toeplitzByDiag_apply] using h00
  have h11' : (2 : ℤ) = t 0 := by
    simpa [toeplitzCounterexample_mul_apply_one_one, toeplitzByDiag_apply] using h11
  exact (by decide : (1 : ℤ) ≠ 2) (h00'.trans h11'.symm)

end Matrix
