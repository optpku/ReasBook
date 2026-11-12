/-
Authors: Ziyu Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@d380aaa277a7a97379616d8bd2809e751c1052f4:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization contributors, confirmed by the submitter on 2026-11-04.
-/

module

public import Mathlib.Data.Fin.Tuple.Basic
public import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap01.section_1_5.ch1_sec1_5_1_theorem_1_8.CoefficientGcd

@[expose] public section

variable {n : ℕ}

/-- The coefficient-gcd normal form row `(coefficientGcd a, 0, ..., 0)`. -/
def coefficientGcdNormalFormRow (a : Fin n → ℤ) : Fin n → ℤ :=
  fun j ↦ if j.1 = 0 then coefficientGcd a else 0

/-- On `Fin (n + 1)`, the coefficient-gcd normal form row is `Fin.cons (coefficientGcd a) 0`. -/
theorem coefficientGcdNormalFormRow_eq_cons (a : Fin (n + 1) → ℤ) :
    coefficientGcdNormalFormRow a =
      (Fin.cons (coefficientGcd a) (fun _ : Fin n ↦ 0) : Fin (n + 1) → ℤ) := by
  ext j
  cases j using Fin.cases with
  | zero =>
      simp [coefficientGcdNormalFormRow]
  | succ j =>
      simp [coefficientGcdNormalFormRow]

/-- For `n > 0`, the coefficient-gcd normal form row is the first basis row scaled by
`coefficientGcd a`. -/
theorem coefficientGcdNormalFormRow_eq_single
    (hn : 0 < n)
    (a : Fin n → ℤ) :
    coefficientGcdNormalFormRow a = Pi.single ⟨0, hn⟩ (coefficientGcd a) := by
  ext j
  by_cases hj : j = ⟨0, hn⟩
  · subst hj
    simp [coefficientGcdNormalFormRow]
  · have hj0 : j.1 ≠ 0 := by
      intro hj0
      apply hj
      exact Fin.ext hj0
    simp [coefficientGcdNormalFormRow, Pi.single, hj, hj0]

end
