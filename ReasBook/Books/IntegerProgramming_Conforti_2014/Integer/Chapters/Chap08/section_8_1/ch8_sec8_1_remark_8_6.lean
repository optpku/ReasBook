/-
Authors: Ziyu Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@d380aaa277a7a97379616d8bd2809e751c1052f4:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization contributors, confirmed by the submitter on 2026-11-04.
-/

import Mathlib.Data.Real.Basic
import Mathlib.Order.Interval.Set.Pi

section Remark86

variable {mIneq mEq : ℕ}

/- Remark 8.6 is a `bridge/view` recall, not a new owner declaration: for the inequality block,
admissible multipliers are exactly the vectors in the nonnegative orthant
`Set.Ici (0 : Fin mIneq → ℝ)`, while the equality multipliers remain unrestricted, i.e. they range
over the whole space `Set.univ : Set (Fin mEq → ℝ)`. -/
#check (Set.Ici (0 : Fin mIneq → ℝ))
#check (Set.univ : Set (Fin mEq → ℝ))

/-- Membership in the nonnegative orthant of `Fin mIneq → ℝ` is coordinatewise nonnegativity. -/
theorem mem_nonnegative_orthant_iff
    (lambdaIneq : Fin mIneq → ℝ) :
    lambdaIneq ∈ Set.Ici (0 : Fin mIneq → ℝ) ↔ ∀ i : Fin mIneq, 0 ≤ lambdaIneq i := by
  rw [Set.mem_Ici, Pi.le_def]
  simp

/-- Equality-constraint multipliers are unrestricted: every vector of `Fin mEq → ℝ` lies in the
whole-space admissible set. -/
theorem mem_unrestricted_multiplier_space
    (lambdaEq : Fin mEq → ℝ) :
    lambdaEq ∈ (Set.univ : Set (Fin mEq → ℝ)) := by
  simp

end Remark86
