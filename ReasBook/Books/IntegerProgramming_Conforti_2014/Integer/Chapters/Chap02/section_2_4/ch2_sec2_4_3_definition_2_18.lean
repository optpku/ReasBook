/-
Authors: Ziyu Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@cd8690514e91159fccb6bfdf14ab167259196471:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization lead, confirmed by the submitter on 2026-11-04.
-/

module

public import Mathlib.Algebra.Notation.Support
public import Mathlib.Data.Real.Basic

public section

-- Declarations for this item will be appended below by the statement pipeline.

variable (n : ℕ)

/- Definition 2.18. For a vector `x : Fin n → ℝ`, its support is the canonical
Lean set `Function.support x` of nonzero coordinates. Membership is given by
`Function.mem_support : i ∈ Function.support x ↔ x i ≠ 0`. -/
#check (Function.support : (Fin n → ℝ) → Set (Fin n))
#check (Function.mem_support :
  ∀ {x : Fin n → ℝ} {i : Fin n}, i ∈ Function.support x ↔ x i ≠ 0)
