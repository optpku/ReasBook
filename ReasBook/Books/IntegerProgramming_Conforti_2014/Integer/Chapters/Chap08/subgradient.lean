/-
Authors: Ziyu Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@cd8690514e91159fccb6bfdf14ab167259196471:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization lead, confirmed by the submitter on 2026-11-04.
-/

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Basic

open scoped BigOperators

section Chapter8Subgradient

variable {n : ℕ}

/-- Chapter 8 owner for the affine subgradient inequality on a comparison set.
The codomain may be `ℝ` or `WithBot ℝ`. -/
def IsSubgradientAtOn
    {α : Type*} [LE α] [Add α] [CoeTC ℝ α]
    (g : (Fin n → ℝ) → α)
    (P : Set (Fin n → ℝ))
    (x s : Fin n → ℝ) : Prop :=
  ∀ y ∈ P, g y ≥ g x + ((∑ i, s i * (y i - x i) : ℝ) : α)

end Chapter8Subgradient
