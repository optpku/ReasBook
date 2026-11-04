/-
Authors: Ziyu Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@cd8690514e91159fccb6bfdf14ab167259196471:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization lead, confirmed by the submitter on 2026-11-04.
-/

module

public import Mathlib.Analysis.Convex.Basic
import Mathlib.Data.Real.Basic

public section

variable {n : ℕ}

/- Definition 1.26 [Convex set]
For `S : Set (Fin n → ℝ)`, the textbook notion of a convex set is mathlib's
predicate `Convex ℝ S`.
-/

#check (Convex ℝ : Set (Fin n → ℝ) → Prop)
