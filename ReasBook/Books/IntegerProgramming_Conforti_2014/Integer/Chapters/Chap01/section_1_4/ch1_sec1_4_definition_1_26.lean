/-
Authors: Ziyu Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@d380aaa277a7a97379616d8bd2809e751c1052f4:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization contributors, confirmed by the submitter on 2026-11-04.
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
