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
