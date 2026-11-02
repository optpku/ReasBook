import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap04.section_4_1.ch4_sec4_1_theorem_4_1.Integral

-- Semantic recall note: the Chapter 4.1 owner API for integral subsets of `ℝ^n` already lives
-- in `ch4_sec4_1_theorem_4_1`, so this file reuses that canonical declaration surface instead of
-- restating a parallel local copy.

/-
Definition 4.1-extra-1. A subset `P` of `ℝ^n` is integral if it is the convex hull of its integer
points; this notion and its source-facing equality characterization are already owned upstream in
Chapter 4.1.
-/
#check is_integral
#check is_integral_iff

/-- Every integral set is convex. -/
theorem convex_of_is_integral {n : ℕ} {P : Set (Fin n → ℝ)} (hP : is_integral P) :
    Convex ℝ P := by
  rw [hP]
  exact convex_convexHull ℝ _
