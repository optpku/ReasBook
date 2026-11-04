/-
Authors: Ziyu Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@cd8690514e91159fccb6bfdf14ab167259196471:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization lead, confirmed by the submitter on 2026-11-04.
-/

module

public import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap01.section_1_4.ch1_sec1_4_proposition_1_11.Comparison

public section

variable {n : ℕ}

/-
Definition 1.28 [Convex combination]. For `S : Set (Fin n → ℝ)` and `x : Fin n → ℝ`,
the source statement “`x` is a convex combination of points in `S`” is exactly the
canonical predicate `x ∈ convexHull ℝ S`. Proposition 1.11 provides the standard finite
coefficient characterization of this predicate.
-/

#check
  ((fun (S : Set (Fin n → ℝ)) (x : Fin n → ℝ) ↦ x ∈ convexHull ℝ S) :
    Set (Fin n → ℝ) → (Fin n → ℝ) → Prop)
#check mem_convexHull_iff_exists_fin

end
