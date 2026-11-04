/-
Authors: Ziyu Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@cd8690514e91159fccb6bfdf14ab167259196471:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization lead, confirmed by the submitter on 2026-11-04.
-/

module

public import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap01.section_1_4.ch1_sec1_4_proposition_1_11.Comparison

open scoped BigOperators

public section

variable {n : ℕ}

/-- Proposition 1.11 (Characterization of the convex hull). For `S ⊆ ℝ^n`,
`convexHull ℝ S` is exactly the set of points that admit a finite convex-combination
representation by points of `S`. -/
theorem convexHull_eq_setOf_exists_fin (S : Set (Fin n → ℝ)) :
    convexHull ℝ S =
      {x | ∃ m : ℕ,
          ∃ s : Fin m → (Fin n → ℝ),
            ∃ w : Fin m → ℝ,
              (∀ i, s i ∈ S) ∧
                (∀ i, 0 ≤ w i) ∧
                (∑ i, w i = 1) ∧
                (∑ i, w i • s i = x)} := by
  ext x
  simpa [Set.mem_setOf_eq] using
    (mem_convexHull_iff_exists_fin :
      x ∈ convexHull ℝ S ↔
        ∃ m : ℕ,
          ∃ s : Fin m → Fin n → ℝ,
            ∃ w : Fin m → ℝ,
              (∀ i, s i ∈ S) ∧
                (∀ i, 0 ≤ w i) ∧
                (∑ i, w i = 1) ∧
                (∑ i, w i • s i = x))

end
