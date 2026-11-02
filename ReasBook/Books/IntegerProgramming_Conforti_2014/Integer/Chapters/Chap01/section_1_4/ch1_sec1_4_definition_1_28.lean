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
