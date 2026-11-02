import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap04.section_4_10.ch4_sec4_10_definition_4_10_extra_2

open scoped BigOperators Matrix

section CommRing

variable {R : Type*} [CommRing R]

private def slackLeftFactor
    {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) R)
    (b : Fin m → R) :
    Matrix (Fin m) (Unit ⊕ Fin n) R :=
  fun i s ↦ Sum.elim (fun _ ↦ b i) (fun k ↦ -A i k) s

private def slackRightFactor
    {n v : ℕ}
    (vertices : Fin v → Fin n → R) :
    Matrix (Unit ⊕ Fin n) (Fin v) R :=
  fun s j ↦ Sum.elim (fun _ ↦ (1 : R)) (fun k ↦ vertices j k) s

/-- Homogenizing the affine slack functions factors the slack matrix through the coordinate space
indexed by `Unit ⊕ Fin n`. -/
lemma slack_matrix_eq_homogenized_product
    {m n v : ℕ}
    (A : Matrix (Fin m) (Fin n) R)
    (b : Fin m → R)
    (vertices : Fin v → Fin n → R) :
    slack_matrix A b vertices = slackLeftFactor A b * slackRightFactor vertices := by
  ext i j
  simp [slack_matrix, slackLeftFactor, slackRightFactor, Matrix.mul_apply, Matrix.mulVec,
    dotProduct, sub_eq_add_neg]

/-- Exercise 4.35. Every slack matrix of an `n`-dimensional affine inequality system has rank at
most `n + 1`. Over `ℝ`, this gives the usual rank bound for polytope slack matrices. -/
lemma slack_matrix_rank_le_ambient_add_one
    {m n v : ℕ}
    (A : Matrix (Fin m) (Fin n) R)
    (b : Fin m → R)
    (vertices : Fin v → Fin n → R) :
    (slack_matrix A b vertices).rank ≤ n + 1 := by
  by_cases hR : Subsingleton R
  · letI := hR
    simp
  · letI : Nontrivial R := not_subsingleton_iff_nontrivial.mp hR
    rw [slack_matrix_eq_homogenized_product]
    calc
      (slackLeftFactor A b * slackRightFactor vertices).rank ≤ (slackLeftFactor A b).rank :=
        Matrix.rank_mul_le_left _ _
      _ ≤ Fintype.card (Unit ⊕ Fin n) := Matrix.rank_le_card_width _
      _ = n + 1 := by simp [Nat.add_comm]

end CommRing
