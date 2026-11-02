import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap04.section_4_10.ch4_sec4_10_definition_4_10_extra_1

-- Declarations for this item will be appended below by the statement pipeline.

open Matrix
open scoped BigOperators Matrix NonnegativeRankNotation

section PartialOrderSemiring

variable {m n R : Type*} [Semiring R] [PartialOrder R]

/-- A size-`t` nonnegative factorization of `S` is equivalently a decomposition of `S` into `t`
entrywise nonnegative outer products. -/
theorem has_nonnegative_rank_factorization_iff_exists_sum_vecMulVec
    {t : ℕ}
    {S : Matrix m n R} :
    has_nonnegative_rank_factorization S t ↔
      ∃ U : Fin t → m → R,
        ∃ V : Fin t → n → R,
          (∀ h i, 0 ≤ U h i) ∧
          (∀ h j, 0 ≤ V h j) ∧
          S = ∑ h, vecMulVec (U h) (V h) := by
  constructor
  · rintro hfact
    rcases (has_nonnegative_rank_factorization_iff).1 hfact with ⟨F, W, hF, hW, rfl⟩
    refine ⟨F.col, W.row, ?_, ?_, ?_⟩
    · intro h i
      simpa [Matrix.col_apply] using hF i h
    · intro h j
      simpa [Matrix.row_apply] using hW h j
    · ext i j
      have hsum :
          (∑ h, vecMulVec (F.col h) (W.row h)) i j = ∑ h, F i h * W h j := by
        simpa [Matrix.vecMulVec, Matrix.col_apply, Matrix.row_apply] using
          (Matrix.sum_apply i j Finset.univ (fun h ↦ vecMulVec (F.col h) (W.row h)))
      rw [Matrix.mul_apply, hsum]
  · rintro ⟨U, V, hU, hV, hS⟩
    refine (has_nonnegative_rank_factorization_iff).2 ⟨fun i h ↦ U h i, fun h j ↦ V h j, ?_, ?_, ?_⟩
    · intro i h
      exact hU h i
    · intro h j
      exact hV h j
    · rw [hS]
      ext i j
      have hsum :
          (∑ h, vecMulVec (U h) (V h)) i j = ∑ h, U h i * V h j := by
        simpa [Matrix.vecMulVec] using
          (Matrix.sum_apply i j Finset.univ (fun h ↦ vecMulVec (U h) (V h)))
      rw [hsum, Matrix.mul_apply]
section ZeroLEOneClass

variable [Finite n] [ZeroLEOneClass R]

/-- Lemma 4.52. Let `S` be an `m × n` nonnegative matrix. Then the nonnegative rank of `S` is
the smallest number `t` such that `S` is the sum of `t` entrywise nonnegative outer products,
hence of `t` nonnegative rank-one summands. -/
theorem nonnegative_rank_isLeast_nonnegative_rank_one_sum_count
    (S : Matrix.Nonnegative m n R) :
    IsLeast
      {t : ℕ |
        ∃ U : Fin t → m → R,
          ∃ V : Fin t → n → R,
            (∀ h i, 0 ≤ U h i) ∧
            (∀ h j, 0 ≤ V h j) ∧
            S = ∑ h, vecMulVec (U h) (V h)}
      (rank₊ S) := by
  have hleast := nonnegative_rank_isLeast S
  refine ⟨?_, ?_⟩
  · exact (has_nonnegative_rank_factorization_iff_exists_sum_vecMulVec).1 hleast.1
  · intro t ht
    exact nonnegative_rank_le_of_has_nonnegative_rank_factorization
      ((has_nonnegative_rank_factorization_iff_exists_sum_vecMulVec).2 ht)

end ZeroLEOneClass
end PartialOrderSemiring
