import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Matrix

namespace Matrix

instance instPointwiseLE {m n R : Type*} [LE R] : LE (Matrix m n R) :=
  inferInstanceAs (LE (m → n → R))

instance instPointwisePreorder {m n R : Type*} [Preorder R] : Preorder (Matrix m n R) :=
  inferInstanceAs (Preorder (m → n → R))

instance instPointwisePartialOrder {m n R : Type*} [PartialOrder R] : PartialOrder (Matrix m n R) :=
  inferInstanceAs (PartialOrder (m → n → R))

/-- Entrywise-nonnegative matrices. This is the source-facing owner for nonnegative rank. -/
abbrev Nonnegative (m n : Type*) (R : Type*) [Zero R] [LE R] := {S : Matrix m n R // 0 ≤ S}

end Matrix

section PreorderSemiring

variable {m n R : Type*} [Semiring R] [Preorder R]

/-- Helper for Definition 4.10-extra-1: a size-`t` nonnegative factorization of `S` is a
decomposition `S = F * W` through some finite middle index set `Fin t`, where both factors are
entrywise nonnegative. -/
def has_nonnegative_rank_factorization
    (S : Matrix m n R)
    (t : ℕ) : Prop :=
  ∃ F : Matrix m (Fin t) R, ∃ W : Matrix (Fin t) n R,
    0 ≤ F ∧
    0 ≤ W ∧
    S = F * W

/-- Helper for Definition 4.10-extra-1: unfolding
`has_nonnegative_rank_factorization S t` gives exactly the required nonnegative factors `F`
and `W`. -/
theorem has_nonnegative_rank_factorization_iff
    {S : Matrix m n R}
    {t : ℕ} :
    has_nonnegative_rank_factorization S t ↔
      ∃ F : Matrix m (Fin t) R,
        ∃ W : Matrix (Fin t) n R,
          0 ≤ F ∧
          0 ≤ W ∧
          S = F * W :=
  Iff.rfl

end PreorderSemiring

section ZeroLEOneClass

variable {m n R : Type*} [Finite n] [Semiring R] [Preorder R] [ZeroLEOneClass R]

/-- Helper for Definition 4.10-extra-1: an entrywise-nonnegative matrix has a size-`Nat.card n`
nonnegative factorization via itself and the identity matrix. -/
theorem has_nonnegative_rank_factorization_self
    (S : Matrix.Nonnegative m n R) :
    has_nonnegative_rank_factorization (S : Matrix m n R) (Nat.card n) := by
  classical
  let _ : Fintype n := Fintype.ofFinite n
  let e : n ≃ Fin (Nat.card n) := Finite.equivFin n
  -- Reindex the given matrix and the identity matrix onto `Fin (Nat.card n)`.
  refine ⟨(S : Matrix m n R).reindex (Equiv.refl _) e,
    (1 : Matrix n n R).reindex e (Equiv.refl _), ?_, ?_, ?_⟩
  · intro i j
    -- The left factor inherits entrywise nonnegativity from `S`.
    simpa [e, Matrix.reindex_apply] using S.2 i (e.symm j)
  · intro i j
    -- The reindexed identity matrix is entrywise nonnegative.
    simpa [e, Matrix.reindex_apply] using Matrix.zero_le_one_elem (e.symm i) j
  · have hrew :
        (S : Matrix m n R).reindex (Equiv.refl _) e * (1 : Matrix n n R).reindex e (Equiv.refl _)
          = S := by
        -- Multiplying by the reindexed identity matrix recovers `S`.
        simpa [e, Matrix.reindex_apply] using
          (Matrix.submatrix_mul_equiv (S : Matrix m n R) (1 : Matrix n n R) id e.symm id)
    simpa using hrew.symm

/-- Helper for Definition 4.10-extra-1: the set of admissible factorization sizes is nonempty
for an entrywise-nonnegative matrix. -/
theorem has_nonnegative_rank_factorization_nonempty
    (S : Matrix.Nonnegative m n R) :
    {t : ℕ | has_nonnegative_rank_factorization (S : Matrix m n R) t}.Nonempty := by
  exact ⟨Nat.card n, has_nonnegative_rank_factorization_self S⟩

/-- Definition 4.10-extra-1: for an entrywise-nonnegative matrix with finite column index type,
the nonnegative rank of `S` is the smallest integer `t` for which `S` admits a size-`t`
nonnegative factorization. -/
noncomputable def nonnegative_rank
    (S : Matrix.Nonnegative m n R)
    : ℕ :=
  sInf {t : ℕ | has_nonnegative_rank_factorization (S : Matrix m n R) t}

namespace NonnegativeRankNotation

scoped notation "rank₊ " S:arg => nonnegative_rank S

end NonnegativeRankNotation

open scoped NonnegativeRankNotation

/-- Helper for Definition 4.10-extra-1: the definition of `nonnegative_rank` is the infimum of
the sizes of nonnegative factorizations. -/
theorem nonnegative_rank_eq_sInf
    {S : Matrix.Nonnegative m n R} :
    rank₊ S =
      sInf {t : ℕ | has_nonnegative_rank_factorization (S : Matrix m n R) t} :=
  rfl

/-- Helper for Definition 4.10-extra-1: the nonnegative rank is the least size of a nonnegative
factorization. -/
theorem nonnegative_rank_isLeast
    (S : Matrix.Nonnegative m n R) :
    IsLeast
      {t : ℕ | has_nonnegative_rank_factorization (S : Matrix m n R) t}
      (rank₊ S) := by
  -- `Nat.sInf_mem` gives existence at the infimum, and `Nat.sInf_le` gives minimality.
  refine ⟨?_, ?_⟩
  · simpa using
      (Nat.sInf_mem (has_nonnegative_rank_factorization_nonempty S) :
        sInf {t : ℕ | has_nonnegative_rank_factorization (S : Matrix m n R) t} ∈
          {t : ℕ | has_nonnegative_rank_factorization (S : Matrix m n R) t})
  · intro t ht
    simpa using
      (Nat.sInf_le ht :
        sInf {u : ℕ | has_nonnegative_rank_factorization (S : Matrix m n R) u} ≤ t)

/-- Helper for Definition 4.10-extra-1: any size-`t` nonnegative factorization of `S` bounds
the nonnegative rank of `S` by `t`. -/
theorem nonnegative_rank_le_of_has_nonnegative_rank_factorization
    {t : ℕ}
    {S : Matrix.Nonnegative m n R}
    (hfact : has_nonnegative_rank_factorization (S : Matrix m n R) t) :
    rank₊ S ≤ t := by
  -- Any explicit admissible size lies above the infimum.
  simpa using
    (Nat.sInf_le hfact :
      sInf {u : ℕ | has_nonnegative_rank_factorization (S : Matrix m n R) u} ≤ t)

end ZeroLEOneClass
