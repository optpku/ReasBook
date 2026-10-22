/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import Mathlib
import FirstOrderMethodsOptimization_Beck_2017.Chap01.Definition_1_29
import FirstOrderMethodsOptimization_Beck_2017.Chap07.Definition_7_8
import FirstOrderMethodsOptimization_Beck_2017.Chap07.Definition_7_10
import FirstOrderMethodsOptimization_Beck_2017.Chap07.Definition_7_15
import FirstOrderMethodsOptimization_Beck_2017.Chap07.Theorem_7_1
import FirstOrderMethodsOptimization_Beck_2017.Chap07.Theorem_7_2

-- Declarations for this item will be appended below by the statement pipeline.

open Matrix
open scoped Matrix

noncomputable section

section

variable {m n : ℕ}

/-- The rectangular diagonal matrix whose diagonal entries are the ordered singular values of a
real `m × n` matrix. -/
def singular_value_diagonal_matrix (X : Matrix (Fin m) (Fin n) ℝ) :
    Matrix (Fin m) (Fin n) ℝ :=
  fun i j ↦
    if h : i.1 = j.1 then
      singular_value_function X ⟨i.1, Nat.lt_min.mpr ⟨i.2, h ▸ j.2⟩⟩
    else 0

-- Proof sketch: unfold `singular_value_diagonal_matrix`; its `(i,j)` entry is the corresponding
-- singular value when the row and column indices agree, and `0` otherwise.
/-- The entries of `singular_value_diagonal_matrix X` are the ordered singular values of `X` on the
common diagonal and `0` away from that diagonal. -/
theorem singular_value_diagonal_matrix_apply (X : Matrix (Fin m) (Fin n) ℝ) (i : Fin m)
    (j : Fin n) :
    singular_value_diagonal_matrix X i j =
      if h : i.1 = j.1 then
        singular_value_function X ⟨i.1, Nat.lt_min.mpr ⟨i.2, h ▸ j.2⟩⟩
      else 0 := by
  -- This is the defining evaluation rule for the rectangular diagonal singular-value matrix.
  rfl

/-- Two real `m × n` matrices admit a simultaneous nonincreasing singular value decomposition if
they can be written with the same left and right orthogonal factors and with their singular-value
lists on the common rectangular diagonal. -/
def has_simultaneous_nonincreasing_singular_value_decomposition
    (X Y : Matrix (Fin m) (Fin n) ℝ) : Prop :=
  ∃ U : Matrix.orthogonalGroup (Fin m) ℝ,
    ∃ V : Matrix.orthogonalGroup (Fin n) ℝ,
      X = (U : Matrix (Fin m) (Fin m) ℝ) * singular_value_diagonal_matrix X *
            ((V : Matrix (Fin n) (Fin n) ℝ)ᵀ) ∧
        Y = (U : Matrix (Fin m) (Fin m) ℝ) * singular_value_diagonal_matrix Y *
            ((V : Matrix (Fin n) (Fin n) ℝ)ᵀ)

/-- Helper for Theorem 7.4: the block symmetric dilation of a rectangular matrix, indexed on
`Fin m ⊕ Fin n`, is the usual off-diagonal block matrix `[[0, X], [Xᵀ, 0]]`. -/
def block_symmetric_dilation (X : Matrix (Fin m) (Fin n) ℝ) :
    Matrix (Fin m ⊕ Fin n) (Fin m ⊕ Fin n) ℝ :=
  Matrix.fromBlocks 0 X Xᵀ 0

/-- Helper for Theorem 7.4: the symmetric dilation reindexed onto `Fin (m + n)` so that the
earlier Fan inequalities on `Fin n` can be applied directly. -/
def symmetric_dilation (X : Matrix (Fin m) (Fin n) ℝ) :
    Matrix (Fin (m + n)) (Fin (m + n)) ℝ :=
  Matrix.reindex finSumFinEquiv finSumFinEquiv (block_symmetric_dilation X)

/-- Helper for Theorem 7.4: reindexing a square matrix along an equivalence preserves its trace. -/
lemma trace_reindex
    {α β R : Type*} [Fintype α] [Fintype β] [AddCommMonoid R]
    (e : α ≃ β) (M : Matrix α α R) :
    Matrix.trace (Matrix.reindex e e M) = Matrix.trace M := by
  -- Expand the trace and transport the finite sum across the index equivalence.
  unfold Matrix.trace
  classical
  rw [Fintype.sum_equiv e]
  simp [Matrix.reindex_apply]

/-- Helper for Theorem 7.4: the block symmetric dilation is symmetric before reindexing to
`Fin (m + n)`. -/
lemma block_symmetric_dilation_isSymm (X : Matrix (Fin m) (Fin n) ℝ) :
    (block_symmetric_dilation X).IsSymm := by
  -- The off-diagonal blocks are transposes of each other and the diagonal blocks are zero.
  dsimp [block_symmetric_dilation]
  exact Matrix.IsSymm.fromBlocks (by simp) (by simp) (by simp)

/-- Helper for Theorem 7.4: the `Fin (m + n)` symmetric dilation is symmetric. -/
lemma symmetric_dilation_isSymm (X : Matrix (Fin m) (Fin n) ℝ) :
    (symmetric_dilation X).IsSymm := by
  -- Symmetry is preserved by reindexing both rows and columns along the same equivalence.
  exact (block_symmetric_dilation_isSymm X).reindex finSumFinEquiv

/-- Helper for Theorem 7.4: the symmetric dilation defines an element of the symmetric-matrix
space `𝕊^(m+n)`. -/
lemma symmetric_dilation_mem_symmetricMatrices (X : Matrix (Fin m) (Fin n) ℝ) :
    symmetric_dilation X ∈ symmetricMatrices (m + n) := by
  -- Membership in `symmetricMatrices` is exactly the transpose-fixed condition.
  rw [mem_symmetricMatrices_iff]
  exact symmetric_dilation_isSymm X

/-- Helper for Theorem 7.4: the symmetric dilation viewed as an element of `𝕊^(m+n)`. -/
def symmetric_dilation_symmetricMatrix (X : Matrix (Fin m) (Fin n) ℝ) :
    symmetricMatrices (m + n) :=
  ⟨symmetric_dilation X, symmetric_dilation_mem_symmetricMatrices X⟩

/-- Helper for Theorem 7.4: on the block index set, multiplying two symmetric dilations isolates
`X * Yᵀ` and `Xᵀ * Y` on the diagonal blocks. -/
lemma block_symmetric_dilation_mul (X Y : Matrix (Fin m) (Fin n) ℝ) :
    block_symmetric_dilation X * block_symmetric_dilation Y =
      Matrix.fromBlocks (X * Yᵀ) 0 0 (Xᵀ * Y) := by
  -- The block multiplication is explicit because the diagonal blocks are zero.
  dsimp [block_symmetric_dilation]
  simp [Matrix.fromBlocks_multiply]

/-- Helper for Theorem 7.4: the trace pairing of two symmetric dilations is twice the rectangular
trace pairing `Tr(XᵀY)`. -/
lemma symmetric_dilation_trace_mul_eq_two_trace_transpose_mul
    (X Y : Matrix (Fin m) (Fin n) ℝ) :
    Matrix.trace (symmetric_dilation X * symmetric_dilation Y) =
      2 * Matrix.trace (Xᵀ * Y) := by
  have htraceXY : Matrix.trace (X * Yᵀ) = Matrix.trace (Xᵀ * Y) :=
    (Matrix.trace_transpose_mul X Yᵀ).symm
  calc
    Matrix.trace (symmetric_dilation X * symmetric_dilation Y)
      = Matrix.trace
          (Matrix.reindex finSumFinEquiv finSumFinEquiv
            (block_symmetric_dilation X * block_symmetric_dilation Y)) := by
          -- Reindexing commutes with multiplication on square matrices.
          simp [symmetric_dilation]
    _ = Matrix.trace (block_symmetric_dilation X * block_symmetric_dilation Y) := by
          -- The trace is unchanged by the shared reindexing.
          exact trace_reindex finSumFinEquiv _
    _ = Matrix.trace
          (Matrix.fromBlocks (X * Yᵀ) 0 0 (Xᵀ * Y) :
            Matrix (Fin m ⊕ Fin n) (Fin m ⊕ Fin n) ℝ) := by
          -- Compute the block product before evaluating the trace.
          rw [block_symmetric_dilation_mul]
    _ = Matrix.trace (X * Yᵀ) + Matrix.trace (Xᵀ * Y) := by
          -- The trace of a block-diagonal matrix is the sum of the traces of its diagonal blocks.
          simp [Matrix.trace, Matrix.fromBlocks]
    _ = Matrix.trace (Xᵀ * Y) + Matrix.trace (Xᵀ * Y) := by
          rw [htraceXY]
    _ = 2 * Matrix.trace (Xᵀ * Y) := by
          ring

/-- Helper for Theorem 7.4: multiplying the transpose of the rectangular singular-value diagonal
matrix of `X` with that of `Y` yields the diagonal matrix of pointwise singular-value products,
followed by a zero tail when `n > min m n`. -/
lemma singular_value_diagonal_matrix_transpose_mul
    (X Y : Matrix (Fin m) (Fin n) ℝ) :
    (singular_value_diagonal_matrix X)ᵀ * singular_value_diagonal_matrix Y =
      Matrix.diagonal
        (fun j : Fin n ↦
          if h : j.1 < min m n then
            singular_value_function X ⟨j.1, h⟩ * singular_value_function Y ⟨j.1, h⟩
          else 0) := by
  -- Compute the product entrywise and isolate the unique common diagonal contribution.
  ext i j
  by_cases hij : i = j
  · subst hij
    rw [Matrix.mul_apply]
    by_cases hi : i.1 < m
    · let ii : Fin m := ⟨i.1, hi⟩
      rw [Fintype.sum_eq_single ii]
      · -- On the diagonal, the unique surviving term is the matching singular-value product.
        have hmin : i.1 < min m n := Nat.lt_min.mpr ⟨hi, i.2⟩
        rw [Matrix.diagonal_apply, if_pos rfl]
        simp [singular_value_diagonal_matrix, hmin, ii]
      · intro k hk
        -- Every nonmatching row index forces one of the rectangular diagonal entries to vanish.
        have hk' : k.1 ≠ i.1 := by
          intro hki
          apply hk
          ext
          exact hki
        simp [singular_value_diagonal_matrix, hk']
    · have hk' : ∀ k : Fin m, k.1 ≠ i.1 := by
        intro k hki
        exact hi (hki ▸ k.2)
      have hsum :
          (∑ k : Fin m,
              ((singular_value_diagonal_matrix X)ᵀ i k) *
                singular_value_diagonal_matrix Y k i) = 0 := by
        -- If the ambient column index lies past `m`, there is no matching row index at all.
        apply Fintype.sum_eq_zero
        intro k
        simp [singular_value_diagonal_matrix, hk' k]
      have hmin : ¬ i.1 < min m n := by
        intro h
        exact hi (Nat.lt_of_lt_of_le h (Nat.min_le_left _ _))
      rw [Matrix.diagonal_apply, if_pos rfl]
      simpa [hmin] using hsum
  · rw [Matrix.diagonal_apply]
    have hmul :
        (((singular_value_diagonal_matrix X)ᵀ * singular_value_diagonal_matrix Y) i j) = 0 := by
      rw [Matrix.mul_apply]
      by_cases hi : i.1 < m
      · let ii : Fin m := ⟨i.1, hi⟩
        rw [Fintype.sum_eq_single ii]
        · -- Off the diagonal, the candidate surviving term still vanishes because `i ≠ j`.
          have hij' : ii.1 ≠ j.1 := by
            intro h
            apply hij
            ext
            simpa [ii] using h
          simp [singular_value_diagonal_matrix, hij']
        · intro k hk
          have hk' : k.1 ≠ i.1 := by
            intro hki
            apply hk
            ext
            exact hki
          simp [singular_value_diagonal_matrix, hk']
      · have hk' : ∀ k : Fin m, k.1 ≠ i.1 := by
          intro k hki
          exact hi (hki ▸ k.2)
        have hsum :
            (∑ k : Fin m,
                ((singular_value_diagonal_matrix X)ᵀ i k) *
                  singular_value_diagonal_matrix Y k j) = 0 := by
          -- Again, if the would-be matching row is unavailable, every term is forced to zero.
          apply Fintype.sum_eq_zero
          intro k
          simp [singular_value_diagonal_matrix, hk' k]
        simpa using hsum
    rw [if_neg hij]
    exact hmul

/-- Helper for Theorem 7.4: the trace pairing of two rectangular singular-value diagonal matrices
is exactly the Euclidean dot product of their singular-value vectors. -/
lemma trace_singular_value_diagonal_matrix_transpose_mul
    (X Y : Matrix (Fin m) (Fin n) ℝ) :
    Matrix.trace ((singular_value_diagonal_matrix X)ᵀ * singular_value_diagonal_matrix Y) =
      dotProduct (singular_value_function X) (singular_value_function Y) := by
  -- Rewrite the product as a diagonal matrix, then split off the zero tail beyond `min m n`.
  let f : ℕ → ℝ := fun j ↦
    if h : j < min m n then
      singular_value_function X ⟨j, h⟩ * singular_value_function Y ⟨j, h⟩
    else 0
  rw [singular_value_diagonal_matrix_transpose_mul, Matrix.trace_diagonal, dotProduct]
  have hmin : min m n ≤ n := Nat.min_le_right _ _
  have hhead :
      (∑ j ∈ Finset.range (min m n), f j) =
        ∑ i : Fin (min m n), singular_value_function X i * singular_value_function Y i := by
    -- On the genuine diagonal range, every `if` branch is the singular-value product.
    have hfin :
        (∑ i : Fin (min m n), f i) =
          ∑ i : Fin (min m n), singular_value_function X i * singular_value_function Y i := by
      apply Finset.sum_congr rfl
      intro i hi
      show f i = singular_value_function X i * singular_value_function Y i
      dsimp [f]
      rw [if_pos i.2]
    calc
      (∑ j ∈ Finset.range (min m n), f j) = ∑ i : Fin (min m n), f i := by
        exact (Fin.sum_univ_eq_sum_range f (min m n)).symm
      _ = ∑ i : Fin (min m n), singular_value_function X i * singular_value_function Y i := hfin
  have htail :
      (∑ j ∈ Finset.Ico (min m n) n, f j) = 0 := by
    -- Past `min m n`, the diagonal tail is identically zero.
    apply Finset.sum_eq_zero
    intro j hj
    have hj' : ¬ j < min m n := by
      exact not_lt_of_ge (Finset.mem_Ico.mp hj).1
    show f j = 0
    simpa [f] using (dif_neg hj' : (if h : j < min m n then
      singular_value_function X ⟨j, h⟩ * singular_value_function Y ⟨j, h⟩ else 0) = 0)
  calc
    (∑ i : Fin n, f i)
      = ∑ j ∈ Finset.range n, f j := by
          exact Fin.sum_univ_eq_sum_range f n
    _ = (∑ j ∈ Finset.range (min m n), f j) +
          (∑ j ∈ Finset.Ico (min m n) n, f j) := by
              symm
              exact Finset.sum_range_add_sum_Ico _ hmin
    _ = ∑ i : Fin (min m n), singular_value_function X i * singular_value_function Y i := by
          rw [hhead, htail, add_zero]

/-- Helper for Theorem 7.4: a simultaneous nonincreasing singular value decomposition forces the
trace pairing to equal the dot product of the singular-value vectors. -/
lemma trace_eq_dotProduct_of_simultaneous_nonincreasing_singular_value_decomposition
    (X Y : Matrix (Fin m) (Fin n) ℝ)
    (hXY : has_simultaneous_nonincreasing_singular_value_decomposition X Y) :
    Matrix.trace (Xᵀ * Y) =
      dotProduct (singular_value_function X) (singular_value_function Y) := by
  rcases hXY with ⟨U, V, hX, hY⟩
  let SX : Matrix (Fin m) (Fin n) ℝ := singular_value_diagonal_matrix X
  let SY : Matrix (Fin m) (Fin n) ℝ := singular_value_diagonal_matrix Y
  have hU :
      ((U : Matrix (Fin m) (Fin m) ℝ)ᵀ) * (U : Matrix (Fin m) (Fin m) ℝ) = 1 :=
    (Matrix.mem_orthogonalGroup_iff' (A := (U : Matrix (Fin m) (Fin m) ℝ)) (R := ℝ)).1 U.2
  have hV :
      ((V : Matrix (Fin n) (Fin n) ℝ)ᵀ) * (V : Matrix (Fin n) (Fin n) ℝ) = 1 :=
    (Matrix.mem_orthogonalGroup_iff' (A := (V : Matrix (Fin n) (Fin n) ℝ)) (R := ℝ)).1 V.2
  -- Substitute the common orthogonal factors and cycle the trace to cancel the outer conjugation.
  calc
    Matrix.trace (Xᵀ * Y)
      = Matrix.trace
          ((((V : Matrix (Fin n) (Fin n) ℝ) * SXᵀ * ((U : Matrix (Fin m) (Fin m) ℝ)ᵀ)) *
              ((U : Matrix (Fin m) (Fin m) ℝ) * SY)) *
            ((V : Matrix (Fin n) (Fin n) ℝ)ᵀ)) := by
          rw [hX, hY]
          simp [SX, SY, Matrix.transpose_mul]
          rw [← Matrix.mul_assoc
            (V : Matrix (Fin n) (Fin n) ℝ)
            ((singular_value_diagonal_matrix X)ᵀ)
            ((U : Matrix (Fin m) (Fin m) ℝ)ᵀ)]
          rw [← Matrix.mul_assoc
            (((V : Matrix (Fin n) (Fin n) ℝ) * (singular_value_diagonal_matrix X)ᵀ *
                ((U : Matrix (Fin m) (Fin m) ℝ)ᵀ)))
            (((U : Matrix (Fin m) (Fin m) ℝ) * singular_value_diagonal_matrix Y))
            ((V : Matrix (Fin n) (Fin n) ℝ)ᵀ)]
    _ = Matrix.trace
          (((V : Matrix (Fin n) (Fin n) ℝ)ᵀ) *
            (((V : Matrix (Fin n) (Fin n) ℝ) * SXᵀ * ((U : Matrix (Fin m) (Fin m) ℝ)ᵀ)) *
              ((U : Matrix (Fin m) (Fin m) ℝ) * SY))) := by
          simpa [Matrix.mul_assoc] using
            (Matrix.trace_mul_cycle
              (((V : Matrix (Fin n) (Fin n) ℝ) * SXᵀ * ((U : Matrix (Fin m) (Fin m) ℝ)ᵀ)))
              ((U : Matrix (Fin m) (Fin m) ℝ) * SY)
              (((V : Matrix (Fin n) (Fin n) ℝ)ᵀ)))
    _ = Matrix.trace
          (SXᵀ * ((U : Matrix (Fin m) (Fin m) ℝ)ᵀ) *
            ((U : Matrix (Fin m) (Fin m) ℝ) * SY)) := by
          rw [show
              ((V : Matrix (Fin n) (Fin n) ℝ)ᵀ) *
                  (((V : Matrix (Fin n) (Fin n) ℝ) * SXᵀ *
                      ((U : Matrix (Fin m) (Fin m) ℝ)ᵀ)) *
                    ((U : Matrix (Fin m) (Fin m) ℝ) * SY))
                =
              (((((V : Matrix (Fin n) (Fin n) ℝ)ᵀ) *
                    (V : Matrix (Fin n) (Fin n) ℝ)) * SXᵀ) *
                  ((U : Matrix (Fin m) (Fin m) ℝ)ᵀ)) *
                ((U : Matrix (Fin m) (Fin m) ℝ) * SY) by
                repeat rw [Matrix.mul_assoc]]
          simp [hV]
    _ = Matrix.trace (SXᵀ * SY) := by
          calc
            Matrix.trace
                (SXᵀ * ((U : Matrix (Fin m) (Fin m) ℝ)ᵀ) *
                  ((U : Matrix (Fin m) (Fin m) ℝ) * SY))
              = Matrix.trace
                  ((((U : Matrix (Fin m) (Fin m) ℝ) * SY) * SXᵀ) *
                    ((U : Matrix (Fin m) (Fin m) ℝ)ᵀ)) := by
                    exact Matrix.trace_mul_cycle
                      SXᵀ
                      ((U : Matrix (Fin m) (Fin m) ℝ)ᵀ)
                      ((U : Matrix (Fin m) (Fin m) ℝ) * SY)
            _ = Matrix.trace
                  (((U : Matrix (Fin m) (Fin m) ℝ)ᵀ) *
                    (U : Matrix (Fin m) (Fin m) ℝ) * (SY * SXᵀ)) := by
                    simpa [Matrix.mul_assoc] using
                      (Matrix.trace_mul_cycle
                        (U : Matrix (Fin m) (Fin m) ℝ)
                        (SY * SXᵀ)
                        ((U : Matrix (Fin m) (Fin m) ℝ)ᵀ))
            _ = Matrix.trace (SY * SXᵀ) := by
                    simp [hU]
            _ = Matrix.trace (SXᵀ * SY) := by
                    rw [Matrix.trace_mul_comm SY SXᵀ]
    _ = dotProduct (singular_value_function X) (singular_value_function Y) := by
          simpa [SX, SY] using trace_singular_value_diagonal_matrix_transpose_mul X Y

/-- Helper for Theorem 7.4: a tail position of the signed singular-value profile reflects to the
corresponding singular-value index in `Fin (min m n)`. -/
lemma signed_singular_value_profile_tailIndex_lt (i : Fin (m + n))
    (hi : m + n - min m n ≤ i.1) :
    m + n - 1 - i.1 < min m n := by
  omega

/-- Helper for Theorem 7.4: the singular-value index attached to a tail coordinate of the signed
singular-value profile. -/
def signed_singular_value_profile_tailIndex (i : Fin (m + n))
    (hi : m + n - min m n ≤ i.1) : Fin (min m n) :=
  ⟨m + n - 1 - i.1, signed_singular_value_profile_tailIndex_lt i hi⟩

/-- Helper for Theorem 7.4: the ordered signed singular-value profile attached to the symmetric
dilation of a rectangular matrix, consisting of the positive singular values, a zero middle block,
and the reversed negative singular values. -/
def signed_singular_value_profile (X : Matrix (Fin m) (Fin n) ℝ) :
    Fin (m + n) → ℝ :=
  fun i ↦
    if hhead : i.1 < min m n then
      singular_value_function X ⟨i.1, hhead⟩
    else if htail : m + n - min m n ≤ i.1 then
      -singular_value_function X (signed_singular_value_profile_tailIndex i htail)
    else
      0

/-- Helper for Theorem 7.4: on the positive head block, the signed singular-value profile agrees
with the singular-value function. -/
lemma signed_singular_value_profile_head
    (X : Matrix (Fin m) (Fin n) ℝ) (i : Fin (m + n))
    (hi : i.1 < min m n) :
    signed_singular_value_profile X i = singular_value_function X ⟨i.1, hi⟩ := by
  -- The head branch of the piecewise profile is exactly the singular-value list.
  simp [signed_singular_value_profile, hi]

/-- Helper for Theorem 7.4: on the middle block between the positive and negative singular-value
tails, the signed singular-value profile vanishes. -/
lemma signed_singular_value_profile_middle
    (X : Matrix (Fin m) (Fin n) ℝ) (i : Fin (m + n))
    (hleft : min m n ≤ i.1) (hright : i.1 < m + n - min m n) :
    signed_singular_value_profile X i = 0 := by
  have hhead : ¬ i.1 < min m n := by
    exact not_lt_of_ge hleft
  have htail : ¬ m + n - min m n ≤ i.1 := by
    exact not_le_of_gt hright
  -- Once the head and tail tests both fail, only the zero middle block remains.
  simp [signed_singular_value_profile, hhead, htail]

/-- Helper for Theorem 7.4: on the negative tail block, the signed singular-value profile is the
reversed negative singular-value list. -/
lemma signed_singular_value_profile_tail
    (X : Matrix (Fin m) (Fin n) ℝ) (i : Fin (m + n))
    (hi : m + n - min m n ≤ i.1) :
    signed_singular_value_profile X i =
      -singular_value_function X (signed_singular_value_profile_tailIndex i hi) := by
  have hhead : ¬ i.1 < min m n := by
    omega
  -- Past the tail cutoff, the profile is definitionally the reversed negative branch.
  simp [signed_singular_value_profile, hhead, hi]

/-- Helper for Theorem 7.4: the signed singular-value profile is weakly decreasing along the
ordered dilation coordinates. -/
lemma signed_singular_value_profile_antitone
    (X : Matrix (Fin m) (Fin n) ℝ) :
    Antitone (signed_singular_value_profile X) := by
  intro i j hij
  by_cases hi_head : i.1 < min m n
  · by_cases hj_head : j.1 < min m n
    · -- On the positive head block, the monotonicity is exactly the monotonicity of singular values.
      rw [signed_singular_value_profile_head X i hi_head,
        signed_singular_value_profile_head X j hj_head]
      exact singular_value_function_antitone X hij
    · have hj_tail_or_middle : j.1 < m + n - min m n ∨ m + n - min m n ≤ j.1 := by
        omega
      rcases hj_tail_or_middle with hj_middle | hj_tail
      · -- The head block is nonnegative and dominates the zero middle block.
        rw [signed_singular_value_profile_head X i hi_head,
          signed_singular_value_profile_middle X j (by omega) hj_middle]
        exact singular_value_function_nonneg X ⟨i.1, hi_head⟩
      · -- The head block is nonnegative and the tail block is nonpositive.
        rw [signed_singular_value_profile_head X i hi_head,
          signed_singular_value_profile_tail X j hj_tail]
        have hσi : 0 ≤ singular_value_function X ⟨i.1, hi_head⟩ :=
          singular_value_function_nonneg X ⟨i.1, hi_head⟩
        have hσ : 0 ≤ singular_value_function X (signed_singular_value_profile_tailIndex j hj_tail) :=
          singular_value_function_nonneg X (signed_singular_value_profile_tailIndex j hj_tail)
        linarith
  · have hi_not_head : min m n ≤ i.1 := by
      omega
    by_cases hi_tail : m + n - min m n ≤ i.1
    · have hj_tail : m + n - min m n ≤ j.1 := by
        omega
      -- On the negative tail block, reversing the index order turns antitonicity back into the
      -- singular-value antitonicity.
      rw [signed_singular_value_profile_tail X i hi_tail,
        signed_singular_value_profile_tail X j hj_tail]
      have htail_nat : m + n - 1 - j.1 ≤ m + n - 1 - i.1 := by
        omega
      have htail :
          (signed_singular_value_profile_tailIndex j hj_tail : ℕ) ≤
            (signed_singular_value_profile_tailIndex i hi_tail : ℕ) := by
        simpa [signed_singular_value_profile_tailIndex] using htail_nat
      have hσ :
          singular_value_function X (signed_singular_value_profile_tailIndex j hj_tail) ≥
            singular_value_function X (signed_singular_value_profile_tailIndex i hi_tail) :=
        singular_value_function_antitone X htail
      linarith
    · have hi_middle : i.1 < m + n - min m n := by
        omega
      have hj_tail_or_middle : j.1 < m + n - min m n ∨ m + n - min m n ≤ j.1 := by
        omega
      rcases hj_tail_or_middle with hj_middle | hj_tail
      · -- The whole middle block is identically zero.
        rw [signed_singular_value_profile_middle X i hi_not_head hi_middle,
          signed_singular_value_profile_middle X j (by omega) hj_middle]
      · -- The zero middle block dominates the negative tail block.
        rw [signed_singular_value_profile_middle X i hi_not_head hi_middle,
          signed_singular_value_profile_tail X j hj_tail]
        have hσ : 0 ≤ singular_value_function X (signed_singular_value_profile_tailIndex j hj_tail) :=
          singular_value_function_nonneg X (signed_singular_value_profile_tailIndex j hj_tail)
        linarith

/-- Helper for Theorem 7.4: the block-sign involution `diag(I,-I)` on `Fin m ⊕ Fin n`. -/
def block_sign_sumMatrix :
    Matrix (Fin m ⊕ Fin n) (Fin m ⊕ Fin n) ℝ :=
  Matrix.fromBlocks
    (1 : Matrix (Fin m) (Fin m) ℝ) 0 0
    (- (1 : Matrix (Fin n) (Fin n) ℝ))

/-- Helper for Theorem 7.4: the block-sign involution reindexed to the `Fin (m + n)` dilation
coordinates. -/
def block_sign_matrix :
    Matrix (Fin (m + n)) (Fin (m + n)) ℝ :=
  Matrix.reindex finSumFinEquiv finSumFinEquiv block_sign_sumMatrix

/-- Helper for Theorem 7.4: conjugating the block symmetric dilation by `diag(I,-I)` flips its
sign. -/
lemma block_sign_conjugate_block_symmetric_dilation_eq_neg
    (X : Matrix (Fin m) (Fin n) ℝ) :
    block_sign_sumMatrix * block_symmetric_dilation X * block_sign_sumMatrixᵀ =
      - block_symmetric_dilation X := by
  -- Route correction: isolate the source-proof sign symmetry on the sum-indexed block matrix
  -- before transporting it to the `Fin (m + n)` coordinates used by the ordered spectrum API.
  rw [block_sign_sumMatrix, block_symmetric_dilation, Matrix.fromBlocks_multiply,
    Matrix.fromBlocks_transpose]
  suffices hmul :
      Matrix.fromBlocks 0 X (-Xᵀ) 0 *
          Matrix.fromBlocks (1 : Matrix (Fin m) (Fin m) ℝ) 0 0
            (- (1 : Matrix (Fin n) (Fin n) ℝ)) =
        -Matrix.fromBlocks 0 X Xᵀ 0 by
    simpa using hmul
  -- The second block multiplication just negates the off-diagonal blocks.
  rw [Matrix.fromBlocks_multiply]
  ext i j
  cases i <;> cases j <;> simp

/-- Helper for Theorem 7.4: conjugating the `Fin (m + n)` symmetric dilation by the reindexed
block-sign involution flips its sign. -/
lemma block_sign_conjugate_symmetric_dilation_eq_neg
    (X : Matrix (Fin m) (Fin n) ℝ) :
    block_sign_matrix * symmetric_dilation X * block_sign_matrixᵀ =
      - symmetric_dilation X := by
  -- Transport the block sign computation through the fixed `finSumFinEquiv` reindexing.
  simpa [block_sign_matrix, symmetric_dilation] using
    congrArg (Matrix.reindex finSumFinEquiv finSumFinEquiv)
      (block_sign_conjugate_block_symmetric_dilation_eq_neg (m := m) (n := n) X)

/-- Helper for Theorem 7.4: orthogonal conjugation by a real matrix with `UᵀU = I` preserves the
characteristic polynomial. -/
private lemma orthogonal_conjugate_charpoly {k : ℕ}
    (U A : Matrix (Fin k) (Fin k) ℝ) (hU : Uᵀ * U = 1) :
    Matrix.charpoly (U * A * Uᵀ) = Matrix.charpoly A := by
  -- Move one orthogonal factor around the characteristic polynomial and cancel it.
  calc
    Matrix.charpoly (U * A * Uᵀ) = Matrix.charpoly (U * (A * Uᵀ)) := by
      simp [Matrix.mul_assoc]
    _ = Matrix.charpoly ((A * Uᵀ) * U) := by
      rw [Matrix.charpoly_mul_comm]
    _ = Matrix.charpoly (A * (Uᵀ * U)) := by
      rw [Matrix.mul_assoc]
    _ = Matrix.charpoly A := by
      rw [hU, Matrix.mul_one]

/-- Helper for Theorem 7.4: symmetric matrices with the same characteristic polynomial have the
same ordered eigenvalue function. -/
lemma symmetric_eigenvalue_function_eq_of_charpoly_eq {k : ℕ}
    (A B : symmetricMatrices k)
    (hchar :
      Matrix.charpoly ((A : symmetricMatrices k) : Matrix (Fin k) (Fin k) ℝ) =
        Matrix.charpoly ((B : symmetricMatrices k) : Matrix (Fin k) (Fin k) ℝ)) :
    symmetric_eigenvalue_function A = symmetric_eigenvalue_function B := by
  have heig0 :
      A.property.isHermitian.eigenvalues₀ = B.property.isHermitian.eigenvalues₀ := by
    -- The ordered Hermitian spectrum is determined by the characteristic polynomial.
    simp_rw [← List.ofFn_inj, ← A.property.isHermitian.sort_roots_charpoly_eq_eigenvalues₀,
      ← B.property.isHermitian.sort_roots_charpoly_eq_eigenvalues₀, hchar]
  ext i
  rw [symmetric_eigenvalue_function_apply, symmetric_eigenvalue_function_apply]
  exact congrFun heig0 (Fin.cast (Fintype.card_fin k).symm i)

/-- Helper for Theorem 7.4: orthogonal conjugation preserves the ordered eigenvalue function of a
real symmetric matrix. -/
lemma symmetric_eigenvalue_function_eq_of_orthogonal_conjugate {k : ℕ}
    (A B : symmetricMatrices k) (U : Matrix (Fin k) (Fin k) ℝ)
    (hU : Uᵀ * U = 1)
    (hB :
      ((B : symmetricMatrices k) : Matrix (Fin k) (Fin k) ℝ) =
        U * (((A : symmetricMatrices k) : Matrix (Fin k) (Fin k) ℝ)) * Uᵀ) :
    symmetric_eigenvalue_function B = symmetric_eigenvalue_function A := by
  -- Reduce to the conjugacy-invariance of the characteristic polynomial.
  apply symmetric_eigenvalue_function_eq_of_charpoly_eq
  rw [hB]
  exact orthogonal_conjugate_charpoly U
    (((A : symmetricMatrices k) : Matrix (Fin k) (Fin k) ℝ)) hU

/-- Helper for Theorem 7.4: reverse a finite vector and flip its sign. -/
def reverse_neg {k : ℕ} (x : Fin k → ℝ) : Fin k → ℝ :=
  fun i ↦ -x i.rev

/-- Helper for Theorem 7.4: reversing an antitone finite vector and negating it preserves
antitonicity. -/
lemma reverse_neg_antitone {k : ℕ} (x : Fin k → ℝ) (hx : Antitone x) :
    Antitone (reverse_neg x) := by
  intro i j hij
  -- Reversing flips the order, and the outer negation restores antitonicity.
  dsimp [reverse_neg]
  have hrev : j.rev ≤ i.rev := by
    simpa using Fin.rev_le_rev.mpr hij
  linarith [hx hrev]

/-- Helper for Theorem 7.4: negating a symmetric matrix reverses its ordered eigenvalue list and
changes every sign. -/
lemma symmetric_eigenvalue_function_neg_eq_reverse_neg {k : ℕ}
    (A : symmetricMatrices k) :
    symmetric_eigenvalue_function
        ⟨-((A : symmetricMatrices k) : Matrix (Fin k) (Fin k) ℝ), by
          have hA :
              (((A : symmetricMatrices k) : Matrix (Fin k) (Fin k) ℝ))ᵀ =
                ((A : symmetricMatrices k) : Matrix (Fin k) (Fin k) ℝ) :=
            mem_symmetricMatrices_iff.mp A.property
          simpa [mem_symmetricMatrices_iff, Matrix.IsSymm] using congrArg Neg.neg hA⟩ =
      reverse_neg (symmetric_eigenvalue_function A) := by
  obtain ⟨Q, hQ⟩ := exists_orthogonal_diagonalization_with_symmetric_eigenvalue_function A
  let z : Fin k → ℝ := reverse_neg (symmetric_eigenvalue_function A)
  let P : Matrix.orthogonalGroup (Fin k) ℝ := permutationOrthogonalMatrix Fin.revPerm
  have hz : Antitone z := reverse_neg_antitone _ (symmetric_eigenvalue_function_antitone A)
  have hdiag :
      Matrix.diagonal (fun i : Fin k ↦ -symmetric_eigenvalue_function A i) =
        ((P : Matrix.orthogonalGroup (Fin k) ℝ) : Matrix (Fin k) (Fin k) ℝ) *
          Matrix.diagonal z *
          (((P : Matrix.orthogonalGroup (Fin k) ℝ) : Matrix (Fin k) (Fin k) ℝ)ᵀ) := by
    -- The reverse permutation turns `diag z` into the diagonal of the entrywise negatives.
    simpa [z, reverse_neg, Function.comp_def] using
      diagonal_comp_perm_eq_orthogonal_conjugate Fin.revPerm z
  have hneg :
      (-((A : symmetricMatrices k) : Matrix (Fin k) (Fin k) ℝ)) =
        (((Q * P : Matrix.orthogonalGroup (Fin k) ℝ) :
            Matrix (Fin k) (Fin k) ℝ)) *
          Matrix.diagonal z *
          ((((Q * P : Matrix.orthogonalGroup (Fin k) ℝ) :
              Matrix (Fin k) (Fin k) ℝ))ᵀ) := by
    -- Rewrite `-A` by negating the diagonal and then reversing the order to make it antitone.
    calc
      -((A : symmetricMatrices k) : Matrix (Fin k) (Fin k) ℝ) =
          -((Q : Matrix (Fin k) (Fin k) ℝ) *
            Matrix.diagonal (symmetric_eigenvalue_function A) *
            ((Q : Matrix (Fin k) (Fin k) ℝ)ᵀ)) := by
              rw [hQ]
      _ = (Q : Matrix (Fin k) (Fin k) ℝ) *
          (-Matrix.diagonal (symmetric_eigenvalue_function A)) *
          ((Q : Matrix (Fin k) (Fin k) ℝ)ᵀ) := by
            have hmul :
                (Q : Matrix (Fin k) (Fin k) ℝ) *
                    (-Matrix.diagonal (symmetric_eigenvalue_function A)) =
                  -((Q : Matrix (Fin k) (Fin k) ℝ) *
                    Matrix.diagonal (symmetric_eigenvalue_function A)) := by
              simpa using
                (Matrix.mul_neg (Q : Matrix (Fin k) (Fin k) ℝ)
                  (Matrix.diagonal (symmetric_eigenvalue_function A)))
            calc
              -((Q : Matrix (Fin k) (Fin k) ℝ) *
                  Matrix.diagonal (symmetric_eigenvalue_function A) *
                  ((Q : Matrix (Fin k) (Fin k) ℝ)ᵀ))
                = -((Q : Matrix (Fin k) (Fin k) ℝ) *
                    Matrix.diagonal (symmetric_eigenvalue_function A)) *
                    ((Q : Matrix (Fin k) (Fin k) ℝ)ᵀ) := by
                      simp [Matrix.mul_assoc]
              _ = ((Q : Matrix (Fin k) (Fin k) ℝ) *
                    (-Matrix.diagonal (symmetric_eigenvalue_function A))) *
                    ((Q : Matrix (Fin k) (Fin k) ℝ)ᵀ) := by
                      rw [← hmul]
              _ = (Q : Matrix (Fin k) (Fin k) ℝ) *
                    (-Matrix.diagonal (symmetric_eigenvalue_function A)) *
                    ((Q : Matrix (Fin k) (Fin k) ℝ)ᵀ) := by
                      simp [Matrix.mul_assoc]
      _ = (Q : Matrix (Fin k) (Fin k) ℝ) *
          Matrix.diagonal (fun i : Fin k ↦ -symmetric_eigenvalue_function A i) *
          ((Q : Matrix (Fin k) (Fin k) ℝ)ᵀ) := by
            simp
      _ = (Q : Matrix (Fin k) (Fin k) ℝ) *
          ((((P : Matrix.orthogonalGroup (Fin k) ℝ) : Matrix (Fin k) (Fin k) ℝ) *
              Matrix.diagonal z *
              (((P : Matrix.orthogonalGroup (Fin k) ℝ) :
                  Matrix (Fin k) (Fin k) ℝ)ᵀ))) *
          ((Q : Matrix (Fin k) (Fin k) ℝ)ᵀ) := by
            rw [hdiag]
      _ = (((Q * P : Matrix.orthogonalGroup (Fin k) ℝ) :
            Matrix (Fin k) (Fin k) ℝ)) *
          Matrix.diagonal z *
          ((((Q * P : Matrix.orthogonalGroup (Fin k) ℝ) :
              Matrix (Fin k) (Fin k) ℝ))ᵀ) := by
            simp [Matrix.mul_assoc, Matrix.transpose_mul]
  -- The negated matrix is an orthogonal conjugate of the antitone diagonal `z`.
  have hneg' :
      (-((A : symmetricMatrices k) : Matrix (Fin k) (Fin k) ℝ)) =
        (Q : Matrix (Fin k) (Fin k) ℝ) *
          (P : Matrix (Fin k) (Fin k) ℝ) *
          Matrix.diagonal z *
          (((P : Matrix (Fin k) (Fin k) ℝ)ᵀ) * ((Q : Matrix (Fin k) (Fin k) ℝ)ᵀ)) := by
    simpa [Matrix.mul_assoc, Matrix.transpose_mul] using hneg
  simpa [z, hneg', Matrix.mul_assoc, Matrix.transpose_mul] using
    orthogonal_diagonal_symmetric_eigenvalue_function_eq_of_antitone (Q * P) z hz

/-- Helper for Theorem 7.4: the block-sign involution is orthogonal on the dilation coordinates. -/
lemma block_sign_matrix_transpose_mul_self :
    block_sign_matrixᵀ * block_sign_matrix =
      (1 : Matrix (Fin (m + n)) (Fin (m + n)) ℝ) := by
  have hsum :
      block_sign_sumMatrixᵀ * block_sign_sumMatrix =
        (1 : Matrix (Fin m ⊕ Fin n) (Fin m ⊕ Fin n) ℝ) := by
    -- The block-sign matrix is diagonal with diagonal entries `±1`.
    rw [block_sign_sumMatrix, Matrix.fromBlocks_transpose, Matrix.fromBlocks_multiply]
    ext i j <;> cases i <;> cases j <;> simpa [Matrix.one_apply]
  -- Reindexing preserves the orthogonality identity.
  simpa [block_sign_matrix] using
    congrArg (Matrix.reindex finSumFinEquiv finSumFinEquiv) hsum

/-- Helper for Theorem 7.4: the ordered eigenvalue list of the dilation is symmetric under
sign-reversal and index reversal. -/
lemma symmetric_dilation_spectrum_eq_reverse_neg
    (X : Matrix (Fin m) (Fin n) ℝ) :
    symmetric_eigenvalue_function (symmetric_dilation_symmetricMatrix X) =
      reverse_neg (symmetric_eigenvalue_function (symmetric_dilation_symmetricMatrix X)) := by
  let A : symmetricMatrices (m + n) := symmetric_dilation_symmetricMatrix X
  let negA : symmetricMatrices (m + n) :=
    ⟨-((A : symmetricMatrices (m + n)) : Matrix (Fin (m + n)) (Fin (m + n)) ℝ), by
      have hA :
          (((A : symmetricMatrices (m + n)) :
              Matrix (Fin (m + n)) (Fin (m + n)) ℝ))ᵀ =
            ((A : symmetricMatrices (m + n)) :
              Matrix (Fin (m + n)) (Fin (m + n)) ℝ) :=
        mem_symmetricMatrices_iff.mp A.property
      simpa [mem_symmetricMatrices_iff, Matrix.IsSymm] using congrArg Neg.neg hA⟩
  have hconj :
      symmetric_eigenvalue_function negA = symmetric_eigenvalue_function A := by
    -- The block-sign involution orthogonally conjugates the dilation to its negative.
    apply symmetric_eigenvalue_function_eq_of_orthogonal_conjugate A negA block_sign_matrix
      block_sign_matrix_transpose_mul_self
    simpa [A, negA] using
      (block_sign_conjugate_symmetric_dilation_eq_neg (m := m) (n := n) X).symm
  -- Compare the direct description of the negated ordered spectrum with the block-sign conjugacy.
  calc
    symmetric_eigenvalue_function A = symmetric_eigenvalue_function negA := hconj.symm
    _ = reverse_neg (symmetric_eigenvalue_function A) :=
      symmetric_eigenvalue_function_neg_eq_reverse_neg A

/-- Helper for Theorem 7.4: the trace of the Gram matrix `Xᵀ X` is the sum of the squares of the
ordered singular values of `X`. -/
private lemma sum_sq_singular_values_eq_trace_transpose_mul
    (X : Matrix (Fin m) (Fin n) ℝ) :
    (∑ i : Fin (min m n), X.toEuclideanLin.singularValues i ^ (2 : ℕ)) =
      Matrix.trace (Xᵀ * X) := by
  have htrace_n :
      Matrix.trace (Xᵀ * X) = ∑ i : Fin n, X.toEuclideanLin.singularValues i ^ (2 : ℕ) := by
    let G : Matrix (Fin n) (Fin n) ℝ := Xᵀ * X
    have hcomp :
        LinearMap.adjoint (Matrix.toEuclideanLin X) ∘ₗ Matrix.toEuclideanLin X =
          Matrix.toEuclideanLin G := by
      -- Identify the matrix Gram operator with `T†T` for `T = X.toEuclideanLin`.
      rw [show LinearMap.adjoint (Matrix.toEuclideanLin X) = Matrix.toEuclideanLin Xᵀ by
        simpa using (Matrix.toEuclideanLin_conjTranspose_eq_adjoint (A := X)).symm]
      ext v j
      simp [G, Matrix.toLpLin_apply, Matrix.mulVec_mulVec]
    have hn : Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) = n := by
      simp
    calc
      Matrix.trace (Xᵀ * X) = G.trace := by
        simp [G]
      _ = LinearMap.trace ℝ (EuclideanSpace ℝ (Fin n)) (Matrix.toEuclideanLin G) := by
        rw [LinearMap.trace_eq_matrix_trace ℝ ((EuclideanSpace.basisFun (Fin n) ℝ).toBasis)]
        simp [Matrix.toEuclideanLin_eq_toLin_orthonormal]
      _ = LinearMap.trace ℝ (EuclideanSpace ℝ (Fin n))
            (LinearMap.adjoint (Matrix.toEuclideanLin X) ∘ₗ Matrix.toEuclideanLin X) := by
        rw [hcomp]
      _ = ∑ i : Fin n,
            ((Matrix.toEuclideanLin X).isSymmetric_adjoint_comp_self.eigenvalues hn i : ℝ) := by
        simpa using
          ((Matrix.toEuclideanLin X).isSymmetric_adjoint_comp_self).trace_eq_sum_eigenvalues hn
      _ = ∑ i : Fin n, X.toEuclideanLin.singularValues i ^ (2 : ℕ) := by
        refine Finset.sum_congr rfl ?_
        intro i hi
        -- Each Gram eigenvalue is the square of the corresponding singular value.
        simpa using (LinearMap.sq_singularValues_fin (T := X.toEuclideanLin) hn i).symm
  by_cases hmn : m ≤ n
  · let f : ℕ → ℝ := fun i ↦ X.toEuclideanLin.singularValues i ^ (2 : ℕ)
    have htrace_range : Matrix.trace (Xᵀ * X) = Finset.sum (Finset.range n) f := by
      exact htrace_n.trans (by simpa [f] using (Fin.sum_univ_eq_sum_range f n))
    have htail : Finset.sum (Finset.Ico m n) f = 0 := by
      apply Finset.sum_eq_zero
      intro i hi
      have hi' : m ≤ i := (Finset.mem_Ico.mp hi).1
      have hfinrank : Module.finrank ℝ X.toEuclideanLin.range ≤ m := by
        simpa using (Submodule.finrank_le X.toEuclideanLin.range)
      have hzero : X.toEuclideanLin.singularValues i = 0 := by
        -- Past the codomain dimension, the singular values of a rectangular `m × n` matrix vanish.
        rw [LinearMap.singularValues_eq_zero_iff_le_finrank_range]
        exact le_trans hfinrank hi'
      simp [hzero]
    -- When `m ≤ n`, split the full `n`-sum into the first `m` terms and the zero tail.
    rw [htrace_range, ← Finset.sum_range_add_sum_Ico f hmn, htail, add_zero]
    rw [Nat.min_eq_left hmn]
    simpa [f] using (Fin.sum_univ_eq_sum_range f m)
  · have hnm : n ≤ m := le_of_not_ge hmn
    -- When `n ≤ m`, the `min m n` truncation already includes every singular value coming from the
    -- domain dimension.
    rw [Nat.min_eq_right hnm]
    exact htrace_n.symm

/-- Helper for Theorem 7.4: the Frobenius self-pairing `Tr(Xᵀ X)` is the self-dot-product of the
ordered singular-value vector. -/
lemma trace_transpose_mul_eq_dotProduct_singular_value_function
    (X : Matrix (Fin m) (Fin n) ℝ) :
    Matrix.trace (Xᵀ * X) =
      dotProduct (singular_value_function X) (singular_value_function X) := by
  -- Rewrite the square-sum formula from Definition 7.20 as the Euclidean self-pairing of `σ(X)`.
  rw [dotProduct]
  symm
  simpa [pow_two, singular_value_function_apply] using
    sum_sq_singular_values_eq_trace_transpose_mul X

/-- Helper for Theorem 7.4: the square trace of the symmetric dilation is the self-dot-product of
its ordered eigenvalue vector. -/
lemma symmetric_dilation_trace_mul_self_eq_dotProduct_spectrum
    (X : Matrix (Fin m) (Fin n) ℝ) :
    Matrix.trace (symmetric_dilation X * symmetric_dilation X) =
      dotProduct
        (symmetric_eigenvalue_function (symmetric_dilation_symmetricMatrix X))
        (symmetric_eigenvalue_function (symmetric_dilation_symmetricMatrix X)) := by
  let A : symmetricMatrices (m + n) := symmetric_dilation_symmetricMatrix X
  obtain ⟨Q, hQ⟩ :=
    exists_orthogonal_diagonalization_with_symmetric_eigenvalue_function
      A
  have hleft :
      Matrix.trace (symmetric_dilation X * symmetric_dilation X) =
        Matrix.trace
          (((Q : Matrix (Fin (m + n)) (Fin (m + n)) ℝ) *
              Matrix.diagonal (symmetric_eigenvalue_function A) *
              ((Q : Matrix (Fin (m + n)) (Fin (m + n)) ℝ)ᵀ)) *
            ((A : symmetricMatrices (m + n)) :
              Matrix (Fin (m + n)) (Fin (m + n)) ℝ)) := by
    simpa [A] using
      congrArg
        (fun M : Matrix (Fin (m + n)) (Fin (m + n)) ℝ ↦
          Matrix.trace
            (M * ((A : symmetricMatrices (m + n)) :
              Matrix (Fin (m + n)) (Fin (m + n)) ℝ))) hQ
  -- Diagonalize the dilation in its ordered eigenbasis and then read off the trace pairing.
  exact hleft.trans <| by
    simpa using
    trace_orthogonal_diagonal_mul_eq_dotProduct_symmetric_eigenvalue_function
      Q A hQ (symmetric_eigenvalue_function A)

/-- Helper for Theorem 7.4: the self-dot-product of the ordered dilation spectrum is exactly twice
the self-dot-product of the singular-value vector. -/
lemma symmetric_dilation_dotProduct_spectrum_eq_two_dotProduct_singular_values
    (X : Matrix (Fin m) (Fin n) ℝ) :
    dotProduct
        (symmetric_eigenvalue_function (symmetric_dilation_symmetricMatrix X))
        (symmetric_eigenvalue_function (symmetric_dilation_symmetricMatrix X)) =
      2 * dotProduct (singular_value_function X) (singular_value_function X) := by
  -- Rewrite the dilation square trace on both the spectral side and the singular-value side.
  calc
    dotProduct
        (symmetric_eigenvalue_function (symmetric_dilation_symmetricMatrix X))
        (symmetric_eigenvalue_function (symmetric_dilation_symmetricMatrix X))
      = Matrix.trace (symmetric_dilation X * symmetric_dilation X) := by
          symm
          exact symmetric_dilation_trace_mul_self_eq_dotProduct_spectrum X
    _ = 2 * Matrix.trace (Xᵀ * X) := by
          simpa using
            symmetric_dilation_trace_mul_eq_two_trace_transpose_mul (X := X) (Y := X)
    _ = 2 * dotProduct (singular_value_function X) (singular_value_function X) := by
          rw [trace_transpose_mul_eq_dotProduct_singular_value_function]

/-- Helper for Theorem 7.4: every coordinate of the positive head of the ordered dilation
spectrum is nonnegative. -/
lemma symmetric_dilation_head_nonneg
    (X : Matrix (Fin m) (Fin n) ℝ) (i : Fin (m + n)) (hi : i.1 < min m n) :
    0 ≤ symmetric_eigenvalue_function (symmetric_dilation_symmetricMatrix X) i := by
  let x := symmetric_eigenvalue_function (symmetric_dilation_symmetricMatrix X)
  have hx_antitone : Antitone x := by
    -- The ordered eigenvalue coordinates are decreasing by definition.
    simpa [x] using
      symmetric_eigenvalue_function_antitone (symmetric_dilation_symmetricMatrix X)
  have hx_symm :
      x = reverse_neg x := by
    -- The block-sign involution pairs the spectrum with its negative reverse.
    simpa [x] using symmetric_dilation_spectrum_eq_reverse_neg (m := m) (n := n) X
  have hij : i ≤ i.rev := by
    -- Head indices lie before their reflected partners because `i` sits in the first `min m n`
    -- positions of the symmetric profile.
    show i.1 ≤ i.rev.1
    simp [Fin.rev]
    omega
  have hge : x i ≥ x i.rev := hx_antitone hij
  have hj :
      x i.rev = -x i := by
    -- Evaluating the reverse-neg symmetry at `i` identifies the reflected coordinate.
    have hx_symm' := congrFun hx_symm i
    simp only [reverse_neg] at hx_symm'
    linarith
  have hnonneg : 0 ≤ x i := by
    linarith
  simpa [x] using hnonneg

/-- Helper for Theorem 7.4: the ordered Gram-spectrum profile of `Xᵀ X`, consisting of the
squared singular values on the leading `min m n` block and zeros afterwards. -/
def gram_square_profile (X : Matrix (Fin m) (Fin n) ℝ) : Fin n → ℝ :=
  fun j ↦
    if h : j.1 < min m n then
      singular_value_function X ⟨j.1, h⟩ ^ (2 : ℕ)
    else
      0

/-- Helper for Theorem 7.4: the squared Gram-spectrum profile is weakly decreasing. -/
lemma gram_square_profile_antitone
    (X : Matrix (Fin m) (Fin n) ℝ) :
    Antitone (gram_square_profile X) := by
  intro i j hij
  by_cases hi : i.1 < min m n
  · by_cases hj : j.1 < min m n
    · -- On the genuine Gram-spectrum block, square the antitone singular-value comparison.
      have hσj : 0 ≤ singular_value_function X ⟨j.1, hj⟩ :=
        singular_value_function_nonneg X ⟨j.1, hj⟩
      have hle :
          singular_value_function X ⟨j.1, hj⟩ ≤
            singular_value_function X ⟨i.1, hi⟩ :=
        singular_value_function_antitone X (by simpa using hij)
      have hsquare :
          singular_value_function X ⟨j.1, hj⟩ ^ (2 : ℕ) ≤
            singular_value_function X ⟨i.1, hi⟩ ^ (2 : ℕ) :=
        pow_le_pow_left₀ hσj hle 2
      simpa [gram_square_profile, hi, hj] using hsquare
    · -- Any genuine squared singular value dominates the zero tail.
      simpa [gram_square_profile, hi, hj] using
        sq_nonneg (singular_value_function X ⟨i.1, hi⟩)
  · have hj : ¬ j.1 < min m n := by
      intro hj
      exact hi (lt_of_le_of_lt (show i.1 ≤ j.1 by simpa using hij) hj)
    -- Past the `min m n` cutoff the profile is identically zero.
    simp [gram_square_profile, hi, hj]

/-- Helper for Theorem 7.4: the square of the symmetric dilation has the same characteristic
polynomial as the block Gram matrix `diag(X Xᵀ, Xᵀ X)`. -/
lemma symmetric_dilation_square_charpoly_eq_block_charpoly
    (X : Matrix (Fin m) (Fin n) ℝ) :
    Matrix.charpoly (symmetric_dilation X * symmetric_dilation X) =
      Matrix.charpoly (X * Xᵀ) * Matrix.charpoly (Xᵀ * X) := by
  -- Undo the fixed `finSumFinEquiv` reindexing and expose the block-diagonal square.
  calc
    Matrix.charpoly (symmetric_dilation X * symmetric_dilation X)
      = Matrix.charpoly
          (Matrix.reindex finSumFinEquiv finSumFinEquiv
            (block_symmetric_dilation X * block_symmetric_dilation X)) := by
            simp [symmetric_dilation]
    _ = Matrix.charpoly (block_symmetric_dilation X * block_symmetric_dilation X) := by
          rw [Matrix.charpoly_reindex]
    _ = Matrix.charpoly
          (Matrix.fromBlocks (X * Xᵀ) 0 0 (Xᵀ * X) :
            Matrix (Fin m ⊕ Fin n) (Fin m ⊕ Fin n) ℝ) := by
          rw [block_symmetric_dilation_mul]
    _ = Matrix.charpoly (X * Xᵀ) * Matrix.charpoly (Xᵀ * X) := by
          simp

/-- Helper for Theorem 7.4: after squaring the dilation, the characteristic polynomial is the
square of the smaller Gram characteristic polynomial times the forced zero tail from the dimension
mismatch. -/
lemma symmetric_dilation_square_charpoly_eq_small_gram_square
    (X : Matrix (Fin m) (Fin n) ℝ) :
    Matrix.charpoly (symmetric_dilation X * symmetric_dilation X) =
      if _hmn : m ≤ n then
        Polynomial.X ^ (n - m) * (Matrix.charpoly (X * Xᵀ)) ^ 2
      else
        Polynomial.X ^ (m - n) * (Matrix.charpoly (Xᵀ * X)) ^ 2 := by
  have hbase :
      Matrix.charpoly (symmetric_dilation X * symmetric_dilation X) =
        Matrix.charpoly (X * Xᵀ) * Matrix.charpoly (Xᵀ * X) :=
    symmetric_dilation_square_charpoly_eq_block_charpoly (m := m) (n := n) X
  by_cases hmn : m ≤ n
  · -- When `m ≤ n`, the larger Gram matrix contributes exactly the zero tail `X^(n-m)`.
    simp only [hmn, dite_eq_ite, if_true]
    rw [hbase]
    have hcomm :
        Matrix.charpoly (Xᵀ * X) =
          Polynomial.X ^ (n - m) * Matrix.charpoly (X * Xᵀ) := by
      simpa using
        (Matrix.charpoly_mul_comm_of_le (A := Xᵀ) (B := X) (by simpa using hmn))
    rw [hcomm]
    ring
  · -- The `n ≤ m` case is the same argument after swapping the two Gram factors.
    simp only [hmn, dite_eq_ite, if_false]
    rw [hbase]
    have hnm : n ≤ m := le_of_not_ge hmn
    have hcomm :
        Matrix.charpoly (X * Xᵀ) =
          Polynomial.X ^ (m - n) * Matrix.charpoly (Xᵀ * X) := by
      simpa using
        (Matrix.charpoly_mul_comm_of_le (A := X) (B := Xᵀ) (by simpa using hnm))
    rw [hcomm]
    ring

/-- Helper for Theorem 7.4: the Gram matrix `Xᵀ X` is symmetric, so it defines an element of
`𝕊^n`. -/
lemma transpose_mul_self_mem_symmetricMatrices
    (X : Matrix (Fin m) (Fin n) ℝ) :
    Xᵀ * X ∈ symmetricMatrices n := by
  -- The transpose of `Xᵀ X` is definitionally itself.
  rw [mem_symmetricMatrices_iff]
  simp [Matrix.transpose_mul, Matrix.mul_assoc]

/-- Helper for Theorem 7.4: the Gram matrix `Xᵀ X` packaged as a symmetric matrix. -/
def transpose_mul_self_symmetricMatrix
    (X : Matrix (Fin m) (Fin n) ℝ) : symmetricMatrices n :=
  ⟨Xᵀ * X, transpose_mul_self_mem_symmetricMatrices X⟩

/-- Helper for Theorem 7.4: the ordered spectrum of the Gram matrix `Xᵀ X` is the squared
singular-value profile followed by the forced zero tail. -/
lemma transpose_mul_self_symmetric_eigenvalue_function_eq_gram_square_profile
    (X : Matrix (Fin m) (Fin n) ℝ) :
    symmetric_eigenvalue_function (transpose_mul_self_symmetricMatrix X) =
      gram_square_profile X := by
  ext i
  have hcomp :
      LinearMap.adjoint (Matrix.toEuclideanLin X) ∘ₗ Matrix.toEuclideanLin X =
        Matrix.toEuclideanLin (Xᵀ * X) := by
    -- Rewrite the Gram operator of `X.toEuclideanLin` back into matrix multiplication.
    rw [show LinearMap.adjoint (Matrix.toEuclideanLin X) = Matrix.toEuclideanLin (Xᵀ) by
      simpa using (Matrix.toEuclideanLin_conjTranspose_eq_adjoint (A := X)).symm]
    ext v j
    simpa [Matrix.toLpLin_apply, Matrix.mulVec_mulVec, Matrix.transpose_mul, Matrix.mul_assoc] using
      congrArg (fun M : Matrix (Fin n) (Fin n) ℝ ↦ (M *ᵥ v.ofLp) j) (rfl : Xᵀ * X = Xᵀ * X)
  have hsq :
      (Matrix.toEuclideanLin X).singularValues i.1 ^ 2 =
        symmetric_eigenvalue_function (transpose_mul_self_symmetricMatrix X) i := by
    have hGramHermitian : (Xᵀ * X).IsHermitian := by
      simp [Matrix.IsHermitian, Matrix.transpose_mul, Matrix.mul_assoc]
    have hsq' :
        (Matrix.toEuclideanLin X).singularValues i.1 ^ 2 =
          ((Matrix.isSymmetric_toEuclideanLin_iff).2
            hGramHermitian).eigenvalues finrank_euclideanSpace
              (Fin.cast (Fintype.card_fin n).symm i) := by
      -- Mathlib identifies the ordered Gram spectrum with the squared singular values.
      simpa [hcomp] using
        (LinearMap.sq_singularValues_fin (T := Matrix.toEuclideanLin X)
          (hn := finrank_euclideanSpace) (i := Fin.cast (Fintype.card_fin n).symm i))
    -- Transport the Euclidean-linear-map eigenvalue coordinate back to the matrix-side spectrum.
    simpa [symmetric_eigenvalue_function_apply, transpose_mul_self_symmetricMatrix,
      Matrix.IsHermitian.eigenvalues₀] using hsq'
  by_cases hi : i.1 < min m n
  · have hs :
        (Matrix.toEuclideanLin X).singularValues i.1 =
          singular_value_function X ⟨i.1, hi⟩ := by
      rw [singular_value_function_apply]
    have hsquare :
        (singular_value_function X ⟨i.1, hi⟩) ^ (2 : ℕ) =
          symmetric_eigenvalue_function (transpose_mul_self_symmetricMatrix X) i := by
      calc
        (singular_value_function X ⟨i.1, hi⟩) ^ (2 : ℕ)
          = (Matrix.toEuclideanLin X).singularValues i.1 ^ (2 : ℕ) := by rw [hs.symm]
        _ = symmetric_eigenvalue_function (transpose_mul_self_symmetricMatrix X) i := hsq
    -- On the leading `min m n` block, the Gram eigenvalues are exactly the squared singular values.
    simpa [gram_square_profile, hi] using hsquare.symm
  · have htail : (Matrix.toEuclideanLin X).singularValues i.1 = 0 := by
      rw [LinearMap.singularValues_eq_zero_iff_le_finrank_range]
      have hrange_le : Module.finrank ℝ (LinearMap.range (Matrix.toEuclideanLin X)) ≤ m := by
        simpa using (Submodule.finrank_le (LinearMap.range (Matrix.toEuclideanLin X)))
      exact le_trans hrange_le (by omega)
    -- Past the `min m n` cutoff, the remaining Gram spectrum is forced to be zero.
    have hz :
        symmetric_eigenvalue_function (transpose_mul_self_symmetricMatrix X) i = 0 := by
      rw [← hsq, htail]
      norm_num
    simpa [gram_square_profile, hi] using hz

/-- Helper for Theorem 7.4: the ordered square-spectrum profile of the symmetric dilation,
obtained by duplicating each squared singular value and appending the zero tail forced by the
dimension mismatch. -/
def symmetric_dilation_square_profile
    (X : Matrix (Fin m) (Fin n) ℝ) : Fin (m + n) → ℝ :=
  fun j ↦
    if h : j.1 < 2 * min m n then
      (singular_value_function X ⟨j.1 / 2, by
        omega⟩) ^ (2 : ℕ)
    else
      0

/-- Helper for Theorem 7.4: the duplicated square-spectrum profile of the symmetric dilation is
weakly decreasing. -/
lemma symmetric_dilation_square_profile_antitone
    (X : Matrix (Fin m) (Fin n) ℝ) :
    Antitone (symmetric_dilation_square_profile X) := by
  intro i j hij
  have hij_nat : i.1 ≤ j.1 := by
    exact hij
  by_cases hj : j.1 < 2 * min m n
  · have hi : i.1 < 2 * min m n := by
      exact lt_of_le_of_lt hij_nat hj
    have hdiv : i.1 / 2 ≤ j.1 / 2 :=
      Nat.div_le_div_right hij_nat
    have hσj : 0 ≤ singular_value_function X ⟨j.1 / 2, by omega⟩ :=
      singular_value_function_nonneg X ⟨j.1 / 2, by omega⟩
    have hσle :
        singular_value_function X ⟨j.1 / 2, by omega⟩ ≤
          singular_value_function X ⟨i.1 / 2, by omega⟩ := by
      -- Dividing by two collapses each adjacent pair back to the same singular-value index.
      exact singular_value_function_antitone X (show i.1 / 2 ≤ j.1 / 2 from hdiv)
    have hsquare :
        (singular_value_function X ⟨j.1 / 2, by omega⟩) ^ (2 : ℕ) ≤
          (singular_value_function X ⟨i.1 / 2, by omega⟩) ^ (2 : ℕ) := by
      -- Squaring preserves order because singular values are nonnegative.
      exact pow_le_pow_left₀ hσj hσle 2
    simpa [symmetric_dilation_square_profile, hi, hj] using hsquare
  · by_cases hi : i.1 < 2 * min m n
    · have hσi : 0 ≤ singular_value_function X ⟨i.1 / 2, by omega⟩ :=
        singular_value_function_nonneg X ⟨i.1 / 2, by omega⟩
      -- The remaining head square is nonnegative, so it still dominates the zero tail.
      simpa [symmetric_dilation_square_profile, hi, hj] using
        sq_nonneg (singular_value_function X ⟨i.1 / 2, by omega⟩)
    · -- Once both indices lie past the cutoff, the duplicated square profile is identically zero.
      simp [symmetric_dilation_square_profile, hi, hj]

/-- Helper for Theorem 7.4: the square of the symmetric dilation is again symmetric. -/
lemma symmetric_dilation_square_mem_symmetricMatrices
    (X : Matrix (Fin m) (Fin n) ℝ) :
    symmetric_dilation X * symmetric_dilation X ∈ symmetricMatrices (m + n) := by
  -- The square of a symmetric matrix is symmetric because `Aᵀ = A`.
  rw [mem_symmetricMatrices_iff]
  have hsymm := symmetric_dilation_isSymm X
  simpa [Matrix.IsSymm, Matrix.transpose_mul, Matrix.mul_assoc] using congrArg (fun M ↦ M * M) hsymm

/-- Helper for Theorem 7.4: the square of the symmetric dilation viewed as an element of
`𝕊^(m+n)`. -/
def symmetric_dilation_square_symmetricMatrix
    (X : Matrix (Fin m) (Fin n) ℝ) : symmetricMatrices (m + n) :=
  ⟨symmetric_dilation X * symmetric_dilation X, symmetric_dilation_square_mem_symmetricMatrices X⟩

/-- Helper for Theorem 7.4: pairing the indices `2 * i` and `2 * i + 1` in `range (2 * p)`
duplicates each factor exactly twice. -/
lemma duplicated_range_product_eq_square_product
    {α : Type*} [CommMonoid α] (p : ℕ) (f : ℕ → α) :
    Finset.prod (Finset.range (2 * p)) (fun j ↦ f (j / 2)) =
      Finset.prod (Finset.range p) (fun i ↦ (f i) ^ 2) := by
  induction p with
  | zero =>
      -- The empty duplicated range contributes no factors.
      simp
  | succ p ih =>
      -- Peel off the two new indices `2 * p` and `2 * p + 1`; both divide back to `p`.
      have heven : (2 * p) / 2 = p := by
        omega
      have hodd : (2 * p + 1) / 2 = p := by
        omega
      calc
        Finset.prod (Finset.range (2 * (p + 1))) (fun j ↦ f (j / 2))
          = Finset.prod (Finset.range (2 * p)) (fun j ↦ f (j / 2)) *
              f ((2 * p) / 2) * f ((2 * p + 1) / 2) := by
              rw [show 2 * (p + 1) = 2 * p + 1 + 1 by omega, Finset.prod_range_succ,
                Finset.prod_range_succ]
        _ = Finset.prod (Finset.range p) (fun i ↦ (f i) ^ 2) * f p * f p := by
              rw [ih, heven, hodd]
        _ = Finset.prod (Finset.range p) (fun i ↦ (f i) ^ 2) * (f p) ^ 2 := by
              simp [pow_two, mul_assoc]
        _ = Finset.prod (Finset.range (p + 1)) (fun i ↦ (f i) ^ 2) := by
              rw [Finset.prod_range_succ]

/-- Helper for Theorem 7.4: the diagonal matrix attached to the duplicated square-spectrum profile
has the expected factorized characteristic polynomial. -/
lemma symmetric_dilation_square_profile_charpoly
    (X : Matrix (Fin m) (Fin n) ℝ) :
    Matrix.charpoly (Matrix.diagonal (symmetric_dilation_square_profile X)) =
      Polynomial.X ^ (m + n - 2 * min m n) *
        ∏ i : Fin (min m n),
          (Polynomial.X - Polynomial.C ((singular_value_function X i) ^ (2 : ℕ) : ℝ)) ^ 2 := by
  let p : ℕ := min m n
  let f : ℕ → Polynomial ℝ := fun j ↦
    if hj : j < m + n then
      Polynomial.X - Polynomial.C (symmetric_dilation_square_profile X ⟨j, hj⟩)
    else
      1
  have hp : 2 * p ≤ m + n := by
    omega
  have hprod :
      Matrix.charpoly (Matrix.diagonal (symmetric_dilation_square_profile X)) =
        Finset.prod (Finset.range (m + n)) f := by
    -- Rewrite the diagonal characteristic polynomial in the natural `range (m + n)` indexing.
    calc
      Matrix.charpoly (Matrix.diagonal (symmetric_dilation_square_profile X))
        = ∏ i : Fin (m + n),
            (Polynomial.X - Polynomial.C (symmetric_dilation_square_profile X i)) := by
              simpa using Matrix.charpoly_diagonal (symmetric_dilation_square_profile X)
      _ = ∏ i : Fin (m + n), f i := by
            simp [f]
      _ = Finset.prod (Finset.range (m + n)) f := by
            simpa using (Fin.prod_univ_eq_prod_range f (m + n))
  have hhead :
      Finset.prod (Finset.range (2 * p)) f =
        ∏ i : Fin p,
          (Polynomial.X - Polynomial.C ((singular_value_function X i) ^ (2 : ℕ) : ℝ)) ^ 2 := by
    -- On the leading block, `symmetric_dilation_square_profile` is exactly the duplicated squared
    -- singular-value list.
    let g : ℕ → Polynomial ℝ := fun j ↦
      if hj : j < p then
        Polynomial.X - Polynomial.C ((singular_value_function X ⟨j, hj⟩) ^ (2 : ℕ) : ℝ)
      else
        1
    have hg_range :
        Finset.prod (Finset.range p) (fun j ↦ (g j) ^ 2) =
          ∏ i : Fin p,
            (Polynomial.X - Polynomial.C ((singular_value_function X i) ^ (2 : ℕ) : ℝ)) ^ 2 := by
      calc
        Finset.prod (Finset.range p) (fun j ↦ (g j) ^ 2)
          = ∏ i : Fin p, (g i) ^ 2 := by
              symm
              exact Fin.prod_univ_eq_prod_range (fun j ↦ (g j) ^ 2) p
        _ = ∏ i : Fin p,
              (Polynomial.X - Polynomial.C ((singular_value_function X i) ^ (2 : ℕ) : ℝ)) ^ 2 := by
              simp [g]
    calc
      Finset.prod (Finset.range (2 * p)) f
        = Finset.prod (Finset.range (2 * p)) (fun j ↦ g (j / 2)) := by
                apply Finset.prod_congr rfl
                intro j hj
                have hjp : j < 2 * p := Finset.mem_range.mp hj
                have hjmn : j < m + n := lt_of_lt_of_le hjp hp
                have hjdiv : j / 2 < p := by
                  omega
                have hprofile :
                    symmetric_dilation_square_profile X ⟨j, hjmn⟩ =
                      (singular_value_function X ⟨j / 2, hjdiv⟩) ^ (2 : ℕ) := by
                    simp [symmetric_dilation_square_profile, hjp, p]
                simp [f, g, hjmn, hprofile, hjdiv]
      _ = ∏ i : Fin p,
            (Polynomial.X - Polynomial.C ((singular_value_function X i) ^ (2 : ℕ) : ℝ)) ^ 2 := by
              exact (duplicated_range_product_eq_square_product (p := p) (f := g)).trans hg_range
  have htail :
      Finset.prod (Finset.Ico (2 * p) (m + n)) f =
        Polynomial.X ^ (m + n - 2 * p) := by
    -- Past the duplicated head, the square profile is zero, so each diagonal factor is `X`.
    calc
      Finset.prod (Finset.Ico (2 * p) (m + n)) f
        = Finset.prod (Finset.Ico (2 * p) (m + n)) (fun _ ↦ Polynomial.X) := by
            apply Finset.prod_congr rfl
            intro j hj
            have hjmn : j < m + n := (Finset.mem_Ico.mp hj).2
            have hjp : ¬ j < 2 * p := not_lt_of_ge (Finset.mem_Ico.mp hj).1
            have hnot : ¬ j < 2 * min m n := by
              simpa [p] using hjp
            have hprofile : symmetric_dilation_square_profile X ⟨j, hjmn⟩ = 0 := by
              simp [symmetric_dilation_square_profile, hnot]
            simp [f, hjmn, hprofile]
      _ = Polynomial.X ^ (m + n - 2 * p) := by
            simp
  -- Split the diagonal characteristic polynomial into the duplicated head and the zero tail.
  calc
    Matrix.charpoly (Matrix.diagonal (symmetric_dilation_square_profile X))
      = Finset.prod (Finset.range (2 * p)) f * Finset.prod (Finset.Ico (2 * p) (m + n)) f := by
          rw [hprod]
          exact (Finset.prod_range_mul_prod_Ico f hp).symm
    _ = (∏ i : Fin p,
          (Polynomial.X - Polynomial.C ((singular_value_function X i) ^ (2 : ℕ) : ℝ)) ^ 2) *
          Polynomial.X ^ (m + n - 2 * p) := by
            rw [hhead, htail]
    _ = Polynomial.X ^ (m + n - 2 * p) *
          ∏ i : Fin p,
            (Polynomial.X - Polynomial.C ((singular_value_function X i) ^ (2 : ℕ) : ℝ)) ^ 2 := by
            rw [mul_comm]
    _ = Polynomial.X ^ (m + n - 2 * min m n) *
          ∏ i : Fin (min m n),
            (Polynomial.X - Polynomial.C ((singular_value_function X i) ^ (2 : ℕ) : ℝ)) ^ 2 := by
            simp [p]

/-- Helper for Theorem 7.4: the diagonal Gram-spectrum profile has the expected characteristic
polynomial, with the zero tail contributing the forced power of `X`. -/
lemma gram_square_profile_charpoly
    (X : Matrix (Fin m) (Fin n) ℝ) :
    Matrix.charpoly (Matrix.diagonal (gram_square_profile X)) =
      Polynomial.X ^ (n - min m n) *
        ∏ i : Fin (min m n),
          (Polynomial.X - Polynomial.C ((singular_value_function X i) ^ (2 : ℕ) : ℝ)) := by
  let p : ℕ := min m n
  let f : ℕ → Polynomial ℝ := fun j ↦
    if hj : j < n then
      Polynomial.X - Polynomial.C (gram_square_profile X ⟨j, hj⟩)
    else
      1
  have hp : p ≤ n := Nat.min_le_right _ _
  have hprod :
      Matrix.charpoly (Matrix.diagonal (gram_square_profile X)) =
        Finset.prod (Finset.range n) f := by
    -- Rewrite the diagonal characteristic polynomial in `range n` coordinates.
    calc
      Matrix.charpoly (Matrix.diagonal (gram_square_profile X))
        = ∏ i : Fin n,
            (Polynomial.X - Polynomial.C (gram_square_profile X i)) := by
              simpa using Matrix.charpoly_diagonal (gram_square_profile X)
      _ = ∏ i : Fin n, f i := by
            simp [f]
      _ = Finset.prod (Finset.range n) f := by
            simpa using (Fin.prod_univ_eq_prod_range f n)
  have hhead :
      Finset.prod (Finset.range p) f =
        ∏ i : Fin p,
          (Polynomial.X - Polynomial.C ((singular_value_function X i) ^ (2 : ℕ) : ℝ)) := by
    -- On the leading block the Gram profile is exactly the squared singular-value list.
    calc
      Finset.prod (Finset.range p) f
        = ∏ i : Fin p, f i := by
            symm
            exact Fin.prod_univ_eq_prod_range f p
      _ = ∏ i : Fin p,
            (Polynomial.X - Polynomial.C ((singular_value_function X i) ^ (2 : ℕ) : ℝ)) := by
            apply Finset.prod_congr rfl
            intro i hi
            have hi_n : (i : ℕ) < n := lt_of_lt_of_le i.2 hp
            have hi_m : (i : ℕ) < m := lt_of_lt_of_le i.2 (Nat.min_le_left _ _)
            simp [f, gram_square_profile, hi_n, hi_m]
  have htail :
      Finset.prod (Finset.Ico p n) f = Polynomial.X ^ (n - p) := by
    -- Past the `min m n` cutoff the Gram profile vanishes, so every factor is just `X`.
    calc
      Finset.prod (Finset.Ico p n) f
        = Finset.prod (Finset.Ico p n) (fun _ ↦ Polynomial.X) := by
            apply Finset.prod_congr rfl
            intro j hj
            have hjn : j < n := (Finset.mem_Ico.mp hj).2
            have hjp : ¬ j < p := not_lt_of_ge (Finset.mem_Ico.mp hj).1
            have hnot : ¬ j < min m n := by
              simpa [p] using hjp
            have hprofile : gram_square_profile X ⟨j, hjn⟩ = 0 := by
              simp [gram_square_profile, hnot]
            simp [f, hjn, hprofile]
      _ = Polynomial.X ^ (n - p) := by
            simp
  -- Split the diagonal characteristic polynomial into the nonzero head and the zero tail.
  calc
    Matrix.charpoly (Matrix.diagonal (gram_square_profile X))
      = Finset.prod (Finset.range p) f * Finset.prod (Finset.Ico p n) f := by
          rw [hprod]
          exact (Finset.prod_range_mul_prod_Ico f hp).symm
    _ = (∏ i : Fin p,
          (Polynomial.X - Polynomial.C ((singular_value_function X i) ^ (2 : ℕ) : ℝ))) *
          Polynomial.X ^ (n - p) := by
            rw [hhead, htail]
    _ = Polynomial.X ^ (n - p) *
          ∏ i : Fin p,
            (Polynomial.X - Polynomial.C ((singular_value_function X i) ^ (2 : ℕ) : ℝ)) := by
            rw [mul_comm]
    _ = Polynomial.X ^ (n - min m n) *
          ∏ i : Fin (min m n),
            (Polynomial.X - Polynomial.C ((singular_value_function X i) ^ (2 : ℕ) : ℝ)) := by
            simp [p]

/-- Helper for Theorem 7.4: diagonalizing the Gram matrix `Xᵀ X` and rewriting its ordered
spectrum identifies its characteristic polynomial with the diagonal Gram-spectrum model. -/
lemma transpose_mul_self_charpoly_eq_gram_square_profile_charpoly
    (X : Matrix (Fin m) (Fin n) ℝ) :
    Matrix.charpoly (Xᵀ * X) = Matrix.charpoly (Matrix.diagonal (gram_square_profile X)) := by
  let A : symmetricMatrices n := transpose_mul_self_symmetricMatrix X
  obtain ⟨Q, hQ⟩ :=
    exists_orthogonal_diagonalization_with_symmetric_eigenvalue_function A
  have hQQ :
      ((Q : Matrix (Fin n) (Fin n) ℝ)ᵀ) * (Q : Matrix (Fin n) (Fin n) ℝ) = 1 :=
    (Matrix.mem_orthogonalGroup_iff' (A := (Q : Matrix (Fin n) (Fin n) ℝ)) (R := ℝ)).1 Q.2
  -- Compare the Gram matrix with its ordered orthogonal diagonalization.
  calc
    Matrix.charpoly (Xᵀ * X)
      = Matrix.charpoly
          (((A : symmetricMatrices n) : Matrix (Fin n) (Fin n) ℝ)) := by
            rfl
    _ = Matrix.charpoly
          ((Q : Matrix (Fin n) (Fin n) ℝ) *
            Matrix.diagonal (symmetric_eigenvalue_function A) *
            ((Q : Matrix (Fin n) (Fin n) ℝ)ᵀ)) := by
            rw [hQ]
    _ = Matrix.charpoly (Matrix.diagonal (symmetric_eigenvalue_function A)) := by
          exact
            orthogonal_conjugate_charpoly
              (U := (Q : Matrix (Fin n) (Fin n) ℝ))
              (A := Matrix.diagonal (symmetric_eigenvalue_function A)) hQQ
    _ = Matrix.charpoly (Matrix.diagonal (gram_square_profile X)) := by
          rw [transpose_mul_self_symmetric_eigenvalue_function_eq_gram_square_profile]

/-- Helper for Theorem 7.4: the ordered spectrum of the squared symmetric dilation is exactly the
duplicated squared singular-value profile. -/
lemma symmetric_dilation_square_symmetric_eigenvalue_function_eq_duplicated_square_profile
    (X : Matrix (Fin m) (Fin n) ℝ) :
    symmetric_eigenvalue_function (symmetric_dilation_square_symmetricMatrix X) =
      symmetric_dilation_square_profile X := by
  let A : symmetricMatrices (m + n) := symmetric_dilation_square_symmetricMatrix X
  let D : symmetricMatrices (m + n) :=
    ⟨Matrix.diagonal (symmetric_dilation_square_profile X),
      diagonal_mem_symmetricMatrices (symmetric_dilation_square_profile X)⟩
  have hchar :
      Matrix.charpoly ((A : symmetricMatrices (m + n)) :
        Matrix (Fin (m + n)) (Fin (m + n)) ℝ) =
        Matrix.charpoly ((D : symmetricMatrices (m + n)) :
          Matrix (Fin (m + n)) (Fin (m + n)) ℝ) := by
    by_cases hmn : m ≤ n
    · have hmul :
          Matrix.charpoly (Xᵀ * X) =
            Polynomial.X ^ (n - m) * Matrix.charpoly (X * Xᵀ) := by
        simpa using
          (Matrix.charpoly_mul_comm_of_le (A := Xᵀ) (B := X) (by simpa using hmn))
      have hgram :
          Matrix.charpoly (Xᵀ * X) =
            Polynomial.X ^ (n - m) *
              ∏ i : Fin (min m n),
                (Polynomial.X - Polynomial.C ((singular_value_function X i) ^ (2 : ℕ) : ℝ)) := by
        calc
          Matrix.charpoly (Xᵀ * X)
            = Matrix.charpoly (Matrix.diagonal (gram_square_profile X)) := by
                exact transpose_mul_self_charpoly_eq_gram_square_profile_charpoly X
          _ = Polynomial.X ^ (n - min m n) *
                ∏ i : Fin (min m n),
                  (Polynomial.X - Polynomial.C ((singular_value_function X i) ^ (2 : ℕ) : ℝ)) := by
                exact gram_square_profile_charpoly X
          _ = Polynomial.X ^ (n - m) *
                ∏ i : Fin (min m n),
                  (Polynomial.X - Polynomial.C ((singular_value_function X i) ^ (2 : ℕ) : ℝ)) := by
                simp [Nat.min_eq_left hmn]
      have hsmall :
          Matrix.charpoly (X * Xᵀ) =
            ∏ i : Fin (min m n),
              (Polynomial.X - Polynomial.C ((singular_value_function X i) ^ (2 : ℕ) : ℝ)) := by
        have hpow_ne :
            Polynomial.X ^ (n - m : ℕ) ≠ (0 : Polynomial ℝ) := by
          exact pow_ne_zero _ Polynomial.X_ne_zero
        have hEqMul :
            Polynomial.X ^ (n - m) * Matrix.charpoly (X * Xᵀ) =
              Polynomial.X ^ (n - m) *
                ∏ i : Fin (min m n),
                  (Polynomial.X - Polynomial.C ((singular_value_function X i) ^ (2 : ℕ) : ℝ)) := by
          rw [← hmul, hgram]
        exact mul_left_cancel₀ hpow_ne hEqMul
      -- Rewrite the squared dilation charpoly through the smaller Gram matrix, then substitute
      -- the singular-value-square factorization obtained above.
      calc
        Matrix.charpoly ((A : symmetricMatrices (m + n)) :
            Matrix (Fin (m + n)) (Fin (m + n)) ℝ)
          = Matrix.charpoly (symmetric_dilation X * symmetric_dilation X) := by
              rfl
        _ = Polynomial.X ^ (n - m) * (Matrix.charpoly (X * Xᵀ)) ^ 2 := by
              simpa [hmn] using symmetric_dilation_square_charpoly_eq_small_gram_square
                (m := m) (n := n) X
        _ = Polynomial.X ^ (n - m) *
              (∏ i : Fin (min m n),
                (Polynomial.X - Polynomial.C ((singular_value_function X i) ^ (2 : ℕ) : ℝ))) ^ 2 := by
              rw [hsmall]
        _ = Polynomial.X ^ (n - m) *
              ∏ i : Fin (min m n),
                (Polynomial.X - Polynomial.C ((singular_value_function X i) ^ (2 : ℕ) : ℝ)) ^ 2 := by
              rw [pow_two]
              congr 1
              calc
                (∏ i : Fin (min m n),
                    (Polynomial.X - Polynomial.C ((singular_value_function X i) ^ (2 : ℕ) : ℝ))) *
                    ∏ i : Fin (min m n),
                      (Polynomial.X - Polynomial.C ((singular_value_function X i) ^ (2 : ℕ) : ℝ))
                  = ∏ i : Fin (min m n),
                      ((Polynomial.X - Polynomial.C ((singular_value_function X i) ^ (2 : ℕ) : ℝ)) *
                        (Polynomial.X - Polynomial.C ((singular_value_function X i) ^ (2 : ℕ) : ℝ))) := by
                    rw [← Finset.prod_mul_distrib]
                _ = ∏ i : Fin (min m n),
                      (Polynomial.X - Polynomial.C ((singular_value_function X i) ^ (2 : ℕ) : ℝ)) ^ 2 := by
                    apply Finset.prod_congr rfl
                    intro i hi
                    simp [pow_two]
        _ = Matrix.charpoly ((D : symmetricMatrices (m + n)) :
              Matrix (Fin (m + n)) (Fin (m + n)) ℝ) := by
              symm
              simpa [D, Nat.min_eq_left hmn, show m + n - 2 * m = n - m by omega] using
                symmetric_dilation_square_profile_charpoly (m := m) (n := n) X
    · have hnm : n ≤ m := le_of_not_ge hmn
      have hgram :
          Matrix.charpoly (Xᵀ * X) =
            ∏ i : Fin (min m n),
              (Polynomial.X - Polynomial.C ((singular_value_function X i) ^ (2 : ℕ) : ℝ)) := by
        calc
          Matrix.charpoly (Xᵀ * X)
            = Matrix.charpoly (Matrix.diagonal (gram_square_profile X)) := by
                exact transpose_mul_self_charpoly_eq_gram_square_profile_charpoly X
          _ = Polynomial.X ^ (n - min m n) *
                ∏ i : Fin (min m n),
                  (Polynomial.X - Polynomial.C ((singular_value_function X i) ^ (2 : ℕ) : ℝ)) := by
                exact gram_square_profile_charpoly X
          _ = ∏ i : Fin (min m n),
                (Polynomial.X - Polynomial.C ((singular_value_function X i) ^ (2 : ℕ) : ℝ)) := by
                simp [Nat.min_eq_right hnm]
      -- In the `n ≤ m` branch, the smaller Gram matrix is already `Xᵀ X`.
      calc
        Matrix.charpoly ((A : symmetricMatrices (m + n)) :
            Matrix (Fin (m + n)) (Fin (m + n)) ℝ)
          = Matrix.charpoly (symmetric_dilation X * symmetric_dilation X) := by
              rfl
        _ = Polynomial.X ^ (m - n) * (Matrix.charpoly (Xᵀ * X)) ^ 2 := by
              simpa [hmn] using symmetric_dilation_square_charpoly_eq_small_gram_square
                (m := m) (n := n) X
        _ = Polynomial.X ^ (m - n) *
              (∏ i : Fin (min m n),
                (Polynomial.X - Polynomial.C ((singular_value_function X i) ^ (2 : ℕ) : ℝ))) ^ 2 := by
              rw [hgram]
        _ = Polynomial.X ^ (m - n) *
              ∏ i : Fin (min m n),
                (Polynomial.X - Polynomial.C ((singular_value_function X i) ^ (2 : ℕ) : ℝ)) ^ 2 := by
              rw [pow_two]
              congr 1
              calc
                (∏ i : Fin (min m n),
                    (Polynomial.X - Polynomial.C ((singular_value_function X i) ^ (2 : ℕ) : ℝ))) *
                    ∏ i : Fin (min m n),
                      (Polynomial.X - Polynomial.C ((singular_value_function X i) ^ (2 : ℕ) : ℝ))
                  = ∏ i : Fin (min m n),
                      ((Polynomial.X - Polynomial.C ((singular_value_function X i) ^ (2 : ℕ) : ℝ)) *
                        (Polynomial.X - Polynomial.C ((singular_value_function X i) ^ (2 : ℕ) : ℝ))) := by
                    rw [← Finset.prod_mul_distrib]
                _ = ∏ i : Fin (min m n),
                      (Polynomial.X - Polynomial.C ((singular_value_function X i) ^ (2 : ℕ) : ℝ)) ^ 2 := by
                    apply Finset.prod_congr rfl
                    intro i hi
                    simp [pow_two]
        _ = Matrix.charpoly ((D : symmetricMatrices (m + n)) :
              Matrix (Fin (m + n)) (Fin (m + n)) ℝ) := by
              symm
              simpa [D, Nat.min_eq_right hnm, show m + n - 2 * n = m - n by omega] using
                symmetric_dilation_square_profile_charpoly (m := m) (n := n) X
  have heig :
      symmetric_eigenvalue_function A = symmetric_eigenvalue_function D :=
    symmetric_eigenvalue_function_eq_of_charpoly_eq A D hchar
  -- The diagonal model already has the target ordered spectrum because the square profile is
  -- antitone.
  calc
    symmetric_eigenvalue_function A = symmetric_eigenvalue_function D := heig
    _ = symmetric_dilation_square_profile X := by
          simpa [D] using
            diagonal_symmetric_eigenvalue_function_eq_of_antitone
              (symmetric_dilation_square_profile X)
              (symmetric_dilation_square_profile_antitone X)

/-- Helper for Theorem 7.4: reverse-neg symmetry identifies each middle-strip coordinate of the
ordered dilation spectrum with the negative of its reflected partner. -/
lemma symmetric_dilation_middle_eq_neg_rev_of_reverse_neg
    (X : Matrix (Fin m) (Fin n) ℝ) (i : Fin (m + n))
    (hleft : min m n ≤ i.1) (hright : i.1 < m + n - min m n) :
    symmetric_eigenvalue_function (symmetric_dilation_symmetricMatrix X) i =
      -symmetric_eigenvalue_function (symmetric_dilation_symmetricMatrix X) i.rev := by
  let x := symmetric_eigenvalue_function (symmetric_dilation_symmetricMatrix X)
  have hx_symm : x = reverse_neg x := by
    -- The block-sign involution identifies the spectrum with its reversed negation.
    simpa [x] using symmetric_dilation_spectrum_eq_reverse_neg (m := m) (n := n) X
  -- The middle-strip assumptions are kept to document the intended range of this reflection fact.
  have hx_eval := congrFun hx_symm i
  simpa [x, reverse_neg] using hx_eval

/-- Helper for Theorem 7.4: the duplicated positive-head square profile built from the ordered
dilation spectrum. -/
def squared_dilation_head_square_profile
    (X : Matrix (Fin m) (Fin n) ℝ) : Fin (m + n) → ℝ :=
  fun j ↦
    if h : j.1 < 2 * min m n then
      (symmetric_eigenvalue_function (symmetric_dilation_symmetricMatrix X)
        ⟨j.1 / 2, by
          omega⟩) ^ (2 : ℕ)
    else
      0

/-- Helper for Theorem 7.4: the duplicated positive-head square profile built from the ordered
dilation spectrum is antitone. -/
lemma squared_dilation_head_square_profile_antitone
    (X : Matrix (Fin m) (Fin n) ℝ) :
    Antitone (squared_dilation_head_square_profile X) := by
  let eig := symmetric_eigenvalue_function (symmetric_dilation_symmetricMatrix X)
  have heig_antitone : Antitone eig := by
    -- The ordered dilation spectrum is decreasing by definition.
    simpa [eig] using
      symmetric_eigenvalue_function_antitone (symmetric_dilation_symmetricMatrix X)
  intro i j hij
  have hij_nat : i.1 ≤ j.1 := by
    exact hij
  by_cases hj : j.1 < 2 * min m n
  · have hi : i.1 < 2 * min m n := by
      exact lt_of_le_of_lt hij_nat hj
    have hdiv : i.1 / 2 ≤ j.1 / 2 := Nat.div_le_div_right hij_nat
    have hj_half_mn : j.1 / 2 < m + n := by
      omega
    have hj_half : j.1 / 2 < min m n := by
      omega
    have heig_nonneg : 0 ≤ eig ⟨j.1 / 2, hj_half_mn⟩ := by
      -- The duplicated profile only reads positive-head coordinates of the ordered dilation
      -- spectrum, so the relevant square root input is nonnegative.
      exact symmetric_dilation_head_nonneg (m := m) (n := n) X ⟨j.1 / 2, hj_half_mn⟩ hj_half
    have heig_le :
        eig ⟨j.1 / 2, hj_half_mn⟩ ≤
          eig ⟨i.1 / 2, by
            omega⟩ := by
      -- Dividing by two collapses each adjacent pair back to the same head index.
      exact heig_antitone (by simpa using hdiv)
    have hsquare :
        (eig ⟨j.1 / 2, hj_half_mn⟩) ^ (2 : ℕ) ≤
          (eig ⟨i.1 / 2, by
            omega⟩) ^ (2 : ℕ) := by
      -- Squaring preserves order on the nonnegative head of the dilation spectrum.
      exact pow_le_pow_left₀ heig_nonneg heig_le 2
    simpa [squared_dilation_head_square_profile, eig, hi, hj] using hsquare
  · by_cases hi : i.1 < 2 * min m n
    · have hi_half : i.1 / 2 < min m n := by
        omega
      have hi_half_mn : i.1 / 2 < m + n := by
        omega
      have heig_nonneg : 0 ≤ eig ⟨i.1 / 2, hi_half_mn⟩ := by
        -- The remaining head square still dominates the zero tail.
        exact symmetric_dilation_head_nonneg (m := m) (n := n) X ⟨i.1 / 2, hi_half_mn⟩ hi_half
      simpa [squared_dilation_head_square_profile, eig, hi, hj] using
        sq_nonneg (eig ⟨i.1 / 2, hi_half_mn⟩)
    · -- Once both coordinates lie past the duplicated head, the profile is identically zero.
      simp [squared_dilation_head_square_profile, hi, hj]

/-- Helper for Theorem 7.4: the squared positive head of the ordered dilation spectrum, indexed
only by the active `min m n` singular-value coordinates. -/
def dilation_head_square_profile
    (X : Matrix (Fin m) (Fin n) ℝ) : Fin (min m n) → ℝ :=
  fun i ↦
    (symmetric_eigenvalue_function (symmetric_dilation_symmetricMatrix X)
      ⟨i.1,
        lt_of_lt_of_le i.2
          (Nat.le_trans (Nat.min_le_left m n) (Nat.le_add_right m n))⟩) ^ (2 : ℕ)

/-- Helper for Theorem 7.4: the diagonal matrix built from the duplicated head-square profile has
the expected zero-tail times squared-head characteristic polynomial. -/
lemma squared_dilation_head_square_profile_charpoly
    (X : Matrix (Fin m) (Fin n) ℝ) :
    Matrix.charpoly (Matrix.diagonal (squared_dilation_head_square_profile X)) =
      Polynomial.X ^ (m + n - 2 * min m n) *
        (Matrix.charpoly (Matrix.diagonal (dilation_head_square_profile X))) ^ 2 := by
  let p : ℕ := min m n
  let f : ℕ → Polynomial ℝ := fun j ↦
    if hj : j < m + n then
      Polynomial.X - Polynomial.C (squared_dilation_head_square_profile X ⟨j, hj⟩)
    else
      1
  have hp : 2 * p ≤ m + n := by
    omega
  have hprod :
      Matrix.charpoly (Matrix.diagonal (squared_dilation_head_square_profile X)) =
        Finset.prod (Finset.range (m + n)) f := by
    -- Rewrite the diagonal characteristic polynomial in the natural `range (m + n)` coordinates.
    calc
      Matrix.charpoly (Matrix.diagonal (squared_dilation_head_square_profile X))
        = ∏ i : Fin (m + n),
            (Polynomial.X - Polynomial.C (squared_dilation_head_square_profile X i)) := by
              simpa using Matrix.charpoly_diagonal (squared_dilation_head_square_profile X)
      _ = ∏ i : Fin (m + n), f i := by
            simp [f]
      _ = Finset.prod (Finset.range (m + n)) f := by
            simpa using (Fin.prod_univ_eq_prod_range f (m + n))
  have hhead :
      Finset.prod (Finset.range (2 * p)) f =
        ∏ i : Fin p,
          (Polynomial.X - Polynomial.C (dilation_head_square_profile X i)) ^ 2 := by
    -- The leading duplicated block reads each head-square factor exactly twice.
    let g : ℕ → Polynomial ℝ := fun j ↦
      if hj : j < p then
        Polynomial.X - Polynomial.C (dilation_head_square_profile X ⟨j, hj⟩)
      else
        1
    have hg_range :
        Finset.prod (Finset.range p) (fun j ↦ (g j) ^ 2) =
          ∏ i : Fin p,
            (Polynomial.X - Polynomial.C (dilation_head_square_profile X i)) ^ 2 := by
      calc
        Finset.prod (Finset.range p) (fun j ↦ (g j) ^ 2)
          = ∏ i : Fin p, (g i) ^ 2 := by
              symm
              exact Fin.prod_univ_eq_prod_range (fun j ↦ (g j) ^ 2) p
        _ = ∏ i : Fin p,
              (Polynomial.X - Polynomial.C (dilation_head_square_profile X i)) ^ 2 := by
              simp [g]
    calc
      Finset.prod (Finset.range (2 * p)) f
        = Finset.prod (Finset.range (2 * p)) (fun j ↦ g (j / 2)) := by
            apply Finset.prod_congr rfl
            intro j hj
            have hjp : j < 2 * p := Finset.mem_range.mp hj
            have hjmn : j < m + n := lt_of_lt_of_le hjp hp
            have hjdiv : j / 2 < p := by
              omega
            have hprofile :
                squared_dilation_head_square_profile X ⟨j, hjmn⟩ =
                  dilation_head_square_profile X ⟨j / 2, hjdiv⟩ := by
              simp [squared_dilation_head_square_profile, dilation_head_square_profile, hjp, p]
            simp [f, g, hjmn, hprofile, hjdiv]
      _ = ∏ i : Fin p,
            (Polynomial.X - Polynomial.C (dilation_head_square_profile X i)) ^ 2 := by
            exact (duplicated_range_product_eq_square_product (p := p) (f := g)).trans hg_range
  have htail :
      Finset.prod (Finset.Ico (2 * p) (m + n)) f =
        Polynomial.X ^ (m + n - 2 * p) := by
    -- Past the duplicated head, the profile vanishes, so every diagonal factor is `X`.
    calc
      Finset.prod (Finset.Ico (2 * p) (m + n)) f
        = Finset.prod (Finset.Ico (2 * p) (m + n)) (fun _ ↦ Polynomial.X) := by
            apply Finset.prod_congr rfl
            intro j hj
            have hjmn : j < m + n := (Finset.mem_Ico.mp hj).2
            have hjp : ¬ j < 2 * p := not_lt_of_ge (Finset.mem_Ico.mp hj).1
            have hnot : ¬ j < 2 * min m n := by
              simpa [p] using hjp
            have hprofile : squared_dilation_head_square_profile X ⟨j, hjmn⟩ = 0 := by
              simp [squared_dilation_head_square_profile, hnot]
            simp [f, hjmn, hprofile]
      _ = Polynomial.X ^ (m + n - 2 * p) := by
            simp
  have hdiag_sq :
      (Matrix.charpoly (Matrix.diagonal (dilation_head_square_profile X))) ^ 2 =
        ∏ i : Fin p,
          (Polynomial.X - Polynomial.C (dilation_head_square_profile X i : ℝ)) ^ 2 := by
    -- Squaring the diagonal characteristic polynomial squares each head factor pointwise.
    rw [Matrix.charpoly_diagonal, pow_two]
    calc
      (∏ i : Fin p, (Polynomial.X - Polynomial.C (dilation_head_square_profile X i : ℝ))) *
          ∏ i : Fin p, (Polynomial.X - Polynomial.C (dilation_head_square_profile X i : ℝ))
        = ∏ i : Fin p,
            ((Polynomial.X - Polynomial.C (dilation_head_square_profile X i : ℝ)) *
              (Polynomial.X - Polynomial.C (dilation_head_square_profile X i : ℝ))) := by
              rw [← Finset.prod_mul_distrib]
      _ = ∏ i : Fin p,
            (Polynomial.X - Polynomial.C (dilation_head_square_profile X i : ℝ)) ^ 2 := by
            apply Finset.prod_congr rfl
            intro i hi
            simp [pow_two]
  -- Split the diagonal characteristic polynomial into the duplicated head block and the forced
  -- zero tail, then rewrite the duplicated head product as a squared diagonal charpoly.
  calc
    Matrix.charpoly (Matrix.diagonal (squared_dilation_head_square_profile X))
      = Finset.prod (Finset.range (2 * p)) f * Finset.prod (Finset.Ico (2 * p) (m + n)) f := by
          rw [hprod]
          exact (Finset.prod_range_mul_prod_Ico f hp).symm
    _ = (∏ i : Fin p,
          (Polynomial.X - Polynomial.C (dilation_head_square_profile X i)) ^ 2) *
          Polynomial.X ^ (m + n - 2 * p) := by
            rw [hhead, htail]
    _ = Polynomial.X ^ (m + n - 2 * p) *
          ∏ i : Fin p,
            (Polynomial.X - Polynomial.C (dilation_head_square_profile X i)) ^ 2 := by
            rw [mul_comm]
    _ = Polynomial.X ^ (m + n - 2 * p) *
          (Matrix.charpoly (Matrix.diagonal (dilation_head_square_profile X))) ^ 2 := by
            rw [hdiag_sq]
    _ = Polynomial.X ^ (m + n - 2 * min m n) *
          (Matrix.charpoly (Matrix.diagonal (dilation_head_square_profile X))) ^ 2 := by
            simp [p]

/-- Helper for Theorem 7.4: squaring an ordered orthogonal diagonalization of the symmetric
dilation turns the squared dilation into the diagonal matrix of the squared ordered spectrum, so
the two matrices have the same characteristic polynomial. -/
lemma symmetric_dilation_square_charpoly_eq_squared_ordered_diagonal
    (X : Matrix (Fin m) (Fin n) ℝ) :
    let A : symmetricMatrices (m + n) := symmetric_dilation_symmetricMatrix X
    let z : Fin (m + n) → ℝ := fun i ↦ (symmetric_eigenvalue_function A i) ^ (2 : ℕ)
    Matrix.charpoly (symmetric_dilation X * symmetric_dilation X) =
      Matrix.charpoly (Matrix.diagonal z) := by
  let A : symmetricMatrices (m + n) := symmetric_dilation_symmetricMatrix X
  obtain ⟨Q, hQ⟩ :=
    exists_orthogonal_diagonalization_with_symmetric_eigenvalue_function A
  have hQQ :
      ((Q : Matrix (Fin (m + n)) (Fin (m + n)) ℝ)ᵀ) *
          (Q : Matrix (Fin (m + n)) (Fin (m + n)) ℝ) = 1 :=
    (Matrix.mem_orthogonalGroup_iff' (A := (Q : Matrix (Fin (m + n)) (Fin (m + n)) ℝ))
      (R := ℝ)).1 Q.2
  let z : Fin (m + n) → ℝ := fun i ↦ (symmetric_eigenvalue_function A i) ^ (2 : ℕ)
  have hdiag_sq :
      Matrix.diagonal (symmetric_eigenvalue_function A) *
          Matrix.diagonal (symmetric_eigenvalue_function A) =
        Matrix.diagonal z := by
    -- Squaring the ordered diagonal acts pointwise on the diagonal entries.
    simpa [z, pow_two] using
      (Matrix.diagonal_mul_diagonal
        (symmetric_eigenvalue_function A)
        (symmetric_eigenvalue_function A))
  -- Square the ordered dilation diagonalization first, then remove the orthogonal conjugation
  -- from the characteristic polynomial.
  calc
    Matrix.charpoly (symmetric_dilation X * symmetric_dilation X)
      = Matrix.charpoly
          ((((Q : Matrix (Fin (m + n)) (Fin (m + n)) ℝ) *
              Matrix.diagonal (symmetric_eigenvalue_function A) *
              ((Q : Matrix (Fin (m + n)) (Fin (m + n)) ℝ)ᵀ)) *
            ((Q : Matrix (Fin (m + n)) (Fin (m + n)) ℝ) *
              Matrix.diagonal (symmetric_eigenvalue_function A) *
              ((Q : Matrix (Fin (m + n)) (Fin (m + n)) ℝ)ᵀ)))) := by
            simpa [A] using
              congrArg
                (fun M : Matrix (Fin (m + n)) (Fin (m + n)) ℝ ↦ Matrix.charpoly (M * M)) hQ
    _ = Matrix.charpoly
          ((Q : Matrix (Fin (m + n)) (Fin (m + n)) ℝ) *
            Matrix.diagonal z *
            ((Q : Matrix (Fin (m + n)) (Fin (m + n)) ℝ)ᵀ)) := by
            congr 1
            calc
              (((Q : Matrix (Fin (m + n)) (Fin (m + n)) ℝ) *
                    Matrix.diagonal (symmetric_eigenvalue_function A) *
                    ((Q : Matrix (Fin (m + n)) (Fin (m + n)) ℝ)ᵀ)) *
                  ((Q : Matrix (Fin (m + n)) (Fin (m + n)) ℝ) *
                    Matrix.diagonal (symmetric_eigenvalue_function A) *
                    ((Q : Matrix (Fin (m + n)) (Fin (m + n)) ℝ)ᵀ)))
                  =
                  (Q : Matrix (Fin (m + n)) (Fin (m + n)) ℝ) *
                    Matrix.diagonal (symmetric_eigenvalue_function A) *
                    (((Q : Matrix (Fin (m + n)) (Fin (m + n)) ℝ)ᵀ) *
                      (Q : Matrix (Fin (m + n)) (Fin (m + n)) ℝ)) *
                    Matrix.diagonal (symmetric_eigenvalue_function A) *
                    ((Q : Matrix (Fin (m + n)) (Fin (m + n)) ℝ)ᵀ) := by
                      simp [Matrix.mul_assoc]
              _ =
                  (Q : Matrix (Fin (m + n)) (Fin (m + n)) ℝ) *
                    Matrix.diagonal (symmetric_eigenvalue_function A) *
                    Matrix.diagonal (symmetric_eigenvalue_function A) *
                    ((Q : Matrix (Fin (m + n)) (Fin (m + n)) ℝ)ᵀ) := by
                      rw [hQQ]
                      simp [Matrix.mul_assoc]
              _ =
                  (Q : Matrix (Fin (m + n)) (Fin (m + n)) ℝ) *
                    Matrix.diagonal z *
                    ((Q : Matrix (Fin (m + n)) (Fin (m + n)) ℝ)ᵀ) := by
                      simpa [Matrix.mul_assoc] using
                        congrArg
                          (fun M : Matrix (Fin (m + n)) (Fin (m + n)) ℝ ↦
                            (Q : Matrix (Fin (m + n)) (Fin (m + n)) ℝ) * M *
                              ((Q : Matrix (Fin (m + n)) (Fin (m + n)) ℝ)ᵀ))
                          hdiag_sq
    _ = Matrix.charpoly (Matrix.diagonal z) := by
          exact
            orthogonal_conjugate_charpoly
              (U := (Q : Matrix (Fin (m + n)) (Fin (m + n)) ℝ))
              (A := Matrix.diagonal z) hQQ

/-- Helper for Theorem 7.4: orthogonal diagonalization preserves rank, so a real symmetric matrix
has the same rank as the diagonal matrix of its ordered eigenvalue function. -/
lemma symmetric_rank_eq_diagonal_spectrum_rank {k : ℕ}
    (A : symmetricMatrices k) :
    (((A : symmetricMatrices k) : Matrix (Fin k) (Fin k) ℝ)).rank =
      (Matrix.diagonal (symmetric_eigenvalue_function A)).rank := by
  obtain ⟨Q, hQ⟩ := exists_orthogonal_diagonalization_with_symmetric_eigenvalue_function A
  have hQQ_left :
      ((Q : Matrix (Fin k) (Fin k) ℝ) *
          ((Q : Matrix (Fin k) (Fin k) ℝ)ᵀ)) = 1 :=
    (Matrix.mem_orthogonalGroup_iff (A := (Q : Matrix (Fin k) (Fin k) ℝ)) (R := ℝ)).1 Q.2
  have hQQ_right :
      (((Q : Matrix (Fin k) (Fin k) ℝ)ᵀ) *
          (Q : Matrix (Fin k) (Fin k) ℝ)) = 1 :=
    (Matrix.mem_orthogonalGroup_iff' (A := (Q : Matrix (Fin k) (Fin k) ℝ)) (R := ℝ)).1 Q.2
  have hdetQ : IsUnit ((Q : Matrix (Fin k) (Fin k) ℝ)).det :=
    Matrix.isUnit_det_of_right_inverse hQQ_left
  have hdetQt : IsUnit (((Q : Matrix (Fin k) (Fin k) ℝ)ᵀ)).det :=
    Matrix.isUnit_det_of_left_inverse hQQ_left
  -- Remove the orthogonal factors on the left and right one at a time.
  calc
    (((A : symmetricMatrices k) : Matrix (Fin k) (Fin k) ℝ)).rank
      = (((Q : Matrix (Fin k) (Fin k) ℝ) *
            Matrix.diagonal (symmetric_eigenvalue_function A) *
            ((Q : Matrix (Fin k) (Fin k) ℝ)ᵀ))).rank := by
            rw [hQ]
    _ = (((Q : Matrix (Fin k) (Fin k) ℝ) *
            Matrix.diagonal (symmetric_eigenvalue_function A))).rank := by
            rw [Matrix.rank_mul_eq_left_of_isUnit_det
              (((Q : Matrix (Fin k) (Fin k) ℝ)ᵀ))
              (((Q : Matrix (Fin k) (Fin k) ℝ) *
                  Matrix.diagonal (symmetric_eigenvalue_function A)))
              hdetQt]
    _ = (Matrix.diagonal (symmetric_eigenvalue_function A)).rank := by
            rw [Matrix.rank_mul_eq_right_of_isUnit_det
              ((Q : Matrix (Fin k) (Fin k) ℝ))
              (Matrix.diagonal (symmetric_eigenvalue_function A))
              hdetQ]

/-- Helper for Theorem 7.4: the square of the symmetric dilation has rank at most
`2 * min m n`, because its ordered spectrum is supported on the duplicated head block. -/
lemma symmetric_dilation_square_rank_le_twice_min
    (X : Matrix (Fin m) (Fin n) ℝ) :
    (symmetric_dilation X * symmetric_dilation X).rank ≤ 2 * min m n := by
  let p : ℕ := min m n
  let y : Fin (m + n) → ℝ := symmetric_dilation_square_profile X
  have hrank_diag :
      (symmetric_dilation X * symmetric_dilation X).rank =
        (Matrix.diagonal y).rank := by
    -- Read the squared dilation through its ordered orthogonal diagonalization.
    calc
      (symmetric_dilation X * symmetric_dilation X).rank
        = (Matrix.diagonal
            (symmetric_eigenvalue_function (symmetric_dilation_square_symmetricMatrix X))).rank := by
              simpa using
                symmetric_rank_eq_diagonal_spectrum_rank
                  (symmetric_dilation_square_symmetricMatrix X)
      _ = (Matrix.diagonal y).rank := by
            rw [symmetric_dilation_square_symmetric_eigenvalue_function_eq_duplicated_square_profile]
  have hsupport :
      Fintype.card {i // y i ≠ 0} ≤ 2 * p := by
    let f : {i // y i ≠ 0} → Fin (2 * p) := fun i ↦
      ⟨i.1.1, by
        have hi_lt : i.1.1 < m + n := i.1.2
        by_contra hi_head
        have hnot : ¬ i.1.1 < 2 * min m n := by
          simpa [p] using hi_head
        have hzero : y i.1 = 0 := by
          simp [y, symmetric_dilation_square_profile, hnot]
        exact i.2 hzero⟩
    have hf : Function.Injective f := by
      intro a b hab
      apply Subtype.ext
      exact Fin.ext (by simpa [f] using congrArg Fin.val hab)
    simpa [f, p] using Fintype.card_le_of_injective f hf
  -- The diagonal rank is the number of its nonzero entries, and those entries occur only in the
  -- leading duplicated block.
  calc
    (symmetric_dilation X * symmetric_dilation X).rank
      = Fintype.card {i // y i ≠ 0} := by
          rw [hrank_diag, Matrix.rank_diagonal]
    _ ≤ 2 * p := hsupport

/-- Helper for Theorem 7.4: any positive eigenvalue in the middle strip of the ordered dilation
would force too many nonzero eigenvalues, contradicting the rank bound. -/
lemma positive_middle_symmetric_dilation_rank_lower_bound
    (X : Matrix (Fin m) (Fin n) ℝ) (i : Fin (m + n))
    (hleft : min m n ≤ i.1)
    (hpos : 0 < symmetric_eigenvalue_function (symmetric_dilation_symmetricMatrix X) i) :
    2 * (i.1 + 1) ≤
      ((symmetric_dilation : Matrix (Fin m) (Fin n) ℝ →
          Matrix (Fin (m + n)) (Fin (m + n)) ℝ) X).rank := by
  let x : Fin (m + n) → ℝ := symmetric_eigenvalue_function (symmetric_dilation_symmetricMatrix X)
  have hx_antitone : Antitone x := by
    simpa [x] using
      symmetric_eigenvalue_function_antitone (symmetric_dilation_symmetricMatrix X)
  have hx_symm : x = reverse_neg x := by
    simpa [x] using symmetric_dilation_spectrum_eq_reverse_neg (m := m) (n := n) X
  let e : Fin (i.1 + 1) → Fin (m + n) := fun j ↦
    ⟨j.1, by
      exact lt_of_lt_of_le j.2 (Nat.succ_le_of_lt i.2)⟩
  have he_le : ∀ j : Fin (i.1 + 1), e j ≤ i := by
    intro j
    exact show (e j).1 ≤ i.1 by
      exact Nat.le_of_lt_succ j.2
  have hleft_pos : ∀ j : Fin (i.1 + 1), 0 < x (e j) := by
    intro j
    have hge : x (e j) ≥ x i := hx_antitone (he_le j)
    linarith
  have hleft_nonzero : ∀ j : Fin (i.1 + 1), x (e j) ≠ 0 := by
    intro j
    linarith [hleft_pos j]
  have hright_neg : ∀ j : Fin (i.1 + 1), x (e j).rev < 0 := by
    intro j
    have hsymm_j : x (e j) = -x (e j).rev := by
      have hx_eval := congrFun hx_symm (e j)
      simpa [reverse_neg] using hx_eval
    linarith [hleft_pos j]
  have hright_nonzero : ∀ j : Fin (i.1 + 1), x (e j).rev ≠ 0 := by
    intro j
    linarith [hright_neg j]
  let f :
      Sum (Fin (i.1 + 1)) (Fin (i.1 + 1)) →
        {j // x j ≠ 0} :=
    Sum.elim
      (fun j ↦ ⟨e j, hleft_nonzero j⟩)
      (fun j ↦ ⟨(e j).rev, hright_nonzero j⟩)
  have hf : Function.Injective f := by
    intro a b hab
    rcases a with a | a <;> rcases b with b | b
    · have hab' : e a = e b := by
        simpa [f] using congrArg Subtype.val hab
      have hEq : a = b := by
        apply Fin.ext
        simpa [e] using congrArg Fin.val hab'
      simpa [hEq]
    · exfalso
      have heq : x (e a) = x (e b).rev := by
        simpa [f, e] using congrArg (fun t ↦ x t.1) hab
      linarith [hleft_pos a, hright_neg b]
    · exfalso
      have heq : x (e a).rev = x (e b) := by
        simpa [f, e] using congrArg (fun t ↦ x t.1) hab
      linarith [hright_neg a, hleft_pos b]
    · have hval : (e a).rev = (e b).rev := by
        simpa [f, e] using congrArg Subtype.val hab
      have hab' : e a = e b := Fin.rev_injective hval
      have hEq : a = b := by
        apply Fin.ext
        simpa [e] using congrArg Fin.val hab'
      simpa [hEq]
  have hrank_support :
      2 * (i.1 + 1) ≤ Fintype.card {j // x j ≠ 0} := by
    calc
      2 * (i.1 + 1)
        = Fintype.card (Sum (Fin (i.1 + 1)) (Fin (i.1 + 1))) := by
            simp
            omega
      _ ≤ Fintype.card {j // x j ≠ 0} := by
            exact Fintype.card_le_of_injective f hf
  -- Compare the size of the nonzero spectrum with the diagonal rank of the ordered orthogonal
  -- diagonalization.
  calc
    2 * (i.1 + 1) ≤ Fintype.card {j // x j ≠ 0} := hrank_support
    _ = (Matrix.diagonal x).rank := by
          symm
          exact Matrix.rank_diagonal x
    _ = ((symmetric_dilation : Matrix (Fin m) (Fin n) ℝ →
            Matrix (Fin (m + n)) (Fin (m + n)) ℝ) X).rank := by
          symm
          simpa [x] using
            symmetric_rank_eq_diagonal_spectrum_rank
              (symmetric_dilation_symmetricMatrix X)

/-- Helper for Theorem 7.4: the middle strip of the ordered dilation spectrum is zero by the
rank bound on the symmetric dilation. -/
lemma symmetric_dilation_middle_eq_zero_of_rank_bound
    (X : Matrix (Fin m) (Fin n) ℝ) (i : Fin (m + n))
    (hleft : min m n ≤ i.1) (hright : i.1 < m + n - min m n) :
    symmetric_eigenvalue_function (symmetric_dilation_symmetricMatrix X) i = 0 := by
  let x : Fin (m + n) → ℝ := symmetric_eigenvalue_function (symmetric_dilation_symmetricMatrix X)
  have hrank_square :
      (symmetric_dilation X).rank ≤ 2 * min m n := by
    have hsymm : (symmetric_dilation X).IsSymm := symmetric_dilation_isSymm X
    calc
      (symmetric_dilation X).rank = (symmetric_dilation X * (symmetric_dilation X)ᵀ).rank := by
        symm
        simpa using Matrix.rank_self_mul_transpose (symmetric_dilation X)
      _ = (symmetric_dilation X * symmetric_dilation X).rank := by
        rw [show (symmetric_dilation X)ᵀ = symmetric_dilation X by
          exact hsymm.eq]
      _ ≤ 2 * min m n := symmetric_dilation_square_rank_le_twice_min (m := m) (n := n) X
  by_contra hxi
  have hx_symm : x = reverse_neg x := by
    simpa [x] using symmetric_dilation_spectrum_eq_reverse_neg (m := m) (n := n) X
  have hsplit : x i < 0 ∨ 0 < x i := lt_or_gt_of_ne hxi
  rcases hsplit with hneg | hpos
  · have hrev_pos : 0 < x i.rev := by
      have hx_eval := congrFun hx_symm i
      have hsymm_i : x i = -x i.rev := by
        simpa [x, reverse_neg] using hx_eval
      linarith
    have hrev_left : min m n ≤ i.rev.1 := by
      simp [Fin.rev]
      omega
    have hlarge :
        2 * (i.rev.1 + 1) ≤ (symmetric_dilation X).rank :=
      positive_middle_symmetric_dilation_rank_lower_bound
        (m := m) (n := n) X i.rev hrev_left hrev_pos
    have hstrict : 2 * min m n < 2 * (i.rev.1 + 1) := by
      simp [Fin.rev]
      omega
    omega
  · have hlarge :
        2 * (i.1 + 1) ≤ (symmetric_dilation X).rank :=
      positive_middle_symmetric_dilation_rank_lower_bound
        (m := m) (n := n) X i hleft hpos
    have hstrict : 2 * min m n < 2 * (i.1 + 1) := by
      omega
    omega

/-- Helper for Theorem 7.4: reflecting the negative tail of the squared ordered dilation spectrum
recovers exactly the positive head-square diagonal factors. -/
lemma ordered_squared_dilation_tail_product_reflects_head_square_profile
    (X : Matrix (Fin m) (Fin n) ℝ) :
    let A : symmetricMatrices (m + n) := symmetric_dilation_symmetricMatrix X
    let z : Fin (m + n) → ℝ := fun i ↦ (symmetric_eigenvalue_function A i) ^ (2 : ℕ)
    let p : ℕ := min m n
    let f : ℕ → Polynomial ℝ := fun j ↦
      if hj : j < m + n then
        Polynomial.X - Polynomial.C (z ⟨j, hj⟩)
      else
        1
    Finset.prod (Finset.Ico (m + n - p) (m + n)) f =
      Matrix.charpoly (Matrix.diagonal (dilation_head_square_profile X)) := by
  let A : symmetricMatrices (m + n) := symmetric_dilation_symmetricMatrix X
  let z : Fin (m + n) → ℝ := fun i ↦ (symmetric_eigenvalue_function A i) ^ (2 : ℕ)
  let p : ℕ := min m n
  let f : ℕ → Polynomial ℝ := fun j ↦
    if hj : j < m + n then
      Polynomial.X - Polynomial.C (z ⟨j, hj⟩)
    else
      1
  let g : ℕ → Polynomial ℝ := fun j ↦
    if hj : j < p then
      Polynomial.X - Polynomial.C (dilation_head_square_profile X ⟨j, hj⟩)
    else
      1
  have hshift :
      Finset.prod (Finset.Ico (m + n - p) (m + n)) f =
        Finset.prod (Finset.range p) (fun j ↦ f (m + n - p + j)) := by
    -- Shift the tail interval down to `range p` before applying the reflection formula.
    rw [Finset.prod_Ico_eq_prod_range]
    have hrange : m + n - (m + n - p) = p := by
      simpa [p] using (show m + n - (m + n - min m n) = min m n by omega)
    rw [hrange]
  have hreflect :
      Finset.prod (Finset.range p) (fun j ↦ f (m + n - p + j)) =
        Finset.prod (Finset.range p) (fun j ↦ g (p - 1 - j)) := by
    -- Each shifted tail factor is the square of a reflected head eigenvalue, so the sign drops
    -- out and only the head-square factor remains.
    apply Finset.prod_congr rfl
    intro j hj
    have hjp : j < p := Finset.mem_range.mp hj
    have hjmn : m + n - p + j < m + n := by
      omega
    have hrev : p - 1 - j < p := by
      omega
    let tail : Fin (m + n) := ⟨m + n - p + j, hjmn⟩
    have hsymm :
        symmetric_eigenvalue_function (symmetric_dilation_symmetricMatrix X) tail =
          -symmetric_eigenvalue_function (symmetric_dilation_symmetricMatrix X) tail.rev := by
      -- Evaluate the reverse-neg symmetry at the chosen tail coordinate.
      have hx := congrFun (symmetric_dilation_spectrum_eq_reverse_neg (m := m) (n := n) X) tail
      simpa [reverse_neg] using hx
    have htail_rev :
        tail.rev = ⟨p - 1 - j, by
          omega⟩ := by
      ext
      simp [tail, p, Fin.rev]
      omega
    have hz_eq :
        z tail = dilation_head_square_profile X ⟨p - 1 - j, hrev⟩ := by
      -- After reflecting the tail index back to the head, squaring removes the minus sign.
      calc
        z tail =
            (symmetric_eigenvalue_function (symmetric_dilation_symmetricMatrix X) tail) ^
              (2 : ℕ) := by
              rfl
        _ =
            (-symmetric_eigenvalue_function (symmetric_dilation_symmetricMatrix X) tail.rev) ^
              (2 : ℕ) := by
              rw [hsymm]
        _ =
            (symmetric_eigenvalue_function (symmetric_dilation_symmetricMatrix X)
              ⟨p - 1 - j, by
                omega⟩) ^ (2 : ℕ) := by
              rw [htail_rev]
              ring
        _ = dilation_head_square_profile X ⟨p - 1 - j, hrev⟩ := by
              simp [dilation_head_square_profile]
    have hz_eq' :
        z ⟨m + n - p + j, hjmn⟩ = dilation_head_square_profile X ⟨p - 1 - j, hrev⟩ := by
      simpa [tail] using hz_eq
    rw [show f (m + n - p + j) =
        Polynomial.X - Polynomial.C (z ⟨m + n - p + j, hjmn⟩) by
          simp [f, hjmn]]
    rw [show g (p - 1 - j) =
        Polynomial.X - Polynomial.C (dilation_head_square_profile X ⟨p - 1 - j, hrev⟩) by
          simp [g, hrev]]
    rw [hz_eq']
  have hg_charpoly :
      Finset.prod (Finset.range p) g =
        Matrix.charpoly (Matrix.diagonal (dilation_head_square_profile X)) := by
    -- Reassemble the reflected head product back into the diagonal characteristic polynomial.
    calc
      Finset.prod (Finset.range p) g = ∏ i : Fin p, g i := by
            symm
            exact Fin.prod_univ_eq_prod_range g p
      _ = ∏ i : Fin p,
            (Polynomial.X - Polynomial.C (dilation_head_square_profile X i)) := by
            apply Finset.prod_congr rfl
            intro i hi
            simp [g]
      _ = Matrix.charpoly (Matrix.diagonal (dilation_head_square_profile X)) := by
            symm
            simpa using Matrix.charpoly_diagonal (dilation_head_square_profile X)
  -- Reflect the shifted tail and read the resulting product as the head diagonal charpoly.
  calc
    Finset.prod (Finset.Ico (m + n - p) (m + n)) f
      = Finset.prod (Finset.range p) (fun j ↦ f (m + n - p + j)) := hshift
    _ = Finset.prod (Finset.range p) (fun j ↦ g (p - 1 - j)) := hreflect
    _ = Finset.prod (Finset.range p) g := by
          exact Finset.prod_range_reflect g p
    _ = Matrix.charpoly (Matrix.diagonal (dilation_head_square_profile X)) := hg_charpoly

/-- Helper for Theorem 7.4: the diagonal matrix of the squared ordered dilation spectrum should
match the duplicated head-square diagonal model. -/
lemma ordered_squared_dilation_diagonal_charpoly_eq_head_square_profile_noncircular
    (X : Matrix (Fin m) (Fin n) ℝ) :
    let A : symmetricMatrices (m + n) := symmetric_dilation_symmetricMatrix X
    let z : Fin (m + n) → ℝ := fun i ↦ (symmetric_eigenvalue_function A i) ^ (2 : ℕ)
    Matrix.charpoly (Matrix.diagonal z) =
      Matrix.charpoly (Matrix.diagonal (squared_dilation_head_square_profile X)) := by
  let A : symmetricMatrices (m + n) := symmetric_dilation_symmetricMatrix X
  let z : Fin (m + n) → ℝ := fun i ↦ (symmetric_eigenvalue_function A i) ^ (2 : ℕ)
  let p : ℕ := min m n
  let f : ℕ → Polynomial ℝ := fun j ↦
    if hj : j < m + n then
      Polynomial.X - Polynomial.C (z ⟨j, hj⟩)
    else
      1
  have hprod :
      Matrix.charpoly (Matrix.diagonal z) =
        Finset.prod (Finset.range (m + n)) f := by
    -- Rewrite the diagonal characteristic polynomial in the natural `range (m + n)` coordinates.
    calc
      Matrix.charpoly (Matrix.diagonal z)
        = ∏ i : Fin (m + n), (Polynomial.X - Polynomial.C (z i)) := by
            simpa using Matrix.charpoly_diagonal z
      _ = ∏ i : Fin (m + n), f i := by
            simp [f]
      _ = Finset.prod (Finset.range (m + n)) f := by
            simpa using (Fin.prod_univ_eq_prod_range f (m + n))
  have hhead :
      Finset.prod (Finset.range p) f =
        Matrix.charpoly (Matrix.diagonal (dilation_head_square_profile X)) := by
    -- On the positive head block, the squared ordered spectrum is exactly the head-square profile.
    calc
      Finset.prod (Finset.range p) f = ∏ i : Fin p, f i := by
            symm
            exact Fin.prod_univ_eq_prod_range f p
      _ = ∏ i : Fin p,
            (Polynomial.X - Polynomial.C (dilation_head_square_profile X i)) := by
            apply Finset.prod_congr rfl
            intro i hi
            have himn : (i : ℕ) < m + n := by
              omega
            simp [f, z, A, dilation_head_square_profile, himn]
      _ = Matrix.charpoly (Matrix.diagonal (dilation_head_square_profile X)) := by
            symm
            simpa using Matrix.charpoly_diagonal (dilation_head_square_profile X)
  have hmiddle :
      Finset.prod (Finset.Ico p (m + n - p)) f =
        Polynomial.X ^ (m + n - 2 * p) := by
    -- The middle strip is forced to zero by the rank bound, so every factor is `Polynomial.X`.
    calc
      Finset.prod (Finset.Ico p (m + n - p)) f
        = Finset.prod (Finset.Ico p (m + n - p)) (fun _ ↦ Polynomial.X) := by
            apply Finset.prod_congr rfl
            intro j hj
            have hleft : p ≤ j := (Finset.mem_Ico.mp hj).1
            have hright : j < m + n - p := (Finset.mem_Ico.mp hj).2
            have hjmn : j < m + n := by
              omega
            have hzero :
                symmetric_eigenvalue_function (symmetric_dilation_symmetricMatrix X) ⟨j, hjmn⟩ =
                  0 := by
              exact symmetric_dilation_middle_eq_zero_of_rank_bound (m := m) (n := n) X ⟨j, hjmn⟩
                (by simpa [p] using hleft) (by simpa [p] using hright)
            have hz_zero : z ⟨j, hjmn⟩ = 0 := by
              simpa [z] using congrArg (fun t : ℝ ↦ t ^ (2 : ℕ)) hzero
            simp [f, hjmn, hz_zero]
      _ = Polynomial.X ^ ((m + n - p) - p) := by
            simp
      _ = Polynomial.X ^ (m + n - 2 * p) := by
            congr 1
            simpa [p] using (show (m + n - min m n) - min m n = m + n - 2 * min m n by omega)
  have htail :
      Finset.prod (Finset.Ico (m + n - p) (m + n)) f =
        Matrix.charpoly (Matrix.diagonal (dilation_head_square_profile X)) := by
    -- The tail reflects back to the same head-square factors by reverse-neg symmetry.
    simpa [A, z, p, f] using
      ordered_squared_dilation_tail_product_reflects_head_square_profile
        (m := m) (n := n) X
  have hp_tail : p ≤ m + n - p := by
    omega
  have hp_top : m + n - p ≤ m + n := by
    omega
  -- Assemble the head, middle, and reflected tail products and match the known duplicated model.
  calc
    Matrix.charpoly (Matrix.diagonal z)
      = Finset.prod (Finset.range p) f *
          Finset.prod (Finset.Ico p (m + n - p)) f *
          Finset.prod (Finset.Ico (m + n - p) (m + n)) f := by
            rw [hprod]
            calc
              Finset.prod (Finset.range (m + n)) f
                = Finset.prod (Finset.range p) f * Finset.prod (Finset.Ico p (m + n)) f := by
                    symm
                    exact Finset.prod_range_mul_prod_Ico f (by omega)
              _ = Finset.prod (Finset.range p) f *
                    (Finset.prod (Finset.Ico p (m + n - p)) f *
                      Finset.prod (Finset.Ico (m + n - p) (m + n)) f) := by
                    rw [← Finset.prod_Ico_consecutive f hp_tail hp_top]
              _ = Finset.prod (Finset.range p) f *
                    Finset.prod (Finset.Ico p (m + n - p)) f *
                    Finset.prod (Finset.Ico (m + n - p) (m + n)) f := by
                    ring
    _ = Matrix.charpoly (Matrix.diagonal (dilation_head_square_profile X)) *
          Polynomial.X ^ (m + n - 2 * p) *
          Matrix.charpoly (Matrix.diagonal (dilation_head_square_profile X)) := by
            rw [hhead, hmiddle, htail]
    _ = Polynomial.X ^ (m + n - 2 * p) *
          (Matrix.charpoly (Matrix.diagonal (dilation_head_square_profile X))) ^ 2 := by
            simp [pow_two, mul_assoc, mul_left_comm, mul_comm]
    _ = Matrix.charpoly (Matrix.diagonal (squared_dilation_head_square_profile X)) := by
            symm
            simpa [p] using squared_dilation_head_square_profile_charpoly (m := m) (n := n) X

/-- Helper for Theorem 7.4: the ordered spectrum of the squared dilation should be the duplicated
square profile built from the positive head of the ordered dilation spectrum. -/
lemma squared_dilation_ordered_spectrum_eq_duplicated_head_square_profile
    (X : Matrix (Fin m) (Fin n) ℝ) :
    symmetric_eigenvalue_function (symmetric_dilation_square_symmetricMatrix X) =
      squared_dilation_head_square_profile X :=
by
  let A : symmetricMatrices (m + n) := symmetric_dilation_symmetricMatrix X
  let z : Fin (m + n) → ℝ := fun i ↦ (symmetric_eigenvalue_function A i) ^ (2 : ℕ)
  have hsquare_charpoly :
      Matrix.charpoly (symmetric_dilation X * symmetric_dilation X) =
        Matrix.charpoly (Matrix.diagonal z) := by
    -- This helper isolates the already-closed square-diagonalization part of the argument.
    simpa [A, z] using
      symmetric_dilation_square_charpoly_eq_squared_ordered_diagonal
        (m := m) (n := n) X
  let D : symmetricMatrices (m + n) :=
    ⟨Matrix.diagonal (squared_dilation_head_square_profile X),
      diagonal_mem_symmetricMatrices (squared_dilation_head_square_profile X)⟩
  have hchar :
      Matrix.charpoly (symmetric_dilation X * symmetric_dilation X) =
        Matrix.charpoly ((D : symmetricMatrices (m + n)) :
          Matrix (Fin (m + n)) (Fin (m + n)) ℝ) := by
    -- First identify the squared dilation with the ordered diagonal square model, then replace
    -- that diagonal model by the duplicated head-square diagonal.
    calc
      Matrix.charpoly (symmetric_dilation X * symmetric_dilation X)
        = Matrix.charpoly (Matrix.diagonal z) := hsquare_charpoly
      _ = Matrix.charpoly (Matrix.diagonal (squared_dilation_head_square_profile X)) := by
            simpa [A, z] using
              ordered_squared_dilation_diagonal_charpoly_eq_head_square_profile_noncircular
                (m := m) (n := n) X
      _ = Matrix.charpoly ((D : symmetricMatrices (m + n)) :
            Matrix (Fin (m + n)) (Fin (m + n)) ℝ) := by
            rfl
  have heig :
      symmetric_eigenvalue_function (symmetric_dilation_square_symmetricMatrix X) =
        symmetric_eigenvalue_function D :=
    symmetric_eigenvalue_function_eq_of_charpoly_eq
      (symmetric_dilation_square_symmetricMatrix X) D hchar
  -- The duplicated head-square diagonal is already antitone, so its ordered spectrum is read off
  -- directly from the diagonal entries.
  calc
    symmetric_eigenvalue_function (symmetric_dilation_square_symmetricMatrix X)
      = symmetric_eigenvalue_function D := heig
    _ = squared_dilation_head_square_profile X := by
          simpa [D] using
            diagonal_symmetric_eigenvalue_function_eq_of_antitone
              (squared_dilation_head_square_profile X)
              (squared_dilation_head_square_profile_antitone X)

/-- Helper for Theorem 7.4: on the positive head of the ordered dilation spectrum, the squares of
the ordered eigenvalues should match the squared singular values of the original rectangular
matrix. -/
lemma symmetric_dilation_head_sq_eq_singular_value_sq
    (X : Matrix (Fin m) (Fin n) ℝ) (i : Fin (min m n)) :
    (symmetric_eigenvalue_function (symmetric_dilation_symmetricMatrix X)
      ⟨i.1, by
        omega⟩) ^ (2 : ℕ) =
      (singular_value_function X i) ^ (2 : ℕ) := by
  let j : Fin (m + n) := ⟨2 * i.1, by
    omega⟩
  have hj_head_nat : 2 * i.1 < 2 * min m n := by
    omega
  have hj_head : j.1 < 2 * min m n := by
    simpa [j] using hj_head_nat
  have hordered :
      symmetric_eigenvalue_function (symmetric_dilation_square_symmetricMatrix X) j =
        (symmetric_eigenvalue_function (symmetric_dilation_symmetricMatrix X)
          ⟨i.1, by
            omega⟩) ^ (2 : ℕ) := by
    -- Evaluate the missing ordered-spectrum bridge at the even coordinate `2 * i`.
    simpa [j, squared_dilation_head_square_profile, hj_head] using
      congrFun
        (squared_dilation_ordered_spectrum_eq_duplicated_head_square_profile
          (m := m) (n := n) X) j
  have hprofile :
      symmetric_eigenvalue_function (symmetric_dilation_square_symmetricMatrix X) j =
        (singular_value_function X i) ^ (2 : ℕ) := by
    -- The already-closed square-spectrum API gives the same even coordinate as the squared
    -- singular value.
    simpa [j, symmetric_dilation_square_profile, hj_head] using
      congrFun
        (symmetric_dilation_square_symmetric_eigenvalue_function_eq_duplicated_square_profile
          (m := m) (n := n) X) j
  -- Compare the even coordinate of the ordered squared-dilation spectrum in the two available
  -- descriptions: first via the ordered dilation head, and second via the singular-value square
  -- profile.
  calc
    (symmetric_eigenvalue_function (symmetric_dilation_symmetricMatrix X)
      ⟨i.1, by
        omega⟩) ^ (2 : ℕ)
      = symmetric_eigenvalue_function (symmetric_dilation_square_symmetricMatrix X) j := by
          exact hordered.symm
    _ = (singular_value_function X i) ^ (2 : ℕ) := by
          exact hprofile

/-- Helper for Theorem 7.4: squaring the ordered head of the dilation spectrum gives the
factorization of the squared-dilation characteristic polynomial coming from that head. -/
lemma symmetric_dilation_square_charpoly_eq_head_square_profile
    (X : Matrix (Fin m) (Fin n) ℝ) :
    let p : ℕ := min m n
    let x : Fin p → ℝ := fun i ↦
      (symmetric_eigenvalue_function (symmetric_dilation_symmetricMatrix X) ⟨i.1, by
        omega⟩) ^ (2 : ℕ)
    Matrix.charpoly (symmetric_dilation X * symmetric_dilation X) =
      Polynomial.X ^ (m + n - 2 * p) * (Matrix.charpoly (Matrix.diagonal x)) ^ 2 := by
  dsimp
  set x : Fin (min m n) → ℝ := fun i ↦
    (symmetric_eigenvalue_function (symmetric_dilation_symmetricMatrix X) ⟨i.1, by
      omega⟩) ^ (2 : ℕ) with hxdef
  change
    Matrix.charpoly (symmetric_dilation X * symmetric_dilation X) =
      Polynomial.X ^ (m + n - 2 * min m n) * (Matrix.charpoly (Matrix.diagonal x)) ^ 2
  have hsquare_charpoly :
      Matrix.charpoly (symmetric_dilation X * symmetric_dilation X) =
        Polynomial.X ^ (m + n - 2 * min m n) *
          ∏ i : Fin (min m n),
            (Polynomial.X - Polynomial.C ((singular_value_function X i) ^ (2 : ℕ) : ℝ)) ^ 2 := by
    have hdiag_charpoly :
        Matrix.charpoly (symmetric_dilation X * symmetric_dilation X) =
          Matrix.charpoly (Matrix.diagonal (symmetric_dilation_square_profile X)) := by
      let A : symmetricMatrices (m + n) := symmetric_dilation_square_symmetricMatrix X
      obtain ⟨Q, hQ⟩ :=
        exists_orthogonal_diagonalization_with_symmetric_eigenvalue_function A
      have hQQ :
          ((Q : Matrix (Fin (m + n)) (Fin (m + n)) ℝ)ᵀ) *
              (Q : Matrix (Fin (m + n)) (Fin (m + n)) ℝ) = 1 :=
        (Matrix.mem_orthogonalGroup_iff' (A := (Q : Matrix (Fin (m + n)) (Fin (m + n)) ℝ))
          (R := ℝ)).1 Q.2
      -- Compare the squared dilation with its ordered orthogonal diagonal model.
      calc
        Matrix.charpoly (symmetric_dilation X * symmetric_dilation X)
          = Matrix.charpoly (((A : symmetricMatrices (m + n)) :
              Matrix (Fin (m + n)) (Fin (m + n)) ℝ)) := by
                rfl
        _ = Matrix.charpoly
              ((Q : Matrix (Fin (m + n)) (Fin (m + n)) ℝ) *
                Matrix.diagonal (symmetric_eigenvalue_function A) *
                ((Q : Matrix (Fin (m + n)) (Fin (m + n)) ℝ)ᵀ)) := by
                rw [hQ]
        _ = Matrix.charpoly (Matrix.diagonal (symmetric_eigenvalue_function A)) := by
              exact
                orthogonal_conjugate_charpoly
                  (U := (Q : Matrix (Fin (m + n)) (Fin (m + n)) ℝ))
                  (A := Matrix.diagonal (symmetric_eigenvalue_function A)) hQQ
        _ = Matrix.charpoly (Matrix.diagonal (symmetric_dilation_square_profile X)) := by
              rw [symmetric_dilation_square_symmetric_eigenvalue_function_eq_duplicated_square_profile]
    -- Reuse the already closed diagonal-model characteristic-polynomial computation.
    calc
      Matrix.charpoly (symmetric_dilation X * symmetric_dilation X)
        = Matrix.charpoly (Matrix.diagonal (symmetric_dilation_square_profile X)) := hdiag_charpoly
      _ = Polynomial.X ^ (m + n - 2 * min m n) *
            ∏ i : Fin (min m n),
              (Polynomial.X - Polynomial.C ((singular_value_function X i) ^ (2 : ℕ) : ℝ)) ^ 2 := by
            exact symmetric_dilation_square_profile_charpoly X
  have hx :
      x = fun i : Fin (min m n) ↦ (singular_value_function X i) ^ (2 : ℕ) := by
    ext i
    -- The remaining spectral input is exactly the head-square bridge.
    rw [hxdef]
    simpa using symmetric_dilation_head_sq_eq_singular_value_sq (m := m) (n := n) X i
  have hdiag_sq :
      (Matrix.charpoly (Matrix.diagonal x)) ^ 2 =
        ∏ i : Fin (min m n),
          (Polynomial.X - Polynomial.C (x i : ℝ)) ^ 2 := by
    rw [Matrix.charpoly_diagonal, pow_two]
    calc
      (∏ i : Fin (min m n), (Polynomial.X - Polynomial.C (x i : ℝ))) *
          ∏ i : Fin (min m n), (Polynomial.X - Polynomial.C (x i : ℝ))
        = ∏ i : Fin (min m n),
            ((Polynomial.X - Polynomial.C (x i : ℝ)) *
              (Polynomial.X - Polynomial.C (x i : ℝ))) := by
              rw [← Finset.prod_mul_distrib]
      _ = ∏ i : Fin (min m n),
            (Polynomial.X - Polynomial.C (x i : ℝ)) ^ 2 := by
            apply Finset.prod_congr rfl
            intro i hi
            simp [pow_two]
  -- After substituting the head-square identification, the diagonal factors are identical.
  calc
    Matrix.charpoly (symmetric_dilation X * symmetric_dilation X)
      = Polynomial.X ^ (m + n - 2 * min m n) *
          ∏ i : Fin (min m n),
            (Polynomial.X - Polynomial.C ((singular_value_function X i) ^ (2 : ℕ) : ℝ)) ^ 2 :=
          hsquare_charpoly
    _ = Polynomial.X ^ (m + n - 2 * min m n) *
          ∏ i : Fin (min m n),
            (Polynomial.X - Polynomial.C (x i : ℝ)) ^ 2 := by
          congr 1
          apply Finset.prod_congr rfl
          intro i hi
          simp [hx]
    _ = Polynomial.X ^ (m + n - 2 * min m n) *
          (Matrix.charpoly (Matrix.diagonal x)) ^ 2 := by
          rw [hdiag_sq]

/-- Helper for Theorem 7.4: once the head-square comparison is known, the nonnegative head of the
ordered dilation spectrum agrees pointwise with the singular-value list. -/
lemma symmetric_dilation_head_eq_singular_value
    (X : Matrix (Fin m) (Fin n) ℝ) (i : Fin (m + n)) (hi : i.1 < min m n) :
    symmetric_eigenvalue_function (symmetric_dilation_symmetricMatrix X) i =
      singular_value_function X ⟨i.1, hi⟩ := by
  have hsquare :
      (symmetric_eigenvalue_function (symmetric_dilation_symmetricMatrix X) i) ^ (2 : ℕ) =
        (singular_value_function X ⟨i.1, hi⟩) ^ (2 : ℕ) := by
    simpa using
      symmetric_dilation_head_sq_eq_singular_value_sq (m := m) (n := n) X ⟨i.1, hi⟩
  have hnonneg_head :
      0 ≤ symmetric_eigenvalue_function (symmetric_dilation_symmetricMatrix X) i :=
    symmetric_dilation_head_nonneg (m := m) (n := n) X i hi
  have hnonneg_sv : 0 ≤ singular_value_function X ⟨i.1, hi⟩ :=
    singular_value_function_nonneg X ⟨i.1, hi⟩
  -- Both sides are nonnegative, so equality of squares upgrades to equality.
  nlinarith

/-- Helper for Theorem 7.4: the middle coordinates of the ordered dilation spectrum should vanish,
matching the kernel block created by the size mismatch between `m` and `n`. -/
-- TODO: use the total square-mass identity together with the head-square comparison and the
-- reverse-neg symmetry to show that the middle strip carries no square mass.
lemma symmetric_dilation_middle_eq_zero
    (X : Matrix (Fin m) (Fin n) ℝ) (i : Fin (m + n))
    (hleft : min m n ≤ i.1) (hright : i.1 < m + n - min m n) :
    symmetric_eigenvalue_function (symmetric_dilation_symmetricMatrix X) i = 0 := by
  -- Route correction: the middle-zero statement is now deduced from the rank bound on the
  -- symmetric dilation, avoiding the earlier circular dependence on the head-square bridge.
  exact symmetric_dilation_middle_eq_zero_of_rank_bound (m := m) (n := n) X i hleft hright

/-- Helper for Theorem 7.4: the negative tail of the ordered dilation spectrum is the reversed
negative singular-value list. -/
lemma symmetric_dilation_tail_eq_neg_singular_value
    (X : Matrix (Fin m) (Fin n) ℝ) (i : Fin (m + n))
    (hi : m + n - min m n ≤ i.1) :
    symmetric_eigenvalue_function (symmetric_dilation_symmetricMatrix X) i =
      -singular_value_function X (signed_singular_value_profile_tailIndex i hi) := by
  have hrev_head : i.rev.1 < min m n := by
    simp [Fin.rev]
    omega
  have hsymm :
      symmetric_eigenvalue_function (symmetric_dilation_symmetricMatrix X) i =
        -symmetric_eigenvalue_function (symmetric_dilation_symmetricMatrix X) i.rev := by
    -- Evaluate the reverse-neg symmetry at `i` to relate the tail entry to its reflected head
    -- partner.
    have hx_symm :=
      congrFun (symmetric_dilation_spectrum_eq_reverse_neg (m := m) (n := n) X) i
    simpa [reverse_neg] using hx_symm
  have hhead :
      symmetric_eigenvalue_function (symmetric_dilation_symmetricMatrix X) i.rev =
        singular_value_function X ⟨i.rev.1, hrev_head⟩ :=
    symmetric_dilation_head_eq_singular_value (m := m) (n := n) X i.rev hrev_head
  have htailIndex :
      (⟨i.rev.1, hrev_head⟩ : Fin (min m n)) =
        signed_singular_value_profile_tailIndex i hi := by
    ext
    simp [signed_singular_value_profile_tailIndex, Fin.rev]
    omega
  -- Replace the reflected head coordinate by the corresponding singular-value index.
  calc
    symmetric_eigenvalue_function (symmetric_dilation_symmetricMatrix X) i
      = -symmetric_eigenvalue_function (symmetric_dilation_symmetricMatrix X) i.rev := hsymm
    _ = -singular_value_function X ⟨i.rev.1, hrev_head⟩ := by
          rw [hhead]
    _ = -singular_value_function X (signed_singular_value_profile_tailIndex i hi) := by
          rw [htailIndex]

/-- Helper for Theorem 7.4: the ordered dilation spectrum should agree with the signed
singular-value profile. -/
lemma symmetric_dilation_symmetric_eigenvalue_function_eq_signed_singular_value_profile
    (X : Matrix (Fin m) (Fin n) ℝ) :
    symmetric_eigenvalue_function (symmetric_dilation_symmetricMatrix X) =
      signed_singular_value_profile X := by
  ext i
  by_cases hhead : i.1 < min m n
  · -- On the positive head, the square-spectrum bridge and nonnegativity recover the singular
    -- values themselves.
    rw [signed_singular_value_profile_head X i hhead]
    exact symmetric_dilation_head_eq_singular_value (m := m) (n := n) X i hhead
  · have hleft : min m n ≤ i.1 := by
      omega
    by_cases htail : m + n - min m n ≤ i.1
    · -- On the tail, the reverse-neg symmetry reflects the head computation.
      rw [signed_singular_value_profile_tail X i htail]
      exact symmetric_dilation_tail_eq_neg_singular_value (m := m) (n := n) X i htail
    · have hmiddle : i.1 < m + n - min m n := by
        omega
      -- The remaining middle block is forced to be zero by the square-mass decomposition.
      rw [signed_singular_value_profile_middle X i hleft hmiddle]
      exact symmetric_dilation_middle_eq_zero (m := m) (n := n) X i hleft hmiddle

/-- Helper for Theorem 7.4: the signed-profile pairing is exactly twice the pairing of the
rectangular singular-value vectors. -/
lemma dotProduct_signed_singular_value_profile_eq_two_dotProduct_singular_values
    (X Y : Matrix (Fin m) (Fin n) ℝ) :
    dotProduct (signed_singular_value_profile X) (signed_singular_value_profile Y) =
      2 * dotProduct (singular_value_function X) (singular_value_function Y) := by
  let p : ℕ := min m n
  let f : ℕ → ℝ := fun j ↦
    if hj : j < m + n then
      signed_singular_value_profile X ⟨j, hj⟩ * signed_singular_value_profile Y ⟨j, hj⟩
    else
      0
  let g : ℕ → ℝ := fun j ↦
    if hj : j < p then
      singular_value_function X ⟨j, hj⟩ * singular_value_function Y ⟨j, hj⟩
    else
      0
  have hp_left : p ≤ m := Nat.min_le_left _ _
  have hp_right : p ≤ n := Nat.min_le_right _ _
  have hp_tail : p ≤ m + n - p := by
    omega
  have hp_top : m + n - p ≤ m + n := by
    omega
  have hdot :
      (∑ j ∈ Finset.range p, g j) =
        dotProduct (singular_value_function X) (singular_value_function Y) := by
    -- The head block is exactly the singular-value dot product.
    calc
      (∑ j ∈ Finset.range p, g j)
        = ∑ i : Fin p, singular_value_function X i * singular_value_function Y i := by
            rw [← Fin.sum_univ_eq_sum_range]
            apply Finset.sum_congr rfl
            intro i hi
            have hi' : (i : ℕ) < p := i.2
            simp [g, hi']
      _ = dotProduct (singular_value_function X) (singular_value_function Y) := by
            rfl
  have hhead :
      (∑ j ∈ Finset.range p, f j) =
        dotProduct (singular_value_function X) (singular_value_function Y) := by
    -- On the positive head block, the signed profile agrees with the singular-value function.
    calc
      (∑ j ∈ Finset.range p, f j) = ∑ j ∈ Finset.range p, g j := by
        apply Finset.sum_congr rfl
        intro j hj
        have hjp : j < p := Finset.mem_range.mp hj
        have hjmn : j < m + n := by omega
        rw [show f j =
            signed_singular_value_profile X ⟨j, hjmn⟩ *
              signed_singular_value_profile Y ⟨j, hjmn⟩ by
              simp [f, hjmn]]
        rw [show g j =
            singular_value_function X ⟨j, hjp⟩ *
              singular_value_function Y ⟨j, hjp⟩ by
              simp [g, hjp]]
        rw [signed_singular_value_profile_head X ⟨j, hjmn⟩ (by simpa [p] using hjp),
          signed_singular_value_profile_head Y ⟨j, hjmn⟩ (by simpa [p] using hjp)]
      _ = dotProduct (singular_value_function X) (singular_value_function Y) := hdot
  have hmiddle :
      (∑ j ∈ Finset.Ico p (m + n - p), f j) = 0 := by
    -- The middle block vanishes for both signed profiles.
    apply Finset.sum_eq_zero
    intro j hj
    have hj_left : p ≤ j := (Finset.mem_Ico.mp hj).1
    have hj_right : j < m + n - p := (Finset.mem_Ico.mp hj).2
    have hjmn : j < m + n := by omega
    simp [f, hjmn, signed_singular_value_profile_middle,
      (show min m n ≤ j by simpa [p] using hj_left), (show j < m + n - min m n by simpa [p] using hj_right)]
  have htail_shift :
      (∑ j ∈ Finset.Ico (m + n - p) (m + n), f j) =
        ∑ j ∈ Finset.range p, g (p - 1 - j) := by
    -- Shift the tail interval down to `range p`, then rewrite each reflected tail term.
    rw [Finset.sum_Ico_eq_sum_range]
    have hrange : m + n - (m + n - p) = p := by omega
    rw [hrange]
    apply Finset.sum_congr rfl
    intro j hj
    have hjp : j < p := Finset.mem_range.mp hj
    have hjmn : m + n - p + j < m + n := by omega
    have hjtail : m + n - p ≤ m + n - p + j := by omega
    have hidx :
        signed_singular_value_profile_tailIndex ⟨m + n - p + j, hjmn⟩ hjtail =
          ⟨p - 1 - j, by omega⟩ := by
      ext
      simp [signed_singular_value_profile_tailIndex]
      omega
    have hrev : p - 1 - j < p := by omega
    rw [show f (m + n - p + j) =
        signed_singular_value_profile X ⟨m + n - p + j, hjmn⟩ *
          signed_singular_value_profile Y ⟨m + n - p + j, hjmn⟩ by
          simp [f, hjmn]]
    rw [show g (p - 1 - j) =
        singular_value_function X ⟨p - 1 - j, hrev⟩ *
          singular_value_function Y ⟨p - 1 - j, hrev⟩ by
          simp [g, hrev]]
    rw [signed_singular_value_profile_tail X ⟨m + n - p + j, hjmn⟩ hjtail,
      signed_singular_value_profile_tail Y ⟨m + n - p + j, hjmn⟩ hjtail]
    have htail_product (hx hy : p - 1 - j < p) :
        -singular_value_function X ⟨p - 1 - j, hx⟩ *
            -singular_value_function Y ⟨p - 1 - j, hy⟩ =
          singular_value_function X ⟨p - 1 - j, hrev⟩ *
            singular_value_function Y ⟨p - 1 - j, hrev⟩ := by
      have hX :
          singular_value_function X ⟨p - 1 - j, hx⟩ =
            singular_value_function X ⟨p - 1 - j, hrev⟩ := by
        congr
      have hY :
          singular_value_function Y ⟨p - 1 - j, hy⟩ =
            singular_value_function Y ⟨p - 1 - j, hrev⟩ := by
        congr
      rw [hX, hY]
      ring
    have hidx' :
        signed_singular_value_profile_tailIndex ⟨m + n - p + j, hjmn⟩ hjtail =
          ⟨p - 1 - j, hrev⟩ := by
      ext
      simp [signed_singular_value_profile_tailIndex]
      omega
    rw [hidx']
    exact htail_product hrev hrev
  have htail :
      (∑ j ∈ Finset.Ico (m + n - p) (m + n), f j) =
        dotProduct (singular_value_function X) (singular_value_function Y) := by
    -- Reflecting the tail reverses the singular-value order but leaves the head sum unchanged.
    calc
      (∑ j ∈ Finset.Ico (m + n - p) (m + n), f j)
        = ∑ j ∈ Finset.range p, g (p - 1 - j) := htail_shift
      _ = ∑ j ∈ Finset.range p, g j := by
            exact Finset.sum_range_reflect g p
      _ = dotProduct (singular_value_function X) (singular_value_function Y) := hdot
  -- Assemble the head, middle, and tail blocks.
  calc
    dotProduct (signed_singular_value_profile X) (signed_singular_value_profile Y)
      = ∑ j ∈ Finset.range (m + n), f j := by
          calc
            dotProduct (signed_singular_value_profile X) (signed_singular_value_profile Y)
              = ∑ i : Fin (m + n), f i := by
                  simp [dotProduct, f]
            _ = ∑ j ∈ Finset.range (m + n), f j := by
                  exact Fin.sum_univ_eq_sum_range f (m + n)
    _ = (∑ j ∈ Finset.range p, f j) +
          (∑ j ∈ Finset.Ico p (m + n - p), f j) +
          (∑ j ∈ Finset.Ico (m + n - p) (m + n), f j) := by
            calc
              ∑ j ∈ Finset.range (m + n), f j
                = (∑ j ∈ Finset.range p, f j) + ∑ j ∈ Finset.Ico p (m + n), f j := by
                    symm
                    exact Finset.sum_range_add_sum_Ico f (by omega)
              _ = (∑ j ∈ Finset.range p, f j) +
                    ((∑ j ∈ Finset.Ico p (m + n - p), f j) +
                      ∑ j ∈ Finset.Ico (m + n - p) (m + n), f j) := by
                    rw [← Finset.sum_Ico_consecutive f hp_tail hp_top]
              _ = (∑ j ∈ Finset.range p, f j) +
                    (∑ j ∈ Finset.Ico p (m + n - p), f j) +
                    (∑ j ∈ Finset.Ico (m + n - p) (m + n), f j) := by
                    ring
    _ = dotProduct (singular_value_function X) (singular_value_function Y) +
          0 +
          dotProduct (singular_value_function X) (singular_value_function Y) := by
            rw [hhead, hmiddle, htail]
    _ = 2 * dotProduct (singular_value_function X) (singular_value_function Y) := by
          ring

/-- Helper for Theorem 7.4: equality in Fan's inequality for the dilations yields a common
orthogonal diagonalization with the ordered dilation eigenvalue coordinates on the diagonal. -/
lemma dilation_fan_equality_implies_common_ordered_diagonalization
    (X Y : Matrix (Fin m) (Fin n) ℝ)
    (hEq :
      Matrix.trace
          (((symmetric_dilation_symmetricMatrix X : symmetricMatrices (m + n)) :
              Matrix (Fin (m + n)) (Fin (m + n)) ℝ) *
            ((symmetric_dilation_symmetricMatrix Y : symmetricMatrices (m + n)) :
              Matrix (Fin (m + n)) (Fin (m + n)) ℝ)) =
        dotProduct
          (symmetric_eigenvalue_function (symmetric_dilation_symmetricMatrix X))
          (symmetric_eigenvalue_function (symmetric_dilation_symmetricMatrix Y))) :
    ∃ Q : Matrix.orthogonalGroup (Fin (m + n)) ℝ,
      (symmetric_dilation X : Matrix (Fin (m + n)) (Fin (m + n)) ℝ) =
        (Q : Matrix (Fin (m + n)) (Fin (m + n)) ℝ) *
          Matrix.diagonal (signed_singular_value_profile X) *
          ((Q : Matrix (Fin (m + n)) (Fin (m + n)) ℝ)ᵀ) ∧
      (symmetric_dilation Y : Matrix (Fin (m + n)) (Fin (m + n)) ℝ) =
        (Q : Matrix (Fin (m + n)) (Fin (m + n)) ℝ) *
          Matrix.diagonal (signed_singular_value_profile Y) *
          ((Q : Matrix (Fin (m + n)) (Fin (m + n)) ℝ)ᵀ) := by
  let dX : symmetricMatrices (m + n) := symmetric_dilation_symmetricMatrix X
  let dY : symmetricMatrices (m + n) := symmetric_dilation_symmetricMatrix Y
  obtain ⟨σ, hσ⟩ := exists_eigenvalue_reindex_perm (n := m + n)
  have hEq' :
      Matrix.trace
          (((dX : symmetricMatrices (m + n)) : Matrix (Fin (m + n)) (Fin (m + n)) ℝ) *
            ((dY : symmetricMatrices (m + n)) : Matrix (Fin (m + n)) (Fin (m + n)) ℝ)) =
        dotProduct dX.property.isHermitian.eigenvalues dY.property.isHermitian.eigenvalues := by
    calc
      Matrix.trace
          (((dX : symmetricMatrices (m + n)) : Matrix (Fin (m + n)) (Fin (m + n)) ℝ) *
            ((dY : symmetricMatrices (m + n)) : Matrix (Fin (m + n)) (Fin (m + n)) ℝ))
        = dotProduct (symmetric_eigenvalue_function dX) (symmetric_eigenvalue_function dY) := hEq
      _ = dotProduct (dX.property.isHermitian.eigenvalues) (dY.property.isHermitian.eigenvalues) := by
            rw [hσ dX, hσ dY]
            symm
            exact dotProduct_comp_perm σ
              (symmetric_eigenvalue_function dX) (symmetric_eigenvalue_function dY)
  rcases (fan_inequality_trace_eq_iff_exists_orthogonal_diagonalization dX dY).1 hEq' with
    ⟨V, hVx, hVy⟩
  let P : Matrix.orthogonalGroup (Fin (m + n)) ℝ := permutationOrthogonalMatrix σ
  refine ⟨V * P, ?_, ?_⟩
  · -- Conjugate the theorem-coordinate diagonalization by the fixed permutation to move from
    -- `eigenvalues` to the ordered `symmetric_eigenvalue_function`, then rewrite by the profile.
    calc
      (symmetric_dilation X : Matrix (Fin (m + n)) (Fin (m + n)) ℝ)
        = (V : Matrix (Fin (m + n)) (Fin (m + n)) ℝ) *
            Matrix.diagonal dX.property.isHermitian.eigenvalues *
            ((V : Matrix (Fin (m + n)) (Fin (m + n)) ℝ)ᵀ) := by
              simpa [dX] using hVx
      _ = (V : Matrix (Fin (m + n)) (Fin (m + n)) ℝ) *
            (((P : Matrix.orthogonalGroup (Fin (m + n)) ℝ) : Matrix (Fin (m + n)) (Fin (m + n)) ℝ) *
              Matrix.diagonal (symmetric_eigenvalue_function dX) *
              (((P : Matrix (Fin (m + n)) (Fin (m + n)) ℝ))ᵀ)) *
            ((V : Matrix (Fin (m + n)) (Fin (m + n)) ℝ)ᵀ) := by
              rw [hσ dX, diagonal_comp_perm_eq_orthogonal_conjugate σ
                (symmetric_eigenvalue_function dX)]
      _ = ((V * P : Matrix.orthogonalGroup (Fin (m + n)) ℝ) :
            Matrix (Fin (m + n)) (Fin (m + n)) ℝ) *
            Matrix.diagonal (symmetric_eigenvalue_function dX) *
            ((((V * P : Matrix.orthogonalGroup (Fin (m + n)) ℝ) :
                Matrix (Fin (m + n)) (Fin (m + n)) ℝ))ᵀ) := by
              simp [P, Matrix.mul_assoc, Matrix.transpose_mul]
      _ = ((V * P : Matrix.orthogonalGroup (Fin (m + n)) ℝ) :
            Matrix (Fin (m + n)) (Fin (m + n)) ℝ) *
            Matrix.diagonal (signed_singular_value_profile X) *
            ((((V * P : Matrix.orthogonalGroup (Fin (m + n)) ℝ) :
                Matrix (Fin (m + n)) (Fin (m + n)) ℝ))ᵀ) := by
              rw [symmetric_dilation_symmetric_eigenvalue_function_eq_signed_singular_value_profile X]
  · -- The same fixed permutation transport works for the second dilation.
    calc
      (symmetric_dilation Y : Matrix (Fin (m + n)) (Fin (m + n)) ℝ)
        = (V : Matrix (Fin (m + n)) (Fin (m + n)) ℝ) *
            Matrix.diagonal dY.property.isHermitian.eigenvalues *
            ((V : Matrix (Fin (m + n)) (Fin (m + n)) ℝ)ᵀ) := by
              simpa [dY] using hVy
      _ = (V : Matrix (Fin (m + n)) (Fin (m + n)) ℝ) *
            (((P : Matrix.orthogonalGroup (Fin (m + n)) ℝ) : Matrix (Fin (m + n)) (Fin (m + n)) ℝ) *
              Matrix.diagonal (symmetric_eigenvalue_function dY) *
              (((P : Matrix (Fin (m + n)) (Fin (m + n)) ℝ))ᵀ)) *
            ((V : Matrix (Fin (m + n)) (Fin (m + n)) ℝ)ᵀ) := by
              rw [hσ dY, diagonal_comp_perm_eq_orthogonal_conjugate σ
                (symmetric_eigenvalue_function dY)]
      _ = ((V * P : Matrix.orthogonalGroup (Fin (m + n)) ℝ) :
            Matrix (Fin (m + n)) (Fin (m + n)) ℝ) *
            Matrix.diagonal (symmetric_eigenvalue_function dY) *
            ((((V * P : Matrix.orthogonalGroup (Fin (m + n)) ℝ) :
                Matrix (Fin (m + n)) (Fin (m + n)) ℝ))ᵀ) := by
              simp [P, Matrix.mul_assoc, Matrix.transpose_mul]
      _ = ((V * P : Matrix.orthogonalGroup (Fin (m + n)) ℝ) :
            Matrix (Fin (m + n)) (Fin (m + n)) ℝ) *
            Matrix.diagonal (signed_singular_value_profile Y) *
            ((((V * P : Matrix.orthogonalGroup (Fin (m + n)) ℝ) :
                Matrix (Fin (m + n)) (Fin (m + n)) ℝ))ᵀ) := by
              rw [symmetric_dilation_symmetric_eigenvalue_function_eq_signed_singular_value_profile Y]

/-- Helper for Theorem 7.4: the symmetric Fan right-hand side for the two dilations is exactly
twice the rectangular singular-value dot product. -/
lemma dotProduct_symmetric_eigenvalue_function_symmetric_dilation
    (X Y : Matrix (Fin m) (Fin n) ℝ) :
    dotProduct
        (symmetric_eigenvalue_function (symmetric_dilation_symmetricMatrix X))
        (symmetric_eigenvalue_function (symmetric_dilation_symmetricMatrix Y)) =
      2 * dotProduct (singular_value_function X) (singular_value_function Y) := by
  -- Route correction: the proof is now reduced to the explicit signed-profile bookkeeping and the
  -- single remaining spectral-identification lemma for the dilation.
  rw [symmetric_dilation_symmetric_eigenvalue_function_eq_signed_singular_value_profile X,
    symmetric_dilation_symmetric_eigenvalue_function_eq_signed_singular_value_profile Y]
  exact dotProduct_signed_singular_value_profile_eq_two_dotProduct_singular_values X Y

/-- Helper for Theorem 7.4: a common ordered diagonalization of the two symmetric dilations forces
the dilations to commute. -/
lemma common_ordered_dilation_diagonalization_commute
    (X Y : Matrix (Fin m) (Fin n) ℝ)
    (Q : Matrix.orthogonalGroup (Fin (m + n)) ℝ)
    (hQX :
      (symmetric_dilation X : Matrix (Fin (m + n)) (Fin (m + n)) ℝ) =
        (Q : Matrix (Fin (m + n)) (Fin (m + n)) ℝ) *
          Matrix.diagonal (signed_singular_value_profile X) *
          ((Q : Matrix (Fin (m + n)) (Fin (m + n)) ℝ)ᵀ))
    (hQY :
      (symmetric_dilation Y : Matrix (Fin (m + n)) (Fin (m + n)) ℝ) =
        (Q : Matrix (Fin (m + n)) (Fin (m + n)) ℝ) *
          Matrix.diagonal (signed_singular_value_profile Y) *
          ((Q : Matrix (Fin (m + n)) (Fin (m + n)) ℝ)ᵀ)) :
    symmetric_dilation X * symmetric_dilation Y =
      symmetric_dilation Y * symmetric_dilation X := by
  let DX : Matrix (Fin (m + n)) (Fin (m + n)) ℝ :=
    Matrix.diagonal (signed_singular_value_profile X)
  let DY : Matrix (Fin (m + n)) (Fin (m + n)) ℝ :=
    Matrix.diagonal (signed_singular_value_profile Y)
  have hQQ :
      ((Q : Matrix (Fin (m + n)) (Fin (m + n)) ℝ)ᵀ) *
          (Q : Matrix (Fin (m + n)) (Fin (m + n)) ℝ) = 1 :=
    (Matrix.mem_orthogonalGroup_iff' (A := (Q :
        Matrix (Fin (m + n)) (Fin (m + n)) ℝ)) (R := ℝ)).1 Q.2
  have hdiagComm : DX * DY = DY * DX := by
    -- Diagonal matrices commute because their diagonal entries commute pointwise.
    calc
      DX * DY =
          Matrix.diagonal
            (fun i : Fin (m + n) ↦
              signed_singular_value_profile X i * signed_singular_value_profile Y i) := by
            simpa [DX, DY] using
              Matrix.diagonal_mul_diagonal
                (signed_singular_value_profile X) (signed_singular_value_profile Y)
      _ = Matrix.diagonal
            (fun i : Fin (m + n) ↦
              signed_singular_value_profile Y i * signed_singular_value_profile X i) := by
            simp [mul_comm]
      _ = DY * DX := by
            simpa [DX, DY] using
              (Matrix.diagonal_mul_diagonal
                (signed_singular_value_profile Y) (signed_singular_value_profile X)).symm
  have hleft :
      ((Q : Matrix (Fin (m + n)) (Fin (m + n)) ℝ) * DX * (Q : Matrix (Fin (m + n))
          (Fin (m + n)) ℝ)ᵀ) *
          ((Q : Matrix (Fin (m + n)) (Fin (m + n)) ℝ) * DY *
            (Q : Matrix (Fin (m + n)) (Fin (m + n)) ℝ)ᵀ) =
        (Q : Matrix (Fin (m + n)) (Fin (m + n)) ℝ) * (DX * DY) *
          (Q : Matrix (Fin (m + n)) (Fin (m + n)) ℝ)ᵀ := by
    -- Cancel the middle orthogonal pair and expose the commuting diagonal core.
    calc
      ((Q : Matrix (Fin (m + n)) (Fin (m + n)) ℝ) * DX * (Q : Matrix (Fin (m + n))
          (Fin (m + n)) ℝ)ᵀ) *
          ((Q : Matrix (Fin (m + n)) (Fin (m + n)) ℝ) * DY *
            (Q : Matrix (Fin (m + n)) (Fin (m + n)) ℝ)ᵀ)
        = (Q : Matrix (Fin (m + n)) (Fin (m + n)) ℝ) *
            (DX * (((Q : Matrix (Fin (m + n)) (Fin (m + n)) ℝ)ᵀ) *
              (Q : Matrix (Fin (m + n)) (Fin (m + n)) ℝ)) * DY) *
            (Q : Matrix (Fin (m + n)) (Fin (m + n)) ℝ)ᵀ := by
              simp [Matrix.mul_assoc]
      _ = (Q : Matrix (Fin (m + n)) (Fin (m + n)) ℝ) * (DX * DY) *
            (Q : Matrix (Fin (m + n)) (Fin (m + n)) ℝ)ᵀ := by
              rw [hQQ]
              simp [Matrix.mul_assoc]
  have hright :
      ((Q : Matrix (Fin (m + n)) (Fin (m + n)) ℝ) * DY * (Q : Matrix (Fin (m + n))
          (Fin (m + n)) ℝ)ᵀ) *
          ((Q : Matrix (Fin (m + n)) (Fin (m + n)) ℝ) * DX *
            (Q : Matrix (Fin (m + n)) (Fin (m + n)) ℝ)ᵀ) =
        (Q : Matrix (Fin (m + n)) (Fin (m + n)) ℝ) * (DY * DX) *
          (Q : Matrix (Fin (m + n)) (Fin (m + n)) ℝ)ᵀ := by
    -- The same cancellation works after swapping the two diagonal factors.
    calc
      ((Q : Matrix (Fin (m + n)) (Fin (m + n)) ℝ) * DY * (Q : Matrix (Fin (m + n))
          (Fin (m + n)) ℝ)ᵀ) *
          ((Q : Matrix (Fin (m + n)) (Fin (m + n)) ℝ) * DX *
            (Q : Matrix (Fin (m + n)) (Fin (m + n)) ℝ)ᵀ)
        = (Q : Matrix (Fin (m + n)) (Fin (m + n)) ℝ) *
            (DY * (((Q : Matrix (Fin (m + n)) (Fin (m + n)) ℝ)ᵀ) *
              (Q : Matrix (Fin (m + n)) (Fin (m + n)) ℝ)) * DX) *
            (Q : Matrix (Fin (m + n)) (Fin (m + n)) ℝ)ᵀ := by
              simp [Matrix.mul_assoc]
      _ = (Q : Matrix (Fin (m + n)) (Fin (m + n)) ℝ) * (DY * DX) *
            (Q : Matrix (Fin (m + n)) (Fin (m + n)) ℝ)ᵀ := by
              rw [hQQ]
              simp [Matrix.mul_assoc]
  -- Rewrite both dilations in the common ordered diagonal basis and commute the diagonal core.
  calc
    symmetric_dilation X * symmetric_dilation Y
      = ((Q : Matrix (Fin (m + n)) (Fin (m + n)) ℝ) *
          DX *
          ((Q : Matrix (Fin (m + n)) (Fin (m + n)) ℝ)ᵀ)) *
        ((Q : Matrix (Fin (m + n)) (Fin (m + n)) ℝ) *
          DY *
          ((Q : Matrix (Fin (m + n)) (Fin (m + n)) ℝ)ᵀ)) := by
            rw [hQX, hQY]
    _ = (Q : Matrix (Fin (m + n)) (Fin (m + n)) ℝ) * (DX * DY) *
          ((Q : Matrix (Fin (m + n)) (Fin (m + n)) ℝ)ᵀ) := hleft
    _ = (Q : Matrix (Fin (m + n)) (Fin (m + n)) ℝ) * (DY * DX) *
          ((Q : Matrix (Fin (m + n)) (Fin (m + n)) ℝ)ᵀ) := by
            rw [hdiagComm]
    _ = ((Q : Matrix (Fin (m + n)) (Fin (m + n)) ℝ) *
          DY *
          ((Q : Matrix (Fin (m + n)) (Fin (m + n)) ℝ)ᵀ)) *
        ((Q : Matrix (Fin (m + n)) (Fin (m + n)) ℝ) *
          DX *
          ((Q : Matrix (Fin (m + n)) (Fin (m + n)) ℝ)ᵀ)) := hright.symm
    _ = symmetric_dilation Y * symmetric_dilation X := by
            rw [hQX, hQY]

/-- Helper for Theorem 7.4: when two symmetric dilations commute, the rectangular cross-Gram
matrices `Xᵀ Y` and `X Yᵀ` are symmetric. -/
lemma symmetric_dilation_commute_implies_cross_gram_isSymm
    (X Y : Matrix (Fin m) (Fin n) ℝ)
    (hcomm :
      symmetric_dilation X * symmetric_dilation Y =
        symmetric_dilation Y * symmetric_dilation X) :
    (Xᵀ * Y).IsSymm ∧ (X * Yᵀ).IsSymm := by
  have hblock :
      block_symmetric_dilation X * block_symmetric_dilation Y =
        block_symmetric_dilation Y * block_symmetric_dilation X := by
    -- Undo the shared `finSumFinEquiv` reindexing so the block equations can be read entrywise.
    simpa [symmetric_dilation] using
      congrArg (Matrix.reindex finSumFinEquiv.symm finSumFinEquiv.symm) hcomm
  rw [block_symmetric_dilation_mul, block_symmetric_dilation_mul] at hblock
  constructor
  · have h₂₂ : Xᵀ * Y = Yᵀ * X := by
      -- The `(2,2)` block records the rectangular product `Xᵀ Y`.
      simpa using congrArg Matrix.toBlocks₂₂ hblock
    -- Symmetry follows because the transpose of `Xᵀ Y` is `Yᵀ X`.
    rw [Matrix.IsSymm]
    simpa [Matrix.transpose_mul] using h₂₂.symm
  · have h₁₁ : X * Yᵀ = Y * Xᵀ := by
      -- The `(1,1)` block records the rectangular product `X Yᵀ`.
      simpa using congrArg Matrix.toBlocks₁₁ hblock
    -- The transpose of `X Yᵀ` is `Y Xᵀ`, so the block equality is exactly symmetry.
    rw [Matrix.IsSymm]
    simpa [Matrix.transpose_mul] using h₁₁.symm

/-- Helper for Theorem 7.4: applying the block symmetric dilation to a vector on
`Fin m ⊕ Fin n` simply swaps the two blocks through `X` and `Xᵀ`. -/
lemma block_symmetric_dilation_mulVec_split
    (X : Matrix (Fin m) (Fin n) ℝ) (u : Fin m → ℝ) (v : Fin n → ℝ) :
    block_symmetric_dilation X *ᵥ Sum.elim u v =
      Sum.elim (X.mulVec v) (Xᵀ.mulVec u) := by
  -- Evaluate the block dilation row-by-row and read off the two off-diagonal actions.
  ext a
  cases a with
  | inl i =>
      simp [block_symmetric_dilation, Matrix.mulVec, Matrix.fromBlocks, dotProduct]
  | inr j =>
      simp [block_symmetric_dilation, Matrix.mulVec, Matrix.fromBlocks, dotProduct]

/-- Helper for Theorem 7.4: each positive-head column of a common ordered diagonalization of the
two symmetric dilations yields common left/right singular-vector equations for `X` and `Y`. -/
lemma head_dilation_column_common_singular_vector_equations
    (X Y : Matrix (Fin m) (Fin n) ℝ)
    (Q : Matrix.orthogonalGroup (Fin (m + n)) ℝ)
    (hQX :
      (symmetric_dilation X : Matrix (Fin (m + n)) (Fin (m + n)) ℝ) =
        (Q : Matrix (Fin (m + n)) (Fin (m + n)) ℝ) *
          Matrix.diagonal (signed_singular_value_profile X) *
          ((Q : Matrix (Fin (m + n)) (Fin (m + n)) ℝ)ᵀ))
    (hQY :
      (symmetric_dilation Y : Matrix (Fin (m + n)) (Fin (m + n)) ℝ) =
        (Q : Matrix (Fin (m + n)) (Fin (m + n)) ℝ) *
          Matrix.diagonal (signed_singular_value_profile Y) *
          ((Q : Matrix (Fin (m + n)) (Fin (m + n)) ℝ)ᵀ))
    (i : Fin (min m n)) :
    let j : Fin (m + n) := ⟨i.1, by
      omega⟩
    let q : Fin (m + n) → ℝ := (Q : Matrix (Fin (m + n)) (Fin (m + n)) ℝ).col j
    let u : Fin m → ℝ := fun r ↦ q (finSumFinEquiv (Sum.inl r))
    let v : Fin n → ℝ := fun c ↦ q (finSumFinEquiv (Sum.inr c))
    X.mulVec v = singular_value_function X i • u ∧
      Xᵀ.mulVec u = singular_value_function X i • v ∧
      Y.mulVec v = singular_value_function Y i • u ∧
      Yᵀ.mulVec u = singular_value_function Y i • v := by
  dsimp
  let j : Fin (m + n) := ⟨i.1, by
    omega⟩
  let q : Fin (m + n) → ℝ := (Q : Matrix (Fin (m + n)) (Fin (m + n)) ℝ).col j
  let u : Fin m → ℝ := fun r ↦ q (finSumFinEquiv (Sum.inl r))
  let v : Fin n → ℝ := fun c ↦ q (finSumFinEquiv (Sum.inr c))
  have hQQ :
      ((Q : Matrix (Fin (m + n)) (Fin (m + n)) ℝ)ᵀ) *
          (Q : Matrix (Fin (m + n)) (Fin (m + n)) ℝ) = 1 :=
    (Matrix.mem_orthogonalGroup_iff' (A := (Q :
        Matrix (Fin (m + n)) (Fin (m + n)) ℝ)) (R := ℝ)).1 Q.2
  have hAQX :
      symmetric_dilation X * (Q : Matrix (Fin (m + n)) (Fin (m + n)) ℝ) =
        (Q : Matrix (Fin (m + n)) (Fin (m + n)) ℝ) *
          Matrix.diagonal (signed_singular_value_profile X) := by
    -- Cancel the right orthogonal factor in the common diagonal model for `X`.
    calc
      symmetric_dilation X * (Q : Matrix (Fin (m + n)) (Fin (m + n)) ℝ)
        = ((Q : Matrix (Fin (m + n)) (Fin (m + n)) ℝ) *
            Matrix.diagonal (signed_singular_value_profile X) *
            ((Q : Matrix (Fin (m + n)) (Fin (m + n)) ℝ)ᵀ)) *
            (Q : Matrix (Fin (m + n)) (Fin (m + n)) ℝ) := by
              rw [hQX]
      _ = (Q : Matrix (Fin (m + n)) (Fin (m + n)) ℝ) *
            Matrix.diagonal (signed_singular_value_profile X) := by
              rw [show
                  (((Q : Matrix (Fin (m + n)) (Fin (m + n)) ℝ) *
                      Matrix.diagonal (signed_singular_value_profile X) *
                      ((Q : Matrix (Fin (m + n)) (Fin (m + n)) ℝ)ᵀ)) *
                      (Q : Matrix (Fin (m + n)) (Fin (m + n)) ℝ)) =
                    (Q : Matrix (Fin (m + n)) (Fin (m + n)) ℝ) *
                      (Matrix.diagonal (signed_singular_value_profile X) *
                        (((Q : Matrix (Fin (m + n)) (Fin (m + n)) ℝ)ᵀ) *
                          (Q : Matrix (Fin (m + n)) (Fin (m + n)) ℝ))) by
                    simp [Matrix.mul_assoc]]
              rw [hQQ]
              simp [Matrix.mul_assoc]
  have hAQY :
      symmetric_dilation Y * (Q : Matrix (Fin (m + n)) (Fin (m + n)) ℝ) =
        (Q : Matrix (Fin (m + n)) (Fin (m + n)) ℝ) *
          Matrix.diagonal (signed_singular_value_profile Y) := by
    -- The same cancellation exposes the diagonal eigenvalue action for `Y`.
    calc
      symmetric_dilation Y * (Q : Matrix (Fin (m + n)) (Fin (m + n)) ℝ)
        = ((Q : Matrix (Fin (m + n)) (Fin (m + n)) ℝ) *
            Matrix.diagonal (signed_singular_value_profile Y) *
            ((Q : Matrix (Fin (m + n)) (Fin (m + n)) ℝ)ᵀ)) *
            (Q : Matrix (Fin (m + n)) (Fin (m + n)) ℝ) := by
              rw [hQY]
      _ = (Q : Matrix (Fin (m + n)) (Fin (m + n)) ℝ) *
            Matrix.diagonal (signed_singular_value_profile Y) := by
              rw [show
                  (((Q : Matrix (Fin (m + n)) (Fin (m + n)) ℝ) *
                      Matrix.diagonal (signed_singular_value_profile Y) *
                      ((Q : Matrix (Fin (m + n)) (Fin (m + n)) ℝ)ᵀ)) *
                      (Q : Matrix (Fin (m + n)) (Fin (m + n)) ℝ)) =
                    (Q : Matrix (Fin (m + n)) (Fin (m + n)) ℝ) *
                      (Matrix.diagonal (signed_singular_value_profile Y) *
                        (((Q : Matrix (Fin (m + n)) (Fin (m + n)) ℝ)ᵀ) *
                          (Q : Matrix (Fin (m + n)) (Fin (m + n)) ℝ))) by
                    simp [Matrix.mul_assoc]]
              rw [hQQ]
              simp [Matrix.mul_assoc]
  have hq :
      q = fun a ↦ Sum.elim u v (finSumFinEquiv.symm a) := by
    -- The chosen column of `Q` splits into its top and bottom blocks on the sum index set.
    ext a
    cases ha : finSumFinEquiv.symm a with
    | inl r =>
        rw [← finSumFinEquiv.apply_symm_apply a, ha]
        simp [q, u, v, Matrix.col]
    | inr c =>
        rw [← finSumFinEquiv.apply_symm_apply a, ha]
        simp [q, u, v, Matrix.col]
  have hcolX :
      symmetric_dilation X *ᵥ q = singular_value_function X i • q := by
    -- Apply the diagonalized matrix identity to the `j`-th basis vector and collapse the diagonal
    -- action to the `j`-th scalar.
    have hcol :=
      congrArg
        (fun M : Matrix (Fin (m + n)) (Fin (m + n)) ℝ ↦ M *ᵥ Pi.single j 1)
        hAQX
    have hprofile :
        signed_singular_value_profile X j = singular_value_function X i := by
      simpa [j] using
        signed_singular_value_profile_head (m := m) (n := n) X j (by simpa [j] using i.2)
    have hdiag :
        Matrix.diagonal (signed_singular_value_profile X) *ᵥ Pi.single j 1 =
          Pi.single j (singular_value_function X i) := by
      simpa [hprofile] using
        (Matrix.diagonal_mulVec_single (signed_singular_value_profile X) j (1 : ℝ))
    calc
      symmetric_dilation X *ᵥ q
        = ((Q : Matrix (Fin (m + n)) (Fin (m + n)) ℝ) *
            Matrix.diagonal (signed_singular_value_profile X)) *ᵥ Pi.single j 1 := by
              simpa [q, Matrix.mulVec_single_one] using hcol
      _ = (Q : Matrix (Fin (m + n)) (Fin (m + n)) ℝ) *ᵥ
            (Matrix.diagonal (signed_singular_value_profile X) *ᵥ Pi.single j 1) := by
              rw [Matrix.mulVec_mulVec]
      _ = (Q : Matrix (Fin (m + n)) (Fin (m + n)) ℝ) *ᵥ
            Pi.single j (singular_value_function X i) := by
              rw [hdiag]
      _ = singular_value_function X i • q := by
              simpa [q] using
                (Matrix.mulVec_single
                  (Q : Matrix (Fin (m + n)) (Fin (m + n)) ℝ)
                  j
                  (singular_value_function X i))
  have hcolY :
      symmetric_dilation Y *ᵥ q = singular_value_function Y i • q := by
    -- The same basis-vector evaluation gives the common eigenvector equation for `Y`.
    have hcol :=
      congrArg
        (fun M : Matrix (Fin (m + n)) (Fin (m + n)) ℝ ↦ M *ᵥ Pi.single j 1)
        hAQY
    have hprofile :
        signed_singular_value_profile Y j = singular_value_function Y i := by
      simpa [j] using
        signed_singular_value_profile_head (m := m) (n := n) Y j (by simpa [j] using i.2)
    have hdiag :
        Matrix.diagonal (signed_singular_value_profile Y) *ᵥ Pi.single j 1 =
          Pi.single j (singular_value_function Y i) := by
      simpa [hprofile] using
        (Matrix.diagonal_mulVec_single (signed_singular_value_profile Y) j (1 : ℝ))
    calc
      symmetric_dilation Y *ᵥ q
        = ((Q : Matrix (Fin (m + n)) (Fin (m + n)) ℝ) *
            Matrix.diagonal (signed_singular_value_profile Y)) *ᵥ Pi.single j 1 := by
              simpa [q, Matrix.mulVec_single_one] using hcol
      _ = (Q : Matrix (Fin (m + n)) (Fin (m + n)) ℝ) *ᵥ
            (Matrix.diagonal (signed_singular_value_profile Y) *ᵥ Pi.single j 1) := by
              rw [Matrix.mulVec_mulVec]
      _ = (Q : Matrix (Fin (m + n)) (Fin (m + n)) ℝ) *ᵥ
            Pi.single j (singular_value_function Y i) := by
              rw [hdiag]
      _ = singular_value_function Y i • q := by
              simpa [q] using
                (Matrix.mulVec_single
                  (Q : Matrix (Fin (m + n)) (Fin (m + n)) ℝ)
                  j
                  (singular_value_function Y i))
  have hcolXsum :
      block_symmetric_dilation X *ᵥ Sum.elim u v =
        singular_value_function X i • Sum.elim u v := by
    -- Reindex the column eigenvector equation from `Fin (m + n)` back to the block coordinates.
    ext a
    change
      (fun j : Fin m ⊕ Fin n ↦ block_symmetric_dilation X a j) ⬝ᵥ Sum.elim u v =
        (singular_value_function X i • Sum.elim u v) a
    have h := congrFun hcolX (finSumFinEquiv a)
    rw [hq] at h
    simp [symmetric_dilation, Matrix.mulVec, Matrix.reindex_apply] at h
    have hdot :
        ((fun j : Fin (m + n) ↦ block_symmetric_dilation X a (finSumFinEquiv.symm j)) ⬝ᵥ
            fun b ↦ (u ⊕ᵥ v) (finSumFinEquiv.symm b)) =
          (fun j : Fin m ⊕ Fin n ↦ block_symmetric_dilation X a j) ⬝ᵥ Sum.elim u v := by
      simpa [Function.comp_def] using
        (dotProduct_comp_equiv_symm
          (u := fun j : Fin (m + n) ↦ block_symmetric_dilation X a (finSumFinEquiv.symm j))
          (x := Sum.elim u v)
          finSumFinEquiv)
    rw [hdot] at h
    simpa [dotProduct] using h
  have hcolYsum :
      block_symmetric_dilation Y *ᵥ Sum.elim u v =
        singular_value_function Y i • Sum.elim u v := by
    -- The same reindexing gives the common block eigenvector equation for `Y`.
    ext a
    change
      (fun j : Fin m ⊕ Fin n ↦ block_symmetric_dilation Y a j) ⬝ᵥ Sum.elim u v =
        (singular_value_function Y i • Sum.elim u v) a
    have h := congrFun hcolY (finSumFinEquiv a)
    rw [hq] at h
    simp [symmetric_dilation, Matrix.mulVec, Matrix.reindex_apply] at h
    have hdot :
        ((fun j : Fin (m + n) ↦ block_symmetric_dilation Y a (finSumFinEquiv.symm j)) ⬝ᵥ
            fun b ↦ (u ⊕ᵥ v) (finSumFinEquiv.symm b)) =
          (fun j : Fin m ⊕ Fin n ↦ block_symmetric_dilation Y a j) ⬝ᵥ Sum.elim u v := by
      simpa [Function.comp_def] using
        (dotProduct_comp_equiv_symm
          (u := fun j : Fin (m + n) ↦ block_symmetric_dilation Y a (finSumFinEquiv.symm j))
          (x := Sum.elim u v)
          finSumFinEquiv)
    rw [hdot] at h
    simpa [dotProduct] using h
  constructor
  · -- Read the `Sum.inl` block of the `j`-th column eigenvector equation for `X`.
    ext r
    have hsplit :
        Sum.elim (X.mulVec v) (Xᵀ.mulVec u) =
          singular_value_function X i • Sum.elim u v := by
      rw [← block_symmetric_dilation_mulVec_split (m := m) (n := n) X u v]
      exact hcolXsum
    simpa using congrFun hsplit (Sum.inl r)
  · constructor
    · -- Read the `Sum.inr` block of the same column equation for `X`.
      ext c
      have hsplit :
          Sum.elim (X.mulVec v) (Xᵀ.mulVec u) =
            singular_value_function X i • Sum.elim u v := by
        rw [← block_symmetric_dilation_mulVec_split (m := m) (n := n) X u v]
        exact hcolXsum
      simpa using congrFun hsplit (Sum.inr c)
    · constructor
      · -- The identical head-column argument gives the singular-vector equation for `Y`.
        ext r
        have hsplit :
            Sum.elim (Y.mulVec v) (Yᵀ.mulVec u) =
              singular_value_function Y i • Sum.elim u v := by
          rw [← block_symmetric_dilation_mulVec_split (m := m) (n := n) Y u v]
          exact hcolYsum
        simpa using congrFun hsplit (Sum.inl r)
      · -- The bottom block of the common column closes the transpose equation for `Y`.
        ext c
        have hsplit :
            Sum.elim (Y.mulVec v) (Yᵀ.mulVec u) =
              singular_value_function Y i • Sum.elim u v := by
          rw [← block_symmetric_dilation_mulVec_split (m := m) (n := n) Y u v]
          exact hcolYsum
        simpa using congrFun hsplit (Sum.inr c)

/-- Helper for Theorem 7.4: flipping the bottom block of a positive-head common dilation column
produces the companion column on which both block dilations act by the negative singular values. -/
lemma head_dilation_column_block_sign_companion_equations
    (X Y : Matrix (Fin m) (Fin n) ℝ)
    (Q : Matrix.orthogonalGroup (Fin (m + n)) ℝ)
    (hQX :
      (symmetric_dilation X : Matrix (Fin (m + n)) (Fin (m + n)) ℝ) =
        (Q : Matrix (Fin (m + n)) (Fin (m + n)) ℝ) *
          Matrix.diagonal (signed_singular_value_profile X) *
          ((Q : Matrix (Fin (m + n)) (Fin (m + n)) ℝ)ᵀ))
    (hQY :
      (symmetric_dilation Y : Matrix (Fin (m + n)) (Fin (m + n)) ℝ) =
        (Q : Matrix (Fin (m + n)) (Fin (m + n)) ℝ) *
          Matrix.diagonal (signed_singular_value_profile Y) *
          ((Q : Matrix (Fin (m + n)) (Fin (m + n)) ℝ)ᵀ))
    (i : Fin (min m n)) :
    let j : Fin (m + n) := ⟨i.1, by
      omega⟩
    let q : Fin (m + n) → ℝ := (Q : Matrix (Fin (m + n)) (Fin (m + n)) ℝ).col j
    let u : Fin m → ℝ := fun r ↦ q (finSumFinEquiv (Sum.inl r))
    let v : Fin n → ℝ := fun c ↦ q (finSumFinEquiv (Sum.inr c))
    block_symmetric_dilation X *ᵥ Sum.elim u (-v) =
        -singular_value_function X i • Sum.elim u (-v) ∧
      block_symmetric_dilation Y *ᵥ Sum.elim u (-v) =
        -singular_value_function Y i • Sum.elim u (-v) := by
  dsimp
  let j : Fin (m + n) := ⟨i.1, by
    omega⟩
  let q : Fin (m + n) → ℝ := (Q : Matrix (Fin (m + n)) (Fin (m + n)) ℝ).col j
  let u : Fin m → ℝ := fun r ↦ q (finSumFinEquiv (Sum.inl r))
  let v : Fin n → ℝ := fun c ↦ q (finSumFinEquiv (Sum.inr c))
  rcases
      head_dilation_column_common_singular_vector_equations
        (m := m) (n := n) X Y Q hQX hQY i with
    ⟨hXuv, hXtu, hYuv, hYtu⟩
  constructor
  · -- The companion vector uses the same top block and the negated bottom block, so the block
    -- dilation equations pick up the opposite eigenvalue.
    change
      block_symmetric_dilation X *ᵥ Sum.elim u (fun c ↦ -v c) =
        -singular_value_function X i • Sum.elim u (fun c ↦ -v c)
    rw [block_symmetric_dilation_mulVec_split (m := m) (n := n) X u (fun c ↦ -v c)]
    ext a
    cases a with
    | inl r =>
        have hneg := congrArg Neg.neg (congrFun hXuv r)
        simpa [Matrix.mulVec, dotProduct, Pi.neg_apply] using hneg
    | inr c =>
        simpa using congrFun hXtu c
  · -- The identical sign flip works for the second block dilation as well.
    change
      block_symmetric_dilation Y *ᵥ Sum.elim u (fun c ↦ -v c) =
        -singular_value_function Y i • Sum.elim u (fun c ↦ -v c)
    rw [block_symmetric_dilation_mulVec_split (m := m) (n := n) Y u (fun c ↦ -v c)]
    ext a
    cases a with
    | inl r =>
        have hneg := congrArg Neg.neg (congrFun hYuv r)
        simpa [Matrix.mulVec, dotProduct, Pi.neg_apply] using hneg
    | inr c =>
        simpa using congrFun hYtu c

/-- Helper for Theorem 7.4: different columns of an orthogonal matrix have the expected
Kronecker-delta dot products. -/
lemma orthogonalGroup_col_dotProduct_eq_ite {k : ℕ}
    (Q : Matrix.orthogonalGroup (Fin k) ℝ) (i j : Fin k) :
    dotProduct ((Q : Matrix (Fin k) (Fin k) ℝ).col i) ((Q : Matrix (Fin k) (Fin k) ℝ).col j) =
      if i = j then 1 else 0 := by
  -- Read the `(i,j)` entry of `Qᵀ Q = I` as the dot product of the `i`-th and `j`-th columns.
  have hQQ :
      ((Q : Matrix (Fin k) (Fin k) ℝ)ᵀ) * (Q : Matrix (Fin k) (Fin k) ℝ) = 1 :=
    (Matrix.mem_orthogonalGroup_iff' (A := (Q : Matrix (Fin k) (Fin k) ℝ)) (R := ℝ)).1 Q.2
  have hentry :
      ((((Q : Matrix (Fin k) (Fin k) ℝ)ᵀ) * (Q : Matrix (Fin k) (Fin k) ℝ)) i j) =
        (1 : Matrix (Fin k) (Fin k) ℝ) i j := by
    simpa using congrFun (congrFun hQQ i) j
  simpa [Matrix.mul_apply, Matrix.col, dotProduct] using hentry

/-- Helper for Theorem 7.4: each positive-head column of the common dilation basis is an
eigenvector of both block symmetric dilations, with the corresponding singular values as
eigenvalues. -/
lemma head_dilation_column_block_eigenvector_equations
    (X Y : Matrix (Fin m) (Fin n) ℝ)
    (Q : Matrix.orthogonalGroup (Fin (m + n)) ℝ)
    (hQX :
      (symmetric_dilation X : Matrix (Fin (m + n)) (Fin (m + n)) ℝ) =
        (Q : Matrix (Fin (m + n)) (Fin (m + n)) ℝ) *
          Matrix.diagonal (signed_singular_value_profile X) *
          ((Q : Matrix (Fin (m + n)) (Fin (m + n)) ℝ)ᵀ))
    (hQY :
      (symmetric_dilation Y : Matrix (Fin (m + n)) (Fin (m + n)) ℝ) =
        (Q : Matrix (Fin (m + n)) (Fin (m + n)) ℝ) *
          Matrix.diagonal (signed_singular_value_profile Y) *
          ((Q : Matrix (Fin (m + n)) (Fin (m + n)) ℝ)ᵀ))
    (i : Fin (min m n)) :
    let j : Fin (m + n) := ⟨i.1, by
      omega⟩
    let q : Fin (m + n) → ℝ := (Q : Matrix (Fin (m + n)) (Fin (m + n)) ℝ).col j
    let u : Fin m → ℝ := fun r ↦ q (finSumFinEquiv (Sum.inl r))
    let v : Fin n → ℝ := fun c ↦ q (finSumFinEquiv (Sum.inr c))
    block_symmetric_dilation X *ᵥ Sum.elim u v =
        singular_value_function X i • Sum.elim u v ∧
      block_symmetric_dilation Y *ᵥ Sum.elim u v =
        singular_value_function Y i • Sum.elim u v := by
  dsimp
  let j : Fin (m + n) := ⟨i.1, by
    omega⟩
  let q : Fin (m + n) → ℝ := (Q : Matrix (Fin (m + n)) (Fin (m + n)) ℝ).col j
  let u : Fin m → ℝ := fun r ↦ q (finSumFinEquiv (Sum.inl r))
  let v : Fin n → ℝ := fun c ↦ q (finSumFinEquiv (Sum.inr c))
  rcases
      head_dilation_column_common_singular_vector_equations
        (m := m) (n := n) X Y Q hQX hQY i with
    ⟨hXuv, hXtu, hYuv, hYtu⟩
  constructor
  · -- Reassemble the top and bottom block equations into the block-dilation eigenvector identity.
    calc
      block_symmetric_dilation X *ᵥ Sum.elim u v = Sum.elim (X.mulVec v) (Xᵀ.mulVec u) := by
        exact block_symmetric_dilation_mulVec_split (m := m) (n := n) X u v
      _ = singular_value_function X i • Sum.elim u v := by
        ext a
        cases a with
        | inl r =>
            simpa using congrFun hXuv r
        | inr c =>
            simpa using congrFun hXtu c
  · -- The same block reassembly yields the common eigenvector identity for `Y`.
    calc
      block_symmetric_dilation Y *ᵥ Sum.elim u v = Sum.elim (Y.mulVec v) (Yᵀ.mulVec u) := by
        exact block_symmetric_dilation_mulVec_split (m := m) (n := n) Y u v
      _ = singular_value_function Y i • Sum.elim u v := by
        ext a
        cases a with
        | inl r =>
            simpa using congrFun hYuv r
        | inr c =>
            simpa using congrFun hYtu c

/-- Helper for Theorem 7.4: splitting two positive-head columns of the common dilation basis into
their top and bottom blocks decomposes the column dot product into the sum of the block
dot products. -/
lemma head_dilation_column_block_dotProduct_add_eq_ite
    (Q : Matrix.orthogonalGroup (Fin (m + n)) ℝ)
    (i j : Fin (min m n)) :
    let ji : Fin (m + n) := ⟨i.1, by
      omega⟩
    let jj : Fin (m + n) := ⟨j.1, by
      omega⟩
    let qi : Fin (m + n) → ℝ := (Q : Matrix (Fin (m + n)) (Fin (m + n)) ℝ).col ji
    let qj : Fin (m + n) → ℝ := (Q : Matrix (Fin (m + n)) (Fin (m + n)) ℝ).col jj
    let ui : Fin m → ℝ := fun r ↦ qi (finSumFinEquiv (Sum.inl r))
    let vi : Fin n → ℝ := fun c ↦ qi (finSumFinEquiv (Sum.inr c))
    let uj : Fin m → ℝ := fun r ↦ qj (finSumFinEquiv (Sum.inl r))
    let vj : Fin n → ℝ := fun c ↦ qj (finSumFinEquiv (Sum.inr c))
    dotProduct ui uj + dotProduct vi vj = if i = j then 1 else 0 := by
  dsimp
  let ji : Fin (m + n) := ⟨i.1, by
    omega⟩
  let jj : Fin (m + n) := ⟨j.1, by
    omega⟩
  let qi : Fin (m + n) → ℝ := (Q : Matrix (Fin (m + n)) (Fin (m + n)) ℝ).col ji
  let qj : Fin (m + n) → ℝ := (Q : Matrix (Fin (m + n)) (Fin (m + n)) ℝ).col jj
  let ui : Fin m → ℝ := fun r ↦ qi (finSumFinEquiv (Sum.inl r))
  let vi : Fin n → ℝ := fun c ↦ qi (finSumFinEquiv (Sum.inr c))
  let uj : Fin m → ℝ := fun r ↦ qj (finSumFinEquiv (Sum.inl r))
  let vj : Fin n → ℝ := fun c ↦ qj (finSumFinEquiv (Sum.inr c))
  have hcol :
      dotProduct qi qj = if ji = jj then 1 else 0 :=
    orthogonalGroup_col_dotProduct_eq_ite (Q := Q) ji jj
  have hsplit :
      dotProduct qi qj = dotProduct ui uj + dotProduct vi vj := by
    -- Reindex the column dot product back to the block coordinates and then split the sum type.
    have hqj :
        qj = (Sum.elim uj vj) ∘ finSumFinEquiv.symm := by
      ext x
      cases h : finSumFinEquiv.symm x with
      | inl r =>
          have hx : x = finSumFinEquiv (Sum.inl r) := by
            simpa using congrArg finSumFinEquiv h
          simp [qj, uj, vj, hx]
      | inr c =>
          have hx : x = finSumFinEquiv (Sum.inr c) := by
            simpa using congrArg finSumFinEquiv h
          simp [qj, uj, vj, hx]
    have hqi :
        qi ∘ finSumFinEquiv = Sum.elim ui vi := by
      ext x
      cases x with
      | inl r =>
          simp [qi, ui, vi]
      | inr c =>
          simp [qi, ui, vi]
    calc
      dotProduct qi qj = dotProduct qi ((Sum.elim uj vj) ∘ finSumFinEquiv.symm) := by
        rw [hqj]
      _ = dotProduct (qi ∘ finSumFinEquiv) (Sum.elim uj vj) := by
        simpa [qi, ui, vi, Function.comp_def] using
          (dotProduct_comp_equiv_symm
            (u := qi) (x := Sum.elim uj vj) finSumFinEquiv)
      _ = dotProduct (Sum.elim ui vi) (Sum.elim uj vj) := by
        rw [hqi]
      _ = dotProduct ui uj + dotProduct vi vj := by
        simp [dotProduct]
  calc
    dotProduct ui uj + dotProduct vi vj = dotProduct qi qj := hsplit.symm
    _ = if ji = jj then 1 else 0 := hcol
    _ = if i = j then 1 else 0 := by
      by_cases hij : i = j
      · subst hij
        simp [ji, jj]
      · have hji : ji ≠ jj := by
          intro h
          apply hij
          ext
          simpa [ji, jj] using congrArg Fin.val h
        simp [hij, hji]

/-- Helper for Theorem 7.4: eigenvectors of a real symmetric matrix with different eigenvalues are
orthogonal in the Euclidean dot product. -/
lemma dotProduct_eq_zero_of_isSymm_mulVec_eq_smul_of_ne
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ) (hA : A.IsSymm)
    (x y : ι → ℝ) {a b : ℝ}
    (hx : A *ᵥ x = a • x) (hy : A *ᵥ y = b • y) (hab : a ≠ b) :
    dotProduct x y = 0 := by
  have hxy : a * dotProduct x y = b * dotProduct x y := by
    -- Move the symmetric matrix across the dot product and compare the two eigenvalue scalars.
    calc
      a * dotProduct x y = dotProduct (a • x) y := by
            simp
      _ = dotProduct (A *ᵥ x) y := by
            rw [hx]
      _ = dotProduct (Aᵀ *ᵥ x) y := by
            rw [show Aᵀ *ᵥ x = A *ᵥ x by
              simpa [Matrix.IsSymm] using congrArg (fun M ↦ M *ᵥ x) hA]
      _ = dotProduct x (A *ᵥ y) := by
            rw [Matrix.dotProduct_mulVec,
              ← Matrix.vecMul_transpose (A := Aᵀ) (x := x), Matrix.transpose_transpose]
      _ = dotProduct x (b • y) := by
            rw [hy]
      _ = b * dotProduct x y := by
            simp
  have hsub : (a - b) * dotProduct x y = 0 := by
    linarith
  by_cases hdot : dotProduct x y = 0
  · exact hdot
  · have hab0 : a - b = 0 := (mul_eq_zero.mp hsub).resolve_right hdot
    exact (hab (sub_eq_zero.mp hab0)).elim

/-- Helper for Theorem 7.4: on active indices, a positive-head column is orthogonal to any
block-sign companion column, so the top and bottom block dot products agree. -/
lemma active_head_dilation_column_block_dotProduct_sub_eq_zero
    (X Y : Matrix (Fin m) (Fin n) ℝ)
    (Q : Matrix.orthogonalGroup (Fin (m + n)) ℝ)
    (hQX :
      (symmetric_dilation X : Matrix (Fin (m + n)) (Fin (m + n)) ℝ) =
        (Q : Matrix (Fin (m + n)) (Fin (m + n)) ℝ) *
          Matrix.diagonal (signed_singular_value_profile X) *
          ((Q : Matrix (Fin (m + n)) (Fin (m + n)) ℝ)ᵀ))
    (hQY :
      (symmetric_dilation Y : Matrix (Fin (m + n)) (Fin (m + n)) ℝ) =
        (Q : Matrix (Fin (m + n)) (Fin (m + n)) ℝ) *
          Matrix.diagonal (signed_singular_value_profile Y) *
          ((Q : Matrix (Fin (m + n)) (Fin (m + n)) ℝ)ᵀ))
    (i j : Fin (min m n))
    (hi : singular_value_function X i ≠ 0 ∨ singular_value_function Y i ≠ 0)
    (hj : singular_value_function X j ≠ 0 ∨ singular_value_function Y j ≠ 0) :
    let ji : Fin (m + n) := ⟨i.1, by
      omega⟩
    let jj : Fin (m + n) := ⟨j.1, by
      omega⟩
    let qi : Fin (m + n) → ℝ := (Q : Matrix (Fin (m + n)) (Fin (m + n)) ℝ).col ji
    let qj : Fin (m + n) → ℝ := (Q : Matrix (Fin (m + n)) (Fin (m + n)) ℝ).col jj
    let ui : Fin m → ℝ := fun r ↦ qi (finSumFinEquiv (Sum.inl r))
    let vi : Fin n → ℝ := fun c ↦ qi (finSumFinEquiv (Sum.inr c))
    let uj : Fin m → ℝ := fun r ↦ qj (finSumFinEquiv (Sum.inl r))
    let vj : Fin n → ℝ := fun c ↦ qj (finSumFinEquiv (Sum.inr c))
    dotProduct ui uj - dotProduct vi vj = 0 := by
  dsimp
  let ji : Fin (m + n) := ⟨i.1, by
    omega⟩
  let jj : Fin (m + n) := ⟨j.1, by
    omega⟩
  let qi : Fin (m + n) → ℝ := (Q : Matrix (Fin (m + n)) (Fin (m + n)) ℝ).col ji
  let qj : Fin (m + n) → ℝ := (Q : Matrix (Fin (m + n)) (Fin (m + n)) ℝ).col jj
  let ui : Fin m → ℝ := fun r ↦ qi (finSumFinEquiv (Sum.inl r))
  let vi : Fin n → ℝ := fun c ↦ qi (finSumFinEquiv (Sum.inr c))
  let uj : Fin m → ℝ := fun r ↦ qj (finSumFinEquiv (Sum.inl r))
  let vj : Fin n → ℝ := fun c ↦ qj (finSumFinEquiv (Sum.inr c))
  have hhead := head_dilation_column_block_eigenvector_equations
    (m := m) (n := n) X Y Q hQX hQY i
  have hcomp := head_dilation_column_block_sign_companion_equations
    (m := m) (n := n) X Y Q hQX hQY j
  have horthX :
      singular_value_function X i ≠ 0 ∨ singular_value_function X j ≠ 0 →
        dotProduct (Sum.elim ui vi) (Sum.elim uj (fun c ↦ -vj c)) = 0 := by
    intro hactiveX
    have hneX :
        singular_value_function X i ≠ -singular_value_function X j := by
      intro hneg
      have hXi_nonneg : 0 ≤ singular_value_function X i :=
        singular_value_function_nonneg X i
      have hXj_nonneg : 0 ≤ singular_value_function X j :=
        singular_value_function_nonneg X j
      rcases hactiveX with hXi | hXj
      · have hzero : singular_value_function X i = 0 := by
          linarith
        exact hXi hzero
      · have hzero : singular_value_function X j = 0 := by
          linarith
        exact hXj hzero
    exact
      dotProduct_eq_zero_of_isSymm_mulVec_eq_smul_of_ne
        (A := block_symmetric_dilation X)
        (hA := block_symmetric_dilation_isSymm X)
        (x := Sum.elim ui vi)
        (y := Sum.elim uj (fun c ↦ -vj c))
        (hx := hhead.1)
        (hy := hcomp.1)
        (hab := hneX)
  have horthY :
      singular_value_function Y i ≠ 0 ∨ singular_value_function Y j ≠ 0 →
        dotProduct (Sum.elim ui vi) (Sum.elim uj (fun c ↦ -vj c)) = 0 := by
    intro hactiveY
    have hneY :
        singular_value_function Y i ≠ -singular_value_function Y j := by
      intro hneg
      have hYi_nonneg : 0 ≤ singular_value_function Y i :=
        singular_value_function_nonneg Y i
      have hYj_nonneg : 0 ≤ singular_value_function Y j :=
        singular_value_function_nonneg Y j
      rcases hactiveY with hYi | hYj
      · have hzero : singular_value_function Y i = 0 := by
          linarith
        exact hYi hzero
      · have hzero : singular_value_function Y j = 0 := by
          linarith
        exact hYj hzero
    exact
      dotProduct_eq_zero_of_isSymm_mulVec_eq_smul_of_ne
        (A := block_symmetric_dilation Y)
        (hA := block_symmetric_dilation_isSymm Y)
        (x := Sum.elim ui vi)
        (y := Sum.elim uj (fun c ↦ -vj c))
        (hx := hhead.2)
        (hy := hcomp.2)
        (hab := hneY)
  have horth :
      dotProduct (Sum.elim ui vi) (Sum.elim uj (fun c ↦ -vj c)) = 0 := by
    by_cases hXi0 : singular_value_function X i = 0
    · by_cases hXj0 : singular_value_function X j = 0
      · have hYi : singular_value_function Y i ≠ 0 := by
          rcases hi with hXi' | hYi
          · exact (hXi' hXi0).elim
          · exact hYi
        have hYj : singular_value_function Y j ≠ 0 := by
          rcases hj with hXj' | hYj
          · exact (hXj' hXj0).elim
          · exact hYj
        exact horthY (Or.inl hYi)
      · exact horthX (Or.inr hXj0)
    · exact horthX (Or.inl hXi0)
  -- Reindex the orthogonality of the head/companion pair back to the block coordinates.
  simpa [dotProduct] using horth

/-- Helper for Theorem 7.4: on active indices, the top and bottom blocks of the positive-head
columns have the same dot products, and together they split the orthogonal-column delta. -/
lemma active_head_dilation_column_block_dotProduct_eq_half_ite
    (X Y : Matrix (Fin m) (Fin n) ℝ)
    (Q : Matrix.orthogonalGroup (Fin (m + n)) ℝ)
    (hQX :
      (symmetric_dilation X : Matrix (Fin (m + n)) (Fin (m + n)) ℝ) =
        (Q : Matrix (Fin (m + n)) (Fin (m + n)) ℝ) *
          Matrix.diagonal (signed_singular_value_profile X) *
          ((Q : Matrix (Fin (m + n)) (Fin (m + n)) ℝ)ᵀ))
    (hQY :
      (symmetric_dilation Y : Matrix (Fin (m + n)) (Fin (m + n)) ℝ) =
        (Q : Matrix (Fin (m + n)) (Fin (m + n)) ℝ) *
          Matrix.diagonal (signed_singular_value_profile Y) *
          ((Q : Matrix (Fin (m + n)) (Fin (m + n)) ℝ)ᵀ))
    (i j : Fin (min m n))
    (hi : singular_value_function X i ≠ 0 ∨ singular_value_function Y i ≠ 0)
    (hj : singular_value_function X j ≠ 0 ∨ singular_value_function Y j ≠ 0) :
    let ji : Fin (m + n) := ⟨i.1, by
      omega⟩
    let jj : Fin (m + n) := ⟨j.1, by
      omega⟩
    let qi : Fin (m + n) → ℝ := (Q : Matrix (Fin (m + n)) (Fin (m + n)) ℝ).col ji
    let qj : Fin (m + n) → ℝ := (Q : Matrix (Fin (m + n)) (Fin (m + n)) ℝ).col jj
    let ui : Fin m → ℝ := fun r ↦ qi (finSumFinEquiv (Sum.inl r))
    let vi : Fin n → ℝ := fun c ↦ qi (finSumFinEquiv (Sum.inr c))
    let uj : Fin m → ℝ := fun r ↦ qj (finSumFinEquiv (Sum.inl r))
    let vj : Fin n → ℝ := fun c ↦ qj (finSumFinEquiv (Sum.inr c))
    dotProduct ui uj = (if i = j then (1 : ℝ) / 2 else (0 : ℝ)) ∧
      dotProduct vi vj = (if i = j then (1 : ℝ) / 2 else (0 : ℝ)) := by
  dsimp
  let ji : Fin (m + n) := ⟨i.1, by
    omega⟩
  let jj : Fin (m + n) := ⟨j.1, by
    omega⟩
  let qi : Fin (m + n) → ℝ := (Q : Matrix (Fin (m + n)) (Fin (m + n)) ℝ).col ji
  let qj : Fin (m + n) → ℝ := (Q : Matrix (Fin (m + n)) (Fin (m + n)) ℝ).col jj
  let ui : Fin m → ℝ := fun r ↦ qi (finSumFinEquiv (Sum.inl r))
  let vi : Fin n → ℝ := fun c ↦ qi (finSumFinEquiv (Sum.inr c))
  let uj : Fin m → ℝ := fun r ↦ qj (finSumFinEquiv (Sum.inl r))
  let vj : Fin n → ℝ := fun c ↦ qj (finSumFinEquiv (Sum.inr c))
  have hadd :
      dotProduct ui uj + dotProduct vi vj = if i = j then 1 else 0 :=
    head_dilation_column_block_dotProduct_add_eq_ite (m := m) (n := n) Q i j
  have hsub :
      dotProduct ui uj - dotProduct vi vj = 0 :=
    active_head_dilation_column_block_dotProduct_sub_eq_zero
      (m := m) (n := n) X Y Q hQX hQY i j hi hj
  constructor
  · by_cases hij : i = j
    · subst hij
      have hadd' : dotProduct ui ui + dotProduct vi vi = 1 := by
        simpa using hadd
      have hsub' : dotProduct ui ui - dotProduct vi vi = 0 := by
        simpa using hsub
      have hhalf : dotProduct ui ui = (1 : ℝ) / 2 := by
        linarith
      simpa using hhalf
    · have hadd' : dotProduct ui uj + dotProduct vi vj = 0 := by
        simpa [hij] using hadd
      have hsub' : dotProduct ui uj - dotProduct vi vj = 0 := by
        simpa using hsub
      have hzero : dotProduct ui uj = 0 := by
        linarith
      simpa [hij] using hzero
  · by_cases hij : i = j
    · subst hij
      have hadd' : dotProduct ui ui + dotProduct vi vi = 1 := by
        simpa using hadd
      have hsub' : dotProduct ui ui - dotProduct vi vi = 0 := by
        simpa using hsub
      have hhalf : dotProduct vi vi = (1 : ℝ) / 2 := by
        linarith
      simpa using hhalf
    · have hadd' : dotProduct ui uj + dotProduct vi vj = 0 := by
        simpa [hij] using hadd
      have hsub' : dotProduct ui uj - dotProduct vi vj = 0 := by
        simpa using hsub
      have hzero : dotProduct vi vj = 0 := by
        linarith
      simpa [hij] using hzero

/-- Helper for Theorem 7.4: the positive-head columns of a common ordered dilation basis satisfy
the common singular-vector equations directly in Euclidean-space form. -/
lemma head_dilation_column_common_singular_vector_equations_euclidean
    (X Y : Matrix (Fin m) (Fin n) ℝ)
    (Q : Matrix.orthogonalGroup (Fin (m + n)) ℝ)
    (hQX :
      (symmetric_dilation X : Matrix (Fin (m + n)) (Fin (m + n)) ℝ) =
        (Q : Matrix (Fin (m + n)) (Fin (m + n)) ℝ) *
          Matrix.diagonal (signed_singular_value_profile X) *
          ((Q : Matrix (Fin (m + n)) (Fin (m + n)) ℝ)ᵀ))
    (hQY :
      (symmetric_dilation Y : Matrix (Fin (m + n)) (Fin (m + n)) ℝ) =
        (Q : Matrix (Fin (m + n)) (Fin (m + n)) ℝ) *
          Matrix.diagonal (signed_singular_value_profile Y) *
          ((Q : Matrix (Fin (m + n)) (Fin (m + n)) ℝ)ᵀ))
    (i : Fin (min m n)) :
    let j : Fin (m + n) := ⟨i.1, by
      omega⟩
    let q : Fin (m + n) → ℝ := (Q : Matrix (Fin (m + n)) (Fin (m + n)) ℝ).col j
    let u : Fin m → ℝ := fun r ↦ q (finSumFinEquiv (Sum.inl r))
    let v : Fin n → ℝ := fun c ↦ q (finSumFinEquiv (Sum.inr c))
    Matrix.toEuclideanLin X (WithLp.toLp 2 v) =
        singular_value_function X i • WithLp.toLp 2 u ∧
      Matrix.toEuclideanLin Xᵀ (WithLp.toLp 2 u) =
        singular_value_function X i • WithLp.toLp 2 v ∧
      Matrix.toEuclideanLin Y (WithLp.toLp 2 v) =
        singular_value_function Y i • WithLp.toLp 2 u ∧
      Matrix.toEuclideanLin Yᵀ (WithLp.toLp 2 u) =
        singular_value_function Y i • WithLp.toLp 2 v := by
  dsimp
  let j : Fin (m + n) := ⟨i.1, by
    omega⟩
  let q : Fin (m + n) → ℝ := (Q : Matrix (Fin (m + n)) (Fin (m + n)) ℝ).col j
  let u : Fin m → ℝ := fun r ↦ q (finSumFinEquiv (Sum.inl r))
  let v : Fin n → ℝ := fun c ↦ q (finSumFinEquiv (Sum.inr c))
  rcases
      head_dilation_column_common_singular_vector_equations
        (m := m) (n := n) X Y Q hQX hQY i with
    ⟨hXuv, hXtu, hYuv, hYtu⟩
  constructor
  · -- Transport the matrix `mulVec` equation for `X` into Euclidean-space coordinates.
    simpa [Matrix.toEuclideanLin_apply_piLp_toLp] using congrArg (WithLp.toLp 2) hXuv
  · constructor
    · -- The transpose equation for `X` is transported in the same way.
      simpa [Matrix.toEuclideanLin_apply_piLp_toLp] using congrArg (WithLp.toLp 2) hXtu
    · constructor
      · -- The common right singular directions satisfy the Euclidean-space equation for `Y`.
        simpa [Matrix.toEuclideanLin_apply_piLp_toLp] using congrArg (WithLp.toLp 2) hYuv
      · -- The transpose equation for `Y` closes the Euclidean-form package.
        simpa [Matrix.toEuclideanLin_apply_piLp_toLp] using congrArg (WithLp.toLp 2) hYtu

/-- Helper for Theorem 7.4: summing the squared norms of `Matrix.toEuclideanLin X` along any
orthonormal basis of the domain recovers the Frobenius square trace `Tr(Xᵀ X)`. -/
lemma sum_sq_norm_toEuclideanLin_on_orthonormalBasis_eq_trace_transpose_mul
    (X : Matrix (Fin m) (Fin n) ℝ)
    (b : OrthonormalBasis (Fin n) ℝ (EuclideanSpace ℝ (Fin n))) :
    (∑ j, ‖Matrix.toEuclideanLin X (b j)‖ ^ (2 : ℕ)) =
      Matrix.trace (Xᵀ * X) := by
  let T : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin m) := Matrix.toEuclideanLin X
  have htrace :
      LinearMap.trace ℝ (EuclideanSpace ℝ (Fin n)) (LinearMap.adjoint T ∘ₗ T) =
        ∑ j, ‖T (b j)‖ ^ (2 : ℕ) := by
    -- Rewrite the trace of `T†T` in the chosen orthonormal basis and collapse each summand to a
    -- squared norm by the adjoint identity.
    calc
      LinearMap.trace ℝ (EuclideanSpace ℝ (Fin n)) (LinearMap.adjoint T ∘ₗ T)
        = ∑ j, inner ℝ (b j) ((LinearMap.adjoint T ∘ₗ T) (b j)) := by
            simpa using
              LinearMap.trace_eq_sum_inner (LinearMap.adjoint T ∘ₗ T) b
      _ = ∑ j, ‖T (b j)‖ ^ (2 : ℕ) := by
            apply Finset.sum_congr rfl
            intro j hj
            simp [LinearMap.comp_apply, LinearMap.adjoint_inner_right, T, inner_self_eq_norm_sq]
  have hcomp :
      LinearMap.adjoint T ∘ₗ T = Matrix.toEuclideanLin (Xᵀ * X) := by
    -- Identify `T†T` with the Euclidean linear map attached to the Gram matrix `Xᵀ X`.
    rw [show LinearMap.adjoint T = Matrix.toEuclideanLin Xᵀ by
      simpa [T] using (Matrix.toEuclideanLin_conjTranspose_eq_adjoint (A := X)).symm]
    ext v j
    simp [T, Matrix.toLpLin_apply, Matrix.mulVec_mulVec]
  -- Transport the basis-trace computation back to the matrix trace of `Xᵀ X`.
  calc
    (∑ j, ‖Matrix.toEuclideanLin X (b j)‖ ^ (2 : ℕ))
      = LinearMap.trace ℝ (EuclideanSpace ℝ (Fin n)) (LinearMap.adjoint T ∘ₗ T) := by
          symm
          simpa [T] using htrace
    _ = LinearMap.trace ℝ (EuclideanSpace ℝ (Fin n))
          (Matrix.toEuclideanLin (Xᵀ * X)) := by
          rw [hcomp]
    _ = Matrix.trace (Xᵀ * X) := by
          rw [LinearMap.trace_eq_matrix_trace ℝ ((EuclideanSpace.basisFun (Fin n) ℝ).toBasis)]
          simp [Matrix.toEuclideanLin_eq_toLin_orthonormal]

/-- Helper for Theorem 7.4: scaling Euclidean coordinate vectors by `√2` doubles the underlying
dot product. -/
lemma scaled_toLp_inner_eq_two_dotProduct {k : ℕ} (u v : Fin k → ℝ) :
    inner ℝ ((Real.sqrt 2 : ℝ) • WithLp.toLp 2 u) ((Real.sqrt 2 : ℝ) • WithLp.toLp 2 v) =
      2 * dotProduct u v := by
  -- Rewrite the Euclidean inner product in coordinates and then collapse the two `√2` factors.
  rw [inner_smul_left, inner_smul_right]
  have hsqrt : (Real.sqrt 2 : ℝ) * Real.sqrt 2 = 2 := by
    nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
  have hinner : inner ℝ (WithLp.toLp 2 u) (WithLp.toLp 2 v) = dotProduct u v := by
    simpa [dotProduct_comm] using (EuclideanSpace.inner_toLp_toLp u v)
  have hstar : (starRingEnd ℝ) (Real.sqrt 2) = Real.sqrt 2 := by
    simp
  rw [hinner, hstar]
  ring_nf
  rw [pow_two, hsqrt]
  ring

/-- Helper for Theorem 7.4: after scaling by `√2`, the active top and bottom block families from
the common dilation basis have the Kronecker-delta inner products needed for orthonormality. -/
lemma scaled_active_head_block_inner_eq_ite
    (X Y : Matrix (Fin m) (Fin n) ℝ)
    (Q : Matrix.orthogonalGroup (Fin (m + n)) ℝ)
    (hQX :
      (symmetric_dilation X : Matrix (Fin (m + n)) (Fin (m + n)) ℝ) =
        (Q : Matrix (Fin (m + n)) (Fin (m + n)) ℝ) *
          Matrix.diagonal (signed_singular_value_profile X) *
          ((Q : Matrix (Fin (m + n)) (Fin (m + n)) ℝ)ᵀ))
    (hQY :
      (symmetric_dilation Y : Matrix (Fin (m + n)) (Fin (m + n)) ℝ) =
        (Q : Matrix (Fin (m + n)) (Fin (m + n)) ℝ) *
          Matrix.diagonal (signed_singular_value_profile Y) *
          ((Q : Matrix (Fin (m + n)) (Fin (m + n)) ℝ)ᵀ))
    (i j : Fin (min m n))
    (hi : singular_value_function X i ≠ 0 ∨ singular_value_function Y i ≠ 0)
    (hj : singular_value_function X j ≠ 0 ∨ singular_value_function Y j ≠ 0) :
    let ji : Fin (m + n) := ⟨i.1, by
      omega⟩
    let jj : Fin (m + n) := ⟨j.1, by
      omega⟩
    let qi : Fin (m + n) → ℝ := (Q : Matrix (Fin (m + n)) (Fin (m + n)) ℝ).col ji
    let qj : Fin (m + n) → ℝ := (Q : Matrix (Fin (m + n)) (Fin (m + n)) ℝ).col jj
    let ui : Fin m → ℝ := fun r ↦ qi (finSumFinEquiv (Sum.inl r))
    let vi : Fin n → ℝ := fun c ↦ qi (finSumFinEquiv (Sum.inr c))
    let uj : Fin m → ℝ := fun r ↦ qj (finSumFinEquiv (Sum.inl r))
    let vj : Fin n → ℝ := fun c ↦ qj (finSumFinEquiv (Sum.inr c))
    inner ℝ ((Real.sqrt 2 : ℝ) • WithLp.toLp 2 ui)
        ((Real.sqrt 2 : ℝ) • WithLp.toLp 2 uj) = (if i = j then 1 else 0) ∧
      inner ℝ ((Real.sqrt 2 : ℝ) • WithLp.toLp 2 vi)
        ((Real.sqrt 2 : ℝ) • WithLp.toLp 2 vj) = (if i = j then 1 else 0) := by
  dsimp
  let ji : Fin (m + n) := ⟨i.1, by
    omega⟩
  let jj : Fin (m + n) := ⟨j.1, by
    omega⟩
  let qi : Fin (m + n) → ℝ := (Q : Matrix (Fin (m + n)) (Fin (m + n)) ℝ).col ji
  let qj : Fin (m + n) → ℝ := (Q : Matrix (Fin (m + n)) (Fin (m + n)) ℝ).col jj
  let ui : Fin m → ℝ := fun r ↦ qi (finSumFinEquiv (Sum.inl r))
  let vi : Fin n → ℝ := fun c ↦ qi (finSumFinEquiv (Sum.inr c))
  let uj : Fin m → ℝ := fun r ↦ qj (finSumFinEquiv (Sum.inl r))
  let vj : Fin n → ℝ := fun c ↦ qj (finSumFinEquiv (Sum.inr c))
  rcases
      active_head_dilation_column_block_dotProduct_eq_half_ite
        (m := m) (n := n) X Y Q hQX hQY i j hi hj with
    ⟨hui, hvi⟩
  constructor
  · -- The active top blocks already have `1/2` Gram entries, so scaling by `√2` normalizes them.
    rw [scaled_toLp_inner_eq_two_dotProduct]
    change 2 * dotProduct ui uj = (if i = j then 1 else 0)
    by_cases hij : i = j
    · subst hij
      have hui' : dotProduct ui uj = (1 : ℝ) / 2 := by
        simpa [ui, uj] using hui
      rw [if_pos rfl]
      nlinarith [hui']
    · rw [if_neg hij] at hui ⊢
      have hui' : dotProduct ui uj = 0 := by
        simpa [ui, uj] using hui
      nlinarith [hui']
  · -- The same scaling argument upgrades the bottom-block Gram identities to orthonormal form.
    rw [scaled_toLp_inner_eq_two_dotProduct]
    change 2 * dotProduct vi vj = (if i = j then 1 else 0)
    by_cases hij : i = j
    · subst hij
      have hvi' : dotProduct vi vj = (1 : ℝ) / 2 := by
        simpa [vi, vj] using hvi
      rw [if_pos rfl]
      nlinarith [hvi']
    · rw [if_neg hij] at hvi ⊢
      have hvi' : dotProduct vi vj = 0 := by
        simpa [vi, vj] using hvi
      nlinarith [hvi']

/-- Helper for Theorem 7.4: the active singular-value indices are those where at least one of the
two matrices has a nonzero singular value. -/
def common_active_singular_index_set
    (X Y : Matrix (Fin m) (Fin n) ℝ) : Set (Fin (min m n)) :=
  {i | singular_value_function X i ≠ 0 ∨ singular_value_function Y i ≠ 0}

/-- Helper for Theorem 7.4: after scaling by `√2`, the active left singular directions extracted
from the common dilation basis form an orthonormal family. -/
lemma scaled_active_left_family_orthonormal
    (X Y : Matrix (Fin m) (Fin n) ℝ)
    (Q : Matrix.orthogonalGroup (Fin (m + n)) ℝ)
    (hQX :
      (symmetric_dilation X : Matrix (Fin (m + n)) (Fin (m + n)) ℝ) =
        (Q : Matrix (Fin (m + n)) (Fin (m + n)) ℝ) *
          Matrix.diagonal (signed_singular_value_profile X) *
          ((Q : Matrix (Fin (m + n)) (Fin (m + n)) ℝ)ᵀ))
    (hQY :
      (symmetric_dilation Y : Matrix (Fin (m + n)) (Fin (m + n)) ℝ) =
        (Q : Matrix (Fin (m + n)) (Fin (m + n)) ℝ) *
          Matrix.diagonal (signed_singular_value_profile Y) *
          ((Q : Matrix (Fin (m + n)) (Fin (m + n)) ℝ)ᵀ)) :
    Orthonormal ℝ
      (fun i : common_active_singular_index_set X Y ↦
        (Real.sqrt 2 : ℝ) •
          WithLp.toLp 2
            (fun r ↦
              ((Q : Matrix (Fin (m + n)) (Fin (m + n)) ℝ).col
                ⟨i.1.1, by
                  omega⟩) (finSumFinEquiv (Sum.inl r)))) := by
  let u :
      common_active_singular_index_set X Y → EuclideanSpace ℝ (Fin m) :=
    fun i ↦
      (Real.sqrt 2 : ℝ) •
        WithLp.toLp 2
          (fun r ↦
            ((Q : Matrix (Fin (m + n)) (Fin (m + n)) ℝ).col
              ⟨i.1.1, by
                omega⟩) (finSumFinEquiv (Sum.inl r)))
  change Orthonormal ℝ u
  refine ⟨?_, ?_⟩
  · intro i
    -- Read the diagonal Gram identity for the scaled active left family as a norm computation.
    have hu :
        inner ℝ (u i) (u i) = 1 := by
      simpa [u] using
        (scaled_active_head_block_inner_eq_ite
          (m := m) (n := n) X Y Q hQX hQY i.1 i.1 i.2 i.2).1
    have hsq : ‖u i‖ ^ (2 : ℕ) = 1 := by
      simpa [real_inner_self_eq_norm_sq] using hu
    have hnonneg : 0 ≤ ‖u i‖ := norm_nonneg (u i)
    nlinarith
  · intro i j hij
    -- Off-diagonal Gram identities give orthogonality of distinct active left directions.
    have hij_val : i.1 ≠ j.1 := by
      intro hij'
      apply hij
      exact Subtype.ext hij'
    have hu :
        inner ℝ (u i) (u j) = 0 := by
      simpa [u, hij_val] using
        (scaled_active_head_block_inner_eq_ite
          (m := m) (n := n) X Y Q hQX hQY i.1 j.1 i.2 j.2).1
    simpa [u] using hu

/-- Helper for Theorem 7.4: after scaling by `√2`, the active right singular directions extracted
from the common dilation basis form an orthonormal family. -/
lemma scaled_active_right_family_orthonormal
    (X Y : Matrix (Fin m) (Fin n) ℝ)
    (Q : Matrix.orthogonalGroup (Fin (m + n)) ℝ)
    (hQX :
      (symmetric_dilation X : Matrix (Fin (m + n)) (Fin (m + n)) ℝ) =
        (Q : Matrix (Fin (m + n)) (Fin (m + n)) ℝ) *
          Matrix.diagonal (signed_singular_value_profile X) *
          ((Q : Matrix (Fin (m + n)) (Fin (m + n)) ℝ)ᵀ))
    (hQY :
      (symmetric_dilation Y : Matrix (Fin (m + n)) (Fin (m + n)) ℝ) =
        (Q : Matrix (Fin (m + n)) (Fin (m + n)) ℝ) *
          Matrix.diagonal (signed_singular_value_profile Y) *
          ((Q : Matrix (Fin (m + n)) (Fin (m + n)) ℝ)ᵀ)) :
    Orthonormal ℝ
      (fun i : common_active_singular_index_set X Y ↦
        (Real.sqrt 2 : ℝ) •
          WithLp.toLp 2
            (fun c ↦
              ((Q : Matrix (Fin (m + n)) (Fin (m + n)) ℝ).col
                ⟨i.1.1, by
                  omega⟩) (finSumFinEquiv (Sum.inr c)))) := by
  let v :
      common_active_singular_index_set X Y → EuclideanSpace ℝ (Fin n) :=
    fun i ↦
      (Real.sqrt 2 : ℝ) •
        WithLp.toLp 2
          (fun c ↦
            ((Q : Matrix (Fin (m + n)) (Fin (m + n)) ℝ).col
              ⟨i.1.1, by
                omega⟩) (finSumFinEquiv (Sum.inr c)))
  change Orthonormal ℝ v
  refine ⟨?_, ?_⟩
  · intro i
    -- The diagonal Gram identity also normalizes each active right direction.
    have hv :
        inner ℝ (v i) (v i) = 1 := by
      simpa [v] using
        (scaled_active_head_block_inner_eq_ite
          (m := m) (n := n) X Y Q hQX hQY i.1 i.1 i.2 i.2).2
    have hsq : ‖v i‖ ^ (2 : ℕ) = 1 := by
      simpa [real_inner_self_eq_norm_sq] using hv
    have hnonneg : 0 ≤ ‖v i‖ := norm_nonneg (v i)
    nlinarith
  · intro i j hij
    -- Distinct active right directions are orthogonal by the off-diagonal block formula.
    have hij_val : i.1 ≠ j.1 := by
      intro hij'
      apply hij
      exact Subtype.ext hij'
    have hv :
        inner ℝ (v i) (v j) = 0 := by
      simpa [v, hij_val] using
        (scaled_active_head_block_inner_eq_ite
          (m := m) (n := n) X Y Q hQX hQY i.1 j.1 i.2 j.2).2
    simpa [v] using hv

/-- Helper for Theorem 7.4: inactive head columns and their sign companions lie in the joint
zero-eigenspaces of both block symmetric dilations. -/
lemma inactive_head_columns_are_joint_zero_eigenvectors
    (X Y : Matrix (Fin m) (Fin n) ℝ)
    (Q : Matrix.orthogonalGroup (Fin (m + n)) ℝ)
    (hQX :
      (symmetric_dilation X : Matrix (Fin (m + n)) (Fin (m + n)) ℝ) =
        (Q : Matrix (Fin (m + n)) (Fin (m + n)) ℝ) *
          Matrix.diagonal (signed_singular_value_profile X) *
          ((Q : Matrix (Fin (m + n)) (Fin (m + n)) ℝ)ᵀ))
    (hQY :
      (symmetric_dilation Y : Matrix (Fin (m + n)) (Fin (m + n)) ℝ) =
        (Q : Matrix (Fin (m + n)) (Fin (m + n)) ℝ) *
          Matrix.diagonal (signed_singular_value_profile Y) *
          ((Q : Matrix (Fin (m + n)) (Fin (m + n)) ℝ)ᵀ))
    (i : Fin (min m n))
    (hXi : singular_value_function X i = 0)
    (hYi : singular_value_function Y i = 0) :
    let j : Fin (m + n) := ⟨i.1, by
      omega⟩
    let q : Fin (m + n) → ℝ := (Q : Matrix (Fin (m + n)) (Fin (m + n)) ℝ).col j
    let u : Fin m → ℝ := fun r ↦ q (finSumFinEquiv (Sum.inl r))
    let v : Fin n → ℝ := fun c ↦ q (finSumFinEquiv (Sum.inr c))
    block_symmetric_dilation X *ᵥ Sum.elim u v = 0 ∧
      block_symmetric_dilation Y *ᵥ Sum.elim u v = 0 ∧
      block_symmetric_dilation X *ᵥ Sum.elim u (-v) = 0 ∧
      block_symmetric_dilation Y *ᵥ Sum.elim u (-v) = 0 := by
  dsimp
  let j : Fin (m + n) := ⟨i.1, by
    omega⟩
  let q : Fin (m + n) → ℝ := (Q : Matrix (Fin (m + n)) (Fin (m + n)) ℝ).col j
  let u : Fin m → ℝ := fun r ↦ q (finSumFinEquiv (Sum.inl r))
  let v : Fin n → ℝ := fun c ↦ q (finSumFinEquiv (Sum.inr c))
  rcases
      head_dilation_column_block_eigenvector_equations
        (m := m) (n := n) X Y Q hQX hQY i with
    ⟨hheadX, hheadY⟩
  rcases
      head_dilation_column_block_sign_companion_equations
        (m := m) (n := n) X Y Q hQX hQY i with
    ⟨hcompX, hcompY⟩
  have hXi' : (Matrix.toEuclideanLin X).singularValues i = 0 := by
    simpa [singular_value_function_apply] using hXi
  have hYi' : (Matrix.toEuclideanLin Y).singularValues i = 0 := by
    simpa [singular_value_function_apply] using hYi
  constructor
  · -- The inactive head column has eigenvalue `0` for the `X` dilation.
    simpa [hXi'] using hheadX
  · constructor
    · -- The same inactive head column also has eigenvalue `0` for the `Y` dilation.
      simpa [hYi'] using hheadY
    · constructor
      · -- The sign companion inherits the same vanishing eigenvalue for the `X` dilation.
        simpa [hXi'] using hcompX
      · -- The sign companion is likewise killed by the `Y` dilation.
        simpa [hYi'] using hcompY

/-- Helper for Theorem 7.4: the active left and right singular directions indexed by the common
head coordinates extend to orthonormal bases on `Fin m` and `Fin n`. -/
lemma active_head_coordinate_basis_extensions
    (X Y : Matrix (Fin m) (Fin n) ℝ)
    (Q : Matrix.orthogonalGroup (Fin (m + n)) ℝ)
    (hQX :
      (symmetric_dilation X : Matrix (Fin (m + n)) (Fin (m + n)) ℝ) =
        (Q : Matrix (Fin (m + n)) (Fin (m + n)) ℝ) *
          Matrix.diagonal (signed_singular_value_profile X) *
          ((Q : Matrix (Fin (m + n)) (Fin (m + n)) ℝ)ᵀ))
    (hQY :
      (symmetric_dilation Y : Matrix (Fin (m + n)) (Fin (m + n)) ℝ) =
        (Q : Matrix (Fin (m + n)) (Fin (m + n)) ℝ) *
          Matrix.diagonal (signed_singular_value_profile Y) *
          ((Q : Matrix (Fin (m + n)) (Fin (m + n)) ℝ)ᵀ)) :
    ∃ bU : OrthonormalBasis (Fin m) ℝ (EuclideanSpace ℝ (Fin m)),
      ∃ bV : OrthonormalBasis (Fin n) ℝ (EuclideanSpace ℝ (Fin n)),
        (∀ i : common_active_singular_index_set X Y,
          bU ⟨i.1.1, Nat.lt_of_lt_of_le i.1.2 (Nat.min_le_left m n)⟩ =
            (Real.sqrt 2 : ℝ) •
              WithLp.toLp 2
                (fun r ↦
                  ((Q : Matrix (Fin (m + n)) (Fin (m + n)) ℝ).col
                    ⟨i.1.1, by
                      omega⟩) (finSumFinEquiv (Sum.inl r)))) ∧
        (∀ i : common_active_singular_index_set X Y,
          bV ⟨i.1.1, Nat.lt_of_lt_of_le i.1.2 (Nat.min_le_right m n)⟩ =
            (Real.sqrt 2 : ℝ) •
              WithLp.toLp 2
                (fun c ↦
                  ((Q : Matrix (Fin (m + n)) (Fin (m + n)) ℝ).col
                    ⟨i.1.1, by
                      omega⟩) (finSumFinEquiv (Sum.inr c)))) := by
  classical
  let eU : common_active_singular_index_set X Y ↪ Fin m :=
    ⟨fun i ↦ ⟨i.1.1, Nat.lt_of_lt_of_le i.1.2 (Nat.min_le_left m n)⟩,
      by
        intro i j hij
        apply Subtype.ext
        have hij_val : i.1.1 = j.1.1 := by
          simpa using congrArg (fun a : Fin m ↦ a.1) hij
        exact Fin.ext hij_val⟩
  let eV : common_active_singular_index_set X Y ↪ Fin n :=
    ⟨fun i ↦ ⟨i.1.1, Nat.lt_of_lt_of_le i.1.2 (Nat.min_le_right m n)⟩,
      by
        intro i j hij
        apply Subtype.ext
        have hij_val : i.1.1 = j.1.1 := by
          simpa using congrArg (fun a : Fin n ↦ a.1) hij
        exact Fin.ext hij_val⟩
  let uFamily : common_active_singular_index_set X Y → EuclideanSpace ℝ (Fin m) :=
    fun i ↦
      (Real.sqrt 2 : ℝ) •
        WithLp.toLp 2
          (fun r ↦
            ((Q : Matrix (Fin (m + n)) (Fin (m + n)) ℝ).col
              ⟨i.1.1, by
                omega⟩) (finSumFinEquiv (Sum.inl r)))
  let vFamily : common_active_singular_index_set X Y → EuclideanSpace ℝ (Fin n) :=
    fun i ↦
      (Real.sqrt 2 : ℝ) •
        WithLp.toLp 2
          (fun c ↦
            ((Q : Matrix (Fin (m + n)) (Fin (m + n)) ℝ).col
              ⟨i.1.1, by
                omega⟩) (finSumFinEquiv (Sum.inr c)))
  let invU : Set.range eU → common_active_singular_index_set X Y :=
    fun x ↦ Classical.choose x.2
  let invV : Set.range eV → common_active_singular_index_set X Y :=
    fun x ↦ Classical.choose x.2
  let totalU : Fin m → EuclideanSpace ℝ (Fin m) :=
    fun j ↦
      if h : j ∈ Set.range eU then uFamily (invU ⟨j, h⟩) else 0
  let totalV : Fin n → EuclideanSpace ℝ (Fin n) :=
    fun j ↦
      if h : j ∈ Set.range eV then vFamily (invV ⟨j, h⟩) else 0
  have huFamily : Orthonormal ℝ uFamily := by
    -- The extracted active left family is already orthonormal after the `√2` rescaling.
    simpa [uFamily] using
      scaled_active_left_family_orthonormal (m := m) (n := n) X Y Q hQX hQY
  have hvFamily : Orthonormal ℝ vFamily := by
    -- The same rescaling gives the orthonormal active right family.
    simpa [vFamily] using
      scaled_active_right_family_orthonormal (m := m) (n := n) X Y Q hQX hQY
  have hinvU : Function.Injective invU := by
    intro x y hxy
    apply Subtype.ext
    have hx : eU (invU x) = x.1 := Classical.choose_spec x.2
    have hy : eU (invU y) = y.1 := Classical.choose_spec y.2
    calc
      x.1 = eU (invU x) := by simp [hx]
      _ = eU (invU y) := by rw [hxy]
      _ = y.1 := by simp [hy]
  have hinvV : Function.Injective invV := by
    intro x y hxy
    apply Subtype.ext
    have hx : eV (invV x) = x.1 := Classical.choose_spec x.2
    have hy : eV (invV y) = y.1 := Classical.choose_spec y.2
    calc
      x.1 = eV (invV x) := by simp [hx]
      _ = eV (invV y) := by rw [hxy]
      _ = y.1 := by simp [hy]
  have htotalU :
      Orthonormal ℝ ((Set.range eU).restrict totalU) := by
    have hrestrict :
        (Set.range eU).restrict totalU = fun x : Set.range eU ↦ uFamily (invU x) := by
      funext x
      rw [Set.restrict_apply]
      dsimp [totalU]
      split_ifs with hx
      · have hxsub : (⟨x.1, hx⟩ : Set.range eU) = x := by
          apply Subtype.ext
          rfl
        simp [hxsub, invU]
      · exact (hx x.2).elim
    -- Rewrite the restricted family through the inverse parametrization of the active range.
    rw [hrestrict]
    simpa [Function.comp] using huFamily.comp invU hinvU
  have htotalV :
      Orthonormal ℝ ((Set.range eV).restrict totalV) := by
    have hrestrict :
        (Set.range eV).restrict totalV = fun x : Set.range eV ↦ vFamily (invV x) := by
      funext x
      rw [Set.restrict_apply]
      dsimp [totalV]
      split_ifs with hx
      · have hxsub : (⟨x.1, hx⟩ : Set.range eV) = x := by
          apply Subtype.ext
          rfl
        simp [hxsub, invV]
      · exact (hx x.2).elim
    -- The right active family is transferred to the embedded head coordinates in the same way.
    rw [hrestrict]
    simpa [Function.comp] using hvFamily.comp invV hinvV
  have hcardU : Module.finrank ℝ (EuclideanSpace ℝ (Fin m)) = Fintype.card (Fin m) := by
    simp
  have hcardV : Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) = Fintype.card (Fin n) := by
    simp
  rcases
      Orthonormal.exists_orthonormalBasis_extension_of_card_eq
        (𝕜 := ℝ) (E := EuclideanSpace ℝ (Fin m)) (ι := Fin m) hcardU htotalU with
    ⟨bU, hbU⟩
  rcases
      Orthonormal.exists_orthonormalBasis_extension_of_card_eq
        (𝕜 := ℝ) (E := EuclideanSpace ℝ (Fin n)) (ι := Fin n) hcardV htotalV with
    ⟨bV, hbV⟩
  refine ⟨bU, bV, ?_, ?_⟩
  · intro i
    have hi : eU i ∈ Set.range eU := ⟨i, rfl⟩
    have hpreimage : invU ⟨eU i, hi⟩ = i := by
      apply eU.injective
      exact Classical.choose_spec hi
    -- On active head coordinates, the extended left basis agrees with the extracted family.
    specialize hbU (eU i) hi
    simpa [totalU, hi, hpreimage, uFamily] using hbU
  · intro i
    have hi : eV i ∈ Set.range eV := ⟨i, rfl⟩
    have hpreimage : invV ⟨eV i, hi⟩ = i := by
      apply eV.injective
      exact Classical.choose_spec hi
    -- The same agreement holds for the extended right basis.
    specialize hbV (eV i) hi
    simpa [totalV, hi, hpreimage, vFamily] using hbV

/-- Helper for Theorem 7.4: once the active families are extended to head-coordinate bases, the
common singular-vector equations transfer to those basis columns verbatim. -/
lemma active_basis_extension_column_equations
    (X Y : Matrix (Fin m) (Fin n) ℝ)
    (Q : Matrix.orthogonalGroup (Fin (m + n)) ℝ)
    (hQX :
      (symmetric_dilation X : Matrix (Fin (m + n)) (Fin (m + n)) ℝ) =
        (Q : Matrix (Fin (m + n)) (Fin (m + n)) ℝ) *
          Matrix.diagonal (signed_singular_value_profile X) *
          ((Q : Matrix (Fin (m + n)) (Fin (m + n)) ℝ)ᵀ))
    (hQY :
      (symmetric_dilation Y : Matrix (Fin (m + n)) (Fin (m + n)) ℝ) =
        (Q : Matrix (Fin (m + n)) (Fin (m + n)) ℝ) *
          Matrix.diagonal (signed_singular_value_profile Y) *
          ((Q : Matrix (Fin (m + n)) (Fin (m + n)) ℝ)ᵀ))
    (bU : OrthonormalBasis (Fin m) ℝ (EuclideanSpace ℝ (Fin m)))
    (bV : OrthonormalBasis (Fin n) ℝ (EuclideanSpace ℝ (Fin n)))
    (hbU :
      ∀ i : common_active_singular_index_set X Y,
        bU ⟨i.1.1, Nat.lt_of_lt_of_le i.1.2 (Nat.min_le_left m n)⟩ =
          (Real.sqrt 2 : ℝ) •
            WithLp.toLp 2
              (fun r ↦
                ((Q : Matrix (Fin (m + n)) (Fin (m + n)) ℝ).col
                  ⟨i.1.1, by
                    omega⟩) (finSumFinEquiv (Sum.inl r))))
    (hbV :
      ∀ i : common_active_singular_index_set X Y,
        bV ⟨i.1.1, Nat.lt_of_lt_of_le i.1.2 (Nat.min_le_right m n)⟩ =
          (Real.sqrt 2 : ℝ) •
            WithLp.toLp 2
              (fun c ↦
                ((Q : Matrix (Fin (m + n)) (Fin (m + n)) ℝ).col
                  ⟨i.1.1, by
                    omega⟩) (finSumFinEquiv (Sum.inr c)))) :
    ∀ i : common_active_singular_index_set X Y,
      Matrix.toEuclideanLin X
          (bV ⟨i.1.1, Nat.lt_of_lt_of_le i.1.2 (Nat.min_le_right m n)⟩) =
        singular_value_function X i.1 •
          bU ⟨i.1.1, Nat.lt_of_lt_of_le i.1.2 (Nat.min_le_left m n)⟩ ∧
      Matrix.toEuclideanLin Xᵀ
          (bU ⟨i.1.1, Nat.lt_of_lt_of_le i.1.2 (Nat.min_le_left m n)⟩) =
        singular_value_function X i.1 •
          bV ⟨i.1.1, Nat.lt_of_lt_of_le i.1.2 (Nat.min_le_right m n)⟩ ∧
      Matrix.toEuclideanLin Y
          (bV ⟨i.1.1, Nat.lt_of_lt_of_le i.1.2 (Nat.min_le_right m n)⟩) =
        singular_value_function Y i.1 •
          bU ⟨i.1.1, Nat.lt_of_lt_of_le i.1.2 (Nat.min_le_left m n)⟩ ∧
      Matrix.toEuclideanLin Yᵀ
          (bU ⟨i.1.1, Nat.lt_of_lt_of_le i.1.2 (Nat.min_le_left m n)⟩) =
        singular_value_function Y i.1 •
          bV ⟨i.1.1, Nat.lt_of_lt_of_le i.1.2 (Nat.min_le_right m n)⟩ := by
  intro i
  rcases
      head_dilation_column_common_singular_vector_equations_euclidean
        (m := m) (n := n) X Y Q hQX hQY i.1 with
    ⟨hX, hXt, hY, hYt⟩
  constructor
  · -- Rewrite the active right basis vector back to the extracted head column and scale the
    -- Euclidean singular-vector equation by `√2`.
    calc
      Matrix.toEuclideanLin X
          (bV ⟨i.1.1, Nat.lt_of_lt_of_le i.1.2 (Nat.min_le_right m n)⟩)
        = Matrix.toEuclideanLin X
            ((Real.sqrt 2 : ℝ) •
              WithLp.toLp 2
                (fun c ↦
                  ((Q : Matrix (Fin (m + n)) (Fin (m + n)) ℝ).col
                    ⟨i.1.1, by
                      omega⟩) (finSumFinEquiv (Sum.inr c)))) := by
              rw [hbV i]
      _ = (Real.sqrt 2 : ℝ) •
            Matrix.toEuclideanLin X
              (WithLp.toLp 2
                (fun c ↦
                  ((Q : Matrix (Fin (m + n)) (Fin (m + n)) ℝ).col
                    ⟨i.1.1, by
                      omega⟩) (finSumFinEquiv (Sum.inr c)))) := by
              rw [map_smul]
      _ = (Real.sqrt 2 : ℝ) •
            (singular_value_function X i.1 •
              WithLp.toLp 2
                (fun r ↦
                  ((Q : Matrix (Fin (m + n)) (Fin (m + n)) ℝ).col
                    ⟨i.1.1, by
                      omega⟩) (finSumFinEquiv (Sum.inl r)))) := by
              rw [hX]
      _ = singular_value_function X i.1 •
            ((Real.sqrt 2 : ℝ) •
              WithLp.toLp 2
                (fun r ↦
                  ((Q : Matrix (Fin (m + n)) (Fin (m + n)) ℝ).col
                    ⟨i.1.1, by
                      omega⟩) (finSumFinEquiv (Sum.inl r)))) := by
              simp [smul_smul, mul_comm, mul_left_comm, mul_assoc]
      _ = singular_value_function X i.1 •
            bU ⟨i.1.1, Nat.lt_of_lt_of_le i.1.2 (Nat.min_le_left m n)⟩ := by
              rw [hbU i]
  · constructor
    · -- The transpose equation is transferred to the active basis coordinates in the same way.
      calc
        Matrix.toEuclideanLin Xᵀ
            (bU ⟨i.1.1, Nat.lt_of_lt_of_le i.1.2 (Nat.min_le_left m n)⟩)
          = Matrix.toEuclideanLin Xᵀ
              ((Real.sqrt 2 : ℝ) •
                WithLp.toLp 2
                  (fun r ↦
                    ((Q : Matrix (Fin (m + n)) (Fin (m + n)) ℝ).col
                      ⟨i.1.1, by
                        omega⟩) (finSumFinEquiv (Sum.inl r)))) := by
                rw [hbU i]
        _ = (Real.sqrt 2 : ℝ) •
              Matrix.toEuclideanLin Xᵀ
                (WithLp.toLp 2
                  (fun r ↦
                    ((Q : Matrix (Fin (m + n)) (Fin (m + n)) ℝ).col
                      ⟨i.1.1, by
                        omega⟩) (finSumFinEquiv (Sum.inl r)))) := by
                rw [map_smul]
        _ = (Real.sqrt 2 : ℝ) •
              (singular_value_function X i.1 •
                WithLp.toLp 2
                  (fun c ↦
                    ((Q : Matrix (Fin (m + n)) (Fin (m + n)) ℝ).col
                      ⟨i.1.1, by
                        omega⟩) (finSumFinEquiv (Sum.inr c)))) := by
                rw [hXt]
        _ = singular_value_function X i.1 •
              ((Real.sqrt 2 : ℝ) •
                WithLp.toLp 2
                  (fun c ↦
                    ((Q : Matrix (Fin (m + n)) (Fin (m + n)) ℝ).col
                      ⟨i.1.1, by
                        omega⟩) (finSumFinEquiv (Sum.inr c)))) := by
                simp [smul_smul, mul_comm, mul_left_comm, mul_assoc]
        _ = singular_value_function X i.1 •
              bV ⟨i.1.1, Nat.lt_of_lt_of_le i.1.2 (Nat.min_le_right m n)⟩ := by
                rw [hbV i]
    · constructor
      · -- The common `Y` equation is transferred with the same basis substitution.
        calc
          Matrix.toEuclideanLin Y
              (bV ⟨i.1.1, Nat.lt_of_lt_of_le i.1.2 (Nat.min_le_right m n)⟩)
            = Matrix.toEuclideanLin Y
                ((Real.sqrt 2 : ℝ) •
                  WithLp.toLp 2
                    (fun c ↦
                      ((Q : Matrix (Fin (m + n)) (Fin (m + n)) ℝ).col
                        ⟨i.1.1, by
                          omega⟩) (finSumFinEquiv (Sum.inr c)))) := by
                  rw [hbV i]
          _ = (Real.sqrt 2 : ℝ) •
                Matrix.toEuclideanLin Y
                  (WithLp.toLp 2
                    (fun c ↦
                      ((Q : Matrix (Fin (m + n)) (Fin (m + n)) ℝ).col
                        ⟨i.1.1, by
                          omega⟩) (finSumFinEquiv (Sum.inr c)))) := by
                  rw [map_smul]
          _ = (Real.sqrt 2 : ℝ) •
                (singular_value_function Y i.1 •
                  WithLp.toLp 2
                    (fun r ↦
                      ((Q : Matrix (Fin (m + n)) (Fin (m + n)) ℝ).col
                        ⟨i.1.1, by
                          omega⟩) (finSumFinEquiv (Sum.inl r)))) := by
                  rw [hY]
          _ = singular_value_function Y i.1 •
                ((Real.sqrt 2 : ℝ) •
                  WithLp.toLp 2
                    (fun r ↦
                      ((Q : Matrix (Fin (m + n)) (Fin (m + n)) ℝ).col
                        ⟨i.1.1, by
                          omega⟩) (finSumFinEquiv (Sum.inl r)))) := by
                  simp [smul_smul, mul_comm, mul_left_comm, mul_assoc]
          _ = singular_value_function Y i.1 •
                bU ⟨i.1.1, Nat.lt_of_lt_of_le i.1.2 (Nat.min_le_left m n)⟩ := by
                  rw [hbU i]
      · -- The transpose equation for `Y` closes the active basis-column package.
        calc
          Matrix.toEuclideanLin Yᵀ
              (bU ⟨i.1.1, Nat.lt_of_lt_of_le i.1.2 (Nat.min_le_left m n)⟩)
            = Matrix.toEuclideanLin Yᵀ
                ((Real.sqrt 2 : ℝ) •
                  WithLp.toLp 2
                    (fun r ↦
                      ((Q : Matrix (Fin (m + n)) (Fin (m + n)) ℝ).col
                        ⟨i.1.1, by
                          omega⟩) (finSumFinEquiv (Sum.inl r)))) := by
                  rw [hbU i]
          _ = (Real.sqrt 2 : ℝ) •
                Matrix.toEuclideanLin Yᵀ
                  (WithLp.toLp 2
                    (fun r ↦
                      ((Q : Matrix (Fin (m + n)) (Fin (m + n)) ℝ).col
                        ⟨i.1.1, by
                          omega⟩) (finSumFinEquiv (Sum.inl r)))) := by
                  rw [map_smul]
          _ = (Real.sqrt 2 : ℝ) •
                (singular_value_function Y i.1 •
                  WithLp.toLp 2
                    (fun c ↦
                      ((Q : Matrix (Fin (m + n)) (Fin (m + n)) ℝ).col
                        ⟨i.1.1, by
                          omega⟩) (finSumFinEquiv (Sum.inr c)))) := by
                  rw [hYt]
          _ = singular_value_function Y i.1 •
                ((Real.sqrt 2 : ℝ) •
                  WithLp.toLp 2
                    (fun c ↦
                      ((Q : Matrix (Fin (m + n)) (Fin (m + n)) ℝ).col
                        ⟨i.1.1, by
                          omega⟩) (finSumFinEquiv (Sum.inr c)))) := by
                  simp [smul_smul, mul_comm, mul_left_comm, mul_assoc]
          _ = singular_value_function Y i.1 •
                bV ⟨i.1.1, Nat.lt_of_lt_of_le i.1.2 (Nat.min_le_right m n)⟩ := by
                  rw [hbV i]

/-- Helper for Theorem 7.4: the active right basis columns carry exactly the squared singular-value
mass of `X` and `Y`. -/
lemma active_basis_extension_sq_norms
    (X Y : Matrix (Fin m) (Fin n) ℝ)
    (bU : OrthonormalBasis (Fin m) ℝ (EuclideanSpace ℝ (Fin m)))
    (bV : OrthonormalBasis (Fin n) ℝ (EuclideanSpace ℝ (Fin n)))
    (eU : common_active_singular_index_set X Y ↪ Fin m)
    (eV : common_active_singular_index_set X Y ↪ Fin n)
    (hactive_columns :
      ∀ i : common_active_singular_index_set X Y,
        Matrix.toEuclideanLin X (bV (eV i)) =
          singular_value_function X i.1 • bU (eU i) ∧
        Matrix.toEuclideanLin Xᵀ (bU (eU i)) =
          singular_value_function X i.1 • bV (eV i) ∧
        Matrix.toEuclideanLin Y (bV (eV i)) =
          singular_value_function Y i.1 • bU (eU i) ∧
        Matrix.toEuclideanLin Yᵀ (bU (eU i)) =
          singular_value_function Y i.1 • bV (eV i)) :
    ∀ i : common_active_singular_index_set X Y,
      ‖Matrix.toEuclideanLin X (bV (eV i))‖ ^ (2 : ℕ) =
          singular_value_function X i.1 ^ (2 : ℕ) ∧
        ‖Matrix.toEuclideanLin Y (bV (eV i))‖ ^ (2 : ℕ) =
          singular_value_function Y i.1 ^ (2 : ℕ) := by
  intro i
  rcases hactive_columns i with ⟨hX, _, hY, _⟩
  constructor
  · -- Taking norms of the active `X` column equation collapses the basis vector to unit norm.
    rw [hX, norm_smul]
    simp [bU.orthonormal.1 (eU i)]
  · -- The same norm computation on the active `Y` column gives the second square identity.
    rw [hY, norm_smul]
    simp [bU.orthonormal.1 (eU i)]

/-- Helper for Theorem 7.4: exact Frobenius trace exhaustion forces every right basis column
outside the active range to lie in the common kernels of `X` and `Y`. -/
lemma basis_extension_right_complement_common_kernel_from_trace_exhaustion
    (X Y : Matrix (Fin m) (Fin n) ℝ)
    (bV : OrthonormalBasis (Fin n) ℝ (EuclideanSpace ℝ (Fin n)))
    (eV : common_active_singular_index_set X Y ↪ Fin n)
    (hactive_sq_norms :
      ∀ i : common_active_singular_index_set X Y,
        ‖Matrix.toEuclideanLin X (bV (eV i))‖ ^ (2 : ℕ) =
            singular_value_function X i.1 ^ (2 : ℕ) ∧
          ‖Matrix.toEuclideanLin Y (bV (eV i))‖ ^ (2 : ℕ) =
            singular_value_function Y i.1 ^ (2 : ℕ))
    (hinactive_eq_zero :
      ∀ i : Fin (min m n), i ∉ common_active_singular_index_set X Y →
        singular_value_function X i = 0 ∧ singular_value_function Y i = 0) :
    ∀ j : Fin n, j ∉ Set.range eV →
      Matrix.toEuclideanLin X (bV j) = 0 ∧ Matrix.toEuclideanLin Y (bV j) = 0 := by
  classical
  let gX : Fin n → ℝ := fun j ↦ ‖Matrix.toEuclideanLin X (bV j)‖ ^ (2 : ℕ)
  let gY : Fin n → ℝ := fun j ↦ ‖Matrix.toEuclideanLin Y (bV j)‖ ^ (2 : ℕ)
  have hactive_sumX :
      (Finset.univ.image eV).sum gX =
        ∑ i : common_active_singular_index_set X Y,
          singular_value_function X i.1 ^ (2 : ℕ) := by
    -- Reindex the active-range sum along the embedding `eV`.
    calc
      (Finset.univ.image eV).sum gX
        = ∑ i : common_active_singular_index_set X Y, gX (eV i) := by
            simpa using
              (Finset.sum_image
                (s := Finset.univ) (g := eV) (f := gX)
                (by
                  intro a ha b hb hab
                  exact eV.injective hab))
      _ = ∑ i : common_active_singular_index_set X Y,
            singular_value_function X i.1 ^ (2 : ℕ) := by
            apply Finset.sum_congr rfl
            intro i hi
            exact (hactive_sq_norms i).1
  have hactive_sumY :
      (Finset.univ.image eV).sum gY =
        ∑ i : common_active_singular_index_set X Y,
          singular_value_function Y i.1 ^ (2 : ℕ) := by
    -- The same reindexing identifies the active `Y` contribution.
    calc
      (Finset.univ.image eV).sum gY
        = ∑ i : common_active_singular_index_set X Y, gY (eV i) := by
            simpa using
              (Finset.sum_image
                (s := Finset.univ) (g := eV) (f := gY)
                (by
                  intro a ha b hb hab
                  exact eV.injective hab))
      _ = ∑ i : common_active_singular_index_set X Y,
            singular_value_function Y i.1 ^ (2 : ℕ) := by
            apply Finset.sum_congr rfl
            intro i hi
            exact (hactive_sq_norms i).2
  have hactive_sigmaX :
      ∑ i : common_active_singular_index_set X Y,
          singular_value_function X i.1 ^ (2 : ℕ) =
        ∑ i : Fin (min m n), singular_value_function X i ^ (2 : ℕ) := by
    let p : Fin (min m n) → Prop := fun i ↦ i ∈ common_active_singular_index_set X Y
    have hactive_filter :
        (Finset.univ.filter p).sum
            (fun i ↦ singular_value_function X i ^ (2 : ℕ)) =
          ∑ i : common_active_singular_index_set X Y,
            singular_value_function X i.1 ^ (2 : ℕ) := by
      simpa using
        (Finset.sum_subtype
          (s := Finset.univ.filter p)
          (h := by
            intro i
            simp [p])
          (f := fun i : Fin (min m n) ↦ singular_value_function X i ^ (2 : ℕ)))
    have hinactive_sum :
        (Finset.univ.filter fun i : Fin (min m n) => ¬ p i).sum
            (fun i ↦ singular_value_function X i ^ (2 : ℕ)) = 0 := by
      apply Finset.sum_eq_zero
      intro i hi
      rcases hinactive_eq_zero i (by simpa using hi) with ⟨hXi, _⟩
      have hXi_sq : singular_value_function X i ^ (2 : ℕ) = 0 := by
        rw [hXi]
        simp
      simpa [singular_value_function_apply] using hXi_sq
    have hsplit :
        (Finset.univ.filter p).sum
            (fun i ↦ singular_value_function X i ^ (2 : ℕ)) +
          (Finset.univ.filter fun i : Fin (min m n) => ¬ p i).sum
            (fun i ↦ singular_value_function X i ^ (2 : ℕ)) =
          ∑ i : Fin (min m n), singular_value_function X i ^ (2 : ℕ) := by
      simpa using
        (Finset.sum_filter_add_sum_filter_not
          (s := Finset.univ)
          (p := p)
          (f := fun i ↦ singular_value_function X i ^ (2 : ℕ)))
    linarith
  have hactive_sigmaY :
      ∑ i : common_active_singular_index_set X Y,
          singular_value_function Y i.1 ^ (2 : ℕ) =
        ∑ i : Fin (min m n), singular_value_function Y i ^ (2 : ℕ) := by
    let p : Fin (min m n) → Prop := fun i ↦ i ∈ common_active_singular_index_set X Y
    have hactive_filter :
        (Finset.univ.filter p).sum
            (fun i ↦ singular_value_function Y i ^ (2 : ℕ)) =
          ∑ i : common_active_singular_index_set X Y,
            singular_value_function Y i.1 ^ (2 : ℕ) := by
      simpa using
        (Finset.sum_subtype
          (s := Finset.univ.filter p)
          (h := by
            intro i
            simp [p])
          (f := fun i : Fin (min m n) ↦ singular_value_function Y i ^ (2 : ℕ)))
    have hinactive_sum :
        (Finset.univ.filter fun i : Fin (min m n) => ¬ p i).sum
            (fun i ↦ singular_value_function Y i ^ (2 : ℕ)) = 0 := by
      apply Finset.sum_eq_zero
      intro i hi
      rcases hinactive_eq_zero i (by simpa using hi) with ⟨_, hYi⟩
      have hYi_sq : singular_value_function Y i ^ (2 : ℕ) = 0 := by
        rw [hYi]
        simp
      simpa [singular_value_function_apply] using hYi_sq
    have hsplit :
        (Finset.univ.filter p).sum
            (fun i ↦ singular_value_function Y i ^ (2 : ℕ)) +
          (Finset.univ.filter fun i : Fin (min m n) => ¬ p i).sum
            (fun i ↦ singular_value_function Y i ^ (2 : ℕ)) =
          ∑ i : Fin (min m n), singular_value_function Y i ^ (2 : ℕ) := by
      simpa using
        (Finset.sum_filter_add_sum_filter_not
          (s := Finset.univ)
          (p := p)
          (f := fun i ↦ singular_value_function Y i ^ (2 : ℕ)))
    linarith
  have htotalX :
      (Finset.univ.image eV).sum gX = ∑ j : Fin n, gX j := by
    -- The active contribution already exhausts the full Frobenius trace of `X`.
    calc
      (Finset.univ.image eV).sum gX
        = ∑ i : common_active_singular_index_set X Y,
            singular_value_function X i.1 ^ (2 : ℕ) := hactive_sumX
      _ = ∑ i : Fin (min m n), singular_value_function X i ^ (2 : ℕ) := hactive_sigmaX
      _ = Matrix.trace (Xᵀ * X) := sum_sq_singular_values_eq_trace_transpose_mul X
      _ = ∑ j : Fin n, gX j := by
            simpa [gX] using
              (sum_sq_norm_toEuclideanLin_on_orthonormalBasis_eq_trace_transpose_mul X bV).symm
  have htotalY :
      (Finset.univ.image eV).sum gY = ∑ j : Fin n, gY j := by
    -- The same exact exhaustion argument works for `Y`.
    calc
      (Finset.univ.image eV).sum gY
        = ∑ i : common_active_singular_index_set X Y,
            singular_value_function Y i.1 ^ (2 : ℕ) := hactive_sumY
      _ = ∑ i : Fin (min m n), singular_value_function Y i ^ (2 : ℕ) := hactive_sigmaY
      _ = Matrix.trace (Yᵀ * Y) := sum_sq_singular_values_eq_trace_transpose_mul Y
      _ = ∑ j : Fin n, gY j := by
            simpa [gY] using
              (sum_sq_norm_toEuclideanLin_on_orthonormalBasis_eq_trace_transpose_mul Y bV).symm
  have hcomp_sumX : (Finset.univ.image eV)ᶜ.sum gX = 0 := by
    -- The complement sum must vanish because the active part already equals the total trace.
    have hsplit := Finset.sum_add_sum_compl (Finset.univ.image eV) gX
    linarith
  have hcomp_sumY : (Finset.univ.image eV)ᶜ.sum gY = 0 := by
    -- The same complement sum vanishes for `Y`.
    have hsplit := Finset.sum_add_sum_compl (Finset.univ.image eV) gY
    linarith
  have hcomp_zeroX :
      ∀ j ∈ (Finset.univ.image eV)ᶜ, gX j = 0 := by
    exact
      (Finset.sum_eq_zero_iff_of_nonneg
        (by
          intro j hj
          positivity)).1 hcomp_sumX
  have hcomp_zeroY :
      ∀ j ∈ (Finset.univ.image eV)ᶜ, gY j = 0 := by
    exact
      (Finset.sum_eq_zero_iff_of_nonneg
        (by
          intro j hj
          positivity)).1 hcomp_sumY
  intro j hj
  have hjmem : j ∈ (Finset.univ.image eV)ᶜ := by
    simp only [Finset.mem_compl, Finset.mem_image, Finset.mem_univ, true_and]
    exact hj
  constructor
  · -- A zero square norm on the complement forces the corresponding `X` column to vanish.
    have hsq : gX j = 0 := hcomp_zeroX j hjmem
    have hnorm : ‖Matrix.toEuclideanLin X (bV j)‖ = 0 := eq_zero_of_pow_eq_zero hsq
    exact norm_eq_zero.mp hnorm
  · -- The identical argument yields the `Y`-kernel statement.
    have hsq : gY j = 0 := hcomp_zeroY j hjmem
    have hnorm : ‖Matrix.toEuclideanLin Y (bV j)‖ = 0 := eq_zero_of_pow_eq_zero hsq
    exact norm_eq_zero.mp hnorm

/-- Helper for Theorem 7.4: if a right basis column is outside the active range, then every entry
in the corresponding column of both rectangular singular-value diagonal matrices vanishes. -/
lemma singular_value_diagonal_entry_eq_zero_of_not_mem_active_range
    (X Y : Matrix (Fin m) (Fin n) ℝ)
    (eV : common_active_singular_index_set X Y ↪ Fin n)
    (heV : ∀ i : common_active_singular_index_set X Y, (eV i).1 = i.1.1) :
    ∀ {j : Fin n}, j ∉ Set.range eV →
      ∀ i : Fin m,
        singular_value_diagonal_matrix X i j = 0 ∧
          singular_value_diagonal_matrix Y i j = 0 := by
  intro j hj i
  constructor
  · -- On a complement column, the diagonal branch would create an active index, contradicting
    -- `j ∉ Set.range eV`; hence every `X` entry in that column is zero.
    rw [singular_value_diagonal_matrix_apply]
    by_cases hij : i.1 = j.1
    · have hjlt : j.1 < min m n := Nat.lt_min.mpr ⟨hij.symm ▸ i.2, j.2⟩
      have hnot_active :
          ¬ (singular_value_function X ⟨j.1, hjlt⟩ ≠ 0 ∨
              singular_value_function Y ⟨j.1, hjlt⟩ ≠ 0) := by
        intro hactive
        let k : common_active_singular_index_set X Y := ⟨⟨j.1, hjlt⟩, hactive⟩
        apply hj
        refine ⟨k, ?_⟩
        apply Fin.ext
        simpa [k, heV k]
      have hXzero : singular_value_function X ⟨j.1, hjlt⟩ = 0 := by
        by_contra hX
        exact hnot_active (Or.inl hX)
      rw [dif_pos hij]
      have hindex :
          (⟨i.1, Nat.lt_min.mpr ⟨i.2, hij ▸ j.2⟩⟩ : Fin (min m n)) = ⟨j.1, hjlt⟩ := by
        apply Fin.ext
        exact hij
      rw [hindex, hXzero]
    · simp [hij]
  · -- The same active-range contradiction makes the `Y` column vanish entrywise as well.
    rw [singular_value_diagonal_matrix_apply]
    by_cases hij : i.1 = j.1
    · have hjlt : j.1 < min m n := Nat.lt_min.mpr ⟨hij.symm ▸ i.2, j.2⟩
      have hnot_active :
          ¬ (singular_value_function X ⟨j.1, hjlt⟩ ≠ 0 ∨
              singular_value_function Y ⟨j.1, hjlt⟩ ≠ 0) := by
        intro hactive
        let k : common_active_singular_index_set X Y := ⟨⟨j.1, hjlt⟩, hactive⟩
        apply hj
        refine ⟨k, ?_⟩
        apply Fin.ext
        simpa [k, heV k]
      have hYzero : singular_value_function Y ⟨j.1, hjlt⟩ = 0 := by
        by_contra hY
        exact hnot_active (Or.inr hY)
      rw [dif_pos hij]
      have hindex :
          (⟨i.1, Nat.lt_min.mpr ⟨i.2, hij ▸ j.2⟩⟩ : Fin (min m n)) = ⟨j.1, hjlt⟩ := by
        apply Fin.ext
        exact hij
      rw [hindex, hYzero]
    · simp [hij]

/-- Helper for Theorem 7.4: once the active columns are matched and the right-basis complement is
in the common kernels, the basis extensions assemble into the rectangular diagonalizations
`X * V = U * Σ_X` and `Y * V = U * Σ_Y`. -/
lemma paired_column_basis_extension_columnwise_diagonalization
    (X Y : Matrix (Fin m) (Fin n) ℝ)
    (bU : OrthonormalBasis (Fin m) ℝ (EuclideanSpace ℝ (Fin m)))
    (bV : OrthonormalBasis (Fin n) ℝ (EuclideanSpace ℝ (Fin n)))
    (eU : common_active_singular_index_set X Y ↪ Fin m)
    (eV : common_active_singular_index_set X Y ↪ Fin n)
    (heU : ∀ i : common_active_singular_index_set X Y, (eU i).1 = i.1.1)
    (heV : ∀ i : common_active_singular_index_set X Y, (eV i).1 = i.1.1)
    (hactive_columns :
      ∀ i : common_active_singular_index_set X Y,
        Matrix.toEuclideanLin X (bV (eV i)) =
          singular_value_function X i.1 • bU (eU i) ∧
        Matrix.toEuclideanLin Xᵀ (bU (eU i)) =
          singular_value_function X i.1 • bV (eV i) ∧
        Matrix.toEuclideanLin Y (bV (eV i)) =
          singular_value_function Y i.1 • bU (eU i) ∧
        Matrix.toEuclideanLin Yᵀ (bU (eU i)) =
          singular_value_function Y i.1 • bV (eV i))
    (hkernel :
      ∀ j : Fin n, j ∉ Set.range eV →
        Matrix.toEuclideanLin X (bV j) = 0 ∧ Matrix.toEuclideanLin Y (bV j) = 0)
    (hzero_diagonal :
      ∀ {j : Fin n}, j ∉ Set.range eV →
        ∀ i : Fin m,
          singular_value_diagonal_matrix X i j = 0 ∧
            singular_value_diagonal_matrix Y i j = 0) :
    ∃ U : Matrix.orthogonalGroup (Fin m) ℝ,
      ∃ V : Matrix.orthogonalGroup (Fin n) ℝ,
        X * (V : Matrix (Fin n) (Fin n) ℝ) =
            (U : Matrix (Fin m) (Fin m) ℝ) * singular_value_diagonal_matrix X ∧
          Y * (V : Matrix (Fin n) (Fin n) ℝ) =
            (U : Matrix (Fin m) (Fin m) ℝ) * singular_value_diagonal_matrix Y := by
  have hUorth :
      (EuclideanSpace.basisFun (Fin m) ℝ).toBasis.toMatrix bU.toBasis ∈
        Matrix.orthogonalGroup (Fin m) ℝ := by
    -- The matrix whose columns are the `bU` basis vectors is orthogonal.
    simpa using
      (EuclideanSpace.basisFun (Fin m) ℝ).toMatrix_orthonormalBasis_mem_orthogonal bU
  have hVorth :
      (EuclideanSpace.basisFun (Fin n) ℝ).toBasis.toMatrix bV.toBasis ∈
        Matrix.orthogonalGroup (Fin n) ℝ := by
    -- The same construction turns `bV` into an orthogonal matrix.
    simpa using
      (EuclideanSpace.basisFun (Fin n) ℝ).toMatrix_orthonormalBasis_mem_orthogonal bV
  let U : Matrix.orthogonalGroup (Fin m) ℝ :=
    ⟨(EuclideanSpace.basisFun (Fin m) ℝ).toBasis.toMatrix bU.toBasis, hUorth⟩
  let V : Matrix.orthogonalGroup (Fin n) ℝ :=
    ⟨(EuclideanSpace.basisFun (Fin n) ℝ).toBasis.toMatrix bV.toBasis, hVorth⟩
  refine ⟨U, V, ?_, ?_⟩
  · ext i j
    by_cases hj : j ∈ Set.range eV
    · rcases hj with ⟨k, rfl⟩
      rcases hactive_columns k with ⟨hX, _, _, _⟩
      have hcoord :
          (Matrix.toEuclideanLin X (bV (eV k))).ofLp i =
            (singular_value_function X k.1 • bU (eU k)).ofLp i := by
        simpa using congrArg (fun v : EuclideanSpace ℝ (Fin m) ↦ v.ofLp i) hX
      have hleft :
          (X * (V : Matrix (Fin n) (Fin n) ℝ)) i (eV k) =
            (Matrix.toEuclideanLin X (bV (eV k))) i := by
        simp [V, Matrix.toLpLin_apply, Matrix.mul_apply, Matrix.mulVec, dotProduct,
          Module.Basis.toMatrix_apply]
      have hright :
          ((U : Matrix (Fin m) (Fin m) ℝ) * singular_value_diagonal_matrix X) i (eV k) =
            (singular_value_function X k.1 • bU (eU k)).ofLp i := by
        have hek : (eU k).1 = (eV k).1 := (heU k).trans (heV k).symm
        rw [Matrix.mul_apply]
        rw [Fintype.sum_eq_single (eU k)]
        · have hkdiag :
              singular_value_diagonal_matrix X (eU k) (eV k) =
                singular_value_function X k.1 := by
            rw [singular_value_diagonal_matrix]
            rw [dif_pos hek]
            have hkindex :
                (⟨(eU k).1, Nat.lt_min.mpr ⟨(eU k).2, hek ▸ (eV k).2⟩⟩ :
                  Fin (min m n)) = k.1 := by
              apply Fin.ext
              simp [heU k]
            rw [hkindex]
          rw [hkdiag]
          simp [U, Module.Basis.toMatrix_apply, smul_eq_mul, mul_comm]
        · intro l hl
          have hne : l.1 ≠ (eV k).1 := by
            intro hlval
            apply hl
            apply Fin.ext
            exact hlval.trans ((heU k).trans (heV k).symm).symm
          simp [singular_value_diagonal_matrix, hne]
      calc
        (X * (V : Matrix (Fin n) (Fin n) ℝ)) i (eV k)
          = (Matrix.toEuclideanLin X (bV (eV k))) i := hleft
        _ = (singular_value_function X k.1 • bU (eU k)).ofLp i := hcoord
        _ = ((U : Matrix (Fin m) (Fin m) ℝ) * singular_value_diagonal_matrix X) i (eV k) :=
              hright.symm
    · have hleft :
          (X * (V : Matrix (Fin n) (Fin n) ℝ)) i j =
            (Matrix.toEuclideanLin X (bV j)) i := by
        simp [V, Matrix.toLpLin_apply, Matrix.mul_apply, Matrix.mulVec, dotProduct,
          Module.Basis.toMatrix_apply]
      have hright :
          ((U : Matrix (Fin m) (Fin m) ℝ) * singular_value_diagonal_matrix X) i j = 0 := by
        rw [Matrix.mul_apply]
        apply Finset.sum_eq_zero
        intro l hl
        simp [(hzero_diagonal hj l).1]
      rcases hkernel j hj with ⟨hXj, _⟩
      calc
        (X * (V : Matrix (Fin n) (Fin n) ℝ)) i j
          = (Matrix.toEuclideanLin X (bV j)) i := hleft
        _ = 0 := by simp [hXj]
        _ = ((U : Matrix (Fin m) (Fin m) ℝ) * singular_value_diagonal_matrix X) i j :=
              hright.symm
  · ext i j
    by_cases hj : j ∈ Set.range eV
    · rcases hj with ⟨k, rfl⟩
      rcases hactive_columns k with ⟨_, _, hY, _⟩
      have hcoord :
          (Matrix.toEuclideanLin Y (bV (eV k))).ofLp i =
            (singular_value_function Y k.1 • bU (eU k)).ofLp i := by
        simpa using congrArg (fun v : EuclideanSpace ℝ (Fin m) ↦ v.ofLp i) hY
      have hleft :
          (Y * (V : Matrix (Fin n) (Fin n) ℝ)) i (eV k) =
            (Matrix.toEuclideanLin Y (bV (eV k))) i := by
        simp [V, Matrix.toLpLin_apply, Matrix.mul_apply, Matrix.mulVec, dotProduct,
          Module.Basis.toMatrix_apply]
      have hright :
          ((U : Matrix (Fin m) (Fin m) ℝ) * singular_value_diagonal_matrix Y) i (eV k) =
            (singular_value_function Y k.1 • bU (eU k)).ofLp i := by
        have hek : (eU k).1 = (eV k).1 := (heU k).trans (heV k).symm
        rw [Matrix.mul_apply]
        rw [Fintype.sum_eq_single (eU k)]
        · have hkdiag :
              singular_value_diagonal_matrix Y (eU k) (eV k) =
                singular_value_function Y k.1 := by
            rw [singular_value_diagonal_matrix]
            rw [dif_pos hek]
            have hkindex :
                (⟨(eU k).1, Nat.lt_min.mpr ⟨(eU k).2, hek ▸ (eV k).2⟩⟩ :
                  Fin (min m n)) = k.1 := by
              apply Fin.ext
              simp [heU k]
            rw [hkindex]
          rw [hkdiag]
          simp [U, Module.Basis.toMatrix_apply, smul_eq_mul, mul_comm]
        · intro l hl
          have hne : l.1 ≠ (eV k).1 := by
            intro hlval
            apply hl
            apply Fin.ext
            exact hlval.trans ((heU k).trans (heV k).symm).symm
          simp [singular_value_diagonal_matrix, hne]
      calc
        (Y * (V : Matrix (Fin n) (Fin n) ℝ)) i (eV k)
          = (Matrix.toEuclideanLin Y (bV (eV k))) i := hleft
        _ = (singular_value_function Y k.1 • bU (eU k)).ofLp i := hcoord
        _ = ((U : Matrix (Fin m) (Fin m) ℝ) * singular_value_diagonal_matrix Y) i (eV k) :=
              hright.symm
    · have hleft :
          (Y * (V : Matrix (Fin n) (Fin n) ℝ)) i j =
            (Matrix.toEuclideanLin Y (bV j)) i := by
        simp [V, Matrix.toLpLin_apply, Matrix.mul_apply, Matrix.mulVec, dotProduct,
          Module.Basis.toMatrix_apply]
      have hright :
          ((U : Matrix (Fin m) (Fin m) ℝ) * singular_value_diagonal_matrix Y) i j = 0 := by
        rw [Matrix.mul_apply]
        apply Finset.sum_eq_zero
        intro l hl
        simp [(hzero_diagonal hj l).2]
      rcases hkernel j hj with ⟨_, hYj⟩
      calc
        (Y * (V : Matrix (Fin n) (Fin n) ℝ)) i j
          = (Matrix.toEuclideanLin Y (bV j)) i := hleft
        _ = 0 := by simp [hYj]
        _ = ((U : Matrix (Fin m) (Fin m) ℝ) * singular_value_diagonal_matrix Y) i j :=
              hright.symm

/-- Helper for Theorem 7.4: a common ordered dilation diagonalization should be converted into a
simultaneous nonincreasing singular value decomposition of the original rectangular matrices. -/
-- TODO: reindex the common ordered basis along `finSumFinEquiv`, pair each positive-head column
-- with its reflected negative-tail column, and use the resulting Hadamard sums/differences to
-- build the shared orthogonal factors `U` and `V`.
lemma paired_column_extraction_from_common_ordered_dilation_basis
    (X Y : Matrix (Fin m) (Fin n) ℝ)
    (Q : Matrix.orthogonalGroup (Fin (m + n)) ℝ)
    (hQX :
      (symmetric_dilation X : Matrix (Fin (m + n)) (Fin (m + n)) ℝ) =
        (Q : Matrix (Fin (m + n)) (Fin (m + n)) ℝ) *
          Matrix.diagonal (signed_singular_value_profile X) *
          ((Q : Matrix (Fin (m + n)) (Fin (m + n)) ℝ)ᵀ))
    (hQY :
      (symmetric_dilation Y : Matrix (Fin (m + n)) (Fin (m + n)) ℝ) =
        (Q : Matrix (Fin (m + n)) (Fin (m + n)) ℝ) *
          Matrix.diagonal (signed_singular_value_profile Y) *
          ((Q : Matrix (Fin (m + n)) (Fin (m + n)) ℝ)ᵀ)) :
    has_simultaneous_nonincreasing_singular_value_decomposition X Y := by
  -- Route correction: the file now has the positive-head column equations needed to recover
  -- common singular directions. The remaining blocker is packaging those columnwise equations into
  -- global orthogonal factors `U` and `V`, using the canonical negative companions and basis
  -- extension rather than ad hoc tail-column pairing.
  let S : Set (Fin (min m n)) :=
    common_active_singular_index_set X Y
  have hhead_columns :
      ∀ i : Fin (min m n),
        let j : Fin (m + n) := ⟨i.1, by
          omega⟩
        let q : Fin (m + n) → ℝ := (Q : Matrix (Fin (m + n)) (Fin (m + n)) ℝ).col j
        let u : Fin m → ℝ := fun r ↦ q (finSumFinEquiv (Sum.inl r))
        let v : Fin n → ℝ := fun c ↦ q (finSumFinEquiv (Sum.inr c))
        X.mulVec v = singular_value_function X i • u ∧
          Xᵀ.mulVec u = singular_value_function X i • v ∧
          Y.mulVec v = singular_value_function Y i • u ∧
          Yᵀ.mulVec u = singular_value_function Y i • v := by
    intro i
    exact head_dilation_column_common_singular_vector_equations
      (m := m) (n := n) X Y Q hQX hQY i
  have hcompanion_columns :
      ∀ i : Fin (min m n),
        let j : Fin (m + n) := ⟨i.1, by
          omega⟩
        let q : Fin (m + n) → ℝ := (Q : Matrix (Fin (m + n)) (Fin (m + n)) ℝ).col j
        let u : Fin m → ℝ := fun r ↦ q (finSumFinEquiv (Sum.inl r))
        let v : Fin n → ℝ := fun c ↦ q (finSumFinEquiv (Sum.inr c))
        block_symmetric_dilation X *ᵥ Sum.elim u (-v) =
            -singular_value_function X i • Sum.elim u (-v) ∧
          block_symmetric_dilation Y *ᵥ Sum.elim u (-v) =
            -singular_value_function Y i • Sum.elim u (-v) := by
    intro i
    exact head_dilation_column_block_sign_companion_equations
      (m := m) (n := n) X Y Q hQX hQY i
  have hinactive_eq_zero :
      ∀ i : Fin (min m n), i ∉ S →
        singular_value_function X i = 0 ∧ singular_value_function Y i = 0 := by
    intro i hi
    have hi' :
        ¬ (singular_value_function X i ≠ 0 ∨ singular_value_function Y i ≠ 0) := by
      simpa [S, common_active_singular_index_set] using hi
    constructor
    · by_contra hXi
      exact hi' (Or.inl hXi)
    · by_contra hYi
      exact hi' (Or.inr hYi)
  have hactive_block_products :
      ∀ i j : Fin (min m n), i ∈ S → j ∈ S →
        let ji : Fin (m + n) := ⟨i.1, by
          omega⟩
        let jj : Fin (m + n) := ⟨j.1, by
          omega⟩
        let qi : Fin (m + n) → ℝ := (Q : Matrix (Fin (m + n)) (Fin (m + n)) ℝ).col ji
        let qj : Fin (m + n) → ℝ := (Q : Matrix (Fin (m + n)) (Fin (m + n)) ℝ).col jj
        let ui : Fin m → ℝ := fun r ↦ qi (finSumFinEquiv (Sum.inl r))
        let vi : Fin n → ℝ := fun c ↦ qi (finSumFinEquiv (Sum.inr c))
        let uj : Fin m → ℝ := fun r ↦ qj (finSumFinEquiv (Sum.inl r))
        let vj : Fin n → ℝ := fun c ↦ qj (finSumFinEquiv (Sum.inr c))
        dotProduct ui uj = (if i = j then (1 : ℝ) / 2 else (0 : ℝ)) ∧
          dotProduct vi vj = (if i = j then (1 : ℝ) / 2 else (0 : ℝ)) := by
    intro i j hiS hjS
    exact active_head_dilation_column_block_dotProduct_eq_half_ite
      (m := m) (n := n) X Y Q hQX hQY i j hiS hjS
  have hhead_columns_euclidean :
      ∀ i : Fin (min m n),
        let j : Fin (m + n) := ⟨i.1, by
          omega⟩
        let q : Fin (m + n) → ℝ := (Q : Matrix (Fin (m + n)) (Fin (m + n)) ℝ).col j
        let u : Fin m → ℝ := fun r ↦ q (finSumFinEquiv (Sum.inl r))
        let v : Fin n → ℝ := fun c ↦ q (finSumFinEquiv (Sum.inr c))
        Matrix.toEuclideanLin X (WithLp.toLp 2 v) =
            singular_value_function X i • WithLp.toLp 2 u ∧
          Matrix.toEuclideanLin Xᵀ (WithLp.toLp 2 u) =
            singular_value_function X i • WithLp.toLp 2 v ∧
          Matrix.toEuclideanLin Y (WithLp.toLp 2 v) =
            singular_value_function Y i • WithLp.toLp 2 u ∧
          Matrix.toEuclideanLin Yᵀ (WithLp.toLp 2 u) =
            singular_value_function Y i • WithLp.toLp 2 v := by
    intro i
    exact head_dilation_column_common_singular_vector_equations_euclidean
      (m := m) (n := n) X Y Q hQX hQY i
  have hscaled_active_left_orthonormal :
      Orthonormal ℝ
        (fun i : ↥S ↦
          (Real.sqrt 2 : ℝ) •
            WithLp.toLp 2
              (fun r ↦
                ((Q : Matrix (Fin (m + n)) (Fin (m + n)) ℝ).col
                  ⟨i.1.1, by
                    omega⟩) (finSumFinEquiv (Sum.inl r)))) := by
    -- Package the left active family into a reusable orthonormality statement for basis extension.
    simpa [S] using
      scaled_active_left_family_orthonormal (m := m) (n := n) X Y Q hQX hQY
  have hscaled_active_right_orthonormal :
      Orthonormal ℝ
        (fun i : ↥S ↦
          (Real.sqrt 2 : ℝ) •
            WithLp.toLp 2
              (fun c ↦
                ((Q : Matrix (Fin (m + n)) (Fin (m + n)) ℝ).col
                  ⟨i.1.1, by
                    omega⟩) (finSumFinEquiv (Sum.inr c)))) := by
    -- The right active family has the same orthonormality package.
    simpa [S] using
      scaled_active_right_family_orthonormal (m := m) (n := n) X Y Q hQX hQY
  have hinactive_zero :
      ∀ i : Fin (min m n), i ∉ S →
        let j : Fin (m + n) := ⟨i.1, by
          omega⟩
        let q : Fin (m + n) → ℝ := (Q : Matrix (Fin (m + n)) (Fin (m + n)) ℝ).col j
        let u : Fin m → ℝ := fun r ↦ q (finSumFinEquiv (Sum.inl r))
        let v : Fin n → ℝ := fun c ↦ q (finSumFinEquiv (Sum.inr c))
        block_symmetric_dilation X *ᵥ Sum.elim u v = 0 ∧
          block_symmetric_dilation Y *ᵥ Sum.elim u v = 0 ∧
        block_symmetric_dilation X *ᵥ Sum.elim u (-v) = 0 ∧
          block_symmetric_dilation Y *ᵥ Sum.elim u (-v) = 0 := by
    intro i hi
    rcases hinactive_eq_zero i hi with ⟨hXi, hYi⟩
    exact inactive_head_columns_are_joint_zero_eigenvectors
      (m := m) (n := n) X Y Q hQX hQY i hXi hYi
  rcases
      active_head_coordinate_basis_extensions
        (m := m) (n := n) X Y Q hQX hQY with
    ⟨bU, bV, hbU, hbV⟩
  have hactive_columns :
      ∀ i : common_active_singular_index_set X Y,
        Matrix.toEuclideanLin X
            (bV ⟨i.1.1, Nat.lt_of_lt_of_le i.1.2 (Nat.min_le_right m n)⟩) =
          singular_value_function X i.1 •
            bU ⟨i.1.1, Nat.lt_of_lt_of_le i.1.2 (Nat.min_le_left m n)⟩ ∧
        Matrix.toEuclideanLin Xᵀ
            (bU ⟨i.1.1, Nat.lt_of_lt_of_le i.1.2 (Nat.min_le_left m n)⟩) =
          singular_value_function X i.1 •
            bV ⟨i.1.1, Nat.lt_of_lt_of_le i.1.2 (Nat.min_le_right m n)⟩ ∧
        Matrix.toEuclideanLin Y
            (bV ⟨i.1.1, Nat.lt_of_lt_of_le i.1.2 (Nat.min_le_right m n)⟩) =
          singular_value_function Y i.1 •
            bU ⟨i.1.1, Nat.lt_of_lt_of_le i.1.2 (Nat.min_le_left m n)⟩ ∧
        Matrix.toEuclideanLin Yᵀ
            (bU ⟨i.1.1, Nat.lt_of_lt_of_le i.1.2 (Nat.min_le_left m n)⟩) =
          singular_value_function Y i.1 •
            bV ⟨i.1.1, Nat.lt_of_lt_of_le i.1.2 (Nat.min_le_right m n)⟩ := by
    -- The active singular-vector equations now live directly on basis columns indexed by the
    -- original head coordinates, so the remaining gap is purely the trace-exhaustion packaging.
    intro i
    exact
      active_basis_extension_column_equations
        (m := m) (n := n) X Y Q hQX hQY bU bV hbU hbV i
  let eU : common_active_singular_index_set X Y ↪ Fin m :=
    ⟨fun i ↦ ⟨i.1.1, Nat.lt_of_lt_of_le i.1.2 (Nat.min_le_left m n)⟩,
      by
        intro i j hij
        apply Subtype.ext
        have hij_val : i.1.1 = j.1.1 := by
          simpa using congrArg (fun a : Fin m ↦ a.1) hij
        exact Fin.ext hij_val⟩
  let eV : common_active_singular_index_set X Y ↪ Fin n :=
    ⟨fun i ↦ ⟨i.1.1, Nat.lt_of_lt_of_le i.1.2 (Nat.min_le_right m n)⟩,
      by
        intro i j hij
        apply Subtype.ext
        have hij_val : i.1.1 = j.1.1 := by
          simpa using congrArg (fun a : Fin n ↦ a.1) hij
        exact Fin.ext hij_val⟩
  have heU : ∀ i : common_active_singular_index_set X Y, (eU i).1 = i.1.1 := by
    intro i
    rfl
  have heV : ∀ i : common_active_singular_index_set X Y, (eV i).1 = i.1.1 := by
    intro i
    rfl
  have hactive_columns' :
      ∀ i : common_active_singular_index_set X Y,
        Matrix.toEuclideanLin X (bV (eV i)) =
          singular_value_function X i.1 • bU (eU i) ∧
        Matrix.toEuclideanLin Xᵀ (bU (eU i)) =
          singular_value_function X i.1 • bV (eV i) ∧
        Matrix.toEuclideanLin Y (bV (eV i)) =
          singular_value_function Y i.1 • bU (eU i) ∧
        Matrix.toEuclideanLin Yᵀ (bU (eU i)) =
          singular_value_function Y i.1 • bV (eV i) := by
    -- Repackage the active equations in terms of the explicit head embeddings `eU` and `eV`.
    intro i
    simpa [eU, eV] using hactive_columns i
  have hactive_sq_norms :
      ∀ i : common_active_singular_index_set X Y,
        ‖Matrix.toEuclideanLin X (bV (eV i))‖ ^ (2 : ℕ) =
            singular_value_function X i.1 ^ (2 : ℕ) ∧
          ‖Matrix.toEuclideanLin Y (bV (eV i))‖ ^ (2 : ℕ) =
            singular_value_function Y i.1 ^ (2 : ℕ) := by
    -- The active column equations already identify the full Frobenius mass of the active range.
    exact active_basis_extension_sq_norms X Y bU bV eU eV hactive_columns'
  have hkernel :
      ∀ j : Fin n, j ∉ Set.range eV →
        Matrix.toEuclideanLin X (bV j) = 0 ∧ Matrix.toEuclideanLin Y (bV j) = 0 := by
    -- Exact trace exhaustion on the right basis leaves no mass on the complement columns.
    exact
      basis_extension_right_complement_common_kernel_from_trace_exhaustion
        X Y bV eV hactive_sq_norms (by
          intro i hi
          simpa [S] using hinactive_eq_zero i hi)
  have hzero_diagonal :
      ∀ {j : Fin n}, j ∉ Set.range eV →
        ∀ i : Fin m,
          singular_value_diagonal_matrix X i j = 0 ∧
            singular_value_diagonal_matrix Y i j = 0 := by
    -- Outside the active range, the rectangular diagonal matrices have zero columns.
    exact singular_value_diagonal_entry_eq_zero_of_not_mem_active_range X Y eV heV
  rcases
      paired_column_basis_extension_columnwise_diagonalization
        X Y bU bV eU eV heU heV hactive_columns' hkernel hzero_diagonal with
    ⟨U, V, hXV, hYV⟩
  have hVleft :
      (V : Matrix (Fin n) (Fin n) ℝ) * ((V : Matrix (Fin n) (Fin n) ℝ)ᵀ) = 1 :=
    (Matrix.mem_orthogonalGroup_iff
      (A := (V : Matrix (Fin n) (Fin n) ℝ)) (R := ℝ)).1 V.2
  refine ⟨U, V, ?_, ?_⟩
  · -- Right-multiply the columnwise diagonalization by `Vᵀ` to recover the SVD formula for `X`.
    calc
      X = X * (1 : Matrix (Fin n) (Fin n) ℝ) := by simp
      _ = X * ((V : Matrix (Fin n) (Fin n) ℝ) * ((V : Matrix (Fin n) (Fin n) ℝ)ᵀ)) := by
            rw [hVleft]
      _ = (X * (V : Matrix (Fin n) (Fin n) ℝ)) * ((V : Matrix (Fin n) (Fin n) ℝ)ᵀ) := by
            simp [Matrix.mul_assoc]
      _ =
          ((U : Matrix (Fin m) (Fin m) ℝ) * singular_value_diagonal_matrix X) *
            ((V : Matrix (Fin n) (Fin n) ℝ)ᵀ) := by
              rw [hXV]
      _ =
          (U : Matrix (Fin m) (Fin m) ℝ) * singular_value_diagonal_matrix X *
            ((V : Matrix (Fin n) (Fin n) ℝ)ᵀ) := by
              simp [Matrix.mul_assoc]
  · -- The identical right-multiplication argument gives the SVD formula for `Y`.
    calc
      Y = Y * (1 : Matrix (Fin n) (Fin n) ℝ) := by simp
      _ = Y * ((V : Matrix (Fin n) (Fin n) ℝ) * ((V : Matrix (Fin n) (Fin n) ℝ)ᵀ)) := by
            rw [hVleft]
      _ = (Y * (V : Matrix (Fin n) (Fin n) ℝ)) * ((V : Matrix (Fin n) (Fin n) ℝ)ᵀ) := by
            simp [Matrix.mul_assoc]
      _ =
          ((U : Matrix (Fin m) (Fin m) ℝ) * singular_value_diagonal_matrix Y) *
            ((V : Matrix (Fin n) (Fin n) ℝ)ᵀ) := by
              rw [hYV]
      _ =
          (U : Matrix (Fin m) (Fin m) ℝ) * singular_value_diagonal_matrix Y *
            ((V : Matrix (Fin n) (Fin n) ℝ)ᵀ) := by
              simp [Matrix.mul_assoc]

/-- Helper for Theorem 7.4: a common ordered dilation diagonalization should be converted into a
simultaneous nonincreasing singular value decomposition of the original rectangular matrices. -/
lemma common_ordered_dilation_diagonalization_implies_simultaneous_svd
    (X Y : Matrix (Fin m) (Fin n) ℝ)
    (Q : Matrix.orthogonalGroup (Fin (m + n)) ℝ)
    (hQX :
      (symmetric_dilation X : Matrix (Fin (m + n)) (Fin (m + n)) ℝ) =
        (Q : Matrix (Fin (m + n)) (Fin (m + n)) ℝ) *
          Matrix.diagonal (signed_singular_value_profile X) *
          ((Q : Matrix (Fin (m + n)) (Fin (m + n)) ℝ)ᵀ))
    (hQY :
      (symmetric_dilation Y : Matrix (Fin (m + n)) (Fin (m + n)) ℝ) =
        (Q : Matrix (Fin (m + n)) (Fin (m + n)) ℝ) *
          Matrix.diagonal (signed_singular_value_profile Y) *
          ((Q : Matrix (Fin (m + n)) (Fin (m + n)) ℝ)ᵀ)) :
    has_simultaneous_nonincreasing_singular_value_decomposition X Y := by
  have hcomm :
      symmetric_dilation X * symmetric_dilation Y =
        symmetric_dilation Y * symmetric_dilation X := by
    -- First isolate the commuting consequence of the common ordered diagonal basis.
    exact common_ordered_dilation_diagonalization_commute X Y Q hQX hQY
  have hcross :
      (Xᵀ * Y).IsSymm ∧ (X * Yᵀ).IsSymm := by
    -- The common dilation basis already forces the two rectangular cross-Gram matrices to be
    -- symmetric; this is the concrete matrix frontier needed for the final simultaneous-SVD step.
    exact symmetric_dilation_commute_implies_cross_gram_isSymm X Y hcomm
  -- Route correction: the remaining work is no longer generic block algebra. The file has reduced
  -- the equality case to extracting shared left/right singular directions from the common ordered
  -- dilation basis and the resulting cross-Gram symmetries.
  exact paired_column_extraction_from_common_ordered_dilation_basis
    (m := m) (n := n) X Y Q hQX hQY

/-- Helper for Theorem 7.4: equality in Fan's inequality for the two symmetric dilations should
be converted into a simultaneous nonincreasing singular value decomposition of the original
rectangular matrices. -/
lemma simultaneous_nonincreasing_singular_value_decomposition_of_dilation_fan_equality
    (X Y : Matrix (Fin m) (Fin n) ℝ)
    (hEq :
      Matrix.trace
          (((symmetric_dilation_symmetricMatrix X : symmetricMatrices (m + n)) :
              Matrix (Fin (m + n)) (Fin (m + n)) ℝ) *
            ((symmetric_dilation_symmetricMatrix Y : symmetricMatrices (m + n)) :
              Matrix (Fin (m + n)) (Fin (m + n)) ℝ)) =
        dotProduct
          (symmetric_eigenvalue_function (symmetric_dilation_symmetricMatrix X))
          (symmetric_eigenvalue_function (symmetric_dilation_symmetricMatrix Y))) :
    has_simultaneous_nonincreasing_singular_value_decomposition X Y := by
  rcases dilation_fan_equality_implies_common_ordered_diagonalization X Y hEq with
    ⟨Q, hQX, hQY⟩
  -- Route correction: the Fan equality lifting step is now proved via `Theorem_7_1`; the only
  -- remaining blocker is the rectangular extraction from the common ordered dilation basis.
  exact common_ordered_dilation_diagonalization_implies_simultaneous_svd X Y Q hQX hQY

-- Proof sketch: identify the Frobenius pairing with `Tr(XᵀY)`, apply the singular-value majoration
-- argument behind von Neumann's trace inequality, and then rewrite the right-hand side as the
-- Euclidean dot product of the finite singular-value lists.
/-- Theorem 7.4 (1): von Neumann's trace inequality for real `m × n` matrices says that the
Frobenius pairing `Tr(Xᵀ Y)` is bounded above by the Euclidean pairing of the ordered singular
value vectors `σ(X)` and `σ(Y)`. -/
theorem von_neumann_trace_inequality (X Y : Matrix (Fin m) (Fin n) ℝ) :
    Matrix.trace (Xᵀ * Y) ≤
      dotProduct (singular_value_function X) (singular_value_function Y) := by
  let dX : symmetricMatrices (m + n) := symmetric_dilation_symmetricMatrix X
  let dY : symmetricMatrices (m + n) := symmetric_dilation_symmetricMatrix Y
  have hFan :
      Matrix.trace ((dX : Matrix (Fin (m + n)) (Fin (m + n)) ℝ) *
        (dY : Matrix (Fin (m + n)) (Fin (m + n)) ℝ)) ≤
        dotProduct (symmetric_eigenvalue_function dX) (symmetric_eigenvalue_function dY) :=
    fan_inequality_trace_le_dotProduct_symmetric_eigenvalue_function dX dY
  have hScaled :
      2 * Matrix.trace (Xᵀ * Y) ≤
        2 * dotProduct (singular_value_function X) (singular_value_function Y) := by
    -- Route correction: the rectangular inequality now passes through Fan's symmetric inequality
    -- applied to the dilations, with the spectral identification isolated in one local helper.
    calc
      2 * Matrix.trace (Xᵀ * Y)
        = Matrix.trace ((dX : Matrix (Fin (m + n)) (Fin (m + n)) ℝ) *
            (dY : Matrix (Fin (m + n)) (Fin (m + n)) ℝ)) := by
              simpa [dX, dY] using
                (symmetric_dilation_trace_mul_eq_two_trace_transpose_mul X Y).symm
      _ ≤ dotProduct (symmetric_eigenvalue_function dX) (symmetric_eigenvalue_function dY) := hFan
      _ = 2 * dotProduct (singular_value_function X) (singular_value_function Y) := by
            simpa [dX, dY] using
              dotProduct_symmetric_eigenvalue_function_symmetric_dilation X Y
  linarith

-- Proof sketch: the forward direction refines the proof of von Neumann's trace inequality to its
-- equality case, forcing a common pair of orthogonal factors that simultaneously realizes the
-- ordered singular-value diagonals of `X` and `Y`. The reverse direction follows by substituting
-- such a simultaneous singular value decomposition into `Tr(XᵀY)` and simplifying.
/-- Theorem 7.4 (2): equality in von Neumann's trace inequality holds exactly when `X` and `Y`
admit a simultaneous nonincreasing singular value decomposition. -/
theorem von_neumann_trace_inequality_eq_iff
    (X Y : Matrix (Fin m) (Fin n) ℝ) :
    Matrix.trace (Xᵀ * Y) =
        dotProduct (singular_value_function X) (singular_value_function Y) ↔
      has_simultaneous_nonincreasing_singular_value_decomposition X Y := by
  constructor
  · intro hEq
    let dX : symmetricMatrices (m + n) := symmetric_dilation_symmetricMatrix X
    let dY : symmetricMatrices (m + n) := symmetric_dilation_symmetricMatrix Y
    have hDilEq :
        Matrix.trace ((dX : Matrix (Fin (m + n)) (Fin (m + n)) ℝ) *
            (dY : Matrix (Fin (m + n)) (Fin (m + n)) ℝ)) =
          dotProduct (symmetric_eigenvalue_function dX) (symmetric_eigenvalue_function dY) := by
      -- Route correction: the equality case is first lifted to the symmetric dilations; the only
      -- remaining bridge is then the common-diagonalization-to-simultaneous-SVD step.
      calc
        Matrix.trace ((dX : Matrix (Fin (m + n)) (Fin (m + n)) ℝ) *
            (dY : Matrix (Fin (m + n)) (Fin (m + n)) ℝ))
          = 2 * Matrix.trace (Xᵀ * Y) := by
              simpa [dX, dY] using
                symmetric_dilation_trace_mul_eq_two_trace_transpose_mul X Y
        _ = 2 * dotProduct (singular_value_function X) (singular_value_function Y) := by
              rw [hEq]
        _ = dotProduct (symmetric_eigenvalue_function dX) (symmetric_eigenvalue_function dY) := by
              symm
              simpa [dX, dY] using
                dotProduct_symmetric_eigenvalue_function_symmetric_dilation X Y
    exact simultaneous_nonincreasing_singular_value_decomposition_of_dilation_fan_equality
      X Y hDilEq
  · intro hXY
    -- Substituting the common orthogonal singular-value factors collapses the trace to the
    -- diagonal singular-value dot product.
    exact trace_eq_dotProduct_of_simultaneous_nonincreasing_singular_value_decomposition X Y hXY

end
