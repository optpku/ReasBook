module

public import Mathlib.Algebra.Field.Rat
public import Mathlib.Data.Matrix.Mul
public import Mathlib.LinearAlgebra.Matrix.Integer
public import Mathlib.LinearAlgebra.Matrix.Rank
public import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap01.section_1_5.ch1_sec1_5_1_theorem_1_8
public import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap01.section_1_5.ch1_sec1_5_2_definition_1_38.ColumnHermite

@[expose] public section

open scoped Matrix
open Matrix

namespace Matrix

section Theorem110

variable {m n : ℕ}

/-- Helper for Theorem 1.10: clearing denominators does not change the rank of a rational matrix. -/
lemma rank_numMap_eq (A : Matrix (Fin m) (Fin n) ℚ) :
    (A.num.map (Int.castRingHom ℚ)).rank = A.rank := by
  -- The cleared numerator matrix differs from `A` by left multiplication with an invertible scalar.
  have hdet : IsUnit ((((A.den⁻¹ : ℚ) • (1 : Matrix (Fin m) (Fin m) ℚ))).det) := by
    apply isUnit_iff_ne_zero.mpr
    simp [Nat.cast_ne_zero.mpr A.den_ne_zero]
  calc
    (A.num.map (Int.castRingHom ℚ)).rank =
        ((((A.den⁻¹ : ℚ) • (1 : Matrix (Fin m) (Fin m) ℚ))) *
          A.num.map (Int.castRingHom ℚ)).rank := by
      symm
      exact Matrix.rank_mul_eq_right_of_isUnit_det _ _ hdet
    _ = A.rank := by
      -- Expanding the scalar matrix recovers `A` via `Matrix.inv_denom_smul_num`.
      have hscale :
          (((A.den⁻¹ : ℚ) • (1 : Matrix (Fin m) (Fin m) ℚ)) * A.num.map (Int.castRingHom ℚ)) =
            (A.den⁻¹ : ℚ) • A.num.map (Int.castRingHom ℚ) := by
        simp
      rw [hscale]
      exact congrArg Matrix.rank (Matrix.inv_denom_smul_num A)

/-- Helper for Theorem 1.10: positive scalar rescaling preserves column Hermite normal form. -/
theorem IsColumnHermiteNormalForm.smul_pos
    {A : Matrix (Fin m) (Fin n) ℚ} {q : ℚ}
    (hq : 0 < q)
    (hA : A.IsColumnHermiteNormalForm) :
    (q • A).IsColumnHermiteNormalForm := by
  rw [Matrix.isColumnHermiteNormalForm_iff_exists_block] at hA ⊢
  rcases hA with ⟨r, h, D, hblock, htri, hdiag, hsub⟩
  refine ⟨r, h, q • D, ?_, ?_, ?_, ?_⟩
  · -- The same block decomposition works after scaling every entry by `q`.
    change q • (Matrix.reindex (Equiv.refl (Fin m)) ((finCongr h).trans finSumFinEquiv.symm) A) =
      Matrix.fromCols (q • D) 0
    rw [hblock]
    ext i j
    cases j with
    | inl j =>
        simp
    | inr j =>
        simp
  · -- Positive scaling preserves lower triangularity because zero entries stay zero.
    intro i j hij
    simp [htri hij]
  · -- The diagonal stays positive after multiplying by a positive scalar.
    intro i
    exact mul_pos hq (hdiag i)
  · -- The reduced subdiagonal inequalities scale by the same positive factor.
    intro i j hij
    rcases hsub i j hij with ⟨hij_nonneg, hij_lt⟩
    exact ⟨mul_nonneg hq.le hij_nonneg, mul_lt_mul_of_pos_left hij_lt hq⟩

/-- Helper for Theorem 1.10: the top `m` rows of a full-row-rank `(m + 1) × n` rational matrix
still have rank `m`. -/
lemma prefixRank_of_fullRankSucc
    (A : Matrix (Fin (m + 1)) (Fin n) ℚ)
    (hA : A.rank = m + 1) :
    (A.submatrix Fin.castSucc id).rank = m := by
  -- Full row rank forces the whole row family to be linearly independent.
  have hrows : LinearIndependent ℚ A.row := by
    apply linearIndependent_iff_card_eq_finrank_span.mpr
    simpa [Matrix.rank_eq_finrank_span_row] using hA.symm
  -- Restricting to the prefix rows keeps the family linearly independent.
  have hprefix : LinearIndependent ℚ (A.submatrix Fin.castSucc id).row := by
    simpa [Matrix.row, Matrix.submatrix, Function.comp_def] using
      hrows.comp Fin.castSucc
        (Fin.castSucc_injective m)
  -- A linearly independent family of `m` rows has rank exactly `m`.
  simpa [Fintype.card_fin] using hprefix.rank_matrix

/-- Helper for Theorem 1.10: a matrix with no rows is already in column Hermite normal form. -/
lemma isColumnHermiteNormalForm_finZero
    (A : Matrix (Fin 0) (Fin n) ℚ) :
    A.IsColumnHermiteNormalForm := by
  -- Expanding the predicate leaves only empty-index obligations.
  rw [Matrix.isColumnHermiteNormalForm_iff_exists_block]
  refine ⟨n, by simp, 0, ?_, ?_, ?_, ?_⟩
  · -- There are no rows, so the reindexed matrix is forced.
    ext i
    exact Fin.elim0 i
  · -- Lower triangularity is vacuous on the empty index type.
    intro i j hij
    exact Fin.elim0 i
  · -- There is no diagonal to check.
    intro i
    exact Fin.elim0 i
  · -- The reduced subdiagonal condition is also vacuous.
    intro i j hij
    exact Fin.elim0 i

/-- Helper for Theorem 1.10: a one-row full-rank integral matrix has a nonzero row vector. -/
lemma oneRow_ne_zero_of_rank_eq_one
    (B : Matrix (Fin 1) (Fin n) ℤ)
    (hB : (B.map (Int.castRingHom ℚ)).rank = 1) :
    (fun j : Fin n ↦ B 0 j) ≠ 0 := by
  intro hzero
  -- If the unique row vanished, the rational cast would be the zero matrix.
  have hcast_zero : B.map (Int.castRingHom ℚ) = 0 := by
    ext i j
    fin_cases i
    simp [hzero]
  have hrank_zero : (B.map (Int.castRingHom ℚ)).rank = 0 := by
    rw [hcast_zero]
    exact Matrix.rank_zero
  exact Nat.zero_ne_one <| hrank_zero.symm.trans hB

/-- Helper for Theorem 1.10: the one-row full-rank integral case is exactly Theorem 1.8 plus the
column-Hermite packaging step. -/
lemma exists_unimodular_columnHermiteNormalForm_of_integralRankEq_oneRow
    (B : Matrix (Fin 1) (Fin n) ℤ)
    (hB : (B.map (Int.castRingHom ℚ)).rank = 1) :
    ∃ U : Matrix (Fin n) (Fin n) ℤ,
      IsUnit U.det ∧
        ((B.map (Int.castRingHom ℚ)) * U.map (Int.castRingHom ℚ)).IsColumnHermiteNormalForm := by
  let a : Fin n → ℤ := fun j ↦ B 0 j
  have ha : a ≠ 0 := oneRow_ne_zero_of_rank_eq_one B hB
  rcases exists_unimodular_normalForm a with ⟨U, hU, hform⟩
  refine ⟨U, hU, ?_⟩
  have hwidth : 1 ≤ n := by
    calc
      1 = (B.map (Int.castRingHom ℚ)).rank := hB.symm
      _ ≤ Fintype.card (Fin n) := Matrix.rank_le_card_width (B.map (Int.castRingHom ℚ))
      _ = n := by simp
  have hn : 0 < n := Nat.succ_le_iff.mp hwidth
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
  have hg_nonneg : 0 ≤ coefficientGcd a := by
    exact Int.nonneg_of_normalize_eq_self (Finset.normalize_gcd (s := Finset.univ) (f := a))
  have hg_pos : 0 < coefficientGcd a := by
    exact lt_of_le_of_ne hg_nonneg (by simpa [eq_comm] using coefficientGcd_ne_zero_of_nonzero a ha)
  let normalRow : Matrix (Fin 1) (Fin (k + 1)) ℚ :=
    fun _ j ↦ (coefficientGcdNormalFormRow a j : ℚ)
  have hmul :
      ((B.map (Int.castRingHom ℚ)) * U.map (Int.castRingHom ℚ)) =
        normalRow := by
    ext i j
    fin_cases i
    -- Cast the one-row normal form identity from `ℤ` to `ℚ`.
    have hcast :
        (((a ᵥ* U) j : ℤ) : ℚ) = (coefficientGcdNormalFormRow a j : ℚ) := by
      exact_mod_cast congrFun hform j
    simpa [a, normalRow, Matrix.vecMul, dotProduct, Matrix.mul_apply] using hcast
  -- Reindex the normalized row so that the pivot column appears first and the tail vanishes.
  rw [Matrix.isColumnHermiteNormalForm_iff_exists_block]
  refine ⟨k, by simp [Nat.succ_eq_add_one, Nat.add_comm],
    (fun _ _ ↦ (coefficientGcd a : ℚ)), ?_, ?_, ?_, ?_⟩
  · rw [hmul]
    ext i j
    fin_cases i
    cases j with
    | inl j =>
        fin_cases j
        have hcol : (Fin.castAdd k 0 : Fin (1 + k)) = 0 := by
          ext
          simp
        simp [Matrix.reindex_apply, normalRow, coefficientGcdNormalFormRow, hcol]
    | inr j =>
        simp [Matrix.reindex_apply, normalRow, coefficientGcdNormalFormRow]
  · -- A `1 × 1` matrix is automatically lower triangular.
    intro i j hij
    fin_cases i
    fin_cases j
    exact (lt_irrefl (0 : Fin 1) hij).elim
  · -- The pivot is the positive coefficient gcd.
    intro i
    fin_cases i
    simpa using (show (0 : ℚ) < (coefficientGcd a : ℚ) from by exact_mod_cast hg_pos)
  · -- There are no strict subdiagonal entries in a one-row matrix.
    intro i j hij
    fin_cases i
    fin_cases j
    exact (lt_irrefl (0 : Fin 1) hij).elim

/-- Helper for Theorem 1.10: the selector keeping only the trailing `r` columns has full rank. -/
lemma trailingColumnSelector_rank
    {p r : ℕ} :
    (Matrix.fromRows
      (0 : Matrix (Fin p) (Fin r) ℚ)
      (1 : Matrix (Fin r) (Fin r) ℚ)).rank = r := by
  have hupper :
      (Matrix.fromRows
        (0 : Matrix (Fin p) (Fin r) ℚ)
        (1 : Matrix (Fin r) (Fin r) ℚ)).rank ≤ r := by
    calc
      (Matrix.fromRows
        (0 : Matrix (Fin p) (Fin r) ℚ)
        (1 : Matrix (Fin r) (Fin r) ℚ)).rank ≤ Fintype.card (Fin r) := Matrix.rank_le_card_width _
      _ = r := by simp
  have hsub :
      (1 : Matrix (Fin r) (Fin r) ℚ).rank ≤
        (Matrix.fromRows
          (0 : Matrix (Fin p) (Fin r) ℚ)
          (1 : Matrix (Fin r) (Fin r) ℚ)).rank := by
    have hsubmatrix :
        ((Matrix.fromRows
          (0 : Matrix (Fin p) (Fin r) ℚ)
          (1 : Matrix (Fin r) (Fin r) ℚ)).submatrix Sum.inr id) =
          (1 : Matrix (Fin r) (Fin r) ℚ) := by
      ext i j
      simp
    rw [← hsubmatrix]
    exact
      Matrix.rank_submatrix_le
        (A := Matrix.fromRows
          (0 : Matrix (Fin p) (Fin r) ℚ)
          (1 : Matrix (Fin r) (Fin r) ℚ))
        (r := Sum.inr) (c := id)
  have hlower :
      r ≤
        (Matrix.fromRows
          (0 : Matrix (Fin p) (Fin r) ℚ)
          (1 : Matrix (Fin r) (Fin r) ℚ)).rank := by
    simpa [Matrix.rank_one] using hsub
  exact le_antisymm hupper hlower

/-- Helper for Theorem 1.10: in the block induction step, the trailing integral row block cannot
vanish if the full rational matrix still has rank `m + 2`. -/
lemma tailBlockNonzero_of_fullRankCast
    {r : ℕ}
    {D : Matrix (Fin (m + 1)) (Fin (m + 1)) ℚ}
    {b : Matrix (Fin 1) (Fin (m + 1)) ℤ}
    {c : Matrix (Fin 1) (Fin r) ℤ}
    (hRank :
      (Matrix.fromRows
        (Matrix.fromCols D 0)
        (Matrix.fromCols (b.map (Int.castRingHom ℚ)) (c.map (Int.castRingHom ℚ)))).rank = m + 2) :
    c ≠ 0 := by
  intro hc
  subst hc
  let M : Matrix (Fin (m + 1) ⊕ Fin 1) (Fin (m + 1) ⊕ Fin r) ℚ :=
    Matrix.fromRows
      (Matrix.fromCols D 0)
      (Matrix.fromCols (b.map (Int.castRingHom ℚ)) 0)
  let S : Matrix (Fin (m + 1) ⊕ Fin r) (Fin r) ℚ :=
    Matrix.fromRows
      (0 : Matrix (Fin (m + 1)) (Fin r) ℚ)
      (1 : Matrix (Fin r) (Fin r) ℚ)
  have hmul : M * S = 0 := by
    -- The selector matrix only sees the trailing block, so it vanishes when `c = 0`.
    dsimp [M, S]
    rw [Matrix.fromRows_fromCols_eq_fromBlocks, Matrix.fromBlocks_mul_fromRows]
    simp
  have hineq :
      M.rank + S.rank ≤ Fintype.card (Fin (m + 1) ⊕ Fin r) := by
    simpa [M, S] using Matrix.rank_add_rank_le_card_of_mul_eq_zero hmul
  have hSel : S.rank = r := by
    simpa [S] using (trailingColumnSelector_rank (p := m + 1) (r := r))
  have hbound : M.rank ≤ m + 1 := by
    rw [hSel, Fintype.card_sum, Fintype.card_fin, Fintype.card_fin] at hineq
    omega
  have : m + 2 ≤ m + 1 := by
    exact hRank ▸ hbound
  have hcontra : Nat.succ (m + 1) ≤ m + 1 := by
    simpa [Nat.succ_eq_add_one, Nat.add_assoc] using this
  exact Nat.not_succ_le_self (m + 1) hcontra

/-- Helper for Theorem 1.10: once a row reindex sends the `inl` branch back to `Fin.castSucc`,
the top rows of the reindexed matrix are exactly the reindexed prefix block. -/
lemma topRows_reindex_eq_prefix
    {r : ℕ}
    (A : Matrix (Fin (m + 2)) (Fin n) ℚ)
    (e : Fin n ≃ Fin (m + 1) ⊕ Fin r)
    (erow : Fin (m + 2) ≃ Fin (m + 1) ⊕ Fin 1)
    (herow : ∀ i : Fin (m + 1), erow.symm (Sum.inl i) = Fin.castSucc i) :
    (Matrix.reindex erow e A).toRows₁ =
      Matrix.reindex (Equiv.refl _) e (A.submatrix Fin.castSucc id) := by
  -- The chosen row equivalence exposes the prefix block as the `toRows₁` projection.
  ext i j
  simp [Matrix.reindex_apply, herow i]

/-- Helper for Theorem 1.10: after splitting the bottom reindexed integral row into left and right
column blocks, casting to `ℚ` reconstructs the same bottom row via `Matrix.fromCols`. -/
lemma bottomRows_map_eq_fromCols
    {r : ℕ}
    (MRZ : Matrix (Fin (m + 1) ⊕ Fin 1) (Fin (m + 1) ⊕ Fin r) ℤ) :
    let b : Matrix (Fin 1) (Fin (m + 1)) ℤ := MRZ.toRows₂.toCols₁
    let c : Matrix (Fin 1) (Fin r) ℤ := MRZ.toRows₂.toCols₂
    (MRZ.map (Int.castRingHom ℚ)).toRows₂ =
      Matrix.fromCols (b.map (Int.castRingHom ℚ)) (c.map (Int.castRingHom ℚ)) := by
  -- The bottom row is recovered entrywise from its left and right column projections.
  ext i j
  cases j <;> rfl

/-- Helper for Theorem 1.10: lifting the one-row unimodular normalizer to the explicit
reindexed block matrix changes only the trailing row block. -/
lemma normalizeTailBlock_reindexed
    {r : ℕ}
    (D : Matrix (Fin (m + 1)) (Fin (m + 1)) ℚ)
    (b : Matrix (Fin 1) (Fin (m + 1)) ℤ)
    (c : Matrix (Fin 1) (Fin r) ℤ)
    (T : Matrix (Fin r) (Fin r) ℤ)
    (hTform :
      (fun j : Fin r ↦ c 0 j) ᵥ* T =
        coefficientGcdNormalFormRow (fun j : Fin r ↦ c 0 j)) :
    Matrix.fromRows
        (Matrix.fromCols D 0)
        (Matrix.fromCols (b.map (Int.castRingHom ℚ)) (c.map (Int.castRingHom ℚ))) *
        (Matrix.fromBlocks
          (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) ℤ) 0 0 T).map (Int.castRingHom ℚ) =
      Matrix.fromRows
        (Matrix.fromCols D 0)
        (Matrix.fromCols
          (b.map (Int.castRingHom ℚ))
          (fun _ j ↦ (coefficientGcdNormalFormRow (fun j : Fin r ↦ c 0 j) j : ℚ))) := by
  let tailRow : Fin r → ℤ := fun j ↦ c 0 j
  have hTformQ :
      (c.map (Int.castRingHom ℚ)) * (T.map (Int.castRingHom ℚ)) =
        (fun _ j ↦ (coefficientGcdNormalFormRow tailRow j : ℚ) :
          Matrix (Fin 1) (Fin r) ℚ) := by
    -- Cast the one-row normal form identity from `ℤ` to the bottom-right rational block.
    ext i j
    fin_cases i
    have hcast :
        (((tailRow ᵥ* T) j : ℤ) : ℚ) =
          (coefficientGcdNormalFormRow tailRow j : ℚ) := by
      exact_mod_cast congrFun hTform j
    simpa [tailRow, Matrix.vecMul, dotProduct, Matrix.mul_apply] using hcast
  -- Rewriting both sides as block matrices isolates the bottom-right multiplication by `T`.
  rw [Matrix.fromRows_fromCols_eq_fromBlocks, Matrix.fromRows_fromCols_eq_fromBlocks]
  have hLift :
      (Matrix.fromBlocks
        (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) ℤ) 0 0 T).map (Int.castRingHom ℚ) =
        Matrix.fromBlocks
          (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) ℚ) 0 0 (T.map (Int.castRingHom ℚ)) := by
    -- Coefficient casting commutes with the four block entries of the lifted matrix.
    ext i j <;> cases i <;> cases j <;> simp [Matrix.one_apply]
  rw [hLift, Matrix.fromBlocks_multiply]
  simpa [hTformQ]

/-- Helper for Theorem 1.10: once the tail has been normalized to the single positive pivot `g`,
the lower-left row can be reduced entrywise modulo `g` by one cleanup shear. -/
lemma normalizedPivotCleanupRow
    {k : ℕ}
    (b : Matrix (Fin 1) (Fin (m + 1)) ℤ)
    {g : ℤ}
    (hg : 0 < g) :
    let normalTail : Matrix (Fin 1) (Fin (k + 1)) ℚ :=
      fun _ j ↦ if j.1 = 0 then (g : ℚ) else 0
    let C : Matrix (Fin (k + 1)) (Fin (m + 1)) ℤ :=
      fun i j ↦ if i.1 = 0 then -(b 0 j / g) else 0
    let bred : Matrix (Fin 1) (Fin (m + 1)) ℤ :=
      fun _ j ↦ b 0 j % g
    ((b.map (Int.castRingHom ℚ)) + normalTail * (C.map (Int.castRingHom ℚ)) =
        bred.map (Int.castRingHom ℚ)) ∧
      (∀ j : Fin (m + 1), 0 ≤ bred 0 j ∧ bred 0 j < g) := by
  constructor
  · -- Only the first normalized tail column contributes, so the row identity is the Euclidean
    -- division formula `b = g * (b / g) + b % g` rewritten into cleanup form.
    ext i j
    fin_cases i
    simp [Matrix.add_apply, Matrix.mul_apply]
    have hmod : b 0 j + -(g * (b 0 j / g)) = b 0 j % g := by
      linarith [Int.mul_ediv_add_emod (b 0 j) g]
    exact_mod_cast hmod
  · -- Positive divisors give the standard remainder bounds needed for the new subdiagonal entries.
    intro j
    exact ⟨Int.emod_nonneg _ (ne_of_gt hg), Int.emod_lt_of_pos _ hg⟩

/-- Helper for Theorem 1.10: the cleanup shear lifts the row-level remainder identity to the full
explicit block matrix after the tail has been normalized. -/
lemma liftPivotCleanupShear
    {k : ℕ}
    (D : Matrix (Fin (m + 1)) (Fin (m + 1)) ℚ)
    (b : Matrix (Fin 1) (Fin (m + 1)) ℤ)
    {g : ℤ}
    (hg : 0 < g) :
    let normalTail : Matrix (Fin 1) (Fin (k + 1)) ℚ :=
      fun _ j ↦ if j.1 = 0 then (g : ℚ) else 0
    let C : Matrix (Fin (k + 1)) (Fin (m + 1)) ℤ :=
      fun i j ↦ if i.1 = 0 then -(b 0 j / g) else 0
    let bred : Matrix (Fin 1) (Fin (m + 1)) ℤ :=
      fun _ j ↦ b 0 j % g
    let A1 : Matrix (Fin (m + 1) ⊕ Fin 1) (Fin (m + 1) ⊕ Fin (k + 1)) ℚ :=
      Matrix.fromRows
        (Matrix.fromCols D 0)
        (Matrix.fromCols (b.map (Int.castRingHom ℚ)) normalTail)
    let Vred : Matrix (Fin (m + 1) ⊕ Fin (k + 1)) (Fin (m + 1) ⊕ Fin (k + 1)) ℤ :=
      Matrix.fromBlocks
        (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) ℤ) 0 C 1
    let A2 : Matrix (Fin (m + 1) ⊕ Fin 1) (Fin (m + 1) ⊕ Fin (k + 1)) ℚ :=
      Matrix.fromRows
        (Matrix.fromCols D 0)
        (Matrix.fromCols (bred.map (Int.castRingHom ℚ)) normalTail)
    A1 * Vred.map (Int.castRingHom ℚ) = A2 := by
  have hrow :
      let normalTail : Matrix (Fin 1) (Fin (k + 1)) ℚ :=
        fun _ j ↦ if j.1 = 0 then (g : ℚ) else 0
      let C : Matrix (Fin (k + 1)) (Fin (m + 1)) ℤ :=
        fun i j ↦ if i.1 = 0 then -(b 0 j / g) else 0
      let bred : Matrix (Fin 1) (Fin (m + 1)) ℤ :=
        fun _ j ↦ b 0 j % g
      (b.map (Int.castRingHom ℚ)) + normalTail * (C.map (Int.castRingHom ℚ)) =
        bred.map (Int.castRingHom ℚ) := by
    -- Reuse the row-level cleanup identity without reopening the Euclidean arithmetic.
    simpa using (normalizedPivotCleanupRow (m := m) (k := k) b (g := g) hg).1
  -- Rewriting both matrices as explicit `fromBlocks` products isolates the bottom-left cleanup.
  dsimp
  let Cmat : Matrix (Fin (k + 1)) (Fin (m + 1)) ℤ := fun i j ↦ if i.1 = 0 then -(b 0 j / g) else 0
  let bredMat : Matrix (Fin 1) (Fin (m + 1)) ℤ := fun _ j ↦ b 0 j % g
  rw [Matrix.fromRows_fromCols_eq_fromBlocks, Matrix.fromRows_fromCols_eq_fromBlocks]
  have hLift :
      (Matrix.fromBlocks
        (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) ℤ)
        (0 : Matrix (Fin (m + 1)) (Fin (k + 1)) ℤ)
        Cmat
        (1 : Matrix (Fin (k + 1)) (Fin (k + 1)) ℤ)).map (Int.castRingHom ℚ) =
        Matrix.fromBlocks
          (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) ℚ)
          (0 : Matrix (Fin (m + 1)) (Fin (k + 1)) ℚ)
          (Cmat.map (Int.castRingHom ℚ))
          (1 : Matrix (Fin (k + 1)) (Fin (k + 1)) ℚ) := by
    -- Coefficient casting commutes entrywise with the block-matrix shear.
    ext i j
    cases i <;> cases j <;> simp [Cmat, Matrix.one_apply]
  have hgoal :
      (Matrix.fromBlocks
        D 0
        (b.map (Int.castRingHom ℚ))
        (fun _ j ↦ if j.1 = 0 then (g : ℚ) else 0)) *
        (Matrix.fromBlocks
          (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) ℤ)
          (0 : Matrix (Fin (m + 1)) (Fin (k + 1)) ℤ)
          Cmat
          (1 : Matrix (Fin (k + 1)) (Fin (k + 1)) ℤ)).map (Int.castRingHom ℚ) =
        Matrix.fromBlocks
          D 0
          (bredMat.map (Int.castRingHom ℚ))
          (fun _ j ↦ if j.1 = 0 then (g : ℚ) else 0) := by
    rw [hLift, Matrix.fromBlocks_multiply]
    -- The top block is unchanged, while the bottom-left block is exactly the cleaned row.
    simpa [Cmat, bredMat] using hrow
  simpa [Cmat, bredMat] using hgoal

/-- Helper for Theorem 1.10: adjoining one final pivot to a square matrix places the old matrix
in the upper-left block and a prescribed reduced row below it. -/
def appendPivotMatrix
    {p : ℕ}
    (D : Matrix (Fin p) (Fin p) ℚ)
    (b : Fin p → ℚ)
    (g : ℚ) :
    Matrix (Fin (p + 1)) (Fin (p + 1)) ℚ :=
  fun i j ↦
    Fin.lastCases
      (Fin.lastCases g b j)
      (fun i₀ ↦ Fin.lastCases 0 (D i₀) j)
      i

/-- Helper for Theorem 1.10: the cleaned two-by-two block presentation transported back to
canonical `Fin` row and column indices. -/
def cleanedPivotBlockMatrix
    {p k N : ℕ}
    (hSplit : N = p + (k + 1))
    (D : Matrix (Fin p) (Fin p) ℚ)
    (b : Fin p → ℚ)
    (g : ℚ) :
    Matrix (Fin (p + 1)) (Fin N) ℚ :=
  Matrix.reindex finSumFinEquiv
    ((finCongr hSplit).trans finSumFinEquiv.symm).symm
    (Matrix.fromRows
      (Matrix.fromCols D 0)
      (Matrix.fromCols
        (fun _ j ↦ b j)
        (fun _ j ↦ if j.1 = 0 then g else 0)))

/-- Helper for Theorem 1.10: canonical column reassociation turns the cleaned block presentation
into an appended pivot block followed by zero columns. -/
lemma cleanedPivotBlockMatrix_reindex
    {p k N : ℕ}
    (hSplit : N = p + (k + 1))
    (hFinal : N = (p + 1) + k)
    (D : Matrix (Fin p) (Fin p) ℚ)
    (b : Fin p → ℚ)
    (g : ℚ) :
    Matrix.reindex (Equiv.refl _)
        ((finCongr hFinal).trans finSumFinEquiv.symm)
        (cleanedPivotBlockMatrix hSplit D b g) =
      Matrix.fromCols (appendPivotMatrix D b g) 0 := by
  let eSplit : Fin N ≃ Fin p ⊕ Fin (k + 1) :=
    (finCongr hSplit).trans finSumFinEquiv.symm
  let eFinal : Fin N ≃ Fin (p + 1) ⊕ Fin k :=
    (finCongr hFinal).trans finSumFinEquiv.symm
  have hOldColumn (j : Fin p) :
      eSplit (eFinal.symm (Sum.inl j.castSucc)) = Sum.inl j := by
    apply finSumFinEquiv.injective
    ext
    simp [eSplit, eFinal]
  have hPivotColumn :
      eSplit (eFinal.symm (Sum.inl (Fin.last p))) = Sum.inr 0 := by
    apply finSumFinEquiv.injective
    ext
    simp [eSplit, eFinal]
  have hTailColumn (j : Fin k) :
      eSplit (eFinal.symm (Sum.inr j)) = Sum.inr j.succ := by
    apply finSumFinEquiv.injective
    ext
    simp [eSplit, eFinal]
    omega
  have hEntry (i : Fin (p + 1)) (j : Fin (p + 1) ⊕ Fin k) :
      Matrix.reindex (Equiv.refl _)
          ((finCongr hFinal).trans finSumFinEquiv.symm)
          (cleanedPivotBlockMatrix hSplit D b g) i j =
        Matrix.fromRows
            (Matrix.fromCols D 0)
            (Matrix.fromCols
              (fun _ j ↦ b j)
              (fun _ j ↦ if j.1 = 0 then g else 0))
          (finSumFinEquiv.symm i) (eSplit (eFinal.symm j)) := by
    rfl
  -- The three column cases are respectively an old pivot column, the new pivot, and the zero tail.
  ext i j
  cases j with
  | inl j =>
      induction i using Fin.lastCases with
      | last =>
          induction j using Fin.lastCases with
          | last =>
              rw [hEntry, hPivotColumn]
              simp [appendPivotMatrix]
          | cast j =>
              rw [hEntry, hOldColumn]
              simp [appendPivotMatrix]
      | cast i =>
          induction j using Fin.lastCases with
          | last =>
              rw [hEntry, hPivotColumn]
              simp [appendPivotMatrix]
          | cast j =>
              rw [hEntry, hOldColumn]
              simp [appendPivotMatrix]
  | inr j =>
      induction i using Fin.lastCases with
      | last =>
          rw [hEntry, hTailColumn]
          simp
      | cast i =>
          rw [hEntry, hTailColumn]
          simp

/-- Helper for Theorem 1.10: adjoining a positive pivot and a reduced final row preserves all
lower-triangular column Hermite inequalities. -/
lemma appendPivotMatrix_isReducedLowerTriangular
    {p : ℕ}
    (D : Matrix (Fin p) (Fin p) ℚ)
    (b : Fin p → ℚ)
    (g : ℚ)
    (htri : D.BlockTriangular OrderDual.toDual)
    (hdiag : ∀ i, 0 < D i i)
    (hsub : ∀ i j, j < i → 0 ≤ D i j ∧ D i j < D i i)
    (hg : 0 < g)
    (hb : ∀ j, 0 ≤ b j ∧ b j < g) :
    (appendPivotMatrix D b g).BlockTriangular OrderDual.toDual ∧
      (∀ i, 0 < appendPivotMatrix D b g i i) ∧
      (∀ i j, j < i →
        0 ≤ appendPivotMatrix D b g i j ∧
          appendPivotMatrix D b g i j < appendPivotMatrix D b g i i) := by
  refine ⟨?_, ?_, ?_⟩
  · -- Above the enlarged diagonal, either the old triangularity applies or the new column is zero.
    intro i j hij
    induction i using Fin.lastCases with
    | last =>
        exact (not_lt_of_ge (Fin.le_last j) hij).elim
    | cast i =>
        induction j using Fin.lastCases with
        | last => simp [appendPivotMatrix]
        | cast j =>
            simp only [appendPivotMatrix, Fin.lastCases_castSucc]
            exact htri hij
  · -- The old diagonal remains positive and the new diagonal entry is `g`.
    intro i
    induction i using Fin.lastCases with
    | last => simpa [appendPivotMatrix] using hg
    | cast i => simpa [appendPivotMatrix] using hdiag i
  · -- Strict subdiagonal entries are either old reduced entries or entries of the new row.
    intro i j hij
    induction i using Fin.lastCases with
    | last =>
        induction j using Fin.lastCases with
        | last => exact (lt_irrefl (Fin.last p) hij).elim
        | cast j => simpa [appendPivotMatrix] using hb j
    | cast i =>
        induction j using Fin.lastCases with
        | last => exact (not_lt_of_ge (Fin.le_last (Fin.castSucc i)) hij).elim
        | cast j => simpa [appendPivotMatrix] using hsub i j hij

/-- Helper for Theorem 1.10: a matrix whose canonical leading block is an appended positive pivot
is in column Hermite normal form. -/
lemma isColumnHermiteNormalForm_of_reindex_eq_appendPivot
    {p k N : ℕ}
    (A : Matrix (Fin (p + 1)) (Fin N) ℚ)
    (D : Matrix (Fin p) (Fin p) ℚ)
    (b : Fin p → ℚ)
    (g : ℚ)
    (hN : N = (p + 1) + k)
    (hblock :
      Matrix.reindex (Equiv.refl _)
          ((finCongr hN).trans finSumFinEquiv.symm) A =
        Matrix.fromCols (appendPivotMatrix D b g) 0)
    (htri : D.BlockTriangular OrderDual.toDual)
    (hdiag : ∀ i, 0 < D i i)
    (hsub : ∀ i j, j < i → 0 ≤ D i j ∧ D i j < D i i)
    (hg : 0 < g)
    (hb : ∀ j, 0 ≤ b j ∧ b j < g) :
    A.IsColumnHermiteNormalForm := by
  have hpivot := appendPivotMatrix_isReducedLowerTriangular D b g htri hdiag hsub hg hb
  -- The canonical block characterization now consumes the structural equality and inequalities.
  rw [Matrix.isColumnHermiteNormalForm_iff_exists_block]
  exact ⟨k, hN, appendPivotMatrix D b g, hblock, hpivot.1, hpivot.2.1, hpivot.2.2⟩

/-- Helper for Theorem 1.10: the integral full-row-rank case is the remaining induction target
after denominator clearing. -/
theorem exists_unimodular_columnHermiteNormalForm_of_integralRankEq
    (B : Matrix (Fin m) (Fin n) ℤ)
    (hB : (B.map (Int.castRingHom ℚ)).rank = m) :
    ∃ U : Matrix (Fin n) (Fin n) ℤ,
      IsUnit U.det ∧
        ((B.map (Int.castRingHom ℚ)) * U.map (Int.castRingHom ℚ)).IsColumnHermiteNormalForm := by
  induction m generalizing n with
  | zero =>
      refine ⟨1, ?_, ?_⟩
      · simp
      · -- With no rows, the matrix is already in Hermite normal form.
        simpa using isColumnHermiteNormalForm_finZero (A := B.map (Int.castRingHom ℚ))
  | succ m ih =>
      cases m with
      | zero =>
          -- The one-row case is exactly the normal-form theorem for a nonzero integer row.
          simpa using
            exists_unimodular_columnHermiteNormalForm_of_integralRankEq_oneRow B hB
      | succ m =>
          let Btop : Matrix (Fin (m + 1)) (Fin n) ℤ := B.submatrix Fin.castSucc id
          have hBtop : (Btop.map (Int.castRingHom ℚ)).rank = m + 1 := by
            -- The induction hypothesis applies to the prefix block because full row rank
            -- is preserved when the last row is removed.
            simpa [Btop] using
              prefixRank_of_fullRankSucc (A := B.map (Int.castRingHom ℚ)) hB
          rcases ih Btop hBtop with ⟨U₀, hU₀, hTop⟩
          rw [Matrix.isColumnHermiteNormalForm_iff_exists_block] at hTop
          rcases hTop with ⟨r, hr, D, hblock, htri, hdiag, hsub⟩
          -- Route correction: the remaining `m + 2` step should follow the Agent C block route,
          -- not a repeated unfolding of `IsColumnHermiteNormalForm`.
          -- TODO: transport the full matrix into the IH column split once, expose its bottom row
          -- as integer blocks `b` and `c`, invoke `tailBlockNonzero_of_fullRankCast` on that block
          -- presentation, and then complete the tail normalization and modulo-reduction steps
          -- entirely in the reindexed column world before transporting back once.
          let e : Fin n ≃ Fin (m + 1) ⊕ Fin r :=
            (finCongr hr).trans finSumFinEquiv.symm
          let erow : Fin (m + 2) ≃ Fin (m + 1) ⊕ Fin 1 :=
            (finCongr (by omega)).trans finSumFinEquiv.symm
          let MZ : Matrix (Fin (m + 2)) (Fin n) ℤ := B * U₀
          let Mq : Matrix (Fin (m + 2)) (Fin n) ℚ := MZ.map (Int.castRingHom ℚ)
          let MRZ : Matrix (Fin (m + 1) ⊕ Fin 1) (Fin (m + 1) ⊕ Fin r) ℤ :=
            Matrix.reindex erow e MZ
          let MRq : Matrix (Fin (m + 1) ⊕ Fin 1) (Fin (m + 1) ⊕ Fin r) ℚ :=
            Matrix.reindex erow e Mq
          have hMqRank : Mq.rank = m + 2 := by
            -- Right multiplication by a unimodular integer matrix preserves rational rank.
            have hUq : IsUnit (U₀.map (Int.castRingHom ℚ)).det := by
              apply isUnit_iff_ne_zero.mpr
              simpa [Int.cast_det] using
                (show ((U₀.det : ℚ)) ≠ 0 from by exact_mod_cast hU₀.ne_zero)
            calc
              Mq.rank = (((B.map (Int.castRingHom ℚ)) * (U₀.map (Int.castRingHom ℚ))).rank) := by
                simp [Mq, MZ, Matrix.map_mul]
              _ = (B.map (Int.castRingHom ℚ)).rank := by
                exact Matrix.rank_mul_eq_left_of_isUnit_det
                  (A := U₀.map (Int.castRingHom ℚ))
                  (B := B.map (Int.castRingHom ℚ))
                  hUq
              _ = m + 2 := hB
          have herow :
              ∀ i : Fin (m + 1), erow.symm (Sum.inl i) = Fin.castSucc i := by
            intro i
            change Fin.castAdd 1 i = Fin.castSucc i
            rfl
          have hTopSubmatrix :
              Mq.submatrix Fin.castSucc id =
                (Btop.map (Int.castRingHom ℚ)) * (U₀.map (Int.castRingHom ℚ)) := by
            -- Restricting the transformed full matrix to the prefix rows recovers the IH matrix.
            calc
              Mq.submatrix Fin.castSucc id =
                  ((B.map (Int.castRingHom ℚ)).submatrix Fin.castSucc id) *
                    ((U₀.map (Int.castRingHom ℚ)).submatrix id id) := by
                simpa [Mq, MZ, Matrix.map_mul] using
                  (Matrix.submatrix_mul
                    (B.map (Int.castRingHom ℚ))
                    (U₀.map (Int.castRingHom ℚ))
                    Fin.castSucc id id Function.bijective_id)
              _ = ((B.submatrix Fin.castSucc id).map (Int.castRingHom ℚ)) *
                    (U₀.map (Int.castRingHom ℚ)) := by
                rw [Matrix.submatrix_map]
                simp
              _ = (Btop.map (Int.castRingHom ℚ)) * (U₀.map (Int.castRingHom ℚ)) := by
                rfl
          have hTopRows :
              MRq.toRows₁ = Matrix.fromCols D 0 := by
            -- The top rows of the reindexed full matrix are exactly the IH block witness.
            calc
              MRq.toRows₁ =
                  Matrix.reindex (Equiv.refl _) e (Mq.submatrix Fin.castSucc id) := by
                simpa [MRq] using topRows_reindex_eq_prefix (A := Mq) e erow herow
              _ = Matrix.fromCols D 0 := by
                rw [hTopSubmatrix]
                simpa [Matrix.map_mul] using hblock
          let b : Matrix (Fin 1) (Fin (m + 1)) ℤ := MRZ.toRows₂.toCols₁
          let c : Matrix (Fin 1) (Fin r) ℤ := MRZ.toRows₂.toCols₂
          have hMRqMap : MRq = MRZ.map (Int.castRingHom ℚ) := by
            -- Reindexing commutes with coefficient casting.
            ext i j
            rfl
          have hBottomRows :
              MRq.toRows₂ =
                Matrix.fromCols (b.map (Int.castRingHom ℚ)) (c.map (Int.castRingHom ℚ)) := by
            -- The bottom row is read directly from the reindexed integral matrix `MRZ`.
            rw [hMRqMap]
            simpa [b, c] using bottomRows_map_eq_fromCols (MRZ := MRZ)
          have hMRqBlock :
              MRq =
                Matrix.fromRows
                  (Matrix.fromCols D 0)
                  (Matrix.fromCols (b.map (Int.castRingHom ℚ)) (c.map (Int.castRingHom ℚ))) := by
            -- Reconstruct the full reindexed matrix from its verified top and bottom projections.
            calc
              MRq = Matrix.fromRows MRq.toRows₁ MRq.toRows₂ := by
                symm
                exact Matrix.fromRows_toRows MRq
              _ =
                  Matrix.fromRows
                    (Matrix.fromCols D 0)
                    (Matrix.fromCols
                      (b.map (Int.castRingHom ℚ))
                      (c.map (Int.castRingHom ℚ))) := by
                rw [hTopRows, hBottomRows]
          have hMRqRank :
              MRq.rank = m + 2 := by
            -- Row and column reindexing preserve rank.
            calc
              MRq.rank = Mq.rank := by
                simpa [MRq] using Matrix.rank_reindex erow e Mq
              _ = m + 2 := hMqRank
          have hBlockRank :
              (Matrix.fromRows
                (Matrix.fromCols D 0)
                (Matrix.fromCols (b.map (Int.castRingHom ℚ)) (c.map (Int.castRingHom ℚ)))).rank =
                m + 2 := by
            -- The explicit block presentation carries the full-rank information of `MRq`.
            rw [← hMRqBlock]
            exact hMRqRank
          have hc : c ≠ 0 := by
            -- Once the split block presentation is explicit, the existing nonzero-tail lemma applies.
            exact tailBlockNonzero_of_fullRankCast (m := m) (D := D) (b := b) (c := c) hBlockRank
          have hr_ne_zero : r ≠ 0 := by
            -- A nonzero `1 × r` tail block forces the tail width to be positive.
            intro hr0
            apply hc
            ext i j
            fin_cases i
            exact Fin.elim0 (hr0 ▸ j)
          obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hr_ne_zero
          let tailRow : Fin (k + 1) → ℤ := fun j ↦ c 0 j
          have htailRow : tailRow ≠ 0 := by
            -- The explicit bottom-right row vector is the nonzero witness carried by `c`.
            intro htail
            apply hc
            ext i j
            fin_cases i
            exact congrFun htail j
          rcases exists_unimodular_normalForm tailRow with ⟨T, hTdet, hTform⟩
          have hg_nonneg : 0 ≤ coefficientGcd tailRow := by
            -- The coefficient gcd is normalized to a nonnegative integer.
            exact
              Int.nonneg_of_normalize_eq_self
                (Finset.normalize_gcd (s := Finset.univ) (f := tailRow))
          have hg_pos : 0 < coefficientGcd tailRow := by
            -- Nonzero tails have strictly positive coefficient gcd.
            exact
              lt_of_le_of_ne hg_nonneg
                (by simpa [eq_comm] using coefficientGcd_ne_zero_of_nonzero tailRow htailRow)
          have hTailNormalized :
              Matrix.fromRows
                  (Matrix.fromCols D 0)
                  (Matrix.fromCols
                    (b.map (Int.castRingHom ℚ))
                    (c.map (Int.castRingHom ℚ))) *
                (Matrix.fromBlocks
                  (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) ℤ) 0 0 T).map
                  (Int.castRingHom ℚ) =
                Matrix.fromRows
                  (Matrix.fromCols D 0)
                  (Matrix.fromCols
                    (b.map (Int.castRingHom ℚ))
                    (fun _ j ↦ (coefficientGcdNormalFormRow tailRow j : ℚ))) := by
            -- The lifted block-diagonal multiplier applies the one-row normalizer to `c` only.
            simpa [tailRow] using
              normalizeTailBlock_reindexed (m := m) D b c T hTform
          let g : ℤ := coefficientGcd tailRow
          let normalTail : Matrix (Fin 1) (Fin (k + 1)) ℚ :=
            fun _ j ↦ (coefficientGcdNormalFormRow tailRow j : ℚ)
          let C : Matrix (Fin (k + 1)) (Fin (m + 1)) ℤ :=
            fun i j ↦ if i.1 = 0 then -(b 0 j / g) else 0
          let bred : Matrix (Fin 1) (Fin (m + 1)) ℤ :=
            fun _ j ↦ b 0 j % g
          let A1 : Matrix (Fin (m + 1) ⊕ Fin 1) (Fin (m + 1) ⊕ Fin (k + 1)) ℚ :=
            Matrix.fromRows
              (Matrix.fromCols D 0)
              (Matrix.fromCols (b.map (Int.castRingHom ℚ)) normalTail)
          let Vred : Matrix (Fin (m + 1) ⊕ Fin (k + 1)) (Fin (m + 1) ⊕ Fin (k + 1)) ℤ :=
            Matrix.fromBlocks
              (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) ℤ) 0 C 1
          let A2 : Matrix (Fin (m + 1) ⊕ Fin 1) (Fin (m + 1) ⊕ Fin (k + 1)) ℚ :=
            Matrix.fromRows
              (Matrix.fromCols D 0)
              (Matrix.fromCols (bred.map (Int.castRingHom ℚ)) normalTail)
          have hCleanupRow :
              ((b.map (Int.castRingHom ℚ)) + normalTail * (C.map (Int.castRingHom ℚ)) =
                bred.map (Int.castRingHom ℚ)) := by
            -- The Euclidean cleanup now lives in a single reusable row lemma.
            simpa [g, normalTail, C, bred, coefficientGcdNormalFormRow] using
              (normalizedPivotCleanupRow (m := m) (k := k) b (g := g) hg_pos).1
          have hCleanupBounds :
              ∀ j : Fin (m + 1), 0 ≤ bred 0 j ∧ bred 0 j < g := by
            -- These are exactly the remainder bounds needed for the final HNF inequalities.
            simpa [g, bred] using
              (normalizedPivotCleanupRow (m := m) (k := k) b (g := g) hg_pos).2
          have hA1 :
              MRq *
                  (Matrix.fromBlocks
                    (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) ℤ) 0 0 T).map
                    (Int.castRingHom ℚ) =
                A1 := by
            -- Compose the explicit block witness with the lifted tail normalizer once.
            rw [hMRqBlock]
            simpa [A1, normalTail] using hTailNormalized
          have hA2 :
              A1 * Vred.map (Int.castRingHom ℚ) = A2 := by
            -- Lift the row-level cleanup identity through the full block matrix.
            simpa [A1, A2, Vred, g, normalTail, C, bred, coefficientGcdNormalFormRow] using
              liftPivotCleanupShear (m := m) (k := k) D b (g := g) hg_pos
          -- The verified frontier is now the explicit normalized matrix `A1`, the cleaned matrix
          -- `A2`, and the exact cleanup bounds on `bred`. The remaining work is only the final
          -- column reassociation and HNF packaging.
          have hFinal : n = (m + 2) + k := by
            omega
          have hg_pos_rat : (0 : ℚ) < (g : ℚ) := by
            exact_mod_cast hg_pos
          have hCleanupBounds_rat :
              ∀ j : Fin (m + 1),
                (0 : ℚ) ≤ (bred 0 j : ℚ) ∧ (bred 0 j : ℚ) < (g : ℚ) := by
            -- Cast the integral Euclidean remainder bounds once for the HNF interface.
            intro j
            exact_mod_cast hCleanupBounds j
          let H : Matrix (Fin (m + 2)) (Fin n) ℚ :=
            cleanedPivotBlockMatrix hr D (fun j ↦ (bred 0 j : ℚ)) (g : ℚ)
          have hHblock :
              Matrix.reindex (Equiv.refl _)
                  ((finCongr hFinal).trans finSumFinEquiv.symm) H =
                Matrix.fromCols
                  (appendPivotMatrix D (fun j ↦ (bred 0 j : ℚ)) (g : ℚ)) 0 := by
            -- Reassociate the old pivot columns, the new pivot, and the remaining zero tail.
            simpa [H] using
              cleanedPivotBlockMatrix_reindex hr hFinal D
                (fun j ↦ (bred 0 j : ℚ)) (g : ℚ)
          have hH : H.IsColumnHermiteNormalForm := by
            -- The append-pivot interface packages the cleaned block and all four HNF conditions.
            exact
              isColumnHermiteNormalForm_of_reindex_eq_appendPivot H D
                (fun j ↦ (bred 0 j : ℚ)) (g : ℚ) hFinal
                hHblock htri hdiag hsub hg_pos_rat hCleanupBounds_rat
          have herowSymm : erow.symm = finSumFinEquiv := by
            -- The chosen row transport is the canonical split into the old rows and final row.
            apply Equiv.ext
            intro i
            ext
            simp [erow]
          have hBredMap :
              bred.map (Int.castRingHom ℚ) =
                (fun _ j ↦ (bred 0 j : ℚ) : Matrix (Fin 1) (Fin (m + 1)) ℚ) := by
            -- A one-row mapped matrix is determined by its unique row.
            ext i j
            fin_cases i
            rfl
          have hA2Source :
              A2 =
                Matrix.fromRows
                  (Matrix.fromCols D 0)
                  (Matrix.fromCols
                    (fun _ j ↦ (bred 0 j : ℚ))
                    (fun _ j ↦ if j.1 = 0 then (g : ℚ) else 0)) := by
            -- Normalize the unique mapped cleanup row before applying the outer reindexing.
            change
              Matrix.fromRows
                  (Matrix.fromCols D 0)
                  (Matrix.fromCols (bred.map (Int.castRingHom ℚ)) normalTail) = _
            rw [hBredMap]
            simp [normalTail, g, coefficientGcdNormalFormRow]
          have hA2Fin : Matrix.reindex erow.symm e.symm A2 = H := by
            -- Both sides are the same cleaned block after replacing the row equivalence by its
            -- canonical spelling.
            rw [herowSymm, hA2Source]
            rfl
          let Vtail :
              Matrix (Fin (m + 1) ⊕ Fin (k + 1)) (Fin (m + 1) ⊕ Fin (k + 1)) ℤ :=
            Matrix.fromBlocks
              (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) ℤ) 0 0 T
          let Vsum :
              Matrix (Fin (m + 1) ⊕ Fin (k + 1)) (Fin (m + 1) ⊕ Fin (k + 1)) ℤ :=
            Vtail * Vred
          let Vfin : Matrix (Fin n) (Fin n) ℤ :=
            Matrix.reindex e.symm e.symm Vsum
          let U : Matrix (Fin n) (Fin n) ℤ := U₀ * Vfin
          have hVtail : IsUnit Vtail.det := by
            -- The lifted tail normalizer has determinant `det T`.
            simpa [Vtail] using hTdet
          have hVred : IsUnit Vred.det := by
            -- The cleanup shear is block triangular with identity diagonal blocks.
            simp [Vred]
          have hVsum : IsUnit Vsum.det := by
            -- Determinants multiply under the two consecutive sum-indexed operations.
            simp only [Vsum, Matrix.det_mul]
            exact hVtail.mul hVred
          have hVfin : IsUnit Vfin.det := by
            -- Simultaneous row and column reindexing preserves the determinant.
            have hdet : Vfin.det = Vsum.det := by
              dsimp [Vfin]
              exact Matrix.det_reindex_self e.symm Vsum
            rw [hdet]
            exact hVsum
          have hU : IsUnit U.det := by
            -- The original induction multiplier and the transported tail multiplier are unimodular.
            simp only [U, Matrix.det_mul]
            exact hU₀.mul hVfin
          have hMRqVsum :
              MRq * Vsum.map (Int.castRingHom ℚ) = A2 := by
            -- Compose tail normalization and row cleanup in their stable block presentation.
            simp only [Vsum, Matrix.map_mul]
            rw [← Matrix.mul_assoc, hA1, hA2]
          have hReindexVfin :
              Matrix.reindex e e (Vfin.map (Int.castRingHom ℚ)) =
                Vsum.map (Int.castRingHom ℚ) := by
            -- Mapping coefficients commutes with undoing the simultaneous column reindexing.
            ext i j
            simp [Vfin, Matrix.reindex_apply]
          have hProductReindexed :
              Matrix.reindex erow e
                  (Mq * Vfin.map (Int.castRingHom ℚ)) = A2 := by
            -- Reindexing multiplication exposes exactly `MRq * Vsum`.
            calc
              Matrix.reindex erow e
                    (Mq * Vfin.map (Int.castRingHom ℚ)) =
                  Matrix.reindex erow e Mq *
                    Matrix.reindex e e (Vfin.map (Int.castRingHom ℚ)) := by
                symm
                exact Matrix.reindexLinearEquiv_mul ℚ ℚ erow e e Mq
                  (Vfin.map (Int.castRingHom ℚ))
              _ = MRq * Vsum.map (Int.castRingHom ℚ) := by
                rw [hReindexVfin]
              _ = A2 := hMRqVsum
          have hProductFin :
              Mq * Vfin.map (Int.castRingHom ℚ) =
                Matrix.reindex erow.symm e.symm A2 := by
            -- Apply the inverse row-and-column transport only once to return to canonical indices.
            calc
              Mq * Vfin.map (Int.castRingHom ℚ) =
                  Matrix.reindex erow.symm e.symm
                    (Matrix.reindex erow e
                      (Mq * Vfin.map (Int.castRingHom ℚ))) := by
                ext i j
                simp [Matrix.reindex_apply]
              _ = Matrix.reindex erow.symm e.symm A2 :=
                congrArg (Matrix.reindex erow.symm e.symm) hProductReindexed
          refine ⟨U, hU, ?_⟩
          have hBU :
              (B.map (Int.castRingHom ℚ)) * U.map (Int.castRingHom ℚ) = H := by
            -- Associate the complete multiplier, use the transported block calculation, and
            -- identify the result with the packaged HNF matrix.
            calc
              (B.map (Int.castRingHom ℚ)) * U.map (Int.castRingHom ℚ) =
                  (B.map (Int.castRingHom ℚ)) *
                    ((U₀.map (Int.castRingHom ℚ)) *
                      (Vfin.map (Int.castRingHom ℚ))) := by
                simp only [U, Matrix.map_mul]
              _ = Mq * Vfin.map (Int.castRingHom ℚ) := by
                rw [← Matrix.mul_assoc]
                simp [Mq, MZ, Matrix.map_mul]
              _ = Matrix.reindex erow.symm e.symm A2 := hProductFin
              _ = H := hA2Fin
          rw [hBU]
          exact hH

/-- Theorem 1.10. A full-row-rank rational `m × n` matrix admits a unimodular integer right
change of variables that puts it into column Hermite normal form. -/
theorem exists_unimodular_columnHermiteNormalForm_of_rank_eq
    (A : Matrix (Fin m) (Fin n) ℚ)
    (hA : A.rank = m) :
    ∃ U : Matrix (Fin n) (Fin n) ℤ,
      IsUnit U.det ∧
        (A * U.map (Int.castRingHom ℚ)).IsColumnHermiteNormalForm := by
  -- First clear denominators so that the remaining existence statement is purely integral.
  have hnum : (A.num.map (Int.castRingHom ℚ)).rank = m := by
    rw [rank_numMap_eq, hA]
  rcases exists_unimodular_columnHermiteNormalForm_of_integralRankEq A.num hnum with
    ⟨U, hU, hHNF⟩
  refine ⟨U, hU, ?_⟩
  have hq_den : 0 < (A.den : ℚ) := by
    exact_mod_cast Nat.pos_of_ne_zero A.den_ne_zero
  have hq : 0 < (A.den⁻¹ : ℚ) := by
    simpa using inv_pos.mpr hq_den
  -- Reinsert the cleared denominator and then use positive-scaling invariance of HNF.
  have hmul :
      A * U.map (Int.castRingHom ℚ) =
        (A.den⁻¹ : ℚ) •
          ((A.num.map (Int.castRingHom ℚ)) * U.map (Int.castRingHom ℚ)) := by
    have hdenom :
        A = (A.den⁻¹ : ℚ) • A.num.map (Int.castRingHom ℚ) := by
      simpa using (Matrix.inv_denom_smul_num A).symm
    calc
      A * U.map (Int.castRingHom ℚ) =
          (((A.den⁻¹ : ℚ) • A.num.map (Int.castRingHom ℚ)) * U.map (Int.castRingHom ℚ)) := by
        exact congrArg (fun M ↦ M * U.map (Int.castRingHom ℚ)) hdenom
      _ = (A.den⁻¹ : ℚ) •
            ((A.num.map (Int.castRingHom ℚ)) * U.map (Int.castRingHom ℚ)) := by
        simp
  rw [hmul]
  exact IsColumnHermiteNormalForm.smul_pos hq hHNF

end Theorem110

end Matrix

end
