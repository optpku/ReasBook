import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

-- Domain sampling for this exercise:
-- * primary domain: totally unimodular matrices over a commutative ring and the Chapter 1 full-row
--   condition on the identity augmentation `(A | I)`
-- * core/canonical owners: `Matrix.IsTotallyUnimodular`, `Matrix.isTotallyUnimodular_iff`,
--   `Matrix.transpose_isTotallyUnimodular_iff`, and `Matrix.fromCols_one_isTotallyUnimodular_iff`
-- * source-facing bridge/view layer: the condition that every full-row minor of `(A | I)` has
--   determinant `0`, `1`, or `-1`
-- * primitive data: a column embedding `cols : Fin m ↪ Fin n ⊕ Fin m`; derived API: the
--   determinant-sign condition for the corresponding full-row minor

namespace Matrix

section FlipRowSigns

variable {m n R : Type*} [Neg R]

/-- `flipRowSigns A s` is obtained from `A` by multiplying each row with `s i = true` by `-1` and
leaving the remaining rows unchanged. -/
def flipRowSigns (A : Matrix m n R) (s : m → Bool) : Matrix m n R :=
  fun i j ↦ if s i then -A i j else A i j

end FlipRowSigns

end Matrix

section Exercise45

variable {m n : ℕ} {R : Type*} [CommRing R]

namespace Matrix

/-- Helper for Exercise 4.5: multiplying any chosen set of rows by `-1` changes each square minor
only by an overall sign, so total unimodularity is preserved. -/
theorem IsTotallyUnimodular.flipRowSigns
    {α β : Type*} {A : Matrix α β R} (hA : A.IsTotallyUnimodular) (s : α → Bool) :
    (A.flipRowSigns s).IsTotallyUnimodular := by
  -- Rewrite each minor as a diagonal row-scaling of the corresponding minor of `A`.
  rw [Matrix.isTotallyUnimodular_iff] at hA ⊢
  intro k f g
  let ε : Fin k → R := fun i ↦ if s (f i) then (-1 : R) else 1
  have hsub :
      (A.flipRowSigns s).submatrix f g = Matrix.diagonal ε * A.submatrix f g := by
    ext i j
    simp [ε, Matrix.flipRowSigns, Matrix.diagonal_mul]
  have hdet :
      (Matrix.diagonal ε * A.submatrix f g).det =
        (∏ i, ε i) * (A.submatrix f g).det := by
    conv_lhs => simp [Matrix.diagonal_mul]
  rw [hsub, hdet]
  let τ : Fin k → SignType := fun i ↦ if s (f i) then (-1 : SignType) else 1
  have hprod : (∏ i, ε i) ∈ Set.range SignType.cast := by
    have hcast : ((↑(∏ i, τ i) : R)) = ∏ i, ↑(τ i) := by
      classical
      let u : Finset (Fin k) := Finset.univ
      change ((↑(Finset.prod u τ) : R)) = Finset.prod u fun i ↦ ↑(τ i)
      clear_value u
      induction u using Finset.induction_on with
      | empty =>
          simp
      | @insert a s ha ih =>
          simp [ha, ih, SignType.coe_mul]
    have hετ : ∀ i, ε i = ((τ i : SignType) : R) := by
      intro i
      by_cases hsfi : s (f i)
      · simp [ε, τ, hsfi]
      · simp [ε, τ, hsfi]
    refine ⟨∏ i, τ i, ?_⟩
    calc
      ((↑(∏ i, τ i) : R)) = ∏ i, ↑(τ i) := hcast
      _ = ∏ i, ε i := by simp_rw [hετ]
  -- The determinant of the scaled minor is the product of two sign values.
  change ((∏ i, ε i) * (A.submatrix f g).det) ∈ MonoidHom.mrange SignType.castHom.toMonoidHom
  exact mul_mem (by simpa using hprod) (by simpa using hA k f g)

/-- Helper for Exercise 4.5: an injective `k × k` minor of `A` can be padded with identity columns
to become a full-row `m × m` minor of `(A | I)`. -/
theorem padded_minor_det_fromCols_one
    (A : Matrix (Fin m) (Fin n) R)
    {k : ℕ} (f : Fin k → Fin m) (g : Fin k → Fin n)
    (hf : Function.Injective f) (hg : Function.Injective g) :
    ∃ cols : Fin m ↪ (Fin n ⊕ Fin m),
      ((Matrix.fromCols A (1 : Matrix (Fin m) (Fin m) R)).submatrix id cols).det =
        (A.submatrix f g).det := by
  classical
  let ef : Fin k ↪ Fin m := ⟨f, hf⟩
  let eg : Fin k ↪ Fin n := ⟨g, hg⟩
  let eRange : Fin k ≃ Set.range f := ef.toEquivRange
  let leftCols' : Set.range f ↪ Fin n :=
    ⟨eg ∘ eRange.symm, eg.injective.comp eRange.symm.injective⟩
  let rightCols' : {i : Fin m // i ∉ Set.range f} ↪ Fin m :=
    Function.Embedding.subtype fun i : Fin m ↦ i ∉ Set.range f
  let splitFun : Set.range f ⊕ {i : Fin m // i ∉ Set.range f} → Fin n ⊕ Fin m :=
    Sum.elim (Sum.inl ∘ leftCols') (Sum.inr ∘ rightCols')
  have hsplitFun : Function.Injective splitFun := by
    intro x y hxy
    cases x <;> cases y
    · exact congrArg Sum.inl (leftCols'.injective (Sum.inl.inj hxy))
    · cases hxy
    · cases hxy
    · exact congrArg Sum.inr (rightCols'.injective (Sum.inr.inj hxy))
  let splitCols : Set.range f ⊕ {i : Fin m // i ∉ Set.range f} ↪ Fin n ⊕ Fin m :=
    ⟨splitFun, hsplitFun⟩
  let eCompl : Fin m ≃ Set.range f ⊕ {i : Fin m // i ∉ Set.range f} :=
    (Equiv.sumCompl fun i : Fin m ↦ i ∈ Set.range f).symm
  let cols : Fin m ↪ Fin n ⊕ Fin m :=
    ⟨splitCols ∘ eCompl, splitCols.injective.comp eCompl.injective⟩
  let B : Matrix (Fin m) (Fin m) R :=
    (Matrix.fromCols A (1 : Matrix (Fin m) (Fin m) R)).submatrix id cols
  let topLeft : Matrix (Set.range f) (Set.range f) R :=
    A.submatrix Subtype.val leftCols'
  let bottomLeft : Matrix {i : Fin m // i ∉ Set.range f} (Set.range f) R :=
    A.submatrix Subtype.val leftCols'
  let blockMatrix :
      Matrix (Set.range f ⊕ {i : Fin m // i ∉ Set.range f})
        (Set.range f ⊕ {i : Fin m // i ∉ Set.range f}) R :=
    Matrix.fromBlocks topLeft
      (0 : Matrix (Set.range f) {i : Fin m // i ∉ Set.range f} R)
      bottomLeft
      (1 : Matrix {i : Fin m // i ∉ Set.range f} {i : Fin m // i ∉ Set.range f} R)
  have hblock :
      B.reindex eCompl eCompl = blockMatrix := by
    -- After reordering rows and columns into chosen rows versus complementary rows, the padded
    -- minor becomes lower block triangular with identity on the complementary block.
    ext i j; cases i <;> cases j
    · simp [B, cols, eCompl, splitCols, splitFun, topLeft, blockMatrix, leftCols', rightCols']
    · rename_i i j
      have hij : (i : Fin m) ≠ j := by
        intro h
        exact j.2 (h ▸ i.2)
      simp [B, cols, eCompl, splitCols, splitFun, topLeft, blockMatrix, leftCols', rightCols',
        hij]
    · simp [B, cols, eCompl, splitCols, splitFun, bottomLeft, blockMatrix, leftCols', rightCols']
    · rename_i i j
      by_cases hij : i = j
      · subst hij
        simp [B, cols, eCompl, splitCols, splitFun, blockMatrix, leftCols', rightCols']
      · have hne : (i : Fin m) ≠ j := by
          intro h
          exact hij (Subtype.ext h)
        simp [B, cols, eCompl, splitCols, splitFun, blockMatrix, leftCols', rightCols', hij, hne]
  have htop :
      topLeft = (A.submatrix f g).reindex eRange eRange := by
    -- The top-left block is exactly the chosen `k × k` minor, reindexed by the range equivalence.
    ext i j
    change A i.1 (leftCols' j) = A (f (eRange.symm i)) (g (eRange.symm j))
    rw [show f (eRange.symm i) = i.1 by
      exact congrArg Subtype.val (eRange.apply_symm_apply i)]
    rfl
  refine ⟨cols, ?_⟩
  -- Determinants are unchanged by the reindexing, and the lower triangular block has determinant
  -- equal to the determinant of its top-left block.
  calc
    B.det = (B.reindex eCompl eCompl).det := by
      symm
      exact Matrix.det_reindex_self eCompl B
    _ = blockMatrix.det := by rw [hblock]
    _ = topLeft.det := by rw [Matrix.det_fromBlocks_zero₁₂, Matrix.det_one, mul_one]
    _ = ((A.submatrix f g).reindex eRange eRange).det := by rw [htop]
    _ = (A.submatrix f g).det := by rw [Matrix.det_reindex_self eRange]

/-- Helper for Exercise 4.5: if every full-row minor of `(A | I)` has determinant `0`, `1`, or
`-1`, then every square minor of `A` does as well. -/
theorem isTotallyUnimodular_of_fromColsOne
    (A : Matrix (Fin m) (Fin n) R)
    (hA : ∀ cols : Fin m ↪ Fin n ⊕ Fin m,
      ((Matrix.fromCols A (1 : Matrix (Fin m) (Fin m) R)).submatrix id cols).det ∈
        Set.range SignType.cast) :
    A.IsTotallyUnimodular := by
  -- Reduce total unimodularity to the arbitrary-minor formulation and only use padding when the
  -- selected rows and columns are injective.
  rw [Matrix.isTotallyUnimodular_iff]
  intro k f g
  by_cases hfg : Function.Injective f ∧ Function.Injective g
  · obtain ⟨cols, hcols⟩ := Matrix.padded_minor_det_fromCols_one A f g hfg.1 hfg.2
    simpa [hcols] using hA cols
  · use 0
    simp_rw [not_and_or, Function.not_injective_iff] at hfg
    obtain ⟨i, j, hfij, hij⟩ | ⟨i, j, hgij, hij⟩ := hfg
    · rw [← Matrix.det_transpose, Matrix.transpose_submatrix]
      symm
      apply Matrix.det_zero_of_column_eq hij.symm
      simp [hfij]
    · symm
      apply Matrix.det_zero_of_column_eq hij
      simp [hgij]

end Matrix

/- Exercise 4.5 (1). Condition (1) is equivalent to condition (2): this is the canonical mathlib
theorem `Matrix.transpose_isTotallyUnimodular_iff`. -/
recall Matrix.transpose_isTotallyUnimodular_iff

/-- Exercise 4.5 (2). Condition (1) is equivalent to condition (3): `A` is totally unimodular if
and only if the block matrix `(A | -A)`, represented in Lean by `Matrix.fromCols A (-A)`, is
totally unimodular. -/
theorem exercise_4_5_totally_unimodular_fromCols_neg_iff
    (A : Matrix (Fin m) (Fin n) R) :
    A.IsTotallyUnimodular ↔ (Matrix.fromCols A (-A)).IsTotallyUnimodular := by
  constructor
  · intro hA
    have hDup : (Matrix.fromCols A A).IsTotallyUnimodular := by
      have hsub : Matrix.fromCols A A = A.submatrix id (Sum.elim id id) := by
        ext i j
        cases j <;> rfl
      simpa [hsub] using hA.submatrix id (Sum.elim id id)
    have hRows : (Matrix.fromRows A.transpose A.transpose).IsTotallyUnimodular := by
      -- Move the duplicated-column statement to the transpose, where sign changes act on rows.
      simpa [Matrix.transpose_fromCols] using hDup.transpose
    let s : Fin n ⊕ Fin n → Bool := Sum.elim (fun _ : Fin n ↦ false) (fun _ : Fin n ↦ true)
    have hFlip :
        ((Matrix.fromRows A.transpose A.transpose).flipRowSigns s).IsTotallyUnimodular :=
      hRows.flipRowSigns s
    have hEq :
        (Matrix.fromRows A.transpose A.transpose).flipRowSigns s =
          Matrix.fromRows A.transpose (-A.transpose) := by
      -- Flipping exactly the second block of rows negates the second block.
      ext i j; cases i <;> simp [s, Matrix.flipRowSigns]
    have hNegRows : (Matrix.fromRows A.transpose (-A.transpose)).IsTotallyUnimodular := by
      simpa [hEq] using hFlip
    -- Transposing back turns the row statement into the desired column statement.
    simpa [Matrix.transpose_fromRows] using hNegRows.transpose
  · intro hA
    -- Recover `A` as the left block submatrix of `(A | -A)`.
    simpa using hA.submatrix id Sum.inl

/-- Exercise 4.5 (3). Condition (1) is equivalent to condition (4): `A` is totally unimodular if
and only if the block matrix `(A | I)`, represented in Lean by
`Matrix.fromCols A (1 : Matrix (Fin m) (Fin m) R)`, is unimodular in the Chapter 1 sense. -/
theorem exercise_4_5_totally_unimodular_fromCols_one_isUnimodular_iff
    (A : Matrix (Fin m) (Fin n) R) :
    A.IsTotallyUnimodular ↔
      ∀ cols : Fin m ↪ Fin n ⊕ Fin m,
        ((Matrix.fromCols A (1 : Matrix (Fin m) (Fin m) R)).submatrix id cols).det ∈
          Set.range SignType.cast := by
  constructor
  · intro hA
    have hAI :
        (Matrix.fromCols A (1 : Matrix (Fin m) (Fin m) R)).IsTotallyUnimodular :=
      hA.fromCols_one
    rw [Matrix.isTotallyUnimodular_iff] at hAI
    -- Full-row minors are a special case of the arbitrary square minors controlled by total
    -- unimodularity.
    intro cols
    simpa using hAI m id cols
  · intro hA
    -- Pad each injective square minor of `A` with identity columns to reduce to the Chapter 1
    -- unimodularity hypothesis on `(A | I)`.
    exact Matrix.isTotallyUnimodular_of_fromColsOne A hA

/-- Exercise 4.5 (4). Condition (1) is equivalent to condition (5): `A` is totally unimodular if
and only if every matrix obtained from `A` by changing the signs of all entries in some rows,
represented in Lean by `A.flipRowSigns s`, is totally unimodular. -/
theorem exercise_4_5_totally_unimodular_flipRowSigns_iff
    (A : Matrix (Fin m) (Fin n) R) :
    A.IsTotallyUnimodular ↔
      ∀ s : Fin m → Bool, (A.flipRowSigns s).IsTotallyUnimodular := by
  constructor
  · intro hA s
    -- Row sign changes preserve total unimodularity.
    exact hA.flipRowSigns s
  · intro hA
    -- Choosing the trivial sign pattern recovers the original matrix.
    simpa [Matrix.flipRowSigns] using hA (fun _ ↦ false)

end Exercise45
