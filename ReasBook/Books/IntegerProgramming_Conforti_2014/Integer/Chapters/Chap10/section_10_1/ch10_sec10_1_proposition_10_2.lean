import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.Matrix.Order
import Mathlib.Data.Real.StarOrdered

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Matrix MatrixOrder

-- Domain sampling for this proposition:
-- * primary domain: positive semidefinite real matrices
-- * core/canonical owner: `Matrix.PosSemidef`
-- * canonical derived API already available upstream:
--   `Matrix.posSemidef_conjTranspose_mul_self`, `Matrix.PosSemidef.submatrix`,
--   `Matrix.PosSemidef.det_nonneg`, `Matrix.posSemidef_iff_eq_sum_vecMulVec`
-- * source-facing content that remains here: the two textbook equivalences of Proposition 10.2

section Proposition102

variable {n : ℕ}
variable {A : Matrix (Fin n) (Fin n) ℝ}

namespace Matrix

/-- Helper for Proposition 10.2: principal-minor nonnegativity descends to the lower-right block
of a `Fin 1 ⊕ Fin n` block decomposition. -/
theorem principalDetNonneg_toBlocks₂₂
    {n : ℕ} {B : Matrix (Fin 1 ⊕ Fin n) (Fin 1 ⊕ Fin n) ℝ}
    (hprincipal : ∀ ⦃d : ℕ⦄ (e : Fin d ↪ Fin 1 ⊕ Fin n), 0 ≤ (B.submatrix e e).det) :
    ∀ ⦃d : ℕ⦄ (e : Fin d ↪ Fin n), 0 ≤ ((B.toBlocks₂₂).submatrix e e).det := by
  let inrEmbedding : Fin n ↪ Fin 1 ⊕ Fin n :=
    ⟨Sum.inr, fun _ _ h ↦ Sum.inr.inj h⟩
  -- Restrict the principal-minor hypothesis along the canonical inclusion of the lower block.
  intro d e
  simpa [Matrix.toBlocks₂₂, inrEmbedding] using hprincipal (e.trans inrEmbedding)

/-- Helper for Proposition 10.2: a zero leading pivot forces the first row block to vanish once
all principal minors are nonnegative. -/
theorem crossBlock_eq_zero_of_zeroLeadingPrincipal
    {n : ℕ} {B : Matrix (Fin 1 ⊕ Fin n) (Fin 1 ⊕ Fin n) ℝ}
    (hBsymm : B.IsSymm)
    (h00 : B (Sum.inl 0) (Sum.inl 0) = 0)
    (hprincipal : ∀ ⦃d : ℕ⦄ (e : Fin d ↪ Fin 1 ⊕ Fin n), 0 ≤ (B.submatrix e e).det) :
    B.toBlocks₁₂ = 0 := by
  ext i j
  fin_cases i
  let e : Fin 2 ↪ Fin 1 ⊕ Fin n :=
    { toFun := fun k => if k = 0 then Sum.inl 0 else Sum.inr j
      inj' := by
        intro k l hkl
        fin_cases k <;> fin_cases l <;> simp at hkl ⊢ }
  have hdet := hprincipal e
  have hsymmEntry : B (Sum.inr j) (Sum.inl 0) = B (Sum.inl 0) (Sum.inr j) := by
    -- Symmetry turns the mixed entries of the `2 × 2` principal minor into the same scalar.
    simpa [Matrix.IsSymm, Matrix.transpose_apply] using
      congr_fun (congr_fun hBsymm (Sum.inl 0)) (Sum.inr j)
  rw [Matrix.det_fin_two] at hdet
  -- The `2 × 2` determinant simplifies to `-(B₀ⱼ)^2`, so nonnegativity forces `B₀ⱼ = 0`.
  have hdet' : (B (Sum.inl 0) (Sum.inr j)) ^ 2 ≤ 0 := by
    simpa [Matrix.submatrix, e, h00, hsymmEntry, sq] using hdet
  have hsq : (B (Sum.inl 0) (Sum.inr j)) ^ 2 = 0 := le_antisymm hdet' (sq_nonneg _)
  exact sq_eq_zero_iff.mp hsq

/-- Helper for Proposition 10.2: adjoining a zero first row and column preserves positive
semidefiniteness. -/
theorem posSemidef_fromBlocks_zero
    {n : ℕ} {C : Matrix (Fin n) (Fin n) ℝ} (hC : C.PosSemidef) :
    (Matrix.fromBlocks (0 : Matrix (Fin 1) (Fin 1) ℝ) 0 0 C).PosSemidef := by
  rcases CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hC.nonneg with ⟨U, hU⟩
  let V : Matrix (Fin n) (Fin 1 ⊕ Fin n) ℝ :=
    Matrix.of fun i => Sum.elim (fun _ => 0) (U i)
  have hU' : C = Uᵀ * U := by
    -- Over `ℝ`, the star in the square-root witness is just transpose.
    simpa [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial] using hU
  have hVeq : Vᵀ * V = Matrix.fromBlocks (0 : Matrix (Fin 1) (Fin 1) ℝ) 0 0 C := by
    -- The lifted witness has zero first column, so only the lower-right block survives.
    ext i j
    cases i <;> cases j <;> simp [V, hU', Matrix.mul_apply]
  have hVpsd : (Vᵀ * V).PosSemidef := by
    -- Gram matrices are positive semidefinite.
    simpa [Matrix.conjTranspose_eq_transpose_of_trivial, V] using
      (Matrix.posSemidef_conjTranspose_mul_self V)
  rwa [hVeq] at hVpsd

/-- Helper for Proposition 10.2: selecting the leading pivot together with a tail principal
submatrix yields the expected block matrix. -/
theorem submatrixIncludePivot_eq_fromBlocks
    {n d : ℕ} (B : Matrix (Fin 1 ⊕ Fin n) (Fin 1 ⊕ Fin n) ℝ) (e : Fin d ↪ Fin n) :
    let lift : Fin 1 ⊕ Fin d ↪ Fin 1 ⊕ Fin n :=
      { toFun := Sum.elim Sum.inl (fun i => Sum.inr (e i))
        inj' := by
          intro i j hij
          cases i <;> cases j
          · simpa using hij
          · cases hij
          · cases hij
          · exact congrArg Sum.inr <| e.injective <| by simpa using hij }
    B.submatrix lift lift =
      Matrix.fromBlocks B.toBlocks₁₁ (B.toBlocks₁₂.submatrix id e)
        (B.toBlocks₂₁.submatrix e id) (B.toBlocks₂₂.submatrix e e) := by
  let lift : Fin 1 ⊕ Fin d ↪ Fin 1 ⊕ Fin n :=
    { toFun := Sum.elim Sum.inl (fun i => Sum.inr (e i))
      inj' := by
        intro i j hij
        cases i <;> cases j
        · simpa using hij
        · cases hij
        · cases hij
        · exact congrArg Sum.inr <| e.injective <| by simpa using hij }
  -- Compare the lifted principal submatrix entrywise against the canonical block decomposition.
  ext i j
  cases i <;> cases j <;> rfl

/-- Helper for Proposition 10.2: taking a tail principal submatrix commutes with the Schur
complement attached to the leading `1 × 1` block. -/
theorem submatrix_schurComplement_toBlocks₁₁
    {n d : ℕ} (B : Matrix (Fin 1 ⊕ Fin n) (Fin 1 ⊕ Fin n) ℝ) (e : Fin d ↪ Fin n)
    [Invertible B.toBlocks₁₁] :
    B.toBlocks₂₂.submatrix e e
        - B.toBlocks₂₁.submatrix e id * ⅟(B.toBlocks₁₁) * B.toBlocks₁₂.submatrix id e =
      (B.toBlocks₂₂ - B.toBlocks₂₁ * ⅟(B.toBlocks₁₁) * B.toBlocks₁₂).submatrix e e := by
  have hMul₁ :
      B.toBlocks₂₁.submatrix e id * ⅟(B.toBlocks₁₁) =
        (B.toBlocks₂₁ * ⅟(B.toBlocks₁₁)).submatrix e id := by
    simpa using
      (Matrix.submatrix_mul B.toBlocks₂₁ (⅟(B.toBlocks₁₁)) e id id Function.bijective_id).symm
  have hMul₂ :
      (B.toBlocks₂₁ * ⅟(B.toBlocks₁₁)).submatrix e id * B.toBlocks₁₂.submatrix id e =
        (B.toBlocks₂₁ * ⅟(B.toBlocks₁₁) * B.toBlocks₁₂).submatrix e e := by
    simpa [Matrix.mul_assoc] using
      (Matrix.submatrix_mul (B.toBlocks₂₁ * ⅟(B.toBlocks₁₁)) B.toBlocks₁₂ e id e
        Function.bijective_id).symm
  -- Push the principal-submatrix operation through subtraction and multiplication once.
  rw [Matrix.submatrix_sub]
  calc
    B.toBlocks₂₂.submatrix e e
        - B.toBlocks₂₁.submatrix e id * ⅟(B.toBlocks₁₁) * B.toBlocks₁₂.submatrix id e
      = B.toBlocks₂₂.submatrix e e -
          (B.toBlocks₂₁ * ⅟(B.toBlocks₁₁) * B.toBlocks₁₂).submatrix e e := by
            rw [hMul₁, hMul₂]
    _ = (B.toBlocks₂₂ - B.toBlocks₂₁ * ⅟(B.toBlocks₁₁) * B.toBlocks₁₂).submatrix e e := by
      rfl

/-- Helper for Proposition 10.2: positivity of the unique diagonal entry makes a real `1 × 1`
matrix positive definite. -/
theorem posDefFinOneOfPos {a : Matrix (Fin 1) (Fin 1) ℝ} (ha : 0 < a 0 0) : a.PosDef := by
  have hdiag : a = Matrix.diagonal fun _ : Fin 1 => a 0 0 := by
    -- A `1 × 1` matrix is already diagonal with its only entry.
    ext i j
    fin_cases i
    fin_cases j
    simp
  rw [hdiag]
  simpa using (Matrix.PosDef.diagonal fun _ : Fin 1 => ha)

/-- Helper for Proposition 10.2: principal-minor nonnegativity passes from a symmetric block
matrix to the Schur complement of a positive leading `1 × 1` block. -/
theorem principalDetNonneg_schurComplement
    {n : ℕ} {B : Matrix (Fin 1 ⊕ Fin n) (Fin 1 ⊕ Fin n) ℝ}
    (hprincipal : ∀ ⦃d : ℕ⦄ (e : Fin d ↪ Fin 1 ⊕ Fin n), 0 ≤ (B.submatrix e e).det)
    [Invertible B.toBlocks₁₁] (hLeadingPos : 0 < (B.toBlocks₁₁) 0 0) :
    ∀ ⦃d : ℕ⦄ (e : Fin d ↪ Fin n),
      0 ≤ ((B.toBlocks₂₂ - B.toBlocks₂₁ * ⅟(B.toBlocks₁₁) * B.toBlocks₁₂).submatrix e e).det := by
  intro d e
  let lift : Fin 1 ⊕ Fin d ↪ Fin 1 ⊕ Fin n :=
    { toFun := Sum.elim Sum.inl (fun i => Sum.inr (e i))
      inj' := by
        intro i j hij
        cases i <;> cases j
        · simpa using hij
        · cases hij
        · cases hij
        · exact congrArg Sum.inr <| e.injective <| by simpa using hij }
  let withPivot : Fin (1 + d) ↪ Fin 1 ⊕ Fin n :=
    finSumFinEquiv.symm.toEmbedding.trans lift
  have hwithPivotEq :
      B.submatrix withPivot withPivot =
        (B.submatrix lift lift).submatrix finSumFinEquiv.symm finSumFinEquiv.symm := by
    rfl
  have hdetWithPivot :
      0 ≤ ((B.submatrix lift lift).submatrix finSumFinEquiv.symm finSumFinEquiv.symm).det := by
    -- Reindex the pivot-containing principal minor to `Fin (1 + d)` so `hprincipal` applies.
    simpa [hwithPivotEq] using hprincipal withPivot
  have hdetLift : 0 ≤ (B.submatrix lift lift).det := by
    have hdetLiftEq :
        ((B.submatrix lift lift).submatrix finSumFinEquiv.symm finSumFinEquiv.symm).det =
          (B.submatrix lift lift).det := by
      simpa using
        (Matrix.det_submatrix_equiv_self finSumFinEquiv.symm (B.submatrix lift lift))
    rw [hdetLiftEq] at hdetWithPivot
    exact hdetWithPivot
  have hBlockEq :
      B.submatrix lift lift =
        Matrix.fromBlocks B.toBlocks₁₁ (B.toBlocks₁₂.submatrix id e)
          (B.toBlocks₂₁.submatrix e id) (B.toBlocks₂₂.submatrix e e) := by
    -- Normalize the lifted principal minor into block form once.
    simpa [lift] using (submatrixIncludePivot_eq_fromBlocks (B := B) e)
  rw [hBlockEq] at hdetLift
  have hdetBlock :
      0 ≤
        (Matrix.fromBlocks B.toBlocks₁₁ (B.toBlocks₁₂.submatrix id e)
          (B.toBlocks₂₁.submatrix e id) (B.toBlocks₂₂.submatrix e e)).det := hdetLift
  have hdetA : 0 < B.toBlocks₁₁.det := by
    simpa [Matrix.det_fin_one] using hLeadingPos
  have hdetSchur :
      0 ≤
        (B.toBlocks₂₂.submatrix e e -
          B.toBlocks₂₁.submatrix e id * ⅟(B.toBlocks₁₁) * B.toBlocks₁₂.submatrix id e).det := by
    -- Normalize that principal minor into the block form seen by `det_fromBlocks₁₁`.
    rw [Matrix.det_fromBlocks₁₁] at hdetBlock
    -- The leading `1 × 1` determinant is positive, so the Schur-complement
    -- determinant is nonnegative.
    nlinarith
  rw [submatrix_schurComplement_toBlocks₁₁] at hdetSchur
  exact hdetSchur

/-- Helper for Proposition 10.2: the Schur complement of a symmetric block matrix along the
leading `1 × 1` block is again symmetric. -/
theorem isSymm_schurComplement_toBlocks₁₁
    {n : ℕ} {B : Matrix (Fin 1 ⊕ Fin n) (Fin 1 ⊕ Fin n) ℝ}
    (hBsymm : B.IsSymm) [Invertible B.toBlocks₁₁] :
    (B.toBlocks₂₂ - B.toBlocks₂₁ * ⅟(B.toBlocks₁₁) * B.toBlocks₁₂).IsSymm := by
  have hTail : B.toBlocks₂₂.IsSymm := by
    -- The lower-right block inherits symmetry from the ambient matrix.
    simpa [Matrix.toBlocks₂₂] using hBsymm.submatrix Sum.inr
  have hBlocks :
      (Matrix.fromBlocks B.toBlocks₁₁ B.toBlocks₁₂ B.toBlocks₂₁ B.toBlocks₂₂).IsSymm := by
    -- Re-express the ambient matrix in block form once to read off the mixed-block relation.
    simpa using ((Matrix.fromBlocks_toBlocks B).symm ▸ hBsymm)
  have h21 : B.toBlocks₂₁ = B.toBlocks₁₂ᵀ := by
    exact ((Matrix.isSymm_fromBlocks_iff.mp hBlocks).2.1).symm
  have hMixed : (B.toBlocks₂₁ * ⅟(B.toBlocks₁₁) * B.toBlocks₁₂).IsSymm := by
    -- The mixed term is `bᵀ * scalar * b`, hence symmetric over `ℝ`.
    rw [Matrix.IsSymm]
    ext i j
    simp [Matrix.transpose_apply, Matrix.mul_apply, h21]
    ring
  exact hTail.sub hMixed

/-- A real Gram factorization `A = Uᵀ * U` is a canonical source-facing bridge to the owner
predicate `A.PosSemidef`. -/
theorem posSemidef_of_eq_transpose_mul_self
    {d : ℕ} (U : Matrix (Fin d) (Fin n) ℝ) (hA : A = Uᵀ * U) :
    A.PosSemidef := by
  rw [hA]
  simpa using Matrix.posSemidef_conjTranspose_mul_self U

/-- Proposition 10.2. For a symmetric real matrix, nonnegative determinants of all principal
submatrices imply positive semidefiniteness. Combined with the standard Gram factorization and
principal-submatrix determinant facts below, this yields the textbook equivalence. -/
theorem posSemidef_of_isSymm_of_nonneg_det_principal_submatrix
    (hA : A.IsSymm) (hprincipal : ∀ ⦃d : ℕ⦄ (e : Fin d ↪ Fin n), 0 ≤ (A.submatrix e e).det) :
    A.PosSemidef := by
  classical
  induction n with
  | zero =>
      -- The empty matrix is the zero matrix, so positive semidefiniteness is immediate.
      simpa [Subsingleton.elim A 0] using
        (Matrix.PosSemidef.zero : (0 : Matrix (Fin 0) (Fin 0) ℝ).PosSemidef)
  | succ n ih =>
      -- Route correction: normalize once to a `Fin 1 ⊕ Fin n` block matrix before splitting on the
      -- leading `1 × 1` pivot.
      let blockEquiv : Fin 1 ⊕ Fin n ≃ Fin (n + 1) :=
        finSumFinEquiv.trans (finCongr (Nat.add_comm 1 n))
      let B : Matrix (Fin 1 ⊕ Fin n) (Fin 1 ⊕ Fin n) ℝ :=
        A.submatrix blockEquiv blockEquiv
      let a : Matrix (Fin 1) (Fin 1) ℝ := B.toBlocks₁₁
      let b : Matrix (Fin 1) (Fin n) ℝ := B.toBlocks₁₂
      let C : Matrix (Fin n) (Fin n) ℝ := B.toBlocks₂₂
      have hBsymm : B.IsSymm := by
        simpa [B, blockEquiv] using hA.submatrix blockEquiv
      have hBprincipal :
          ∀ ⦃d : ℕ⦄ (e : Fin d ↪ Fin 1 ⊕ Fin n), 0 ≤ (B.submatrix e e).det := by
        -- Transport principal-minor nonnegativity across the single boundary reindex.
        intro d e
        simpa [B, blockEquiv] using hprincipal (e.trans blockEquiv.toEmbedding)
      have hCsymm : C.IsSymm := by
        -- The tail block inherits symmetry from the reindexed ambient matrix.
        simpa [C, Matrix.toBlocks₂₂] using hBsymm.submatrix Sum.inr
      have hCprincipal : ∀ ⦃d : ℕ⦄ (e : Fin d ↪ Fin n), 0 ≤ (C.submatrix e e).det :=
        principalDetNonneg_toBlocks₂₂ hBprincipal
      by_cases ha0 : a 0 0 = 0
      · have haZero : a = 0 := by
          -- A `1 × 1` matrix is determined by its unique entry.
          ext i j
          fin_cases i
          fin_cases j
          simpa [a] using ha0
        have hbZero : b = 0 := by
          -- The zero leading pivot kills every mixed entry through the `2 × 2` principal minors.
          refine crossBlock_eq_zero_of_zeroLeadingPrincipal hBsymm ?_ hBprincipal
          simpa [a, Matrix.toBlocks₁₁] using ha0
        have hBsymmBlocks : (Matrix.fromBlocks a b B.toBlocks₂₁ C).IsSymm := by
          -- Re-express the reindexed matrix in block form once to read off the transpose relation.
          dsimp [a, b, C]
          simpa using ((Matrix.fromBlocks_toBlocks B).symm ▸ hBsymm)
        have h21 : B.toBlocks₂₁ = bᵀ := by
          exact ((Matrix.isSymm_fromBlocks_iff.mp hBsymmBlocks).2.1).symm
        have h21Zero : B.toBlocks₂₁ = 0 := by
          rw [h21, hbZero]
          simp
        have hCpsd : C.PosSemidef := ih hCsymm hCprincipal
        have hBpsd : B.PosSemidef := by
          -- After the mixed blocks vanish, the matrix is the zero-extension of the tail block.
          have hBdecomp : B = Matrix.fromBlocks (0 : Matrix (Fin 1) (Fin 1) ℝ) 0 0 C := by
            calc
              B = Matrix.fromBlocks a b B.toBlocks₂₁ C := by
                symm
                exact Matrix.fromBlocks_toBlocks B
              _ = Matrix.fromBlocks (0 : Matrix (Fin 1) (Fin 1) ℝ) 0 0 C := by
                rw [haZero, hbZero, h21Zero]
          rw [hBdecomp]
          exact posSemidef_fromBlocks_zero hCpsd
        -- Transport positive semidefiniteness back across the single boundary reindex.
        simpa [B, blockEquiv] using (Matrix.posSemidef_submatrix_equiv blockEquiv).mp hBpsd
      · -- TODO: show `0 < a 0 0`, transport principal-minor nonnegativity to the Schur
        -- complement, apply the induction hypothesis there, and finish with
        -- `Matrix.PosDef.fromBlocks₁₁`.
        have hLeadingNonneg : 0 ≤ a 0 0 := by
          let inlEmbedding : Fin 1 ↪ Fin 1 ⊕ Fin n :=
            ⟨Sum.inl, fun _ _ h ↦ Sum.inl.inj h⟩
          -- The `1 × 1` principal minor at the pivot is exactly the leading entry.
          simpa [a, Matrix.toBlocks₁₁, Matrix.det_fin_one, inlEmbedding] using
            hBprincipal inlEmbedding
        have hLeadingPos : 0 < a 0 0 := by
          exact lt_of_le_of_ne hLeadingNonneg (fun h ↦ ha0 h.symm)
        have haposDef : a.PosDef := posDefFinOneOfPos hLeadingPos
        letI : Invertible a := haposDef.isUnit.invertible
        have hSsymm : (C - B.toBlocks₂₁ * ⅟a * b).IsSymm := by
          -- The Schur complement keeps the symmetry needed for the induction hypothesis.
          simpa [a, b, C] using (isSymm_schurComplement_toBlocks₁₁ (B := B) hBsymm)
        have hSprincipal :
            ∀ ⦃d : ℕ⦄ (e : Fin d ↪ Fin n), 0 ≤ ((C - B.toBlocks₂₁ * ⅟a * b).submatrix e e).det := by
          -- Principal-minor nonnegativity descends across the positive pivot.
          simpa [a, b, C] using
            (principalDetNonneg_schurComplement (B := B) hBprincipal hLeadingPos)
        have hSpsd : (C - B.toBlocks₂₁ * ⅟a * b).PosSemidef := ih hSsymm hSprincipal
        have hBsymmBlocks : (Matrix.fromBlocks a b B.toBlocks₂₁ C).IsSymm := by
          -- Re-express the reindexed matrix in block form once to identify the mixed blocks.
          dsimp [a, b, C]
          simpa using ((Matrix.fromBlocks_toBlocks B).symm ▸ hBsymm)
        have h21 : B.toBlocks₂₁ = bᵀ := by
          exact ((Matrix.isSymm_fromBlocks_iff.mp hBsymmBlocks).2.1).symm
        have hBpsd : B.PosSemidef := by
          -- Convert the Schur-complement PSD statement back into the full block matrix.
          have hBdecomp : B = Matrix.fromBlocks a b bᵀ C := by
            calc
              B = Matrix.fromBlocks a b B.toBlocks₂₁ C := by
                symm
                exact Matrix.fromBlocks_toBlocks B
              _ = Matrix.fromBlocks a b bᵀ C := by
                rw [h21]
          rw [hBdecomp]
          exact (Matrix.PosDef.fromBlocks₁₁ b C haposDef).2 <| by
            simpa
              [h21, Matrix.invOf_eq_nonsing_inv,
                Matrix.conjTranspose_eq_transpose_of_trivial] using
              hSpsd
        -- Transport positive semidefiniteness back across the single boundary reindex.
        simpa [B, blockEquiv] using (Matrix.posSemidef_submatrix_equiv blockEquiv).mp hBpsd

end Matrix

namespace Matrix.PosSemidef

/-- A positive semidefinite real matrix admits a square Gram factorization `A = Uᵀ * U`. This is
the canonical owner-level companion behind Proposition 10.2 (1); the textbook row bound `d ≤ n`
then follows by taking `d = n`. -/
theorem exists_eq_transpose_mul_self (hA : A.PosSemidef) :
    ∃ U : Matrix (Fin n) (Fin n) ℝ, A = Uᵀ * U := by
  -- Use the owner-level square-root characterization of nonnegative matrices.
  rcases CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hA.nonneg with ⟨U, hU⟩
  refine ⟨U, ?_⟩
  simpa [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial] using hU

/-- Every principal submatrix of a positive semidefinite real matrix has nonnegative determinant. -/
theorem nonneg_det_principal_submatrix
    (hA : A.PosSemidef) {d : ℕ} (e : Fin d ↪ Fin n) :
    0 ≤ (A.submatrix e e).det := by
  simpa using (hA.submatrix e).det_nonneg

end Matrix.PosSemidef

/-- First equivalence from Proposition 10.2. Over `ℝ`, positive semidefiniteness is equivalent to
admitting a Gram factorization `A = Uᵀ * U` with `U` having at most `n` rows. The source
symmetry hypothesis is redundant here, since both sides already force symmetry. -/
theorem posSemidef_iff_exists_transpose_mul_self
    (A : Matrix (Fin n) (Fin n) ℝ) :
    A.PosSemidef ↔ ∃ d : ℕ, d ≤ n ∧ ∃ U : Matrix (Fin d) (Fin n) ℝ, A = Uᵀ * U := by
  refine ⟨fun hA ↦ ?_, fun hA ↦ ?_⟩
  · rcases hA.exists_eq_transpose_mul_self with ⟨U, hU⟩
    exact ⟨n, le_rfl, U, hU⟩
  · rcases hA with ⟨d, hd, U, hU⟩
    exact Matrix.posSemidef_of_eq_transpose_mul_self U hU

/-- Second equivalence from Proposition 10.2. For a symmetric real square matrix,
positive semidefiniteness is equivalent to every principal submatrix having nonnegative
determinant. -/
theorem symmetric_posSemidef_iff_nonneg_det_principal_submatrix
    (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.IsSymm) :
    A.PosSemidef ↔ ∀ ⦃d : ℕ⦄ (e : Fin d ↪ Fin n), 0 ≤ (A.submatrix e e).det := by
  refine ⟨fun hpsd _ e ↦ hpsd.nonneg_det_principal_submatrix e, fun hprincipal ↦ ?_⟩
  exact Matrix.posSemidef_of_isSymm_of_nonneg_det_principal_submatrix hA hprincipal

end Proposition102
