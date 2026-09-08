module

public import Mathlib.LinearAlgebra.Matrix.PosDef

public section

open scoped Matrix

namespace Matrix

/-- Helper for the block-congruence bridge: the quadratic form of a zero-cross-block
matrix is the sum of the two diagonal block quadratic forms. -/
theorem fromBlocks_zero_zero_dotProduct
    {m n : Type*} [Fintype m] [Fintype n]
    (A : Matrix m m ℝ) (D : Matrix n n ℝ) (z : m ⊕ n → ℝ) :
    star z ⬝ᵥ ((fromBlocks A 0 0 D) *ᵥ z) =
      star (z ∘ Sum.inl) ⬝ᵥ (A *ᵥ (z ∘ Sum.inl)) +
        star (z ∘ Sum.inr) ⬝ᵥ (D *ᵥ (z ∘ Sum.inr)) := by
  rw [fromBlocks_mulVec, dotProduct_block]
  simp [dotProduct, star_trivial]

/-- For the block-congruence bridge, a block diagonal matrix is positive
semidefinite exactly when both diagonal blocks are positive semidefinite. -/
theorem fromBlocks_zero_zero_posSemidef_iff
    {m n : Type*} [Finite m] [Finite n]
    (A : Matrix m m ℝ) (D : Matrix n n ℝ) :
    (fromBlocks A 0 0 D : Matrix (m ⊕ n) (m ⊕ n) ℝ).PosSemidef ↔
      A.PosSemidef ∧ D.PosSemidef := by
  -- Local instance justification (finite block indices): the finite quadratic-form
  -- characterization is used only inside this proof, while the public statement
  -- needs no chosen enumeration.
  letI := Fintype.ofFinite m
  letI := Fintype.ofFinite n
  constructor
  · intro h
    have hA := h.submatrix (Sum.inl : m → m ⊕ n)
    have hD := h.submatrix (Sum.inr : n → m ⊕ n)
    have hAeq :
        (fromBlocks A 0 0 D : Matrix (m ⊕ n) (m ⊕ n) ℝ).submatrix
            (Sum.inl : m → m ⊕ n) Sum.inl = A := by
      ext i j
      rfl
    have hDeq :
        (fromBlocks A 0 0 D : Matrix (m ⊕ n) (m ⊕ n) ℝ).submatrix
            (Sum.inr : n → m ⊕ n) Sum.inr = D := by
      ext i j
      rfl
    rw [hAeq] at hA
    rw [hDeq] at hD
    exact ⟨hA, hD⟩
  · rintro ⟨hA, hD⟩
    have hHerm :
        (fromBlocks A 0 0 D : Matrix (m ⊕ n) (m ⊕ n) ℝ).IsHermitian := by
      apply IsHermitian.fromBlocks
      · exact hA.1
      · simp
      · exact hD.1
    refine posSemidef_iff_dotProduct_mulVec.mpr ⟨hHerm, ?_⟩
    intro z
    rw [fromBlocks_zero_zero_dotProduct]
    exact add_nonneg
      (hA.dotProduct_mulVec_nonneg (z ∘ Sum.inl))
      (hD.dotProduct_mulVec_nonneg (z ∘ Sum.inr))

/-- For the block-congruence bridge, a block diagonal matrix is positive
definite exactly when both diagonal blocks are positive definite. -/
theorem fromBlocks_zero_zero_posDef_iff
    {m n : Type*} [Finite m] [Finite n]
    (A : Matrix m m ℝ) (D : Matrix n n ℝ) :
    (fromBlocks A 0 0 D : Matrix (m ⊕ n) (m ⊕ n) ℝ).PosDef ↔
      A.PosDef ∧ D.PosDef := by
  -- Local instance justification (finite block indices): the finite quadratic-form
  -- characterization is used only inside this proof, while the public statement
  -- needs no chosen enumeration.
  letI := Fintype.ofFinite m
  letI := Fintype.ofFinite n
  constructor
  · intro h
    have hA := h.submatrix Sum.inl_injective
    have hD := h.submatrix Sum.inr_injective
    have hAeq :
        (fromBlocks A 0 0 D : Matrix (m ⊕ n) (m ⊕ n) ℝ).submatrix
            (Sum.inl : m → m ⊕ n) Sum.inl = A := by
      ext i j
      rfl
    have hDeq :
        (fromBlocks A 0 0 D : Matrix (m ⊕ n) (m ⊕ n) ℝ).submatrix
            (Sum.inr : n → m ⊕ n) Sum.inr = D := by
      ext i j
      rfl
    rw [hAeq] at hA
    rw [hDeq] at hD
    exact ⟨hA, hD⟩
  · rintro ⟨hA, hD⟩
    have hHerm :
        (fromBlocks A 0 0 D : Matrix (m ⊕ n) (m ⊕ n) ℝ).IsHermitian := by
      apply IsHermitian.fromBlocks
      · exact hA.1
      · simp
      · exact hD.1
    refine posDef_iff_dotProduct_mulVec.mpr ⟨hHerm, ?_⟩
    intro z hz
    have hleft : z ∘ Sum.inl ≠ 0 ∨ z ∘ Sum.inr ≠ 0 := by
      classical
      by_cases hl : z ∘ Sum.inl = 0
      · right
        intro hr
        apply hz
        funext q
        cases q with
        | inl i => exact congrFun hl i
        | inr j => exact congrFun hr j
      · exact Or.inl hl
    rw [fromBlocks_zero_zero_dotProduct]
    rcases hleft with hleft | hright
    · exact add_pos_of_pos_of_nonneg
        (hA.dotProduct_mulVec_pos hleft)
        (hD.posSemidef.dotProduct_mulVec_nonneg (z ∘ Sum.inr))
    · exact add_pos_of_nonneg_of_pos
        (hA.posSemidef.dotProduct_mulVec_nonneg (z ∘ Sum.inl))
        (hD.dotProduct_mulVec_pos hright)

end Matrix
