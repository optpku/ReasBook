module

public import ReasLib.LinearAlgebra.EuclideanSpace.OrthogonalSum

/-!
Adapters for positive (semi-)definiteness on orthogonal-sum blocks.

The generic matrix facts live in `Mathlib.LinearAlgebra.Matrix.PosDef`; this
file records the forms used by the DFP orthogonal-sum construction, including
the positive-semidefinite analogue of the identity-block extension theorem.
-/

public section

noncomputable section

open scoped Matrix

namespace DFP.OrthogonalSum.PosDefAdapters

/-- Helper for OrthogonalSum PosDef adapters: the canonical extension is the
corresponding identity-block matrix from `Matrix.fromBlocks`. -/
theorem extendMatrix_eq_fromBlocks {m n : Type*} [DecidableEq n]
    (H : Matrix m m ℝ) :
    EuclideanSpace.OrthogonalSum.extendMatrix (κ := n) H =
      Matrix.fromBlocks H 0 0 1 := by
  ext i j
  cases i with
  | inl i =>
      cases j with
      | inl j =>
          exact EuclideanSpace.OrthogonalSum.extendMatrix_apply_inl_inl H i j
      | inr j =>
          exact EuclideanSpace.OrthogonalSum.extendMatrix_apply_inl_inr H i j
  | inr i =>
      cases j with
      | inl j =>
          exact EuclideanSpace.OrthogonalSum.extendMatrix_apply_inr_inl H i j
      | inr j =>
          simpa [Matrix.one_apply] using
            EuclideanSpace.OrthogonalSum.extendMatrix_apply_inr_inr H i j

/-!
The following two bridges keep the congruence direction explicit at call
sites.  They are useful when a block embedding is represented by a rectangular
matrix rather than by an equivalence.
-/

/-- Helper for OrthogonalSum PosDef adapters: congruence by a rectangular matrix
preserves positive semidefiniteness. -/
theorem posSemidef_congruence_left {m n : Type*} [Fintype m] [Fintype n]
    (A : Matrix n n ℝ) (B : Matrix n m ℝ) (hA : A.PosSemidef) :
    (Bᴴ * A * B).PosSemidef := by
  exact hA.conjTranspose_mul_mul_same B

/-- Helper for OrthogonalSum PosDef adapters: an injective rectangular
congruence preserves positive definiteness. -/
theorem posDef_congruence_left {m n : Type*} [Fintype m] [Fintype n]
    (A : Matrix n n ℝ) (B : Matrix n m ℝ) (hA : A.PosDef)
    (hB : Function.Injective B.mulVec) :
    (Bᴴ * A * B).PosDef := by
  exact hA.conjTranspose_mul_mul_same hB

/-- Helper for OrthogonalSum PosDef adapters: an invertible left congruence
reflects and preserves positive semidefiniteness. -/
theorem posSemidef_congruence_iff {n : Type*} [Fintype n] [DecidableEq n]
    (A U : Matrix n n ℝ) (hU : IsUnit U) :
    (star U * A * U).PosSemidef ↔ A.PosSemidef := by
  exact Matrix.IsUnit.posSemidef_star_left_conjugate_iff hU

/-- Helper for OrthogonalSum PosDef adapters: an invertible left congruence
reflects and preserves positive definiteness. -/
theorem posDef_congruence_iff {n : Type*} [Fintype n] [DecidableEq n]
    (A U : Matrix n n ℝ) (hU : IsUnit U) :
    (star U * A * U).PosDef ↔ A.PosDef := by
  exact Matrix.IsUnit.posDef_star_left_conjugate_iff hU

/-!
For the identity-block extension, the semidefinite direction is proved by
splitting a finitely-supported vector into its two summands.  This is the
missing PSD companion to `extendMatrix_posDef_iff`.
-/

/-- Helper for OrthogonalSum PosDef adapters: the zero rectangular block has
zero conjugate transpose. -/
lemma zero_conjTranspose_matrix {m n : Type*} :
    (0 : Matrix m n ℝ)ᴴ = 0 := by
  simp

/-- Helper for OrthogonalSum PosDef adapters: a finitely-supported vector on
an orthogonal sum is recovered from its two `Finsupp` components. -/
lemma sumElim_components_eq {m n : Type*}
    (z : (m ⊕ n) →₀ ℝ) :
    ((Finsupp.sumFinsuppEquivProdFinsupp z).1).sumElim
        ((Finsupp.sumFinsuppEquivProdFinsupp z).2) = z := by
  simp

/-- Positive semidefiniteness of an identity-block extension is equivalent to
positive semidefiniteness of its original block. -/
theorem extendMatrix_posSemidef_iff {m n : Type*} [DecidableEq n]
    (H : Matrix m m ℝ) :
    (EuclideanSpace.OrthogonalSum.extendMatrix (κ := n) H :
      Matrix (m ⊕ n) (m ⊕ n) ℝ).PosSemidef ↔ H.PosSemidef := by
  constructor
  · intro h
    have hsub := h.submatrix (Sum.inl : m → m ⊕ n)
    have heq :
        (EuclideanSpace.OrthogonalSum.extendMatrix (κ := n) H).submatrix
            (Sum.inl : m → m ⊕ n) Sum.inl = H := by
      rw [extendMatrix_eq_fromBlocks (n := n) H]
      ext i j
      rfl
    rw [heq] at hsub
    exact hsub
  · intro hH
    have hzero :
        (0 : Matrix m n ℝ)ᴴ = (0 : Matrix n m ℝ) :=
      zero_conjTranspose_matrix
    have hblocks :
        (Matrix.fromBlocks H (0 : Matrix m n ℝ) (0 : Matrix n m ℝ)
          (1 : Matrix n n ℝ)).IsHermitian := by
      apply Matrix.IsHermitian.fromBlocks
      · exact hH.1
      · exact hzero
      · exact Matrix.isHermitian_one
    have hHerm :
        (EuclideanSpace.OrthogonalSum.extendMatrix (κ := n) H :
          Matrix (m ⊕ n) (m ⊕ n) ℝ).IsHermitian := by
      rw [extendMatrix_eq_fromBlocks (n := n) H]
      exact hblocks
    refine ⟨hHerm, ?_⟩
    intro z
    let x : m →₀ ℝ := (Finsupp.sumFinsuppEquivProdFinsupp z).1
    let y : n →₀ ℝ := (Finsupp.sumFinsuppEquivProdFinsupp z).2
    have hdecomp : x.sumElim y = z := by
      exact sumElim_components_eq z
    rw [← hdecomp]
    change 0 ≤ (x.sumElim y).sum (fun i xi ↦
      (x.sumElim y).sum (fun j xj ↦
        star xi * EuclideanSpace.OrthogonalSum.extendMatrix H i j * xj))
    have hquad := EuclideanSpace.OrthogonalSum.quadraticForm_extendMatrix H x y
    have hquad' :
        (x.sumElim y).sum (fun i xi ↦
          (x.sumElim y).sum (fun j xj ↦
            star xi * EuclideanSpace.OrthogonalSum.extendMatrix H i j * xj)) =
          x.sum (fun i xi ↦ x.sum (fun j xj ↦ xi * H i j * xj)) +
            y.sum (fun _ yi ↦ yi ^ 2) := by
      simpa only [star_trivial] using hquad
    rw [hquad']
    have hx_nonneg := hH.2 x
    have hy_nonneg : 0 ≤ y.sum (fun _ yi ↦ yi ^ 2) := by
      exact Finsupp.sum_nonneg (fun i hi ↦ sq_nonneg (y i))
    exact add_nonneg hx_nonneg hy_nonneg

end DFP.OrthogonalSum.PosDefAdapters

end
