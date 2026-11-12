/-
Authors: Ziyu Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@d380aaa277a7a97379616d8bd2809e751c1052f4:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization contributors, confirmed by the submitter on 2026-11-04.
-/

module

public import Mathlib.Algebra.Field.Rat
public import Mathlib.Data.Fin.SuccPred
public import Mathlib.Data.Matrix.ColumnRowPartitioned
public import Mathlib.LinearAlgebra.Matrix.Block
public import Mathlib.Logic.Equiv.Fin.Basic

@[expose] public section

open scoped Matrix

namespace Matrix

section ColumnHermite

variable {m n : ℕ}

/-- A rational matrix `A : Matrix (Fin m) (Fin n) ℚ` is in column Hermite normal form when, after
identifying `n` with `m + r`, its columns split as `D` followed by a zero block, where `D` is
lower triangular, has positive diagonal entries, and every strict subdiagonal entry is
nonnegative and strictly smaller than the diagonal entry in its row. -/
def IsColumnHermiteNormalForm (A : Matrix (Fin m) (Fin n) ℚ) : Prop :=
  ∃ r : ℕ, ∃ h : n = m + r,
    let Aprime : Matrix (Fin m) (Fin m ⊕ Fin r) ℚ :=
      Matrix.reindex (Equiv.refl _) ((finCongr h).trans finSumFinEquiv.symm) A
    let D : Matrix (Fin m) (Fin m) ℚ := Matrix.toCols₁ Aprime
    let Z : Matrix (Fin m) (Fin r) ℚ := Matrix.toCols₂ Aprime
    Z = 0 ∧
      D.BlockTriangular OrderDual.toDual ∧
      (∀ i, 0 < D i i) ∧
      (∀ i j, j < i → 0 ≤ D i j ∧ D i j < D i i)

/-- remote integer-programming sorry cleanup Integer/Chapters/Chap01/section_1_5/ch1_sec1_5_2_definition_1_38/ColumnHermite.lean.
Expanding `A.IsColumnHermiteNormalForm` recovers the textbook horizontal block presentation:
after reindexing the columns of `A` as `Fin m ⊕ Fin r`, the matrix is `Matrix.fromCols D 0` with
the leading block `D` lower triangular, diagonally positive, and reduced below the diagonal. -/
theorem isColumnHermiteNormalForm_iff_exists_block
    (A : Matrix (Fin m) (Fin n) ℚ) :
    A.IsColumnHermiteNormalForm ↔
      ∃ r : ℕ, ∃ h : n = m + r, ∃ D : Matrix (Fin m) (Fin m) ℚ,
        Matrix.reindex (Equiv.refl _) ((finCongr h).trans finSumFinEquiv.symm) A =
          Matrix.fromCols D 0 ∧
        D.BlockTriangular OrderDual.toDual ∧
        (∀ i, 0 < D i i) ∧
        (∀ i j, j < i → 0 ≤ D i j ∧ D i j < D i i) := by
  constructor
  · -- Extract the canonical leading block and reconstruct the matrix from its two projections.
    intro hA
    unfold IsColumnHermiteNormalForm at hA
    rcases hA with ⟨r, h, hzero, htriangular, hpositive, hreduced⟩
    let A' : Matrix (Fin m) (Fin m ⊕ Fin r) ℚ :=
      Matrix.reindex (Equiv.refl _) ((finCongr h).trans finSumFinEquiv.symm) A
    have hblock : A' = Matrix.fromCols (Matrix.toCols₁ A') 0 := by
      calc
        A' = Matrix.fromCols (Matrix.toCols₁ A') (Matrix.toCols₂ A') :=
          (Matrix.fromCols_toCols A').symm
        _ = Matrix.fromCols (Matrix.toCols₁ A') 0 := congrArg _ hzero
    exact ⟨r, h, Matrix.toCols₁ A', hblock, htriangular, hpositive, hreduced⟩
  · -- Project the explicit block equality to recover the defining leading and trailing blocks.
    rintro ⟨r, h, D, hblock, htriangular, hpositive, hreduced⟩
    let A' : Matrix (Fin m) (Fin m ⊕ Fin r) ℚ :=
      Matrix.reindex (Equiv.refl _) ((finCongr h).trans finSumFinEquiv.symm) A
    have hleading : Matrix.toCols₁ A' = D := by
      simpa only [Matrix.toCols₁_fromCols] using congrArg Matrix.toCols₁ hblock
    have htrailing : Matrix.toCols₂ A' = 0 := by
      simpa only [Matrix.toCols₂_fromCols] using congrArg Matrix.toCols₂ hblock
    unfold IsColumnHermiteNormalForm
    refine ⟨r, h, htrailing, ?_, ?_, ?_⟩
    · rw [hleading]
      exact htriangular
    · rw [hleading]
      exact hpositive
    · rw [hleading]
      exact hreduced

/-- A matrix in column Hermite normal form has at least as many columns as rows. -/
theorem IsColumnHermiteNormalForm.shape
    {A : Matrix (Fin m) (Fin n) ℚ}
    (hA : A.IsColumnHermiteNormalForm) :
    m ≤ n := by
  -- The shape witness writes the number of columns as the number of rows plus a remainder.
  unfold IsColumnHermiteNormalForm at hA
  rcases hA with ⟨r, h, _⟩
  omega

/-- For a matrix in column Hermite normal form, the trailing block vanishes after the canonical
column reindexing to `Fin m ⊕ Fin r`. -/
theorem IsColumnHermiteNormalForm.trailing_zero
    {A : Matrix (Fin m) (Fin n) ℚ}
    (hA : A.IsColumnHermiteNormalForm) :
    ∃ r : ℕ, ∃ h : n = m + r,
      Matrix.toCols₂
          (Matrix.reindex (Equiv.refl _) ((finCongr h).trans finSumFinEquiv.symm) A) = 0 := by
  -- Reuse the same dimension witnesses and trailing-block equation stored in the definition.
  unfold IsColumnHermiteNormalForm at hA
  rcases hA with ⟨r, h, hzero, _⟩
  exact ⟨r, h, hzero⟩

#print axioms isColumnHermiteNormalForm_iff_exists_block

end ColumnHermite

end Matrix

end

#eval IO.println "M2F_PROOF_AXIOM_AUDIT_BEGIN_14b7c4d67f3b678f2ac6"
#print axioms _root_.Matrix.isColumnHermiteNormalForm_iff_exists_block
#eval IO.println "M2F_PROOF_AXIOM_AUDIT_END_14b7c4d67f3b678f2ac6"
