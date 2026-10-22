/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import Mathlib.Data.Real.Basic
public import Mathlib.LinearAlgebra.Matrix.Diagonal
public import Mathlib.LinearAlgebra.UnitaryGroup

public section

noncomputable section

open scoped Matrix

universe u

section

variable {n : Type u} [Fintype n] [DecidableEq n]

/-- The Chapter 7 influence matrix has the explicit orthogonal diagonalization
`(7.39)` with diagonal weights `w (s i ^ 2)`. -/
structure HasInfluenceMatrixSpectralRep
    (A U : Matrix n n ℝ) (w : ℝ → ℝ) (s : n → ℝ) : Prop where
  orthogonal : U ∈ Matrix.orthogonalGroup n ℝ
  eq_spectralRep : A = U * Matrix.diagonal (fun i ↦ w (s i ^ 2)) * Uᵀ

namespace HasInfluenceMatrixSpectralRep

set_option linter.defProp false in
/-- Build the Chapter 7 influence-matrix spectral representation from the
explicit orthogonality and diagonalization hypotheses. -/
def ofOrthogonalEq
    (hU : U ∈ Matrix.orthogonalGroup n ℝ)
    (hA : A = U * Matrix.diagonal (fun i ↦ w (s i ^ 2)) * Uᵀ) :
    HasInfluenceMatrixSpectralRep A U w s :=
  ⟨hU, hA⟩

/-- Unpack `HasInfluenceMatrixSpectralRep` into the underlying orthogonality and
diagonalization conditions. -/
theorem iff
    (A U : Matrix n n ℝ) (w : ℝ → ℝ) (s : n → ℝ) :
    HasInfluenceMatrixSpectralRep A U w s ↔
      U ∈ Matrix.orthogonalGroup n ℝ ∧
        A = U * Matrix.diagonal (fun i ↦ w (s i ^ 2)) * Uᵀ := by
  constructor
  · intro h
    exact ⟨h.orthogonal, h.eq_spectralRep⟩
  · rintro ⟨hU, hA⟩
    exact ofOrthogonalEq hU hA

end HasInfluenceMatrixSpectralRep

/-- The Chapter 7 reconstruction matrix has the explicit filter representation
`(7.36)` with scalar filter `w`, together with the convention `w 0 = 0`. -/
structure HasReconstructionSpectralRep
    (R U V : Matrix n n ℝ) (w : ℝ → ℝ) (s : n → ℝ) : Prop where
  filter_zero : w 0 = 0
  orthogonalU : U ∈ Matrix.orthogonalGroup n ℝ
  orthogonalV : V ∈ Matrix.orthogonalGroup n ℝ
  eq_spectralRep : R = V * Matrix.diagonal (fun i ↦ w (s i ^ 2) / s i) * Uᵀ

namespace HasReconstructionSpectralRep

set_option linter.defProp false in
/-- Build the Chapter 7 reconstruction-matrix filter representation from the
explicit zero-filter, orthogonality, and diagonalization hypotheses. -/
def ofOrthogonalEq
    (hw0 : w 0 = 0)
    (hU : U ∈ Matrix.orthogonalGroup n ℝ)
    (hV : V ∈ Matrix.orthogonalGroup n ℝ)
    (hR : R = V * Matrix.diagonal (fun i ↦ w (s i ^ 2) / s i) * Uᵀ) :
    HasReconstructionSpectralRep R U V w s :=
  ⟨hw0, hU, hV, hR⟩

/-- Unpack `HasReconstructionSpectralRep` into the underlying Chapter 7 filter
representation data. -/
theorem iff
    (R U V : Matrix n n ℝ) (w : ℝ → ℝ) (s : n → ℝ) :
    HasReconstructionSpectralRep R U V w s ↔
      w 0 = 0 ∧
        U ∈ Matrix.orthogonalGroup n ℝ ∧
          V ∈ Matrix.orthogonalGroup n ℝ ∧
            R = V * Matrix.diagonal (fun i ↦ w (s i ^ 2) / s i) * Uᵀ := by
  constructor
  · intro h
    exact ⟨h.filter_zero, h.orthogonalU, h.orthogonalV, h.eq_spectralRep⟩
  · rintro ⟨hw0, hU, hV, hR⟩
    exact ofOrthogonalEq hw0 hU hV hR

end HasReconstructionSpectralRep

end
