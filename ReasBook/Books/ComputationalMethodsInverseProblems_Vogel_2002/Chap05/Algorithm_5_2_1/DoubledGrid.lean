/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import Mathlib.Data.Complex.Basic
public import ComputationalMethodsInverseProblems_Vogel_2002.Chap05.Definition_5_25.Array

public section

noncomputable section

namespace Matrix

/-- Zero-pad an `n_x × n_y` array into the upper-left block of the doubled
`(n_x + n_x) × (n_y + n_y)` grid, with zeros elsewhere. -/
@[expose] def blockCirculantExtensionZeroPad
    {n_x n_y : ℕ}
    (r : Matrix (Fin n_x) (Fin n_y) ℂ) :
    Matrix (Fin (2 * n_x)) (Fin (2 * n_y)) ℂ :=
  Matrix.of fun i j ↦
    if hix : i.1 < n_x then
      if hjy : j.1 < n_y then
        r ⟨i.1, hix⟩ ⟨j.1, hjy⟩
      else
        0
    else
      0

/-- The defining entrywise formula for `Matrix.blockCirculantExtensionZeroPad`. -/
theorem blockCirculantExtensionZeroPad_apply
    {n_x n_y : ℕ}
    (r : Matrix (Fin n_x) (Fin n_y) ℂ)
    (i : Fin (2 * n_x)) (j : Fin (2 * n_y)) :
    Matrix.blockCirculantExtensionZeroPad r i j =
      if hix : i.1 < n_x then
        if hjy : j.1 < n_y then
          r ⟨i.1, hix⟩ ⟨j.1, hjy⟩
        else
          0
      else
        0 := by
  simp [Matrix.blockCirculantExtensionZeroPad]

/-- Extract the leading `n_x × n_y` block from a doubled-grid array. -/
abbrev blockCirculantExtensionLeadingBlock
    {n_x n_y : ℕ}
    (sExt : Matrix (Fin (2 * n_x)) (Fin (2 * n_y)) ℂ) :
    Matrix (Fin n_x) (Fin n_y) ℂ :=
  Matrix.subUpLeft
    (Matrix.reindex (finCongr (two_mul n_x)) (finCongr (two_mul n_y)) sExt)

end Matrix
