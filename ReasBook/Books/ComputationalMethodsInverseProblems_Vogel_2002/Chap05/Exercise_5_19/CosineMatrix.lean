/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import Mathlib.Analysis.Complex.Trigonometric
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.LinearAlgebra.Matrix.Defs

public section

/-- The explicit real cosine matrix with first column `1 / √n` and remaining columns
`√(2 / n) * cos (((2 * i + 1) * j * π) / (2 * n))` in zero-based `Fin n` coordinates. -/
noncomputable def cosineMatrix (n : ℕ) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j ↦
    if j.1 = 0 then
      1 / Real.sqrt n
    else
      Real.sqrt ((2 : ℝ) / n) *
        Real.cos (((2 * (i : ℝ) + 1) * (j : ℝ) * Real.pi) / (2 * n))

/-- The entrywise formula for `cosineMatrix`. -/
theorem cosineMatrix_apply (n : ℕ) (i j : Fin n) :
    cosineMatrix n i j =
      if j.1 = 0 then
        1 / Real.sqrt n
      else
        Real.sqrt ((2 : ℝ) / n) *
          Real.cos (((2 * (i : ℝ) + 1) * (j : ℝ) * Real.pi) / (2 * n)) := by
  rfl
