/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import Mathlib.LinearAlgebra.Matrix.Circulant

public section

open scoped Matrix

universe u

namespace Matrix

variable {α : Type u}

/- Definition 5.12. Circulant `n × n` matrices are represented by the canonical
mathlib owner `Matrix.circulant`; `Matrix.circulant_apply` gives the displayed
entrywise formula, and `Matrix.circulant_col_zero_eq` states that the generating
vector is the first column entrywise. -/
#check Matrix.circulant
#check Matrix.circulant_apply
#check Matrix.circulant_col_zero_eq

/-- The first column of `Matrix.circulant c` is the generating vector `c`. -/
theorem circulant_col_zero {n : ℕ} [NeZero n] (c : Fin n → α) :
    (circulant c).col 0 = c := by
  ext i
  rw [col_apply, circulant_col_zero_eq]

end Matrix
