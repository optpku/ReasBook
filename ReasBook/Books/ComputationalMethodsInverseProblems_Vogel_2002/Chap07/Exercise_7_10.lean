/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import Mathlib.Data.Real.Basic
public import Mathlib.LinearAlgebra.Matrix.Trace
public import Mathlib.LinearAlgebra.UnitaryGroup

public section

open scoped Matrix

universe u

section

variable {n : Type u} [Fintype n] [DecidableEq n]

/-- Exercise 7.10. Conjugating a real matrix by an orthogonal matrix preserves its trace.

The source states this for symmetric `A`, but the trace identity does not use
that hypothesis. -/
theorem trace_eq_trace_orthogonal_conj
    (A U : Matrix n n ℝ)
    (hU : U ∈ Matrix.orthogonalGroup n ℝ) :
    Matrix.trace A = Matrix.trace (Uᵀ * A * U) := by
  have hU' : U * Uᵀ = 1 := (Matrix.mem_orthogonalGroup_iff n ℝ).mp hU
  calc
    Matrix.trace A = Matrix.trace (A * U * Uᵀ) := by
      simp [Matrix.mul_assoc, hU']
    _ = Matrix.trace (Uᵀ * A * U) := Matrix.trace_mul_cycle A U Uᵀ

end
