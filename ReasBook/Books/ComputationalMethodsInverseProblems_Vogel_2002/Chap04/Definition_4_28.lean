/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import Mathlib.LinearAlgebra.Matrix.Trace

public section

universe u v

namespace Matrix

/- Definition 4.28 (1). The canonical matrix-trace operator is `Matrix.trace`,
whose defining formula is `trace A = ∑ i, A i i`. -/
#check Matrix.trace

/-
Definition 4.28 (2). The canonical linear-map owner of matrix trace is
`Matrix.traceLinearMap`. The source-facing linearity formula is recorded by
`trace_add_smul` below.
-/
#check Matrix.traceLinearMap

/-- Definition 4.28 (2). The matrix trace is linear:
`trace (α • A + β • B) = α • trace A + β • trace B`. -/
theorem trace_add_smul
    {n : Type u} [Fintype n] {R : Type v} [Semiring R]
    (α β : R) (A B : Matrix n n R) :
    trace (α • A + β • B) = α • trace A + β • trace B := by
  rw [trace_add, trace_smul, trace_smul]

/- Definition 4.28 (3). The canonical transpose-invariance statement is
`Matrix.trace_transpose`. -/
#check Matrix.trace_transpose

end Matrix
