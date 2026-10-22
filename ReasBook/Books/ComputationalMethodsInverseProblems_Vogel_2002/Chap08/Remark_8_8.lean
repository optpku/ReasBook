/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import ComputationalMethodsInverseProblems_Vogel_2002.Chap05.Definition_5_24.BTTB
public import ComputationalMethodsInverseProblems_Vogel_2002.Chap08.Algorithm_8_2_4.Clauses
public import Mathlib.Data.Matrix.Mul
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Mathlib.LinearAlgebra.Matrix.Symmetric

public section

universe u v

open scoped Matrix

/- This item is intentionally kept as a source-facing blocker. The current
repository snapshot exposes the concrete Chapter 8 Newton-matrix formula and
the iterate-dependent bridge `TVPrimalDualNewton.HasIntermediateAssignments.lbar_eq`
for `L̄_v`, but it still lacks checked source-specific owners for the block
Toeplitz cost claim, conjugate-gradient admissibility, and the cited
convergence and preconditioner results. This file therefore must not invent a
generic wrapper proposition for the whole remark. -/

/- Remark 8.8. The displayed Newton inner system uses the matrix
`Kᵀ * K + α • L̄`. The `#check` below records that concrete formula surface
directly, without introducing a surrogate public owner for the full
iterative-solver claim. -/
#check
  fun {ι : Type u} {κ : Type v} [Fintype ι] [Fintype κ]
    (K : Matrix κ ι ℝ) (α : ℝ) (barL : Matrix ι ι ℝ) (deltaF r : ι → ℝ) ↦
      Matrix.mulVec (Kᵀ * K + α • barL) deltaF = r

/- Remark 8.8. The displayed replacement of `L̄` by its symmetric part keeps
the matrix predicate `Matrix.PosSemidef` explicit on
`((2 : ℝ)⁻¹) • (L̄ + L̄ᵀ)`. -/
#check
  fun {ι : Type u} (barL : Matrix ι ι ℝ) ↦
    Matrix.PosSemidef (((2 : ℝ)⁻¹) • (barL + barLᵀ))

/- Remark 8.8. Existing Chapter 8 bridge to the displayed formula `(8.61)` for
`L̄_v`. -/
#check TVPrimalDualNewton.HasIntermediateAssignments.lbar_eq

/- Verified backend anchors for the surviving source-facing formula surfaces.
The current repository snapshot still does not provide source-specific owners
for the cost, conjugate-gradient, convergence, or preconditioner parts of the
remark. -/
#check Matrix.bttb
#check Matrix.PosSemidef
#check Matrix.PosSemidef.add
#check Matrix.PosSemidef.smul
#check Matrix.isSymm_transpose_mul_self
#check Matrix.isSymm_add_transpose_self
