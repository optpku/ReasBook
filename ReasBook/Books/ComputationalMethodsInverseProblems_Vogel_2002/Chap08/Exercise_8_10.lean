/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import ComputationalMethodsInverseProblems_Vogel_2002.Chap08.Algorithm_8_2_4.Clauses
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Mathlib.LinearAlgebra.Matrix.Symmetric

public section

universe u

open scoped Matrix

namespace TVPrimalDualNewton

/- This item is intentionally kept as a source-facing blocker. The current
repository snapshot exposes the concrete Chapter 8 formula `(8.61)` for `L̄`
through `TVPrimalDualNewton.HasIntermediateAssignments.lbar_eq`, but it does
not yet expose the additional source-specific positivity hypotheses needed to
derive positive semidefiniteness of the symmetric part. This file therefore
records only the target proposition surface and the existing Chapter 8 bridge,
rather than asserting an overstated theorem from
`HasIntermediateAssignments` alone. -/

/- Exercise 8.10. The displayed matrix predicate is that the symmetric part
`((2 : ℝ)⁻¹) • (L̄ + L̄ᵀ)` is positive semidefinite. -/
#check
  fun {ι : Type u} (barL : Matrix ι ι ℝ) ↦
    Matrix.PosSemidef (((2 : ℝ)⁻¹) • (barL + barLᵀ))

/- Exercise 8.10. Existing Chapter 8 bridge to the concrete `(8.61)` formula
for `L̄`. -/
#check HasIntermediateAssignments.lbar_eq

/- Verified backend anchors for the surviving blocker surface. -/
#check Matrix.PosSemidef
#check Matrix.isSymm_add_transpose_self

end TVPrimalDualNewton
