/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import ComputationalMethodsInverseProblems_Vogel_2002.Chap02.Exercise_2_10
public import Mathlib.Analysis.InnerProductSpace.PiL2

public section

universe u v x

namespace ContinuousLinearMap

/- Example 2.11 (1). Any bounded linear operator `K : H₁ →L[𝕜] H₂` whose range `K.range` is
finite-dimensional is compact. -/
#check isCompactOperator_of_finiteDimensional_range

end ContinuousLinearMap

namespace Matrix

/- Example 2.11 (2). Matrix operators, viewed as bounded linear maps via
`A.toEuclideanLin.toContinuousLinearMap`, equivalently via `A.toEuclideanLin`, are compact. -/
set_option linter.unusedFintypeInType false in
theorem isCompactOperator_toEuclideanLin
    {𝕜 : Type u} {m : Type v} {n : Type x} [RCLike 𝕜]
    [Fintype m] [Fintype n] [DecidableEq n] (A : Matrix m n 𝕜) :
    IsCompactOperator A.toEuclideanLin.toContinuousLinearMap := by
  let K := A.toEuclideanLin.toContinuousLinearMap
  have h_range_fin : FiniteDimensional 𝕜 K.range := inferInstance
  simpa [K] using ContinuousLinearMap.isCompactOperator_of_finiteDimensional_range K h_range_fin

end Matrix
