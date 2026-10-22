/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import ComputationalMethodsInverseProblems_Vogel_2002.Chap02.Definition_2_16.LeastSquares

public section

noncomputable section

universe u v w

namespace ContinuousLinearMap

variable {𝕜 : Type u} {H₁ : Type v} {H₂ : Type w}
variable [NormedField 𝕜]
variable [NormedAddCommGroup H₁] [NormedSpace 𝕜 H₁]
variable [NormedAddCommGroup H₂] [NormedSpace 𝕜 H₂]

/-- A vector `f` is a least-squares minimum-norm solution for `K f = g` when it is a
least-squares solution and has minimal norm among all least-squares solutions. -/
structure IsLeastSquaresMinimumNormSolution
    (K : H₁ →L[𝕜] H₂) (g : H₂) (f : H₁) : Prop where
  /-- A least-squares minimum-norm solution is, in particular, a least-squares solution. -/
  leastSquares : K.IsLeastSquaresSolution g f
  /-- Among least-squares solutions, a least-squares minimum-norm solution has minimal norm. -/
  norm_le : ∀ h : H₁, K.IsLeastSquaresSolution g h → ‖f‖ ≤ ‖h‖

namespace IsLeastSquaresMinimumNormSolution

set_option linter.defProp false in
/-- Constructs a least-squares minimum-norm solution from least-squares solvability and the
minimal-norm inequality over all least-squares solutions. -/
def ofLeastSquaresAndNormLE
    {K : H₁ →L[𝕜] H₂} {g : H₂} {f : H₁}
    (hLeastSquares : K.IsLeastSquaresSolution g f)
    (hNormLE : ∀ h : H₁, K.IsLeastSquaresSolution g h → ‖f‖ ≤ ‖h‖) :
    K.IsLeastSquaresMinimumNormSolution g f :=
  ⟨hLeastSquares, hNormLE⟩

end IsLeastSquaresMinimumNormSolution

/-- The defining characterization of
`ContinuousLinearMap.IsLeastSquaresMinimumNormSolution`. -/
theorem isLeastSquaresMinimumNormSolution_iff
    (K : H₁ →L[𝕜] H₂) (g : H₂) (f : H₁) :
    K.IsLeastSquaresMinimumNormSolution g f ↔
      K.IsLeastSquaresSolution g f ∧
        ∀ h : H₁, K.IsLeastSquaresSolution g h → ‖f‖ ≤ ‖h‖ := by
  constructor
  · intro hf
    exact ⟨hf.leastSquares, hf.norm_le⟩
  · rintro ⟨hf, hnorm⟩
    exact ⟨hf, hnorm⟩

end ContinuousLinearMap
