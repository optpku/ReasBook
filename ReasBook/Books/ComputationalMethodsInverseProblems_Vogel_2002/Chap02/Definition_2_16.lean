/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import ComputationalMethodsInverseProblems_Vogel_2002.Chap02.Definition_2_16.LeastSquares
public import ComputationalMethodsInverseProblems_Vogel_2002.Chap02.Definition_2_16.MinimumNorm
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.InnerProductSpace.Projection.Minimal
public import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Basic
public import Mathlib.Order.Filter.Extr

public section

noncomputable section

universe u v w

namespace ContinuousLinearMap

variable {𝕜 : Type u} {H₁ : Type v} {H₂ : Type w}



/- Definition 2.16 (1). Least-squares solutions of `K f = g` are represented by the canonical
predicate `ContinuousLinearMap.IsLeastSquaresSolution`. -/
#check ContinuousLinearMap.IsLeastSquaresSolution

/- Definition 2.16 (2). If `f_ls` is a least-squares solution, then all least-squares solutions
are exactly the points of `AffineSubspace.mk' f_ls K.ker`. -/
#check ContinuousLinearMap.isLeastSquaresSolution_iff_mem_affineSubspace

/- Definition 2.16 (3). The least-squares minimum-norm notion is represented by the existing
predicate `ContinuousLinearMap.IsLeastSquaresMinimumNormSolution`. -/
#check ContinuousLinearMap.IsLeastSquaresMinimumNormSolution

variable [RCLike 𝕜]
variable [NormedAddCommGroup H₁] [InnerProductSpace 𝕜 H₁] [CompleteSpace H₁]
variable [NormedAddCommGroup H₂] [InnerProductSpace 𝕜 H₂] [CompleteSpace H₂]

/-- Definition 2.16 (4). For a chosen least-squares solution `f_ls`, a vector `f` is a
least-squares minimum-norm solution of `K f = g` exactly when it is a least-squares solution and
its norm is minimal on `AffineSubspace.mk' f_ls K.ker`, expressed by `IsMinOn`. -/
theorem isLeastSquaresMinimumNormSolution_iff_isMinOn_norm_affineSubspace
    (K : H₁ →L[𝕜] H₂) (g : H₂) {f_ls f : H₁}
    (hls : K.IsLeastSquaresSolution g f_ls) :
    K.IsLeastSquaresMinimumNormSolution g f ↔
      K.IsLeastSquaresSolution g f ∧
        IsMinOn (fun h : H₁ ↦ ‖h‖) (AffineSubspace.mk' f_ls K.ker) f := by
  let _ : CompleteSpace H₁ := inferInstance
  let _ : CompleteSpace H₂ := inferInstance
  -- Rewrite the bundled minimum-norm predicate into its least-squares and pointwise norm parts.
  rw [K.isLeastSquaresMinimumNormSolution_iff]
  have hmemiff (h : H₁) :
      K.IsLeastSquaresSolution g h ↔ h ∈ AffineSubspace.mk' f_ls K.ker :=
    K.isLeastSquaresSolution_iff_mem_affineSubspace (g := g) (f_ls := f_ls) (f := h) hls
  constructor
  · rintro ⟨hf, hnorm⟩
    refine ⟨hf, ?_⟩
    -- Restrict the global norm comparison to the affine subspace of least-squares solutions.
    rw [isMinOn_iff]
    intro h hh
    exact hnorm h ((hmemiff h).mpr hh)
  · rintro ⟨hf, hmin⟩
    refine ⟨hf, ?_⟩
    -- Move each least-squares competitor into the affine subspace and apply minimality there.
    rw [isMinOn_iff] at hmin
    intro h hh
    exact hmin h ((hmemiff h).mp hh)

/-- Companion form of Definition 2.16 (4) unpacking
`ContinuousLinearMap.isLeastSquaresMinimumNormSolution_iff_isMinOn_norm_affineSubspace`
through `isMinOn_iff`. -/
theorem isLeastSquaresMinimumNormSolution_iff_norm_le_on_affineSubspace
    (K : H₁ →L[𝕜] H₂) (g : H₂) {f_ls f : H₁}
    (hls : K.IsLeastSquaresSolution g f_ls) :
    K.IsLeastSquaresMinimumNormSolution g f ↔
      K.IsLeastSquaresSolution g f ∧
        ∀ h ∈ AffineSubspace.mk' f_ls K.ker, ‖f‖ ≤ ‖h‖ := by
  simpa [isMinOn_iff] using
    K.isLeastSquaresMinimumNormSolution_iff_isMinOn_norm_affineSubspace g hls

end ContinuousLinearMap
