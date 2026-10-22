/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import ComputationalMethodsInverseProblems_Vogel_2002.Chap02.Definition_2_40.Hessian
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.LinearAlgebra.Matrix.BilinearForm

public section

noncomputable section

/-- Example 2.41. On `ℝ^n`, the `(i, j)` entry of the Hessian matrix of `J` at `f`
is the mixed second Fréchet derivative `(2.43)`.

This is the source-facing coordinate specialization of the canonical Chapter 2
owner `hessian J f` from Definition 2.40. -/
theorem hessianEntry_eq_secondFDeriv {n : ℕ} (J : EuclideanSpace ℝ (Fin n) → ℝ)
    (f : EuclideanSpace ℝ (Fin n)) (i j : Fin n) :
    LinearMap.BilinForm.toMatrix ((EuclideanSpace.basisFun (Fin n) ℝ).toBasis)
        (fderiv ℝ (fderiv ℝ J) f).toBilinForm i j =
      fderiv ℝ (fderiv ℝ J) f (EuclideanSpace.single i (1 : ℝ))
        (EuclideanSpace.single j (1 : ℝ)) := by
  rw [LinearMap.BilinForm.toMatrix_apply, ContinuousLinearMap.toBilinForm_apply]
  simp

/-- Companion bridge for Example 2.41: the same Hessian matrix entry can be read through the
canonical Hessian operator `hessian J f`. -/
theorem hessianEntry_eq_hessian_inner {n : ℕ} (J : EuclideanSpace ℝ (Fin n) → ℝ)
    (f : EuclideanSpace ℝ (Fin n)) (i j : Fin n) :
    LinearMap.BilinForm.toMatrix ((EuclideanSpace.basisFun (Fin n) ℝ).toBasis)
        (fderiv ℝ (fderiv ℝ J) f).toBilinForm i j =
      inner ℝ (hessian J f (EuclideanSpace.single i (1 : ℝ)))
        (EuclideanSpace.single j (1 : ℝ)) := by
  rw [hessianEntry_eq_secondFDeriv, ← hessian_inner J f (EuclideanSpace.single i (1 : ℝ))
    (EuclideanSpace.single j (1 : ℝ))]
