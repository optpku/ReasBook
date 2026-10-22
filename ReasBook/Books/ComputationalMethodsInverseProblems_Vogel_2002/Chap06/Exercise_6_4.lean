/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.LinearAlgebra.Matrix.BilinearForm

public section

noncomputable section

namespace OutputLeastSquares
namespace GaussNewton

universe u

variable {n : ℕ}
variable {U : Type u} [NormedAddCommGroup U] [InnerProductSpace ℝ U]

/-- The Exercise 6.4 directional action `v ↦ ((dA / dq) v) u` obtained by
evaluating the operator-valued parameter derivative at the solved state
`solve q`. -/
def directionalAction (solve : EuclideanSpace ℝ (Fin n) → U)
    (dA : EuclideanSpace ℝ (Fin n) →
      EuclideanSpace ℝ (Fin n) →L[ℝ] U →L[ℝ] U)
    (q : EuclideanSpace ℝ (Fin n)) :
    EuclideanSpace ℝ (Fin n) →L[ℝ] U :=
  (ContinuousLinearMap.apply ℝ U (solve q)).comp (dA q)

/-- The pointwise defining equation for the Exercise 6.4 directional action. -/
@[simp] theorem directionalAction_apply (solve : EuclideanSpace ℝ (Fin n) → U)
    (dA : EuclideanSpace ℝ (Fin n) →
      EuclideanSpace ℝ (Fin n) →L[ℝ] U →L[ℝ] U)
    (q v : EuclideanSpace ℝ (Fin n)) :
    directionalAction solve dA q v = ((dA q) v) (solve q) := by
  simp [directionalAction]

/-- The Gauss-Newton Hessian-approximation bilinear form from Exercise 6.4,
with entries computed from the directional derivative action and the operator
realizing `A(q)⁻²` on the state space. -/
def hessian (solve : EuclideanSpace ℝ (Fin n) → U)
    (dA : EuclideanSpace ℝ (Fin n) →
      EuclideanSpace ℝ (Fin n) →L[ℝ] U →L[ℝ] U)
    (AinvSq : EuclideanSpace ℝ (Fin n) → U →L[ℝ] U)
  (q : EuclideanSpace ℝ (Fin n)) :
    LinearMap.BilinForm ℝ (EuclideanSpace ℝ (Fin n)) :=
  (ContinuousLinearMap.bilinearComp
      (isBoundedBilinearMap_inner.toContinuousLinearMap.flip)
      ((AinvSq q).comp (directionalAction solve dA q))
      (directionalAction solve dA q)).toBilinForm

/-- The Gauss-Newton bilinear form evaluates to
`⟪((dA(q) / dq) w) (solve q), A(q)⁻² (((dA(q) / dq) v) (solve q))⟫` on
parameter directions `v` and `w`. -/
theorem hessian_apply (solve : EuclideanSpace ℝ (Fin n) → U)
    (dA : EuclideanSpace ℝ (Fin n) →
      EuclideanSpace ℝ (Fin n) →L[ℝ] U →L[ℝ] U)
    (AinvSq : EuclideanSpace ℝ (Fin n) → U →L[ℝ] U)
    (q v w : EuclideanSpace ℝ (Fin n)) :
    hessian solve dA AinvSq q v w =
      inner ℝ (((dA q) w) (solve q))
        ((AinvSq q) ((((dA q) v) (solve q)))) := by
  simp [hessian]

/-- Exercise 6.4. The `(i, j)` component of the Gauss-Newton Hessian
approximation is
`⟪((dA(q) / dq) e_j) (solve q), A(q)⁻² (((dA(q) / dq) e_i) (solve q))⟫` in
the state-space inner product. -/
theorem hessianEntry_eq_inner (solve : EuclideanSpace ℝ (Fin n) → U)
    (dA : EuclideanSpace ℝ (Fin n) →
      EuclideanSpace ℝ (Fin n) →L[ℝ] U →L[ℝ] U)
    (AinvSq : EuclideanSpace ℝ (Fin n) → U →L[ℝ] U)
    (q : EuclideanSpace ℝ (Fin n)) (i j : Fin n) :
    LinearMap.BilinForm.toMatrix ((EuclideanSpace.basisFun (Fin n) ℝ).toBasis)
        (hessian solve dA AinvSq q) i j =
      inner ℝ (((dA q) (EuclideanSpace.single j (1 : ℝ))) (solve q))
        ((AinvSq q)
          ((((dA q) (EuclideanSpace.single i (1 : ℝ))) (solve q)))) := by
  rw [LinearMap.BilinForm.toMatrix_apply, hessian_apply]
  simp

end GaussNewton
end OutputLeastSquares
