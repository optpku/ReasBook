/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Upstream attribution: https://github.com/imathwy/DFP_wolfe_local/blob/e308927f5b7930bdd002f0c0e42b9d112ad821cb/README.md (formalization author).
Upstream source: https://github.com/imathwy/DFP_wolfe_local/blob/e308927f5b7930bdd002f0c0e42b9d112ad821cb/ReasLib/Analysis/Convex/EuclideanPlaneHessian.lean
-/

module

public import ReasLib.Analysis.Calculus.EuclideanPlaneHessian
public import ReasLib.Analysis.Convex.Hessian

public section

namespace EuclideanPlane

/-- A twice continuously differentiable function on the Euclidean plane with a global
positive lower bound on its Hessian quadratic form is strongly convex on the whole plane. -/
theorem strongConvexOnOfHessianLowerBound
    (f : EuclideanSpace ℝ (Fin 2) → ℝ) (m : ℝ) (hf : ContDiff ℝ 2 f) (hm : 0 < m)
    (h_lower : ∀ x v : EuclideanSpace ℝ (Fin 2), m * ‖v‖ ^ 2 ≤ inner ℝ (hessian f x v) v) :
    StrongConvexOn Set.univ m f := by
  -- Apply the Hilbert-space criterion, which contains the affine-line integration argument.
  refine ContDiff.strongConvexOnOfHessianLowerBound f m hf hm ?_
  intro x v
  -- The Euclidean-plane Hessian is the Fréchet derivative of the gradient used there.
  simpa only [hessian_def] using h_lower x v

end EuclideanPlane
