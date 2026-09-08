module

public import ReasLib.Analysis.Calculus.Gradient.OrthogonalSum.Hessian
public import ReasLib.Optimization.DFP.OrthogonalSum

public section

/-!
# Hessian bounds for DFP orthogonal-sum objectives

This file exposes the generic Hessian transport theorem through the
`DFP.OrthogonalSum` objective interface.
-/

noncomputable section

universe u v

namespace DFP.OrthogonalSum

/-- Adjoining the quadratic `‖w‖² / 2` preserves Hessian bounds whenever the
new identity block lies between the same lower and upper bounds. -/
theorem hasHessianBounds_objective {ι : Type u} {κ : Type v}
    [Fintype ι] [Fintype κ] {m M : ℝ} {f : EuclideanSpace ℝ ι → ℝ}
    (hf : ContDiff ℝ 2 f) (h : HasHessianBounds m M f) (hm : m ≤ 1) (hM : 1 ≤ M) :
    HasHessianBounds m M (objective (κ := κ) f) := by
  rw [objective_eq]
  exact EuclideanSpace.OrthogonalSum.Gradient.hasHessianBounds_objective hf h hm hM

end DFP.OrthogonalSum
