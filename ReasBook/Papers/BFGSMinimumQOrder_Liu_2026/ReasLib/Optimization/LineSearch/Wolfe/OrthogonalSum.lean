/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Upstream attribution: https://github.com/imathwy/DFP_wolfe_local/blob/e308927f5b7930bdd002f0c0e42b9d112ad821cb/README.md (formalization author).
Upstream source: https://github.com/imathwy/DFP_wolfe_local/blob/e308927f5b7930bdd002f0c0e42b9d112ad821cb/ReasLib/Optimization/LineSearch/Wolfe/OrthogonalSum.lean
-/

module

public import ReasLib.Analysis.Calculus.Gradient.OrthogonalSum
public import ReasLib.Optimization.LineSearch.Wolfe.Map

public section

/-!
# Wolfe conditions on orthogonal-sum objectives
-/

noncomputable section

universe u v

namespace LineSearch.Wolfe

/-- Weak Wolfe satisfaction is invariant under embedding into an orthogonal-sum objective. -/
theorem IsWeak.orthogonalSum_iff {ι : Type u} {κ : Type v}
    [Fintype ι] [Fintype κ] {p : Coefficients}
    {f : EuclideanSpace ℝ ι → ℝ} {x s : EuclideanSpace ℝ ι} :
    IsWeak p (EuclideanSpace.OrthogonalSum.Gradient.objective (κ := κ) f)
        (EuclideanSpace.OrthogonalSum.inl (κ := κ) x)
        (EuclideanSpace.OrthogonalSum.inl (κ := κ) s) ↔
      IsWeak p f x s := by
  apply IsWeak.map_iff
  exact fun z ↦ EuclideanSpace.OrthogonalSum.Gradient.objective_inl f z

/-- Strong Wolfe satisfaction is invariant under embedding into an orthogonal-sum objective. -/
theorem IsStrong.orthogonalSum_iff {ι : Type u} {κ : Type v}
    [Fintype ι] [Fintype κ] {p : Coefficients}
    {f : EuclideanSpace ℝ ι → ℝ} {x s : EuclideanSpace ℝ ι} :
    IsStrong p (EuclideanSpace.OrthogonalSum.Gradient.objective (κ := κ) f)
        (EuclideanSpace.OrthogonalSum.inl (κ := κ) x)
        (EuclideanSpace.OrthogonalSum.inl (κ := κ) s) ↔
      IsStrong p f x s := by
  apply IsStrong.map_iff
  exact fun z ↦ EuclideanSpace.OrthogonalSum.Gradient.objective_inl f z

end LineSearch.Wolfe
