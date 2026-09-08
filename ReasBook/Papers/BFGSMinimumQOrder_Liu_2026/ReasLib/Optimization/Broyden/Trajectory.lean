module

public import ReasLib.Optimization.LineSearch
public import ReasLib.Optimization.QuasiNewton

public section

universe u

namespace Broyden

variable {ι : Type u} [Fintype ι] [DecidableEq ι]

/-- A variable-parameter convex Broyden trajectory with exact line search. -/
structure IsTrajectory (F : EuclideanSpace ℝ ι → ℝ) (φ : ℕ → ℝ)
    (B₀ : Matrix ι ι ℝ) (x : ℕ → EuclideanSpace ℝ ι)
    (B : ℕ → Matrix ι ι ℝ) (α : ℕ → ℝ) : Prop where
  /-- The Hessian sequence starts at the prescribed approximation. -/
  initial : B 0 = B₀
  /-- The objective is differentiable. -/
  differentiable : Differentiable ℝ F
  /-- Every interpolation parameter belongs to the convex Broyden interval. -/
  parameter_mem : ∀ k, φ k ∈ Set.Icc (0 : ℝ) 1
  /-- Every Hessian approximation is positive definite. -/
  posDef : ∀ k, (B k).PosDef
  /-- Every step size is selected by exact line search. -/
  exact : ∀ k, LineSearch.IsExact F (x k)
    (BFGS.searchDirection (B k) (gradient F (x k))) (α k)
  /-- The point sequence follows the quasi-Newton search direction. -/
  point : ∀ k, x (k + 1) =
    x k + α k • BFGS.searchDirection (B k) (gradient F (x k))
  /-- The Hessian sequence follows the variable-parameter convex Broyden update. -/
  update : ∀ k, B (k + 1) = Broyden.update (φ k) (B k) (x (k + 1) - x k)
    (gradient F (x (k + 1)) - gradient F (x k))

namespace IsTrajectory

/-- Construct a convex Broyden trajectory from its initialization and step laws. -/
def ofConditions {F : EuclideanSpace ℝ ι → ℝ} {φ : ℕ → ℝ}
    {B₀ : Matrix ι ι ℝ} {x : ℕ → EuclideanSpace ℝ ι}
    {B : ℕ → Matrix ι ι ℝ} {α : ℕ → ℝ}
    (initial : B 0 = B₀) (differentiable : Differentiable ℝ F)
    (parameter_mem : ∀ k, φ k ∈ Set.Icc (0 : ℝ) 1)
    (posDef : ∀ k, (B k).PosDef)
    (exact : ∀ k, LineSearch.IsExact F (x k)
      (BFGS.searchDirection (B k) (gradient F (x k))) (α k))
    (point : ∀ k, x (k + 1) =
      x k + α k • BFGS.searchDirection (B k) (gradient F (x k)))
    (update : ∀ k, B (k + 1) = Broyden.update (φ k) (B k) (x (k + 1) - x k)
      (gradient F (x (k + 1)) - gradient F (x k))) :
    IsTrajectory F φ B₀ x B α :=
  -- Populate each trajectory field directly from the supplied hypotheses.
  ⟨initial, differentiable, parameter_mem, posDef, exact, point, update⟩

/-- The parameter, positivity, exact-search, point, and update laws at one Broyden step. -/
theorem step_spec {F : EuclideanSpace ℝ ι → ℝ} {φ : ℕ → ℝ}
    {B₀ : Matrix ι ι ℝ} {x : ℕ → EuclideanSpace ℝ ι}
    {B : ℕ → Matrix ι ι ℝ} {α : ℕ → ℝ}
    (h : IsTrajectory F φ B₀ x B α) (k : ℕ) :
    φ k ∈ Set.Icc (0 : ℝ) 1 ∧
      (B k).PosDef ∧
        LineSearch.IsExact F (x k)
          (BFGS.searchDirection (B k) (gradient F (x k))) (α k) ∧
      x (k + 1) = x k + α k • BFGS.searchDirection (B k) (gradient F (x k)) ∧
      B (k + 1) = Broyden.update (φ k) (B k) (x (k + 1) - x k)
        (gradient F (x (k + 1)) - gradient F (x k)) := by
  -- Read the five indexed laws from the corresponding structure projections.
  exact ⟨h.parameter_mem k, h.posDef k, h.exact k, h.point k, h.update k⟩

end IsTrajectory

end Broyden
