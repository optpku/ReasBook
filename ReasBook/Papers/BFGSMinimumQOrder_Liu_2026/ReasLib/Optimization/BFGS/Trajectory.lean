module

public import ReasLib.Optimization.LineSearch
public import ReasLib.Optimization.QuasiNewton
public import Mathlib.Analysis.Calculus.Gradient.Basic

public section

universe u

namespace BFGS

variable {ι : Type u} [Fintype ι] [DecidableEq ι]

/-- An exact-line-search BFGS trajectory records the initial Hessian, differentiability,
positive definiteness, exact step sizes, iterate recurrence, and Hessian update recurrence. -/
def IsTrajectory (F : EuclideanSpace ℝ ι → ℝ) (B₀ : Matrix ι ι ℝ)
    (x : ℕ → EuclideanSpace ℝ ι) (B : ℕ → Matrix ι ι ℝ) (α : ℕ → ℝ) : Prop :=
  B 0 = B₀ ∧
    Differentiable ℝ F ∧
      (∀ k, (B k).PosDef) ∧
        (∀ k, LineSearch.IsExact F (x k)
          (searchDirection (B k) (gradient F (x k))) (α k)) ∧
          (∀ k, x (k + 1) =
            x k + α k • searchDirection (B k) (gradient F (x k))) ∧
            ∀ k, B (k + 1) = update (B k) (x (k + 1) - x k)
              (gradient F (x (k + 1)) - gradient F (x k))

/-- The defining laws of an exact-line-search BFGS trajectory. -/
theorem isTrajectory_iff (F : EuclideanSpace ℝ ι → ℝ) (B₀ : Matrix ι ι ℝ)
    (x : ℕ → EuclideanSpace ℝ ι) (B : ℕ → Matrix ι ι ℝ) (α : ℕ → ℝ) :
    IsTrajectory F B₀ x B α ↔
      B 0 = B₀ ∧
        Differentiable ℝ F ∧
          (∀ k, (B k).PosDef) ∧
            (∀ k, LineSearch.IsExact F (x k)
              (searchDirection (B k) (gradient F (x k))) (α k)) ∧
              (∀ k, x (k + 1) =
                x k + α k • searchDirection (B k) (gradient F (x k))) ∧
                ∀ k, B (k + 1) = update (B k) (x (k + 1) - x k)
                  (gradient F (x (k + 1)) - gradient F (x k)) := by
  -- Unfolding the trajectory predicate exposes exactly the displayed conjunction.
  rfl

namespace IsTrajectory

/-- Every Hessian approximation along a BFGS trajectory is positive definite. -/
theorem posDef {F : EuclideanSpace ℝ ι → ℝ} {B₀ : Matrix ι ι ℝ}
    {x : ℕ → EuclideanSpace ℝ ι} {B : ℕ → Matrix ι ι ℝ} {α : ℕ → ℝ}
    (h : IsTrajectory F B₀ x B α) (k : ℕ) : (B k).PosDef := by
  -- Normalize the trajectory hypothesis and select its positive-definiteness law.
  rw [isTrajectory_iff] at h
  exact h.2.2.1 k

/-- Every selected parameter along a BFGS trajectory is an exact line-search step. -/
theorem exact {F : EuclideanSpace ℝ ι → ℝ} {B₀ : Matrix ι ι ℝ}
    {x : ℕ → EuclideanSpace ℝ ι} {B : ℕ → Matrix ι ι ℝ} {α : ℕ → ℝ}
    (h : IsTrajectory F B₀ x B α) (k : ℕ) :
    LineSearch.IsExact F (x k) (searchDirection (B k) (gradient F (x k))) (α k) := by
  -- Normalize the trajectory hypothesis and select its exact-line-search law.
  rw [isTrajectory_iff] at h
  exact h.2.2.2.1 k

end IsTrajectory

end BFGS
