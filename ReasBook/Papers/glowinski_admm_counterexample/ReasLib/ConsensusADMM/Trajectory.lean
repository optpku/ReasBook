module

public import Mathlib.Analysis.InnerProductSpace.EuclideanDist
public import Mathlib.Data.EReal.Basic

@[expose] public section

open scoped RealInnerProductSpace

namespace ConsensusADMM

/-- A unit-penalty consensus ADMM trajectory with multiplier step size `γ`.
The block conditions assert global minimization with finite attained values,
followed by the relaxed multiplier update. -/
def IsTrajectory {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (γ : ℝ) (f g : E → EReal) (x y dual : ℕ → E) : Prop :=
  ∀ k,
    (∀ z,
      f (x (k + 1)) +
          ((inner ℝ (dual k) (x (k + 1) - y k) + ‖x (k + 1) - y k‖ ^ 2 / 2 : ℝ) : EReal) ≤
        f z + ((inner ℝ (dual k) (z - y k) + ‖z - y k‖ ^ 2 / 2 : ℝ) : EReal)) ∧
    (∀ z,
      g (y (k + 1)) +
          ((inner ℝ (dual k) (x (k + 1) - y (k + 1)) +
              ‖x (k + 1) - y (k + 1)‖ ^ 2 / 2 : ℝ) : EReal) ≤
        g z + ((inner ℝ (dual k) (x (k + 1) - z) + ‖x (k + 1) - z‖ ^ 2 / 2 : ℝ) : EReal)) ∧
    f (x (k + 1)) ≠ ⊤ ∧ g (y (k + 1)) ≠ ⊤ ∧
    dual (k + 1) = dual k + γ • (x (k + 1) - y (k + 1))

/-- The trajectory predicate is exactly the two block minimizations, finite
attained values, and the relaxed multiplier recurrence. -/
theorem trajectory_iff {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {γ : ℝ} {f g : E → EReal} {x y dual : ℕ → E} :
    IsTrajectory γ f g x y dual ↔
      ∀ k,
        (∀ z,
          f (x (k + 1)) +
              ((inner ℝ (dual k) (x (k + 1) - y k) + ‖x (k + 1) - y k‖ ^ 2 / 2 : ℝ) : EReal) ≤
            f z + ((inner ℝ (dual k) (z - y k) + ‖z - y k‖ ^ 2 / 2 : ℝ) : EReal)) ∧
        (∀ z,
          g (y (k + 1)) +
              ((inner ℝ (dual k) (x (k + 1) - y (k + 1)) +
                  ‖x (k + 1) - y (k + 1)‖ ^ 2 / 2 : ℝ) : EReal) ≤
            g z + ((inner ℝ (dual k) (x (k + 1) - z) + ‖x (k + 1) - z‖ ^ 2 / 2 : ℝ) : EReal)) ∧
        f (x (k + 1)) ≠ ⊤ ∧ g (y (k + 1)) ≠ ⊤ ∧
        dual (k + 1) = dual k + γ • (x (k + 1) - y (k + 1)) := by
  -- Unfolding the trajectory predicate exposes exactly the displayed conjunction.
  rfl

/-- Every block minimization along supplied iterates has the displayed update
as its unique minimizer. -/
def HasUniqueUpdates {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (f g : E → EReal) (x y dual : ℕ → E) : Prop :=
  ∀ k,
    (∀ z,
      f z + ((inner ℝ (dual k) (z - y k) + ‖z - y k‖ ^ 2 / 2 : ℝ) : EReal) ≤
          f (x (k + 1)) +
            ((inner ℝ (dual k) (x (k + 1) - y k) + ‖x (k + 1) - y k‖ ^ 2 / 2 : ℝ) : EReal) →
        z = x (k + 1)) ∧
    (∀ z,
      g z + ((inner ℝ (dual k) (x (k + 1) - z) + ‖x (k + 1) - z‖ ^ 2 / 2 : ℝ) : EReal) ≤
          g (y (k + 1)) +
            ((inner ℝ (dual k) (x (k + 1) - y (k + 1)) +
                ‖x (k + 1) - y (k + 1)‖ ^ 2 / 2 : ℝ) : EReal) →
        z = y (k + 1))

/-- Unique block updates amount to uniqueness for both displayed subproblems. -/
theorem uniqueUpdates_iff {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {f g : E → EReal} {x y dual : ℕ → E} :
    HasUniqueUpdates f g x y dual ↔
      ∀ k,
        (∀ z,
          f z + ((inner ℝ (dual k) (z - y k) + ‖z - y k‖ ^ 2 / 2 : ℝ) : EReal) ≤
              f (x (k + 1)) +
                ((inner ℝ (dual k) (x (k + 1) - y k) +
                    ‖x (k + 1) - y k‖ ^ 2 / 2 : ℝ) : EReal) →
            z = x (k + 1)) ∧
        (∀ z,
          g z + ((inner ℝ (dual k) (x (k + 1) - z) + ‖x (k + 1) - z‖ ^ 2 / 2 : ℝ) : EReal) ≤
              g (y (k + 1)) +
                ((inner ℝ (dual k) (x (k + 1) - y (k + 1)) +
                    ‖x (k + 1) - y (k + 1)‖ ^ 2 / 2 : ℝ) : EReal) →
            z = y (k + 1)) := by
  -- Unfolding unique updates exposes the two displayed uniqueness conditions.
  rfl

/-- The post-update state has period `N`, and no smaller positive period. -/
def HasExactPeriod {E : Type u} (N : ℕ) (x y dual : ℕ → E) : Prop :=
  Function.Periodic (fun k ↦ (x (k + 1), y (k + 1), dual (k + 1))) N ∧
    ∀ n, 0 < n →
      Function.Periodic (fun k ↦ (x (k + 1), y (k + 1), dual (k + 1))) n → N ≤ n

/-- Exact period consists of periodicity of the post-update state and minimality
among its positive periods. -/
theorem exactPeriod_iff {E : Type u} {N : ℕ} {x y dual : ℕ → E} :
    HasExactPeriod N x y dual ↔
      Function.Periodic (fun k ↦ (x (k + 1), y (k + 1), dual (k + 1))) N ∧
        ∀ n, 0 < n →
          Function.Periodic (fun k ↦ (x (k + 1), y (k + 1), dual (k + 1))) n → N ≤ n := by
  -- Unfolding exact period exposes periodicity together with its minimality clause.
  rfl

end ConsensusADMM
