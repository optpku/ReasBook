/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import Mathlib.Analysis.Calculus.Gradient.Basic
import OptimizationTheoryAndMethods_SunYuan_2006.Chap02.Definition_2_2_extra_1
import OptimizationTheoryAndMethods_SunYuan_2006.Chap03.Definition_3_1_extra_1

universe u

section

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

-- Domain sampling: the source-facing exact line-search owner already appears in Chapter 2 as
-- `IsExactLineSearchStepOnNonnegativeRay`, built on mathlib's canonical minimizer owner
-- `IsMinOn`. The Chapter 3 owner declarations for the steepest-descent direction and update are
-- `steepestDescentDirection` and `steepestDescentStep`. This file keeps the algorithm data
-- source-facing and exposes those Chapter 3 owners as the derived API.

/-- Chapter03 Algorithm 3.1.1: the steepest descent method on a real Hilbert space starts from
`x₀`, uses explicit gradient data `g k` and search directions `d k`, stops when
`‖g k‖ ≤ ε`, and otherwise updates by exact line search in the negative-gradient
direction. -/
structure IsSteepestDescentMethod (f : E → ℝ)
    (ε : ℝ) (x₀ : E) (x g d : ℕ → E) (α : ℕ → ℝ) : Prop where
  epsilon_pos : 0 < ε
  x_zero : x 0 = x₀
  hasGradientAt : ∀ k : ℕ, HasGradientAt f (g k) (x k)
  direction_eq : ∀ k, ε < ‖g k‖ → d k = -g k
  exactLineSearch :
    ∀ k, ε < ‖g k‖ → IsExactLineSearchStepOnNonnegativeRay f (x k) (d k) (α k)
  next_eq :
    ∀ k, ε < ‖g k‖ → x (k + 1) = x k + α k • d k

variable {f : E → ℝ} {ε : ℝ} {x₀ : E} {x g d : ℕ → E} {α : ℕ → ℝ}

/-- A nonterminal steepest-descent step uses the negative-gradient direction,
exact line search, and the standard iterate update. -/
theorem IsSteepestDescentMethod.gradient_eq
    (hMethod : IsSteepestDescentMethod f ε x₀ x g d α) (k : ℕ) :
    gradient f (x k) = g k :=
  (hMethod.hasGradientAt k).gradient

/-- At every nonterminal stage, the recorded search direction is the canonical
steepest-descent direction. -/
theorem IsSteepestDescentMethod.direction_eq_steepestDescentDirection
    (hMethod : IsSteepestDescentMethod f ε x₀ x g d α) {k : ℕ}
    (hNotStopped : ε < ‖g k‖) :
    d k = steepestDescentDirection f (x k) := by
  calc
    d k = -g k := hMethod.direction_eq k hNotStopped
    _ = steepestDescentDirection f (x k) := by
      simp [steepestDescentDirection, hMethod.gradient_eq k]

/-- At every nonterminal stage, the exact line search is performed along the canonical
steepest-descent direction. -/
theorem IsSteepestDescentMethod.exactLineSearch_steepestDescentDirection
    (hMethod : IsSteepestDescentMethod f ε x₀ x g d α) {k : ℕ}
    (hNotStopped : ε < ‖g k‖) :
    IsExactLineSearchStepOnNonnegativeRay f (x k) (steepestDescentDirection f (x k)) (α k) := by
  simpa [hMethod.direction_eq_steepestDescentDirection hNotStopped] using
    hMethod.exactLineSearch k hNotStopped

/-- At every nonterminal stage, the next iterate is the canonical steepest-descent step. -/
theorem IsSteepestDescentMethod.next_eq_steepestDescentStep
    (hMethod : IsSteepestDescentMethod f ε x₀ x g d α) {k : ℕ}
    (hNotStopped : ε < ‖g k‖) :
    x (k + 1) = steepestDescentStep f (x k) (α k) := by
  rw [hMethod.next_eq k hNotStopped, steepestDescentStep,
    hMethod.direction_eq_steepestDescentDirection hNotStopped]

/-- A nonterminal steepest-descent step uses the canonical steepest-descent direction,
exact line search, and the canonical iterate update. -/
theorem IsSteepestDescentMethod.step
    (hMethod : IsSteepestDescentMethod f ε x₀ x g d α) {k : ℕ}
    (hNotStopped : ε < ‖g k‖) :
    d k = steepestDescentDirection f (x k) ∧
      IsExactLineSearchStepOnNonnegativeRay f (x k) (steepestDescentDirection f (x k)) (α k) ∧
      x (k + 1) = steepestDescentStep f (x k) (α k) :=
  ⟨hMethod.direction_eq_steepestDescentDirection hNotStopped,
    hMethod.exactLineSearch_steepestDescentDirection hNotStopped,
    hMethod.next_eq_steepestDescentStep hNotStopped⟩

/-- The predicate `IsSteepestDescentMethod` is proof-irrelevant. -/
instance isSteepestDescentMethod_subsingleton :
    Subsingleton (IsSteepestDescentMethod f ε x₀ x g d α) := inferInstance

end
