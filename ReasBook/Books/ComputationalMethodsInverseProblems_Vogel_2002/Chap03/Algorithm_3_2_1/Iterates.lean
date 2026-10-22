/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import Mathlib.Analysis.InnerProductSpace.PiL2

public section

noncomputable section

namespace ConjugateGradient

universe u

variable {n : Type u} [Fintype n] [DecidableEq n]

/-- Helper for Algorithm 3.2.1: a conjugate-gradient stage stores the current
approximate solution, gradient, and search direction. -/
structure State (n : Type u) [Fintype n] [DecidableEq n] where
  solution : EuclideanSpace ℝ n
  gradient : EuclideanSpace ℝ n
  direction : EuclideanSpace ℝ n

/-- Helper for Algorithm 3.2.1: `δᵥ` is the squared Euclidean norm of the
current gradient. -/
@[expose] def delta (state : State n) : ℝ :=
  ‖state.gradient‖ ^ 2

/-- Helper for Algorithm 3.2.1: `hᵥ` is the matrix action of `A` on the current
search direction. -/
@[expose] def appliedDirection (A : Matrix n n ℝ) (state : State n) : EuclideanSpace ℝ n :=
  A.toEuclideanLin state.direction

/-- The matrix action companion for `appliedDirection`. -/
@[simp] theorem appliedDirection_eq
    (A : Matrix n n ℝ) (state : State n) :
    appliedDirection A state = A.toEuclideanLin state.direction := rfl

/-- Helper for Algorithm 3.2.1: `τᵥ = δᵥ / ⟪pᵥ, hᵥ⟫`. -/
@[expose] def stepSize (A : Matrix n n ℝ) (state : State n) : ℝ :=
  delta state / inner ℝ state.direction (appliedDirection A state)

/-- The quotient formula companion for `stepSize`. -/
@[simp] theorem stepSize_eq
    (A : Matrix n n ℝ) (state : State n) :
    stepSize A state = delta state / inner ℝ state.direction (appliedDirection A state) := rfl

/-- Helper for Algorithm 3.2.1: the solution update `fᵥ₊₁ = fᵥ + τᵥ pᵥ`. -/
@[expose] def nextSolution (A : Matrix n n ℝ) (state : State n) : EuclideanSpace ℝ n :=
  state.solution + stepSize A state • state.direction

/-- The solution-update companion for `nextSolution`. -/
@[simp] theorem nextSolution_eq
    (A : Matrix n n ℝ) (state : State n) :
    nextSolution A state = state.solution + stepSize A state • state.direction := rfl

/-- Helper for Algorithm 3.2.1: the gradient update `gᵥ₊₁ = gᵥ + τᵥ hᵥ`. -/
@[expose] def nextGradient (A : Matrix n n ℝ) (state : State n) : EuclideanSpace ℝ n :=
  state.gradient + stepSize A state • appliedDirection A state

/-- The gradient-update companion for `nextGradient`. -/
@[simp] theorem nextGradient_eq
    (A : Matrix n n ℝ) (state : State n) :
    nextGradient A state = state.gradient + stepSize A state • appliedDirection A state := rfl

/-- Helper for Algorithm 3.2.1: `βᵥ = δᵥ₊₁ / δᵥ`. -/
@[expose] def beta (A : Matrix n n ℝ) (state : State n) : ℝ :=
  ‖nextGradient A state‖ ^ 2 / delta state

/-- The Fletcher-Reeves coefficient companion for `beta`. -/
@[simp] theorem beta_eq
    (A : Matrix n n ℝ) (state : State n) :
    beta A state = ‖nextGradient A state‖ ^ 2 / delta state := rfl

/-- Helper for Algorithm 3.2.1: the search-direction update
`pᵥ₊₁ = -gᵥ₊₁ + βᵥ pᵥ`. -/
@[expose] def nextDirection (A : Matrix n n ℝ) (state : State n) : EuclideanSpace ℝ n :=
  -nextGradient A state + beta A state • state.direction

/-- The direction-update companion for `nextDirection`. -/
@[simp] theorem nextDirection_eq
    (A : Matrix n n ℝ) (state : State n) :
    nextDirection A state = -nextGradient A state + beta A state • state.direction := rfl

/-- Helper for Algorithm 3.2.1: the initial state has solution `f₀`, gradient
`A.toEuclideanLin f₀ + b`, and direction `-(A.toEuclideanLin f₀ + b)`. -/
@[expose] def init (A : Matrix n n ℝ) (b f0 : EuclideanSpace ℝ n) : State n :=
  let gradient := A.toEuclideanLin f0 + b
  { solution := f0
    gradient := gradient
    direction := -gradient }

/-- The squared-gradient-norm companion for `delta`. -/
@[simp] theorem delta_eq (state : State n) :
    delta state = ‖state.gradient‖ ^ 2 := rfl

/-- Helper for Algorithm 3.2.1: one conjugate-gradient update step. -/
@[expose] def step (A : Matrix n n ℝ) (state : State n) : State n :=
  { solution := nextSolution A state
    gradient := nextGradient A state
    direction := nextDirection A state }

/-- Algorithm 3.2.1. For symmetric positive-definite `A`, the conjugate-gradient
method for quadratic minimization is represented by the state sequence
`ConjugateGradient.iterates A b f₀`, starting from `f₀` with initial gradient
`A.toEuclideanLin f₀ + b` and the usual search-direction recurrence. -/
@[expose] def iterates (A : Matrix n n ℝ) (b f0 : EuclideanSpace ℝ n) : ℕ → State n
  | 0 => init A b f0
  | v + 1 => step A (iterates A b f0 v)

/-- The zeroth conjugate-gradient state is the initial state. -/
@[simp] theorem iterates_zero
    (A : Matrix n n ℝ) (b f0 : EuclideanSpace ℝ n) :
    iterates A b f0 0 = init A b f0 := rfl

/-- The successor conjugate-gradient state is obtained by one application of
`step`. -/
@[simp] theorem iterates_succ
    (A : Matrix n n ℝ) (b f0 : EuclideanSpace ℝ n) (v : ℕ) :
    iterates A b f0 (v + 1) = step A (iterates A b f0 v) := rfl

/-- The initial state stores the initial solution. -/
@[simp] theorem init_solution
    (A : Matrix n n ℝ) (b f0 : EuclideanSpace ℝ n) :
    (init A b f0).solution = f0 := rfl

/-- The initial state stores the initial gradient. -/
@[simp] theorem init_gradient
    (A : Matrix n n ℝ) (b f0 : EuclideanSpace ℝ n) :
    (init A b f0).gradient = A.toEuclideanLin f0 + b := rfl

/-- The initial state stores the negative initial gradient as its search
direction. -/
@[simp] theorem init_direction
    (A : Matrix n n ℝ) (b f0 : EuclideanSpace ℝ n) :
    (init A b f0).direction = -(A.toEuclideanLin f0 + b) := rfl

/-- Stepping updates the stored solution by `nextSolution`. -/
@[simp] theorem step_solution
    (A : Matrix n n ℝ) (state : State n) :
    (step A state).solution = nextSolution A state := rfl

/-- Stepping updates the stored gradient by `nextGradient`. -/
@[simp] theorem step_gradient
    (A : Matrix n n ℝ) (state : State n) :
    (step A state).gradient = nextGradient A state := rfl

/-- Stepping updates the stored direction by `nextDirection`. -/
@[simp] theorem step_direction
    (A : Matrix n n ℝ) (state : State n) :
    (step A state).direction = nextDirection A state := rfl

end ConjugateGradient
