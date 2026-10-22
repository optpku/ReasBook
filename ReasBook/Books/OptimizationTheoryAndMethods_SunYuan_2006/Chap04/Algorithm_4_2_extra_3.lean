/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

-- Domain sample:
-- * `LinearConjugateGradientMethod`
-- * `LinearConjugateGradientMethod.terminatedAt`
-- * `LinearConjugateGradientMethod.nonterminalStep`
-- * `ConjugateGradientIterativeScheme.terminatedAt`
--
-- Owner choice:
-- * `PreconditionedConjugateGradientMethod` remains the `source-facing` owner here: the textbook
--   recurrence includes the extra primitive data `v k = W⁻¹ r k`, so this file should not be
--   collapsed to the unpreconditioned chapter owner.
-- * The relevant chapter style is still the same as `LinearConjugateGradientMethod`: recurrence
--   quotients and successor formulas belong to the nonterminal layer, while termination and
--   stationary continuation are separate derived/guarded API.

section

variable {n : ℕ}

local notation "Vector" => Fin n → ℝ

/-- Chapter04 Algorithm 4.2-extra-3: a preconditioned conjugate gradient method for the linear
system `G.mulVec x + b = 0` with preconditioner `W` and initial point `x0` consists of iterates
`x k`, residuals/gradients `r k`, preconditioned residuals `v k`, search directions `d k`, step
sizes `α k`, and recurrence coefficients `β k`. The initialization is `x 0 = x0`,
`r 0 = G.mulVec x0 + b`, `v k = W⁻¹.mulVec (r k)`, and `d 0 = -v 0`. For every `k`, the step
size, iterate, residual, recurrence coefficient, and next direction satisfy the explicit
preconditioned conjugate-gradient recurrences from the textbook at each nonterminal stage
`r k ≠ 0`, while a terminating stage propagates the zero residual, zero direction, and stationary
iterate thereafter. The denominator conditions record that the fractions defining `α k` and `β k`
are well-defined on nonterminal steps. The field `preconditioner_isUnit` records the source's use
of `W⁻¹`. -/
structure PreconditionedConjugateGradientMethod
    (G W : Matrix (Fin n) (Fin n) ℝ) (b x0 : Vector) where
  x : ℕ → Vector
  r : ℕ → Vector
  v : ℕ → Vector
  d : ℕ → Vector
  α : ℕ → ℝ
  β : ℕ → ℝ
  preconditioner_isUnit : IsUnit W
  x_zero : x 0 = x0
  residual_zero : r 0 = G.mulVec x0 + b
  preconditionedResidual_eq :
    ∀ k : ℕ,
      v k = W⁻¹.mulVec (r k)
  direction_zero : d 0 = -v 0
  stepSize_denom_ne_zero :
    ∀ k : ℕ, r k ≠ 0 →
      dotProduct (d k) (G.mulVec (d k)) ≠ 0
  stepSize_eq :
    ∀ k : ℕ, r k ≠ 0 →
      α k = dotProduct (r k) (v k) / dotProduct (d k) (G.mulVec (d k))
  iterate_eq :
    ∀ k : ℕ, r k ≠ 0 →
      x (k + 1) = x k + α k • d k
  residual_eq :
    ∀ k : ℕ, r k ≠ 0 →
      r (k + 1) = r k + α k • G.mulVec (d k)
  beta_denom_ne_zero :
    ∀ k : ℕ, r k ≠ 0 →
      dotProduct (r k) (v k) ≠ 0
  beta_eq :
    ∀ k : ℕ, r k ≠ 0 →
      β k = dotProduct (r (k + 1)) (v (k + 1)) / dotProduct (r k) (v k)
  direction_eq :
    ∀ k : ℕ, r k ≠ 0 →
      d (k + 1) = -v (k + 1) + β k • d k
  residual_stationary :
    ∀ k t : ℕ, r k = 0 → k ≤ t → r t = 0
  direction_zero_of_terminated :
    ∀ k t : ℕ, r k = 0 → k ≤ t → d t = 0
  iterate_stationary :
    ∀ k t : ℕ, r k = 0 → k ≤ t → x t = x k

/-- A preconditioned conjugate gradient method can be used as its sequence of iterates. -/
instance {G W : Matrix (Fin n) (Fin n) ℝ} {b x0 : Vector} :
    CoeFun (PreconditionedConjugateGradientMethod G W b x0) (fun _ ↦ ℕ → Vector) where
  coe A := A.x

/-- A preconditioned conjugate-gradient method terminates at stage `k` when the current
residual/gradient vanishes. -/
def PreconditionedConjugateGradientMethod.terminatedAt
    {G W : Matrix (Fin n) (Fin n) ℝ} {b x0 : Vector}
    (A : PreconditionedConjugateGradientMethod G W b x0) (k : ℕ) : Prop :=
  A.r k = 0

/-- The gradient notation `g k` used in the source is the residual sequence `r k`. -/
def PreconditionedConjugateGradientMethod.g
    {G W : Matrix (Fin n) (Fin n) ℝ} {b x0 : Vector}
    (A : PreconditionedConjugateGradientMethod G W b x0) (k : ℕ) : Vector :=
  A.r k

/-- Once a preconditioned conjugate-gradient method has terminated, all later stages are also
terminating stages. -/
theorem PreconditionedConjugateGradientMethod.terminatedAt_mono
    {G W : Matrix (Fin n) (Fin n) ℝ} {b x0 : Vector}
    (A : PreconditionedConjugateGradientMethod G W b x0) {k t : ℕ}
    (hk : A.terminatedAt k) (hkt : k ≤ t) :
    A.terminatedAt t :=
  A.residual_stationary k t hk hkt

/-- After termination, the gradient notation `g` stays equal to `0` at every later stage. -/
theorem PreconditionedConjugateGradientMethod.g_eq_zero_of_terminatedAt
    {G W : Matrix (Fin n) (Fin n) ℝ} {b x0 : Vector}
    (A : PreconditionedConjugateGradientMethod G W b x0) {k t : ℕ}
    (hk : A.terminatedAt k) (hkt : k ≤ t) :
    A.g t = 0 :=
  A.residual_stationary k t hk hkt

/-- After termination, all later preconditioned residuals are zero. -/
theorem PreconditionedConjugateGradientMethod.v_eq_zero_of_terminatedAt
    {G W : Matrix (Fin n) (Fin n) ℝ} {b x0 : Vector}
    (A : PreconditionedConjugateGradientMethod G W b x0) {k t : ℕ}
    (hk : A.terminatedAt k) (hkt : k ≤ t) :
    A.v t = 0 := by
  rw [A.preconditionedResidual_eq t, A.terminatedAt_mono hk hkt]
  simp

/-- After termination, all later search directions are zero. -/
theorem PreconditionedConjugateGradientMethod.d_eq_zero_of_terminatedAt
    {G W : Matrix (Fin n) (Fin n) ℝ} {b x0 : Vector}
    (A : PreconditionedConjugateGradientMethod G W b x0) {k t : ℕ}
    (hk : A.terminatedAt k) (hkt : k ≤ t) :
    A.d t = 0 :=
  A.direction_zero_of_terminated k t hk hkt

/-- After termination, the iterate sequence stays constant. -/
theorem PreconditionedConjugateGradientMethod.x_eq_of_terminatedAt
    {G W : Matrix (Fin n) (Fin n) ℝ} {b x0 : Vector}
    (A : PreconditionedConjugateGradientMethod G W b x0) {k t : ℕ}
    (hk : A.terminatedAt k) (hkt : k ≤ t) :
    A.x t = A.x k :=
  A.iterate_stationary k t hk hkt

/-- A nonterminal preconditioned conjugate-gradient step carries the well-defined PCG quotients
and the textbook updates for the next iterate, residual, and direction. -/
theorem PreconditionedConjugateGradientMethod.nonterminalStep
    {G W : Matrix (Fin n) (Fin n) ℝ} {b x0 : Vector}
    (A : PreconditionedConjugateGradientMethod G W b x0) {k : ℕ} (hk : A.r k ≠ 0) :
    dotProduct (A.d k) (G.mulVec (A.d k)) ≠ 0 ∧
      A.α k = dotProduct (A.r k) (A.v k) / dotProduct (A.d k) (G.mulVec (A.d k)) ∧
      A.x (k + 1) = A.x k + A.α k • A.d k ∧
      A.r (k + 1) = A.r k + A.α k • G.mulVec (A.d k) ∧
      dotProduct (A.r k) (A.v k) ≠ 0 ∧
      A.β k = dotProduct (A.r (k + 1)) (A.v (k + 1)) / dotProduct (A.r k) (A.v k) ∧
      A.d (k + 1) = -A.v (k + 1) + A.β k • A.d k := by
  refine ⟨A.stepSize_denom_ne_zero k hk, A.stepSize_eq k hk, A.iterate_eq k hk,
    A.residual_eq k hk, A.beta_denom_ne_zero k hk, A.beta_eq k hk, A.direction_eq k hk⟩

end
