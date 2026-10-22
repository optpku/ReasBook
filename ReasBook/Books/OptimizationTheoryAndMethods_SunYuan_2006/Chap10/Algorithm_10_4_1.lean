/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.Normed.Lp.PiLp
import OptimizationTheoryAndMethods_SunYuan_2006.Chap10.Definition_10_1_extra_1

open scoped BigOperators

noncomputable section

variable {n m : ℕ}

local notation "Point" => EuclideanSpace ℝ (Fin n)
local notation "ConstraintPoint" => EuclideanSpace ℝ (Fin m)

namespace StandardPenaltyProblem

/-- The source augmented Lagrangian `(10.4.5)` used in the method below: equality-block
coordinates contribute `-(λ i) * cᵢ(x) + (1 / 2) * σ i * cᵢ(x)^2`, while inequality-block
coordinates use the same quadratic term when `cᵢ(x) < λ i / σ i` and the constant branch
`-((1 / 2 : ℝ) * (λ i)^2 / σ i)` otherwise. -/
def augmentedLagrangian
    (problem : StandardPenaltyProblem n m) (lam σ : ConstraintPoint) (x : Point) : ℝ :=
  problem.objective x +
    ∑ i : Fin m,
      if i.1 < problem.eqCount then
        (-(lam i) * problem.constraint i x +
          (1 / 2 : ℝ) * σ i * (problem.constraint i x) ^ (2 : ℕ))
      else if problem.constraint i x < lam i / σ i then
        (-(lam i) * problem.constraint i x +
          (1 / 2 : ℝ) * σ i * (problem.constraint i x) ^ (2 : ℕ))
      else
        (-((1 / 2 : ℝ) * (lam i) ^ (2 : ℕ) / σ i))

/-- Evaluating `problem.augmentedLagrangian lam σ x` expands to the source objective and the
coordinatewise penalty sum from `(10.4.5)`. -/
theorem augmentedLagrangian_eq
    (problem : StandardPenaltyProblem n m) (lam σ : ConstraintPoint) (x : Point) :
    problem.augmentedLagrangian lam σ x =
      problem.objective x +
        ∑ i : Fin m,
          if i.1 < problem.eqCount then
            (-(lam i) * problem.constraint i x +
              (1 / 2 : ℝ) * σ i * (problem.constraint i x) ^ (2 : ℕ))
          else if problem.constraint i x < lam i / σ i then
            (-(lam i) * problem.constraint i x +
              (1 / 2 : ℝ) * σ i * (problem.constraint i x) ^ (2 : ℕ))
          else
            (-((1 / 2 : ℝ) * (lam i) ^ (2 : ℕ) / σ i)) :=
  rfl

/-- The source multiplier update `(10.4.7)`-`(10.4.8)` used in the method below: equality
coordinates are `λ i - σ i * cᵢ(x)`, while inequality coordinates are
`max (λ i - σ i * cᵢ(x)) 0`. -/
def multiplierUpdate
    (problem : StandardPenaltyProblem n m) (lam σ : ConstraintPoint) (x : Point) :
    ConstraintPoint :=
  WithLp.toLp 2 fun i ↦
    if i.1 < problem.eqCount then
      lam i - σ i * problem.constraint i x
    else
      max (lam i - σ i * problem.constraint i x) 0

/-- The Step 3 acceptance test `(10.4.11)` compares the coordinatewise violation at `x_(k+1)`
against one quarter of the coordinatewise violation at `x_k`. -/
def penaltyUpdateTest
    (problem : StandardPenaltyProblem n m) (xk xNext : Point) (i : Fin m) : Bool :=
  decide
    (|(c⁽-⁾[problem] xNext) i| ≤
      (1 / 4 : ℝ) * |(c⁽-⁾[problem] xk) i|)

/-- Unfolding `problem.penaltyUpdateTest xk xNext i = true` gives the source Step 3 inequality
`|c⁽-⁾ᵢ(xNext)| ≤ (1 / 4) * |c⁽-⁾ᵢ(xk)|`. -/
theorem penaltyUpdateTest_eq_true_iff
    (problem : StandardPenaltyProblem n m) (xk xNext : Point) (i : Fin m) :
    problem.penaltyUpdateTest xk xNext i = true ↔
      |(c⁽-⁾[problem] xNext) i| ≤ (1 / 4 : ℝ) * |(c⁽-⁾[problem] xk) i| := by
  simp [penaltyUpdateTest]

/-- The source `ℓ∞`-norm of the violation vector `c⁽-⁾(x)`. -/
def linftyConstraintViolation (problem : StandardPenaltyProblem n m) (x : Point) : ℝ :=
  ‖WithLp.toLp (⊤ : ENNReal) (c⁽-⁾[problem] x).ofLp‖

/-- Evaluating `problem.linftyConstraintViolation x` expands to the `ℓ∞`-norm of
`c⁽-⁾[problem] x`. -/
theorem linftyConstraintViolation_eq (problem : StandardPenaltyProblem n m) (x : Point) :
    problem.linftyConstraintViolation x =
      ‖WithLp.toLp (⊤ : ENNReal) (c⁽-⁾[problem] x).ofLp‖ :=
  rfl

end StandardPenaltyProblem

-- Semantic recall: Chapter 10 already owns `StandardPenaltyProblem` in
-- `Definition_10_1_extra_1`, while the local Chapter 10 penalty files use `WithLp.toLp
-- (⊤ : ENNReal)` to express `ℓ∞` norms on `ℝ^m`. This item therefore records the algorithm data
-- directly over that chapter owner.

/-- A point `x` is an approximate minimizer of `f` when its objective value is within some
nonnegative error bound of every competitor in its ambient domain. This keeps Step 2 tied to
actual minimization of the source stage objective, rather than to an arbitrary external
predicate. -/
def Function.IsApproximateMinimizer {α : Type*} (f : α → ℝ) (x : α) : Prop :=
  ∃ η : ℝ, 0 ≤ η ∧ ∀ y : α, f x ≤ f y + η

/-- Unfolding `f.IsApproximateMinimizer x` gives the nonnegative-error minimization inequality
on the ambient domain of `f`. -/
theorem Function.isApproximateMinimizer_iff {α : Type*} (f : α → ℝ) (x : α) :
    f.IsApproximateMinimizer x ↔ ∃ η : ℝ, 0 ≤ η ∧ ∀ y : α, f x ≤ f y + η :=
  Iff.rfl

/-- Chapter10 Algorithm 10.4.1: an augmented Lagrangian method records a constrained problem
`problem`, a tolerance `ε ≥ 0`, an initial point `x₁`, initial multipliers `λ⁽¹⁾` whose
inequality coordinates are nonnegative, and an initial penalty vector `σ⁽¹⁾`. For each stage
`k ≥ 1`, the algorithm records the current primal iterate `x_k`, multiplier vector `λ⁽k⁾`, and
positive componentwise penalty vector `σ⁽k⁾`, with `σ⁽¹⁾` identified with the initial penalty
vector. Step 2 requires `x_(k+1)` to be an approximate
minimizer of the concrete stage objective `problem.augmentedLagrangian (λ⁽k⁾) (σ⁽k⁾)`, Step 3
uses the source test `(10.4.11)`
`|c⁽-⁾ᵢ(x_(k+1))| ≤ (1 / 4) * |c⁽-⁾ᵢ(x_k)|`, and Step 4 updates `λ⁽k+1⁾` by the concrete
formula `(10.4.7)`-`(10.4.8)`. The method stops when `‖c⁽-⁾(x_(k+1))‖∞ ≤ ε`; otherwise Step 3
updates `σᵢ⁽k+1⁾ = σᵢ⁽k⁾` if `(10.4.11)` holds and
`σᵢ⁽k+1⁾ = max (10 * σᵢ⁽k⁾) (k²)` otherwise. -/
structure AugmentedLagrangianMethod (n m : ℕ) where
  problem : StandardPenaltyProblem n m
  tolerance : ℝ
  toleranceNonneg : 0 ≤ tolerance
  initialPoint : EuclideanSpace ℝ (Fin n)
  initialMultiplier : EuclideanSpace ℝ (Fin m)
  initialMultiplier_nonneg :
    ∀ i : Fin m, problem.eqCount ≤ i.1 → 0 ≤ initialMultiplier i
  initialPenaltyParameter : EuclideanSpace ℝ (Fin m)
  iterate : ℕ → EuclideanSpace ℝ (Fin n)
  multiplier : ℕ → EuclideanSpace ℝ (Fin m)
  penaltyParameter : ℕ → EuclideanSpace ℝ (Fin m)
  penaltyParameterPos : ∀ k, 1 ≤ k → ∀ i : Fin m, 0 < penaltyParameter k i
  iterate_one : iterate 1 = initialPoint
  multiplier_one : multiplier 1 = initialMultiplier
  penaltyParameter_one : penaltyParameter 1 = initialPenaltyParameter
  approximateMinimizer_spec :
    ∀ k, 1 ≤ k →
      (problem.augmentedLagrangian
        (multiplier k)
        (penaltyParameter k)).IsApproximateMinimizer
          (iterate (k + 1))
  stop_or_step : ∀ k, 1 ≤ k →
    problem.linftyConstraintViolation (iterate (k + 1)) ≤ tolerance ∨
      (∀ i : Fin m,
        penaltyParameter (k + 1) i =
          if problem.penaltyUpdateTest (iterate k) (iterate (k + 1)) i then
            penaltyParameter k i
          else
            max (10 * penaltyParameter k i) ((k : ℝ) ^ (2 : ℕ))) ∧
        multiplier (k + 1) =
          problem.multiplierUpdate
            (multiplier k)
            (penaltyParameter k)
            (iterate (k + 1))

namespace AugmentedLagrangianMethod

/-- An augmented Lagrangian method canonically coerces to its underlying constrained problem. -/
instance : Coe (AugmentedLagrangianMethod n m) (StandardPenaltyProblem n m) where
  coe method := method.problem

/-- The initial penalty vector is positive componentwise because it is the stage-`1` penalty
vector. -/
theorem initialPenaltyParameterPos
    (method : AugmentedLagrangianMethod n m) (i : Fin m) :
    0 < method.initialPenaltyParameter i := by
  simpa [method.penaltyParameter_one] using method.penaltyParameterPos 1 le_rfl i

/-- The `k`th Step 2 objective is the source augmented-Lagrangian subproblem `(10.4.5)` built
from `problem`, `λ⁽k⁾`, and `σ⁽k⁾`. -/
def stageObjective (method : AugmentedLagrangianMethod n m) (k : ℕ) :
    Point → ℝ :=
  method.problem.augmentedLagrangian
    (method.multiplier k)
    (method.penaltyParameter k)

/-- Evaluating `method.stageObjective k x` gives the stage-`k` augmented-Lagrangian objective
at the point `x`. -/
theorem stageObjective_apply
    (method : AugmentedLagrangianMethod n m) (k : ℕ) (x : Point) :
    method.stageObjective k x =
      method.problem.augmentedLagrangian
        (method.multiplier k)
        (method.penaltyParameter k)
        x :=
  rfl

/-- The `k`th Step 3 test is the source condition `(10.4.11)` applied to `x_k` and
`x_(k+1)`. -/
def penaltyUpdateTestAt
    (method : AugmentedLagrangianMethod n m) (k : ℕ) (i : Fin m) : Bool :=
  method.problem.penaltyUpdateTest (method.iterate k) (method.iterate (k + 1)) i

/-- The `k`th Step 3 condition in Prop form is the source inequality `(10.4.11)` comparing the
coordinatewise violations at `x_k` and `x_(k+1)`. -/
def penaltyUpdateConditionAt
    (method : AugmentedLagrangianMethod n m) (k : ℕ) (i : Fin m) : Prop :=
  |(c⁽-⁾[method.problem] (method.iterate (k + 1))) i| ≤
    (1 / 4 : ℝ) * |(c⁽-⁾[method.problem] (method.iterate k)) i|

/-- The `k`th stage terminates exactly when the recorded point `x_(k+1)` satisfies the source
stopping test `‖c⁽-⁾(x_(k+1))‖∞ ≤ ε`. -/
def terminatedAt (method : AugmentedLagrangianMethod n m) (k : ℕ) : Prop :=
  method.problem.linftyConstraintViolation (method.iterate (k + 1)) ≤ method.tolerance

/-- Unfolding `method.terminatedAt k` gives the source stopping inequality at stage `k`. -/
theorem terminatedAt_iff (method : AugmentedLagrangianMethod n m) (k : ℕ) :
    terminatedAt method k ↔
      method.problem.linftyConstraintViolation (method.iterate (k + 1)) ≤ method.tolerance :=
  Iff.rfl

/-- Unfolding `method.penaltyUpdateTestAt k i = true` gives the source Step 3 condition
`|c⁽-⁾ᵢ(x_(k+1))| ≤ (1 / 4) * |c⁽-⁾ᵢ(x_k)|`. -/
theorem penaltyUpdateTestAt_eq_true_iff
    (method : AugmentedLagrangianMethod n m) (k : ℕ) (i : Fin m) :
    method.penaltyUpdateTestAt k i = true ↔ method.penaltyUpdateConditionAt k i := by
  simpa [penaltyUpdateTestAt, penaltyUpdateConditionAt] using
    method.problem.penaltyUpdateTest_eq_true_iff (method.iterate k) (method.iterate (k + 1)) i

/-- At each stage `k ≥ 1`, the recorded next iterate `x_(k+1)` satisfies the Step 2 approximate
minimizer predicate for the augmented-Lagrangian subproblem `(10.4.5)`. -/
theorem approximateMinimizer_at_nextIterate
    (method : AugmentedLagrangianMethod n m) {k : ℕ} (hk : 1 ≤ k) :
    (method.stageObjective k).IsApproximateMinimizer (method.iterate (k + 1)) := by
  simpa [stageObjective] using method.approximateMinimizer_spec k hk

/-- If the `k`th stage does not terminate, then Step 3 updates the componentwise penalty
parameters by the source rule `(10.4.13)`. -/
theorem penaltyParameter_update_eq
    (method : AugmentedLagrangianMethod n m) {k : ℕ} (hk : 1 ≤ k)
    (hstop : ¬ terminatedAt method k) :
    ∀ i : Fin m,
      method.penaltyParameter (k + 1) i =
        if penaltyUpdateTestAt method k i then
          method.penaltyParameter k i
        else
          max (10 * method.penaltyParameter k i) ((k : ℝ) ^ (2 : ℕ)) := by
  rcases method.stop_or_step k hk with hterm | hstep
  · exact (hstop hterm).elim
  · exact hstep.1

/-- If the `k`th stage does not terminate, then Step 4 updates the multiplier vector using the
concrete source formula `(10.4.7)`-`(10.4.8)`. -/
theorem multiplier_update_eq
    (method : AugmentedLagrangianMethod n m) {k : ℕ} (hk : 1 ≤ k)
    (hstop : ¬ terminatedAt method k) :
    method.multiplier (k + 1) =
      method.problem.multiplierUpdate
        (method.multiplier k)
        (method.penaltyParameter k)
        (method.iterate (k + 1)) := by
  rcases method.stop_or_step k hk with hterm | hstep
  · exact (hstop hterm).elim
  · exact hstep.2

end AugmentedLagrangianMethod

#print axioms StandardPenaltyProblem.constraintViolation
#print axioms StandardPenaltyProblem.augmentedLagrangian
#print axioms StandardPenaltyProblem.multiplierUpdate
#print axioms StandardPenaltyProblem.linftyConstraintViolation
