/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import OptimizationTheoryAndMethods_SunYuan_2006.Chap10.Definition_10_6_extra_1

noncomputable section

section

variable {n m : ℕ}

local notation "Point" => EuclideanSpace ℝ (Fin n)
local notation "ConstraintPoint" => EuclideanSpace ℝ (Fin m)

-- Domain sampling:
-- * primary domain: Chapter 10 nonsmooth exact penalty methods for mixed constrained
--   optimization problems.
-- * inspected owner declarations:
--   `StandardPenaltyProblem.constraintViolation` and `PenaltyFunction` in
--   `Definition_10_1_extra_1`,
--   `IsStrongDistanceFunction`, the Chapter 1 `ℓ₁` notation `‖·‖₁`, and
--   `PenaltyFunction.nonsmoothExact` in
--   `Definition_10_6_extra_1`,
--   `SimplePenaltyFunctionMethod.terminatedAt` in `Algorithm_10_2_3` as the chapter's
--   algorithm-layer precedent.
-- * best owner abstraction: the source-facing stage objective
--   `problem.nonsmoothExactPenalty penaltyKernel σ`, with `PenaltyFunction.nonsmoothExact` only
--   as the bundled bridge/view once positivity is needed.
-- * primitive data vs derived API: the method stores the stagewise problem/kernel/iterate data
--   and minimizer certificates; the stage penalty function and the stopping predicate are
--   derived bridge API.

/-- A nonsmooth exact penalty method for Chapter10 Algorithm 10.6.4 records a constrained problem
`problem`, a strong-distance penalty kernel `h`, an initial point `x₁`, and an initial penalty
parameter `σ₁ > 0`. It also records which stages are reached by the book algorithm, with
`reached 1`. For each reached stage `k ≥ 1`, it records the current iterate `x_k`, the penalty
parameter `σ_k`, the starting point used for the stage-`k` exact-penalty subproblem solve, and
a selected solution `x(σ_k)` of
`min_{x ∈ ℝ^n} problem.objective x + σ_k * h (c⁽-⁾[problem] x)`.
Step 2 is represented by requiring that, at each reached stage, the recorded starting point for
the stage-`k` subproblem is exactly `x_k` and that `x(σ_k)` globally minimizes the stage-`k`
nonsmooth exact penalty objective. Step 3 stops when `c⁽-⁾[problem] (x(σ_k)) = 0`; otherwise it
updates `x_(k+1) = x(σ_k)` and `σ_(k+1) = 10 * σ_k`, and the next stage `k + 1` is reached
exactly when the stage-`k` stopping test fails. The reached stages form a contiguous prefix, so
once some stage terminates no later stage is reached. -/
structure NonsmoothExactPenaltyMethod (n m : ℕ) where
  problem : StandardPenaltyProblem n m
  penaltyKernel : EuclideanSpace ℝ (Fin m) → ℝ
  penaltyKernelStrong : IsStrongDistanceFunction penaltyKernel
  initialPoint : EuclideanSpace ℝ (Fin n)
  initialPenaltyParameter : ℝ
  initialPenaltyParameterPos : 0 < initialPenaltyParameter
  reached : ℕ → Prop
  iterate : ℕ → EuclideanSpace ℝ (Fin n)
  penaltyParameter : ℕ → ℝ
  penaltyParameterPos (k : ℕ) (_ : 1 ≤ k) (_ : reached k) : 0 < penaltyParameter k
  subproblemStartingPoint : ℕ → EuclideanSpace ℝ (Fin n)
  subproblemSolution : ℕ → EuclideanSpace ℝ (Fin n)
  reached_one : reached 1
  reached_pred (k : ℕ) (_ : 1 ≤ k) (_ : reached (k + 1)) : reached k
  iterate_one : iterate 1 = initialPoint
  penaltyParameter_one : penaltyParameter 1 = initialPenaltyParameter
  subproblemStartingPoint_spec (k : ℕ) (_ : 1 ≤ k) (_ : reached k) :
    subproblemStartingPoint k = iterate k
  subproblemSolution_spec (k : ℕ) (_ : 1 ≤ k) (_ : reached k) :
    IsMinOn
      (problem.nonsmoothExactPenalty penaltyKernel (penaltyParameter k))
      Set.univ
      (subproblemSolution k)
  stop_or_step (k : ℕ) (_ : 1 ≤ k) (_ : reached k) :
    problem.constraintViolation (subproblemSolution k) = 0 ∨
      iterate (k + 1) = subproblemSolution k ∧
        penaltyParameter (k + 1) = 10 * penaltyParameter k
  reached_succ_iff (k : ℕ) (_ : 1 ≤ k) (_ : reached k) :
    reached (k + 1) ↔ problem.constraintViolation (subproblemSolution k) ≠ 0

namespace NonsmoothExactPenaltyMethod

/-- A nonsmooth exact penalty method canonically coerces to its underlying constrained problem. -/
instance instCoeStandardPenaltyProblem :
    Coe (NonsmoothExactPenaltyMethod n m) (StandardPenaltyProblem n m) where
  coe := NonsmoothExactPenaltyMethod.problem

/-- The kernel recorded by a nonsmooth exact penalty method is a strong distance function. -/
instance instIsStrongDistanceFunction (method : NonsmoothExactPenaltyMethod n m) :
    IsStrongDistanceFunction method.penaltyKernel :=
  method.penaltyKernelStrong

/-- The reached stage-`k` subproblem is the canonical Chapter 10 nonsmooth exact penalty
function attached to `method.problem`, `method.penaltyKernel`, and `σ_k`. -/
def stagePenaltyFunction
    (method : NonsmoothExactPenaltyMethod n m) (k : ℕ) (hk : 1 ≤ k)
    (hreached : method.reached k) :
    PenaltyFunction method.problem :=
  PenaltyFunction.nonsmoothExact
    method.problem
    method.penaltyKernel
    (method.penaltyParameter k)
    (method.penaltyParameterPos k hk hreached)

/-- Evaluating `method.stagePenaltyFunction k hk hreached` unfolds to the stage-`k` source exact
penalty formula. -/
theorem stagePenaltyFunction_apply
    (method : NonsmoothExactPenaltyMethod n m) (k : ℕ) (hk : 1 ≤ k)
    (hreached : method.reached k) (x : Point) :
    method.stagePenaltyFunction k hk hreached x =
      method.problem.objective x +
        method.penaltyParameter k * method.penaltyKernel (c⁽-⁾[method.problem] x) := by
  rw [stagePenaltyFunction]
  exact
    PenaltyFunction.nonsmoothExact_apply
      method.problem
      method.penaltyKernel
      (method.penaltyParameter k)
      (method.penaltyParameterPos k hk hreached)
      x

/-- The `k`th stage terminates exactly when the selected stage-`k` subproblem solution is
feasible, equivalently when the source violation vector vanishes. -/
def terminatedAt (method : NonsmoothExactPenaltyMethod n m) (k : ℕ) : Prop :=
  c⁽-⁾[method.problem] (method.subproblemSolution k) = 0

/-- Unfolding `method.terminatedAt k` gives the source stopping test
`c⁽-⁾[method.problem] (x(σ_k)) = 0`. -/
theorem terminatedAt_iff
    (method : NonsmoothExactPenaltyMethod n m) (k : ℕ) :
    method.terminatedAt k ↔ c⁽-⁾[method.problem] (method.subproblemSolution k) = 0 :=
  Iff.rfl

/-- For each book stage `k ≥ 1`, the stage-`k` nonsmooth exact penalty subproblem is started
from the current iterate `x_k`. -/
theorem subproblemStartingPoint_eq_iterate
    (method : NonsmoothExactPenaltyMethod n m) {k : ℕ} (hk : 1 ≤ k)
    (hreached : method.reached k) :
    method.subproblemStartingPoint k = method.iterate k :=
  method.subproblemStartingPoint_spec k hk hreached

/-- The recorded stage-`k` solution globally minimizes the source-facing stage-`k` nonsmooth
exact penalty objective on `ℝ^n`. -/
theorem subproblemSolution_isMinimizer
    (method : NonsmoothExactPenaltyMethod n m) {k : ℕ} (hk : 1 ≤ k)
    (hreached : method.reached k) :
    IsMinOn
      (method.problem.nonsmoothExactPenalty
        method.penaltyKernel
        (method.penaltyParameter k))
      Set.univ
      (method.subproblemSolution k) :=
  method.subproblemSolution_spec k hk hreached

/-- The same minimizer certificate can be read through the bundled stage-`k` penalty-function
bridge. -/
theorem subproblemSolution_isMinimizer_stagePenaltyFunction
    (method : NonsmoothExactPenaltyMethod n m) {k : ℕ} (hk : 1 ≤ k)
    (hreached : method.reached k) :
    IsMinOn
      (method.stagePenaltyFunction k hk hreached)
      Set.univ
      (method.subproblemSolution k) := by
  change IsMinOn
    ((PenaltyFunction.nonsmoothExact
      method.problem
      method.penaltyKernel
      (method.penaltyParameter k)
      (method.penaltyParameterPos k hk hreached)).toFun)
    Set.univ
    (method.subproblemSolution k)
  convert method.subproblemSolution_isMinimizer hk hreached using 1
  funext x
  rfl

/-- If the `k`th stage is reached, then Algorithm 10.6.4 reaches stage `k + 1` exactly when the
source stopping test `c⁽-⁾[problem] (x(σ_k)) = 0` fails at stage `k`. -/
theorem reached_succ_iff_not_terminatedAt
    (method : NonsmoothExactPenaltyMethod n m) {k : ℕ} (hk : 1 ≤ k)
    (hreached : method.reached k) :
    method.reached (k + 1) ↔ ¬ method.terminatedAt k := by
  simpa [terminatedAt] using method.reached_succ_iff k hk hreached

/-- Helper for Chapter10 Algorithm 10.6.4: any reached successor stage forces the preceding
stage to be reached as well. -/
theorem reachedOfReachedSucc
    (method : NonsmoothExactPenaltyMethod n m) {k : ℕ} (hk : 1 ≤ k)
    (hreachedSucc : method.reached (k + 1)) :
    method.reached k := by
  -- Reachability forms a contiguous prefix, so a reached successor stage has a reached
  -- predecessor.
  exact method.reached_pred k hk hreachedSucc

/-- Helper for Chapter10 Algorithm 10.6.4: once a stage is not reached, the next stage cannot
be reached either. -/
theorem notReachedSuccOfNotReached
    (method : NonsmoothExactPenaltyMethod n m) {k : ℕ} (hk : 1 ≤ k)
    (hnotReached : ¬ method.reached k) :
    ¬ method.reached (k + 1) := by
  intro hreachedSucc
  -- A reached successor would force the current stage to be reached, contradicting `hnotReached`.
  exact hnotReached (method.reachedOfReachedSucc hk hreachedSucc)

/-- Helper for Chapter10 Algorithm 10.6.4: termination at a reached stage rules out immediate
reachability of the next stage. -/
theorem notReachedNextOfTerminatedAt
    (method : NonsmoothExactPenaltyMethod n m) {k : ℕ} (hk : 1 ≤ k)
    (hreached : method.reached k) (hterm : method.terminatedAt k) :
    ¬ method.reached (k + 1) := by
  intro hreachedSucc
  -- The successor-stage characterization turns a hypothetical next reached stage into the
  -- negation of the stage-`k` stopping test.
  exact ((method.reached_succ_iff_not_terminatedAt hk hreached).1 hreachedSucc) hterm

/-- Chapter10 Algorithm 10.6.4: if the method terminates at a reached stage `k`, then no later
stage `j > k` is reached. -/
theorem not_reached_of_terminatedAt
    (method : NonsmoothExactPenaltyMethod n m) {k j : ℕ} (hk : 1 ≤ k)
    (hreached : method.reached k) (hterm : method.terminatedAt k) (hkj : k < j) :
    ¬ method.reached j := by
  -- First show that every strict successor stage of `k` is unreachable once stage `k`
  -- terminates.
  have hgap : ∀ t : ℕ, ¬ method.reached (k + (t + 1)) := by
    intro t
    induction t with
    | zero =>
        -- The first later stage is ruled out directly by the stopping test at stage `k`.
        simpa using method.notReachedNextOfTerminatedAt hk hreached hterm
    | succ t ih =>
        have hstage : 1 ≤ k + (t + 1) := by
          -- Every index of the form `k + (t + 1)` is a valid predecessor stage for
          -- `reached_pred`.
          simpa [Nat.add_assoc] using Nat.succ_le_succ (Nat.zero_le (k + t))
        -- Once stage `k + (t + 1)` is known unreachable, the predecessor-closure of `reached`
        -- forbids the next stage as well.
        simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
          (method.notReachedSuccOfNotReached hstage ih)
  have hkSuccLe : k + 1 ≤ j := Nat.succ_le_of_lt hkj
  let t := j - (k + 1)
  have hj : j = k + (t + 1) := by
    -- Normalize any later index `j` to a successor gap over `k`.
    calc
      j = (k + 1) + (j - (k + 1)) := (Nat.add_sub_of_le hkSuccLe).symm
      _ = k + (t + 1) := by
        simp [t, Nat.add_assoc, Nat.add_comm]
  -- The normalized gap now falls under the uniform induction statement `hgap`.
  rw [hj]
  exact hgap t

/-- If the `k`th stage does not terminate, then the next iterate is updated to the selected
stage-`k` exact-penalty minimizer `x(σ_k)`. -/
theorem iterate_update_eq
    (method : NonsmoothExactPenaltyMethod n m) {k : ℕ} (hk : 1 ≤ k)
    (hreached : method.reached k) (hactive : ¬ method.terminatedAt k) :
    method.iterate (k + 1) = method.subproblemSolution k := by
  rcases method.stop_or_step k hk hreached with hterm | hstep
  · exact (False.elim <| hactive hterm)
  · exact hstep.1

/-- If the `k`th stage does not terminate, then the next penalty parameter is multiplied by
`10`, so `σ_(k+1) = 10 * σ_k`. -/
theorem penaltyParameter_update_eq
    (method : NonsmoothExactPenaltyMethod n m) {k : ℕ} (hk : 1 ≤ k)
    (hreached : method.reached k) (hactive : ¬ method.terminatedAt k) :
    method.penaltyParameter (k + 1) = 10 * method.penaltyParameter k := by
  rcases method.stop_or_step k hk hreached with hterm | hstep
  · exact (False.elim <| hactive hterm)
  · exact hstep.2

end NonsmoothExactPenaltyMethod

#print axioms StandardPenaltyProblem.constraintViolation
#print axioms PenaltyFunction.nonsmoothExact
#print axioms NonsmoothExactPenaltyMethod.stagePenaltyFunction

end
