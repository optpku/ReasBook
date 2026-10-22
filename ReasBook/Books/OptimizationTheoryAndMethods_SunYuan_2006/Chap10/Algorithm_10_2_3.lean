/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import OptimizationTheoryAndMethods_SunYuan_2006.Chap10.Definition_10_2_extra_1

noncomputable section

section

local notation:max "P_[" problem ", " α "](" σ ")" =>
  StandardPenaltyProblem.simplePenaltyObjective problem σ α

-- Domain sampling:
-- * primary domain: Chapter 10 simple-penalty methods for mixed equality/inequality constrained
--   problems in `ℝ^n`
-- * inspected project declarations of the same kind:
--   `StandardPenaltyProblem` and `c⁽-⁾[problem]` in `Definition_10_1_extra_1`,
--   `PenaltyFunction` in the same file as the canonical penalty-layer owner,
--   `StandardPenaltyProblem.simplePenaltyObjective` and `PenaltyFunction.simple` in
--   `Definition_10_2_extra_1`
-- * best owner abstraction: the source-facing stage objective belongs to
--   `StandardPenaltyProblem`; `PenaltyFunction.simple` is only the bundled bridge/view
-- * primitive data vs. derived API:
--   primitive data are the constrained problem, exponent, tolerance, the reached-stage
--   predicate, iterates, penalty parameters, and recorded reached-stage solves;
--   the stage penalty function, stopping predicate, and minimizer/update views are derived API

/-- A simple penalty function method for Chapter10 Algorithm 10.2.3 records a constrained problem,
an initial point `x₁ ∈ ℝ^n`, an initial penalty parameter `σ₁ > 0`, and a tolerance `ε ≥ 0`.
It also records which stages are reached by the book algorithm, with `reached 1`. For each
reached stage `k ≥ 1`, it records the current iterate `x_k`, the penalty parameter `σ_k`, and a
selected solution `x(σ_k)` of the subproblem `min_{x ∈ ℝ^n} P_(σ_k)(x)`, where
`P_σ = problem.simplePenaltyObjective σ α`. The solver internals are abstracted away, so the
stage-`k` starting point is canonically the current iterate `x_k` and is not separate primitive
data. The method stops when `‖c⁽-⁾[problem] (x(σ_k))‖ ≤ ε`; otherwise it updates
`x_(k+1) = x(σ_k)` and `σ_(k+1) = 10 * σ_k`, and the next stage `k + 1` is reached exactly when
the stage-`k` stopping test fails. The reached stages therefore form a contiguous prefix, so
once some stage terminates no later stage is reached. -/
structure SimplePenaltyFunctionMethod (n m : ℕ) where
  problem : StandardPenaltyProblem n m
  penaltyExponent : ℝ
  penaltyExponentPos : 0 < penaltyExponent
  tolerance : ℝ
  toleranceNonneg : 0 ≤ tolerance
  initialPoint : EuclideanSpace ℝ (Fin n)
  initialPenaltyParameter : ℝ
  initialPenaltyParameterPos : 0 < initialPenaltyParameter
  reached : ℕ → Prop
  iterate : ℕ → EuclideanSpace ℝ (Fin n)
  penaltyParameter : ℕ → ℝ
  penaltyParameterPos (k : ℕ) (_ : 1 ≤ k) (_ : reached k) : 0 < penaltyParameter k
  subproblemSolution : ℕ → EuclideanSpace ℝ (Fin n)
  reached_one : reached 1
  iterate_one : iterate 1 = initialPoint
  penaltyParameter_one : penaltyParameter 1 = initialPenaltyParameter
  subproblemSolution_spec (k : ℕ) (_ : 1 ≤ k) (_ : reached k) :
    IsMinOn
      (P_[problem, penaltyExponent](penaltyParameter k))
      Set.univ
      (subproblemSolution k)
  stop_or_step (k : ℕ) (_ : 1 ≤ k) (_ : reached k) :
    ‖StandardPenaltyProblem.constraintViolation problem (subproblemSolution k)‖ ≤ tolerance ∨
      iterate (k + 1) = subproblemSolution k ∧
        penaltyParameter (k + 1) = 10 * penaltyParameter k
  reached_succ_iff (k : ℕ) (_ : 1 ≤ k) :
    reached (k + 1) ↔
      reached k ∧
        ¬ (‖StandardPenaltyProblem.constraintViolation problem (subproblemSolution k)‖ ≤
            tolerance)

namespace SimplePenaltyFunctionMethod

variable {n m : ℕ}

local notation "Point" => EuclideanSpace ℝ (Fin n)

/-- A simple penalty function method canonically coerces to its underlying constrained problem. -/
instance : Coe (SimplePenaltyFunctionMethod n m) (StandardPenaltyProblem n m) where
  coe := SimplePenaltyFunctionMethod.problem

section

variable (method : SimplePenaltyFunctionMethod n m)

local notation:max "P_" σ => method.problem.simplePenaltyObjective σ method.penaltyExponent

/-- The recorded stage-`k` solution globally minimizes the source-facing Section 10.2 stage
objective `P_(σ_k)`. -/
theorem subproblemSolution_isMinimizer
    {k : ℕ} (hk : 1 ≤ k) (hreached : method.reached k) :
    IsMinOn
      (P_ (method.penaltyParameter k))
      Set.univ
      (method.subproblemSolution k) :=
  method.subproblemSolution_spec k hk hreached

/-- The same minimizer certificate can be read through the canonical bundled owner
`PenaltyFunction.simple`. -/
theorem subproblemSolution_isMinimizer_simple
    {k : ℕ} (hk : 1 ≤ k) (hreached : method.reached k) :
    IsMinOn
      (PenaltyFunction.simple
        method.problem
        method.penaltyExponent
        method.penaltyExponentPos
        (method.penaltyParameter k)
        (method.penaltyParameterPos k hk hreached))
      Set.univ
      (method.subproblemSolution k) := by
  convert method.subproblemSolution_isMinimizer hk hreached using 1
  ext x
  exact
    (PenaltyFunction.simple_apply
      method.problem
      method.penaltyExponent
      method.penaltyExponentPos
      (method.penaltyParameter k)
      (method.penaltyParameterPos k hk hreached)
      x).symm

end

/-- The `k`th stage terminates exactly when the recorded stage-`k` subproblem solution satisfies
the source stopping test `‖c⁽-⁾[problem] (x(σ_k))‖ ≤ ε`. -/
def terminatedAt (method : SimplePenaltyFunctionMethod n m) (k : ℕ) : Prop :=
  ‖c⁽-⁾[method.problem] (method.subproblemSolution k)‖ ≤ method.tolerance

/-- Unfolding `method.terminatedAt k` gives the source stopping inequality at stage `k`. -/
theorem terminatedAt_iff
    (method : SimplePenaltyFunctionMethod n m) (k : ℕ) :
    method.terminatedAt k ↔
      ‖c⁽-⁾[method.problem] (method.subproblemSolution k)‖ ≤ method.tolerance :=
  Iff.rfl

/-- Algorithm 10.2.3 reaches stage `k + 1` exactly when stage `k` is reached and the source
stopping test fails at stage `k`. -/
theorem reached_succ_iff_not_terminatedAt
    (method : SimplePenaltyFunctionMethod n m) {k : ℕ} (hk : 1 ≤ k) :
    method.reached (k + 1) ↔ method.reached k ∧ ¬ method.terminatedAt k := by
  simpa [terminatedAt] using method.reached_succ_iff k hk

/-- Any reached stage `k + 1` of Algorithm 10.2.3 comes from a reached previous stage `k`;
later stages cannot reappear after the algorithm has terminated. -/
theorem reached_of_reached_succ
    (method : SimplePenaltyFunctionMethod n m) {k : ℕ} (hk : 1 ≤ k)
    (hreached : method.reached (k + 1)) :
    method.reached k :=
  (method.reached_succ_iff_not_terminatedAt hk).1 hreached |>.1

/-- Helper for Chapter10 Algorithm 10.2.3: once a stage is not reached, the next stage cannot
be reached either. -/
theorem notReachedSuccOfNotReached
    (method : SimplePenaltyFunctionMethod n m) {k : ℕ} (hk : 1 ≤ k)
    (hnotReached : ¬ method.reached k) :
    ¬ method.reached (k + 1) := by
  intro hreachedSucc
  -- Reachability is predecessor-closed, so a reached successor would force stage `k` to exist.
  exact hnotReached (method.reached_of_reached_succ hk hreachedSucc)

/-- Helper for Chapter10 Algorithm 10.2.3: termination at stage `k` rules out immediate
reachability of the next stage. -/
theorem notReachedNextOfTerminatedAt
    (method : SimplePenaltyFunctionMethod n m) {k : ℕ} (hk : 1 ≤ k)
    (hterm : method.terminatedAt k) :
    ¬ method.reached (k + 1) := by
  intro hreachedSucc
  -- The successor-stage criterion turns a hypothetical next stage into `¬ terminatedAt k`.
  exact ((method.reached_succ_iff_not_terminatedAt hk).1 hreachedSucc).2 hterm

/-- Helper for Chapter10 Algorithm 10.2.3: if stage `k` terminates, then every later successor
gap `k + (t + 1)` is unreachable. -/
theorem notReachedGapOfTerminatedAt
    (method : SimplePenaltyFunctionMethod n m) {k : ℕ} (hk : 1 ≤ k)
    (hterm : method.terminatedAt k) :
    ∀ t : ℕ, ¬ method.reached (k + (t + 1)) := by
  intro t
  induction t with
  | zero =>
      -- The first later stage is excluded directly by termination at stage `k`.
      simpa using method.notReachedNextOfTerminatedAt hk hterm
  | succ t ih =>
      have hstage : 1 ≤ k + (t + 1) := by
        -- Any index of the form `k + (t + 1)` is a valid predecessor stage for the reachability
        -- recursion.
        simpa [Nat.add_assoc] using Nat.succ_le_succ (Nat.zero_le (k + t))
      -- After one unreachable stage appears, predecessor-closure prevents the next stage too.
      simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
        (method.notReachedSuccOfNotReached hstage ih)

/-- Chapter10 Algorithm 10.2.3: if the method terminates at a reached stage `k`, then no later
stage `j > k` is
reached. -/
theorem not_reached_of_terminatedAt
    (method : SimplePenaltyFunctionMethod n m) {k j : ℕ} (hk : 1 ≤ k)
    (hreached : method.reached k) (hterm : method.terminatedAt k) (hkj : k < j) :
    ¬ method.reached j := by
  -- First propagate the cutoff from stage `k + 1` to every later successor gap.
  have hgap : ∀ t : ℕ, ¬ method.reached (k + (t + 1)) :=
    method.notReachedGapOfTerminatedAt hk hterm
  let _ := hreached
  have hkSuccLe : k + 1 ≤ j := Nat.succ_le_of_lt hkj
  let t := j - (k + 1)
  have hj : j = k + (t + 1) := by
    -- Normalize a strict successor index `j` into the canonical gap form over stage `k`.
    calc
      j = (k + 1) + (j - (k + 1)) := (Nat.add_sub_of_le hkSuccLe).symm
      _ = k + (t + 1) := by
        simp [t, Nat.add_assoc, Nat.add_comm]
  -- The normalized later stage lies in the gap family already excluded by `hgap`.
  rw [hj]
  exact hgap t

/-- If the `k`th reached stage does not terminate, then the next iterate is updated to the
selected stage-`k` minimizer `x(σ_k)`. -/
theorem iterate_update_eq
    (method : SimplePenaltyFunctionMethod n m) {k : ℕ} (hk : 1 ≤ k)
    (hreached : method.reached k) (hactive : ¬ method.terminatedAt k) :
    method.iterate (k + 1) = method.subproblemSolution k := by
  rcases method.stop_or_step k hk hreached with hterm | hstep
  · exact (False.elim <| hactive hterm)
  · exact hstep.1

/-- If the `k`th reached stage does not terminate, then the next penalty parameter is
multiplied by `10`, so `σ_(k+1) = 10 * σ_k`. -/
theorem penaltyParameter_update_eq
    (method : SimplePenaltyFunctionMethod n m) {k : ℕ} (hk : 1 ≤ k)
    (hreached : method.reached k) (hactive : ¬ method.terminatedAt k) :
    method.penaltyParameter (k + 1) = 10 * method.penaltyParameter k := by
  rcases method.stop_or_step k hk hreached with hterm | hstep
  · exact (False.elim <| hactive hterm)
  · exact hstep.2

end SimplePenaltyFunctionMethod

end
