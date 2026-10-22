/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import OptimizationTheoryAndMethods_SunYuan_2006.Chap10.Definition_10_3_extra_1

noncomputable section

section

-- Domain sampling:
-- * `InteriorPointPenaltyProblem` in `Definition_10_3_extra_1` is the Chapter 10 owner for the
--   objective, constraints, strict-feasible region, barrier sum, and penalty function.
-- * `IsMinOn` remains the canonical mathlib minimizer surface for the stage subproblems.
-- * nearby Chapter 10 method declarations use binder-first stage fields over generic ambient
--   owners rather than coordinate-specific wrappers.
-- This algorithm is therefore kept at the source-facing method layer, but its penalty-problem
-- API is reused through the inherited owner instead of duplicated locally.

variable {Point : Type*} {ι : Type*} [Fintype ι]

/-- Chapter10 Algorithm 10.3.3: an algorithm based on the interior point penalty function
extends the Chapter 10 interior-point penalty problem on a decision space `Point` with finitely
many inequality constraints indexed by `ι` by recording a tolerance `ε ≥ 0`, an initial strictly
feasible point `x₁` satisfying the source side condition `(10.3.15)`, an initial barrier
parameter `σ₁ > 0`, and for each active stage `k ≥ 1` the current iterate `x_k`, the barrier
parameter `σ_k`, and a selected solution `x(σ_k)` of the interior-point penalty subproblem.
Step 2 is represented by requiring that, at each active stage, `x(σ_k)` minimizes
`method.toInteriorPointPenaltyProblem.penaltyFunction (σ_k)` on
`method.toInteriorPointPenaltyProblem.strictFeasibleSet` and that `x_(k+1) = x(σ_k)`. Step 3 is
represented by a recursive activity predicate: the stage `k + 1` is active exactly when stage
`k` is active and the source stopping inequality
`(1 / σ_k) * ∑ i, h (cᵢ(x_(k+1))) ≤ ε` fails, and whenever the algorithm continues it updates
`σ_(k+1) = 10 * σ_k`. -/
structure InteriorPointPenaltyFunctionMethod (Point : Type*) (ι : Type*) [Fintype ι]
    extends InteriorPointPenaltyProblem Point ι where
  tolerance : ℝ
  toleranceNonneg : 0 ≤ tolerance
  initialPoint : Point
  initialPoint_mem_strictFeasibleSet :
    initialPoint ∈ toInteriorPointPenaltyProblem.strictFeasibleSet
  initialPenaltyParameter : ℝ
  initialPenaltyParameterPos : 0 < initialPenaltyParameter
  active : ℕ → Prop
  iterate : ℕ → Point
  penaltyParameter : ℕ → ℝ
  subproblemSolution : ℕ → Point
  active_one : active 1
  iterate_one : iterate 1 = initialPoint
  penaltyParameter_one : penaltyParameter 1 = initialPenaltyParameter
  subproblemSolution_spec (k : ℕ) (_ : 1 ≤ k) (_ : active k) :
    IsMinOn
      (toInteriorPointPenaltyProblem.penaltyFunction (penaltyParameter k))
      toInteriorPointPenaltyProblem.strictFeasibleSet
      (subproblemSolution k)
  iterate_succ (k : ℕ) (_ : 1 ≤ k) (_ : active k) :
    iterate (k + 1) = subproblemSolution k
  active_succ_iff (k : ℕ) (_ : 1 ≤ k) :
    active (k + 1) ↔
      active k ∧
        ¬ ((1 / penaltyParameter k) *
              toInteriorPointPenaltyProblem.barrierSum (iterate (k + 1)) ≤
            tolerance)
  penaltyParameter_update (k : ℕ) (_ : 1 ≤ k) (_ : active k) (_ : active (k + 1)) :
    penaltyParameter (k + 1) = 10 * penaltyParameter k

namespace InteriorPointPenaltyFunctionMethod

/-- The stage-`k` scaled barrier budget is the source expression
`(1 / σ_k) * ∑ i, h (cᵢ(x_(k+1)))`. -/
def barrierBudgetAt (method : InteriorPointPenaltyFunctionMethod Point ι) (k : ℕ) : ℝ :=
  (1 / method.penaltyParameter k) *
    method.toInteriorPointPenaltyProblem.barrierSum (method.iterate (k + 1))

/-- Evaluating `method.barrierBudgetAt k` expands to the source scaled barrier budget
`(1 / σ_k) * ∑ i, h (cᵢ(x_(k+1)))`. -/
theorem barrierBudgetAt_eq
    (method : InteriorPointPenaltyFunctionMethod Point ι) (k : ℕ) :
    method.barrierBudgetAt k =
      (1 / method.penaltyParameter k) *
        method.toInteriorPointPenaltyProblem.barrierSum (method.iterate (k + 1)) :=
  rfl

/-- The `k`th stage of an interior point penalty function method terminates exactly when the
source stopping test `(1 / σ_k) * ∑ i, h (cᵢ(x_(k+1))) ≤ ε` holds on the recorded next
iterate `x_(k+1)`. -/
def terminatedAt (method : InteriorPointPenaltyFunctionMethod Point ι) (k : ℕ) : Prop :=
  method.barrierBudgetAt k ≤ method.tolerance

/-- Unfolding `method.terminatedAt k` in terms of the stage barrier budget gives the inequality
`method.barrierBudgetAt k ≤ ε`. -/
theorem terminatedAt_iff_barrierBudgetAt_le
    (method : InteriorPointPenaltyFunctionMethod Point ι) (k : ℕ) :
    method.terminatedAt k ↔ method.barrierBudgetAt k ≤ method.tolerance :=
  Iff.rfl

/-- Unfolding `method.terminatedAt k` gives the source stopping inequality at stage `k`. -/
theorem terminatedAt_iff (method : InteriorPointPenaltyFunctionMethod Point ι) (k : ℕ) :
    method.terminatedAt k ↔
      (1 / method.penaltyParameter k) *
          method.toInteriorPointPenaltyProblem.barrierSum (method.iterate (k + 1)) ≤
        method.tolerance := by
  rw [terminatedAt_iff_barrierBudgetAt_le, barrierBudgetAt_eq]

/-- If the `k`th stage is active, then Algorithm 10.3.3 continues to stage `k + 1` exactly
when the source stopping test fails at stage `k`. -/
theorem active_succ_iff_not_terminatedAt
    (method : InteriorPointPenaltyFunctionMethod Point ι) {k : ℕ} (hk : 1 ≤ k)
    (hactive : method.active k) :
    method.active (k + 1) ↔ ¬ method.terminatedAt k := by
  simpa [terminatedAt, barrierBudgetAt, hactive] using method.active_succ_iff k hk

/-- Any active stage `k + 1` of Algorithm 10.3.3 must come from an active previous stage `k`;
later stages cannot reappear after the algorithm has terminated. -/
theorem active_of_active_succ
    (method : InteriorPointPenaltyFunctionMethod Point ι) {k : ℕ} (hk : 1 ≤ k)
    (hactive_succ : method.active (k + 1)) :
    method.active k :=
  (method.active_succ_iff k hk).1 hactive_succ |>.1

/-- For each book stage `k ≥ 1`, Step 2 sets the next iterate `x_(k+1)` equal to the selected
subproblem solution `x(σ_k)`. -/
theorem iterate_succ_eq_subproblemSolution
    (method : InteriorPointPenaltyFunctionMethod Point ι) {k : ℕ} (hk : 1 ≤ k)
    (hactive : method.active k) :
    method.iterate (k + 1) = method.subproblemSolution k :=
  method.iterate_succ k hk hactive

/-- The recorded stage-`k` subproblem solution minimizes the canonical Chapter 10 interior-point
penalty objective on the strict feasible region. -/
theorem subproblemSolution_isMinimizer
    (method : InteriorPointPenaltyFunctionMethod Point ι) {k : ℕ} (hk : 1 ≤ k)
    (hactive : method.active k) :
    IsMinOn
      (method.toInteriorPointPenaltyProblem.penaltyFunction (method.penaltyParameter k))
      method.toInteriorPointPenaltyProblem.strictFeasibleSet
      (method.subproblemSolution k) :=
  method.subproblemSolution_spec k hk hactive

/-- If the `k`th stage does not terminate, then Step 3 updates the penalty parameter by the
source rule `σ_(k+1) = 10 * σ_k`. -/
theorem penaltyParameter_update_eq
    (method : InteriorPointPenaltyFunctionMethod Point ι) {k : ℕ} (hk : 1 ≤ k)
    (hactive : method.active k)
    (hstop : ¬ method.terminatedAt k) :
    method.penaltyParameter (k + 1) = 10 * method.penaltyParameter k := by
  exact method.penaltyParameter_update k hk hactive <|
    (method.active_succ_iff_not_terminatedAt hk hactive).2 hstop

end InteriorPointPenaltyFunctionMethod

end
