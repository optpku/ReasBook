/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import OptimizationTheoryAndMethods_SunYuan_2006.Chap10.Algorithm_10_4_1

open Filter

noncomputable section

variable {n m : ℕ}

namespace AugmentedLagrangianMethod

/-- An augmented Lagrangian method finitely terminates when some reached stage `k ≥ 1` satisfies
the source stopping test `‖c⁽-⁾(x_(k+1))‖∞ ≤ ε`. -/
def finitelyTerminates (method : AugmentedLagrangianMethod n m) : Prop :=
  ∃ k : ℕ, 1 ≤ k ∧ method.terminatedAt k

/-- Unfolding `method.finitelyTerminates` gives the existence of a reached terminating stage. -/
theorem finitelyTerminates_iff (method : AugmentedLagrangianMethod n m) :
    method.finitelyTerminates ↔ ∃ k : ℕ, 1 ≤ k ∧ method.terminatedAt k :=
  Iff.rfl

/-- The stage-`k` objective value of an augmented Lagrangian method is the source quantity
`f(x_k)`. -/
def objectiveValueAt (method : AugmentedLagrangianMethod n m) (k : ℕ) : ℝ :=
  method.problem.objective (method.iterate k)

/-- Evaluating `method.objectiveValueAt k` expands to the source objective value `f(x_k)`. -/
theorem objectiveValueAt_eq (method : AugmentedLagrangianMethod n m) (k : ℕ) :
    method.objectiveValueAt k = method.problem.objective (method.iterate k) :=
  rfl

/-- The source alternative `liminf_{k → ∞} f(x_k) = -∞` is encoded by saying that for every real
threshold `r`, the objective-value sequence `f(x_k)` lies below `r` frequently along `atTop`. -/
def objectiveFrequentlyBelowEveryReal (method : AugmentedLagrangianMethod n m) : Prop :=
  ∀ r : ℝ, ∃ᶠ k : ℕ in atTop, method.objectiveValueAt k < r

/-- Unfolding `method.objectiveFrequentlyBelowEveryReal` gives the direct filter encoding of the
source `liminf_{k → ∞} f(x_k) = -∞` conclusion. -/
theorem objectiveFrequentlyBelowEveryReal_iff (method : AugmentedLagrangianMethod n m) :
    method.objectiveFrequentlyBelowEveryReal ↔
      ∀ r : ℝ, ∃ᶠ k : ℕ in atTop, method.objectiveValueAt k < r :=
  Iff.rfl

/-- A recorded method is a run of `problem` with tolerance `ε` when its stored problem and
tolerance fields are exactly those source parameters. -/
def isRunOf
    (method : AugmentedLagrangianMethod n m) (problem : StandardPenaltyProblem n m)
    (ε : ℝ) : Prop :=
  method.problem = problem ∧ method.tolerance = ε

/-- Unfolding `method.isRunOf problem ε` gives the source equalities fixing the problem and
tolerance of the recorded run. -/
theorem isRunOf_iff
    (method : AugmentedLagrangianMethod n m) (problem : StandardPenaltyProblem n m)
    (ε : ℝ) :
    method.isRunOf problem ε ↔ method.problem = problem ∧ method.tolerance = ε :=
  Iff.rfl

/-- The run-level alternative in Chapter10 Theorem 10.4.2: a recorded Algorithm 10.4.1 run has
the source theorem's fixed problem and tolerance, and is either finitely terminated or has
objective values whose liminf is `-∞`. -/
def finiteTerminationOrObjectiveLiminfBot
    (method : AugmentedLagrangianMethod n m) (problem : StandardPenaltyProblem n m)
    (ε : ℝ) : Prop :=
  method.isRunOf problem ε ∧
    (method.finitelyTerminates ∨ method.objectiveFrequentlyBelowEveryReal)

/-- Unfolding `method.finiteTerminationOrObjectiveLiminfBot problem ε` recovers the direct
source-level run statement used in Chapter10 Theorem 10.4.2. -/
theorem finiteTerminationOrObjectiveLiminfBot_iff
    (method : AugmentedLagrangianMethod n m) (problem : StandardPenaltyProblem n m)
    (ε : ℝ) :
    method.finiteTerminationOrObjectiveLiminfBot problem ε ↔
      method.isRunOf problem ε ∧
        (method.finitelyTerminates ∨ method.objectiveFrequentlyBelowEveryReal) :=
  Iff.rfl

end AugmentedLagrangianMethod
