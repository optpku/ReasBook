/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Basic

noncomputable section

section

open Matrix

variable {ambientDim constraintDim : ℕ}

local notation "Point" => EuclideanSpace ℝ (Fin ambientDim)
local notation "ConstraintPoint" => EuclideanSpace ℝ (Fin constraintDim)
local notation "ConstraintMatrix" => Matrix (Fin ambientDim) (Fin constraintDim) ℝ

-- Semantic recall: `lean_leansearch` did not surface a canonical mathlib owner for this
-- quartering line-search loop. Following nearby Chapter 11 algorithm files, the public surface
-- keeps the stagewise trial map `x_k(α)`, the Step `(11.5.13)` acceptance predicate, and the
-- accepted quartering count explicit.

/-- The feasible set of the equality-constrained system `Aᵀ x = b`. -/
def linearlyConstrainedFeasibleSet (A : ConstraintMatrix) (b : ConstraintPoint) : Set Point :=
  {x | Aᵀ *ᵥ x = b}

/-- Membership in `linearlyConstrainedFeasibleSet A b` is exactly the equation `Aᵀ x = b`. -/
theorem mem_linearlyConstrainedFeasibleSet_iff
    (A : ConstraintMatrix) (b : ConstraintPoint) (x : Point) :
    x ∈ linearlyConstrainedFeasibleSet A b ↔ Aᵀ *ᵥ x = b :=
  Iff.rfl

/-- The Step-2 trial seed `max {2 * α_(k-1), γ}` in Algorithm 11.5.2. -/
def linearlyConstrainedQuarteringTrialSeed (γ αPrev : ℝ) : ℝ :=
  max (2 * αPrev) γ

/-- Unfolding `linearlyConstrainedQuarteringTrialSeed γ αPrev` recovers the Step-2 formula
`max {2 * α_(k-1), γ}`. -/
theorem linearlyConstrainedQuarteringTrialSeed_eq
    (γ αPrev : ℝ) :
    linearlyConstrainedQuarteringTrialSeed γ αPrev = max (2 * αPrev) γ :=
  rfl

/-- After `m` executions of Step 3, the current trial step is the Step-2 seed divided by `4^m`. -/
def linearlyConstrainedQuarteringTrialStep (γ αPrev : ℝ) (m : ℕ) : ℝ :=
  linearlyConstrainedQuarteringTrialSeed γ αPrev / (4 : ℝ) ^ m

/-- Unfolding `linearlyConstrainedQuarteringTrialStep γ αPrev m` gives the Step-3 quartering
formula. -/
theorem linearlyConstrainedQuarteringTrialStep_eq
    (γ αPrev : ℝ) (m : ℕ) :
    linearlyConstrainedQuarteringTrialStep γ αPrev m =
      linearlyConstrainedQuarteringTrialSeed γ αPrev / (4 : ℝ) ^ m :=
  rfl

/-- `IsLinearlyConstrainedQuarteringAcceptedStep accepts γ αPrev α m` means that `α` is the
step accepted at a given stage of Algorithm 11.5.2: it is obtained from the Step-2 seed
`max {2 * α_(k-1), γ}` after exactly `m` quartering updates from Step 3, satisfies the source
acceptance test `(11.5.13)`, and every earlier trial step is rejected. -/
def IsLinearlyConstrainedQuarteringAcceptedStep
    (accepts : ℝ → Prop) (γ αPrev α : ℝ) (m : ℕ) : Prop :=
  α = linearlyConstrainedQuarteringTrialStep γ αPrev m ∧
    accepts α ∧
    ∀ j : ℕ, j < m → ¬ accepts (linearlyConstrainedQuarteringTrialStep γ αPrev j)

/-- Unfolding `IsLinearlyConstrainedQuarteringAcceptedStep` gives the Step-3 acceptance and
minimality conditions. -/
theorem isLinearlyConstrainedQuarteringAcceptedStep_iff
    (accepts : ℝ → Prop) (γ αPrev α : ℝ) (m : ℕ) :
    IsLinearlyConstrainedQuarteringAcceptedStep accepts γ αPrev α m ↔
      α = linearlyConstrainedQuarteringTrialStep γ αPrev m ∧
        accepts α ∧
        ∀ j : ℕ, j < m → ¬ accepts (linearlyConstrainedQuarteringTrialStep γ αPrev j) :=
  Iff.rfl

/-- Chapter11 Algorithm 11.5.2: for the linear equality-constrained feasible set
`linearlyConstrainedFeasibleSet constraintMatrix constraintTarget`, a feasible initial point
`x₁ ∈ linearlyConstrainedFeasibleSet constraintMatrix constraintTarget`, parameters
`μ ∈ (0, 1)` and `γ > 0`, stagewise trial paths `x_k(α)` based at the current iterate via
`x_k(0) = x_k`, and a stagewise acceptance predicate encoding condition `(11.5.13)` as a
condition on `μ`, the trial step `α`, and the trial point `x_k(α)`, the algorithm fixes
`α₀ = 1`. At each stage `k ≥ 1`, Step 2 forms the trial seed `max {2 * α_(k-1), γ}`, Step 3
repeatedly divides it by `4` until `(11.5.13)` holds, and Step 4 sets
`x_(k + 1) = x_k(α_k)`. -/
structure LinearlyConstrainedQuarteringSearchMethod (ambientDim constraintDim : ℕ) where
  constraintMatrix : Matrix (Fin ambientDim) (Fin constraintDim) ℝ
  constraintTarget : EuclideanSpace ℝ (Fin constraintDim)
  μ : ℝ
  γ : ℝ
  initialPoint : EuclideanSpace ℝ (Fin ambientDim)
  trialPoint : ℕ → ℝ → EuclideanSpace ℝ (Fin ambientDim)
  accepts : ℝ → ℕ → ℝ → EuclideanSpace ℝ (Fin ambientDim) → Prop
  iterate : ℕ → EuclideanSpace ℝ (Fin ambientDim)
  stepSize : ℕ → ℝ
  quarteringCount : ℕ → ℕ
  mu_mem : μ ∈ Set.Ioo (0 : ℝ) 1
  gamma_pos : 0 < γ
  initialPoint_mem :
    initialPoint ∈ linearlyConstrainedFeasibleSet constraintMatrix constraintTarget
  iterate_one : iterate 1 = initialPoint
  trialPoint_zero :
    ∀ k, 1 ≤ k → trialPoint k 0 = iterate k
  step_zero : stepSize 0 = 1
  step_spec :
    ∀ k, 1 ≤ k →
      IsLinearlyConstrainedQuarteringAcceptedStep
        (fun α ↦ accepts μ k α (trialPoint k α))
        γ
        (stepSize (k - 1))
        (stepSize k)
        (quarteringCount k)
  iterate_succ :
    ∀ k, 1 ≤ k →
      iterate (k + 1) = trialPoint k (stepSize k)

namespace LinearlyConstrainedQuarteringSearchMethod

variable {ambientDim constraintDim : ℕ}

/-- A linearly constrained quartering search method can be evaluated at stage `k` as its
iterate `x_k`. -/
instance :
    CoeFun (LinearlyConstrainedQuarteringSearchMethod ambientDim constraintDim)
      (fun _ ↦ ℕ → EuclideanSpace ℝ (Fin ambientDim)) where
  coe method := method.iterate

/-- Evaluating `method` as a function returns its iterate sequence. -/
theorem coe_apply
    (method : LinearlyConstrainedQuarteringSearchMethod ambientDim constraintDim) (k : ℕ) :
    method k = method.iterate k :=
  rfl

/-- The Step-3 acceptance condition `(11.5.13)` at stage `k`, specialized to the method
parameter `μ`, evaluated on a trial step `α` and a point `x`. -/
def acceptsAt
    (method : LinearlyConstrainedQuarteringSearchMethod ambientDim constraintDim)
    (k : ℕ) (α : ℝ) (x : EuclideanSpace ℝ (Fin ambientDim)) : Prop :=
  method.accepts method.μ k α x

/-- Unfolding `method.acceptsAt k α x` recovers the source Step-3 acceptance test `(11.5.13)`
evaluated at `μ`, `α`, and `x`. -/
theorem acceptsAt_iff
    (method : LinearlyConstrainedQuarteringSearchMethod ambientDim constraintDim)
    (k : ℕ) (α : ℝ) (x : EuclideanSpace ℝ (Fin ambientDim)) :
    method.acceptsAt k α x ↔ method.accepts method.μ k α x :=
  Iff.rfl

/-- The Step-3 acceptance test at stage `k`, specialized to the parameter `μ` and the trial path
`x_k(α)`. -/
def acceptedAt
    (method : LinearlyConstrainedQuarteringSearchMethod ambientDim constraintDim)
    (k : ℕ) (α : ℝ) : Prop :=
  method.acceptsAt k α (method.trialPoint k α)

/-- Unfolding `method.acceptedAt k α` shows that it is exactly the trial-path specialization of
`method.acceptsAt k`. -/
theorem acceptedAt_iff_acceptsAt
    (method : LinearlyConstrainedQuarteringSearchMethod ambientDim constraintDim)
    (k : ℕ) (α : ℝ) :
    method.acceptedAt k α ↔ method.acceptsAt k α (method.trialPoint k α) :=
  Iff.rfl

/-- Unfolding `method.acceptedAt k α` recovers the source Step-3 acceptance test `(11.5.13)`
evaluated at `μ`, `α`, and `x_k(α)`. -/
theorem acceptedAt_iff
    (method : LinearlyConstrainedQuarteringSearchMethod ambientDim constraintDim)
    (k : ℕ) (α : ℝ) :
    method.acceptedAt k α ↔
      method.accepts method.μ k α (method.trialPoint k α) :=
  by simp [acceptedAt, acceptsAt]

/-- The Step-2 trial seed used at stage `k`. -/
def trialSeedAt
    (method : LinearlyConstrainedQuarteringSearchMethod ambientDim constraintDim)
    (k : ℕ) : ℝ :=
  linearlyConstrainedQuarteringTrialSeed method.γ (method.stepSize (k - 1))

/-- Unfolding `method.trialSeedAt k` gives `max {2 * α_(k-1), γ}`. -/
theorem trialSeedAt_eq
    (method : LinearlyConstrainedQuarteringSearchMethod ambientDim constraintDim)
    (k : ℕ) :
    method.trialSeedAt k =
      linearlyConstrainedQuarteringTrialSeed method.γ (method.stepSize (k - 1)) :=
  rfl

/-- The Step-3 trial step obtained after `j` quartering updates at stage `k`. -/
def trialStepAt
    (method : LinearlyConstrainedQuarteringSearchMethod ambientDim constraintDim)
    (k j : ℕ) : ℝ :=
  linearlyConstrainedQuarteringTrialStep method.γ (method.stepSize (k - 1)) j

/-- Unfolding `method.trialStepAt k j` gives the quartered Step-2 seed used at stage `k`. -/
theorem trialStepAt_eq
    (method : LinearlyConstrainedQuarteringSearchMethod ambientDim constraintDim)
    (k j : ℕ) :
    method.trialStepAt k j =
      linearlyConstrainedQuarteringTrialStep method.γ (method.stepSize (k - 1)) j :=
  rfl

/-- The feasible set recorded by `method` is the equality-constrained set `Aᵀ x = b`. -/
def feasibleSet
    (method : LinearlyConstrainedQuarteringSearchMethod ambientDim constraintDim) :
    Set (EuclideanSpace ℝ (Fin ambientDim)) :=
  linearlyConstrainedFeasibleSet method.constraintMatrix method.constraintTarget

/-- Unfolding `method.feasibleSet` recovers the equality-constrained feasible set of `method`. -/
theorem feasibleSet_eq
    (method : LinearlyConstrainedQuarteringSearchMethod ambientDim constraintDim) :
    method.feasibleSet =
      linearlyConstrainedFeasibleSet method.constraintMatrix method.constraintTarget :=
  rfl

/-- Membership in `method.feasibleSet` is exactly the equality constraint system recorded by
`method`. -/
theorem mem_feasibleSet_iff
    (method : LinearlyConstrainedQuarteringSearchMethod ambientDim constraintDim)
    (x : EuclideanSpace ℝ (Fin ambientDim)) :
    x ∈ method.feasibleSet ↔
      method.constraintMatrixᵀ *ᵥ x = method.constraintTarget := by
  simpa [feasibleSet] using
    mem_linearlyConstrainedFeasibleSet_iff method.constraintMatrix method.constraintTarget x

/-- The initial point recorded by `method` is feasible for the equality-constrained feasible set
of `method`. -/
theorem initialPoint_mem_feasibleSet
    (method : LinearlyConstrainedQuarteringSearchMethod ambientDim constraintDim) :
    method.initialPoint ∈ method.feasibleSet := by
  simpa [feasibleSet] using method.initialPoint_mem

/-- The first iterate of `method` is the given feasible starting point `x₁`. -/
theorem iterate_one_eq_initialPoint
    (method : LinearlyConstrainedQuarteringSearchMethod ambientDim constraintDim) :
    method.iterate 1 = method.initialPoint :=
  method.iterate_one

/-- At every stage `k ≥ 1`, the trial path for stage `k` starts from the current iterate
`x_k(0) = x_k`. -/
theorem trialPoint_zero_eq_iterate
    (method : LinearlyConstrainedQuarteringSearchMethod ambientDim constraintDim)
    {k : ℕ} (hk : 1 ≤ k) :
    method.trialPoint k 0 = method.iterate k :=
  method.trialPoint_zero k hk

/-- At every stage `k ≥ 1`, the recorded step data is exactly the source Step-3 accepted-step
bundle specialized to `method.acceptedAt k`. -/
theorem acceptedStep_spec
    (method : LinearlyConstrainedQuarteringSearchMethod ambientDim constraintDim)
    {k : ℕ} (hk : 1 ≤ k) :
    IsLinearlyConstrainedQuarteringAcceptedStep
      (method.acceptedAt k)
      method.γ
      (method.stepSize (k - 1))
      (method.stepSize k)
      (method.quarteringCount k) := by
  change IsLinearlyConstrainedQuarteringAcceptedStep
    (fun α ↦ method.acceptedAt k α)
    method.γ
    (method.stepSize (k - 1))
    (method.stepSize k)
    (method.quarteringCount k)
  simpa [acceptedAt, acceptsAt] using method.step_spec k hk

/-- At every stage `k ≥ 1`, the recorded step size is the Step-2 seed divided by `4` exactly
`quarteringCount k` times. -/
theorem stepSize_eq_trialStep
    (method : LinearlyConstrainedQuarteringSearchMethod ambientDim constraintDim)
    {k : ℕ} (hk : 1 ≤ k) :
    method.stepSize k = method.trialStepAt k (method.quarteringCount k) := by
  simpa [trialStepAt] using (method.acceptedStep_spec hk).1

/-- At every stage `k ≥ 1`, the recorded step size satisfies the source Step-3 acceptance test
`(11.5.13)`. -/
theorem stepSize_accepted
    (method : LinearlyConstrainedQuarteringSearchMethod ambientDim constraintDim)
    {k : ℕ} (hk : 1 ≤ k) :
    method.acceptedAt k (method.stepSize k) :=
  (method.acceptedStep_spec hk).2.1

/-- At every stage `k ≥ 1`, all earlier quartered trial steps are rejected before the recorded
accepted step `α_k`. -/
theorem minimal_quarteringCount
    (method : LinearlyConstrainedQuarteringSearchMethod ambientDim constraintDim) {k j : ℕ}
    (hk : 1 ≤ k) (hj : j < method.quarteringCount k) :
    ¬ method.acceptedAt k (method.trialStepAt k j) := by
  simpa [trialStepAt] using (method.acceptedStep_spec hk).2.2 j hj

/-- At every stage `k ≥ 1`, Step 4 updates the iterate by the source trial path value
`x_k(α_k)`. -/
theorem iterate_succ_eq_trialPoint
    (method : LinearlyConstrainedQuarteringSearchMethod ambientDim constraintDim)
    {k : ℕ} (hk : 1 ≤ k) :
    method.iterate (k + 1) = method.trialPoint k (method.stepSize k) :=
  method.iterate_succ k hk

end LinearlyConstrainedQuarteringSearchMethod

#print axioms linearlyConstrainedQuarteringTrialSeed
#print axioms linearlyConstrainedQuarteringTrialStep
#print axioms linearlyConstrainedFeasibleSet

end
