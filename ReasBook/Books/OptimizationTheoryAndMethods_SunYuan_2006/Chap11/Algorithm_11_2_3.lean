/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Basic
import Mathlib.LinearAlgebra.Matrix.ToLin
import OptimizationTheoryAndMethods_SunYuan_2006.Chap11.Algorithm_11_2_1
import OptimizationTheoryAndMethods_SunYuan_2006.Chap11.Definition_11_2_extra_2

noncomputable section

section Chapter11Algorithm1123

open GeneralizedEliminationMethod

variable {n m : ℕ}

local notation "Point" => EuclideanSpace ℝ (Fin n)
local notation "BasicPoint" => EuclideanSpace ℝ (Fin m)
local notation "NonbasicPoint" => EuclideanSpace ℝ (Fin (n - m))
local notation "ConstraintPoint" => EuclideanSpace ℝ (Fin m)
local notation "Elimination" => @_root_.GeneralizedEliminationMethod n m

-- Domain sampling:
-- * source-facing owner: `GeneralEliminationMethod`, whose primitive recursive families are the
--   stagewise generalized-elimination owners `M_k`, nonbasic variables `(w_k)_N`, multipliers
--   `λ_k`, directions `d̄_k`, and step sizes `α_k`.
-- * core/canonical owners: `GeneralizedEliminationMethod` for the elimination geometry and
--   `FeasiblePointExactLineSearch` for the reduced-space exact line search.
-- * bridge layer: `GeneralizedEliminationMethod.graphPoint` together with the Chapter 11
--   variable-elimination owner `variableEliminationReducedFeasibleSet`.

namespace GeneralizedEliminationMethod

/-- The reduced feasible set on nonbasic variables induced by `X` and a generalized-elimination
owner `M`. -/
abbrev reducedFeasibleSet
    (M : Elimination) (X : Set Point) : Set NonbasicPoint :=
  variableEliminationReducedFeasibleSet
    {p : BasicPoint × NonbasicPoint | M.point p.1 p.2 ∈ X}
    M

/-- Membership in `M.reducedFeasibleSet X` means that the elimination-graph point stays in `X`.
-/
@[simp] theorem mem_reducedFeasibleSet_iff
    (M : Elimination) (X : Set Point) (wN : NonbasicPoint) :
    wN ∈ M.reducedFeasibleSet X ↔ M.graphPoint wN ∈ X := by
  simp [GeneralizedEliminationMethod.reducedFeasibleSet,
    GeneralizedEliminationMethod.graphPoint]

end GeneralizedEliminationMethod

/-- `GeneralEliminationStageValid objective feasibleSet M wN λ` says that the stagewise
primitive data `(M, w_N, λ)` form a valid active stage of Algorithm 11.2.3: the
elimination-graph point `S_B (φ̄ w_N) + S_N w_N` lies in `X`, and the Step 2 differentiability,
nonsingularity, and multiplier-equation hypotheses from `(11.2.32)`-`(11.2.33)` hold for the
canonical generalized-elimination owner `M` itself. -/
structure GeneralEliminationStageValid
    (objective : Point → ℝ) (feasibleSet : Set Point) (M : Elimination)
    (wN : NonbasicPoint) (lam : ConstraintPoint) : Prop where
  mem_feasibleSet : M.graphPoint wN ∈ feasibleSet
  phiBar_differentiable :
    DifferentiableAt ℝ M.phiBar wN
  objective_differentiable :
    DifferentiableAt ℝ objective (M.graphPoint wN)
  constraint_differentiable :
    DifferentiableAt ℝ M.constraint (M.graphPoint wN)
  basicConstraintBlock_nonsingular :
    IsUnit
      (M.basicBlock.transpose *
        (generalizedEliminationConstraintJacobian
          M.constraint
          (M.graphPoint wN)).transpose)
  multiplierEquation :
    M.multiplierEquation objective wN lam

/-- Chapter11 Algorithm 11.2.3: the general elimination method is the source-facing recursive
algorithm built from a fixed ambient objective `f`, a fixed equality-constraint map `c`, a
feasible set `X`, a tolerance `ε ≥ 0`, initial Step 2 data `(M₁, (w₁)_N, λ₁)`, and the
recursive families `M_k`, `(w_k)_N`, `λ_k`, `d̄_k`, and `α_k`. The current iterate
`x_k = S_B φ̄_k ((w_k)_N) + S_N (w_k)_N` and the current reduced gradient `ḡ_k` are derived.
Continuing stages are governed by the source stopping test `ε < ‖ḡ_k‖`, each continuing stage
uses a feasible descent direction for the reduced objective on the reduced feasible set determined
by `M_k`, the chosen step size satisfies the canonical exact reduced-space line search on that
reduced-space bridge,
and the next stage is required to realize the Step 4 trial point
`S_B φ̄_k ((w_k)_N + α_k d̄_k) + S_N ((w_k)_N + α_k d̄_k)`. -/
structure GeneralEliminationMethod where
  objective : Point → ℝ
  constraint : Point → ConstraintPoint
  feasibleSet : Set Point
  tolerance : ℝ
  initialElimination : Elimination
  initialReducedVariable : NonbasicPoint
  initialMultiplier : ConstraintPoint
  active : ℕ → Prop
  elimination : ℕ → Elimination
  reducedVariable : ℕ → NonbasicPoint
  multiplier : ℕ → ConstraintPoint
  direction : ℕ → NonbasicPoint
  stepSize : ℕ → ℝ
  tolerance_nonneg : 0 ≤ tolerance
  active_one : active 1
  elimination_one : elimination 1 = initialElimination
  reducedVariable_one : reducedVariable 1 = initialReducedVariable
  multiplier_one : multiplier 1 = initialMultiplier
  /-- Every feasible point `x ∈ X` satisfies the equality constraint equation `c x = 0`. -/
  feasibleSet_constraint_eq_zero :
    ∀ {x : Point}, x ∈ feasibleSet → constraint x = 0
  elimination_constraint :
    ∀ k, 1 ≤ k → active k → (elimination k).constraint = constraint
  stage_spec :
    ∀ k, 1 ≤ k → active k →
      GeneralEliminationStageValid
        objective
        feasibleSet
        (elimination k)
        (reducedVariable k)
        (multiplier k)
  active_succ_iff (k : ℕ) (hk : 1 ≤ k) :
    active (k + 1) ↔
      active k ∧
        tolerance <
          ‖(elimination k).reducedGradient objective (reducedVariable k)‖
  direction_spec :
    ∀ k, 1 ≤ k → active (k + 1) →
      IsFeasibleDescentDirection
        ((elimination k).reducedObjective objective)
        (reducedVariable k)
        ((elimination k).reducedFeasibleSet feasibleSet)
        (direction k)
  stepSize_spec :
    ∀ k, 1 ≤ k → active (k + 1) →
      FeasiblePointExactLineSearch
        ((elimination k).reducedObjective objective)
        ((elimination k).reducedFeasibleSet feasibleSet)
        (reducedVariable k)
        (direction k)
        (stepSize k)
  iterate_succ_eq_trialPoint_spec :
    ∀ k, 1 ≤ k → active (k + 1) →
      (elimination (k + 1)).graphPoint (reducedVariable (k + 1)) =
        (elimination k).graphPoint
          (reducedVariable k + stepSize k • direction k)

namespace GeneralEliminationMethod

local notation "Method" => @_root_.GeneralEliminationMethod n m

/-- The current ambient iterate
`x_k = S_B φ̄_k ((w_k)_N) + S_N (w_k)_N`. -/
def iterate (method : Method) (k : ℕ) : Point :=
  (method.elimination k).graphPoint (method.reducedVariable k)

/-- `method` can be evaluated as its iterate sequence `x_k`. -/
instance : CoeFun Method (fun _ ↦ ℕ → Point) where
  coe method := method.iterate

/-- Evaluating `method` as a function returns its iterate sequence. -/
theorem coe_apply
    (method : Method) (k : ℕ) :
    method k = method.iterate k :=
  rfl

/-- The recorded initial point `x₁`. -/
def initialPoint (method : Method) : Point :=
  method.initialElimination.graphPoint method.initialReducedVariable

/-- The reduced gradient `ḡ_k` computed in Step 2 from the current generalized-elimination
owner `M_k`. -/
abbrev currentReducedGradient
    (method : Method) (k : ℕ) : NonbasicPoint :=
  (method.elimination k).reducedGradient method.objective (method.reducedVariable k)

/-- The continuing-stage nonbasic update `(w_k)_N + α_k d̄_k`. -/
def nextReducedVariable
    (method : Method) (k : ℕ) : NonbasicPoint :=
  method.reducedVariable k + method.stepSize k • method.direction k

/-- The Step 4 trial point
`S_B φ̄_k ((w_k)_N + α_k d̄_k) + S_N ((w_k)_N + α_k d̄_k)`. -/
def trialPoint
    (method : Method) (k : ℕ) : Point :=
  (method.elimination k).graphPoint (method.nextReducedVariable k)

/-- The current reduced feasible set on nonbasic variables induced by `X` and `M_k`. -/
abbrev stageReducedFeasibleSet
    (method : Method) (k : ℕ) : Set NonbasicPoint :=
  (method.elimination k).reducedFeasibleSet method.feasibleSet

/-- The positive reduced-feasible line-search domain attached to the current stage data
`((w_k)_N, d̄_k)`. -/
abbrev stageLineSearchDomain
    (method : Method) (k : ℕ) : Set ℝ :=
  feasiblePointLineSearchDomain
    (method.reducedVariable k)
    (method.direction k)
    (method.stageReducedFeasibleSet k)

/-- The canonical Step 4 exact reduced-space line-search condition attached to stage `k`. -/
abbrev stageExactLineSearch
    (method : Method) (k : ℕ) : Prop :=
  FeasiblePointExactLineSearch
    ((method.elimination k).reducedObjective method.objective)
    (method.stageReducedFeasibleSet k)
    (method.reducedVariable k)
    (method.direction k)
    (method.stepSize k)

/-- The canonical active-stage validity package for the stagewise primitive data
`(M_k, (w_k)_N, λ_k)`. -/
theorem stage_valid
    (method : Method) {k : ℕ} (hk : 1 ≤ k) (hactive : method.active k) :
    GeneralEliminationStageValid
      method.objective
      method.feasibleSet
      (method.elimination k)
      (method.reducedVariable k)
      (method.multiplier k) :=
  method.stage_spec k hk hactive

/-- Every active stage of `method` is feasible. -/
theorem stage_mem_feasibleSet
    (method : Method) {k : ℕ} (hk : 1 ≤ k) (hactive : method.active k) :
    method k ∈ method.feasibleSet :=
  (method.stage_valid hk hactive).mem_feasibleSet

/-- On each active stage, the source elimination relation is exactly the stagewise generalized
elimination relation for the ambient constraint map `c`. -/
theorem constraint_eq_zero_iff_eq_elimination
    (method : Method) {k : ℕ} (hk : 1 ≤ k) (hactive : method.active k)
    (wB : BasicPoint) (wN : NonbasicPoint) :
    method.constraint ((method.elimination k).point wB wN) = 0 ↔
      wB = (method.elimination k) wN :=
  by
    rw [← method.elimination_constraint k hk hactive]
    exact (method.elimination k).constraint_eq_zero_iff_eq_phiBar wB wN

/-- Any feasible point of `method` satisfies the equality constraint equation `constraint x = 0`.
-/
theorem constraint_eq_zero_of_mem_feasibleSet
    (method : Method) {x : Point}
    (hx : x ∈ method.feasibleSet) :
    method.constraint x = 0 :=
  method.feasibleSet_constraint_eq_zero hx

/-- For every active stage `k ≥ 1`, the current iterate `x_k` satisfies the equality constraint
equation. -/
theorem constraint_iterate_eq_zero
    (method : Method) {k : ℕ} (hk : 1 ≤ k) (hactive : method.active k) :
    method.constraint (method k) = 0 :=
  method.constraint_eq_zero_of_mem_feasibleSet (method.stage_mem_feasibleSet hk hactive)

/-- At each active stage, the recorded Step 2 multiplier satisfies the canonical
generalized-elimination multiplier equation. -/
theorem multiplierEquation_of_active
    (method : Method) {k : ℕ} (hk : 1 ≤ k) (hactive : method.active k) :
    (method.elimination k).multiplierEquation
      method.objective
      (method.reducedVariable k)
      (method.multiplier k) :=
  (method.stage_valid hk hactive).multiplierEquation

/-- For any active stage `k ≥ 1`, the Step 2 reduced gradient `ḡ_k` is the generalized
elimination residual from formula `(11.2.32)`-`(11.2.33)` evaluated at the current iterate and
current multiplier. -/
theorem currentReducedGradient_eq_nonbasicResidual
    (method : Method) {k : ℕ} (hk : 1 ≤ k) (hactive : method.active k) :
    method.currentReducedGradient k =
      Matrix.toEuclideanLin
        ((method.elimination k).nonbasicBlock.transpose :
          Matrix (Fin (n - m)) (Fin n) ℝ)
        (gradient method.objective (method k) -
          Matrix.toEuclideanLin
            ((generalizedEliminationConstraintJacobian
                method.constraint
                (method k)).transpose :
              Matrix (Fin n) (Fin m) ℝ)
            (method.multiplier k)) := by
  let hstage := method.stage_valid hk hactive
  let hconstraint := method.elimination_constraint k hk hactive
  simpa [currentReducedGradient, iterate, hconstraint] using
    (method.elimination k).reducedGradient_eq_nonbasicStationarityResidual
      method.objective
      (method.reducedVariable k)
      (method.multiplier k)
      hstage.phiBar_differentiable
      (by simpa [iterate] using
        hstage.objective_differentiable)
      (by simpa [iterate, hconstraint] using
        hstage.constraint_differentiable)
      (by simpa [iterate, hconstraint] using
        hstage.basicConstraintBlock_nonsingular)
      hstage.multiplierEquation

/-- Algorithm 11.2.3 terminates at stage `k` exactly when `‖ḡ_k‖ ≤ ε`. -/
def terminatedAt
    (method : Method) (k : ℕ) : Prop :=
  ‖method.currentReducedGradient k‖ ≤ method.tolerance

/-- Unfolding `method.terminatedAt k` gives the Step 3 stopping test `‖ḡ_k‖ ≤ ε`. -/
theorem terminatedAt_iff
    (method : Method) (k : ℕ) :
    method.terminatedAt k ↔
      ‖method.currentReducedGradient k‖ ≤ method.tolerance :=
  Iff.rfl

/-- If stage `k` is active, then Algorithm 11.2.3 continues to stage `k + 1` exactly when the
Step 3 reduced-gradient test does not terminate the method. -/
theorem active_succ_iff_not_terminatedAt
    (method : Method) {k : ℕ} (hk : 1 ≤ k) :
    method.active (k + 1) ↔ method.active k ∧ ¬ method.terminatedAt k := by
  have hActiveSucc := method.active_succ_iff k hk
  simpa [terminatedAt, not_le] using hActiveSucc

/-- Any active stage `k + 1` comes from an active previous stage `k`; later stages cannot
reappear after termination. -/
theorem active_of_active_succ
    (method : Method) {k : ℕ} (hk : 1 ≤ k) (hactive : method.active (k + 1)) :
    method.active k :=
  (method.active_succ_iff_not_terminatedAt hk).1 hactive |>.1

/-- On each continuing stage, Step 4 is the canonical exact reduced-space line search from the
Section 11.2 variable-elimination owner, applied to the current generalized-elimination
split-space bridge data. -/
theorem stepSize_spec_of_active_succ
    (method : Method) {k : ℕ} (hk : 1 ≤ k) (hactive : method.active (k + 1)) :
    method.stageExactLineSearch k :=
  method.stepSize_spec k hk hactive

/-- On each continuing stage, the recorded search direction is a feasible descent direction for
the current reduced objective on the reduced feasible set. -/
theorem direction_spec_of_active_succ
    (method : Method) {k : ℕ} (hk : 1 ≤ k) (hactive : method.active (k + 1)) :
    IsFeasibleDescentDirection
      ((method.elimination k).reducedObjective method.objective)
      (method.reducedVariable k)
      (method.stageReducedFeasibleSet k)
      (method.direction k) := by
  simpa [stageReducedFeasibleSet] using method.direction_spec k hk hactive

/-- On each continuing stage, the recorded search direction is a reduced-gradient descent
direction. -/
theorem direction_descent_of_active_succ
    (method : Method) {k : ℕ} (hk : 1 ≤ k) (hactive : method.active (k + 1)) :
    inner ℝ
        (method.direction k)
        (method.currentReducedGradient k) <
      0 := by
  change inner ℝ
      (method.direction k)
      (gradient
        ((method.elimination k).reducedObjective method.objective)
        (method.reducedVariable k)) <
    0
  simpa [currentReducedGradient] using
    (method.direction_spec_of_active_succ hk hactive).descent

/-- On each continuing stage, the Step 4 steplength is positive. -/
theorem stepSize_pos_of_active_succ
    (method : Method) {k : ℕ} (hk : 1 ≤ k) (hactive : method.active (k + 1)) :
    0 < method.stepSize k :=
  FeasiblePointExactLineSearch.pos (method.stepSize_spec_of_active_succ hk hactive)

/-- On each continuing stage, the Step 4 trial point stays inside the feasible set `X`. -/
theorem trialPoint_mem_feasibleSet_of_active_succ
    (method : Method) {k : ℕ} (hk : 1 ≤ k) (hactive : method.active (k + 1)) :
    method.trialPoint k ∈
      method.feasibleSet := by
  have hmem :=
    FeasiblePointExactLineSearch.add_smul_mem
      (method.stepSize_spec_of_active_succ hk hactive)
  rw [(method.elimination k).mem_reducedFeasibleSet_iff method.feasibleSet] at hmem
  simpa [trialPoint, nextReducedVariable] using hmem

/-- On each continuing stage, the Step 4 trial point satisfies the transformed constraint
equation because every feasible point of `X` does. -/
theorem constraint_trialPoint_eq_zero_of_active_succ
    (method : Method) {k : ℕ} (hk : 1 ≤ k) (hactive : method.active (k + 1)) :
    method.constraint
        (method.trialPoint k) =
      0 :=
  method.constraint_eq_zero_of_mem_feasibleSet
    (method.trialPoint_mem_feasibleSet_of_active_succ hk hactive)

/-- On each continuing stage, the recorded steplength minimizes the current split-space reduced
objective on the positive reduced-feasible line-search domain. -/
theorem stepSize_isMinOn_of_active_succ
    (method : Method) {k : ℕ} (hk : 1 ≤ k) (hactive : method.active (k + 1)) :
    IsMinOn
      (fun a : ℝ ↦
        (method.elimination k).reducedObjective
          method.objective
          (method.reducedVariable k + a • method.direction k))
      (method.stageLineSearchDomain k)
      (method.stepSize k) := by
  simpa [lineSearchObjective_apply, stageLineSearchDomain, stageReducedFeasibleSet] using
    (method.stepSize_spec_of_active_succ hk hactive).isMinOn

/-- If stage `k + 1` is active, Step 4 updates the next iterate by the line-search formula
`x_(k + 1) = S_B φ̄_k ((w_k)_N + α_k d̄_k) + S_N ((w_k)_N + α_k d̄_k)`. -/
theorem iterate_succ_eq_trialPoint
    (method : Method) {k : ℕ} (hk : 1 ≤ k) (hactive : method.active (k + 1)) :
    method (k + 1) =
      method.trialPoint k := by
  simpa [iterate, trialPoint, nextReducedVariable] using
    method.iterate_succ_eq_trialPoint_spec k hk hactive

end GeneralEliminationMethod

#print axioms GeneralEliminationMethod.trialPoint
#print axioms GeneralEliminationMethod.currentReducedGradient
#print axioms GeneralEliminationMethod.currentReducedGradient_eq_nonbasicResidual

end Chapter11Algorithm1123
