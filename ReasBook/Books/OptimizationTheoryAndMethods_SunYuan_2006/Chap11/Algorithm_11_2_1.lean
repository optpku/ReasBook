/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Set.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.ToLin
import OptimizationTheoryAndMethods_SunYuan_2006.Chap02.Definition_2_1_extra_1
import OptimizationTheoryAndMethods_SunYuan_2006.Chap11.Definition_11_1_extra_1
import OptimizationTheoryAndMethods_SunYuan_2006.Chap11.Definition_11_1_extra_3
import OptimizationTheoryAndMethods_SunYuan_2006.Chap11.Definition_11_2_extra_1

noncomputable section

section Chapter11Algorithm1121

variable {basicDim nonbasicDim : ℕ}

local notation "BasicPoint" => EuclideanSpace ℝ (Fin basicDim)
local notation "NonbasicPoint" => EuclideanSpace ℝ (Fin nonbasicDim)
local notation "Point" => BasicPoint × NonbasicPoint

-- Semantic recall: `lean_leansearch` surfaced only generic gradient infrastructure and no
-- canonical mathlib owner for the variable-elimination iteration from Section 11.2. Following
-- nearby Chapter 11 algorithm files, this item keeps an explicit iteration-data owner. The
-- primitive split-space owner is the elimination graph point `x_N ↦ (φ x_N, x_N)`, from which
-- the reduced feasible set, reduced objective, and Step 4 update are derived.

/-- The point on the elimination graph over `x_N`, namely `(φ x_N, x_N)`. -/
def variableEliminationGraphPoint
    (φ : NonbasicPoint → BasicPoint) (xN : NonbasicPoint) : Point :=
  (φ xN, xN)

/-- The basic component of `variableEliminationGraphPoint φ xN` is `φ x_N`. -/
@[simp] theorem variableEliminationGraphPoint_fst
    (φ : NonbasicPoint → BasicPoint) (xN : NonbasicPoint) :
    (variableEliminationGraphPoint φ xN).1 = φ xN :=
  rfl

/-- The nonbasic component of `variableEliminationGraphPoint φ xN` is `x_N`. -/
@[simp] theorem variableEliminationGraphPoint_snd
    (φ : NonbasicPoint → BasicPoint) (xN : NonbasicPoint) :
    (variableEliminationGraphPoint φ xN).2 = xN :=
  rfl

/-- The Step 4 update in Algorithm 11.2.1 sends `(x_B, x_N)` to
`(φ (x_N + α • d̄), x_N + α • d̄)`. -/
def variableEliminationUpdate
    (φ : NonbasicPoint → BasicPoint) (xN dBar : NonbasicPoint) (α : ℝ) : Point :=
  variableEliminationGraphPoint φ (xN + α • dBar)

/-- The basic component of `variableEliminationUpdate φ xN dBar α` is
`φ (xN + α • d̄)`. -/
@[simp] theorem variableEliminationUpdate_fst
    (φ : NonbasicPoint → BasicPoint) (xN dBar : NonbasicPoint) (α : ℝ) :
    (variableEliminationUpdate φ xN dBar α).1 = φ (xN + α • dBar) :=
  rfl

/-- The nonbasic component of `variableEliminationUpdate φ xN dBar α` is
`x_N + α • d̄`. -/
@[simp] theorem variableEliminationUpdate_snd
    (φ : NonbasicPoint → BasicPoint) (xN dBar : NonbasicPoint) (α : ℝ) :
    (variableEliminationUpdate φ xN dBar α).2 = xN + α • dBar :=
  rfl

/-- The reduced feasible set attached to `feasibleSet` and the elimination map `φ` consists of
those nonbasic points `x_N` whose lifted split point `(φ x_N, x_N)` lies in `feasibleSet`. -/
def variableEliminationReducedFeasibleSet
    (feasibleSet : Set Point) (φ : NonbasicPoint → BasicPoint) : Set NonbasicPoint :=
  variableEliminationGraphPoint φ ⁻¹' feasibleSet

/-- Membership in `variableEliminationReducedFeasibleSet feasibleSet φ` means that the split point
`(φ x_N, x_N)` is feasible. -/
@[simp] theorem mem_variableEliminationReducedFeasibleSet_iff
    (feasibleSet : Set Point) (φ : NonbasicPoint → BasicPoint) (xN : NonbasicPoint) :
    xN ∈ variableEliminationReducedFeasibleSet feasibleSet φ ↔
      (φ xN, xN) ∈ feasibleSet :=
  Iff.rfl

/-- The reduced objective attached to `objective` and the elimination map `φ` is
`x_N ↦ objective (φ x_N, x_N)`. -/
def variableEliminationReducedObjective
    (objective : Point → ℝ) (φ : NonbasicPoint → BasicPoint) : NonbasicPoint → ℝ :=
  objective ∘ variableEliminationGraphPoint φ

/-- Unfolding `variableEliminationReducedObjective objective φ` gives the reduced objective value
at the split point `(φ x_N, x_N)`. -/
@[simp] theorem variableEliminationReducedObjective_eq
    (objective : Point → ℝ) (φ : NonbasicPoint → BasicPoint) (xN : NonbasicPoint) :
    variableEliminationReducedObjective objective φ xN =
      objective (φ xN, xN) :=
  rfl

/-- The positive reduced-feasible step sizes along the Step 3 ray `x_N + α • d̄`. This is the
Chapter 11 feasible-point line-search domain on the reduced feasible set. -/
abbrev variableEliminationLineSearchDomain
    (feasibleSet : Set Point) (φ : NonbasicPoint → BasicPoint)
    (xN dBar : NonbasicPoint) : Set ℝ :=
  feasiblePointLineSearchDomain
    xN
    dBar
    (variableEliminationReducedFeasibleSet feasibleSet φ)

/-- Membership in `variableEliminationLineSearchDomain feasibleSet φ x_N d̄` means that the step
size is positive and its Step 4 trial point stays reduced-feasible. -/
@[simp] theorem mem_variableEliminationLineSearchDomain_iff
    (feasibleSet : Set Point) (φ : NonbasicPoint → BasicPoint)
    (xN dBar : NonbasicPoint) (α : ℝ) :
    α ∈ variableEliminationLineSearchDomain feasibleSet φ xN dBar ↔
      0 < α ∧ xN + α • dBar ∈ variableEliminationReducedFeasibleSet feasibleSet φ :=
  mem_feasiblePointLineSearchDomain_iff
    xN
    dBar
    (variableEliminationReducedFeasibleSet feasibleSet φ)
    α

/-- The Step 4 exact reduced-space line-search condition is the Chapter 11 feasible-point exact
line search on the reduced objective and reduced feasible set. -/
theorem variableEliminationExactLineSearch_iff
    (objective : Point → ℝ) (feasibleSet : Set Point) (φ : NonbasicPoint → BasicPoint)
    (xN dBar : NonbasicPoint) (α : ℝ) :
    FeasiblePointExactLineSearch
        (variableEliminationReducedObjective objective φ)
        (variableEliminationReducedFeasibleSet feasibleSet φ)
        xN
        dBar
        α ↔
      IsFeasibleDirectionAt
          (variableEliminationReducedFeasibleSet feasibleSet φ)
          xN
          dBar ∧
        α ∈ variableEliminationLineSearchDomain feasibleSet φ xN dBar ∧
          IsMinOn
            (fun a : ℝ ↦ objective (φ (xN + a • dBar), xN + a • dBar))
            (variableEliminationLineSearchDomain feasibleSet φ xN dBar)
            α := by
  constructor
  · intro h
    rcases
        (feasiblePointExactLineSearch_iff
          (variableEliminationReducedObjective objective φ)
          (variableEliminationReducedFeasibleSet feasibleSet φ)
          xN
          dBar
          α).1 h with
      ⟨hDirection, hAlpha, hMinOn⟩
    refine ⟨hDirection, ?_, ?_⟩
    · simpa [variableEliminationLineSearchDomain] using hAlpha
    · simpa [variableEliminationReducedObjective, variableEliminationGraphPoint,
        variableEliminationLineSearchDomain] using hMinOn
  · rintro ⟨hDirection, hAlpha, hMinOn⟩
    exact
      (feasiblePointExactLineSearch_iff
        (variableEliminationReducedObjective objective φ)
        (variableEliminationReducedFeasibleSet feasibleSet φ)
        xN
        dBar
        α).2
        ⟨hDirection,
          by simpa [variableEliminationLineSearchDomain] using hAlpha,
          by
            simpa [variableEliminationReducedObjective,
              variableEliminationGraphPoint, variableEliminationLineSearchDomain] using hMinOn⟩

/-- `variableEliminationStepTwoSpec objective constraint x A_B A_N λ g̃` states that `A_B` and
`A_N` are the Step 2 transpose Jacobian blocks of `∂ c(x)ᵀ / ∂ x`, `λ` satisfies the multiplier
equation `(11.2.12)`, and `g̃` is the reduced-gradient residual from `(11.2.11)` in split
coordinates at `x = (x_B, x_N)`. -/
def variableEliminationStepTwoSpec
    (objective : Point → ℝ) (constraint : Point → BasicPoint) (x : Point)
    (AB : Matrix (Fin basicDim) (Fin basicDim) ℝ)
    (AN : Matrix (Fin nonbasicDim) (Fin basicDim) ℝ)
    (lam : BasicPoint) (gTilde : NonbasicPoint) : Prop :=
  AB = (constraintJacobianB (fun xB xN ↦ constraint (xB, xN)) x.1 x.2).transpose ∧
    AN = (constraintJacobianN (fun xB xN ↦ constraint (xB, xN)) x.1 x.2).transpose ∧
    partialGradientB (fun xB xN ↦ objective (xB, xN)) x.1 x.2 =
      Matrix.toEuclideanLin AB lam ∧
    gTilde =
      partialGradientN (fun xB xN ↦ objective (xB, xN)) x.1 x.2 -
        Matrix.toEuclideanLin AN lam

/-- Unfolding `variableEliminationStepTwoSpec` gives the Step 2 Jacobian-block equalities and the
formulas `(11.2.12)` and `(11.2.11)` at the current split point. -/
theorem variableEliminationStepTwoSpec_iff
    (objective : Point → ℝ) (constraint : Point → BasicPoint) (x : Point)
    (AB : Matrix (Fin basicDim) (Fin basicDim) ℝ)
    (AN : Matrix (Fin nonbasicDim) (Fin basicDim) ℝ)
    (lam : BasicPoint) (gTilde : NonbasicPoint) :
    variableEliminationStepTwoSpec objective constraint x AB AN lam gTilde ↔
      AB = (constraintJacobianB (fun xB xN ↦ constraint (xB, xN)) x.1 x.2).transpose ∧
        AN = (constraintJacobianN (fun xB xN ↦ constraint (xB, xN)) x.1 x.2).transpose ∧
        partialGradientB (fun xB xN ↦ objective (xB, xN)) x.1 x.2 =
          Matrix.toEuclideanLin AB lam ∧
        gTilde =
          partialGradientN (fun xB xN ↦ objective (xB, xN)) x.1 x.2 -
            Matrix.toEuclideanLin AN lam :=
  Iff.rfl

/-- Chapter11 Algorithm 11.2.1: a variable elimination method is modeled on the split space
`x = (x_B, x_N)` with objective `f`, equality-constraint map `c`, feasible set `X`, elimination
map `φ`, tolerance `ε ≥ 0`, initial feasible point `x₁ ∈ X`, active-stage predicate, iterate
sequence `x_k`, Step 2 Jacobian blocks `A_B` and `A_N`, multiplier sequence `λ_k`, reduced
gradient sequence `g̃_k`, Step 3 descent directions `d̄_k`, and Step 4 step sizes `α_k`. At each
active stage `k ≥ 1`, the equality constraints are solved exactly by the elimination graph
`x_B = φ x_N`, the current iterate lies on that graph, the block `A_B(k)` is nonsingular,
Step 2 satisfies the source formulas `(11.2.12)` and `(11.2.11)`, the recorded reduced gradient
`g̃_k` agrees with the canonical gradient of the reduced objective, the method continues to stage
`k + 1` exactly when `ε < ‖g̃_k‖`, every continuing stage uses a feasible descent direction for
the reduced objective on the reduced feasible set determined by `X`, the chosen step size
satisfies the exact reduced-space line-search condition from `(11.2.17)`, and the next iterate is
`x_(k + 1) = (φ ((x_N)_k + α_k • d̄_k), (x_N)_k + α_k • d̄_k)`. -/
structure VariableEliminationMethod where
  objective : Point → ℝ
  constraint : Point → BasicPoint
  feasibleSet : Set Point
  φ : NonbasicPoint → BasicPoint
  ε : ℝ
  x1 : Point
  active : ℕ → Prop
  iterate : ℕ → Point
  basicJacobian : ℕ → Matrix (Fin basicDim) (Fin basicDim) ℝ
  nonbasicJacobian : ℕ → Matrix (Fin nonbasicDim) (Fin basicDim) ℝ
  multiplier : ℕ → BasicPoint
  reducedGradient : ℕ → NonbasicPoint
  direction : ℕ → NonbasicPoint
  stepSize : ℕ → ℝ
  constraint_eq_zero_iff_eq_phi (xB : BasicPoint) (xN : NonbasicPoint) :
    constraint (xB, xN) = 0 ↔ xB = φ xN
  epsilon_nonneg : 0 ≤ ε
  initialPoint_mem : x1 ∈ feasibleSet
  iterate_one : iterate 1 = x1
  active_one : active 1
  feasible (k : ℕ) (hk : 1 ≤ k) (hactive : active k) :
    iterate k ∈ feasibleSet
  iterate_compatible (k : ℕ) (hk : 1 ≤ k) (hactive : active k) :
    (iterate k).1 = φ (iterate k).2
  basicJacobian_nonsingular (k : ℕ) (hk : 1 ≤ k) (hactive : active k) :
    IsUnit (Matrix.det (basicJacobian k))
  stepTwoSpec (k : ℕ) (hk : 1 ≤ k) (hactive : active k) :
    variableEliminationStepTwoSpec
      objective
      constraint
      (iterate k)
      (basicJacobian k)
      (nonbasicJacobian k)
      (multiplier k)
      (reducedGradient k)
  reducedGradient_eq_gradient (k : ℕ) (hk : 1 ≤ k) (hactive : active k) :
    reducedGradient k =
      gradient (variableEliminationReducedObjective objective φ) (iterate k).2
  active_succ_iff (k : ℕ) (hk : 1 ≤ k) :
    active (k + 1) ↔ active k ∧ ε < ‖reducedGradient k‖
  direction_spec (k : ℕ) (hk : 1 ≤ k) (hactive : active (k + 1)) :
    IsFeasibleDescentDirection
      (variableEliminationReducedObjective objective φ)
      (iterate k).2
      (variableEliminationReducedFeasibleSet feasibleSet φ)
      (direction k)
  stepSize_spec (k : ℕ) (hk : 1 ≤ k) (hactive : active (k + 1)) :
    FeasiblePointExactLineSearch
      (variableEliminationReducedObjective objective φ)
      (variableEliminationReducedFeasibleSet feasibleSet φ)
      (iterate k).2
      (direction k)
      (stepSize k)
  iterate_succ (k : ℕ) (hk : 1 ≤ k) (hactive : active (k + 1)) :
    iterate (k + 1) =
      variableEliminationUpdate φ (iterate k).2 (direction k) (stepSize k)

namespace VariableEliminationMethod

local notation "Method" => @_root_.VariableEliminationMethod basicDim nonbasicDim

/-- `method` can be evaluated as its iterate sequence `x_k`. -/
instance : CoeFun (@_root_.VariableEliminationMethod basicDim nonbasicDim)
    (fun _ ↦ ℕ → Point) where
  coe method := method.iterate

/-- Evaluating `method` as a function returns its iterate sequence. -/
@[simp] theorem coe_apply
    (method : Method) (k : ℕ) :
    method k = method.iterate k :=
  rfl

/-- The elimination-graph point of `method` over `x_N`. -/
def graphPoint
    (method : Method) (xN : NonbasicPoint) : Point :=
  variableEliminationGraphPoint method.φ xN

/-- Unfolding `method.graphPoint xN` gives `(method.φ xN, xN)`. -/
@[simp] theorem graphPoint_eq
    (method : Method) (xN : NonbasicPoint) :
    method.graphPoint xN = (method.φ xN, xN) :=
  rfl

/-- The reduced feasible set determined by the elimination graph of `method`. -/
def reducedFeasibleSet
    (method : Method) : Set NonbasicPoint :=
  variableEliminationReducedFeasibleSet method.feasibleSet method.φ

/-- Membership in `method.reducedFeasibleSet` means that the lifted graph point is feasible. -/
@[simp] theorem mem_reducedFeasibleSet_iff
    (method : Method) (xN : NonbasicPoint) :
    xN ∈ method.reducedFeasibleSet ↔ method.graphPoint xN ∈ method.feasibleSet :=
  Iff.rfl

/-- The reduced objective induced by `method.objective` along the elimination graph. -/
def reducedObjective
    (method : Method) : NonbasicPoint → ℝ :=
  variableEliminationReducedObjective method.objective method.φ

/-- Unfolding `method.reducedObjective xN` evaluates `method.objective` on the graph point. -/
@[simp] theorem reducedObjective_eq
    (method : Method) (xN : NonbasicPoint) :
    method.reducedObjective xN = method.objective (method.graphPoint xN) :=
  rfl

/-- The positive reduced-feasible Step 4 line-search domain of `method` at `(x_N, d̄)`. -/
def lineSearchDomain
    (method : Method) (xN dBar : NonbasicPoint) : Set ℝ :=
  feasiblePointLineSearchDomain xN dBar method.reducedFeasibleSet

/-- Membership in `method.lineSearchDomain xN dBar` means positivity and reduced feasibility. -/
@[simp] theorem mem_lineSearchDomain_iff
    (method : Method) (xN dBar : NonbasicPoint) (α : ℝ) :
    α ∈ method.lineSearchDomain xN dBar ↔
      0 < α ∧ xN + α • dBar ∈ method.reducedFeasibleSet := by
  simp [VariableEliminationMethod.lineSearchDomain, VariableEliminationMethod.reducedFeasibleSet]

/-- The Step 4 variable-elimination update attached to `method.φ`. -/
def update
    (method : Method) (xN dBar : NonbasicPoint) (α : ℝ) : Point :=
  variableEliminationUpdate method.φ xN dBar α

/-- Unfolding `method.update xN dBar α` gives the graph point over `x_N + α • d̄`. -/
@[simp] theorem update_eq
    (method : Method) (xN dBar : NonbasicPoint) (α : ℝ) :
    method.update xN dBar α = method.graphPoint (xN + α • dBar) :=
  rfl

/-- Algorithm 11.2.1 is terminated at stage `k` when the reduced gradient norm satisfies
`‖g̃_k‖ ≤ ε`. -/
def terminatedAt
    (method : Method) (k : ℕ) : Prop :=
  ‖method.reducedGradient k‖ ≤ method.ε

/-- Unfolding `method.terminatedAt k` gives the Step 3 stopping test `‖g̃_k‖ ≤ ε`. -/
@[simp] theorem terminatedAt_iff
    (method : Method) (k : ℕ) :
    method.terminatedAt k ↔ ‖method.reducedGradient k‖ ≤ method.ε :=
  Iff.rfl

/-- At an active stage, the algorithm continues to stage `k + 1` exactly when stage `k`
is not terminated. -/
theorem active_succ_iff_not_terminatedAt
    (method : Method) {k : ℕ} (hk : 1 ≤ k) :
    method.active (k + 1) ↔ method.active k ∧ ¬ method.terminatedAt k := by
  constructor
  · intro hSucc
    rcases (VariableEliminationMethod.active_succ_iff method k hk).1 hSucc with ⟨hActive, hNorm⟩
    refine ⟨hActive, ?_⟩
    simpa [VariableEliminationMethod.terminatedAt, not_le] using hNorm
  · rintro ⟨hActive, hNotTerminated⟩
    refine (VariableEliminationMethod.active_succ_iff method k hk).2 ⟨hActive, ?_⟩
    simpa [VariableEliminationMethod.terminatedAt, not_le] using hNotTerminated

/-- The equality-constraint equation `method.constraint (x_B, x_N) = 0` is solved exactly by the
elimination relation `x_B = method.φ x_N`. -/
theorem constraint_eq_zero_iff
    (method : Method) (xB : BasicPoint) (xN : NonbasicPoint) :
    method.constraint (xB, xN) = 0 ↔ xB = method.φ xN :=
  method.constraint_eq_zero_iff_eq_phi xB xN

/-- Every graph point `(method.φ x_N, x_N)` of the elimination map satisfies the equality
constraints. -/
theorem constraint_graph_eq_zero
    (method : Method) (xN : NonbasicPoint) :
    method.constraint (method.φ xN, xN) = 0 :=
  (method.constraint_eq_zero_iff _ _).2 rfl

/-- At each active stage, the current iterate lies on the elimination graph
`x_B = method.φ x_N`. -/
theorem iterate_fst_eq_phi_of_active
    (method : Method) {k : ℕ} (hk : 1 ≤ k) (hactive : method.active k) :
    (method.iterate k).1 = method.φ (method.iterate k).2 :=
  method.iterate_compatible k hk hactive

/-- At each active stage, the current iterate is exactly the graph point over its nonbasic
component. -/
theorem iterate_eq_graphPoint_of_active
    (method : Method) {k : ℕ} (hk : 1 ≤ k) (hactive : method.active k) :
    method.iterate k = method.graphPoint (method.iterate k).2 := by
  ext <;>
    simp [VariableEliminationMethod.graphPoint,
      method.iterate_fst_eq_phi_of_active hk hactive]

/-- At each active stage, the current iterate satisfies the equality constraints defining the
elimination graph. -/
theorem constraint_iterate_eq_zero_of_active
    (method : Method) {k : ℕ} (hk : 1 ≤ k) (hactive : method.active k) :
    method.constraint (method.iterate k) = 0 := by
  rw [method.iterate_eq_graphPoint_of_active hk hactive]
  exact method.constraint_graph_eq_zero (method.iterate k).2

/-- At each active stage, Step 2 records the source Jacobian block equations together with the
formulas `(11.2.12)` and `(11.2.11)`. -/
theorem stepTwoSpec_of_active
    (method : Method) {k : ℕ} (hk : 1 ≤ k) (hactive : method.active k) :
    variableEliminationStepTwoSpec
      method.objective
      method.constraint
      (method.iterate k)
      (method.basicJacobian k)
      (method.nonbasicJacobian k)
      (method.multiplier k)
      (method.reducedGradient k) :=
  method.stepTwoSpec k hk hactive

/-- At each active stage, the recorded reduced gradient `g̃_k` agrees with the canonical
gradient of the reduced objective at `(x_N)_k`. -/
theorem reducedGradient_eq_of_active
    (method : Method) {k : ℕ} (hk : 1 ≤ k) (hactive : method.active k) :
    method.reducedGradient k =
      gradient method.reducedObjective (method.iterate k).2 := by
  simpa [VariableEliminationMethod.reducedObjective] using
    method.reducedGradient_eq_gradient k hk hactive

/-- The initial iterate of `method` is feasible. -/
theorem iterate_one_mem_feasibleSet
    (method : Method) :
    method.iterate 1 ∈ method.feasibleSet := by
  simpa [method.iterate_one] using method.initialPoint_mem

/-- On each continuing stage, the recorded search direction is a feasible descent direction for
the reduced objective on the reduced feasible set. -/
theorem direction_spec_of_active_succ
    (method : Method) {k : ℕ} (hk : 1 ≤ k)
    (hactive : method.active (k + 1)) :
    IsFeasibleDescentDirection
      method.reducedObjective
      (method.iterate k).2
      method.reducedFeasibleSet
      (method.direction k) := by
  simpa [VariableEliminationMethod.reducedObjective, VariableEliminationMethod.reducedFeasibleSet]
    using method.direction_spec k hk hactive

/-- On each continuing stage, the recorded search direction satisfies the source descent
inequality `⟪d̄_k, g̃_k⟫ < 0`. -/
theorem direction_descent_of_active_succ
    (method : Method) {k : ℕ} (hk : 1 ≤ k)
    (hactive : method.active (k + 1)) :
    inner ℝ (method.direction k) (method.reducedGradient k) < 0 := by
  rw [method.reducedGradient_eq_of_active hk
    ((method.active_succ_iff_not_terminatedAt hk).1 hactive).1]
  simpa using
    IsFeasibleDescentDirection.descent (method.direction_spec_of_active_succ hk hactive)

/-- On each continuing stage, the recorded search direction is a descent direction for the
canonical reduced objective gradient. -/
theorem direction_gradient_descent_of_active_succ
    (method : Method) {k : ℕ} (hk : 1 ≤ k)
    (hactive : method.active (k + 1)) :
    inner ℝ (method.direction k) (gradient method.reducedObjective (method.iterate k).2) < 0 := by
  rw [← method.reducedGradient_eq_of_active hk
    ((method.active_succ_iff_not_terminatedAt hk).1 hactive).1]
  exact method.direction_descent_of_active_succ hk hactive

/-- On each continuing stage, the Step 4 steplength is an exact line-search step on the reduced
objective along the reduced feasible ray. -/
theorem stepSize_spec_of_active_succ
    (method : Method) {k : ℕ} (hk : 1 ≤ k)
    (hactive : method.active (k + 1)) :
    FeasiblePointExactLineSearch
      method.reducedObjective
      method.reducedFeasibleSet
      (method.iterate k).2
      (method.direction k)
      (method.stepSize k) :=
  by
    simpa [VariableEliminationMethod.reducedObjective, VariableEliminationMethod.reducedFeasibleSet]
      using method.stepSize_spec k hk hactive

/-- On each continuing stage, the Step 4 line search step size is positive. -/
theorem stepSize_pos_of_active_succ
    (method : Method) {k : ℕ} (hk : 1 ≤ k)
    (hactive : method.active (k + 1)) :
    0 < method.stepSize k :=
  FeasiblePointExactLineSearch.pos (method.stepSize_spec_of_active_succ hk hactive)

/-- On each continuing stage, the next iterate is the source Step 4 variable-elimination
update. -/
theorem iterate_succ_eq_update
    (method : Method) {k : ℕ} (hk : 1 ≤ k)
    (hactive : method.active (k + 1)) :
    method.iterate (k + 1) =
      method.update (method.iterate k).2 (method.direction k) (method.stepSize k) := by
  simpa [VariableEliminationMethod.update] using method.iterate_succ k hk hactive

end VariableEliminationMethod

#print axioms variableEliminationUpdate
#print axioms variableEliminationReducedFeasibleSet
#print axioms variableEliminationReducedObjective

end Chapter11Algorithm1121
