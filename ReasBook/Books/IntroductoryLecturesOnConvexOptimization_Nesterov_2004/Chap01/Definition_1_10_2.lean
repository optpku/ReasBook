/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap01.Definition_1_1_1
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap01.Definition_1_3_7

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u

open scoped ConstrainedArgmin

/- Definition 1.10.2 lies in the finite-constraint Lagrangian-duality domain.

Sampled owner declarations in this domain:
* `FunctionalConstraintsMinimizationProblem X m` together with
  `FunctionalConstraintsMinimizationProblem.constraintVector` and
  `FunctionalConstraintsMinimizationProblem.mem_feasibleSet_iff` in `Chap01/Definition_1_1_1`,
  the chapter owner for finitely many scalar constraints on an ambient feasible subtype;
* `SetConstrainedMinimizationProblem`, `argmin[Q] f`, and
  `SetConstrainedMinimizationProblem.optimalValue` in `Chap01/Definition_1_3_3` and
  `Chap01/Definition_1_3_7`, the chapter owners for minimizer sets and optimal values of ambient
  constrained problems;
* `problem.constrainedAuxiliaryOptimalValue` in `Chap02/Lemma_2_21`, which already routes a
  Lagrangian-derived value function through `SetConstrainedMinimizationProblem.optimalValue`.

Best owner abstraction:
* source-facing: `LagrangianProblem Q m`, whose primitive data are exactly an ambient objective
  and finitely many inequality constraints on `Q`;
* core/canonical: the chapter owners `FunctionalConstraintsMinimizationProblem Q m` for the
  feasible-set / constraint-vector layer and `SetConstrainedMinimizationProblem Q` together with
  `argmin[Q]` / `optimalValue` for ambient minimization;
* bridge/view: `toFunctionalConstraintsMinimizationProblem`,
  `toSetConstrainedMinimizationProblem`, and the fixed-multiplier minimizer set
  `lagrangianMinimizers`.

Primitive data:
* `objective : Q → ℝ`
* `constraints : Fin m → Q → ℝ`

Derived API:
* the objective coercion
* `constraintVector`
* `feasibleSet`
* `toSetConstrainedMinimizationProblem`
* `primalOptimalValue`
* `lagrangian`
* `dualFunction`
* `lagrangianMinimizers`
* `dualOptimalValue`

This refinement keeps the textbook owner `LagrangianProblem`, but deletes the duplicate ambient
optimal-value and minimizer-set wheels by routing them through the existing Chapter 1 owners
`SetConstrainedMinimizationProblem.optimalValue` and `argmin[Q]`. -/

/-- Definition 1.10.2: A Lagrangian problem is specified by a domain `Q`, an objective function
`f₀ : Q → ℝ`, and finitely many inequality constraint functions `fⱼ : Q → ℝ` for
`j = 1, ..., m`; the feasible set, primal optimal value, Lagrangian, dual function and its
domain, the Lagrangian minimizers, and the dual optimal value are the derived notions defined
below. -/
structure LagrangianProblem (Q : Type u) (m : ℕ) where
  objective : Q → ℝ
  constraints : Fin m → Q → ℝ

/-- A Lagrangian problem coerces to its objective function. -/
instance : CoeFun (LagrangianProblem Q m) (fun _ ↦ Q → ℝ) where
  coe problem := problem.objective

namespace LagrangianProblem

variable {Q : Type u} {m : ℕ}

/-- Evaluating a Lagrangian problem at a point returns its objective value. -/
@[simp] theorem coe_apply (problem : LagrangianProblem Q m) (x : Q) :
    problem x = problem.objective x :=
  rfl

/-- The Chapter 1 functional-constraint owner attached to a Lagrangian problem by taking the
ambient domain `Q` as the basic feasible set and recording that all constraint senses are `≤`.
-/
def toFunctionalConstraintsMinimizationProblem (problem : LagrangianProblem Q m) :
    FunctionalConstraintsMinimizationProblem Q m where
  basicFeasibleSet := Set.univ
  objective := fun x ↦ problem x
  constraints := fun j x ↦ problem.constraints j x
  senses := fun _ ↦ .le

end LagrangianProblem

/-- The nonnegative orthant `ℝ₊^m = {λ ∈ ℝ^m | λⱼ ≥ 0 for all `j`}`. -/
def EuclideanSpace.nonnegativeOrthant (m : ℕ) : Set (EuclideanSpace ℝ (Fin m)) :=
  {l | ∀ j : Fin m, 0 ≤ l j}

/-- The positive orthant `ℝ₊₊^m = {x ∈ ℝ^m | 0 < xⱼ for all `j`}`. -/
def EuclideanSpace.positiveOrthant (m : ℕ) : Set (EuclideanSpace ℝ (Fin m)) :=
  {x | ∀ j : Fin m, 0 < x j}

namespace EuclideanOrthant

/- Source-facing Lean notation for the textbook Euclidean orthants `ℝ₊^m` and `ℝ₊₊^m`. -/
scoped notation:max "ℝ₊^" n:arg => EuclideanSpace.nonnegativeOrthant n
scoped notation:max "ℝ₊₊^" n:arg => EuclideanSpace.positiveOrthant n

end EuclideanOrthant

open scoped EuclideanOrthant

namespace EuclideanSpace

variable {m : ℕ} {l : EuclideanSpace ℝ (Fin m)}

/-- Membership in the nonnegative orthant is coordinatewise nonnegativity. -/
@[simp] theorem mem_nonnegativeOrthant_iff :
    l ∈ ℝ₊^m ↔ ∀ j : Fin m, 0 ≤ l j :=
  Iff.rfl

/-- Membership in the positive orthant is coordinatewise strict positivity. -/
@[simp] theorem mem_positiveOrthant_iff {x : EuclideanSpace ℝ (Fin m)} :
    x ∈ ℝ₊₊^m ↔ ∀ j : Fin m, 0 < x j :=
  Iff.rfl

end EuclideanSpace

namespace LagrangianProblem

variable {Q : Type u} {m : ℕ}

local notation "Λ" => EuclideanSpace ℝ (Fin m)

/-- The vector-valued constraint map `x ↦ (f₁(x), ..., fₘ(x))ᵀ`. -/
def constraintVector (problem : LagrangianProblem Q m) : Q → Λ :=
  fun x ↦ problem.toFunctionalConstraintsMinimizationProblem.constraintVector ⟨x, Set.mem_univ x⟩

/-- The coordinates of the constraint vector are the scalar constraint values. -/
@[simp] theorem constraintVector_apply (problem : LagrangianProblem Q m) (x : Q) (j : Fin m) :
    problem.constraintVector x j = problem.constraints j x :=
  rfl

/-- The feasible set cut out by the inequality constraints `fⱼ(x) ≤ 0`. -/
def feasibleSet (problem : LagrangianProblem Q m) : Set Q :=
  problem.toFunctionalConstraintsMinimizationProblem.feasibleSet

/-- Membership in the feasible set is exactly coordinatewise constraint feasibility. -/
@[simp] theorem mem_feasibleSet_iff (problem : LagrangianProblem Q m) {x : Q} :
    x ∈ problem.feasibleSet ↔ ∀ j : Fin m, problem.constraints j x ≤ 0 := by
  let x' : problem.toFunctionalConstraintsMinimizationProblem.basicFeasibleSet :=
    ⟨x, Set.mem_univ x⟩
  have hx' :
      x' ∈ problem.toFunctionalConstraintsMinimizationProblem.feasibleSet ↔
        ∀ j : Fin m,
          problem.toFunctionalConstraintsMinimizationProblem.constraints j x' ≤ 0 :=
    problem.toFunctionalConstraintsMinimizationProblem.mem_feasibleSet_iff (fun _ ↦ rfl)
  simpa [x', feasibleSet, toFunctionalConstraintsMinimizationProblem] using hx'

/-- The ambient constrained minimization problem obtained by minimizing the objective on the
feasible set cut out by the inequality constraints. -/
def toSetConstrainedMinimizationProblem (problem : LagrangianProblem Q m) :
    SetConstrainedMinimizationProblem Q where
  feasibleSet := problem.feasibleSet
  objective := problem

/-- The owner bridge preserves the feasible set. -/
@[simp] theorem toSetConstrainedMinimizationProblem_feasibleSet
    (problem : LagrangianProblem Q m) :
    problem.toSetConstrainedMinimizationProblem.feasibleSet = problem.feasibleSet :=
  rfl

/-- The owner bridge evaluates to the original objective. -/
@[simp] theorem toSetConstrainedMinimizationProblem_apply
    (problem : LagrangianProblem Q m) (x : Q) :
    problem.toSetConstrainedMinimizationProblem x = problem x :=
  rfl

/-- The primal optimal value `f*`, interpreted as the extended-real infimum over the feasible
set. -/
def primalOptimalValue (problem : LagrangianProblem Q m) : EReal :=
  problem.toSetConstrainedMinimizationProblem.optimalValue

/-- Expanding `problem.primalOptimalValue` recovers the infimum of the objective over the feasible
set. -/
theorem primalOptimalValue_eq_sInf_image (problem : LagrangianProblem Q m) :
    problem.primalOptimalValue =
      sInf ((fun x : Q ↦ (problem x : EReal)) '' problem.feasibleSet) := by
  simpa [primalOptimalValue] using
    problem.toSetConstrainedMinimizationProblem.optimalValue_eq_sInf_image

/-- The Lagrangian `𝓛(x, λ) = f₀(x) + ⟨λ, f(x)⟩`. -/
def lagrangian (problem : LagrangianProblem Q m) (x : Q) (l : Λ) : ℝ :=
  problem x + inner ℝ l (problem.constraintVector x)

/-- For a single inequality constraint, the Lagrangian at the scalar multiplier `λ` is
`f₀(x) + λ f₁(x)`. -/
@[simp] theorem lagrangian_single_eq (problem : LagrangianProblem Q 1) (x : Q) (lam : ℝ) :
    problem.lagrangian x (EuclideanSpace.single 0 lam) =
      problem x + lam * problem.constraints 0 x := by
  rw [lagrangian]
  simpa [constraintVector_apply] using
    (EuclideanSpace.inner_single_left (i := 0) (a := lam) (v := problem.constraintVector x))

/-- The dual function `ψ(λ) = inf_{x ∈ Q} 𝓛(x, λ)`, routed through the Chapter 1 owner
`SetConstrainedMinimizationProblem.optimalValue` for the unconstrained Lagrangian subproblem on
`Q`. The codomain is `EReal` so that `-∞` is available. -/
def dualFunction (problem : LagrangianProblem Q m) (l : Λ) : EReal :=
  (SetConstrainedMinimizationProblem.unconstrained fun x ↦ problem.lagrangian x l).optimalValue

/-- The effective domain of the dual function, consisting of multipliers for which `ψ(λ) > -∞`. -/
def dualDomain (problem : LagrangianProblem Q m) : Set Λ :=
  {l | ⊥ < problem.dualFunction l}

/-- Membership in the dual domain means the dual function is finite from below. -/
@[simp] theorem mem_dualDomain_iff (problem : LagrangianProblem Q m) {l : Λ} :
    l ∈ problem.dualDomain ↔ ⊥ < problem.dualFunction l :=
  Iff.rfl

/-- The feasible set of the Lagrange dual problem is `dom ψ ∩ ℝ₊^m`. -/
def dualFeasibleSet (problem : LagrangianProblem Q m) : Set Λ :=
  problem.dualDomain ∩ ℝ₊^m

/-- Dual feasibility means lying in the dual domain and in the nonnegative orthant. -/
@[simp] theorem mem_dualFeasibleSet_iff (problem : LagrangianProblem Q m) {l : Λ} :
    l ∈ problem.dualFeasibleSet ↔ l ∈ problem.dualDomain ∧ ∀ j : Fin m, 0 ≤ l j := by
  simp [dualFeasibleSet]

/-- The set `X*(λ)` of global minimizers of the Lagrangian subproblem at a fixed multiplier
`λ`. -/
def lagrangianMinimizers (problem : LagrangianProblem Q m) (l : Λ) : Set Q :=
  argmin[Set.univ] fun y ↦ problem.lagrangian y l

/-- Membership in `X*(λ)` means being a global minimizer of `x ↦ 𝓛(x, λ)`. -/
@[simp] theorem mem_lagrangianMinimizers_iff (problem : LagrangianProblem Q m) {l : Λ} {x : Q} :
    x ∈ problem.lagrangianMinimizers l ↔
      IsMinOn (fun y ↦ problem.lagrangian y l) Set.univ x := by
  rw [lagrangianMinimizers, mem_constrainedArgmin_iff]
  simp

/-- A point of `X*(λ)` realizes the dual value `ψ(λ)` by evaluating the Lagrangian at that
point. -/
-- Proof sketch: `problem.dualFunction l` is the owner optimal value of the unconstrained
-- Lagrangian subproblem on `Q`, so apply
-- `SetConstrainedMinimizationProblem.optimalValue_eq_of_isMinOn` to the minimizer witness
-- encoded by `x ∈ X*(λ)`.
theorem dualFunction_eq_lagrangian
    (problem : LagrangianProblem Q m) {l : Λ} {x : Q}
    (hx : x ∈ problem.lagrangianMinimizers l) :
    problem.dualFunction l = (problem.lagrangian x l : EReal) := by
  -- Rewrite `x ∈ X*(λ)` into the owner-level global minimizer statement on `Set.univ`.
  rw [mem_lagrangianMinimizers_iff] at hx
  -- Realize `ψ(λ)` as the optimal value of the unconstrained Lagrangian subproblem.
  simpa [dualFunction] using
    (SetConstrainedMinimizationProblem.optimalValue_eq_of_isMinOn
      (problem := SetConstrainedMinimizationProblem.unconstrained
        (fun y ↦ problem.lagrangian y l))
      (x := x)
      (by simp)
      hx)

/-- The Lagrange dual optimal value `f_*`, interpreted as the extended-real supremum of `ψ` over
`dom ψ ∩ ℝ₊ᵐ`. -/
def dualOptimalValue (problem : LagrangianProblem Q m) : EReal :=
  sSup (problem.dualFunction '' problem.dualFeasibleSet)

end LagrangianProblem
