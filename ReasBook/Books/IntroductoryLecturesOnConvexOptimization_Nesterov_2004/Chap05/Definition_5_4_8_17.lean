/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap01.Definition_1_10_2

-- Declarations for this item will be appended below by the statement pipeline.

open scoped BigOperators
open scoped EuclideanOrthant
open EuclideanSpace (positiveOrthant)

noncomputable section

/-
Definition 5.4.8.17 lies in the Chapter 5 geometric-programming / positive-orthant domain.

Sampled owner declarations:
* `EuclideanSpace.positiveOrthant` and `EuclideanSpace.mem_positiveOrthant_iff` from
  `Chap01/Definition_1_10_2`, the project owner for the strict positive orthant `ℝⁿ₊₊`;
* `LagrangianProblem` and `LagrangianProblem.mem_feasibleSet_iff` from
  `Chap01/Definition_1_10_2`, the canonical owner for an objective together with `≤ 0`
  constraints;
* `SeparableOptimizationProblem.toLagrangianProblem` and
  `SeparableOptimizationProblem.feasibleSet` from `Chap05/Definition_5_4_8_1`, the local Chapter 5
  source-facing pattern of keeping primitive source data while routing feasibility through the
  Chapter 1 owner.

Best owner abstraction:
* source-facing: `GeometricOptimizationProblem n m`, whose primitive data are the block sizes,
  positive coefficients, and exponent vectors defining the posynomials;
* core/canonical: `LagrangianProblem (ℝ₊₊^n) m`;
* bridge/view: `qFunction`, `objective`, `constraintFunction`, and `toLagrangianProblem`.

Primitive data:
* `blockSize`;
* `coefficient`;
* `exponent`.

Derived API:
* the posynomials `qFunction`;
* the objective `q₀` and the constraint family `qᵢ`, `i = 1, ..., m`;
* the canonical Chapter 1 bridge `toLagrangianProblem`;
* the feasible-set rewrite `mem_feasibleSet_iff`.

The previous version duplicated both the strict-orthant owner and the feasible-set owner pattern.
This refinement keeps the source-facing geometric-program data, reuses `ℝ₊₊^n` as the domain,
and derives feasibility through the canonical `LagrangianProblem` bridge.
-/

/-- Definition 5.4.8.17: a geometric optimization problem on the strict positive orthant
`\mathbb{R}^n_{++}` is specified by block sizes `m₀, …, mₘ`, positive coefficients `αᵢⱼ`,
and exponent vectors `σᵢⱼ ∈ ℝⁿ`, yielding the posynomials
`qᵢ(x) = \sum_{j=1}^{mᵢ} αᵢⱼ \prod_{k=1}^n (x^(k))^(σᵢⱼ^(k))`; the problem is to minimize
`q₀(x)` subject to the constraints `qᵢ(x) ≤ 1` for `i = 1, …, m`. -/
structure GeometricOptimizationProblem (n m : ℕ) where
  /-- The number `mᵢ` of monomial terms in the posynomial `qᵢ`. -/
  blockSize : Fin (m + 1) → ℕ
  /-- The strictly positive coefficients `αᵢⱼ` multiplying the monomial terms. -/
  coefficient (i : Fin (m + 1)) (j : Fin (blockSize i)) : Set.Ioi (0 : ℝ)
  /-- The exponent vectors `σᵢⱼ ∈ ℝⁿ` of the monomial terms. -/
  exponent (i : Fin (m + 1)) (j : Fin (blockSize i)) (k : Fin n) : ℝ

namespace GeometricOptimizationProblem

variable {n m : ℕ}

local notation "Eₙ" => EuclideanSpace ℝ (Fin n)
local notation "Xₙ" => ℝ₊₊^n

/-- The `i`-th posynomial `qᵢ` of a geometric optimization problem, defined on the strict positive
orthant `\mathbb{R}^n_{++}`. -/
def qFunction (problem : GeometricOptimizationProblem n m) (i : Fin (m + 1)) :
    Xₙ → ℝ :=
  fun x ↦
    ∑ j : Fin (problem.blockSize i), (problem.coefficient i j : ℝ) *
      ∏ k : Fin n, Real.rpow ((x : Eₙ) k) (problem.exponent i j k)

/-- The objective posynomial `q₀` of a geometric optimization problem. -/
abbrev objective (problem : GeometricOptimizationProblem n m) : Xₙ → ℝ :=
  problem.qFunction 0

/-- The `i`-th inequality-constraint posynomial `q_{i+1}`. -/
abbrev constraintFunction (problem : GeometricOptimizationProblem n m) (i : Fin m) :
    Xₙ → ℝ :=
  problem.qFunction i.succ

def toLagrangianProblem (problem : GeometricOptimizationProblem n m) : LagrangianProblem Xₙ m where
  objective := problem.objective
  constraints := fun i x ↦ problem.constraintFunction i x - 1

/-- A geometric optimization problem coerces to its canonical Chapter 1 Lagrangian owner. -/
instance : Coe (GeometricOptimizationProblem n m) (LagrangianProblem Xₙ m) where
  coe := toLagrangianProblem

/-- A geometric optimization problem can be used as its objective posynomial `q₀` on the strict
positive orthant. -/
instance : CoeFun (GeometricOptimizationProblem n m) (fun _ ↦ Xₙ → ℝ) where
  coe problem := problem.objective

/-- The Chapter 1 Lagrangian owner evaluates to the source-facing objective `q₀`. -/
@[simp] theorem toLagrangianProblem_apply
    (problem : GeometricOptimizationProblem n m) (x : Xₙ) :
    problem.toLagrangianProblem x = problem.objective x :=
  rfl

/-- Evaluating a geometric optimization problem returns the source-facing objective `q₀`. -/
@[simp] theorem coe_apply
    (problem : GeometricOptimizationProblem n m) (x : Xₙ) :
    problem x = problem.objective x :=
  rfl

@[simp] theorem toLagrangianProblem_constraints_apply
    (problem : GeometricOptimizationProblem n m) (i : Fin m) (x : Xₙ) :
    (problem : LagrangianProblem Xₙ m).constraints i x =
      problem.constraintFunction i x - 1 :=
  rfl

/-- The feasible set of a geometric optimization problem consists of the strictly positive vectors
`x` satisfying `qᵢ(x) ≤ 1` for every constraint index `i = 1, …, m`. -/
def feasibleSet (problem : GeometricOptimizationProblem n m) : Set Xₙ :=
  problem.toLagrangianProblem.feasibleSet

/-- Expanding `qFunction` recovers the defining posynomial formula
`qᵢ(x) = \sum_j αᵢⱼ \prod_k (x^(k))^(σᵢⱼ^(k))`. -/
theorem qFunction_apply
    (problem : GeometricOptimizationProblem n m) (i : Fin (m + 1)) (x : Xₙ) :
    problem.qFunction i x =
      ∑ j : Fin (problem.blockSize i), (problem.coefficient i j : ℝ) *
        ∏ k : Fin n, Real.rpow ((x : Eₙ) k) (problem.exponent i j k) :=
  rfl

/-- Membership in the feasible set is equivalent to satisfying all geometric-program inequality
constraints `qᵢ(x) ≤ 1` for `i = 1, …, m`. -/
@[simp] theorem mem_feasibleSet_iff
    (problem : GeometricOptimizationProblem n m) (x : Xₙ) :
    x ∈ problem.feasibleSet ↔ ∀ i : Fin m, problem.constraintFunction i x ≤ (1 : ℝ) := by
  rw [feasibleSet]
  constructor
  · intro hx i
    exact sub_nonpos.mp ((problem.toLagrangianProblem.mem_feasibleSet_iff).1 hx i)
  · intro hx
    exact (problem.toLagrangianProblem.mem_feasibleSet_iff).2
      (fun i ↦ sub_nonpos.mpr (hx i))

end GeometricOptimizationProblem

end
