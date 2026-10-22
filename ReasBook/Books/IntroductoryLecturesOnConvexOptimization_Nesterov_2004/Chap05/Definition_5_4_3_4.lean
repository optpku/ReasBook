/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap02.Example_2_1_1_2
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Definition_3_3
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Definition_5_0_1

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

variable {n m : ℕ}

/- Definition 5.4.3.4 lies in the Chapter 5 QCQP / convex inequality optimization domain.

Sampled owner declarations in this domain:
* `quadraticObjective` from `Chap01/Definition_1_9_1`, the chapter owner for Euclidean
  quadratic-affine functions;
* `Matrix.PosSemidef.convexOn_quadraticObjective` from `Chap02/Example_2_1_1_2`, the derived
  convexity owner for quadratic objectives with positive-semidefinite Hessian;
* `LagrangianProblem` from `Chap01/Definition_1_10_2`, the canonical owner for whole-space
  `≤ 0` constraints;
* `ConvexInequalityConstrainedMinimizationProblem` from `Definition_5_0_1`, the Chapter 5 owner
  for convex whole-space inequality minimization;
* `SetConstrainedMinimizationProblem` from `Chap01/Definition_1_3_3`, the Chapter 1 owner for a
  feasible set together with its objective;
* `constrainedEpigraph` from `Chap03/Definition_3_3`, the chapter owner for epigraph regions.

Source/core/bridge triage:
* source-facing: `QuadraticallyConstrainedQuadraticOptimizationProblem n m`;
* core/canonical: `LagrangianProblem Eₙ m`,
  `ConvexInequalityConstrainedMinimizationProblem n m`,
  `SetConstrainedMinimizationProblem (Eₙ × ℝ)`, and `constrainedEpigraph`;
* bridge/view: the derived function family `quadraticFunction`, the owner bridges
  `toLagrangianProblem` / `toConvexInequalityConstrainedMinimizationProblem`, and the
  epigraph optimization owner together with its feasible-set view.

Primitive data:
* the scalar terms `αᵢ`;
* the linear coefficients `aᵢ`;
* the quadratic matrices `Aᵢ`;
* the positive-semidefinite witnesses for `Aᵢ`;
* the constraint bounds `βᵢ`.

Derived API:
* the textbook quadratic family `qᵢ`;
* the objective and constraint functions;
* convexity of those derived functions;
* the canonical owner bridges and feasible-set API;
* the epigraph optimization owner and its feasible-set view via `constrainedEpigraph`.

The refinement keeps the source-facing QCQP data as the owner, but removes the lower-level
`GeneralMinimizationProblem` packaging and exposes the epigraph reformulation through the exact
Chapter 1/5 owners already used elsewhere in the chapter. -/

/-- Definition 5.4.3.4: A quadratically constrained quadratic optimization problem on `ℝⁿ`
consists of quadratic functions `q₀, …, q_m` with positive-semidefinite quadratic parts and
constraint bounds `β₁, …, β_m`; the problem is to minimize `q₀` subject to `qᵢ(x) ≤ βᵢ` for
`i = 1, …, m`, and it admits the equivalent epigraph reformulation using an auxiliary scalar
variable `τ`. -/
structure QuadraticallyConstrainedQuadraticOptimizationProblem (n m : ℕ) where
  α : Fin (m + 1) → ℝ
  a : Fin (m + 1) → EuclideanSpace ℝ (Fin n)
  A : Fin (m + 1) → Matrix (Fin n) (Fin n) ℝ
  A_posSemidef : ∀ i : Fin (m + 1), (A i).PosSemidef
  β : Fin m → ℝ

namespace QuadraticallyConstrainedQuadraticOptimizationProblem

local notation "Eₙ" => EuclideanSpace ℝ (Fin n)

/-- The `i`-th quadratic function `qᵢ` of a QCQP. -/
abbrev quadraticFunction (problem : QuadraticallyConstrainedQuadraticOptimizationProblem n m)
    (i : Fin (m + 1)) : Eₙ → ℝ :=
  quadraticObjective (problem.α i) (problem.a i) (problem.A i)

/-- The objective function `q₀` of a QCQP. -/
abbrev objective (problem : QuadraticallyConstrainedQuadraticOptimizationProblem n m) :
    Eₙ → ℝ :=
  problem.quadraticFunction 0

/-- The `i`-th constraint function `q_{i+1}` of a QCQP. -/
abbrev constraintFunction (problem : QuadraticallyConstrainedQuadraticOptimizationProblem n m)
    (i : Fin m) : Eₙ → ℝ :=
  problem.quadraticFunction i.succ

/-- A QCQP can be used as its objective function `q₀`. -/
instance : CoeFun (QuadraticallyConstrainedQuadraticOptimizationProblem n m)
    (fun _ ↦ Eₙ → ℝ) where
  coe problem := problem.objective

/-- Evaluating a QCQP returns its objective value `q₀(x)`. -/
@[simp] theorem coe_apply (problem : QuadraticallyConstrainedQuadraticOptimizationProblem n m)
    (x : Eₙ) :
    problem x = problem.objective x :=
  rfl

/-- Each quadratic function of a QCQP is convex on all of `ℝⁿ`. -/
theorem quadraticFunction_convex
    (problem : QuadraticallyConstrainedQuadraticOptimizationProblem n m) (i : Fin (m + 1)) :
    ConvexOn ℝ Set.univ (problem.quadraticFunction i) :=
  (problem.A_posSemidef i).convexOn_quadraticObjective (problem.α i) (problem.a i)

/-- The objective function `q₀` of a QCQP is convex on all of `ℝⁿ`. -/
theorem objective_convex
    (problem : QuadraticallyConstrainedQuadraticOptimizationProblem n m) :
    ConvexOn ℝ Set.univ problem.objective := by
  simpa [objective] using problem.quadraticFunction_convex 0

/-- Each constraint function `q_{i+1}` of a QCQP is convex on all of `ℝⁿ`. -/
theorem constraintFunction_convex
    (problem : QuadraticallyConstrainedQuadraticOptimizationProblem n m) (i : Fin m) :
    ConvexOn ℝ Set.univ (problem.constraintFunction i) := by
  simpa [constraintFunction] using problem.quadraticFunction_convex i.succ

/-- The canonical Chapter 1 Lagrangian owner attached to a QCQP. -/
def toLagrangianProblem
    (problem : QuadraticallyConstrainedQuadraticOptimizationProblem n m) :
    LagrangianProblem Eₙ m where
  objective := problem.objective
  constraints := fun i x ↦ problem.constraintFunction i x - problem.β i

/-- A QCQP coerces to its canonical Chapter 1 Lagrangian owner. -/
instance : Coe (QuadraticallyConstrainedQuadraticOptimizationProblem n m)
    (LagrangianProblem Eₙ m) where
  coe := toLagrangianProblem

/-- The Chapter 1 owner evaluates to the QCQP objective `q₀`. -/
@[simp] theorem toLagrangianProblem_apply
    (problem : QuadraticallyConstrainedQuadraticOptimizationProblem n m) (x : Eₙ) :
    problem.toLagrangianProblem x = problem.objective x :=
  rfl

@[simp] theorem toLagrangianProblem_constraints_apply
    (problem : QuadraticallyConstrainedQuadraticOptimizationProblem n m)
    (i : Fin m) (x : Eₙ) :
    (problem : LagrangianProblem Eₙ m).constraints i x =
      problem.constraintFunction i x - problem.β i :=
  rfl

/-- The canonical Chapter 5 convex inequality owner attached to a QCQP. -/
def toConvexInequalityConstrainedMinimizationProblem
    (problem : QuadraticallyConstrainedQuadraticOptimizationProblem n m) :
    ConvexInequalityConstrainedMinimizationProblem n m where
  objective := problem.objective
  constraints := fun i x ↦ problem.constraintFunction i x - problem.β i
  objective_convex := problem.objective_convex
  constraints_convex i := by
    simpa [sub_eq_add_neg] using (problem.constraintFunction_convex i).add_const (-problem.β i)

/-- A QCQP coerces to its canonical Chapter 5 convex inequality owner. -/
instance : Coe (QuadraticallyConstrainedQuadraticOptimizationProblem n m)
    (ConvexInequalityConstrainedMinimizationProblem n m) where
  coe := toConvexInequalityConstrainedMinimizationProblem

/-- The Chapter 5 owner evaluates to the QCQP objective `q₀`. -/
@[simp] theorem toConvexInequalityConstrainedMinimizationProblem_apply
    (problem : QuadraticallyConstrainedQuadraticOptimizationProblem n m) (x : Eₙ) :
    problem.toConvexInequalityConstrainedMinimizationProblem x = problem.objective x :=
  rfl

@[simp] theorem toConvexInequalityConstrainedMinimizationProblem_constraints_apply
    (problem : QuadraticallyConstrainedQuadraticOptimizationProblem n m)
    (i : Fin m) (x : Eₙ) :
    (problem : ConvexInequalityConstrainedMinimizationProblem n m).constraints i x =
      problem.constraintFunction i x - problem.β i :=
  rfl

/-- The feasible set `\{x : qᵢ(x) ≤ βᵢ \text{ for } i = 1, …, m\}` of a QCQP. -/
def feasibleSet (problem : QuadraticallyConstrainedQuadraticOptimizationProblem n m) :
    Set Eₙ :=
  problem.toLagrangianProblem.feasibleSet

/-- Membership in the feasible set of a QCQP is exactly the family of constraint inequalities
`qᵢ(x) ≤ βᵢ`. -/
@[simp] theorem mem_feasibleSet_iff
    (problem : QuadraticallyConstrainedQuadraticOptimizationProblem n m) (x : Eₙ) :
    x ∈ problem.feasibleSet ↔ ∀ i : Fin m, problem.constraintFunction i x ≤ problem.β i := by
  constructor
  · intro hx i
    exact sub_nonpos.mp ((problem.toLagrangianProblem.mem_feasibleSet_iff).1 hx i)
  · intro hx
    exact (problem.toLagrangianProblem.mem_feasibleSet_iff).2
      (fun i ↦ sub_nonpos.mpr (hx i))

/-- The canonical Chapter 1 epigraph reformulation of a QCQP in the variables `(x, τ)`, whose
objective is the auxiliary scalar `τ`. -/
def epigraphOptimizationProblem
    (problem : QuadraticallyConstrainedQuadraticOptimizationProblem n m) :
    SetConstrainedMinimizationProblem (Eₙ × ℝ) where
  feasibleSet := constrainedEpigraph problem.feasibleSet
    fun x ↦ (problem.objective x : WithTop ℝ)
  objective := Prod.snd

/-- Evaluating the QCQP epigraph owner returns the auxiliary variable `τ`. -/
@[simp] theorem epigraphOptimizationProblem_apply
    (problem : QuadraticallyConstrainedQuadraticOptimizationProblem n m) (x : Eₙ) (τ : ℝ) :
    problem.epigraphOptimizationProblem (x, τ) = τ :=
  rfl

/-- The feasible set of the equivalent epigraph formulation of a QCQP in the variables `(x, τ)`. -/
def epigraphFeasibleSet (problem : QuadraticallyConstrainedQuadraticOptimizationProblem n m) :
    Set (Eₙ × ℝ) :=
  problem.epigraphOptimizationProblem.feasibleSet

/-- The epigraph owner preserves the QCQP epigraph feasible set. -/
theorem epigraphOptimizationProblem_feasibleSet
    (problem : QuadraticallyConstrainedQuadraticOptimizationProblem n m) :
    problem.epigraphOptimizationProblem.feasibleSet = problem.epigraphFeasibleSet :=
  rfl

/-- Membership in the feasible set of the QCQP epigraph optimization owner is the objective
epigraph inequality together with feasibility of the base point. -/
@[simp] theorem mem_epigraphOptimizationProblem_feasibleSet_iff
    (problem : QuadraticallyConstrainedQuadraticOptimizationProblem n m) (xτ : Eₙ × ℝ) :
    xτ ∈ problem.epigraphOptimizationProblem.feasibleSet ↔
      problem.objective xτ.1 ≤ xτ.2 ∧
        ∀ i : Fin m, problem.constraintFunction i xτ.1 ≤ problem.β i := by
  change xτ ∈ constrainedEpigraph problem.feasibleSet
      (fun x ↦ (problem.objective x : WithTop ℝ)) ↔
    problem.objective xτ.1 ≤ xτ.2 ∧
      ∀ i : Fin m, problem.constraintFunction i xτ.1 ≤ problem.β i
  rw [mem_constrainedEpigraph_iff]
  constructor
  · rintro ⟨hx, hτ⟩
    exact ⟨by simpa using hτ, (problem.mem_feasibleSet_iff xτ.1).1 hx⟩
  · rintro ⟨hτ, hx⟩
    exact ⟨(problem.mem_feasibleSet_iff xτ.1).2 hx, by simpa using hτ⟩

/-- Membership in the QCQP epigraph feasible set is the objective epigraph inequality together
with feasibility of the base point. -/
@[simp] theorem mem_epigraphFeasibleSet_iff
    (problem : QuadraticallyConstrainedQuadraticOptimizationProblem n m) (xτ : Eₙ × ℝ) :
    xτ ∈ problem.epigraphFeasibleSet ↔
      problem.objective xτ.1 ≤ xτ.2 ∧
        ∀ i : Fin m, problem.constraintFunction i xτ.1 ≤ problem.β i := by
  simpa [epigraphFeasibleSet] using problem.mem_epigraphOptimizationProblem_feasibleSet_iff xτ

end QuadraticallyConstrainedQuadraticOptimizationProblem
