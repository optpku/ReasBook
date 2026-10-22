/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap01.Definition_1_3_3

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open MeasureTheory
open scoped ProbabilityTheory

universe u v w

section

variable (X : Type u) [MeasurableSpace X]
variable (Ω : Type v) [MeasurableSpace Ω]
variable (Ξ : Type w) [MeasurableSpace Ξ]

/-
Definition 7.79 lies in the constrained stochastic-programming domain.

Mandatory domain-style sampling before refinement:
- `ProbabilityMeasure` and `IsProbabilityMeasure` in mathlib's measure-theoretic probability API,
  the canonical owner for a probability law;
- `AffineVariationalInequalityProblem.gapProblem` in `Chap06/Definition_6_18`, the project
  pattern for a source-facing optimization object whose canonical Chapter 1 bridge lives on the
  feasible subtype;
- `SetConstrainedMinimizationProblem` in `Chap01/Definition_1_3_3`, the project owner for a
  feasible set together with a real-valued objective;
- `IsMaxOn` and `isMaxOn_iff` in mathlib's extremum API, the canonical owner for maximization on
  a set;
- `LinearPackingProblem.toSetConstrainedMinimizationProblem` in `Chap07/Definition_7_41`, the
  nearby chapter pattern for representing a maximization problem canonically via a negated
  minimization bridge.

Best owner abstraction:
- source-facing: `OneStageStochasticProgram X Ω Ξ`;
- core/canonical: `ProbabilityMeasure Ω` for the probability law,
  `SetConstrainedMinimizationProblem problem.feasibleSet` for the expected-payoff optimization
  owner on feasible decisions, and `IsMaxOn problem Set.univ` for optimality;
- bridge/view: `realizedPayoff`, `expectedPayoff`, and `toSetConstrainedMinimizationProblem`.

Primitive data:
- the feasible set of static decisions;
- the probability law, random input, payoff, and the measurability/integrability hypotheses needed
  to define the expected payoff on feasible decisions.

Derived API:
- the realized payoff `ω ↦ payoff x ξ(ω)` of a feasible decision;
- the expected-payoff objective on the feasible subtype;
- the Chapter 1 constrained-minimization bridge with negated objective on the feasible subtype;
- the source optimality notion expressed directly through `IsMaxOn problem Set.univ`;
- the explicit quantified optimality form via `isMaxOn_univ_iff`.

Source/core/bridge triage:
- source-facing: `OneStageStochasticProgram` and the expected-payoff / optimal-static-decision
  surfaces below;
- core/canonical: `ProbabilityMeasure`, `SetConstrainedMinimizationProblem`, and `IsMaxOn`;
- bridge/view: `realizedPayoff`, `expectedPayoff`, `toSetConstrainedMinimizationProblem`, and the
  companion equivalence theorems below.

The textbook presents the random vector in `ℝ^m`, but the mathematical content used here only
needs a measurable input space. This refinement therefore keeps the same source meaning while
moving the stochastic-input layer to the intrinsic measurable-space owner level; the textbook case
is recovered by specializing `Ξ` to `EuclideanSpace ℝ (Fin m)`.
-/

/-- Definition 7.79: a one-stage stochastic programming problem consists of a feasible set of
static decisions, a probability law, a measurable random input `ζ`, and a jointly measurable
payoff function whose expectation is well-defined for every feasible decision. The textbook `ℝ^m`
random-vector presentation is the specialization to `Ξ = EuclideanSpace ℝ (Fin m)`. -/
structure OneStageStochasticProgram where
  /-- The probability law governing the sample space. -/
  law : ProbabilityMeasure Ω
  /-- The feasible set of static decisions. -/
  feasibleSet : Set X
  /-- The random input entering the payoff. -/
  randomVector : Ω → Ξ
  /-- The random input is a measurable random variable. -/
  measurable_randomVector : Measurable randomVector
  /-- The stage payoff as a function of the decision and the realized random input. -/
  payoff : X → Ξ → ℝ
  /-- The payoff is jointly measurable in the decision and random inputs. -/
  measurable_payoff : Measurable fun p : X × Ξ ↦ payoff p.1 p.2
  /-- The realized payoff is integrable for every feasible static decision. -/
  integrable_payoff (x : feasibleSet) :
    Integrable (fun ω ↦ payoff x.1 (randomVector ω)) (law : Measure Ω)

namespace OneStageStochasticProgram

variable {X : Type u} [MeasurableSpace X]
variable {Ω : Type v} [MeasurableSpace Ω]
variable {Ξ : Type w} [MeasurableSpace Ξ]

/-- The realized payoff of a feasible static decision under the program's random input. -/
def realizedPayoff (problem : OneStageStochasticProgram X Ω Ξ)
    (x : problem.feasibleSet) : Ω → ℝ :=
  fun ω ↦ problem.payoff x.1 (problem.randomVector ω)

/-- Evaluating the realized payoff at `ω` gives the stage payoff at the realized input
`randomVector ω`. -/
@[simp] theorem realizedPayoff_apply
    (problem : OneStageStochasticProgram X Ω Ξ) (x : problem.feasibleSet) (ω : Ω) :
    problem.realizedPayoff x ω = problem.payoff x.1 (problem.randomVector ω) :=
  rfl

/-- The realized payoff is measurable because the payoff is jointly measurable and the random
input is measurable. -/
theorem measurable_realizedPayoff
    (problem : OneStageStochasticProgram X Ω Ξ) (x : problem.feasibleSet) :
    Measurable (problem.realizedPayoff x) := by
  simpa [realizedPayoff] using
    problem.measurable_payoff.comp
      (measurable_const.prodMk problem.measurable_randomVector)

/-- The realized payoff is integrable for every feasible decision. -/
theorem integrable_realizedPayoff
    (problem : OneStageStochasticProgram X Ω Ξ) (x : problem.feasibleSet) :
    Integrable (problem.realizedPayoff x) (problem.law : Measure Ω) := by
  simpa [realizedPayoff] using problem.integrable_payoff x

/-- The expected payoff of a feasible static decision is the expectation of its realized payoff
under the program's probability law. -/
def expectedPayoff (problem : OneStageStochasticProgram X Ω Ξ)
    (x : problem.feasibleSet) : ℝ :=
  problem.law[problem.realizedPayoff x]

/-- A one-stage stochastic program can be used as its expected-payoff objective on feasible
decisions. -/
instance : CoeFun (OneStageStochasticProgram X Ω Ξ) (fun problem ↦ problem.feasibleSet → ℝ) where
  coe problem := problem.expectedPayoff

@[simp] theorem coe_apply
    (problem : OneStageStochasticProgram X Ω Ξ) (x : problem.feasibleSet) :
    problem x = problem.expectedPayoff x :=
  rfl

/-- The expected payoff is computed by integrating the realized payoff against the program's
probability law. -/
@[simp] theorem expectedPayoff_eq_integral
    (problem : OneStageStochasticProgram X Ω Ξ) (x : problem.feasibleSet) :
    problem.expectedPayoff x =
      ∫ ω, problem.payoff x.1 (problem.randomVector ω) ∂(problem.law : Measure Ω) := by
  simp [expectedPayoff, realizedPayoff]

/-- The canonical Chapter 1 constrained-minimization owner attached to a one-stage stochastic
program, using the negated expected payoff on the feasible subtype so that expected-payoff
maximization is expressed canonically through minimization. -/
def toSetConstrainedMinimizationProblem
    (problem : OneStageStochasticProgram X Ω Ξ) :
    SetConstrainedMinimizationProblem problem.feasibleSet where
  feasibleSet := Set.univ
  objective := fun x ↦ -problem x

@[simp] theorem toSetConstrainedMinimizationProblem_feasibleSet
    (problem : OneStageStochasticProgram X Ω Ξ) :
    problem.toSetConstrainedMinimizationProblem.feasibleSet = Set.univ :=
  rfl

@[simp] theorem toSetConstrainedMinimizationProblem_apply
    (problem : OneStageStochasticProgram X Ω Ξ) (x : problem.feasibleSet) :
    problem.toSetConstrainedMinimizationProblem x = -problem x :=
  rfl

/-- The negated Chapter 1 owner is minimized exactly at the expected-payoff maximizers on the
feasible-decision type. -/
theorem isMinOn_toSetConstrainedMinimizationProblem_iff
    (problem : OneStageStochasticProgram X Ω Ξ) (xStar : problem.feasibleSet) :
    IsMinOn problem.toSetConstrainedMinimizationProblem
        problem.toSetConstrainedMinimizationProblem.feasibleSet xStar ↔
      IsMaxOn problem Set.univ xStar := by
  constructor
  · intro hx
    simpa [toSetConstrainedMinimizationProblem] using hx.neg
  · intro hx
    simpa [toSetConstrainedMinimizationProblem] using hx.neg

section Optimality

variable (problem : OneStageStochasticProgram X Ω Ξ) (xStar : problem.feasibleSet)

/- Definition 7.79: a feasible static decision is optimal exactly when it maximizes the expected
payoff on the feasible-decision type. The canonical owner surface is `IsMaxOn problem Set.univ`. -/
set_option linter.hashCommand false in
#check (IsMaxOn problem Set.univ xStar)

end Optimality

/-- A feasible static decision is optimal exactly when its expected payoff dominates the expected
payoff of every feasible decision. -/
theorem isOptimalStaticDecision_iff
    (problem : OneStageStochasticProgram X Ω Ξ) (xStar : problem.feasibleSet) :
    IsMaxOn problem Set.univ xStar ↔ ∀ x, problem x ≤ problem xStar := by
  simpa using (isMaxOn_univ_iff : IsMaxOn problem Set.univ xStar ↔ _)

end OneStageStochasticProgram

end
