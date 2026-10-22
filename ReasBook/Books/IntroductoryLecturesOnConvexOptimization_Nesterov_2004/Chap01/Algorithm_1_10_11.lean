/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap01.Definition_1_1_4_1
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap01.Definition_1_10_13
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap01.Definition_1_10_14
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap01.Definition_1_10_21

-- Declarations for this item will be appended below by the statement pipeline.

open Filter Set

universe u

variable {X : Type u} {m : ℕ}

/- Algorithm 1.10.11 lies in the constrained-optimization / sequential-penalization domain.

Sampled owner-style declarations:
* `FunctionalConstraintsMinimizationProblem.feasibleSet` and
  `FunctionalConstraintsMinimizationProblem` in `Chap01/Definition_1_1_3`, which fix the
  feasible-set owner surface for constrained problems;
* `IsPenaltyFunction` in `Chap01/Definition_1_10_14`, the owner predicate for a penalty attached
  to a set;
* `SequentialUnconstrainedMinimizationScheme` in `Chap01/Definition_1_10_13`, the canonical owner
  for iterate sequences minimizing a prescribed family of unconstrained objectives on a fixed
  feasible subtype;
* `BarrierFunctionMethod.toSequentialUnconstrainedMinimizationScheme` in
  `Chap01/Algorithm_1_10_20`, the neighboring source-facing algorithm that bridges to the same
  canonical owner.

Best owner abstraction:
* core/canonical: `SequentialUnconstrainedMinimizationScheme problem.basicFeasibleSet`;
* source-facing: `PenaltyFunctionMethod problem` for
  `problem : FunctionalConstraintsMinimizationProblem X m`;
* bridge/view: `GeneralMinimizationProblem n m` as the Euclidean specialization of that owner.

Primitive data:
* a penalty function on the owner ambient type `problem.basicFeasibleSet`;
* the penalty coefficients;
* the iterate sequence in `problem.basicFeasibleSet`.

Derived API:
* the method-attached penalized objectives `method.penalizedObjective t`;
* the indexed auxiliary objectives `method.auxiliaryObjective k`;
* the owner auxiliary problems `method.auxiliaryProblem k`;
* the bridge `toSequentialUnconstrainedMinimizationScheme`.

Source/core/bridge triage:
* source-facing: `PenaltyFunctionMethod`;
* core/canonical: `SequentialUnconstrainedMinimizationScheme`;
* bridge/view: `toSequentialUnconstrainedMinimizationScheme`.

The feasible-set owner in this chapter is the subtype `problem.basicFeasibleSet`, so the penalty
surface should be attached to `PenaltyFunctionMethod problem` rather than left as a free-standing
ambient wrapper on the Euclidean model. -/

variable [TopologicalSpace X]

/-- Algorithm 1.10.11: a penalty function method for a nonlinear optimization problem with
functional constraints consists of a penalty function `Φ` for the feasible set, penalty
coefficients `tₖ` with `0 < tₖ < tₖ₊₁` and `tₖ → ∞`, and iterates `xₖ ∈ Q` such that each `xₖ`
minimizes the penalized objective `x ↦ f₀(x) + tₖ Φ(x)` on the basic feasible set `Q`. -/
structure PenaltyFunctionMethod
    (problem : FunctionalConstraintsMinimizationProblem X m) where
  penalty : C(problem.basicFeasibleSet, ℝ)
  isPenalty : IsPenaltyFunction problem.feasibleSet penalty
  penaltyCoefficients : ℕ+ → ℝ
  penaltyCoefficients_pos : ∀ k : ℕ+, 0 < penaltyCoefficients k
  penaltyCoefficients_strictMono : StrictMono penaltyCoefficients
  penaltyCoefficients_tendsto_atTop : Tendsto penaltyCoefficients atTop atTop
  iterates : ℕ+ → problem.basicFeasibleSet
  isMinOn_auxiliaryObjective : ∀ k : ℕ+,
    IsMinOn
      (fun x ↦ problem x + penaltyCoefficients k * penalty x)
      univ
      (iterates k)

namespace PenaltyFunctionMethod

variable {problem : FunctionalConstraintsMinimizationProblem X m}

/-- The penalized objective `x ↦ f₀(x) + t Φ(x)` attached to a penalty function method. -/
def penalizedObjective (method : PenaltyFunctionMethod problem) (t : ℝ) :
    problem.basicFeasibleSet → ℝ :=
  fun x ↦ problem x + t * method.penalty x

/-- The `k`-th auxiliary objective attached to a penalty function method. -/
def auxiliaryObjective (method : PenaltyFunctionMethod problem) (k : ℕ+) :
    problem.basicFeasibleSet → ℝ :=
  method.penalizedObjective (method.penaltyCoefficients k)

/-- A penalty function method can be used as its underlying sequence of iterates in the basic
feasible set. -/
instance : CoeFun (PenaltyFunctionMethod problem) (fun _ ↦ ℕ+ → problem.basicFeasibleSet) where
  coe method := method.iterates

/-- The generic sequential unconstrained minimization scheme attached to a penalty function
method. -/
def toSequentialUnconstrainedMinimizationScheme
    (method : PenaltyFunctionMethod problem) :
    SequentialUnconstrainedMinimizationScheme problem.basicFeasibleSet where
  auxiliaryObjectives := method.auxiliaryObjective
  iterates := method
  isMinOn_auxiliaryObjective := method.isMinOn_auxiliaryObjective

/-- The `k`-th auxiliary minimization problem attached to a penalty function method. -/
abbrev auxiliaryProblem (method : PenaltyFunctionMethod problem) (k : ℕ+) :
    SetConstrainedMinimizationProblem problem.basicFeasibleSet :=
  method.toSequentialUnconstrainedMinimizationScheme.auxiliaryProblem k

/-- The optimal value of the `k`-th auxiliary problem is attained at the selected iterate. -/
theorem auxiliaryProblem_optimalValue_eq_iterateValue
    (method : PenaltyFunctionMethod problem) (k : ℕ+) :
    (method.auxiliaryProblem k).optimalValue =
      (method.auxiliaryObjective k (method k) : EReal) :=
  by
    let scheme := method.toSequentialUnconstrainedMinimizationScheme
    simpa [PenaltyFunctionMethod.auxiliaryProblem] using
      scheme.auxiliaryProblem_optimalValue_eq_iterateValue k

end PenaltyFunctionMethod
