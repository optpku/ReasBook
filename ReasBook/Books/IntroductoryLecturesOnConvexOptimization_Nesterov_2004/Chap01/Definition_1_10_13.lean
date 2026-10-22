/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap01.Definition_1_3_7

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u

/- Definition 1.10.13 lies in the Chapter 1 constrained/unconstrained minimization domain.

Sampled owner-style declarations:
* `IsMinOn f Set.univ x` in mathlib, the canonical whole-space minimizer predicate;
* `SetConstrainedMinimizationProblem` in `Chap01/Definition_1_3_3`, the Chapter 1 owner for a
  feasible set together with its real-valued objective;
* `SetConstrainedMinimizationProblem.optimalValue` and
  `SetConstrainedMinimizationProblem.optimalValue_eq_of_isMinOn` in `Chap01/Definition_1_3_7`,
  the derived optimal-value API for that owner object;
* `PenaltyFunctionMethod.toSequentialUnconstrainedMinimizationScheme` in
  `Chap01/Algorithm_1_10_11`, the nearby source-facing algorithm that bridges to this scheme
  owner.

Best owner abstraction:
* source-facing: `SequentialUnconstrainedMinimizationScheme Q`;
* core/canonical: for each index `k`, the Chapter 1 owner
  `SetConstrainedMinimizationProblem Q` specialized to feasible set `Set.univ`;
* bridge/view: the canonical owner problem `scheme.auxiliaryProblem k`.

Primitive data:
* the auxiliary objective family `Φₖ : Q → ℝ`;
* the iterate family `xₖ : Q`;
* the minimizing certificates `IsMinOn (Φₖ) Set.univ xₖ`.

Derived API:
* the associated Chapter 1 owner problem on the subtype `Q`;
* its optimal value and attained-value identities.

Source/core/bridge triage:
* source-facing: the sequential unconstrained minimization scheme itself;
* core/canonical: `SetConstrainedMinimizationProblem Q`;
* bridge/view: packaging each `Φₖ` as the owner problem with feasible set `Set.univ`.

The file therefore keeps the source-facing scheme structure and reuses the Chapter 1 owner object
directly for optimal-value language, instead of introducing a parallel public auxiliary-problem
wrapper. -/

/-- Definition 1.10.13: A sequential unconstrained minimization scheme for a nonlinear
optimization problem with functional constraints consists of auxiliary unconstrained objective
functions `Φₖ : Q → ℝ` and iterates `xₖ ∈ Q` such that each `xₖ` minimizes `Φₖ` on `Q`. The
owner abstraction is the intrinsic feasible type `Q`; any surrounding constrained-problem package
or ambient-set presentation is auxiliary context used only when specializing this generic scheme.
The auxiliary objectives are intended to approximate a solution of the original constrained
problem.
-/
structure SequentialUnconstrainedMinimizationScheme (Q : Type u) where
  auxiliaryObjectives : ℕ+ → Q → ℝ
  iterates : ℕ+ → Q
  isMinOn_auxiliaryObjective (k : ℕ+) :
    IsMinOn (auxiliaryObjectives k) Set.univ (iterates k)

namespace SequentialUnconstrainedMinimizationScheme

variable {Q : Type u}

/-- A sequential unconstrained minimization scheme can be used as its underlying sequence of
iterates in the feasible-set subtype. -/
instance :
    CoeFun (SequentialUnconstrainedMinimizationScheme Q) (fun _ ↦ ℕ+ → Q) where
  coe scheme := scheme.iterates

/-- The `k`-th auxiliary minimization problem attached to a sequential unconstrained
minimization scheme. This is the canonical Chapter 1 owner problem on the feasible-set subtype
`Q`, with feasible set `Set.univ`. -/
abbrev auxiliaryProblem (scheme : SequentialUnconstrainedMinimizationScheme Q) (k : ℕ+) :
    SetConstrainedMinimizationProblem Q :=
  .unconstrained (scheme.auxiliaryObjectives k)

/-- The optimal value of the `k`-th auxiliary problem is attained at the selected iterate. -/
theorem auxiliaryProblem_optimalValue_eq_iterateValue
    (scheme : SequentialUnconstrainedMinimizationScheme Q) (k : ℕ+) :
    (scheme.auxiliaryProblem k).optimalValue =
      (scheme.auxiliaryObjectives k (scheme k) : EReal) :=
  by
    simpa [auxiliaryProblem] using
      (scheme.auxiliaryProblem k).optimalValue_eq_of_isMinOn
        (by simp)
        (scheme.isMinOn_auxiliaryObjective k)

end SequentialUnconstrainedMinimizationScheme
