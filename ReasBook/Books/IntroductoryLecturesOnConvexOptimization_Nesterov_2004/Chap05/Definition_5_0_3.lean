/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap01.Definition_1_4_3

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u

open scoped Gradient
open FunctionalConstraintsMinimizationProblem

namespace SetConstrainedMinimizationProblem

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-
Definition 5.0.3 lies in the unconstrained twice-differentiable minimization domain on complete
real inner-product spaces.

Sampled owner declarations:
- `SetConstrainedMinimizationProblem` in `Chap01/Definition_1_3_3`, the project owner for the
  primitive feasible-set/objective data of an ambient real-valued minimization problem;
- `SetConstrainedMinimizationProblem.toFunctionalConstraintsMinimizationProblem` in
  `Chap01/Definition_1_3_3`, the canonical bridge from a set-constrained problem to the generic
  functional-constraint owner with zero scalar constraints;
- `FunctionalConstraintsMinimizationProblem.IsConstrained` and
  `FunctionalConstraintsMinimizationProblem.not_isConstrained_iff_feasibleSet_eq_univ` in
  `Chap01/Definition_1_1_4_1`, the generic owner predicate and whole-space bridge for
  constrainedness;
- `SetConstrainedMinimizationProblem.unconstrainedSmooth_iff` in `Chap01/Definition_1_4_3`, the
  earlier chapter pattern of keeping unconstrainedness on the owner surface and whole-space
  equalities as companion bridge API.

Best owner abstraction:
- source-facing/core:
  `¬ problem.toFunctionalConstraintsMinimizationProblem.IsConstrained ∧
    Differentiable ℝ problem.objective ∧
    Differentiable ℝ (∇ problem.objective)`;
- bridge/view:
  `problem.feasibleSet = Set.univ ∧
    Differentiable ℝ problem.objective ∧
    Differentiable ℝ (∇ problem.objective)`.

Primitive data:
- `problem.feasibleSet`
- `problem.objective`

Derived API:
- the generic-owner unconstrained-and-twice-differentiable expression above;
- the whole-space reformulation `twiceDifferentiableUnconstrained_iff`.

Source/core/bridge triage:
- source-facing: the unconstrained twice-differentiable minimization problem;
- core/canonical: `SetConstrainedMinimizationProblem E` together with the zero-constraint bridge
  owner `problem.toFunctionalConstraintsMinimizationProblem.IsConstrained` and the regularity
  layer `Differentiable ℝ problem.objective ∧ Differentiable ℝ (∇ problem.objective)`;
- bridge/view: the reformulation `problem.feasibleSet = Set.univ`.

Definition 5.0.3 does not need a Euclidean coordinate model: the source notion is intrinsic to the
ambient real Hilbert space. The public core therefore lives on `SetConstrainedMinimizationProblem
E`, while the whole-space formulation is kept only as a companion bridge theorem.
-/

variable (problem : SetConstrainedMinimizationProblem E)

/- Definition 5.0.3: an unconstrained twice-differentiable minimization problem is a
set-constrained minimization problem whose canonical zero-constraint owner is unconstrained and
whose objective is differentiable with differentiable gradient on the ambient space. -/
#check (
  ¬ problem.toFunctionalConstraintsMinimizationProblem.IsConstrained ∧
    Differentiable ℝ problem.objective ∧
    Differentiable ℝ (∇ problem.objective)
)

section

variable {problem : SetConstrainedMinimizationProblem E}

/-- The canonical owner expression for Definition 5.0.3 is equivalent to the textbook whole-space
twice-differentiability formulation. -/
theorem twiceDifferentiableUnconstrained_iff :
    (¬ problem.toFunctionalConstraintsMinimizationProblem.IsConstrained ∧
      Differentiable ℝ problem.objective ∧
      Differentiable ℝ (∇ problem.objective)) ↔
      problem.feasibleSet = Set.univ ∧
        Differentiable ℝ problem.objective ∧
        Differentiable ℝ (∇ problem.objective) := by
  have hiff :
      ¬ problem.toFunctionalConstraintsMinimizationProblem.IsConstrained ↔
        ((problem.toFunctionalConstraintsMinimizationProblem.feasibleSet : Set E) = Set.univ) :=
    not_isConstrained_iff_feasibleSet_eq_univ
  constructor
  · rintro ⟨hunconstrained, hdiff, hgradDiff⟩
    refine ⟨?_, hdiff, hgradDiff⟩
    simpa using hiff.mp hunconstrained
  · rintro ⟨hfeasible, hdiff, hgradDiff⟩
    refine ⟨?_, hdiff, hgradDiff⟩
    exact hiff.mpr <| by
      simpa using hfeasible

end

end SetConstrainedMinimizationProblem

end
