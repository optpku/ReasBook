/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import Mathlib.Tactic.Recall
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap01.Definition_1_3_7
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap04.Definition_4_2_7

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u

open scoped ConstrainedArgmin

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

namespace SetConstrainedMinimizationProblem

/- Definition 4.3.1 lies in the unconstrained second-order minimization domain on complete real
inner-product spaces.

Sampled owner declarations:
* `SetConstrainedMinimizationProblem.unconstrained` in `Chap01/Definition_1_3_3`, the Chapter 1
  owner for whole-space minimization problems;
* `HasLipschitzContinuousHessian`, written on theorem surfaces as `f ∈ C22[L3]`, in
  `Definition_4_2_7`, the Chapter 4 owner for globally Lipschitz Hessian data;
* `argmin[Q]` and `mem_constrainedArgmin_iff` in `Chap01/Definition_1_3_3`, the canonical
  minimizer-set owner for a feasible set;
* `IsMinOn` in mathlib, the canonical minimizer predicate on a set.

Best owner abstraction:
* source-facing: the textbook description of a whole-space problem with Lipschitz Hessian and an
  attained minimum;
* core/canonical: `problem.feasibleSet = Set.univ ∧ ∃ L3 : NNReal, problem.objective ∈ C22[L3]`
  together with `(argmin[problem.feasibleSet] problem).Nonempty`;
* bridge/view: the specialization to `unconstrained f` and the explicit `IsMinOn` reformulations
  below.

Primitive data:
* the constrained problem `problem`;
* the ambient objective `f` when specializing to the whole-space owner `unconstrained f`.

Derived API:
* the Chapter 1 owner `unconstrained f`;
* the Chapter 4 regularity owner surface `problem.objective ∈ C22[L3]`;
* solvability as nonemptiness of the canonical minimizer set.
* the source-style positive-witness reformulation, derived by enlarging any `C22[L3]` witness.

Source/core/bridge triage:
* source-facing: Definition 4.3.1's whole-space Hessian-Lipschitz condition and solvability
  language;
* core/canonical: the conjunction above and `(argmin[problem.feasibleSet] problem).Nonempty`;
* bridge/view: `mem_constrainedArgmin_iff` and the `unconstrained` specialization.

Definition 4.3.1 adds no new owner beyond the Chapter 1 whole-space problem owner, the Chapter 4
`C22[L3]` owner, and the canonical minimizer-set owner. The earlier local class
`IsSecondOrderUnconstrainedWithLipschitzHessian` and alias `IsSolvable` only repackaged those
owners, so this file stays at direct recall/check surface. -/

section

variable (problem : SetConstrainedMinimizationProblem E)

/- The textbook positive-witness form is equivalent to the canonical existential `C22` surface,
since any Hessian-Lipschitz witness can be enlarged to a positive one. -/
theorem exists_pos_mem_C22_iff :
    (∃ L3 : NNReal, 0 < L3 ∧ problem.objective ∈ C22[L3]) ↔
      ∃ L3 : NNReal, problem.objective ∈ C22[L3] := by
  constructor
  · rintro ⟨L3, -, hL3⟩
    exact ⟨L3, hL3⟩
  · rintro ⟨L3, hL3⟩
    refine ⟨max L3 1, zero_lt_one.trans_le (le_max_right _ _), ?_⟩
    exact ⟨hL3.contDiff, hL3.lipschitz.weaken (le_max_left _ _)⟩

/- Definition 4.3.1: a second-order unconstrained minimization problem with Lipschitz Hessian is
exactly a constrained problem whose feasible set is all of `E` and whose objective belongs to
`C22[L3]` for some witness `L3`. The source's strict positivity requirement is the companion
reformulation `problem.exists_pos_mem_C22_iff`, not the main recall surface. -/
set_option linter.hashCommand false in
#check
  (problem.feasibleSet = Set.univ ∧
    ∃ L3 : NNReal, problem.objective ∈ C22[L3])

/- A constrained problem is solvable exactly when its canonical minimizer set is nonempty. -/
set_option linter.hashCommand false in
#check ((argmin[problem.feasibleSet] problem).Nonempty : Prop)

set_option linter.hashCommand false in
#check
  (show
      (argmin[problem.feasibleSet] problem).Nonempty ↔
        ∃ xStar : E, xStar ∈ problem.feasibleSet ∧
          IsMinOn problem problem.feasibleSet xStar from
    by
      constructor
      · rintro ⟨xStar, hxStar⟩
        exact
          ⟨xStar, (mem_constrainedArgmin_iff.mp hxStar).1,
            (mem_constrainedArgmin_iff.mp hxStar).2⟩
      · rintro ⟨xStar, hxFeasible, hxMin⟩
        exact ⟨xStar, (mem_constrainedArgmin_iff).2 ⟨hxFeasible, hxMin⟩⟩)

end

section

variable (f : E → ℝ)

/- The Chapter 1 owner for the whole-space minimization problem with objective `f` is
`unconstrained f`. -/
recall SetConstrainedMinimizationProblem.unconstrained

recall SetConstrainedMinimizationProblem.unconstrained_feasibleSet

recall SetConstrainedMinimizationProblem.unconstrained_apply

set_option linter.hashCommand false in
#check
  (show
      (∃ L3 : NNReal, (unconstrained f).objective ∈ C22[L3]) ↔ ∃ L3 : NNReal, f ∈ C22[L3] from
    Iff.rfl)

set_option linter.hashCommand false in
#check
  (show
      (argmin[(unconstrained f).feasibleSet] (unconstrained f)).Nonempty ↔
        ∃ xStar : E, IsMinOn f Set.univ xStar from
    by
      constructor
      · rintro ⟨xStar, hxStar⟩
        refine ⟨xStar, ?_⟩
        simpa using (mem_constrainedArgmin_iff.mp hxStar).2
      · rintro ⟨xStar, hxStar⟩
        refine ⟨xStar, ?_⟩
        rw [mem_constrainedArgmin_iff]
        exact ⟨by simp, by simpa using hxStar⟩)

end

end SetConstrainedMinimizationProblem
