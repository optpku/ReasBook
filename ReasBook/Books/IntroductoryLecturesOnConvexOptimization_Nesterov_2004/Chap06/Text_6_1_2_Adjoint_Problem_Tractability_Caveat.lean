/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap01.Definition_1_3_3
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap06.Definition_6_6

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u v

open scoped ConstrainedArgmin

/- Text 6.1.2 lies in the chapter's structured saddle-value / constrained-argmin domain.

Mandatory domain-style sampling before refinement:
- `StructuredObjectiveModel.adjointObjective` in `Chap06/Definition_6_6`, the chapter owner for
  the adjoint value function on `Q₂`, canonically valued in `EReal`;
- `StructuredObjectiveModel.saddleFunction` in `Chap06/Definition_6_6`, the canonical saddle
  slice whose infimum defines the adjoint objective;
- `constrainedArgmin` with notation `argmin[Q] f` in `Chap01/Definition_1_3_3`, the project owner
  for minimizers over a feasible set;
- `cubicRegularizationValue_eq_of_mem_argmin` in `Chap04/Definition_4_1_3`, a chapter-level
  attained-infimum bridge stated directly from `argmin` membership instead of a selector package.

Source/core/bridge triage:
- source-facing: for a fixed `u ∈ Q₂`, evaluating `φ(u)` requires solving the inner minimization
  problem on `Q₁`;
- core/canonical: `problem.adjointObjective u`, `problem.saddleFunction x u`, and
  `argmin[problem.primalSet]
    (fun x ↦ (problem.smoothPart x + problem.linearMap x u - problem.dualPenalty u : EReal))`;
- bridge/view: an attained-inner-minimum theorem identifying `problem.adjointObjective u` with the
  saddle value at a pointwise argmin.

Primitive data:
- `problem : StructuredObjectiveModel E₁ E₂`;
- `u : problem.dualSet`;
- `x : problem.primalSet`;
- the minimizer witness
  `IsMinOn
    (fun y : E₁ ↦
      (problem.smoothPart y + problem.linearMap y u - problem.dualPenalty u : EReal))
    problem.primalSet x`.

Derived API:
- the induced equality `problem.adjointObjective u = problem.saddleFunction x u`;
- the expanded textbook formula as a thin `EReal` companion;
- the `argmin`-surface corollary for a primal feasible point whose ambient representative lies in
  the canonical argmin set.

The previous version used the later specialized owner `PrimalDualObjectiveModel`. This refinement
moves Text 6.1.2 down to the chapter's canonical owner `StructuredObjectiveModel`, keeps the main
bridge directly on `adjointObjective`, `saddleFunction`, and `argmin`, and leaves the expanded
formula as a thin companion in the chapter's `EReal` encoding.
-/

namespace StructuredObjectiveModel

variable {E₁ : Type u} {E₂ : Type v}
  [NormedAddCommGroup E₁] [NormedSpace ℝ E₁]
  [NormedAddCommGroup E₂] [NormedSpace ℝ E₂]

/-- Text 6.1.2-Adjoint Problem Tractability Caveat: for a fixed `u ∈ Q₂`, any point of the
fixed-`u` saddle slice `x ↦ Ψ(x, u)` over `Q₁` evaluates the adjoint objective `φ(u)` via the
chapter's `EReal` owner. -/
theorem adjointObjective_eq_saddleFunction_of_isMinOn
    {problem : StructuredObjectiveModel E₁ E₂}
    {u : problem.dualSet} {x : problem.primalSet}
    (hx : IsMinOn
      (fun y : E₁ ↦
        (problem.smoothPart y + problem.linearMap y u - problem.dualPenalty u : EReal))
      problem.primalSet x) :
    problem.adjointObjective u = (problem.saddleFunction x u : EReal) := by
  rw [isMinOn_iff] at hx
  have hsaddleLeast :
      IsLeast
        (Set.range fun y : problem.primalSet ↦ (problem.saddleFunction y u : EReal))
        (problem.saddleFunction x u : EReal) := by
    refine ⟨⟨x, rfl⟩, ?_⟩
    rintro _ ⟨y, rfl⟩
    exact (hx y y.property).trans_eq <| by simp [saddleFunction]
  rw [problem.adjointObjective_apply]
  exact hsaddleLeast.csInf_eq

/-- A primal feasible point whose ambient representative belongs to the canonical argmin set of
the fixed-`u` saddle slice evaluates the adjoint objective `φ(u)` via the chapter's `EReal`
owner. -/
theorem adjointObjective_eq_saddleFunction_of_mem_argmin
    {problem : StructuredObjectiveModel E₁ E₂}
    {u : problem.dualSet} {x : problem.primalSet}
    (hx : (x : E₁) ∈
      argmin[problem.primalSet]
        (fun y : E₁ ↦
          (problem.smoothPart y + problem.linearMap y u - problem.dualPenalty u : EReal))) :
    problem.adjointObjective u = (problem.saddleFunction x u : EReal) := by
  rcases mem_constrainedArgmin_iff.mp hx with ⟨_, hx_min⟩
  exact adjointObjective_eq_saddleFunction_of_isMinOn <| by
    simpa using hx_min

/-- Expanding `adjointObjective_eq_saddleFunction_of_isMinOn` yields the textbook formula
`φ(u) = -\hat φ(u) + (\langle A x, u \rangle + \hat f(x))` as a thin companion in the chapter's
`EReal` encoding. -/
theorem adjointObjective_eq_of_isMinOn
    {problem : StructuredObjectiveModel E₁ E₂}
    {u : problem.dualSet} {x : problem.primalSet}
    (hx : IsMinOn
      (fun y : E₁ ↦
        (problem.smoothPart y + problem.linearMap y u - problem.dualPenalty u : EReal))
      problem.primalSet x) :
    problem.adjointObjective u =
      ((-problem.dualPenalty u + (problem.linearMap x u + problem.smoothPart x)) : EReal) := by
  simpa [saddleFunction, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
    adjointObjective_eq_saddleFunction_of_isMinOn hx

/-- Expanding `adjointObjective_eq_saddleFunction_of_mem_argmin` yields the textbook formula
`φ(u) = -\hat φ(u) + (\langle A x, u \rangle + \hat f(x))` for any ambient-space argmin point. -/
theorem adjointObjective_eq_of_mem_argmin
    {problem : StructuredObjectiveModel E₁ E₂}
    {u : problem.dualSet} {x : E₁}
    (hx : x ∈
      argmin[problem.primalSet]
        (fun y : E₁ ↦
          (problem.smoothPart y + problem.linearMap y u - problem.dualPenalty u : EReal))) :
    problem.adjointObjective u =
      ((-problem.dualPenalty u + (problem.linearMap x u + problem.smoothPart x)) : EReal) := by
  rcases mem_constrainedArgmin_iff.mp hx with ⟨hx_mem, hx_min⟩
  let x' : problem.primalSet := ⟨x, hx_mem⟩
  have hx'_min :
      IsMinOn
        (fun y : E₁ ↦
          (problem.smoothPart y + problem.linearMap y u - problem.dualPenalty u : EReal))
        problem.primalSet x' := by
    simpa [x'] using hx_min
  simpa [saddleFunction, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
    adjointObjective_eq_saddleFunction_of_isMinOn hx'_min

end StructuredObjectiveModel

end
