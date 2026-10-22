/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import Mathlib.Tactic.Recall
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Definition_3_1_1_3
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap06.Text_6_1_2_Adjoint_Problem_Tractability_Caveat

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open scoped ConvexAnalysis

universe u v

variable {E₁ : Type u} {E₂ : Type v}
  [NormedAddCommGroup E₁] [NormedSpace ℝ E₁]
  [NormedAddCommGroup E₂] [NormedSpace ℝ E₂]

/- Definition 6.64 lies in the chapter's structured saddle-value / adjoint-problem domain.

Mandatory domain-style sampling before refinement:
- `StructuredObjectiveModel.adjointObjective` in `Chap06/Definition_6_6`, the chapter owner for
  the adjoint problem on the feasible dual set, canonically valued in `EReal`;
- `StructuredObjectiveModel.saddleFunction` in `Chap06/Definition_6_6`, the canonical saddle
  slice whose primal infimum defines `adjointObjective`;
- `StructuredObjectiveModel.adjointObjective_eq_of_isMinOn` in
  `Chap06/Text_6_1_2_Adjoint_Problem_Tractability_Caveat`, the chapter bridge from the owner to
  the attained-minimum textbook formula;
- `extendedRealRealPart`, `dom`, and `coe_extendedRealRealPart` in
  `Chap03/Definition_3_1_1_3`, the canonical finite-real-part bridge for `EReal` owners.

Best owner abstraction:
- source-facing: Definition 6.64's adjoint problem on the feasible dual set;
- core/canonical: `StructuredObjectiveModel.adjointObjective`;
- bridge/view: the finite-real-part theorem below under an attained inner minimum.

Primitive data:
- `problem : StructuredObjectiveModel E₁ E₂`;
- `u : problem.dualSet`;
- `x : problem.primalSet`;
- an attained minimum witness for the fixed-`u` saddle slice on `problem.primalSet`.

Derived API:
- the recalled owner `problem.adjointObjective`;
- finiteness of `problem.adjointObjective` at a point with attained inner minimum;
- the finite real-part formula recovering the textbook scalar value.

Source/core/bridge triage:
- source-facing: the adjoint problem from Definition 6.64;
- core/canonical: `StructuredObjectiveModel.adjointObjective`;
- bridge/view: `extendedRealRealPart_adjointObjective_eq_of_isMinOn`.

The previous version rebuilt a second public owner layer
`adjointInnerMinimand` / `adjointValueFunction` / `adjointProblem`, and it specialized the
linear term to Hilbert-space adjoints. This refinement deletes that duplicate wheel, keeps the
main entry as a direct recall of the chapter owner, and states the remaining textbook bridge in
the normed-space / `StrongDual` formulation `problem.linearMap x u`.
-/

namespace StructuredObjectiveModel

/- Definition 6.64 recalls the chapter owner for the adjoint problem. -/
recall adjointObjective (problem : StructuredObjectiveModel E₁ E₂) : problem.dualSet → EReal

/-- Under an attained inner minimum, the canonical adjoint objective is finite at `u`. -/
theorem adjointObjective_mem_dom_of_isMinOn
    {problem : StructuredObjectiveModel E₁ E₂}
    {u : problem.dualSet} {x : problem.primalSet}
    (hx : IsMinOn
      (fun y : E₁ ↦
        (problem.smoothPart y + problem.linearMap y u - problem.dualPenalty u : EReal))
      problem.primalSet x) :
    u ∈ dom problem.adjointObjective := by
  rw [mem_extendedRealEffectiveDomain_iff, problem.adjointObjective_eq_of_isMinOn hx]
  constructor
  · exact EReal.add_ne_top (by simp) <| EReal.add_ne_top (by simp) (by simp)
  · exact (EReal.add_ne_bot_iff).2
      ⟨by simp, (EReal.add_ne_bot_iff).2 ⟨by simp, by simp⟩⟩

/-- Under an attained inner minimum, the finite real part of the canonical adjoint objective
recovers the textbook scalar formula from Definition 6.64, written via the canonical dual pairing
`problem.linearMap x u`. -/
theorem extendedRealRealPart_adjointObjective_eq_of_isMinOn
    {problem : StructuredObjectiveModel E₁ E₂}
    {u : problem.dualSet} {x : problem.primalSet}
    (hx : IsMinOn
      (fun y : E₁ ↦
        (problem.smoothPart y + problem.linearMap y u - problem.dualPenalty u : EReal))
      problem.primalSet x) :
    extendedRealRealPart problem.adjointObjective u =
      -problem.dualPenalty u + (problem.linearMap x u + problem.smoothPart x) := by
  have hdom : u ∈ dom problem.adjointObjective :=
    adjointObjective_mem_dom_of_isMinOn hx
  have hcoe :
      ((extendedRealRealPart problem.adjointObjective u : ℝ) : EReal) =
        problem.adjointObjective u :=
    coe_extendedRealRealPart hdom
  rw [problem.adjointObjective_eq_of_isMinOn hx] at hcoe
  exact EReal.coe_eq_coe_iff.mp hcoe

end StructuredObjectiveModel

end
