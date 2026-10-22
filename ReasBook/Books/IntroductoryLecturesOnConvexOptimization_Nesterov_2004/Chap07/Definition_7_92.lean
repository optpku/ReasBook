/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap01.Definition_1_3_7
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap07.Definition_7_1

-- Declarations for this item will be appended below by the statement pipeline.

universe u

noncomputable section

section

variable {X : Type u}

/- Definition 7.92 lies in the constrained minimization / relative-accuracy domain.

Mandatory domain-style sampling before refinement:
- `SetConstrainedMinimizationProblem` in `Chap01/Definition_1_3_3`, the project owner of a
  feasible set together with a real-valued objective;
- `SetConstrainedMinimizationProblem.optimalValue` in `Chap01/Definition_1_3_7`, the canonical
  Chapter 1 optimal-value owner for constrained minimization problems in `EReal`;
- `IsRelativeAccuracy` in `Chap07/Definition_7_1`, the chapter owner for two-sided scalar
  relative accuracy;
- `IsMixedApproximateSolution` in `Chap07/Definition_7_90`, which shows the local chapter style
  of keeping constrained approximate-solution notions as direct `Prop`-valued owners rather than
  structures with `Fact` packaging.

Best owner abstraction:
- source-facing: the constrained relative-`δ` approximate-solution predicate in Definition 7.92;
- core/canonical: `SetConstrainedMinimizationProblem X` for the ambient constrained problem, and
  `IsRelativeAccuracy` for the scalar two-sided relative-value notion;
- bridge/view: the displayed one-sided inequality against the Chapter 1 owner optimal value,
  together with the `.toReal` projection and the derived `IsRelativeAccuracy` theorem.

Primitive data:
- the feasible set `Q`;
- the objective `f : X → ℝ`;
- the relative-accuracy parameter `δ`;
- the candidate point `xBar`;
- positivity of the canonical constrained optimal value.

Derived API:
- the interval condition `δ ∈ Set.Ioo (0 : ℝ) (1 / 2)`;
- feasibility `xBar ∈ Q`;
- the owner-valued upper bound
  `(f xBar : EReal) ≤ (1 + δ) * (SetConstrainedMinimizationProblem.mk Q f).optimalValue`;
- the real-valued bridge
  `f xBar ≤ (1 + δ) * ((SetConstrainedMinimizationProblem.mk Q f).optimalValue).toReal`.

Source/core/bridge triage:
- source-facing: `IsRelativeDeltaApproximateSolutionOn`;
- core/canonical: `SetConstrainedMinimizationProblem.mk Q f` and `IsRelativeAccuracy`;
- bridge/view: `IsRelativeDeltaApproximateSolutionOn.objective_le_toReal` and
  `IsRelativeDeltaApproximateSolutionOn.toIsRelativeAccuracy`.

The earlier refinement already removed the local raw-`sInf` alias and wrapper packaging, but the
remaining public definition still used the raw real infimum `sInf (f '' Q)`. On `ℝ`, that loses
the distinction between a genuine finite positive optimum and an unbounded-below feasible image.
Definition 7.92 therefore needs the Chapter 1 owner `optimalValue : EReal` as primitive data,
plus positivity of that owner value, so the relative-accuracy bridge is semantically intrinsic
rather than an after-the-fact repair theorem.
-/

/-- Definition 7.92: a point `xBar` is a relative `δ`-approximate solution of the minimization
problem for `f` on `Q` when `δ ∈ (0, 1 / 2)`, `xBar ∈ Q`, the canonical constrained optimal value
is strictly positive, and `f xBar` is at most `(1 + δ)` times that owner optimal value. -/
def IsRelativeDeltaApproximateSolutionOn
    (Q : Set X) (f : X → ℝ) (δ : ℝ) (xBar : X) : Prop :=
  let problem : SetConstrainedMinimizationProblem X := .mk Q f
  δ ∈ Set.Ioo (0 : ℝ) (1 / 2) ∧
    xBar ∈ Q ∧
    (0 : EReal) < problem.optimalValue ∧
    (f xBar : EReal) ≤ (1 + δ) * problem.optimalValue

namespace IsRelativeDeltaApproximateSolutionOn

variable {Q : Set X} {f : X → ℝ} {δ : ℝ} {xBar : X}

/-- A relative `δ`-approximate solution carries the textbook interval condition on `δ`. -/
theorem delta_mem_Ioo
    (h : IsRelativeDeltaApproximateSolutionOn Q f δ xBar) :
    δ ∈ Set.Ioo (0 : ℝ) (1 / 2) :=
  h.1

/-- A relative `δ`-approximate solution is feasible for the original minimization problem. -/
theorem feasible
    (h : IsRelativeDeltaApproximateSolutionOn Q f δ xBar) :
    xBar ∈ Q :=
  h.2.1

/-- A relative `δ`-approximate solution requires a strictly positive constrained optimal value. -/
theorem optimalValue_pos
    (h : IsRelativeDeltaApproximateSolutionOn Q f δ xBar) :
    (0 : EReal) < (SetConstrainedMinimizationProblem.mk Q f).optimalValue :=
  h.2.2.1

/-- A relative `δ`-approximate solution satisfies the defining owner-valued objective bound. -/
theorem objective_le
    (h : IsRelativeDeltaApproximateSolutionOn Q f δ xBar) :
    (f xBar : EReal) ≤ (1 + δ) * (SetConstrainedMinimizationProblem.mk Q f).optimalValue :=
  h.2.2.2

/-- Projecting the owner-valued objective bound back to `ℝ` gives the textbook relative
upper-bound inequality against the canonical constrained optimal value. -/
theorem objective_le_toReal
    (h : IsRelativeDeltaApproximateSolutionOn Q f δ xBar) :
    f xBar ≤ (1 + δ) * ((SetConstrainedMinimizationProblem.mk Q f).optimalValue).toReal := by
  let problem : SetConstrainedMinimizationProblem X := .mk Q f
  have hoptimal_ne_top : problem.optimalValue ≠ ⊤ := by
    exact ne_top_of_le_ne_top (EReal.coe_ne_top _)
      (problem.optimalValue_le_of_mem_feasibleSet h.feasible)
  have hoptimal_ne_bot : problem.optimalValue ≠ ⊥ :=
    ne_bot_of_gt h.optimalValue_pos
  have hmul_ne_top : (((1 + δ : ℝ) : EReal) * problem.optimalValue) ≠ ⊤ := by
    rw [EReal.mul_ne_top]
    exact ⟨Or.inl (EReal.coe_ne_bot _), Or.inr hoptimal_ne_bot,
      Or.inl (EReal.coe_ne_top _), Or.inr hoptimal_ne_top⟩
  simpa [problem, EReal.toReal_mul] using
    EReal.toReal_le_toReal h.objective_le (EReal.coe_ne_bot _) hmul_ne_top

/-- The positivity and owner-valued objective bound in Definition 7.92 induce the chapter's
scalar relative-accuracy owner for the canonical constrained optimal value. -/
theorem toIsRelativeAccuracy
    (h : IsRelativeDeltaApproximateSolutionOn Q f δ xBar) :
    IsRelativeAccuracy ((SetConstrainedMinimizationProblem.mk Q f).optimalValue).toReal δ
      (f xBar) := by
  let problem : SetConstrainedMinimizationProblem X := .mk Q f
  have hoptimal_ne_top : problem.optimalValue ≠ ⊤ := by
    exact ne_top_of_le_ne_top (EReal.coe_ne_top _)
      (problem.optimalValue_le_of_mem_feasibleSet h.feasible)
  have hoptimal_ne_bot : problem.optimalValue ≠ ⊥ :=
    ne_bot_of_gt h.optimalValue_pos
  refine ⟨by simpa [problem] using EReal.toReal_pos h.optimalValue_pos hoptimal_ne_top, ?_,
    by simpa [problem] using h.objective_le_toReal⟩
  simpa [problem] using
    EReal.toReal_le_toReal (problem.optimalValue_le_of_mem_feasibleSet h.feasible)
      hoptimal_ne_bot (EReal.coe_ne_top _)

end IsRelativeDeltaApproximateSolutionOn

/-- Unfolding `IsRelativeDeltaApproximateSolutionOn Q f δ xBar` gives the admissible range for
`δ`, feasibility of `xBar`, positivity of the canonical constrained optimal value, and the
owner-valued relative objective bound. -/
theorem isRelativeDeltaApproximateSolutionOn_iff
    (Q : Set X) (f : X → ℝ) (δ : ℝ) (xBar : X) :
    IsRelativeDeltaApproximateSolutionOn Q f δ xBar ↔
      let problem : SetConstrainedMinimizationProblem X := .mk Q f
      δ ∈ Set.Ioo (0 : ℝ) (1 / 2) ∧
        xBar ∈ Q ∧
        (0 : EReal) < problem.optimalValue ∧
        (f xBar : EReal) ≤ (1 + δ) * problem.optimalValue :=
  Iff.rfl

end
