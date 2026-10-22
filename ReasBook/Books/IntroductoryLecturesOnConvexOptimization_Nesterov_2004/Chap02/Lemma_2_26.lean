/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap02.Definition_2_47

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u v

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable {ι : Type v} [Fintype ι] [Nonempty ι]
variable {m : ℕ} {μ L : ℝ}

namespace SmoothMinimaxProblem

section

variable (problem : SmoothMinimaxProblem E ι μ L)

local notation "modelValue" =>
  fun xBar γ ↦
    sInf
      ((quadraticallyRegularizedObjective
          (problem.affineApproximation xBar)
          γ
          xBar) '' problem.feasibleSet)

local notation "valueFunction" =>
  sInf (problem '' problem.feasibleSet)

local notation "relativeGap" =>
  fun xBar ↦ problem xBar - valueFunction

/-
Primary domain: the scalar stopping inequality for regularized local-model values on the owner
smooth minimax problem.

Owner abstractions sampled before refining:
- `SmoothMinimaxProblem` from `Definition_2_38.lean`, the owner fixed-feasible-set minimax
  problem;
- `SmoothMinimaxProblem.affineApproximation`, the owner local affine model at `xBar`;
- `quadraticallyRegularizedObjective` from `Definition_1_4_17.lean`, the owner quadratic
  regularization of that affine model;
- `SmoothFunctionalConstraintsMinimizationProblem.toParametricSmoothMinimaxProblem` from
  `Definition_2_47.lean`, the later bridge/view which will reuse this owner theorem.

Best owner abstraction:
- `problem : SmoothMinimaxProblem E ι μ L`.

Source/core/bridge triage:
- source-facing in this namespace: the stopping comparison for a smooth minimax problem;
- core/canonical: the owner regularized model values built from `problem.affineApproximation`;
- bridge/view: the fixed-`t` constrained problem in the second half of this file.

Primitive data:
- the owner minimax problem `problem`;
- the base point `xBar`;
- the scalars `α` and `Qf`.

Derived API:
- the regularized model values `modelValue xBar γ`;
- the optimal value `valueFunction`;
- the relative gap `relativeGap xBar`.
-/
/-- On the canonical smooth-minimax owner layer, if the `μ`-regularized model value at `xBar` is
bounded below by the `L`-regularized model value minus `(Q_f - 1)` times the current relative
gap, and if that relative gap is at most `(α / (Q_f - 1))` times the `L`-model value, then
`f^*(xBar; μ) ≥ (1 - α) f^*(xBar; L)`. -/
theorem stopping_condition_of_relativeGapBound
    {α Qf : ℝ} {xBar : E}
    (hQf : 1 < Qf)
    (hModelComparison :
      modelValue xBar μ ≥
        modelValue xBar L - (Qf - 1) * relativeGap xBar)
    (hRelativeGap :
      relativeGap xBar ≤
        (α / (Qf - 1)) * modelValue xBar L) :
    (1 - α) * modelValue xBar L ≤ modelValue xBar μ := by
  have hQf_sub : 0 < Qf - 1 := sub_pos.mpr hQf
  have hRelativeGap' :
      (Qf - 1) * relativeGap xBar ≤ α * modelValue xBar L := by
    have h :=
      mul_le_mul_of_nonneg_left hRelativeGap (le_of_lt hQf_sub)
    calc
      (Qf - 1) * relativeGap xBar ≤
          (Qf - 1) * ((α / (Qf - 1)) * modelValue xBar L) := h
      _ = α * modelValue xBar L := by
        field_simp [hQf_sub.ne']
  nlinarith [hModelComparison, hRelativeGap']

end

end SmoothMinimaxProblem

section

variable (problem : SmoothFunctionalConstraintsMinimizationProblem E m μ L) (t : ℝ)

local notation "parametricProblem" => problem.toParametricSmoothMinimaxProblem t

local notation "modelValue" => problem.regularizedModelValue t

local notation "valueFunction" =>
  sInf (parametricProblem '' (SmoothMinimaxProblem.feasibleSet parametricProblem))

local notation "relativeGap" => fun xBar ↦ parametricProblem xBar - valueFunction

/-
Primary domain: fixed-`t` regularized local-model values for the constrained max-type problem
attached to a smooth functional-constraint problem.

Owner abstractions sampled before refining:
- `SmoothFunctionalConstraintsMinimizationProblem.toParametricSmoothMinimaxProblem` from
  `Definition_2_47.lean`, the owner fixed-`t` smooth minimax problem;
- `SmoothFunctionalConstraintsMinimizationProblem.regularizedModelValue` from
  `Definition_2_47.lean`, the owner fixed-`t` regularized model value;
- `SmoothMinimaxProblem.stopping_condition_of_relativeGapBound` from this file, the owner
  minimax comparison theorem reused below;
- `ConstrainedMinimizationMethod.step1a` from `Algorithm_2_11.lean`, the later bridge/view
  packaging the same stopping inequality along the algorithmic trajectory.

Best owner abstraction:
- `parametricProblem : SmoothMinimaxProblem E (Fin (m + 1)) μ L`.

Source/core/bridge triage:
- source-facing: Lemma 2.26 for the fixed parameter `t` in the constrained problem;
- core/canonical: the owner smooth minimax problem `parametricProblem` and its theorem
  `parametricProblem.stopping_condition_of_relativeGapBound`;
- bridge/view: `ConstrainedMinimizationMethod.step1a`, which later reuses the same comparison.

Primitive data:
- the constrained problem `problem`;
- the scalar parameter `t`;
- the base point `xBar`;
- the scalars `α` and `Qf`.

Derived API:
- the owner local-model values `modelValue xBar γ`, recalled from
  `SmoothFunctionalConstraintsMinimizationProblem.regularizedModelValue`;
- the owner constrained optimal value `valueFunction`;
- the relative gap `relativeGap xBar`.

The refinement therefore keeps the public lemma at the source-facing fixed-`t` layer, recalls the
owner declaration `problem.regularizedModelValue t` for the local-model values, and reuses the
canonical smooth-minimax owner theorem instead of keeping a parallel local proof on the bridge
layer.
-/

/-- Lemma 2.26: for the fixed-`t` parametric minimax problem attached to a smooth functional
constraints problem, if the regularized `μ`-model value is bounded below by the regularized `L`
model value minus `(Q_f - 1)` times the current relative gap, and that relative gap is at most
`(α / (Q_f - 1)) f^*(t; xBar; L)`, then the stopping comparison
`f^*(t; xBar; μ) ≥ (1 - α) f^*(t; xBar; L)` holds. -/
-- Proof sketch: apply the owner minimax version of the same inequality to the fixed-`t` bridge
-- problem `parametricProblem`.
theorem stopping_condition_of_relativeGapBound
    {α Qf : ℝ} {xBar : E}
    (hQf : 1 < Qf)
    (hModelComparison :
      modelValue xBar μ ≥
        modelValue xBar L - (Qf - 1) * relativeGap xBar)
    (hRelativeGap :
      relativeGap xBar ≤
        (α / (Qf - 1)) * modelValue xBar L) :
    (1 - α) * modelValue xBar L ≤ modelValue xBar μ := by
  simpa [SmoothFunctionalConstraintsMinimizationProblem.regularizedModelValue] using
    (problem.toParametricSmoothMinimaxProblem t).stopping_condition_of_relativeGapBound
      hQf hModelComparison hRelativeGap

end
