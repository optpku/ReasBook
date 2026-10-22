/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat

-- Declarations for this item will be appended below by the statement pipeline.

universe u

variable {X : Type u}

/- Definition 4.1.16 lies in the cubic-regularization acceptance domain.

Sampled owner declarations:
* `Set` and `Set.mem_setOf` in mathlib, the canonical owner/view pair for parameter predicates;
* `RelaxedRegularizedNewtonIteration.regularization_mem_Ioc` in `Definition_4_1_5`, which keeps
  interval data separate from the update law;
* `CubicRegularizationMethod.step_value_le_modelValue` in `Algorithm_4_1_5`, which likewise keeps
  the model-comparison inequality separate from the regularization bounds;
* `CubicRegularizationBacktrackingAccepts` in `Definition_4_1_17`, the downstream inequality-only
  acceptance test that should reuse the same core owner.

Best owner abstraction:
* core/canonical: the set of parameters satisfying the acceptance inequality at a fixed point `x`;
* source-facing: the subset of those parameters lying in `[L₀, 2L]`.

Primitive data:
* `f`, `stepMap`, `modelValue`, and the current point `x`;
* for the source-facing layer, the interval endpoints `L₀` and `L`.

Derived API:
* membership characterizations;
* the source-facing introduction lemma from interval membership and the acceptance inequality.

Source/core/bridge triage:
* source-facing: `RegularizedNewton.acceptedParameters`;
* core/canonical: `RegularizedNewton.acceptingParameters`;
* bridge/view: the membership lemmas relating set membership to the textbook inequalities.
-/

namespace RegularizedNewton

variable (f : X → ℝ) (stepMap : ℝ → X → X) (modelValue : ℝ → X → ℝ)
variable (L0 L : ℝ) (x : X)

/-- The core acceptance set at a current point `x`: a parameter `M` belongs to
`acceptingParameters f stepMap modelValue x` exactly when the trial point `T_M(x)` satisfies the
acceptance inequality `f (T_M(x)) ≤ \tilde f_M(x)`. -/
def acceptingParameters
    : Set ℝ :=
  { M | f (stepMap M x) ≤ modelValue M x }

/-- Membership in `acceptingParameters` is exactly the regularized-Newton acceptance inequality at
the current point. -/
@[simp] theorem mem_acceptingParameters_iff
    (M : ℝ) :
    M ∈ acceptingParameters f stepMap modelValue x ↔
      f (stepMap M x) ≤ modelValue M x :=
  Iff.rfl

/-- Definition 4.1.16: the accepted regularized-Newton parameters at `x` are the admissible
parameters `M ∈ [L₀, 2L]` that satisfy the acceptance inequality
`f (T_M(x)) ≤ \tilde f_M(x)`. -/
def acceptedParameters
    : Set ℝ :=
  Set.Icc L0 (2 * L) ∩ acceptingParameters f stepMap modelValue x

/-- Membership in `acceptedParameters` recovers the textbook interval condition together with the
acceptance inequality. -/
@[simp] theorem mem_acceptedParameters_iff
    (M : ℝ) :
    M ∈ acceptedParameters f stepMap modelValue L0 L x ↔
      M ∈ Set.Icc L0 (2 * L) ∧ f (stepMap M x) ≤ modelValue M x := by
  simp [acceptedParameters, acceptingParameters]

/-- An admissible parameter belongs to `acceptedParameters` as soon as it satisfies the
regularized-Newton acceptance inequality at the same current point. -/
theorem mem_acceptedParameters_of_mem_Icc_of_le_modelValue
    {f : X → ℝ} {stepMap : ℝ → X → X} {modelValue : ℝ → X → ℝ}
    {L0 L : ℝ} (x : X) (M : ℝ)
    (hMmem : M ∈ Set.Icc L0 (2 * L))
    (haccept : f (stepMap M x) ≤ modelValue M x) :
    M ∈ acceptedParameters f stepMap modelValue L0 L x := by
  simpa using And.intro hMmem haccept

end RegularizedNewton
