/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import Mathlib.Tactic.Recall
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Definition_3_3
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Definition_3_1_7

-- Declarations for this item will be appended below by the statement pipeline.

open scoped WithTopConvexAnalysis

universe u

/-
Definition 3.19 is a recall-only bridge in the chapter's extended-valued positive-homogeneity API.

Primary domain:
- positive homogeneity for `WithTop ℝ`-valued functions via their effective domains.

Relevant owner-style declarations sampled before refinement:
- `IsPositivelyHomogeneousOn` in `Definition_3_1_7`, the chapter owner for positive homogeneity on
  a cone;
- `dom` and `withTopRealPart` in `Definition_3_3`, the chapter bridge from `WithTop ℝ` values to
  the effective-domain real part;
- `euler_homogeneous_function_theorem` in `Theorem_3_1_21`;
- `subgradient_inner_eq_degree_mul_withTopRealPart_of_homogeneous` in `Theorem_3_26`.

Best owner abstraction:
- `IsPositivelyHomogeneousOn p (dom f) (withTopRealPart f)`.

Primitive data:
- an extended-real-valued function `f : E → WithTop ℝ`;
- a degree `p : ℝ`.

Derived API:
- closure of `dom f` under nonnegative scaling;
- the scaling law for `withTopRealPart f` on `dom f`;
- the downstream homogeneous-subgradient theorems in `Theorem_3_1_21` and `Theorem_3_26`.

Source/core/bridge triage:
- source-facing: Definition 3.19's positive homogeneity on the effective domain of an
  `ℝ ∪ {+∞}`-valued function;
- core/canonical: `IsPositivelyHomogeneousOn`;
- bridge/view: `dom f` and `withTopRealPart f`.

The previous file recalled only the raw generic owner and thereby dropped the chapter's canonical
effective-domain specialization already used downstream. This file now recalls the source-facing
bridge directly.

The source writes the side condition `0 ≤ p`. That inequality is not primitive owner data in this
project: the owner already restricts scaling parameters to `τ : NNReal`, and `Real.rpow (τ : ℝ) p`
is defined for every real exponent on that nonnegative base. The canonical notion is therefore the
specialized predicate below; later results can keep `0 ≤ p` as a separate theorem hypothesis when
the mathematics genuinely uses it.
-/
section

variable {E : Type u} [SMul NNReal E]
variable (p : ℝ) (f : E → WithTop ℝ)

/-- Definition 3.19: an `ℝ ∪ {+∞}`-valued function is positively homogeneous of degree `p` when
its effective domain is closed under nonnegative scaling and its finite real part scales with
degree `p` on that domain. -/
abbrev IsPositivelyHomogeneous (p : ℝ) (f : E → WithTop ℝ) : Prop :=
  IsPositivelyHomogeneousOn p (dom f) (withTopRealPart f)

/-- Helper for Definition 3.19: the source-facing abbreviation is definitionally the chapter owner
on `dom f` and `withTopRealPart f`. -/
theorem isPositivelyHomogeneous_iff_owner {p : ℝ} {f : E → WithTop ℝ} :
    IsPositivelyHomogeneous p f ↔ IsPositivelyHomogeneousOn p (dom f) (withTopRealPart f) :=
  Iff.rfl

/-- Helper for Definition 3.19: the effective domain of a positively homogeneous function is
closed under nonnegative scaling. -/
theorem homogeneous_dom_smul_mem {p : ℝ} {f : E → WithTop ℝ}
    (hhom : IsPositivelyHomogeneous p f) {x : E} (hx : x ∈ dom f) (τ : NNReal) :
    τ • x ∈ dom f := by
  -- The source-facing predicate is just the owner specialized to the effective domain.
  exact hhom.smul_mem hx τ

/-- Helper for Definition 3.19: on the effective domain, the finite real part of a positively
homogeneous function satisfies the expected scaling identity. -/
theorem homogeneous_withTopRealPart_map_smul {p : ℝ} {f : E → WithTop ℝ}
    (hhom : IsPositivelyHomogeneous p f) {x : E} (hx : x ∈ dom f) (τ : NNReal) :
    withTopRealPart f (τ • x) = Real.rpow (τ : ℝ) p • withTopRealPart f x := by
  -- Project the scaling law directly from the specialized owner predicate.
  exact hhom.map_smul hx τ

end
