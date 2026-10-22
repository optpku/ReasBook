/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Definition_3_1_1_3
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Lemma_3_37
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Lemma_3_3_6

-- Declarations for this item will be appended below by the statement pipeline.

open scoped ConvexAnalysis

section

universe u v w

variable {Index : Type u} {Param : Type v} {Decision : Type w}

/-
Lemma 3.3.5 lies in the chapter's constrained-threshold / parametric-value domain.

Relevant owner declarations sampled before refining:
- `parametricValueFunction` in `Chap03/Lemma_3_3_6`, the chapter owner for the scalar model value
  `t ↦ inf_{x ∈ Q} max (hatFn k X x - t) (checkFn k X x)`;
- `estimatedValue_strict_lt_right_and_secant_lower_bound_of_nonpos_right` in `Chap03/Lemma_3_37`,
  the chapter bridge specializing the scalar secant owner to a fixed real right endpoint `τ`;
- `ConvexOn.strict_lt_and_secant_lower_bound_of_nonpos_right` in `Chap02/Proposition_2_26`, the
  upstream owner bridge from convexity plus sign data to the scalar secant inequality.

Best owner abstractions:
- `parametricValueFunction Q (hatFn k X) (checkFn k X)`;
- `extendedRealRealPart (parametricValueFunction Q (hatFn k X) (checkFn k X))`.

Primitive data:
- the feasible set `Q`;
- the stage-`k` upper model `hatFn k X`;
- the stage-`k` constraint model `checkFn k X`;
- the index `k` and parameter `X`.

Derived API:
- the source-facing right-endpoint/secant conclusion obtained by specializing the existing chapter
  bridge `estimatedValue_strict_lt_right_and_secant_lower_bound_of_nonpos_right` to the finite
  real-part view of the extended-real owner value function;
- the convexity and right-endpoint nonpositivity witnesses required by that bridge.

Source/core/bridge triage:
- source-facing: Lemma 3.3.5 in the chapter's complete-data notation;
- core/canonical: `parametricValueFunction`;
- bridge/view: `extendedRealRealPart (parametricValueFunction Q (hatFn k X) (checkFn k X))` and
  the specialization of `estimatedValue_strict_lt_right_and_secant_lower_bound_of_nonpos_right`
  to that real-valued slice.

This file therefore keeps the labeled item only as the source-facing specialization of the chapter
secant bridge to the canonical finite real-part view of `parametricValueFunction`. It does not
repackage the nearby threshold owner as extra local API, because the theorem statement itself uses
only the scalar slice and the right-endpoint sign data.
-/

section

variable (Q : Set Decision) (hatFn checkFn : Index → Param → Decision → ℝ)
variable (k : Index) (X : Param)

local notation "valueFn" =>
  parametricValueFunction Q (hatFn k X) (checkFn k X)
local notation "modelValue" =>
  extendedRealRealPart valueFn

/-- Lemma 3.3.5: if the finite real-part view of the complete-data owner value
`parametricValueFunction Q (hatFn k X) (checkFn k X) t₁` is positive for some
`t₀ < t₁ ≤ τ`, the owner value at `τ` is finite and nonpositive, and the scalar slice is convex
on `(-∞, τ]`, then `τ` lies strictly to the right of `t₁` and the displayed secant lower bound
holds. -/
theorem parametricValueFunction_strict_lt_right_and_secant_lower_bound
    {t0 t1 τ : ℝ}
    (ht0_lt_t1 : t0 < t1)
    (ht1_le_right : t1 ≤ τ)
    (hpos : 0 < modelValue t1)
    (hτ_dom : τ ∈ dom valueFn)
    (hright_nonpos : valueFn τ ≤ (0 : EReal))
    (hconvex : ConvexOn ℝ (Set.Iic τ) modelValue) :
    t1 < τ ∧
      modelValue t0 ≥
        modelValue t1 + ((t1 - t0) / (τ - t1)) * modelValue t1 := by
  exact
    estimatedValue_strict_lt_right_and_secant_lower_bound_of_nonpos_right
      (fun k X ↦ extendedRealRealPart (parametricValueFunction Q (hatFn k X) (checkFn k X)))
      k
      X
      ht0_lt_t1
      ht1_le_right
      hpos
      ((extendedRealRealPart_le_iff hτ_dom).2 hright_nonpos)
      hconvex

end

end
