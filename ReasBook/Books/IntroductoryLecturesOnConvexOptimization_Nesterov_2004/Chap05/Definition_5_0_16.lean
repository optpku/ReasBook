/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Definition_3_3

-- Declarations for this item will be appended below by the statement pipeline.

open scoped WithTopConvexAnalysis

universe u

/- Definition 5.0.16 lies in the chapter's `WithTop`-valued convex-analysis domain.

Sampled owner-style declarations:
- `withTopEffectiveDomain` / `dom` in `Chap03/Definition_3_3`, the chapter owner for the
  effective domain of a `WithTop ℝ`-valued function;
- `withTopRealPart` in `Chap03/Definition_3_3`, the canonical finite real representative on that
  domain;
- the direct chapter recall `#check ConvexOn ℝ (dom f) (withTopRealPart f)` in
  `Chap03/Definition_3_3`;
- mathlib `ConvexOn`, the core owner for convexity on a set.

Best owner abstraction:
- `ConvexOn ℝ (dom f) (withTopRealPart f)`.

Primitive data:
- the function `f : X → WithTop ℝ`.

Derived API:
- convexity of `dom f`;
- the Jensen inequality on `dom f` specialized to coefficients `1 - t` and `t`.

Source/core/bridge triage:
- source-facing: Definition 5.0.16, the convexity notion for `ℝ ∪ {+∞}`-valued functions;
- core/canonical: `ConvexOn ℝ (dom f) (withTopRealPart f)`;
- bridge/view: the domain-convexity and Jensen-inequality consequence lemmas below.

This file uses the Chapter 3 owner directly for its main entry: the exact effective-domain and
finite-real-part surface already exists upstream, so the previous Chapter 5 duplicate wrappers are
deleted instead of being preserved under parallel names. -/

section

variable {X : Type u} [AddCommMonoid X] [Module ℝ X]
variable (f : X → WithTop ℝ)

/- Definition 5.0.16 uses the canonical Chapter 3 specialization of `ConvexOn` to define
convexity for `ℝ ∪ {+∞}`-valued functions. -/
set_option linter.hashCommand false in
#check ConvexOn ℝ (dom f) (withTopRealPart f)

end

section

variable {X : Type u} [AddCommMonoid X] [Module ℝ X]

/-- A convex `ℝ ∪ {+∞}`-valued function has convex effective domain. -/
-- Proof sketch: `ConvexOn` is defined as convexity of the domain together with the Jensen
-- inequality, so the domain-convexity claim is exactly the first projection of `hf`.
theorem convex_effectiveDomain
    {f : X → WithTop ℝ} (hf : ConvexOn ℝ (dom f) (withTopRealPart f)) :
    Convex ℝ (dom f) :=
  hf.1

/-- For a convex `ℝ ∪ {+∞}`-valued function, the convexity inequality holds on its effective
domain. -/
-- Proof sketch: apply the Jensen-inequality field `hf.2` of `ConvexOn`; the interval hypothesis
-- gives `0 ≤ 1 - t` and `0 ≤ t`, and `sub_add_cancel 1 t` supplies the coefficient sum.
theorem withTopRealPart_combo_le
    {f : X → WithTop ℝ} (hf : ConvexOn ℝ (dom f) (withTopRealPart f))
    {x y : X} (hx : x ∈ dom f) (hy : y ∈ dom f)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    withTopRealPart f ((1 - t) • x + t • y) ≤
      (1 - t) * withTopRealPart f x + t * withTopRealPart f y :=
  hf.2 hx hy (sub_nonneg.mpr ht.2) ht.1 (sub_add_cancel 1 t)

end
