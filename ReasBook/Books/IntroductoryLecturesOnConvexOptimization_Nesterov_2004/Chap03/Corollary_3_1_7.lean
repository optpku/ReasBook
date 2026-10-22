/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Proposition_3_21

-- Declarations for this item will be appended below by the statement pipeline.

open scoped BigOperators

universe u v

/- Corollary 3.1.7 lies in finite-family whole-space convex analysis.

Primary domain:
- finite log-sum-exp convexity on a real module.

Sampled owner-style declarations:
- mathlib `ConvexOn`, the canonical owner for convexity on a set;
- mathlib `convex_univ`, the canonical whole-space convex-domain theorem;
- mathlib `LinearMap.convexOn`, a standard source of whole-space convex examples;
- project `convexOn_log_sum_exp_of_convexOn`, the chapter owner theorem on a common domain.

Best owner abstraction:
- source-facing: the whole-space finite log-sum-exp convexity statement;
- core/canonical: `convexOn_log_sum_exp_of_convexOn`;
- bridge/view: specialization of the common-domain owner theorem to `Set.univ`.

Primitive data:
- a finite index set `t : Finset ι`;
- a family `f : ι → E → ℝ`;
- whole-space convexity of each member `f i`.

Derived API:
- convexity of `x ↦ log (∑ i ∈ t, exp (f i x))` on `Set.univ`.

The previous file-level theorem was only the `Set.univ` specialization of the owner theorem, with
no extra mathematical content. This file therefore keeps only the direct owner-level specialization
check instead of a parallel local theorem name.
-/

variable {ι : Type u} {E : Type v} [AddCommMonoid E] [Module ℝ E]

/- Corollary 3.1.7 is the whole-space specialization of the chapter owner theorem
`convexOn_log_sum_exp_of_convexOn`. -/
#check
  (show ∀ {t : Finset ι} {f : ι → E → ℝ},
      t.Nonempty →
      (∀ i ∈ t, ConvexOn ℝ Set.univ (f i)) →
      ConvexOn ℝ Set.univ (fun x ↦ Real.log (∑ i ∈ t, Real.exp (f i x))) from
    convexOn_log_sum_exp_of_convexOn Set.univ)
