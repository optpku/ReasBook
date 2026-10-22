/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import Mathlib.Tactic.Recall
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Lemma_3_8

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open scoped WithTopConvexAnalysis

/- Lemma 3.1.8 is a recall-only bridge in the chapter's extended-valued
convex-composition/subdifferential-calculus domain.

Sampled owner-style declarations:
- `withTopEffectiveDomain` in `Definition_3_3`, the chapter owner for the finite-value domain
- `withTopRealPart` in `Definition_3_3`, the owner finite-value representative
- `subdifferential` in `Definition_3_1_5`, the owner subgradient-set API
- `monotoneConvexComp_convexOn` and `subdifferential_monotoneConvexComp_eq_convexHull` in
  `Lemma_3_8`, the source owner clauses for this monotone composition lemma on real inner-product
  spaces

Best owner abstraction:
- the source-facing composition object `monotoneConvexComp` together with its convexity and
  subdifferential owner clauses in `Lemma_3_8`
- the ambient effective-domain / finite-part / subdifferential notions remain owned upstream by
  `Definition_3_3` and `Definition_3_1_5`

Primitive data:
- none in this recall file

Derived API:
- `monotoneConvexComp`
- `monotoneConvexComp_apply_of_mem_effectiveDomain`
- `monotoneConvexComp_convexOn`
- `subdifferential_monotoneConvexComp_eq_convexHull`

Source/core/bridge triage:
- source-facing: the monotone composition object and its two textbook clauses recalled below
- core/canonical: `withTopEffectiveDomain`, `withTopRealPart`,
  `ConvexOn ℝ (dom f) (withTopRealPart f)`,
  `subdifferential`
- bridge/view: this recall-only file

The previous version redefined the ambient effective-domain, finite-real-part, convexity, and
subdifferential API locally, then split the owner theorem into two wrapper consequences. Those
parallel wrappers had no downstream users. This file now recalls the owner composition surface
directly instead of maintaining a second root API. The owner surface in `Lemma_3_8` is now itself
split into the two atomic textbook clauses, so this recall file follows that same canonical
surface and drops the redundant properness hypotheses that were only artifacts of the earlier
coordinate-specialized statement. -/

recall monotoneConvexComp {V : Type u} (φ : ℝ → WithTop ℝ) (ψ : V → WithTop ℝ) :
    V → WithTop ℝ

recall monotoneConvexComp_apply_of_mem_effectiveDomain
    {V : Type u} {φ : ℝ → WithTop ℝ} {ψ : V → WithTop ℝ} {x : V}
    (hx : x ∈ dom ψ) :
    monotoneConvexComp φ ψ x = φ (withTopRealPart ψ x)

recall monotoneConvexComp_convexOn

recall subdifferential_monotoneConvexComp_eq_convexHull
