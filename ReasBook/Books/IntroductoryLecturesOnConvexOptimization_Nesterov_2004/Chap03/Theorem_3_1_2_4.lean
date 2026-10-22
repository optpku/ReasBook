/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Theorem_3_1_8

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u v

open scoped WithTopConvexAnalysis

variable {ι : Type u} {X : Type v}

/- Theorem 3.1.2.4 is a recall-only `Set.univ` specialization in the chapter's closed-convex
pointwise-supremum domain.

Relevant sampled declarations in this domain:
- `pointwiseSupremumOn` in `Theorem_3_1_8`, the source-facing owner for subset-indexed pointwise
  suprema of `WithTop ℝ`-valued families;
- `pointwiseSupremumOnEffectiveDomain` in `Theorem_3_1_8`, the canonical effective-domain bridge
  for that owner;
- `ClosedConvexOn` in `Definition_3_1_1_5`, the chapter owner predicate for closed convexity on a
  feasible set;
- `ClosedConvexOn.pointwise_sSup` in `Theorem_3_1_8`, the owner theorem for closed-convex
  stability under subset-indexed pointwise suprema.

Best owner abstraction:
- core/canonical owner: `ClosedConvexOn.pointwise_sSup` on
  `pointwiseSupremumOn Δ φ`;
- bridge/view: the `Δ = Set.univ` specialization used in this numbered textbook item.

Primitive data:
- none in this file; the pointwise-supremum owner and its effective-domain bridge already live
  upstream.

Derived API:
- this recall-only `Set.univ` specialization.

Source/core/bridge triage:
- source-facing: Theorem 3.1.2.4 as the all-indices specialization of the pointwise-supremum
  closed-convexity theorem;
- core/canonical: `pointwiseSupremumOn`, `pointwiseSupremumOnEffectiveDomain`, and
  `ClosedConvexOn.pointwise_sSup`;
- bridge/view: the passage from an arbitrary subset `Δ` to `Set.univ`.

The previous file introduced a second theorem name `ClosedConvexOn.pointwise_iSup` for this
specialization. The owner theorem already exists upstream on the correct abstraction layer, so this
file is now recall-only and keeps no parallel local theorem copy.
-/

section

variable [TopologicalSpace X] [AddCommMonoid X] [Module ℝ X] [Nonempty ι]
variable {Q : Set X} {φ : X → ι → WithTop ℝ}

/- Theorem 3.1.2.4: for a nonempty index type, if each slice `x ↦ φ x y` is closed and convex on
`Q`, then the pointwise supremum over all indices is closed and convex on its canonical effective
domain. -/
#check
  (show (∀ y : ι, ClosedConvexOn Q (fun x ↦ φ x y)) →
      ClosedConvexOn (pointwiseSupremumOnEffectiveDomain Q (Set.univ : Set ι) φ)
        (pointwiseSupremumOn (Set.univ : Set ι) φ) from
    fun hφ ↦ by
      let ⟨i⟩ := ‹Nonempty ι›
      exact ClosedConvexOn.pointwise_sSup ⟨i, by simp⟩ (fun y _ ↦ hφ y))

end

end
