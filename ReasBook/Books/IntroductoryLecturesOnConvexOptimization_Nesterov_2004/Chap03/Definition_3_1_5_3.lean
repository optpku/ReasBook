/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Definition_3_1_1_2
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Definition_3_22

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open scoped ConvexAnalysis
open scoped NormalCone

universe u

/- Definition 3.1.5.3 belongs to the chapter's canonical normal-cone API for the sublevel set
`{x ∈ dom f | f x ≤ f x0}`.

Primary domain:
- convex analysis of extended-real-valued functions on real inner-product spaces.

Relevant sampled declarations:
- `normalCone`
- `neg_mem_normalCone_iff`
- `extendedRealEffectiveDomain`
- `subgradient_nonneg_on_sublevelSet_of_mem_subdifferential`

Owner abstraction:
- `normalCone`

Primitive data:
- `extendedRealEffectiveDomain f`
- the source-facing sublevel set `{x ∈ dom f | f x ≤ f x0}`

Derived API:
- the textbook spelling with the explicit domain condition and the inequality
  `inner ℝ g (x0 - x) ≥ 0`

This file therefore states the numbered item as a bridge from the owner abstraction instead of
introducing a parallel local predicate.

Source/core/bridge triage:
- source-facing: the textbook inequality for the sublevel set `{x ∈ dom f | f x ≤ f x0}`
- core/canonical: `normalCone`
- bridge/view: `neg_mem_normalCone_iff` specialized to that source-facing set-builder

The base-point finiteness assumption `x0 ∈ dom f` is redundant for this normal-cone equivalence:
the set itself already records the only finiteness data used by the owner theorem. -/

variable {V : Type u} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]

/-- Definition 3.1.5.3: membership of `-g` in the normal
cone to the sublevel set `{x ∈ dom f | f x ≤ f x₀}` at `x₀` is
equivalent to the textbook inequality `⟪g, x₀ - x⟫ ≥ 0` for every `x` with `f x ≤ f x₀`. -/
-- Proof sketch: specialize `neg_mem_normalCone_iff` to the sublevel set
-- `{x | x ∈ dom f ∧ f x ≤ f x0}` and unpack the resulting set membership.
theorem level_set_inequality_at_iff
    {f : V → EReal} {x0 g : V} :
    (-g) ∈ N[{x | x ∈ dom f ∧ f x ≤ f x0}] x0 ↔
      ∀ ⦃x : V⦄, x ∈ dom f →
        f x ≤ f x0 →
          inner ℝ g (x0 - x) ≥ 0 := by
  rw [neg_mem_normalCone_iff]
  constructor
  · intro hg x hx hxlevel
    exact hg x ⟨hx, hxlevel⟩
  · intro hg x hx
    exact hg hx.1 hx.2

end
