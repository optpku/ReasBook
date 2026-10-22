/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat

-- Declarations for this item will be appended below by the statement pipeline.

section

variable {𝕜 E : Type*} [Ring 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
  [AddCommMonoid E] [Module 𝕜 E]

/-
Primary domain: convex analysis on affine modules over a linearly ordered ring, centered on the
owner predicate `ConvexOn 𝕜 Q f`.

Sampled owner-style declarations before refining this file:
* mathlib `ConvexOn`
* mathlib `convexOn_iff_forall_pos`
* mathlib `convexOn_iff_div`
* Chapter 2 `convexOn_iff_lower_tangent_plane` in `Definition_2_2`, the chapter's matching
  owner-to-textbook bridge for first-order convexity

Source/core/bridge triage:
* source-facing: the one-parameter Jensen inequality along segments in `Q`
* core/canonical: `ConvexOn 𝕜 Q f`
* bridge/view: rewriting the owner weights `(a, b)` as the single parameter `α ∈ Icc 0 1`

Primitive data:
* the feasible set `Q`
* the objective `f`
* convexity of `Q`, supplied separately as `hQ`
* the canonical owner predicate `ConvexOn 𝕜 Q f`

Derived API:
* the one-parameter segment inequality below, obtained by taking weights `α` and `1 - α`
* the converse reconstruction of the owner theorem from that source-facing form and `hQ`

The owner abstraction is `ConvexOn 𝕜 Q f`. The source theorem is stated for `ℝⁿ`, but this
segment-normalized bridge only uses the ordered-ring/module layer already supporting
`convexOn_iff_forall_pos`; no division or inverse-based data is needed. The textbook `C¹` side
condition is redundant for this item, so the refined public API omits it. -/

variable {Q : Set E} {f : E → 𝕜}

/-- Theorem 2.2: on a convex set `Q`, convexity of `f` is exactly the usual two-point Jensen
inequality along every segment in `Q`. Specializing `𝕜` to `ℝ` recovers the textbook setting. -/
-- Proof sketch: `ConvexOn 𝕜 Q f` packages the two-weight Jensen inequality. The displayed
-- source-facing formula is its specialization `b = 1 - α`; conversely, `convexOn_iff_forall_pos`
-- recovers the owner theorem from that normalized one-parameter form and `hQ`.
theorem convexOn_iff_segment_inequality
    (hQ : Convex 𝕜 Q) :
    ConvexOn 𝕜 Q f ↔
      ∀ ⦃x⦄, x ∈ Q → ∀ ⦃y⦄, y ∈ Q → ∀ ⦃α : 𝕜⦄, α ∈ Set.Icc (0 : 𝕜) 1 →
        f (α • x + (1 - α) • y) ≤ α * f x + (1 - α) * f y := by
  constructor
  · intro hf x hx y hy α hα
    have hsum : α + (1 - α) = 1 := by
      abel_nf
    simpa [smul_eq_mul] using hf.2 hx hy hα.1 (sub_nonneg.mpr hα.2) hsum
  · intro h
    rw [convexOn_iff_forall_pos]
    refine ⟨hQ, ?_⟩
    intro x hx y hy a b ha hb hab
    have ha' : a ∈ Set.Icc (0 : 𝕜) 1 := by
      refine ⟨le_of_lt ha, ?_⟩
      exact (by
        have ha_lt : a < 1 := by
          simpa [hab] using lt_add_of_pos_right a hb
        exact ha_lt.le)
    have hb_eq : b = 1 - a := by
      rw [eq_sub_iff_add_eq]
      simpa [add_comm] using hab
    simpa [smul_eq_mul, hb_eq] using h hx hy ha'

end
