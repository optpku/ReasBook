/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

section

universe u v

variable {𝕜 : Type u} {E : Type v}
variable [Semiring 𝕜] [PartialOrder 𝕜] [AddCommMonoid E] [SMul 𝕜 E]

/- Definition 2.3 lies in the convex-geometry domain for subsets of finite-dimensional real vector
spaces.

Primary domain:
* convex subsets `Q ⊆ ℝⁿ`

Sampled owner-style declarations:
* mathlib `Convex`
* mathlib `convex_iff_add_mem`
* mathlib `Convex.segment_subset`
* mathlib `Convex.inter`

Best owner abstraction:
* `Convex ℝ Q`

Primitive data:
* the subset `Q : Set (EuclideanSpace ℝ (Fin n))`

Derived API:
* the textbook two-point convex-combination criterion `convex_iff_add_mem`
* segment closure via `Convex.segment_subset`
* stability under intersection via `Convex.inter`

Source/core/bridge triage:
* source-facing: a convex subset of `ℝⁿ`
* core/canonical: `Convex ℝ Q`
* bridge/view: the two-point convex-combination membership formula

This file therefore keeps no local wrapper such as `IsConvexSet`. Downstream files should use the
owner predicate `Convex ℝ Q` directly, and use `convex_iff_add_mem` only as the companion
source-style specification theorem. This file is therefore recall-only. -/

/- The core owner is the canonical type expression `Convex 𝕜 : Set E → Prop`. -/
#check (Convex 𝕜 : Set E → Prop)

/-- Helper for Definition 2.3: the canonical owner predicate `Convex 𝕜 s` is equivalent to the
textbook two-point convex-combination membership condition. -/
theorem convex_iff_two_point_combination_mem {s : Set E} :
    Convex 𝕜 s ↔
      ∀ ⦃x : E⦄, x ∈ s → ∀ ⦃y : E⦄, y ∈ s → ∀ ⦃a b : 𝕜⦄,
        0 ≤ a → 0 ≤ b → a + b = 1 → a • x + b • y ∈ s := by
  -- This is exactly the source-facing reformulation already provided by mathlib.
  simpa using
    (convex_iff_add_mem :
      Convex 𝕜 s ↔
        ∀ ⦃x : E⦄, x ∈ s → ∀ ⦃y : E⦄, y ∈ s → ∀ ⦃a b : 𝕜⦄,
          0 ≤ a → 0 ≤ b → a + b = 1 → a • x + b • y ∈ s)

/-- Definition 2.3: a set `Q ⊆ ℝⁿ` is convex exactly when it contains every two-point convex
combination `α • x + (1 - α) • y` with `α ∈ [0, 1]`. -/
theorem convex_iff_unit_interval_smul_add_mem {n : ℕ}
    {Q : Set (EuclideanSpace ℝ (Fin n))} :
    Convex ℝ Q ↔
      ∀ ⦃x : EuclideanSpace ℝ (Fin n)⦄, x ∈ Q →
        ∀ ⦃y : EuclideanSpace ℝ (Fin n)⦄, y ∈ Q →
          ∀ ⦃α : ℝ⦄, 0 ≤ α → α ≤ 1 → α • x + (1 - α) • y ∈ Q := by
  constructor
  · intro hQ x hx y hy α hα hα_le_one
    -- Use the complementary weight `1 - α`, which is nonnegative on `[0, 1]`.
    exact hQ hx hy hα (sub_nonneg.mpr hα_le_one) (by ring)
  · intro hQ x hx y hy α β hα hβ hαβ
    -- Rewrite the second weight as `1 - α` to return to the source-facing criterion.
    have hα_le_one : α ≤ 1 := by
      linarith
    have hmem : α • x + (1 - α) • y ∈ Q := hQ hx hy hα hα_le_one
    have hβ_eq : β = 1 - α := by
      linarith
    simpa [hβ_eq] using hmem

recall convex_iff_add_mem

recall Convex.segment_subset

recall Convex.inter

end
