/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Topology.MetricSpace.Bounded
import OptimizationTheoryAndMethods_SunYuan_2006.Chap01.Definition_1_3_26

-- Semantic recall hits verified for this item:
-- `geometric_hahn_banach_closed_compact`, `Metric.isCompact_iff_isClosed_bounded`,
-- `InnerProductSpace.toDual`, `IsCompact.exists_sInf_image_eq_and_le`.
-- Domain sampling:
-- * primary domain: strong sunYuanHyperplane separation of convex subsets in a real inner-product space
-- * owner abstractions inspected:
--   `stronglySeparates`,
--   `stronglySeparates_iff`,
--   `geometric_hahn_banach_closed_compact`,
--   `Metric.isCompact_iff_isClosed_bounded`,
--   `InnerProductSpace.toDual`,
--   `IsCompact.exists_sInf_image_eq_and_le`
-- * best owner abstraction: the chapter owner `stronglySeparates`; mathlib's Hahn-Banach theorem
--   and Fréchet-Riesz identification are proof engines, not the public owner
-- Source/core/bridge triage:
-- * source-facing: `stronglySeparates S₂ S₁ p α`
-- * core/canonical: compact-closed separation via `geometric_hahn_banach_closed_compact`
-- * bridge/view: `InnerProductSpace.toDual` turns the separating functional into a vector normal
-- Primitive data vs derived API:
-- * primitive data: a nonzero normal `p`, a separating level `α`, and a positive margin
-- * derived API: the source inequalities recovered from `stronglySeparates_iff`

open scoped RealInnerProductSpace

section Theorem1328

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [ProperSpace E]
  [Nontrivial E]

/-- Chapter01 Theorem 1.3.28 (Strong Separation Theorem). If `S₁, S₂` are closed convex
subsets of a nontrivial proper real inner-product space, `S₂` is nonempty bounded, and
`S₁` and `S₂` are disjoint, then there exist a nonzero vector `p` and real numbers `α` and
`ε > 0` such that
`α + ε ≤ inner ℝ p z` for every `z ∈ S₂` and `inner ℝ p x ≤ α` for every `x ∈ S₁`.

This is the source's explicit margin form of strong separation, with `S₂` on the upper side of the
separating sunYuanHyperplane and `S₁` on the lower side. The chapter owner for exactly this data is
`stronglySeparates S₂ S₁ p α`, so the theorem returns that owner directly rather than a parallel
tuple of subtype witnesses and pointwise inequalities. -/
theorem existsNonzeroStrongSeparatingVector
    (S₁ S₂ : Set E) (hS₂_nonempty : S₂.Nonempty)
    (hS₁_closed : IsClosed S₁) (hS₂_closed : IsClosed S₂)
    (hS₁_convex : Convex ℝ S₁) (hS₂_convex : Convex ℝ S₂)
    (hS₂_bounded : Bornology.IsBounded S₂) (hdisj : Disjoint S₁ S₂) :
    ∃ p : E, ∃ α : ℝ, stronglySeparates S₂ S₁ p α := by
  classical
  have hS₂_compact : IsCompact S₂ :=
    (Metric.isCompact_iff_isClosed_bounded.2 ⟨hS₂_closed, hS₂_bounded⟩)
  obtain rfl | hS₁_nonempty := S₁.eq_empty_or_nonempty
  · obtain ⟨p, hp⟩ := (nontrivial_iff_exists_ne (0 : E)).mp inferInstance
    have hinner : Continuous fun x : E ↦ inner ℝ p x := by
      simpa using continuous_const.inner continuous_id
    obtain ⟨x₂, hx₂, _, hx₂_min⟩ :=
      hS₂_compact.exists_sInf_image_eq_and_le hS₂_nonempty hinner.continuousOn
    refine ⟨p, inner ℝ p x₂ - 1, ?_⟩
    rw [stronglySeparates_iff]
    refine ⟨hp, 1, by norm_num, ?_, ?_⟩
    · intro x hx
      have hx₂x : inner ℝ p x₂ ≤ inner ℝ p x := hx₂_min x hx
      linarith
    · simp
  · obtain ⟨f, α, β, hS₁_lt, hαβ, hS₂_gt⟩ :=
      geometric_hahn_banach_closed_compact hS₁_convex hS₁_closed hS₂_convex hS₂_compact hdisj
    let p : E := (InnerProductSpace.toDual ℝ E).symm f
    refine ⟨p, α, ?_⟩
    rw [stronglySeparates_iff]
    refine ⟨?_, β - α, sub_pos.mpr hαβ, ?_, ?_⟩
    · intro hp
      have hf0 : f = 0 := by
        simpa [p] using congrArg (InnerProductSpace.toDual ℝ E) hp
      rcases hS₁_nonempty with ⟨x₁, hx₁⟩
      rcases hS₂_nonempty with ⟨x₂, hx₂⟩
      have hα : 0 < α := by
        simpa [hf0] using hS₁_lt x₁ hx₁
      have hβ : β < 0 := by
        simpa [hf0] using hS₂_gt x₂ hx₂
      linarith
    · intro x hx
      have hx' : β < inner ℝ p x := by
        simpa [p, InnerProductSpace.toDual_symm_apply] using hS₂_gt x hx
      linarith
    · intro x hx
      have hx' : inner ℝ p x < α := by
        simpa [p, InnerProductSpace.toDual_symm_apply] using hS₁_lt x hx
      exact hx'.le

end Theorem1328
