/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import OptimizationTheoryAndMethods_SunYuan_2006.Chap01.Corollary_1_3_25
import OptimizationTheoryAndMethods_SunYuan_2006.Chap01.Definition_1_3_26

/-!
Chapter01 Theorem 1.3.27 lives in convex separation.

Domain sampling:
* chapter owner for sunYuanHyperplane separation:
  `separates`,
  `separates_iff`;
* chapter owner for one-set closure separation:
  `existsNonzeroSupportingVectorOnClosureOfNotMem`;
* mathlib closure-transport API:
  `image_closure_subset_closure_image`,
  `closure_prod_eq`;
* mathlib convex-set difference owner:
  `Convex.sub`.

Best owner abstraction:
* the source-facing owner for this theorem is
  `separates (closure S₂) (closure S₁) p α`;
* the proof engine is the chapter owner
  `existsNonzeroSupportingVectorOnClosureOfNotMem` applied to the difference set `S₁ - S₂`;
* the pairwise closure inequality is a thin bridge recovered from `separates_iff`.

Source/core/bridge triage:
* `source-facing`: `existsNonzeroSeparatingVectorOnClosures`;
* `core/canonical`: `existsNonzeroSupportingVectorOnClosureOfNotMem`;
* `bridge/view`: `existsPairwiseInnerLeOnClosures`, obtained by transporting closure points
  `(x₁, x₂) ∈ closure S₁ × closure S₂` to `x₁ - x₂ ∈ closure (S₁ - S₂)`.

Primitive data:
* `S₁`, `S₂`, their nonemptiness, convexity, and disjointness.

Derived API:
* a separating sunYuanHyperplane for `closure S₂` and `closure S₁`;
* the pairwise inequality `⟪p, x₁⟫ ≤ ⟪p, x₂⟫` on `closure S₁ × closure S₂`.
-/

section Theorem1327

open Set
open scoped Pointwise RealInnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

omit [InnerProductSpace ℝ E] [CompleteSpace E] in
private theorem sub_mem_closure_sub {S₁ S₂ : Set E} {x₁ x₂ : E}
    (hx₁ : x₁ ∈ closure S₁) (hx₂ : x₂ ∈ closure S₂) :
    x₁ - x₂ ∈ closure (S₁ - S₂) := by
  have hsub :
      (fun z : E × E ↦ z.1 - z.2) '' closure (S₁ ×ˢ S₂) ⊆ closure (S₁ - S₂) := by
    simpa [sub_image_prod] using
      (image_closure_subset_closure_image
        (continuous_fst.sub continuous_snd) :
          (fun z : E × E ↦ z.1 - z.2) '' closure (S₁ ×ˢ S₂) ⊆
            closure ((fun z : E × E ↦ z.1 - z.2) '' (S₁ ×ˢ S₂)))
  have hpair : (x₁, x₂) ∈ closure (S₁ ×ˢ S₂) := by
    simpa [closure_prod_eq] using show x₁ ∈ closure S₁ ∧ x₂ ∈ closure S₂ from ⟨hx₁, hx₂⟩
  exact hsub ⟨(x₁, x₂), hpair, rfl⟩

private theorem exists_pairwise_inner_le_on_closures
    (S₁ S₂ : Set E) (hS₁_nonempty : S₁.Nonempty) (hS₂_nonempty : S₂.Nonempty)
    (hS₁_convex : Convex ℝ S₁) (hS₂_convex : Convex ℝ S₂) (hdisj : Disjoint S₁ S₂) :
    ∃ p : E, p ≠ 0 ∧
      ∀ x₁ ∈ closure S₁, ∀ x₂ ∈ closure S₂, inner ℝ p x₁ ≤ inner ℝ p x₂ := by
  obtain ⟨p, hp, hp_sep⟩ :=
    existsNonzeroSupportingVectorOnClosureOfNotMem
      (S₁ - S₂) (hS₁_nonempty.sub hS₂_nonempty) (hS₁_convex.sub hS₂_convex) 0 <| by
        intro h0
        rcases h0 with ⟨x₁, hx₁, x₂, hx₂, hsub⟩
        exact Set.disjoint_left.1 hdisj hx₁ (sub_eq_zero.mp hsub ▸ hx₂)
  refine ⟨p, hp, ?_⟩
  intro x₁ hx₁ x₂ hx₂
  have hsub : x₁ - x₂ ∈ closure (S₁ - S₂) := sub_mem_closure_sub hx₁ hx₂
  have hinner : inner ℝ p ((x₁ - x₂) - 0) ≤ (0 : ℝ) := hp_sep (x₁ - x₂) hsub
  simpa [inner_sub_right, sub_nonpos] using hinner

/-- Chapter01 Theorem 1.3.27 (Separation Theorem): if `S₁, S₂` are nonempty convex sets in a
complete real inner-product space and `S₁ ∩ S₂ = ∅`, then the closures of `S₂` and `S₁` admit a
separating sunYuanHyperplane. The source states this on `ℝ^n`; the Hilbert-space formulation is the
natural owner level because the proof is exactly Corollary 1.3.25 applied to the difference set
`S₁ - S₂`, and the chapter’s canonical separation owner is `separates`. -/
theorem existsNonzeroSeparatingVectorOnClosures
    (S₁ S₂ : Set E) (hS₁_nonempty : S₁.Nonempty) (hS₂_nonempty : S₂.Nonempty)
    (hS₁_convex : Convex ℝ S₁) (hS₂_convex : Convex ℝ S₂) (hdisj : Disjoint S₁ S₂) :
    ∃ p : E, ∃ α : ℝ, separates (closure S₂) (closure S₁) p α := by
  obtain ⟨p, hp, hp_pairwise⟩ :=
    exists_pairwise_inner_le_on_closures S₁ S₂ hS₁_nonempty hS₂_nonempty hS₁_convex hS₂_convex
      hdisj
  rcases hS₂_nonempty.closure with ⟨x₂, hx₂⟩
  let T : Set ℝ := (fun x : E ↦ inner ℝ p x) '' closure S₁
  have hT_nonempty : T.Nonempty := by
    rcases hS₁_nonempty.closure with ⟨x₁, hx₁⟩
    exact ⟨inner ℝ p x₁, ⟨x₁, hx₁, rfl⟩⟩
  have hT_bddAbove : BddAbove T := by
    refine ⟨inner ℝ p x₂, ?_⟩
    intro y hy
    rcases hy with ⟨x₁, hx₁, rfl⟩
    exact hp_pairwise x₁ hx₁ x₂ hx₂
  refine ⟨p, sSup T, ?_⟩
  rw [separates_iff]
  refine ⟨hp, ?_, ?_⟩
  · intro x hx
    exact csSup_le hT_nonempty fun y hy ↦ by
      rcases hy with ⟨x₁, hx₁, rfl⟩
      exact hp_pairwise x₁ hx₁ x hx
  · intro x hx
    exact le_csSup hT_bddAbove ⟨x, hx, rfl⟩

/-- Theorem 1.3.27 also recovers the source’s pairwise inequality form on
`closure S₁ × closure S₂`. This is a thin companion to the canonical `separates` statement. -/
theorem existsPairwiseInnerLeOnClosures
    (S₁ S₂ : Set E) (hS₁_nonempty : S₁.Nonempty) (hS₂_nonempty : S₂.Nonempty)
    (hS₁_convex : Convex ℝ S₁) (hS₂_convex : Convex ℝ S₂) (hdisj : Disjoint S₁ S₂) :
    ∃ p : E, p ≠ 0 ∧
      ∀ x₁ ∈ closure S₁, ∀ x₂ ∈ closure S₂, inner ℝ p x₁ ≤ inner ℝ p x₂ := by
  obtain ⟨p, α, hp_sep⟩ :=
    existsNonzeroSeparatingVectorOnClosures S₁ S₂ hS₁_nonempty hS₂_nonempty hS₁_convex hS₂_convex
      hdisj
  rw [separates_iff] at hp_sep
  rcases hp_sep with ⟨hp, hS₂, hS₁⟩
  refine ⟨p, hp, ?_⟩
  intro x₁ hx₁ x₂ hx₂
  exact (hS₁ x₁ hx₁).trans (hS₂ x₂ hx₂)

end Theorem1327
