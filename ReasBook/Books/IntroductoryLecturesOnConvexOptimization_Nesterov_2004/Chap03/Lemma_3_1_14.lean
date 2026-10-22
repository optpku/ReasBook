/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Theorem_3_1_8
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Definition_3_1_5

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open Set
open scoped WithTopConvexAnalysis

universe u v

variable {ι : Type u} {X : Type v}

/- Lemma 3.1.14 sits in the chapter's extended-valued convex-analysis domain of subset-indexed
pointwise suprema and constrained subdifferentials.

Sampled owner declarations:
- `pointwiseSupremumOn`
- `pointwiseSupremumOnEffectiveDomain`
- `ClosedConvexOn.pointwise_sSup`
- `constrainedSubdifferential`

Best owner abstraction:
- the subset-indexed pointwise-supremum owner surface from `Theorem_3_1_8`, together with the
  earlier owner notions `ClosedConvexOn` and `constrainedSubdifferential`

Primitive data:
- the owner pointwise-supremum object `pointwiseSupremumOn Δ φ`
- the owner finite-value domain `pointwiseSupremumOnEffectiveDomain Q Δ φ`
- the earlier chapter owners `ClosedConvexOn` and `constrainedSubdifferential`

Derived API in this file:
- the active-index set `activePointwiseSupremumOnIndices Δ φ x`
- the membership bridge `mem_activePointwiseSupremumOnIndices_iff`
- the active-slice convex-hull inclusion theorem

Source/core/bridge triage:
- source-facing: `activePointwiseSupremumOnIndices`,
  `convexHull_activePointwiseSupremumOnSubdifferentials_subset`
- core/canonical: `pointwiseSupremumOn`, `pointwiseSupremumOnEffectiveDomain`,
  `ClosedConvexOn`, `constrainedSubdifferential`, `ClosedConvexOn.pointwise_sSup`
- bridge/view: `mem_activePointwiseSupremumOnIndices_iff`

This file therefore adds only the active-slice layer from the source text and reuses the earlier
chapter owners directly instead of re-declaring them locally. Its source-facing inclusion theorem
inherits the intrinsic real-inner-product-space ambient assumptions already required by
`constrainedSubdifferential`, instead of freezing that theorem to the textbook Euclidean model. -/

/-- The active parameter set `I(x)` for the subset-indexed pointwise supremum over `Δ`. -/
def activePointwiseSupremumOnIndices
    (Δ : Set ι) (φ : X → ι → WithTop ℝ) (x : X) : Set ι :=
  {y | y ∈ Δ ∧ φ x y = pointwiseSupremumOn Δ φ x}

/-- Membership in `activePointwiseSupremumOnIndices Δ φ x` means that `y ∈ Δ` attains the
pointwise supremum value at `x`. -/
@[simp]
theorem mem_activePointwiseSupremumOnIndices_iff
    {Δ : Set ι} {φ : X → ι → WithTop ℝ} {x : X} {y : ι} :
    y ∈ activePointwiseSupremumOnIndices Δ φ x ↔
      y ∈ Δ ∧ φ x y = pointwiseSupremumOn Δ φ x :=
  Iff.rfl

variable {E : Type v} [SeminormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Helper for Lemma 3.1.14: every admissible slice value lies below the pointwise supremum. -/
lemma slice_le_pointwiseSupremumOn
    {Δ : Set ι} {φ : X → ι → WithTop ℝ} {x : X} {y : ι}
    (hy : y ∈ Δ) :
    φ x y ≤ pointwiseSupremumOn Δ φ x := by
  -- The chosen slice contributes one element to the supremum-defining image set.
  rw [pointwiseSupremumOn_apply]
  refine le_csSup ?_ ?_
  · exact ⟨⊤, fun _ _ ↦ le_top⟩
  · exact ⟨y, hy, rfl⟩

/-- Helper for Lemma 3.1.14: an active slice subgradient is a constrained subgradient of the
pointwise supremum on the effective domain. -/
lemma mem_constrainedSubdifferential_pointwiseSupremumOn_of_mem_active
    {Q : Set E} {Δ : Set ι} {φ : E → ι → WithTop ℝ} {x : E} {y : ι} {g : E}
    (hx : x ∈ pointwiseSupremumOnEffectiveDomain Q Δ φ)
    (hy : y ∈ activePointwiseSupremumOnIndices Δ φ x)
    (hg : g ∈ ∂[Q] (fun z ↦ φ z y)(x)) :
    g ∈ ∂[pointwiseSupremumOnEffectiveDomain Q Δ φ] (pointwiseSupremumOn Δ φ) (x) := by
  rcases (mem_pointwiseSupremumOnEffectiveDomain_iff.mp hx) with ⟨hxQ, hxdom⟩
  rcases (mem_activePointwiseSupremumOnIndices_iff.mp hy) with ⟨hyΔ, hyactive⟩
  rcases (mem_constrainedSubdifferential_iff.mp hg) with ⟨_, _, hsubgrad⟩
  rw [mem_constrainedSubdifferential_iff]
  refine ⟨hx, hxdom, ?_⟩
  intro z hz
  rcases (mem_pointwiseSupremumOnEffectiveDomain_iff.mp hz) with ⟨hzQ, _⟩
  -- Compare the active slice with the whole supremum, then rewrite the base-point value by
  -- activity of `y`.
  calc
    pointwiseSupremumOn Δ φ z ≥ φ z y := slice_le_pointwiseSupremumOn hyΔ
    _ ≥ φ x y + ↑(inner ℝ g (z - x)) := hsubgrad hzQ
    _ = pointwiseSupremumOn Δ φ x + ↑(inner ℝ g (z - x)) := by rw [hyactive]

/-- Helper for Lemma 3.1.14: every constrained subdifferential is convex in the subgradient
variable. -/
lemma convex_constrainedSubdifferential
    {Q : Set E} {f : E → WithTop ℝ} {x : E} :
    Convex ℝ (∂[Q] f(x)) := by
  rw [convex_iff_add_mem]
  intro g₁ hg₁ g₂ hg₂ a b ha hb hab
  rcases (mem_constrainedSubdifferential_iff.mp hg₁) with ⟨hxQ, hxdom, hg₁'⟩
  rcases (mem_constrainedSubdifferential_iff.mp hg₂) with ⟨_, _, hg₂'⟩
  rw [mem_constrainedSubdifferential_iff]
  refine ⟨hxQ, hxdom, ?_⟩
  intro y hyQ
  by_cases hyf : y ∈ dom f
  · -- On the effective domain both endpoint inequalities are real, so a convex combination of
    -- the slopes still satisfies the same support bound.
    have hg₁_withTop :
        (((withTopRealPart f x + inner ℝ g₁ (y - x) : ℝ) : WithTop ℝ) ≤ f y) := by
      rw [WithTop.coe_add, coe_withTopRealPart hxdom]
      exact hg₁' hyQ
    have hg₂_withTop :
        (((withTopRealPart f x + inner ℝ g₂ (y - x) : ℝ) : WithTop ℝ) ≤ f y) := by
      rw [WithTop.coe_add, coe_withTopRealPart hxdom]
      exact hg₂' hyQ
    have hg₁_real :
        withTopRealPart f x + inner ℝ g₁ (y - x) ≤ withTopRealPart f y :=
      (le_withTopRealPart_iff hyf).mpr hg₁_withTop
    have hg₂_real :
        withTopRealPart f x + inner ℝ g₂ (y - x) ≤ withTopRealPart f y :=
      (le_withTopRealPart_iff hyf).mpr hg₂_withTop
    have hslope₁ :
        inner ℝ g₁ (y - x) ≤ withTopRealPart f y - withTopRealPart f x := by
      linarith
    have hslope₂ :
        inner ℝ g₂ (y - x) ≤ withTopRealPart f y - withTopRealPart f x := by
      linarith
    have hcombo_real :
        withTopRealPart f x + inner ℝ (a • g₁ + b • g₂) (y - x) ≤ withTopRealPart f y := by
      rw [inner_add_left]
      have hsmul₁ :
          inner ℝ (a • g₁) (y - x) = a * inner ℝ g₁ (y - x) := by
        simpa using (inner_smul_left g₁ (y - x) a)
      have hsmul₂ :
          inner ℝ (b • g₂) (y - x) = b * inner ℝ g₂ (y - x) := by
        simpa using (inner_smul_left g₂ (y - x) b)
      rw [hsmul₁, hsmul₂]
      have hslope_combo :
          a * inner ℝ g₁ (y - x) + b * inner ℝ g₂ (y - x) ≤
            withTopRealPart f y - withTopRealPart f x := by
        let d : ℝ := withTopRealPart f y - withTopRealPart f x
        have hmul₁ :
            a * inner ℝ g₁ (y - x) ≤ a * d :=
          mul_le_mul_of_nonneg_left hslope₁ ha
        have hmul₂ :
            b * inner ℝ g₂ (y - x) ≤ b * d :=
          mul_le_mul_of_nonneg_left hslope₂ hb
        calc
          a * inner ℝ g₁ (y - x) + b * inner ℝ g₂ (y - x)
              ≤ a * d + b * d :=
            add_le_add hmul₁ hmul₂
          _ = (a + b) * d := by ring_nf
          _ = d := by rw [hab, one_mul]
          _ = withTopRealPart f y - withTopRealPart f x := rfl
      linarith
    have hcombo_withTop :
        (((withTopRealPart f x + inner ℝ (a • g₁ + b • g₂) (y - x) : ℝ) : WithTop ℝ) ≤ f y) :=
      (le_withTopRealPart_iff hyf).mp hcombo_real
    rw [WithTop.coe_add, coe_withTopRealPart hxdom] at hcombo_withTop
    exact hcombo_withTop
  · -- Outside the effective domain the value of `f` is `⊤`, so the support inequality is
    -- immediate.
    have htop : f y = ⊤ := by
      rw [mem_withTopEffectiveDomain_iff, lt_top_iff_ne_top] at hyf
      exact not_ne_iff.mp hyf
    simp [htop]

/-- Lemma 3.1.14, active-slice inclusion part: at every
`x ∈ pointwiseSupremumOnEffectiveDomain Q Δ φ`, the constrained subdifferential of
`pointwiseSupremumOn Δ φ` over `pointwiseSupremumOnEffectiveDomain Q Δ φ` contains the convex
hull of the constrained subdifferentials of the active slices `y ∈ I(x)`.

The closed-convex part of Lemma 3.1.14 is the separate owner theorem
`ClosedConvexOn.pointwise_sSup`. -/
-- Proof sketch: every `g ∈ constrainedSubdifferential Q (fun z ↦ φ z y) x` with active `y`
-- satisfies the subgradient inequality for `pointwiseSupremumOn Δ φ` because
-- `pointwiseSupremumOn Δ φ z ≥ φ z y` for all `z ∈ Q` and activity gives
-- `φ x y = pointwiseSupremumOn Δ φ x`. The target constrained subdifferential is convex, so it
-- contains the convex hull of the union of those active-slice subdifferentials.
theorem convexHull_activePointwiseSupremumOnSubdifferentials_subset
    {Q : Set E} {Δ : Set ι} {φ : E → ι → WithTop ℝ} {x : E}
    (hx : x ∈ pointwiseSupremumOnEffectiveDomain Q Δ φ) :
    convexHull ℝ
        (⋃ y ∈ activePointwiseSupremumOnIndices Δ φ x,
          ∂[Q] (fun z ↦ φ z y)(x)) ⊆
      ∂[pointwiseSupremumOnEffectiveDomain Q Δ φ] (pointwiseSupremumOn Δ φ) (x) := by
  -- First place each active-slice subgradient inside the target constrained subdifferential.
  refine convexHull_min ?_
    (convex_constrainedSubdifferential
      (Q := pointwiseSupremumOnEffectiveDomain Q Δ φ)
      (f := pointwiseSupremumOn Δ φ) (x := x))
  intro g hg
  rcases mem_iUnion.mp hg with ⟨y, hg⟩
  rcases mem_iUnion.mp hg with ⟨hy, hg⟩
  -- The transfer helper is exactly the source-faithful bridge from an active slice to the
  -- ambient pointwise supremum.
  exact mem_constrainedSubdifferential_pointwiseSupremumOn_of_mem_active hx hy hg

end
