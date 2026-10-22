/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import OptimizationTheoryAndMethods_SunYuan_2006.Chap02.Definition_2_1_3

-- Semantic recall: `lean_leansearch` surfaced `StrictAntiOn` and `StrictMonoOn`
-- as the canonical mathlib interval-monotonicity predicates behind the
-- shared owner `unimodalOn` from `Chapter02 Definition 2.1.3`.

open Set

universe u v

variable {α : Type u} {β : Type v} [LinearOrder α] [Preorder β]

/-- Chapter02 Theorem 2.1.5 (1). Assume `φ` is unimodal on `Icc a b`.
Let `α₁, α₂ ∈ Icc a b` satisfy `α₁ < α₂` and `φ α₁ ≤ φ α₂`. Then
`Icc a α₂` is a unimodal interval related to `φ`. -/
theorem unimodalOn_left_of_apply_le {φ : α → β} {a b α₁ α₂ : α}
    (h : unimodalOn φ a b)
    (hα₁ : α₁ ∈ Icc a b) (hα₂ : α₂ ∈ Icc a b)
    (hα : α₁ < α₂) (hφ : φ α₁ ≤ φ α₂) :
    unimodalOn φ a α₂ := by
  rcases h.exists_turningPoint with ⟨αStar, hαStar, hanti, hmono⟩
  have hαStar_le_α₂ : αStar ≤ α₂ := by
    by_contra hαStar_le_α₂
    have hα₂_lt_αStar : α₂ < αStar := lt_of_not_ge hαStar_le_α₂
    exact (not_lt_of_ge hφ) <|
      hanti ⟨hα₁.1, (hα.trans hα₂_lt_αStar).le⟩ ⟨hα₂.1, hα₂_lt_αStar.le⟩ hα
  refine ⟨αStar, ⟨hαStar.1, hαStar_le_α₂⟩, hanti, ?_⟩
  intro x hx y hy hxy
  exact hmono ⟨hx.1, hx.2.trans hα₂.2⟩ ⟨hy.1, hy.2.trans hα₂.2⟩ hxy

/-- Chapter02 Theorem 2.1.5 (2). Assume `φ` is unimodal on `Icc a b`.
Let `α₁, α₂ ∈ Icc a b` satisfy `α₁ < α₂` and `φ α₁ ≥ φ α₂`. Then
`Icc α₁ b` is a unimodal interval related to `φ`. -/
theorem unimodalOn_right_of_apply_ge {φ : α → β} {a b α₁ α₂ : α}
    (h : unimodalOn φ a b)
    (hα₁ : α₁ ∈ Icc a b) (hα₂ : α₂ ∈ Icc a b)
    (hα : α₁ < α₂) (hφ : φ α₁ ≥ φ α₂) :
    unimodalOn φ α₁ b := by
  rcases h.exists_turningPoint with ⟨αStar, hαStar, hanti, hmono⟩
  have hα₁_le_αStar : α₁ ≤ αStar := by
    by_contra hα₁_le_αStar
    have hαStar_lt_α₁ : αStar < α₁ := lt_of_not_ge hα₁_le_αStar
    exact (not_lt_of_ge hφ) <|
      hmono ⟨hαStar_lt_α₁.le, hα₁.2⟩ ⟨(hαStar_lt_α₁.trans hα).le, hα₂.2⟩ hα
  refine ⟨αStar, ⟨hα₁_le_αStar, hαStar.2⟩, ?_, hmono⟩
  intro x hx y hy hxy
  exact hanti ⟨hα₁.1.trans hx.1, hx.2⟩ ⟨hα₁.1.trans hy.1, hy.2⟩ hxy
