/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import Mathlib.Analysis.InnerProductSpace.PiL2
import OptimizationTheoryAndMethods_SunYuan_2006.Chap01.Definition_1_3_26
import OptimizationTheoryAndMethods_SunYuan_2006.Chap01.Theorem_1_3_28

-- Semantic recall hits verified for this item:
-- `geometric_hahn_banach_closed_compact`, `Metric.isCompact_iff_isClosed_bounded`.

open scoped RealInnerProductSpace

section Theorem1329

variable {n : ℕ}

local notation "Point" => EuclideanSpace ℝ (Fin n)

/-- Chapter01 Theorem 1.3.29 (Strict Separation Theorem). If `S₁, S₂ ⊆ ℝ^n` are nonempty closed
convex sets, `S₂` is bounded, and `S₁` and `S₂` are disjoint, then there exist a nonzero vector
`p` and real numbers `α < β` such that `inner ℝ p x < α` for every `x ∈ S₁` and
`β < inner ℝ p x` for every `x ∈ S₂`.

The companion theorem below repackages the same conclusion using a single separating level. -/
theorem existsNonzeroStrictSeparatingVector
    (S₁ S₂ : Set Point) (hS₁_nonempty : S₁.Nonempty) (hS₂_nonempty : S₂.Nonempty)
    (hS₁_closed : IsClosed S₁) (hS₂_closed : IsClosed S₂)
    (hS₁_convex : Convex ℝ S₁) (hS₂_convex : Convex ℝ S₂)
    (hS₂_bounded : Bornology.IsBounded S₂) (hdisj : Disjoint S₁ S₂) :
    ∃ p : Point, p ≠ 0 ∧ ∃ α β : ℝ, α < β ∧
      (∀ x ∈ S₁, inner ℝ p x < α) ∧ ∀ x ∈ S₂, β < inner ℝ p x := by
  have hPoint : Nontrivial Point := by
    rcases hS₁_nonempty with ⟨x₁, hx₁⟩
    rcases hS₂_nonempty with ⟨x₂, hx₂⟩
    refine nontrivial_iff.2 ⟨x₁, x₂, ?_⟩
    intro h
    exact Set.disjoint_left.1 hdisj hx₁ (h ▸ hx₂)
  letI := hPoint
  obtain ⟨p, a, hp⟩ :=
    existsNonzeroStrongSeparatingVector S₁ S₂ hS₂_nonempty hS₁_closed hS₂_closed
      hS₁_convex hS₂_convex hS₂_bounded hdisj
  rw [stronglySeparates_iff] at hp
  rcases hp with ⟨hp, ε, hε, hS₂, hS₁⟩
  refine ⟨p, hp, a + ε / 3, a + 2 * ε / 3, ?_, ?_, ?_⟩
  · linarith
  · intro x hx
    have hx' := hS₁ x hx
    linarith
  · intro x hx
    have hx' := hS₂ x hx
    linarith

/-- Theorem 1.3.29 also yields the chapter's canonical strict-separation predicate: one may
choose a nonzero normal `p` and a level `γ` such that the sunYuanHyperplane `sunYuanHyperplane p γ` strictly
separates `S₂` from `S₁`, equivalently `γ < inner ℝ p x` on `S₂` and `inner ℝ p x < γ` on `S₁`.
This is obtained from the source-facing `α < β` statement by choosing the midpoint
`γ = (α + β) / 2`. -/
theorem existsNonzeroStrictSeparatingLevel
    (S₁ S₂ : Set Point) (hS₁_nonempty : S₁.Nonempty) (hS₂_nonempty : S₂.Nonempty)
    (hS₁_closed : IsClosed S₁) (hS₂_closed : IsClosed S₂)
    (hS₁_convex : Convex ℝ S₁) (hS₂_convex : Convex ℝ S₂)
    (hS₂_bounded : Bornology.IsBounded S₂) (hdisj : Disjoint S₁ S₂) :
    ∃ p : Point, ∃ γ : ℝ, strictlySeparates S₂ S₁ p γ := by
  obtain ⟨p, hp, α, β, hαβ, hS₁, hS₂⟩ :=
    existsNonzeroStrictSeparatingVector S₁ S₂ hS₁_nonempty hS₂_nonempty hS₁_closed hS₂_closed
      hS₁_convex hS₂_convex hS₂_bounded hdisj
  refine ⟨p, (α + β) / 2, ?_⟩
  rw [strictlySeparates_iff]
  refine ⟨hp, ?_, ?_⟩
  · intro x hx
    have hx' := hS₂ x hx
    linarith
  · intro x hx
    have hx' := hS₁ x hx
    linarith

end Theorem1329
