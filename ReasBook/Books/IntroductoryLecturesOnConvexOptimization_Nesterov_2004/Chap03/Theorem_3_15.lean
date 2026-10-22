/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Theorem_3_1_13

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

variable {n : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin n)

/- Theorem 3.15 lies in the chapter's strong-separation domain for disjoint closed convex sets in
`ℝⁿ`.

Relevant sampled declarations:
- the chapter owner predicate `AreStronglySeparable` and its coordinate bridge
  `areStronglySeparable_iff` in `Definition_3_12`;
- the project theorem `areStronglySeparable_of_disjoint_closed_convex_of_bounded_one_side` in
  `Theorem_3_1_13`, the canonical one-sided-bounded strong-separation owner theorem;
- mathlib `geometric_hahn_banach_compact_closed`, the compact/closed strong-separation theorem;
- mathlib `geometric_hahn_banach_closed_compact`, the symmetric closed/compact variant;
- mathlib `Metric.isCompact_of_isClosed_isBounded`, the bounded-to-compact bridge in Euclidean
  spaces, already internalized by `Theorem_3_1_13`.

Best owner abstraction:
- `AreStronglySeparable`.

Primitive data:
- the sets `Q₁`, `Q₂`;
- nonemptiness, closedness, convexity, disjointness, and one-sided boundedness.

Derived API:
- the owner-level separation `AreStronglySeparable Q₂ Q₁`;
- the coordinate witness `g ≠ 0`, `γ` recovered from `areStronglySeparable_iff`.

Source/core/bridge triage:
- source-facing: this textbook coordinate theorem surface in `ℝⁿ`;
- core/canonical: `AreStronglySeparable`;
- bridge/view: this file, which re-expresses the owner theorem on the swapped pair `(Q₂, Q₁)` via
  `areStronglySeparable_iff`.
-/

/-- Theorem 3.15: if `Q₁, Q₂ ⊆ ℝⁿ` are nonempty closed convex sets with empty intersection, and at
least one of them is bounded, then there exist a nonzero vector `g` and a scalar `γ` such that
`⟪g, x⟫ < γ` for every `x ∈ Q₂` and `γ < ⟪g, y⟫` for every `y ∈ Q₁`. -/
-- Proof sketch: reduce the bounded side to a compact convex set, apply the appropriate geometric
-- Hahn--Banach strict-separation theorem, and recenter the two strict bounds at an intermediate
-- value `γ`.
theorem areStronglySeparable_of_disjoint_closed_convex_of_one_bounded
    (Q₁ Q₂ : Set E) (hQ₁_nonempty : Q₁.Nonempty) (hQ₂_nonempty : Q₂.Nonempty)
    (hQ₁_closed : IsClosed Q₁) (hQ₂_closed : IsClosed Q₂)
    (hQ₁_convex : Convex ℝ Q₁) (hQ₂_convex : Convex ℝ Q₂)
    (hdisj : Disjoint Q₁ Q₂)
    (hbounded : Bornology.IsBounded Q₁ ∨ Bornology.IsBounded Q₂) :
    ∃ (g : E) (_ : g ≠ 0) (γ : ℝ),
      (∀ x ∈ Q₂, inner ℝ g x < γ) ∧
      ∀ y ∈ Q₁, γ < inner ℝ g y := by
  have hE_nontrivial : Nontrivial E := by
    rcases subsingleton_or_nontrivial E with hE_sub | hE_nontrivial
    · rcases hQ₁_nonempty with ⟨x, hx⟩
      rcases hQ₂_nonempty with ⟨y, hy⟩
      have hxy : x = y := hE_sub.elim _ _
      exact False.elim ((Set.disjoint_left.mp hdisj hx) (hxy ▸ hy))
    · exact hE_nontrivial
  letI : Nontrivial E := hE_nontrivial
  have hstrong : AreStronglySeparable Q₂ Q₁ := by
    refine areStronglySeparable_of_disjoint_closed_convex_of_bounded_one_side
      Q₂ Q₁ hQ₂_closed hQ₁_closed hQ₂_convex hQ₁_convex hdisj.symm ?_
    rcases hbounded with hQ₁_bounded | hQ₂_bounded
    · right
      exact ⟨hQ₁_nonempty, hQ₁_bounded⟩
    · left
      exact ⟨hQ₂_nonempty, hQ₂_bounded⟩
  rcases areStronglySeparable_iff.mp hstrong with ⟨g, hg, γ, hsep⟩
  exact ⟨g, hg, γ, fun x hx ↦ by simpa using hsep.1 x hx, fun y hy ↦ by simpa using hsep.2 y hy⟩

end
