/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Definition_3_12

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/- Theorem 3 1 13 is source-facing in the chapter's affine-nesterovHyperplane strong-separation domain.

Primary domain:
- strong separation of disjoint closed convex subsets of a finite-dimensional real inner-product
  space when one side is bounded.

Relevant sampled declarations:
- `AreStronglySeparable` in `Definition_3_12`, the chapter owner predicate for two-set strong
  separation by an affine nesterovHyperplane;
- mathlib `geometric_hahn_banach_compact_closed` and
  `geometric_hahn_banach_closed_compact`, the canonical strict-separation owners for compact/closed
  convex sets by continuous linear functionals;
- mathlib `Metric.isCompact_of_isClosed_isBounded` together with
  `FiniteDimensional.proper_real`, the finite-dimensional bounded-to-compact bridge.

Best owner abstraction:
- `AreStronglySeparable`

Primitive data:
- the sets `Q₁`, `Q₂`;
- closedness, convexity, disjointness, and one-sided boundedness on a nonempty side.

Derived API:
- the bounded-to-compact bridge in proper real inner-product spaces;
- the functional-to-nesterovHyperplane conversion through `InnerProductSpace.toDual`.

Source/core/bridge triage:
- source-facing: the textbook bounded-one-side strong-separation theorem, stated intrinsically on
  nontrivial proper real inner-product spaces with finite-dimensional `ℝⁿ` available as a
  specialization;
- core/canonical: the chapter owner `AreStronglySeparable` together with mathlib's compact/closed
  Hahn--Banach separation theorems;
- bridge/view: this file, which converts the source boundedness hypothesis to the canonical
  compactness input and then transports the resulting functional separator to the chapter's
  vector-normal nesterovHyperplane API.
-/

variable [ProperSpace E] [Nontrivial E]

/-- Theorem 3 1 13: if `Q₁, Q₂` are closed convex subsets of a nontrivial proper real
inner-product space with empty intersection, and one nonempty side is bounded, then they admit a
strongly separating nesterovHyperplane. Specializing to finite-dimensional Euclidean spaces recovers the
textbook `ℝⁿ` statement. -/
-- Proof sketch: if the bounded nonempty side faces an empty set, choose any nonzero normal and
-- place the affine level strictly beyond the bounded image of that side under the induced
-- functional. Otherwise, a closed bounded set is compact in a proper space, so the bounded side
-- can be fed to mathlib's compact/closed Hahn--Banach separation theorem. The resulting
-- continuous linear functional is represented by a vector through `InnerProductSpace.toDual`, and
-- the strict bounds are recentered at the midpoint between the two separating levels to produce
-- the chapter owner `AreStronglySeparable`.
theorem areStronglySeparable_of_disjoint_closed_convex_of_bounded_one_side
    (Q₁ Q₂ : Set E)
    (hQ₁_closed : IsClosed Q₁) (hQ₂_closed : IsClosed Q₂)
    (hQ₁_convex : Convex ℝ Q₁) (hQ₂_convex : Convex ℝ Q₂)
    (hdisj : Disjoint Q₁ Q₂)
    (hbounded : (Q₁.Nonempty ∧ Bornology.IsBounded Q₁) ∨
      (Q₂.Nonempty ∧ Bornology.IsBounded Q₂)) :
    AreStronglySeparable Q₁ Q₂ := by
  rw [areStronglySeparable_iff]
  rcases hbounded with ⟨hQ₁_nonempty, hQ₁_bounded⟩ | ⟨hQ₂_nonempty, hQ₂_bounded⟩
  · rcases Set.eq_empty_or_nonempty Q₂ with rfl | hQ₂_nonempty
    · obtain ⟨g, hg⟩ := exists_ne (0 : E)
      let f : E →L[ℝ] ℝ := (InnerProductSpace.toDual ℝ E) g
      rcases (hQ₁_bounded.image f).bddAbove with ⟨M, hM⟩
      refine ⟨g, hg, M + 1, ?_⟩
      constructor
      · intro x hx
        have hfxle : f x ≤ M := hM ⟨x, hx, rfl⟩
        simpa [f] using lt_of_le_of_lt hfxle (by linarith : M < M + 1)
      · intro y hy
        simp at hy
    · obtain ⟨f, u, v, hQ₁_lt, huv, hQ₂_lt⟩ :=
        geometric_hahn_banach_compact_closed hQ₁_convex
          (Metric.isCompact_of_isClosed_isBounded hQ₁_closed hQ₁_bounded)
          hQ₂_convex hQ₂_closed hdisj
      let g : E := (InnerProductSpace.toDual ℝ E).symm f
      refine ⟨g, ?_, (u + v) / 2, ?_⟩
      · intro hg
        have hf : f = 0 := by
          calc
            f = (InnerProductSpace.toDual ℝ E) g := by simp [g]
            _ = 0 := by simp [hg]
        rcases hQ₁_nonempty with ⟨x, hx⟩
        rcases hQ₂_nonempty with ⟨y, hy⟩
        have hxlt : 0 < u := by simpa [hf] using hQ₁_lt x hx
        have hygt : v < 0 := by simpa [hf] using hQ₂_lt y hy
        linarith
      · constructor
        · intro x hx
          have hxltu : f x < u := hQ₁_lt x hx
          have hu_mid : u < (u + v) / 2 := by linarith
          change inner ℝ g x < (u + v) / 2
          simpa [g] using hxltu.trans hu_mid
        · intro y hy
          have hvlty : v < f y := hQ₂_lt y hy
          have hmid_v : (u + v) / 2 < v := by linarith
          change (u + v) / 2 < inner ℝ g y
          simpa [g] using hmid_v.trans hvlty
  · rcases Set.eq_empty_or_nonempty Q₁ with rfl | hQ₁_nonempty
    · obtain ⟨g, hg⟩ := exists_ne (0 : E)
      let f : E →L[ℝ] ℝ := (InnerProductSpace.toDual ℝ E) g
      rcases (hQ₂_bounded.image f).bddBelow with ⟨m, hm⟩
      refine ⟨g, hg, m - 1, ?_⟩
      constructor
      · intro x hx
        simp at hx
      · intro y hy
        have hmle : m ≤ f y := hm ⟨y, hy, rfl⟩
        change m - 1 < inner ℝ g y
        simpa [f] using lt_of_lt_of_le (by linarith : m - 1 < m) hmle
    · obtain ⟨f, u, v, hQ₁_lt, huv, hQ₂_lt⟩ :=
        geometric_hahn_banach_closed_compact hQ₁_convex hQ₁_closed
          hQ₂_convex (Metric.isCompact_of_isClosed_isBounded hQ₂_closed hQ₂_bounded) hdisj
      let g : E := (InnerProductSpace.toDual ℝ E).symm f
      refine ⟨g, ?_, (u + v) / 2, ?_⟩
      · intro hg
        have hf : f = 0 := by
          calc
            f = (InnerProductSpace.toDual ℝ E) g := by simp [g]
            _ = 0 := by simp [hg]
        rcases hQ₁_nonempty with ⟨x, hx⟩
        rcases hQ₂_nonempty with ⟨y, hy⟩
        have hxlt : 0 < u := by simpa [hf] using hQ₁_lt x hx
        have hygt : v < 0 := by simpa [hf] using hQ₂_lt y hy
        linarith
      · constructor
        · intro x hx
          have hxltu : f x < u := hQ₁_lt x hx
          have hu_mid : u < (u + v) / 2 := by linarith
          change inner ℝ g x < (u + v) / 2
          simpa [g] using hxltu.trans hu_mid
        · intro y hy
          have hvlty : v < f y := hQ₂_lt y hy
          have hmid_v : (u + v) / 2 < v := by linarith
          change (u + v) / 2 < inner ℝ g y
          simpa [g] using hmid_v.trans hvlty

end
