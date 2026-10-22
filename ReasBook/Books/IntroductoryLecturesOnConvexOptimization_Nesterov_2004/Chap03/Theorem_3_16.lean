/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap02.Lemma_2_13
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap02.Theorem_2_33
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Definition_3_12

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- Helper for Theorem 3.16: the displacement from a point outside `Q` to its Euclidean
projection on `Q` is nonzero. -/
lemma projection_displacement_ne_zero
    (Q : Set E) (hQ_nonempty : Q.Nonempty) {x : E} (hQ_closed : IsClosed Q)
    (hQ_convex : Convex ℝ Q) (hx : x ∉ Q) :
    x - euclideanProjection Q hQ_nonempty hQ_closed hQ_convex x ≠ 0 := by
  -- The projection point belongs to `Q`, so a zero displacement would force `x ∈ Q`.
  let p := euclideanProjection Q hQ_nonempty hQ_closed hQ_convex x
  have hp : IsProjectionPointOn Q x p := by
    simpa [p] using
      euclideanProjection_isProjectionPointOn Q hQ_nonempty hQ_closed hQ_convex x
  intro hzero
  have hxp : x = p := sub_eq_zero.mp hzero
  exact hx (hxp.symm ▸ hp.1)

/-- Helper for Theorem 3.16: the projection variational inequality bounds every feasible inner
product by the projection value against the projection displacement. -/
lemma projection_inner_le_projection_value
    (Q : Set E) (hQ_nonempty : Q.Nonempty) {x y : E} (hQ_closed : IsClosed Q)
    (hQ_convex : Convex ℝ Q) (hy : y ∈ Q) :
    inner ℝ (x - euclideanProjection Q hQ_nonempty hQ_closed hQ_convex x) y ≤
      inner ℝ (x - euclideanProjection Q hQ_nonempty hQ_closed hQ_convex x)
        (euclideanProjection Q hQ_nonempty hQ_closed hQ_convex x) := by
  -- Rewrite the projection variational inequality into the source-facing support inequality.
  let p := euclideanProjection Q hQ_nonempty hQ_closed hQ_convex x
  have hp : IsProjectionPointOn Q x p := by
    simpa [p] using
      euclideanProjection_isProjectionPointOn Q hQ_nonempty hQ_closed hQ_convex x
  have hinner : inner ℝ (x - p) (y - p) ≤ 0 := by
    have hproj : 0 ≤ inner ℝ (p - x) (y - p) :=
      hp.inner_sub_nonneg hQ_convex hy
    have hproj' : 0 ≤ -inner ℝ (x - p) (y - p) := by
      rw [← inner_neg_left]
      simpa [sub_eq_add_neg] using hproj
    exact neg_nonneg.mp hproj'
  -- Expand `y` around the projection point to isolate the controlled displacement term.
  calc
    inner ℝ (x - p) y = inner ℝ (x - p) ((y - p) + p) := by abel_nf
    _ = inner ℝ (x - p) (y - p) + inner ℝ (x - p) p := by
      rw [inner_add_right]
    _ ≤ 0 + inner ℝ (x - p) p := by
      linarith
    _ = inner ℝ (x - p) p := by
      simp

/-- Helper for Theorem 3.16: the projection point lies strictly below the exterior point along the
projection displacement functional. -/
lemma projection_value_lt_point_value
    (Q : Set E) (hQ_nonempty : Q.Nonempty) {x : E} (hQ_closed : IsClosed Q)
    (hQ_convex : Convex ℝ Q) (hx : x ∉ Q) :
    inner ℝ (x - euclideanProjection Q hQ_nonempty hQ_closed hQ_convex x)
        (euclideanProjection Q hQ_nonempty hQ_closed hQ_convex x) <
      inner ℝ (x - euclideanProjection Q hQ_nonempty hQ_closed hQ_convex x) x := by
  -- The gap equals `‖x - p‖²`, which is positive because `x` lies outside `Q`.
  let p := euclideanProjection Q hQ_nonempty hQ_closed hQ_convex x
  have hne : x - p ≠ 0 := by
    simpa [p] using
      projection_displacement_ne_zero Q hQ_nonempty hQ_closed hQ_convex hx
  have hrewrite :
      inner ℝ (x - p) x =
        inner ℝ (x - p) p + ‖x - p‖ ^ (2 : ℕ) := by
    calc
      inner ℝ (x - p) x = inner ℝ (x - p) (p + (x - p)) := by
        congr 1
        abel_nf
      _ = inner ℝ (x - p) p + inner ℝ (x - p) (x - p) := by
        rw [inner_add_right]
      _ = inner ℝ (x - p) p + ‖x - p‖ ^ (2 : ℕ) := by
        rw [real_inner_self_eq_norm_sq]
  have hpos : 0 < ‖x - p‖ ^ (2 : ℕ) := by
    exact sq_pos_of_ne_zero (norm_ne_zero_iff.mpr hne)
  linarith

/-- Theorem 3.16: if `Q` is a nonempty closed convex subset of a real inner-product space and
`x ∉ Q`, then there exist `a ≠ 0` and `b : ℝ` with `⟪a, x⟫ > b ≥ sup_{y ∈ Q} ⟪a, y⟫`;
equivalently, in the local Chapter 3 API, `Q` and the singleton `{x}` are strongly separable by a
nesterovHyperplane. -/
-- Proof sketch: follow the source proof via the Euclidean projection `p` of `x` onto `Q`; the
-- normal `a = x - p` supports `Q` at `p`, and the midpoint between `⟪a, p⟫` and `⟪a, x⟫` gives a
-- strict offset.
theorem areStronglySeparable_singleton_of_nonmem_closed_convex
    (Q : Set E) (hQ_nonempty : Q.Nonempty) {x : E} (hQ_closed : IsClosed Q)
    (hQ_convex : Convex ℝ Q) (hx : x ∉ Q) :
    AreStronglySeparable Q ({x} : Set E) := by
  -- Route correction: replace the Hahn--Banach shortcut with the textbook projection argument.
  rw [areStronglySeparable_iff]
  let p := euclideanProjection Q hQ_nonempty hQ_closed hQ_convex x
  let a := x - p
  let γ := (inner ℝ a p + inner ℝ a x) / 2
  refine ⟨a, ?_, γ, ?_⟩
  · -- The projection point cannot coincide with `x` because `x ∉ Q`.
    simpa [a, p] using
      projection_displacement_ne_zero Q hQ_nonempty hQ_closed hQ_convex hx
  · constructor
    · intro y hy
      -- The projection point gives a non-strict support bound, and the midpoint makes it strict.
      have hle : inner ℝ a y ≤ inner ℝ a p := by
        simpa [a, p] using
          projection_inner_le_projection_value Q hQ_nonempty hQ_closed hQ_convex hy
      have hgap : inner ℝ a p < inner ℝ a x := by
        simpa [a, p] using
          projection_value_lt_point_value Q hQ_nonempty hQ_closed hQ_convex hx
      have hpγ : inner ℝ a p < γ := by
        dsimp [γ]
        linarith
      linarith
    · intro y hy
      -- The singleton side is exactly the strict upper half-space inequality for `x`.
      have hgap : inner ℝ a p < inner ℝ a x := by
        simpa [a, p] using
          projection_value_lt_point_value Q hQ_nonempty hQ_closed hQ_convex hx
      rcases Set.mem_singleton_iff.mp hy with rfl
      dsimp [γ]
      linarith

end
