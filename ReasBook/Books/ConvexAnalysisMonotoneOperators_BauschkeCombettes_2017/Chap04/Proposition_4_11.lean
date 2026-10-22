/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap04.Definition_4_10
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap04.Proposition_4_4

-- Declarations for this item will be appended below by the statement pipeline.

universe u

variable {H : Type u} [NormedAddCommGroup H]

/-- On a subtype domain, `LipschitzWith 1` is exactly the pairwise nonexpansive norm inequality. -/
private lemma lipschitzWith_one_iff_pairwise_norm_sub_le {D : Set H} {T : D → H} :
    LipschitzWith 1 T ↔ ∀ x y : D, ‖T x - T y‖ ≤ ‖(x : H) - y‖ := by
  constructor
  · intro hT x y
    simpa [Subtype.dist_eq, dist_eq_norm] using hT.dist_le_mul x y
  · intro hT
    refine LipschitzWith.of_dist_le_mul ?_
    intro x y
    simpa [Subtype.dist_eq, dist_eq_norm] using hT x y

/-- Comparing squared norms is equivalent to comparing norms. -/
private lemma norm_sq_le_norm_sq_iff {a b : H} : ‖a‖ ^ 2 ≤ ‖b‖ ^ 2 ↔ ‖a‖ ≤ ‖b‖ := by
  constructor
  · intro h
    have h' := sq_le_sq.mp h
    simpa [abs_of_nonneg (norm_nonneg a), abs_of_nonneg (norm_nonneg b)] using h'
  · intro h
    exact sq_le_sq.mpr <| by
      simpa [abs_of_nonneg (norm_nonneg a), abs_of_nonneg (norm_nonneg b)] using h

section

variable [InnerProductSpace ℝ H]

/-- The residual `1 / 2`-cocoercivity inequality is equivalent to the squared nonexpansive
estimate after expanding the quadratic terms. -/
private lemma residual_quadratic_expansion {D : Set H} (T : D → H) (x y : D) :
    ((1 / 2 : ℝ) * ‖residualMap D T x - residualMap D T y‖ ^ 2 ≤
        inner ℝ ((x : H) - y) (residualMap D T x - residualMap D T y)) ↔
      ‖T x - T y‖ ^ 2 ≤ ‖((x : H) - y)‖ ^ 2 := by
  let u : H := (x : H) - y
  let v : H := T x - T y
  have h_residual : residualMap D T x - residualMap D T y = u - v := by
    change (((x : H) - T x) - (y - T y)) = u - v
    simp [u, v, sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
  rw [h_residual]
  have h_expand : ‖u - v‖ ^ 2 = ‖u‖ ^ 2 - 2 * inner ℝ u v + ‖v‖ ^ 2 := by
    simpa using norm_sub_sq_real u v
  have h_inner : inner ℝ u (u - v) = ‖u‖ ^ 2 - inner ℝ u v := by
    rw [inner_sub_right, real_inner_self_eq_norm_sq]
  constructor <;> intro h <;> nlinarith [h, h_expand, h_inner]

/-- The residual map is `1 / 2`-cocoercive exactly when the map is pairwise nonexpansive in
norm. -/
private lemma residualMap_cocoerciveOn_half_iff_pairwise_norm_sub_le {D : Set H} {T : D → H} :
    CocoerciveOn (1 / 2 : ℝ) D (residualMap D T) ↔
      ∀ x y : D, ‖T x - T y‖ ≤ ‖(x : H) - y‖ := by
  constructor
  · intro h x y
    have hsq :
        ‖T x - T y‖ ^ 2 ≤ ‖((x : H) - y)‖ ^ 2 := by
      exact (residual_quadratic_expansion T x y).mp (h.ineq x y)
    exact (norm_sq_le_norm_sq_iff).mp hsq
  · intro h
    refine ⟨by norm_num, ?_⟩
    intro x y
    have hsq :
        ‖T x - T y‖ ^ 2 ≤ ‖((x : H) - y)‖ ^ 2 := by
      exact (norm_sq_le_norm_sq_iff).mpr (h x y)
    exact (residual_quadratic_expansion T x y).mpr hsq

/-- Proposition 4.11: a map on a subset of a real inner product space is nonexpansive exactly
when its residual map `Id - T` is `1 / 2`-cocoercive. -/
theorem lipschitzWith_one_iff_residualMap_cocoerciveOn_half {D : Set H} (T : D → H) :
    LipschitzWith 1 T ↔ CocoerciveOn (1 / 2 : ℝ) D (residualMap D T) := by
  rw [lipschitzWith_one_iff_pairwise_norm_sub_le,
    residualMap_cocoerciveOn_half_iff_pairwise_norm_sub_le]

end
