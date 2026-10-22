/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap01.Definition_1_4
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap08.Example_8_26

-- Declarations for this item will be appended below by the statement pipeline.

open scoped BigOperators

namespace ERealFunction

/-- The Pearson divergence on the canonical `Fin N → ℝ` model of `ℝ^N × ℝ^N`, given by the
textbook formula `∑ i |x i - y i|^2 / y i` on the positive orthant of the second variable and by
`+∞` otherwise. -/
noncomputable def pearsonDivergence (N : ℕ) : ((Fin N → ℝ) × (Fin N → ℝ)) → EReal :=
  fun p ↦
    if ∀ i, 0 < p.2 i then
      ∑ i, ((|p.1 i - p.2 i| ^ 2 / p.2 i : ℝ) : EReal)
    else
      ⊤

-- Proof sketch: unfold `pearsonDivergence` and simplify the positive branch of the defining `if`
-- using the hypothesis that every coordinate of `y` is positive.
/-- On the positive orthant of the second variable, the Pearson divergence is the finite sum
`∑ i |x i - y i|^2 / y i`. -/
theorem pearsonDivergence_apply_of_pos (N : ℕ) (x y : Fin N → ℝ) (hy : ∀ i, 0 < y i) :
    pearsonDivergence N (x, y) =
      ∑ i, ((|x i - y i| ^ 2 / y i : ℝ) : EReal) := by
  -- Unfold the definition and select the positive branch of the defining `if`.
  simp [pearsonDivergence, hy]

/-- Helper for Example 8.29: the scalar seed `t ↦ |t - 1|^2` never attains `-∞`. -/
private lemma pearson_seed_ne_bot (t : ℝ) :
    ((|t - 1| ^ 2 : ℝ) : EReal) ≠ ⊥ := by
  -- The seed always takes a finite real value, so the extended-real coercion cannot be `-∞`.
  exact EReal.coe_ne_bot (|t - 1| ^ 2)

/-- Helper for Example 8.29: the scalar seed `t ↦ |t - 1|^2` has convex real-height epigraph. -/
private theorem convex_epigraph_pearson_seed :
    Convex ℝ (epigraph (fun t : ℝ ↦ ((|t - 1| ^ 2 : ℝ) : EReal))) := by
  refine (convex_iff_forall_pos).2 ?_
  intro p hp q hq a b ha hb hab
  rcases p with ⟨x, ξ⟩
  rcases q with ⟨y, η⟩
  rw [mem_epigraph_iff] at hp hq ⊢
  have hp' : |x - 1| ^ 2 ≤ ξ := by
    exact_mod_cast hp
  have hq' : |y - 1| ^ 2 ≤ η := by
    exact_mod_cast hq
  have hseed_sq : (a * x + b * y - 1) ^ 2 ≤ a * (x - 1) ^ 2 + b * (y - 1) ^ 2 := by
    -- The quadratic Jensen gap factors as `a * b * (x - y)^2`, which is nonnegative.
    have hidentity :
        a * (x - 1) ^ 2 + b * (y - 1) ^ 2 - (a * x + b * y - 1) ^ 2 =
          a * b * (x - y) ^ 2 := by
      have hb' : b = 1 - a := by
        linarith
      subst b
      ring
    have hnonneg : 0 ≤ a * b * (x - y) ^ 2 := by
      exact mul_nonneg (mul_nonneg ha.le hb.le) (sq_nonneg (x - y))
    nlinarith [hidentity, hnonneg]
  have hseed : |a * x + b * y - 1| ^ 2 ≤ a * |x - 1| ^ 2 + b * |y - 1| ^ 2 := by
    -- Replace the square by the square of the absolute value to match the displayed seed.
    simpa [abs_sub_sq] using hseed_sq
  have hheight : a * |x - 1| ^ 2 + b * |y - 1| ^ 2 ≤ a * ξ + b * η := by
    -- The endpoint epigraph bounds scale and add because the coefficients are nonnegative.
    exact add_le_add (mul_le_mul_of_nonneg_left hp' ha.le) (mul_le_mul_of_nonneg_left hq' hb.le)
  -- Combine scalar convexity of the seed with the endpoint height bounds at the barycenter.
  exact_mod_cast (by
    simpa [Prod.smul_mk, smul_eq_mul, mul_comm, mul_left_comm, mul_assoc, add_comm, add_left_comm,
      add_assoc] using (le_trans hseed hheight) : |a * x + b * y - 1| ^ 2 ≤ a * ξ + b * η)

-- Proof sketch: on the positive orthant, use `y i * |x i / y i - 1|^2 = |x i - y i|^2 / y i`
-- coordinatewise; outside the positive orthant both functions are `⊤` by definition.
/-- The Pearson divergence is the coordinate-perspective sum attached to the scalar function
`t ↦ |t - 1|^2`. -/
theorem pearsonDivergence_eq_coordinatePerspectiveSum (N : ℕ) :
    pearsonDivergence N =
      coordinatePerspectiveSum (Fin N) (fun t ↦ ((|t - 1| ^ 2 : ℝ) : EReal)) := by
  funext p
  rcases p with ⟨x, y⟩
  by_cases hy : ∀ i, 0 < y i
  · -- On the positive orthant, both functions reduce to explicit finite sums with the same
    -- coordinate formula.
    rw [pearsonDivergence_apply_of_pos N x y hy]
    rw [coordinatePerspectiveSum_apply_of_pos (Fin N)
      (fun t ↦ ((|t - 1| ^ 2 : ℝ) : EReal)) x y hy]
    refine Finset.sum_congr rfl ?_
    intro i hi
    have hcoord : y i * |x i / y i - 1| ^ 2 = |x i - y i| ^ 2 / y i := by
      -- Rewrite the perspective argument as a single quotient and then clear the positive
      -- denominator.
      have hdiv : x i / y i - 1 = (x i - y i) / y i := by
        field_simp [(hy i).ne']
      rw [hdiv, abs_div, abs_of_pos (hy i)]
      field_simp [(hy i).ne']
    rw [← EReal.coe_mul]
    exact congrArg (fun r : ℝ ↦ ((r : ℝ) : EReal)) hcoord.symm
  · -- If one coordinate of `y` is nonpositive, both definitions are immediately `+∞`.
    simp [pearsonDivergence, coordinatePerspectiveSum, hy]

-- Proof sketch: rewrite `pearsonDivergence N` as the coordinate-perspective sum for the scalar
-- function `t ↦ |t - 1|^2` using `pearsonDivergence_eq_coordinatePerspectiveSum`. Then apply
-- Example 8.26 to that scalar function, whose real epigraph is convex because
-- `t ↦ |t - 1|^2 = (t - 1)^2` is strictly convex by Proposition 8.14 (2), hence convex.
/-- Example 8.29: the Pearson divergence on `ℝ^N × ℝ^N`, defined by
`f(x, y) = ∑ i |x i - y i|^2 / y i` for `y ∈ ℝ_{++}^N` and `f(x, y) = +∞` otherwise, has convex
epigraph. -/
theorem convex_epigraph_pearsonDivergence (N : ℕ) :
    Convex ℝ (epigraph (pearsonDivergence N)) := by
  have hscalar :
      Convex ℝ {p : ℝ × ℝ | (fun t ↦ ((|t - 1| ^ 2 : ℝ) : EReal)) p.1 ≤ (p.2 : EReal)} := by
    -- Repackage the scalar seed convexity in the set form expected by Example 8.26.
    simpa [epigraph] using convex_epigraph_pearson_seed
  let lift :
      (∀ t, (fun s : ℝ ↦ ((|s - 1| ^ 2 : ℝ) : EReal)) t ≠ ⊥) →
      Convex ℝ {p : ℝ × ℝ | (fun t ↦ ((|t - 1| ^ 2 : ℝ) : EReal)) p.1 ≤ (p.2 : EReal)} →
      Convex ℝ {p : (((Fin N → ℝ) × (Fin N → ℝ)) × ℝ) |
        coordinatePerspectiveSum (Fin N) (fun t ↦ ((|t - 1| ^ 2 : ℝ) : EReal)) p.1 ≤
          (p.2 : EReal)} :=
    ERealFunction.convex_coordinatePerspectiveSum (Fin N)
      (fun t ↦ ((|t - 1| ^ 2 : ℝ) : EReal))
  let hsum :
      Convex ℝ {p : (((Fin N → ℝ) × (Fin N → ℝ)) × ℝ) |
        coordinatePerspectiveSum (Fin N) (fun t ↦ ((|t - 1| ^ 2 : ℝ) : EReal)) p.1 ≤
          (p.2 : EReal)} :=
    lift pearson_seed_ne_bot hscalar
  -- Example 8.26 lifts scalar epigraph convexity once the Pearson formula is identified with the
  -- coordinate perspective sum.
  simpa [pearsonDivergence_eq_coordinatePerspectiveSum, epigraph] using hsum

end ERealFunction
