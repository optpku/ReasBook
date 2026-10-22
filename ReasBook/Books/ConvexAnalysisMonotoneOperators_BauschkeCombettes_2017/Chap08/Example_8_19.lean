/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import Mathlib.Order.Filter.IsBounded

-- Declarations for this item will be appended below by the statement pipeline.

open Filter

universe u

variable {H : Type u} [SeminormedAddCommGroup H] [NormedSpace ℝ H]

/-- The limsup distance function associated to a sequence `z` sends `x` to
`limsup_n dist x (z n) = limsup_n ‖x - z n‖`. -/
noncomputable def limsupDistanceFunction (z : ℕ → H) : H → ℝ :=
  fun x ↦ Filter.limsup (fun n ↦ dist x (z n)) atTop

omit [NormedSpace ℝ H] in
/-- Helper for Example 8.19: boundedness of the range of `z` gives a uniform upper bound on the
distance sequence `n ↦ dist x (z n)` for each fixed base point `x`. -/
private lemma dist_sequence_isBoundedUnder
    (z : ℕ → H) (hbounded : Bornology.IsBounded (Set.range z)) (x : H) :
    Filter.IsBoundedUnder (· ≤ ·) (atTop (α := ℕ)) (fun n ↦ dist x (z n)) := by
  rcases isBounded_iff_forall_norm_le.mp hbounded with ⟨R, hR⟩
  refine Filter.isBoundedUnder_of_eventually_le (a := ‖x‖ + R) ?_
  refine Filter.Eventually.of_forall ?_
  intro n
  have hz : ‖z n‖ ≤ R := by
    simpa using hR (z n) (Set.mem_range_self n)
  -- Compare the distance to `z n` with the norm bound coming from the bounded range of `z`.
  calc
    dist x (z n) = ‖x - z n‖ := by rw [dist_eq_norm]
    _ ≤ ‖x‖ + ‖z n‖ := by
      simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using norm_sub_le x (z n)
    _ ≤ ‖x‖ + R := by
      simpa [add_comm, add_left_comm, add_assoc] using add_le_add_left hz ‖x‖

omit [NormedSpace ℝ H] in
/-- Helper for Example 8.19: every distance sequence `n ↦ dist x (z n)` is frequently bounded
below by `0`, so it is cobounded for `Filter.limsup`. -/
private lemma dist_sequence_isCoboundedUnder (z : ℕ → H) (x : H) :
    Filter.IsCoboundedUnder (· ≤ ·) (atTop (α := ℕ)) (fun n ↦ dist x (z n)) := by
  exact Filter.IsCoboundedUnder.of_frequently_ge (a := 0)
    (Frequently.of_forall fun n ↦ dist_nonneg)

-- Proof sketch: each function `x ↦ dist x (z n)` is convex by `convexOn_univ_dist` and
-- `1`-Lipschitz by `LipschitzWith.dist_right`. Tail suprema preserve convexity, the decreasing
-- tail suprema converge pointwise to the limsup, and the triangle inequality passes the
-- nonexpansive bound to the limsup.
/-- Example 8.19: for a bounded sequence `z`, the function
`x ↦ limsup_n ‖x - z n‖` is convex on the whole space and is `1`-Lipschitz. -/
theorem limsupDistanceFunction_convexOn_univ_and_lipschitzWith_one
    (z : ℕ → H) (hbounded : Bornology.IsBounded (Set.range z)) :
    ConvexOn ℝ Set.univ (limsupDistanceFunction z) ∧
      LipschitzWith 1 (limsupDistanceFunction z) := by
  refine ⟨?_, ?_⟩
  · -- Route correction: in this single-item file we prove convexity directly by passing the
    -- pointwise convexity estimate for each distance function through `Filter.limsup`.
    refine (convexOn_iff_pairwise_pos).2 ?_
    refine ⟨convex_univ, ?_⟩
    intro x _ y _ _hxy a b ha hb hab
    have hdist_bdd_x := dist_sequence_isBoundedUnder z hbounded x
    have hdist_bdd_y := dist_sequence_isBoundedUnder z hbounded y
    have hcombo_cobdd := dist_sequence_isCoboundedUnder z (a • x + b • y)
    have hscaled_x_bddAbove :
        Filter.IsBoundedUnder (· ≤ ·) (atTop (α := ℕ)) (fun n ↦ a * dist x (z n)) := by
      rcases hdist_bdd_x.eventually_le with ⟨U, hU⟩
      refine Filter.isBoundedUnder_of_eventually_le (a := a * U) ?_
      exact hU.mono fun n hn ↦ mul_le_mul_of_nonneg_left hn ha.le
    have hscaled_y_bddAbove :
        Filter.IsBoundedUnder (· ≤ ·) (atTop (α := ℕ)) (fun n ↦ b * dist y (z n)) := by
      rcases hdist_bdd_y.eventually_le with ⟨U, hU⟩
      refine Filter.isBoundedUnder_of_eventually_le (a := b * U) ?_
      exact hU.mono fun n hn ↦ mul_le_mul_of_nonneg_left hn hb.le
    have hscaled_x_bddBelow :
        Filter.IsBoundedUnder (· ≥ ·) (atTop (α := ℕ)) (fun n ↦ a * dist x (z n)) := by
      refine Filter.isBoundedUnder_of_eventually_ge (a := 0) ?_
      exact Filter.Eventually.of_forall fun n ↦ mul_nonneg ha.le (dist_nonneg)
    have hscaled_y_cobdd :
        Filter.IsCoboundedUnder (· ≤ ·) (atTop (α := ℕ)) (fun n ↦ b * dist y (z n)) := by
      exact Filter.IsCoboundedUnder.of_frequently_ge (a := 0)
        (Frequently.of_forall fun n ↦ mul_nonneg hb.le (dist_nonneg))
    have hsum_bdd :
        Filter.IsBoundedUnder (· ≤ ·) (atTop (α := ℕ))
          (fun n ↦ a * dist x (z n) + b * dist y (z n)) := by
      rcases hscaled_x_bddAbove.eventually_le with ⟨U, hU⟩
      rcases hscaled_y_bddAbove.eventually_le with ⟨V, hV⟩
      refine Filter.isBoundedUnder_of_eventually_le (a := U + V) ?_
      filter_upwards [hU, hV] with n hnU hnV
      exact add_le_add hnU hnV
    have hpointwise :
        ∀ n : ℕ, dist (a • x + b • y) (z n) ≤ a * dist x (z n) + b * dist y (z n) := by
      intro n
      -- Each distance-to-`z n` map is convex, so it satisfies the textbook barycentric estimate.
      simpa [smul_eq_mul] using
        (convexOn_univ_dist (z n)).2 (by simp : x ∈ Set.univ) (by simp : y ∈ Set.univ)
          ha.le hb.le hab
    have h_limsup_le :
        Filter.limsup (fun n ↦ dist (a • x + b • y) (z n)) (atTop (α := ℕ)) ≤
          Filter.limsup (fun n ↦ a * dist x (z n) + b * dist y (z n)) (atTop (α := ℕ)) := by
      exact Filter.limsup_le_limsup (Filter.Eventually.of_forall hpointwise) hcombo_cobdd hsum_bdd
    have h_add_le :
        Filter.limsup (fun n ↦ a * dist x (z n) + b * dist y (z n)) (atTop (α := ℕ)) ≤
          Filter.limsup (fun n ↦ a * dist x (z n)) (atTop (α := ℕ)) +
            Filter.limsup (fun n ↦ b * dist y (z n)) (atTop (α := ℕ)) := by
      -- Subadditivity of `limsup` turns the estimate into two one-variable limsup terms.
      exact limsup_add_le hscaled_x_bddBelow hscaled_x_bddAbove hscaled_y_cobdd hscaled_y_bddAbove
    have h_mul_x :
        Filter.limsup (fun n ↦ a * dist x (z n)) (atTop (α := ℕ)) ≤
          a * Filter.limsup (fun n ↦ dist x (z n)) (atTop (α := ℕ)) := by
      have hconst_nonneg : ∃ᶠ n : ℕ in atTop, 0 ≤ (fun _ : ℕ ↦ a) n :=
        Frequently.of_forall fun _ ↦ ha.le
      have hconst_bdd : Filter.IsBoundedUnder (· ≤ ·) (atTop (α := ℕ)) (fun _ : ℕ ↦ a) := by
        simpa using
          (Filter.isBoundedUnder_const :
            Filter.IsBoundedUnder (· ≤ ·) (atTop (α := ℕ)) (fun _ : ℕ ↦ a))
      have hdist_nonneg : 0 ≤ᶠ[atTop] fun n : ℕ ↦ dist x (z n) :=
        Filter.Eventually.of_forall fun _ ↦ dist_nonneg
      -- Bounding the scaled limsup uses the nonnegativity of `a` and of the distance sequence.
      simpa [Filter.limsup_const] using
        (limsup_mul_le (u := fun _ : ℕ ↦ a) (v := fun n ↦ dist x (z n))
          hconst_nonneg hconst_bdd hdist_nonneg hdist_bdd_x)
    have h_mul_y :
        Filter.limsup (fun n ↦ b * dist y (z n)) (atTop (α := ℕ)) ≤
          b * Filter.limsup (fun n ↦ dist y (z n)) (atTop (α := ℕ)) := by
      have hconst_nonneg : ∃ᶠ n : ℕ in atTop, 0 ≤ (fun _ : ℕ ↦ b) n :=
        Frequently.of_forall fun _ ↦ hb.le
      have hconst_bdd : Filter.IsBoundedUnder (· ≤ ·) (atTop (α := ℕ)) (fun _ : ℕ ↦ b) := by
        simpa using
          (Filter.isBoundedUnder_const :
            Filter.IsBoundedUnder (· ≤ ·) (atTop (α := ℕ)) (fun _ : ℕ ↦ b))
      have hdist_nonneg : 0 ≤ᶠ[atTop] fun n : ℕ ↦ dist y (z n) :=
        Filter.Eventually.of_forall fun _ ↦ dist_nonneg
      simpa [Filter.limsup_const] using
        (limsup_mul_le (u := fun _ : ℕ ↦ b) (v := fun n ↦ dist y (z n))
          hconst_nonneg hconst_bdd hdist_nonneg hdist_bdd_y)
    -- Combine the pointwise convexity estimate with the limsup additivity bounds.
    simpa [limsupDistanceFunction, smul_eq_mul] using
      le_trans h_limsup_le <| le_trans h_add_le (add_le_add h_mul_x h_mul_y)
  · -- The triangle inequality gives the one-sided estimate needed for `LipschitzWith.of_le_add`.
    refine LipschitzWith.of_le_add ?_
    intro x y
    have hdist_bdd_y := dist_sequence_isBoundedUnder z hbounded y
    have hdist_cobdd_x := dist_sequence_isCoboundedUnder z x
    have hsum_bdd :
        Filter.IsBoundedUnder (· ≤ ·) (atTop (α := ℕ)) (fun n ↦ dist x y + dist y (z n)) := by
      rcases hdist_bdd_y.eventually_le with ⟨U, hU⟩
      refine Filter.isBoundedUnder_of_eventually_le (a := dist x y + U) ?_
      exact hU.mono fun n hn ↦ by
        simpa [add_comm] using add_le_add_left hn (dist x y)
    have hpointwise :
        ∀ n : ℕ, dist x (z n) ≤ dist x y + dist y (z n) := by
      intro n
      exact dist_triangle x y (z n)
    have h_limsup_le :
        Filter.limsup (fun n ↦ dist x (z n)) (atTop (α := ℕ)) ≤
          Filter.limsup (fun n ↦ dist x y + dist y (z n)) (atTop (α := ℕ)) := by
      exact Filter.limsup_le_limsup (Filter.Eventually.of_forall hpointwise) hdist_cobdd_x hsum_bdd
    have h_const_add :
        Filter.limsup (fun n ↦ dist x y + dist y (z n)) (atTop (α := ℕ)) =
          dist x y + Filter.limsup (fun n ↦ dist y (z n)) (atTop (α := ℕ)) := by
      -- Passing a constant through `limsup` is the exact translation of the textbook argument.
      exact limsup_const_add (atTop (α := ℕ)) (fun n ↦ dist y (z n)) (dist x y) hdist_bdd_y
        (dist_sequence_isCoboundedUnder z y)
    simpa [limsupDistanceFunction, add_comm, add_left_comm, add_assoc] using
      h_limsup_le.trans_eq h_const_add

-- Proof sketch: extract the `LipschitzWith 1` statement from
-- `limsupDistanceFunction_convexOn_univ_and_lipschitzWith_one` and rewrite the metric bound using
-- `dist_eq_norm`.
/-- The limsup distance function satisfies the textbook estimate
`|f x - f y| ≤ ‖x - y‖`. -/
theorem limsupDistanceFunction_abs_sub_le_norm_sub
    (z : ℕ → H) (hbounded : Bornology.IsBounded (Set.range z)) {x y : H} :
    |limsupDistanceFunction z x - limsupDistanceFunction z y| ≤ ‖x - y‖ := by
  let hLip := (limsupDistanceFunction_convexOn_univ_and_lipschitzWith_one z hbounded).2
  -- Rewrite the Lipschitz metric estimate on `ℝ` into the textbook absolute-value inequality.
  simpa [Real.dist_eq, dist_eq_norm] using hLip.dist_le_mul x y
