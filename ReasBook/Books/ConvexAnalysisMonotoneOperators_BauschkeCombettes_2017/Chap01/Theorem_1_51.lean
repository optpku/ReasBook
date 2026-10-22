/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open Filter Function

universe u

/-- The tail sum of the nonnegative coefficient sequence controlling the iterate distances. -/
noncomputable abbrev summable_iterate_bound_tail (β : ℕ → NNReal) (n : ℕ) : NNReal :=
  ∑' m, β (n + m)

/-- The zeroth tail of the iterate-bound coefficients is the full sum of the series. -/
-- Proof sketch: unfold `summable_iterate_bound_tail`; for `n = 0` the shifted series is exactly
-- the original series.
theorem summable_iterate_bound_tail_zero (β : ℕ → NNReal) :
    summable_iterate_bound_tail β 0 = ∑' n, β n := by
  -- Unfold the tail definition and simplify the zero shift.
  simp [summable_iterate_bound_tail]

/-- Helper for Theorem 1.51: the iterate-distance hypothesis bounds the successive increments of
the orbit of `x₀`. -/
private lemma iterate_successive_dist_le {X : Type u} [MetricSpace X] {T : X → X}
    {β : ℕ → NNReal}
    (hiterate : ∀ n : ℕ, ∀ x y : X,
      dist (T^[n] x) (T^[n] y) ≤ (β n : ℝ) * dist x y) (x₀ : X) :
    ∀ n : ℕ, dist (T^[n] x₀) (T^[n + 1] x₀) ≤ (β n : ℝ) * dist x₀ (T x₀) := by
  intro n
  -- Rewrite the next iterate so the given `n`-step estimate applies directly to `x₀` and `T x₀`.
  simpa [Nat.succ_eq_add_one, Function.iterate_succ_apply] using hiterate n x₀ (T x₀)

/-- Helper for Theorem 1.51: applying the iterate bound to two fixed points yields the textbook
estimate used for uniqueness. -/
private lemma fixed_point_dist_le_mul_beta {X : Type u} [MetricSpace X] {T : X → X}
    {β : ℕ → NNReal}
    (hiterate : ∀ n : ℕ, ∀ x y : X,
      dist (T^[n] x) (T^[n] y) ≤ (β n : ℝ) * dist x y) {x y : X}
    (hx : IsFixedPt T x) (hy : IsFixedPt T y) :
    ∀ n : ℕ, dist x y ≤ (β n : ℝ) * dist x y := by
  intro n
  -- Each iterate fixes both points, so the iterate-distance bound collapses back to `dist x y`.
  simpa [(hx.iterate n).eq, (hy.iterate n).eq] using hiterate n x y

/-- Helper for Theorem 1.51: the real tail sum of the weighted coefficients is the coefficient
tail multiplied by the fixed scalar. -/
private lemma iterate_tail_sum_as_bound (β : ℕ → NNReal) (n : ℕ) (c : ℝ) :
    (∑' m, ((β (n + m) : ℝ) * c)) = (summable_iterate_bound_tail β n : ℝ) * c := by
  -- Pull the scalar out of the series, then identify the remaining tail sum with the NNReal tail.
  rw [tsum_mul_right, summable_iterate_bound_tail, ← NNReal.coe_tsum]

/-- Theorem 1.51: if a self-map of a complete metric space has iterates whose pairwise distances
are bounded by a summable nonnegative sequence, then every orbit converges to the unique fixed
point, with the quantitative tail estimate given by the coefficient series. -/
-- Proof sketch: apply the iterate-distance estimate with `y = T x₀` to show that the orbit
-- `(fun n ↦ T^[n] x₀)` has summable successive distances, hence is Cauchy; completeness gives a
-- limit `x`. Then use the `n = 1` bound and continuity of the limit along the orbit to prove
-- `T x = x`, apply the bound to two fixed points and choose `n` with `β n < 1` to get uniqueness,
-- and finally bound `dist (T^[n] x₀) x` by the tail sum of the successive-distance estimate.
theorem exists_fixed_point_of_summable_iterate_bound {X : Type u} [MetricSpace X]
    [CompleteSpace X] {T : X → X} {β : ℕ → NNReal} (hβ : Summable β)
    (hiterate : ∀ n : ℕ, ∀ x y : X, dist (T^[n] x) (T^[n] y) ≤ (β n : ℝ) * dist x y) (x₀ : X) :
    ∃ x : X,
      IsFixedPt T x ∧
      (∀ ⦃y : X⦄, IsFixedPt T y → y = x) ∧
      Tendsto (fun n ↦ T^[n] x₀) atTop (nhds x) ∧
      ∀ n : ℕ, dist (T^[n] x₀) x ≤ (summable_iterate_bound_tail β n : ℝ) * dist x₀ (T x₀) := by
  -- The orbit increments are controlled by the summable coefficient sequence times the first step.
  have hstep :
      ∀ n : ℕ, dist (T^[n] x₀) (T^[n + 1] x₀) ≤ (β n : ℝ) * dist x₀ (T x₀) :=
    iterate_successive_dist_le hiterate x₀
  have hsummable_dist : Summable (fun n ↦ (β n : ℝ) * dist x₀ (T x₀)) := by
    -- Coercing the NNReal series to `ℝ` preserves summability, and scalar multiplication preserves
    -- it as well.
    exact ((NNReal.summable_coe).2 hβ).mul_right (dist x₀ (T x₀))
  have hcauchy : CauchySeq (fun n ↦ T^[n] x₀) :=
    cauchySeq_of_dist_le_of_summable (fun n ↦ (β n : ℝ) * dist x₀ (T x₀)) hstep hsummable_dist
  obtain ⟨x, hx_tendsto⟩ := cauchySeq_tendsto_of_complete hcauchy
  have hT_lipschitz : LipschitzWith (β 1) T := by
    -- The case `n = 1` of the hypothesis says exactly that `T` is Lipschitz.
    refine LipschitzWith.of_dist_le_mul fun y z ↦ ?_
    simpa using hiterate 1 y z
  have hx_fixed : IsFixedPt T x :=
    isFixedPt_of_tendsto_iterate hx_tendsto hT_lipschitz.continuous.continuousAt
  refine ⟨x, ?_⟩
  refine ⟨hx_fixed, ?_, hx_tendsto, ?_⟩
  · intro y hy_fixed
    -- Choose an iterate with coefficient strictly below `1`; then the fixed-point distance
    -- estimate forces the distance to vanish.
    have hβ_lt_one : ∀ᶠ n in atTop, β n < 1 := by
      have hmem : Set.Iio (1 : NNReal) ∈ nhds (0 : NNReal) := by
        exact Iio_mem_nhds (by simp)
      exact (NNReal.tendsto_atTop_zero_of_summable hβ) hmem
    rcases (eventually_atTop.1 hβ_lt_one) with ⟨n, hn⟩
    have hdist_le : dist x y ≤ (β n : ℝ) * dist x y :=
      fixed_point_dist_le_mul_beta hiterate hx_fixed hy_fixed n
    have hβn_lt : (β n : ℝ) < 1 := by
      exact_mod_cast hn n le_rfl
    have hxy : x = y := by
      by_contra hxy
      have hdist_pos : 0 < dist x y := dist_pos.mpr hxy
      nlinarith
    simpa [eq_comm] using hxy
  · intro n
    -- Apply the standard distance-to-limit estimate to the orbit and rewrite the tail series into
    -- the textbook coefficient tail.
    calc
      dist (T^[n] x₀) x ≤ ∑' m, ((β (n + m) : ℝ) * dist x₀ (T x₀)) := by
        exact dist_le_tsum_of_dist_le_of_tendsto
          (fun m ↦ (β m : ℝ) * dist x₀ (T x₀)) hstep hsummable_dist hx_tendsto n
      _ = (summable_iterate_bound_tail β n : ℝ) * dist x₀ (T x₀) := by
        simpa using iterate_tail_sum_as_bound β n (dist x₀ (T x₀))
