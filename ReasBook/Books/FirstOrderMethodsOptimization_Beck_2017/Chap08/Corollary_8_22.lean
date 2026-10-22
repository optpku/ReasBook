/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import Mathlib
import FirstOrderMethodsOptimization_Beck_2017.Chap05.Theorem_5_4
import FirstOrderMethodsOptimization_Beck_2017.Chap08.Algorithm_8_7
import FirstOrderMethodsOptimization_Beck_2017.Chap08.Theorem_8_16

-- Declarations for this item will be appended below by the statement pipeline.

universe u

noncomputable section

open scoped BigOperators

section

open Metric

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable {S₁ S₂ : Set E}
variable (hS₁_closed : IsClosed S₁) (hS₁_convex : Convex ℝ S₁)
variable (hS₂_closed : IsClosed S₂) (hS₂_convex : Convex ℝ S₂)
variable (hinter : (S₁ ∩ S₂).Nonempty) (x0 : S₂)

local notation "x[" k "]" =>
  alternating_projection_method S₁ S₂
    (hinter.mono Set.inter_subset_left) hS₁_closed hS₁_convex
    (hinter.mono Set.inter_subset_right) hS₂_closed hS₂_convex x0 k

/-- Helper for Corollary 8.22: one metric-projection step decreases the squared distance to each
point of the set by at least the squared distance from the current point to the set. -/
lemma metricProjection_sqdist_drop_le {C : Set E}
    (hC_nonempty : C.Nonempty) (hC_closed : IsClosed C) (hC_convex : Convex ℝ C)
    {x y : E} (hy : y ∈ C) :
    dist (metricProjection C hC_nonempty hC_closed hC_convex x : E) y ^ (2 : ℕ) +
        infDist x C ^ (2 : ℕ) ≤
      dist x y ^ (2 : ℕ) := by
  let p : E := metricProjection C hC_nonempty hC_closed hC_convex x
  have hy_proj :
      (metricProjection C hC_nonempty hC_closed hC_convex y : E) = y :=
    by
      simpa [projectionPoint] using
        projectionPoint_eq_self_of_mem C hC_nonempty hC_closed hC_convex hy
  have hfirm :
      inner ℝ (p - y) (x - y) ≥ ‖p - y‖ ^ (2 : ℕ) := by
    -- Firm nonexpansiveness becomes a one-sided inner-product control after fixing `y`.
    simpa [p, hy_proj] using
      metricProjection_firmly_nonexpansive C hC_nonempty hC_closed hC_convex x y
  have hinner_nonneg : 0 ≤ inner ℝ (p - y) (x - p) := by
    -- Rewriting `x - y` as `(p - y) + (x - p)` isolates the nonnegative cross term.
    have hrewrite :
        inner ℝ (p - y) (x - y) = ‖p - y‖ ^ (2 : ℕ) + inner ℝ (p - y) (x - p) := by
      calc
        inner ℝ (p - y) (x - y)
            = inner ℝ (p - y) ((p - y) + (x - p)) := by
                congr 2
                abel
        _ = inner ℝ (p - y) (p - y) + inner ℝ (p - y) (x - p) := by
              rw [inner_add_right]
        _ = ‖p - y‖ ^ (2 : ℕ) + inner ℝ (p - y) (x - p) := by
              rw [real_inner_self_eq_norm_sq]
    nlinarith [hfirm, hrewrite]
  have hnorm_expand :
      dist x y ^ (2 : ℕ) =
        dist p y ^ (2 : ℕ) + 2 * inner ℝ (p - y) (x - p) + dist x p ^ (2 : ℕ) := by
    -- The norm-square expansion of `x - y = (p - y) + (x - p)` exposes the same cross term.
    calc
      dist x y ^ (2 : ℕ) = ‖(p - y) + (x - p)‖ ^ (2 : ℕ) := by
        rw [dist_eq_norm]
        congr 1
        abel
      _ = ‖p - y‖ ^ (2 : ℕ) + 2 * inner ℝ (p - y) (x - p) + ‖x - p‖ ^ (2 : ℕ) := by
        rw [norm_add_sq_real]
      _ = dist p y ^ (2 : ℕ) + 2 * inner ℝ (p - y) (x - p) + dist x p ^ (2 : ℕ) := by
        simp [dist_eq_norm]
  have hsq :
      dist p y ^ (2 : ℕ) + dist x p ^ (2 : ℕ) ≤ dist x y ^ (2 : ℕ) := by
    nlinarith [hinner_nonneg, hnorm_expand]
  have hinf : infDist x C = dist x p := by
    simpa [p] using
      infDist_eq_dist_metricProjection C hC_nonempty hC_closed hC_convex x
  simpa [p, hinf] using hsq

/-- Helper for Corollary 8.22: one full alternating-projection step decreases the squared distance
to every point of `S₁ ∩ S₂` by at least the squared distance to `S₁`. -/
lemma alternating_projection_sqdist_step_le {s : E} (hs : s ∈ S₁ ∩ S₂) (k : ℕ) :
    dist (x[k + 1] : E) s ^ (2 : ℕ) ≤
      dist (x[k] : E) s ^ (2 : ℕ) - infDist (x[k] : E) S₁ ^ (2 : ℕ) := by
  let p : E :=
    metricProjection S₁ (hinter.mono Set.inter_subset_left) hS₁_closed hS₁_convex
      (x[k] : E)
  have hstep₁ :
      dist p s ^ (2 : ℕ) + infDist (x[k] : E) S₁ ^ (2 : ℕ) ≤ dist (x[k] : E) s ^ (2 : ℕ) :=
    metricProjection_sqdist_drop_le
      (hinter.mono Set.inter_subset_left) hS₁_closed hS₁_convex hs.1
  have hstep₂_raw :
      dist
          (metricProjection S₂ (hinter.mono Set.inter_subset_right) hS₂_closed
            hS₂_convex p : E) s ^ (2 : ℕ) +
        infDist p S₂ ^ (2 : ℕ) ≤
      dist p s ^ (2 : ℕ) :=
    metricProjection_sqdist_drop_le
      (hinter.mono Set.inter_subset_right) hS₂_closed hS₂_convex hs.2
  have hstep₂ :
      dist (x[k + 1] : E) s ^ (2 : ℕ) ≤ dist p s ^ (2 : ℕ) := by
    -- The second projection also drops squared distance, and its extra nonnegative term can be
    -- discarded.
    have hstep₂_raw' :
        dist (x[k + 1] : E) s ^ (2 : ℕ) + infDist p S₂ ^ (2 : ℕ) ≤ dist p s ^ (2 : ℕ) := by
      simpa [p, alternating_projection_method_succ] using hstep₂_raw
    nlinarith [hstep₂_raw', sq_nonneg (infDist p S₂)]
  have hstep₁' :
      dist p s ^ (2 : ℕ) ≤ dist (x[k] : E) s ^ (2 : ℕ) - infDist (x[k] : E) S₁ ^ (2 : ℕ) := by
    nlinarith [hstep₁]
  exact le_trans hstep₂ hstep₁'

/-- Helper for Corollary 8.22: the prefix sum of squared distances to `S₁`, together with the
current squared distance to a point of `S₁ ∩ S₂`, is controlled by the initial squared distance. -/
lemma alternating_projection_prefix_sqdist_le {s : E} (hs : s ∈ S₁ ∩ S₂) (K : ℕ) :
    (Finset.sum (Finset.range (K + 1)) fun i ↦ infDist (x[i] : E) S₁ ^ (2 : ℕ)) +
        dist (x[K + 1] : E) s ^ (2 : ℕ) ≤
      dist (x0 : E) s ^ (2 : ℕ) := by
  induction K with
  | zero =>
      -- The base case is exactly the one-step descent from the initial point.
      have hstep := alternating_projection_sqdist_step_le
        (hS₁_closed := hS₁_closed) (hS₁_convex := hS₁_convex)
        (hS₂_closed := hS₂_closed) (hS₂_convex := hS₂_convex) (hinter := hinter) (x0 := x0)
        hs 0
      have hstep' :
          infDist (x[0] : E) S₁ ^ (2 : ℕ) + dist (x[1] : E) s ^ (2 : ℕ) ≤
            dist (x[0] : E) s ^ (2 : ℕ) := by
        nlinarith [hstep]
      simpa using hstep'
  | succ K ih =>
      have hstep :=
        alternating_projection_sqdist_step_le
          (hS₁_closed := hS₁_closed) (hS₁_convex := hS₁_convex)
          (hS₂_closed := hS₂_closed) (hS₂_convex := hS₂_convex) (hinter := hinter) (x0 := x0)
          hs (K + 1)
      have hstep' :
          infDist (x[K + 1] : E) S₁ ^ (2 : ℕ) + dist (x[K + 2] : E) s ^ (2 : ℕ) ≤
            dist (x[K + 1] : E) s ^ (2 : ℕ) := by
        nlinarith [hstep]
      -- Append the next descent estimate to the already-telescoped prefix.
      calc
        (Finset.sum (Finset.range (K + 2)) fun i ↦ infDist (x[i] : E) S₁ ^ (2 : ℕ)) +
            dist (x[K + 2] : E) s ^ (2 : ℕ)
            =
          (Finset.sum (Finset.range (K + 1)) fun i ↦ infDist (x[i] : E) S₁ ^ (2 : ℕ)) +
            (infDist (x[K + 1] : E) S₁ ^ (2 : ℕ) + dist (x[K + 2] : E) s ^ (2 : ℕ)) := by
              rw [Finset.sum_range_succ]
              ring
        _ ≤
          (Finset.sum (Finset.range (K + 1)) fun i ↦ infDist (x[i] : E) S₁ ^ (2 : ℕ)) +
            dist (x[K + 1] : E) s ^ (2 : ℕ) := by
              gcongr
        _ ≤ dist (x0 : E) s ^ (2 : ℕ) := ih

/-- Helper for Corollary 8.22: the telescoping estimate bounds every prefix sum of the squared
distances to `S₁` by the initial squared distance to `S₁ ∩ S₂`. -/
lemma alternating_projection_sum_sq_infDist_le {s : E} (hs : s ∈ S₁ ∩ S₂) (K : ℕ) :
    Finset.sum (Finset.range (K + 1)) (fun i ↦ infDist (x[i] : E) S₁ ^ (2 : ℕ)) ≤
      dist (x0 : E) s ^ (2 : ℕ) := by
  have hprefix :=
    alternating_projection_prefix_sqdist_le
      (hS₁_closed := hS₁_closed) (hS₁_convex := hS₁_convex)
      (hS₂_closed := hS₂_closed) (hS₂_convex := hS₂_convex) (hinter := hinter) (x0 := x0)
      hs K
  -- Dropping the terminal squared-distance term keeps a valid upper bound.
  nlinarith [hprefix, sq_nonneg (dist (x[K + 1] : E) s)]

/-- Helper for Corollary 8.22: the alternating-projection sequence is Fejér monotone with respect
to `S₁ ∩ S₂`. -/
lemma alternating_projection_fejer {s : E} (hs : s ∈ S₁ ∩ S₂) (k : ℕ) :
    dist (x[k + 1] : E) s ≤ dist (x[k] : E) s := by
  have hstep :=
    alternating_projection_sqdist_step_le
      (hS₁_closed := hS₁_closed) (hS₁_convex := hS₁_convex)
      (hS₂_closed := hS₂_closed) (hS₂_convex := hS₂_convex) (hinter := hinter) (x0 := x0)
      hs k
  have hsq :
      dist (x[k + 1] : E) s ^ (2 : ℕ) ≤ dist (x[k] : E) s ^ (2 : ℕ) := by
    nlinarith [hstep, sq_nonneg (infDist (x[k] : E) S₁)]
  -- Distances are nonnegative, so monotonicity of squares gives monotonicity of distances.
  rw [sq_le_sq, abs_of_nonneg (dist_nonneg), abs_of_nonneg (dist_nonneg)] at hsq
  exact hsq

/-- Helper for Corollary 8.22: the distance from the alternating-projection iterates to `S₁`
converges to zero. -/
lemma alternating_projection_infDist_tendsto_zero :
    Filter.Tendsto (fun k ↦ infDist (x[k] : E) S₁) Filter.atTop (nhds 0) := by
  let s : E := Classical.choose hinter
  have hs : s ∈ S₁ ∩ S₂ := Classical.choose_spec hinter
  have hsum_bound :
      ∀ n : ℕ,
        Finset.sum (Finset.range n) (fun i ↦ infDist (x[i] : E) S₁ ^ (2 : ℕ)) ≤
          dist (x0 : E) s ^ (2 : ℕ) := by
    intro n
    cases n with
    | zero =>
        simpa using sq_nonneg (dist (x0 : E) s)
    | succ K =>
        simpa using
          alternating_projection_sum_sq_infDist_le
            (hS₁_closed := hS₁_closed) (hS₁_convex := hS₁_convex)
            (hS₂_closed := hS₂_closed) (hS₂_convex := hS₂_convex) (hinter := hinter) (x0 := x0)
            hs K
  have hsummable :
      Summable (fun n ↦ infDist (x[n] : E) S₁ ^ (2 : ℕ)) :=
    summable_of_sum_range_le (fun n ↦ sq_nonneg (infDist (x[n] : E) S₁)) hsum_bound
  have hsq_tendsto_zero :
      Filter.Tendsto (fun n ↦ infDist (x[n] : E) S₁ ^ (2 : ℕ)) Filter.atTop (nhds 0) :=
    hsummable.tendsto_atTop_zero
  have hinfDist_eq_sqrt :
      ∀ n : ℕ, infDist (x[n] : E) S₁ = Real.sqrt (infDist (x[n] : E) S₁ ^ (2 : ℕ)) := by
    intro n
    rw [Real.sqrt_sq_eq_abs, abs_of_nonneg]
    exact infDist_nonneg
  have hsqrt_tendsto :
      Filter.Tendsto (fun n ↦ Real.sqrt (infDist (x[n] : E) S₁ ^ (2 : ℕ)))
        Filter.atTop (nhds 0) := by
    simpa using Real.continuous_sqrt.continuousAt.tendsto.comp hsq_tendsto_zero
  -- Nonnegativity lets us recover `infDist` from the square root of its square.
  have hEq :
      (fun n ↦ infDist (x[n] : E) S₁) =
        fun n ↦ Real.sqrt (infDist (x[n] : E) S₁ ^ (2 : ℕ)) := by
    funext n
    exact hinfDist_eq_sqrt n
  rw [hEq]
  exact hsqrt_tendsto

-- Proof sketch: combine the firm nonexpansiveness inequalities for the two projections in one
-- alternating-projection step to obtain a telescoping descent inequality for the squared distance
-- to any point of `S₁ ∩ S₂`; summing this inequality up to `k` and comparing the minimum with the
-- average yields the displayed `1 / √(k + 1)` rate.
/-- Corollary 8.22 (1): among the first `k + 1` iterates of the alternating projection method,
there is an iterate whose distance to `S₁` is at most
`d_{S₁ ∩ S₂}(x^0) / √(k + 1)`. -/
theorem alternating_projection_exists_prefix_iterate_infDist_le (k : ℕ) :
    ∃ n ≤ k,
      infDist (x[n] : E) S₁ ≤ infDist (x0 : E) (S₁ ∩ S₂) / Real.sqrt (k + 1) := by
  let T : Finset ℕ := Finset.range (k + 1)
  have hT_nonempty : T.Nonempty := by
    refine ⟨k, ?_⟩
    simp [T]
  obtain ⟨n, hnT, hnmin⟩ := Finset.exists_min_image T (fun i ↦ infDist (x[i] : E) S₁) hT_nonempty
  have hn_le : n ≤ k := by
    simpa [T] using hnT
  let s0 :=
    metricProjection (S₁ ∩ S₂) hinter (hS₁_closed.inter hS₂_closed)
      (hS₁_convex.inter hS₂_convex) (x0 : E)
  have hsum_upper :
      Finset.sum T (fun i ↦ infDist (x[i] : E) S₁ ^ (2 : ℕ)) ≤
        infDist (x0 : E) (S₁ ∩ S₂) ^ (2 : ℕ) := by
    have hsum :=
      alternating_projection_sum_sq_infDist_le
        (hS₁_closed := hS₁_closed) (hS₁_convex := hS₁_convex)
        (hS₂_closed := hS₂_closed) (hS₂_convex := hS₂_convex) (hinter := hinter) (x0 := x0)
        s0.property k
    have hs0dist :
        infDist (x0 : E) (S₁ ∩ S₂) = dist (x0 : E) (s0 : E) := by
      simpa [s0] using
        infDist_eq_dist_metricProjection
          (S₁ ∩ S₂) hinter (hS₁_closed.inter hS₂_closed)
          (hS₁_convex.inter hS₂_convex) (x0 : E)
    simpa [T, hs0dist] using hsum
  have hmin_sq :
      ∀ i ∈ T, infDist (x[n] : E) S₁ ^ (2 : ℕ) ≤ infDist (x[i] : E) S₁ ^ (2 : ℕ) := by
    intro i hi
    have hmin : infDist (x[n] : E) S₁ ≤ infDist (x[i] : E) S₁ := hnmin i hi
    have hn_nonneg : 0 ≤ infDist (x[n] : E) S₁ := infDist_nonneg
    have hi_nonneg : 0 ≤ infDist (x[i] : E) S₁ := infDist_nonneg
    nlinarith
  have hsum_lower :
      ((k + 1 : ℕ) : ℝ) * infDist (x[n] : E) S₁ ^ (2 : ℕ) ≤
        Finset.sum T (fun i ↦ infDist (x[i] : E) S₁ ^ (2 : ℕ)) := by
    simpa [T, nsmul_eq_mul] using
      Finset.card_nsmul_le_sum T (fun i ↦ infDist (x[i] : E) S₁ ^ (2 : ℕ))
        (infDist (x[n] : E) S₁ ^ (2 : ℕ)) hmin_sq
  have hcount_mul :
      ((k + 1 : ℕ) : ℝ) * infDist (x[n] : E) S₁ ^ (2 : ℕ) ≤
        infDist (x0 : E) (S₁ ∩ S₂) ^ (2 : ℕ) :=
    le_trans hsum_lower hsum_upper
  have hn_nonneg : 0 ≤ infDist (x[n] : E) S₁ := infDist_nonneg
  have h0_nonneg : 0 ≤ infDist (x0 : E) (S₁ ∩ S₂) := infDist_nonneg
  have hsqrt_pos : 0 < Real.sqrt (k + 1) := by
    positivity
  have hmul_le :
      infDist (x[n] : E) S₁ * Real.sqrt (k + 1) ≤ infDist (x0 : E) (S₁ ∩ S₂) := by
    have hsqrt_sq : Real.sqrt (k + 1) ^ (2 : ℕ) = (k + 1 : ℝ) := by
      rw [Real.sq_sqrt]
      positivity
    have hsq :
        (infDist (x[n] : E) S₁ * Real.sqrt (k + 1)) ^ (2 : ℕ) ≤
          infDist (x0 : E) (S₁ ∩ S₂) ^ (2 : ℕ) := by
      let a : ℝ := infDist (x[n] : E) S₁ ^ (2 : ℕ)
      calc
        (infDist (x[n] : E) S₁ * Real.sqrt (k + 1)) ^ (2 : ℕ)
            = infDist (x[n] : E) S₁ ^ (2 : ℕ) * (Real.sqrt (k + 1) ^ (2 : ℕ)) := by
                rw [mul_pow]
        _ = infDist (x[n] : E) S₁ ^ (2 : ℕ) * (k + 1 : ℝ) := by rw [hsqrt_sq]
        _ = a * ((k : ℝ) + 1) := by
              simp [a]
        _ = ((k : ℝ) + 1) * a := by ring
        _ = ((k + 1 : ℕ) : ℝ) * infDist (x[n] : E) S₁ ^ (2 : ℕ) := by
              norm_num [a]
        _ ≤ infDist (x0 : E) (S₁ ∩ S₂) ^ (2 : ℕ) := hcount_mul
    rw [sq_le_sq, abs_of_nonneg (mul_nonneg hn_nonneg (Real.sqrt_nonneg _)),
      abs_of_nonneg h0_nonneg] at hsq
    exact hsq
  have hbound :
      infDist (x[n] : E) S₁ ≤ infDist (x0 : E) (S₁ ∩ S₂) / Real.sqrt (k + 1) :=
    (le_div_iff₀ hsqrt_pos).2 hmul_le
  exact ⟨n, hn_le, hbound⟩

end

section

open Metric

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable {S₁ S₂ : Set E}
variable (hS₁_closed : IsClosed S₁) (hS₁_convex : Convex ℝ S₁)
variable (hS₂_closed : IsClosed S₂) (hS₂_convex : Convex ℝ S₂)
variable (hinter : (S₁ ∩ S₂).Nonempty) (x0 : S₂)

local notation "x[" k "]" =>
  alternating_projection_method S₁ S₂
    (hinter.mono Set.inter_subset_left) hS₁_closed hS₁_convex
    (hinter.mono Set.inter_subset_right) hS₂_closed hS₂_convex x0 k

/-- Helper for Corollary 8.22: finite-dimensional compactness provides a sequential cluster point
for the alternating-projection trajectory. -/
lemma alternating_projection_has_mapClusterPt :
    ∃ y : E, MapClusterPt y Filter.atTop (fun n ↦ (x[n] : E)) := by
  have hinter_nonempty : (S₁ ∩ S₂).Nonempty := hinter
  let s : E := Classical.choose hinter_nonempty
  have hs : s ∈ S₁ ∩ S₂ := Classical.choose_spec hinter_nonempty
  let r : ℝ := dist (x[0] : E) s
  have hball : ∀ n : ℕ, (x[n] : E) ∈ Metric.closedBall s r := by
    intro n
    have hdist : dist (x[n] : E) s ≤ dist (x[0] : E) s := by
      induction n with
      | zero =>
          exact le_rfl
      | succ n ih =>
          exact le_trans
            (alternating_projection_fejer
              (hS₁_closed := hS₁_closed) (hS₁_convex := hS₁_convex)
              (hS₂_closed := hS₂_closed) (hS₂_convex := hS₂_convex)
              (hinter := hinter_nonempty) (x0 := x0)
              hs n)
            ih
    simpa [r, Metric.mem_closedBall] using hdist
  letI : ProperSpace E := FiniteDimensional.proper ℝ E
  have hfreq :
      ∃ᶠ n in Filter.atTop, (x[n] : E) ∈ Metric.closedBall s r :=
    (Filter.Eventually.of_forall hball).frequently
  rcases (isCompact_closedBall s r).exists_mapClusterPt_of_frequently hfreq with ⟨y, -, hy⟩
  exact ⟨y, hy⟩

/-- Helper for Corollary 8.22: every sequential cluster point of the alternating-projection
trajectory lies in `S₁ ∩ S₂`. -/
lemma alternating_projection_cluster_point_mem_intersection {y : E}
    (hyCluster : MapClusterPt y Filter.atTop (fun n ↦ (x[n] : E))) :
    y ∈ S₁ ∩ S₂ := by
  have hyS₂ : y ∈ S₂ := by
    -- Closedness of `S₂` transfers membership from the entire trajectory to the cluster point.
    refine hS₂_closed.mem_of_mapClusterPt hyCluster ?_
    exact Filter.Eventually.of_forall fun n => (x[n]).property
  obtain ⟨ψ, hψmono, hψtendsto⟩ := MapClusterPt.tendsto_subseq hyCluster
  have hinfDist_zero :
      Filter.Tendsto (fun n ↦ infDist (x[ψ n] : E) S₁) Filter.atTop (nhds 0) :=
    (alternating_projection_infDist_tendsto_zero
      (hS₁_closed := hS₁_closed) (hS₁_convex := hS₁_convex)
      (hS₂_closed := hS₂_closed) (hS₂_convex := hS₂_convex) (hinter := hinter) (x0 := x0)).comp
      hψmono.tendsto_atTop
  have hinfDist_y :
      Filter.Tendsto (fun n ↦ infDist (x[ψ n] : E) S₁) Filter.atTop (nhds (infDist y S₁)) := by
    -- Continuity of `infDist` identifies the subsequential limit at the cluster point.
    have hcont :
        Filter.Tendsto (fun n ↦ infDist ((fun m ↦ (x[m] : E)) (ψ n)) S₁) Filter.atTop
          (nhds (infDist y S₁)) :=
      ((Metric.continuous_infDist_pt S₁).tendsto y).comp hψtendsto
    simpa [Function.comp] using hcont
  have hy_infDist : infDist y S₁ = 0 :=
    tendsto_nhds_unique hinfDist_y hinfDist_zero
  have hyS₁ : y ∈ S₁ := by
    -- A closed set has positive distance from every exterior point, so zero distance forces
    -- membership.
    by_contra hy_not_mem
    have hpos : 0 < infDist y S₁ :=
      (hS₁_closed.notMem_iff_infDist_pos (hinter.mono Set.inter_subset_left)).1 hy_not_mem
    linarith
  exact ⟨hyS₁, hyS₂⟩

-- Proof sketch: the same descent inequality shows that `x` is Fejér monotone with respect to
-- `S₁ ∩ S₂` and that `infDist (x[k] : E) S₁ → 0`. Finite dimensionality gives a cluster point;
-- closedness of `S₁` and `S₂` puts every cluster point in `S₁ ∩ S₂`, and then
-- `tendsto_to_limitPoint_of_isFejerMonotoneWithRespectTo` yields convergence of the whole
-- alternating-projection sequence.
/-- Corollary 8.22 (2): the alternating projection sequence converges to a point of
`S₁ ∩ S₂`. -/
theorem alternating_projection_tendsto_point_in_intersection :
    ∃ xStar : E,
      xStar ∈ S₁ ∩ S₂ ∧
        Filter.Tendsto (fun k ↦ (x[k] : E)) Filter.atTop (nhds xStar) := by
  have hFejer : ∀ y ∈ S₁ ∩ S₂, ∀ k : ℕ, dist (x[k + 1] : E) y ≤ dist (x[k] : E) y := by
    intro y hy k
    exact alternating_projection_fejer
      (hS₁_closed := hS₁_closed) (hS₁_convex := hS₁_convex)
      (hS₂_closed := hS₂_closed) (hS₂_convex := hS₂_convex) (hinter := hinter) (x0 := x0)
      hy k
  have hlimitPoints_subset :
      {y : E | MapClusterPt y Filter.atTop (fun n ↦ (x[n] : E))} ⊆ S₁ ∩ S₂ := by
    intro y hy
    exact alternating_projection_cluster_point_mem_intersection
      (hS₁_closed := hS₁_closed) (hS₁_convex := hS₁_convex)
      (hS₂_closed := hS₂_closed) (hS₂_convex := hS₂_convex) (hinter := hinter) (x0 := x0)
      hy
  have hlimitPoint : ∃ y : E, MapClusterPt y Filter.atTop (fun n ↦ (x[n] : E)) :=
    alternating_projection_has_mapClusterPt
      (hS₁_closed := hS₁_closed) (hS₁_convex := hS₁_convex)
      (hS₂_closed := hS₂_closed) (hS₂_convex := hS₂_convex) (hinter := hinter) (x0 := x0)
  obtain ⟨xStar, hxStarCluster, hxStarTendsto⟩ :=
    tendsto_to_limitPoint_of_isFejerMonotoneWithRespectTo hFejer hlimitPoints_subset hlimitPoint
  exact ⟨xStar, hlimitPoints_subset hxStarCluster, hxStarTendsto⟩

end
