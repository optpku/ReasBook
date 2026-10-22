/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap02.Lemma_2_47
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap05.Definition_5_32
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap05.Lemma_5_31
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap05.Theorem_5_36
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap05.Theorem_5_5

-- Declarations for this item will be appended below by the statement pipeline.

open Filter
open scoped BigOperators Topology

universe u

section

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable {C : Set H} {y : ℕ → H} {α : ℕ → ℕ → ℝ}

/-- Helper for Corollary 5.37: quasi-Fejér monotonicity makes each distance sequence
`n ↦ ‖y n - z‖` converge. -/
private theorem quasiFejerMonotone_norm_tendsto
    (hy : QuasiFejerMonotone C y) {z : H} (hz : z ∈ C) :
    ∃ l : ℝ, Tendsto (fun n ↦ ‖y n - z‖) atTop (𝓝 l) := by
  rcases hy.exists_summable_sqdist_error z hz with ⟨ε, hεsumm, hstep⟩
  let a : ℕ → NNReal := fun n ↦ ⟨‖y n - z‖ ^ 2, sq_nonneg _⟩
  have hrec : ∀ n : ℕ, a (n + 1) + 0 ≤ (1 + 0) * a n + ε n := by
    intro n
    -- The quasi-Fejér inequality already has the perturbed-descent shape from Lemma 5.31.
    norm_num [a]
    exact hstep n
  rcases
      (
      tendsto_and_summable_of_summable_perturbed_descent
        (α := a) (β := fun _ ↦ 0) (γ := fun _ ↦ 0) (ε := ε)
        summable_zero hεsumm hrec) with
    ⟨⟨l, ha⟩, _⟩
  refine ⟨Real.sqrt l, ?_⟩
  have hareal :
      Tendsto (fun n ↦ ((a n : NNReal) : ℝ)) atTop (𝓝 (l : ℝ)) :=
    (NNReal.tendsto_coe').2 ⟨l.2, ha⟩
  have hsqrt :
      Tendsto (fun n ↦ Real.sqrt (((a n : NNReal) : ℝ))) atTop (𝓝 (Real.sqrt (l : ℝ))) :=
    (Real.continuous_sqrt.tendsto _).comp hareal
  -- Taking square roots converts convergence of squared distances back to convergence of norms.
  have hsqrt_apply :
      (fun n ↦ Real.sqrt (((a n : NNReal) : ℝ))) = (fun n ↦ ‖y n - z‖) := by
    funext n
    change Real.sqrt (‖y n - z‖ ^ 2) = ‖y n - z‖
    rw [Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg _)]
  rw [hsqrt_apply] at hsqrt
  exact hsqrt

/-- Helper for Corollary 5.37: the fixed finite prefix weight tends to `0` because each column of
`α` tends to `0`. -/
private theorem prefix_weight_tendsto_zero
    (hα_tendsto : ∀ k, Tendsto (fun n ↦ α n k) atTop (𝓝 0)) (m : ℕ) :
    Tendsto (fun n ↦ Finset.sum (Finset.range m) (fun k ↦ α n k)) atTop (𝓝 0) := by
  induction m with
  | zero =>
      -- The empty prefix contributes no weight.
      simp
  | succ m hm =>
      -- Extend the prefix by one column and combine the two convergent pieces.
      simpa [Finset.sum_range_succ] using hm.add (hα_tendsto m)

/-- Helper for Corollary 5.37: splitting the total mass at `m` rewrites the tail mass as
`1 -` the prefix mass. -/
private lemma tail_weight_eq_one_sub_prefix_weight
    (hα_sum : ∀ n, Finset.sum (Finset.range (n + 1)) (fun k ↦ α n k) = 1)
    {m n : ℕ} (hmn : m ≤ n) :
    Finset.sum (Finset.Ico m (n + 1)) (fun k ↦ α n k) =
      1 - Finset.sum (Finset.range m) (fun k ↦ α n k) := by
  have hsplit :=
    Finset.sum_range_add_sum_Ico (f := fun k ↦ α n k) (Nat.le_trans hmn (Nat.le_succ n))
  rw [hα_sum n] at hsplit
  linarith

/-- Helper for Corollary 5.37: a finite weighted sum of vectors in the `μ`-ball has norm bounded
by `μ` times the total weight. -/
private lemma norm_weighted_sum_le_mul_weight_sum
    {ι : Type*} (s : Finset ι) (w : ι → ℝ) (z : ι → H) {μ : ℝ}
    (hμ : 0 ≤ μ) (hw : ∀ i ∈ s, 0 ≤ w i) (hz : ∀ i ∈ s, ‖z i‖ ≤ μ) :
    ‖Finset.sum s (fun i ↦ w i • z i)‖ ≤ μ * Finset.sum s w := by
  calc
    ‖Finset.sum s (fun i ↦ w i • z i)‖ ≤ Finset.sum s (fun i ↦ ‖w i • z i‖) := norm_sum_le _ _
    _ = Finset.sum s (fun i ↦ w i * ‖z i‖) := by
          refine Finset.sum_congr rfl ?_
          intro i hi
          rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (hw i hi)]
    _ ≤ Finset.sum s (fun i ↦ w i * μ) := by
          refine Finset.sum_le_sum ?_
          intro i hi
          exact mul_le_mul_of_nonneg_left (hz i hi) (hw i hi)
    _ = μ * Finset.sum s w := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl ?_
          intro i hi
          ring

/-- Helper for Corollary 5.37: the normalized tail average belongs to the closed convex hull of
the sequence tail starting at `m`. -/
private theorem tail_centerMass_mem_tailClosedConvexHull
    (hα_nonneg : ∀ n k, k ≤ n → 0 ≤ α n k)
    {m n : ℕ} (hmn : m ≤ n)
    (hτ : 0 < Finset.sum (Finset.Ico m (n + 1)) (fun k ↦ α n k)) :
    (Finset.Ico m (n + 1)).centerMass (fun k ↦ α n k) y ∈ tailClosedConvexHull y m := by
  have hconv :
      (Finset.Ico m (n + 1)).centerMass (fun k ↦ α n k) y ∈ convexHull ℝ (y '' Set.Ici m) := by
    refine Finset.centerMass_mem_convexHull _ ?_ hτ ?_
    · intro k hk
      exact hα_nonneg n k (Nat.le_of_lt_succ (Finset.mem_Ico.mp hk).2)
    · intro k hk
      exact ⟨k, Finset.mem_Ico.mp hk |>.1, rfl⟩
  exact convexHull_subset_closedConvexHull hconv

-- Proof sketch: quasi-Fejér monotonicity makes `y` bounded. For each tail index `m`, consider the
-- closed convex hull of the tail range `Set.range (fun k ↦ y (k + m))`; normalize the tail weights
-- to obtain a comparison point in that hull and use the vanishing of the fixed-column coefficients
-- to show that the weighted-average sequence approaches every such tail hull in norm. The
-- nonlinear ergodic theorem for quasi-Fejér sequences then yields weak convergence from the weak
-- sequential cluster-point hypothesis.
/-- Corollary 5.37: if `y` is quasi-Fejér monotone with respect to a nonempty set `C`, if
`α n k ≥ 0` for `k ≤ n`, `∑_{k=0}^n α n k = 1`, and each fixed coefficient column tends to `0`,
then the weighted averages `∑_{k=0}^n α n k • y k` converge weakly to a point of `C` provided all
of their weak sequential cluster points lie in `C`. -/
theorem tendsto_weakly_of_weighted_averages_of_quasiFejerMonotone_of_weakSequentialClusterPts_mem
    (hC : C.Nonempty) (hy : QuasiFejerMonotone C y)
    (hα_nonneg : ∀ n k, k ≤ n → 0 ≤ α n k)
    (hα_sum : ∀ n, Finset.sum (Finset.range (n + 1)) (fun k ↦ α n k) = 1)
    (hα_tendsto : ∀ k, Tendsto (fun n ↦ α n k) atTop (𝓝 0))
    (hcluster :
      ∀ z : H,
        IsSequentialClusterPt
            (fun n ↦
              toWeakSpace ℝ H
                (Finset.sum (Finset.range (n + 1)) (fun k ↦ α n k • y k)))
            (toWeakSpace ℝ H z) →
          z ∈ C) :
    ∃ z ∈ C,
      Tendsto
        (fun n ↦
          toWeakSpace ℝ H
            (Finset.sum (Finset.range (n + 1)) (fun k ↦ α n k • y k)))
        atTop (𝓝 (toWeakSpace ℝ H z)) := by
  let xBar : ℕ → H := fun n ↦
    Finset.sum (Finset.range (n + 1)) (fun k ↦ α n k • y k)
  have hy_dist :
      ∀ z ∈ C, ∃ l : ℝ, Tendsto (fun n ↦ ‖y n - z‖) atTop (𝓝 l) := by
    intro z hz
    -- The quasi-Fejér hypothesis supplies the distance convergence required for boundedness.
    exact quasiFejerMonotone_norm_tendsto hy hz
  have hy_bounded : Bornology.IsBounded (Set.range y) := by
    rcases hC with ⟨z, hz⟩
    exact bounded_range_of_convergent_distance_to_point (hy_dist z hz)
  rcases isBounded_iff_forall_norm_le.mp hy_bounded with ⟨μ, hμ⟩
  have hy_norm_le : ∀ k : ℕ, ‖y k‖ ≤ μ := by
    intro k
    exact hμ _ (Set.mem_range_self k)
  have hμ_nonneg : 0 ≤ μ := by
    exact le_trans (norm_nonneg _) (hy_norm_le 0)
  have hy_step :
      ∀ z ∈ C, ∃ ε : ℕ → NNReal, Summable ε ∧
        ∀ n : ℕ, ‖y (n + 1) - z‖ ^ 2 ≤ ‖y n - z‖ ^ 2 + ε n := by
    intro z hz
    -- Unpack the quasi-Fejér witness in the explicit form required by Theorem 5.36.
    exact hy.exists_summable_sqdist_error z hz
  have hdist :
      ∀ m : ℕ, Tendsto (fun n ↦ Metric.infDist (xBar n) (tailClosedConvexHull y m)) atTop (𝓝 0) := by
    intro m
    let s : ℕ → ℝ := fun n ↦ Finset.sum (Finset.range m) (fun k ↦ α n k)
    have hs_tendsto : Tendsto s atTop (𝓝 0) := prefix_weight_tendsto_zero hα_tendsto m
    have hs_lt_one : ∀ᶠ n in atTop, s n < 1 := by
      simpa [s] using hs_tendsto.eventually (Iio_mem_nhds one_pos)
    have hupper :
        ∀ᶠ n in atTop, Metric.infDist (xBar n) (tailClosedConvexHull y m) ≤ 2 * μ * s n := by
      filter_upwards [eventually_ge_atTop m, hs_lt_one] with n hmn hslt
      let τ : ℝ := Finset.sum (Finset.Ico m (n + 1)) (fun k ↦ α n k)
      let z : H := (Finset.Ico m (n + 1)).centerMass (fun k ↦ α n k) y
      have hτ_eq : τ = 1 - s n := by
        simpa [τ, s] using tail_weight_eq_one_sub_prefix_weight hα_sum hmn
      have hs_nonneg_n : 0 ≤ s n := by
        -- Once `n ≥ m`, every prefix index lies in the admissible range `k ≤ n`.
        exact Finset.sum_nonneg fun k hk ↦
          hα_nonneg n k (Nat.le_trans (Nat.le_of_lt (Finset.mem_range.mp hk)) hmn)
      have hτ_pos : 0 < τ := by
        rw [hτ_eq]
        linarith
      have hz_mem : z ∈ tailClosedConvexHull y m := by
        -- The tail comparison point is the normalized tail center of mass from the textbook proof.
        simpa [z] using
          tail_centerMass_mem_tailClosedConvexHull
            (y := y) (α := α) hα_nonneg hmn hτ_pos
      have hz_norm_le : ‖z‖ ≤ μ := by
        have hz_ball : z ∈ Metric.closedBall (0 : H) μ := by
          apply (convex_closedBall (0 : H) μ).centerMass_mem
          · intro k hk
            exact hα_nonneg n k (Nat.le_of_lt_succ (Finset.mem_Ico.mp hk).2)
          · simpa [z, τ] using hτ_pos
          · intro k hk
            simpa [Metric.mem_closedBall, dist_eq_norm] using hy_norm_le k
        simpa [Metric.mem_closedBall, dist_eq_norm] using hz_ball
      have hprefix_norm :
          ‖Finset.sum (Finset.range m) (fun k ↦ α n k • y k)‖ ≤ μ * s n := by
        -- Bounding the prefix part uses the uniform norm bound on `y`.
        simpa [s, mul_comm, mul_left_comm, mul_assoc] using
          norm_weighted_sum_le_mul_weight_sum
            (s := Finset.range m) (w := fun k ↦ α n k) (z := y) hμ_nonneg
            (fun k hk ↦
              hα_nonneg n k (Nat.le_trans (Nat.le_of_lt (Finset.mem_range.mp hk)) hmn))
            (fun k _hk ↦ hy_norm_le k)
      have htail_norm :
          ‖Finset.sum (Finset.Ico m (n + 1)) (fun k ↦ α n k • y k)‖ ≤ μ * τ := by
        -- The same bound controls the unnormalized tail sum by the tail mass.
        simpa [τ, mul_comm, mul_left_comm, mul_assoc] using
          norm_weighted_sum_le_mul_weight_sum
            (s := Finset.Ico m (n + 1)) (w := fun k ↦ α n k) (z := y) hμ_nonneg
            (fun k hk ↦ hα_nonneg n k (Nat.le_of_lt_succ (Finset.mem_Ico.mp hk).2))
            (fun k _hk ↦ hy_norm_le k)
      have htail_eq :
          τ • z = Finset.sum (Finset.Ico m (n + 1)) (fun k ↦ α n k • y k) := by
        -- Unfolding `centerMass` identifies the normalized tail average with the tail sum.
        simp [z, τ, Finset.centerMass, hτ_pos.ne', smul_smul]
      have hx_decomp :
          xBar n =
            Finset.sum (Finset.range m) (fun k ↦ α n k • y k) + τ • z := by
        -- Split the full weighted average into the prefix contribution and the tail center of mass.
        calc
          xBar n = Finset.sum (Finset.range (n + 1)) (fun k ↦ α n k • y k) := by rfl
          _ =
              Finset.sum (Finset.range m) (fun k ↦ α n k • y k) +
                Finset.sum (Finset.Ico m (n + 1)) (fun k ↦ α n k • y k) := by
                simpa [xBar] using
                  (Finset.sum_range_add_sum_Ico
                    (f := fun k ↦ α n k • y k) (Nat.le_trans hmn (Nat.le_succ n))).symm
          _ =
              Finset.sum (Finset.range m) (fun k ↦ α n k • y k) + τ • z := by
                rw [← htail_eq]
      have hz_scaled_norm : ‖s n • z‖ ≤ μ * s n := by
        calc
          ‖s n • z‖ = |s n| * ‖z‖ := norm_smul _ _
          _ = s n * ‖z‖ := by rw [abs_of_nonneg hs_nonneg_n]
          _ ≤ s n * μ := by gcongr
          _ = μ * s n := by ring
      have hxz :
          xBar n - z = Finset.sum (Finset.range m) (fun k ↦ α n k • y k) - s n • z := by
        have hτ_sub : τ - 1 = -s n := by
          rw [hτ_eq]
          ring
        calc
          xBar n - z =
              (Finset.sum (Finset.range m) (fun k ↦ α n k • y k) + τ • z) - z := by
            rw [hx_decomp]
          _ = Finset.sum (Finset.range m) (fun k ↦ α n k • y k) + (τ • z - z) := by
            abel_nf
          _ =
              Finset.sum (Finset.range m) (fun k ↦ α n k • y k) +
                (τ • z + (-1 : ℝ) • z) := by
                  simp [sub_eq_add_neg]
          _ = Finset.sum (Finset.range m) (fun k ↦ α n k • y k) + ((τ - 1) • z) := by
            rw [← add_smul]
            simp [sub_eq_add_neg]
          _ = Finset.sum (Finset.range m) (fun k ↦ α n k • y k) - s n • z := by
            rw [hτ_sub, neg_smul]
            abel_nf
      have hdist_le : dist (xBar n) z ≤ 2 * μ * s n := by
        -- The prefix mass controls both the prefix sum and the correction from renormalizing
        -- the tail weights.
        calc
          dist (xBar n) z = ‖xBar n - z‖ := by rw [dist_eq_norm]
          _ = ‖Finset.sum (Finset.range m) (fun k ↦ α n k • y k) - s n • z‖ := by rw [hxz]
          _ ≤ ‖Finset.sum (Finset.range m) (fun k ↦ α n k • y k)‖ + ‖s n • z‖ := norm_sub_le _ _
          _ ≤ μ * s n + μ * s n := by gcongr
          _ = 2 * μ * s n := by ring
      exact (Metric.infDist_le_dist_of_mem hz_mem).trans hdist_le
    have hupper_tendsto : Tendsto (fun n ↦ 2 * μ * s n) atTop (𝓝 0) := by
      simpa [s, mul_assoc] using hs_tendsto.const_mul (2 * μ)
    exact squeeze_zero' (Eventually.of_forall fun _ ↦ Metric.infDist_nonneg) hupper hupper_tendsto
  have hcluster' :
      ∀ z : H,
        IsSequentialClusterPt (fun n ↦ toWeakSpace ℝ H (xBar n)) (toWeakSpace ℝ H z) → z ∈ C := by
    intro z hz
    simpa [xBar] using hcluster z hz
  -- Route correction: apply Theorem 5.36 directly once the tail-hull distance estimate is proved.
  rcases
      tendsto_weakly_of_quasiFejerMonotone_of_tailClosedConvexHull_infDist_tendsto_zero
        (C := C) hC xBar y hy_step hdist hcluster' with
    ⟨z, hzC, hz⟩
  refine ⟨z, hzC, ?_⟩
  simpa [xBar] using hz

end
