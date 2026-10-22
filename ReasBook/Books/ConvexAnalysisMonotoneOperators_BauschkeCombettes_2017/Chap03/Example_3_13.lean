/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap03.Definition_3_8

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open Filter
open scoped InnerProductSpace Topology

variable {𝓗 : Type u} [NormedAddCommGroup 𝓗] [InnerProductSpace ℝ 𝓗]

/-- Helper for Example 3.13: distinct scaled orthonormal vectors stay at distance strictly bigger
than `1`. -/
private lemma scaled_orthonormal_dist_gt_one_of_ne (e : ℕ → 𝓗) (he : Orthonormal ℝ e)
    (α : ℕ → ℝ)
    (hα_gt_one : ∀ n : ℕ, 1 < α n) {m n : ℕ} (hmn : m ≠ n) :
    1 < dist (α m • e m) (α n • e n) := by
  -- Expand the squared norm and simplify the orthonormal cross-term away.
  have hαm_pos : 0 < α m := lt_trans zero_lt_one (hα_gt_one m)
  have hαn_pos : 0 < α n := lt_trans zero_lt_one (hα_gt_one n)
  have hm : ‖α m • e m‖ = α m := by
    rw [norm_smul, he.norm_eq_one m, mul_one, Real.norm_of_nonneg hαm_pos.le]
  have hn : ‖α n • e n‖ = α n := by
    rw [norm_smul, he.norm_eq_one n, mul_one, Real.norm_of_nonneg hαn_pos.le]
  have hinner : inner ℝ (α m • e m) (α n • e n) = 0 := by
    rw [real_inner_smul_left, inner_smul_right, he.inner_eq_zero hmn, mul_zero, mul_zero]
  have hsq :
      dist (α m • e m) (α n • e n) ^ 2 = α m ^ 2 + α n ^ 2 := by
    rw [dist_eq_norm, norm_sub_sq_real, hm, hn, hinner]
    ring
  have hnonneg : 0 ≤ dist (α m • e m) (α n • e n) := dist_nonneg
  nlinarith [hsq, hα_gt_one m, hα_gt_one n]

/-- Helper for Example 3.13: the distance from `0` to a scaled orthonormal vector is the scaling
coefficient. -/
private lemma dist_zero_scaled_orthonormal_point (e : ℕ → 𝓗) (he : Orthonormal ℝ e)
    (α : ℕ → ℝ)
    (hα_gt_one : ∀ n : ℕ, 1 < α n) (n : ℕ) :
    dist (0 : 𝓗) (α n • e n) = α n := by
  -- The norm is `|α n| · ‖e n‖`, and positivity of `α n` removes the absolute value.
  have hαn_pos : 0 < α n := lt_trans zero_lt_one (hα_gt_one n)
  rw [dist_eq_norm, zero_sub, norm_neg, norm_smul, he.norm_eq_one n, mul_one,
    Real.norm_of_nonneg hαn_pos.le]

/-- Helper for Example 3.13: a convergent sequence in the scaled orthonormal range is eventually
constant. -/
private lemma eventually_constant_of_tendsto_scaled_orthonormal_range (e : ℕ → 𝓗)
    (he : Orthonormal ℝ e) (α : ℕ → ℝ) (hα_gt_one : ∀ n : ℕ, 1 < α n) {u : ℕ → 𝓗} {x : 𝓗}
    (hu : ∀ n : ℕ, u n ∈ Set.range (fun k ↦ α k • e k)) (hx : Tendsto u atTop (𝓝 x)) :
    ∃ N k, ∀ n ≥ N, u n = α k • e k := by
  -- Convergent sequences are Cauchy, so eventually all later terms lie within distance `< 1`
  -- of a fixed anchor term.
  have hcauchy : CauchySeq u := hx.cauchySeq
  rcases (Metric.cauchySeq_iff'.1 hcauchy) 1 zero_lt_one with ⟨N, hN⟩
  rcases Set.mem_range.1 (hu N) with ⟨k, hk⟩
  refine ⟨N, k, ?_⟩
  intro n hn
  rcases Set.mem_range.1 (hu n) with ⟨kn, hkn⟩
  by_contra hneq
  have hdist_lt : dist (u n) (u N) < 1 := hN n hn
  have hkne : kn ≠ k := by
    intro hEq
    apply hneq
    calc
      u n = α kn • e kn := hkn.symm
      _ = α k • e k := by simp [hEq]
  have hdist_gt : 1 < dist (u n) (u N) := by
    rw [← hkn, ← hk]
    exact scaled_orthonormal_dist_gt_one_of_ne e he α hα_gt_one hkne
  linarith

/-- If every coefficient `α n` is strictly bigger than `1`, then the scaled orthonormal range is
closed. This is the separation statement used in Example 3.13 (1). -/
theorem isClosed_scaled_orthonormal_range_of_one_lt (e : ℕ → 𝓗) (he : Orthonormal ℝ e)
    (α : ℕ → ℝ) (hα_gt_one : ∀ n : ℕ, 1 < α n) :
    IsClosed (Set.range (fun n ↦ α n • e n)) := by
  -- The separation lemma makes every convergent sequence in the set eventually constant.
  have hseqClosed : IsSeqClosed (Set.range (fun n ↦ α n • e n)) := by
    intro u x hu hx
    rcases eventually_constant_of_tendsto_scaled_orthonormal_range e he α hα_gt_one hu hx with
      ⟨N, k, hNk⟩
    have hconst : u =ᶠ[atTop] fun _ ↦ α k • e k := by
      exact Filter.eventually_atTop.2 ⟨N, fun n hn ↦ hNk n hn⟩
    have hxconst : Tendsto (fun _ : ℕ ↦ α k • e k) atTop (𝓝 x) := hx.congr' hconst
    have hxeq : x = α k • e k := tendsto_nhds_unique hxconst tendsto_const_nhds
    exact Set.mem_range.2 ⟨k, hxeq.symm⟩
  exact (isSeqClosed_iff_isClosed.1 hseqClosed)

-- Proof sketch: Example 3.13 (1) is an immediate corollary of
-- `isClosed_scaled_orthonormal_range_of_one_lt`.
/-- Example 3.13 (1): if `e` is orthonormal and `α n > 1` decreases to `1`, then the set
`{α n • e n | n : ℕ}` is closed. -/
theorem isClosed_scaled_orthonormal_range (e : ℕ → 𝓗) (he : Orthonormal ℝ e) (α : ℕ → ℝ)
    (hα_gt_one : ∀ n : ℕ, 1 < α n) (_hα_antitone : Antitone α)
    (_hα_tendsto : Tendsto α atTop (nhds 1)) :
    IsClosed (Set.range (fun n ↦ α n • e n)) :=
  isClosed_scaled_orthonormal_range_of_one_lt e he α hα_gt_one

-- Proof sketch: the norms of the points `α n • e n` are exactly `α n`, so `hα_tendsto` gives
-- `Metric.infDist 0 (Set.range (fun n ↦ α n • e n)) = 1`; since every point of the set has norm
-- strictly bigger than `1` by `hα_gt_one`, no point of the set realizes this infimum.
/-- The distance from `0` to `Set.range (fun n ↦ α n • e n)` is `1` whenever `α n > 1` tends to
`1`. -/
theorem zero_infDist_scaled_orthonormal_range_eq_one_of_tendsto (e : ℕ → 𝓗)
    (he : Orthonormal ℝ e) (α : ℕ → ℝ) (hα_gt_one : ∀ n : ℕ, 1 < α n)
    (hα_tendsto : Tendsto α atTop (nhds 1)) :
    Metric.infDist (0 : 𝓗) (Set.range (fun n ↦ α n • e n)) = 1 := by
  let C : Set 𝓗 := Set.range (fun n ↦ α n • e n)
  have hC_nonempty : C.Nonempty := ⟨α 0 • e 0, by
    simp [C]⟩
  have hlower : 1 ≤ Metric.infDist (0 : 𝓗) C := by
    -- Every point in the set has norm strictly bigger than `1`.
    rw [Metric.le_infDist hC_nonempty]
    intro y hy
    rcases Set.mem_range.1 hy with ⟨n, rfl⟩
    rw [dist_zero_scaled_orthonormal_point e he α hα_gt_one n]
    exact le_of_lt (hα_gt_one n)
  have hupper : Metric.infDist (0 : 𝓗) C ≤ 1 := by
    -- Since `α n → 1`, the set contains points whose distance to `0` is arbitrarily close to `1`.
    refine le_of_forall_pos_le_add fun ε hε ↦ ?_
    rcases (Metric.tendsto_atTop.1 hα_tendsto) ε hε with ⟨N, hN⟩
    have hdist : dist (α N) 1 < ε := hN N le_rfl
    have hα_lt : α N < 1 + ε := by
      have hsub : α N - 1 < ε := by
        simpa [Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr (le_of_lt (hα_gt_one N)))] using hdist
      linarith
    have hmem : α N • e N ∈ C := by
      simp [C]
    calc
      Metric.infDist (0 : 𝓗) C ≤ dist (0 : 𝓗) (α N • e N) := Metric.infDist_le_dist_of_mem hmem
      _ = α N := dist_zero_scaled_orthonormal_point e he α hα_gt_one N
      _ ≤ 1 + ε := le_of_lt hα_lt
  exact le_antisymm hupper hlower

/-- Example 3.13 uses the previous infimum computation under the stronger textbook hypothesis that
`α` decreases to `1`. -/
theorem zero_infDist_scaled_orthonormal_range_eq_one (e : ℕ → 𝓗) (he : Orthonormal ℝ e)
    (α : ℕ → ℝ) (hα_gt_one : ∀ n : ℕ, 1 < α n) (_hα_antitone : Antitone α)
    (hα_tendsto : Tendsto α atTop (nhds 1)) :
    Metric.infDist (0 : 𝓗) (Set.range (fun n ↦ α n • e n)) = 1 :=
  zero_infDist_scaled_orthonormal_range_eq_one_of_tendsto e he α hα_gt_one hα_tendsto

-- Proof sketch: combine `zero_infDist_scaled_orthonormal_range_eq_one` with the characterization
-- of best approximations from `Definition 3.8`; any best approximation `p = α n • e n` would
-- satisfy `‖p‖ = 1`, contradicting `1 < α n`.
/-- If `α n > 1` tends to `1`, then `0` has no best approximation in the scaled orthonormal
range. -/
theorem zero_has_no_projection_onto_scaled_orthonormal_range_of_tendsto (e : ℕ → 𝓗)
    (he : Orthonormal ℝ e) (α : ℕ → ℝ) (hα_gt_one : ∀ n : ℕ, 1 < α n)
    (hα_tendsto : Tendsto α atTop (nhds 1)) :
    ¬ ∃ p : 𝓗, IsBestApproximation (0 : 𝓗) (Set.range (fun n ↦ α n • e n)) p := by
  -- A best approximation would have to realize the infimum distance `1`, but every point in the
  -- set has distance strictly bigger than `1`.
  rintro ⟨p, hp⟩
  rw [isBestApproximation_iff_mem_and_dist_eq_infDist] at hp
  rcases Set.mem_range.1 hp.1 with ⟨n, rfl⟩
  have hdist : dist (0 : 𝓗) (α n • e n) = α n :=
    dist_zero_scaled_orthonormal_point e he α hα_gt_one n
  have hinf : Metric.infDist (0 : 𝓗) (Set.range (fun k ↦ α k • e k)) = 1 :=
    zero_infDist_scaled_orthonormal_range_eq_one_of_tendsto e he α hα_gt_one hα_tendsto
  have hα_eq_one : α n = 1 := by
    calc
      α n = dist (0 : 𝓗) (α n • e n) := hdist.symm
      _ = Metric.infDist (0 : 𝓗) (Set.range (fun k ↦ α k • e k)) := hp.2
      _ = 1 := hinf
  linarith [hα_gt_one n]

/-- Example 3.13 (2): `0` has no projection onto `{α n • e n | n : ℕ}`; equivalently, the
distance from `0` to this set is not attained on the set. -/
theorem zero_has_no_projection_onto_scaled_orthonormal_range (e : ℕ → 𝓗)
    (he : Orthonormal ℝ e) (α : ℕ → ℝ) (hα_gt_one : ∀ n : ℕ, 1 < α n)
    (_hα_antitone : Antitone α) (hα_tendsto : Tendsto α atTop (nhds 1)) :
    ¬ ∃ p : 𝓗, IsBestApproximation (0 : 𝓗) (Set.range (fun n ↦ α n • e n)) p :=
  zero_has_no_projection_onto_scaled_orthonormal_range_of_tendsto
    e he α hα_gt_one hα_tendsto
