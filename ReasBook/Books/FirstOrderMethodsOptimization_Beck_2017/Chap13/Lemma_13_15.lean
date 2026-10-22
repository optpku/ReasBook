/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

/- Lemma 13.15 is `source-facing`: the primitive data are only the real sequence `a : ℕ → ℝ`, the
non-summability hypothesis `¬ Summable (fun n ↦ |a n|)`, and the exponent `ε > 0`.

The domain-style owner sampling here is:
- `_root_.summable_nat_add_iff` for canonical tail/shift control of series on `ℕ`;
- `ENNReal.ofReal_tsum_of_nonneg` for nonnegative real series recorded in `ℝ≥0∞`;
- `Filter.frequently_atTop'` for the canonical `atTop` formulation of "infinitely often";
- `Set.Infinite.exists_gt` for the source-facing infinite-set view on `ℕ`.

The square tail itself is genuinely a nonnegative infinite sum that need not be summable in `ℝ`, so
the canonical owner remains the `ENNReal` series. The textbook conclusion speaks about infinitely
many indices, so the main public statement stays `Set.Infinite`; the filter-level `atTop` view is
kept only as a thin bridge theorem below. -/

/-- Helper for Lemma 13.15: if the good-index set is not infinite, then beyond some positive index
every square tail is strictly below the claimed lower bound. -/
lemma eventually_tail_sq_lt_of_not_infinite
    {a : ℕ → ℝ} {ε : ℝ}
    (hfinite :
      ¬ Set.Infinite
        {k : ℕ |
          0 < k ∧
            ENNReal.ofReal ((k : ℝ) ^ (-(1 + ε))) ≤
              ∑' n : ℕ, ENNReal.ofReal ((a (n + k)) ^ 2)}) :
    ∃ K : ℕ, 1 ≤ K ∧ ∀ k ≥ K,
      ∑' n : ℕ, ENNReal.ofReal ((a (n + k)) ^ 2) <
        ENNReal.ofReal ((k : ℝ) ^ (-(1 + ε))) := by
  let good : Set ℕ := {k : ℕ |
    0 < k ∧
      ENNReal.ofReal ((k : ℝ) ^ (-(1 + ε))) ≤
        ∑' n : ℕ, ENNReal.ofReal ((a (n + k)) ^ 2)}
  have hnotfreq : ¬ ∃ᶠ k : ℕ in Filter.atTop, k ∈ good := by
    simpa [good, Nat.frequently_atTop_iff_infinite] using hfinite
  have hevent : ∀ᶠ k : ℕ in Filter.atTop, ¬ k ∈ good := by
    simpa [Filter.Frequently] using hnotfreq
  have hpos : ∀ᶠ k : ℕ in Filter.atTop, 0 < k := Nat.eventually_pos
  have hcombined : ∀ᶠ k : ℕ in Filter.atTop, 0 < k ∧ ¬ k ∈ good := hpos.and hevent
  rcases Filter.mem_atTop_sets.mp hcombined with ⟨K, hK⟩
  refine ⟨K, ?_, ?_⟩
  · exact Nat.succ_le_of_lt (hK K le_rfl).1
  · intro k hk
    have hk' := hK k hk
    have hkpos : 0 < k := hk'.1
    have hknot : ¬ k ∈ good := hk'.2
    dsimp [good] at hknot
    have hnotge :
        ¬ ENNReal.ofReal ((k : ℝ) ^ (-(1 + ε))) ≤
          ∑' n : ℕ, ENNReal.ofReal ((a (n + k)) ^ 2) := by
      intro hge
      have hgood : k ∈ good := And.intro hkpos hge
      exact hknot hgood
    exact lt_of_not_ge hnotge

/-- Helper for Lemma 13.15: every shifted square term is nonnegative. -/
lemma shifted_sq_nonneg {a : ℕ → ℝ} (k n : ℕ) : 0 ≤ (a (n + k)) ^ 2 :=
  sq_nonneg _

/-- Helper for Lemma 13.15: a strict `ENNReal` tail estimate yields the corresponding strict real
bound on the square tail. -/
lemma real_tail_sq_lt_of_ennreal_tail_sq_lt
    {a : ℕ → ℝ} {k : ℕ} {r : ℝ}
    (_hr : 0 ≤ r)
    (htail : ∑' n : ℕ, ENNReal.ofReal ((a (n + k)) ^ 2) < ENNReal.ofReal r) :
    ∑' n : ℕ, (a (n + k)) ^ 2 < r := by
  let b : ℕ → NNReal := fun n ↦ ⟨(a (n + k)) ^ 2, shifted_sq_nonneg k n⟩
  have htail_ne_top :
      ∑' n : ℕ, ENNReal.ofReal ((a (n + k)) ^ 2) ≠ (⊤ : ENNReal) := ne_top_of_lt htail
  have hb_tsum_ne_top : (∑' n : ℕ, (b n : ENNReal)) ≠ (⊤ : ENNReal) := by
    simpa [b, ENNReal.ofReal_eq_coe_nnreal (shifted_sq_nonneg k _)] using htail_ne_top
  have hb_summable : Summable b := ENNReal.tsum_coe_ne_top_iff_summable.mp hb_tsum_ne_top
  have hsummable : Summable (fun n : ℕ ↦ (a (n + k)) ^ 2) := by
    simpa [b] using (NNReal.summable_coe.2 hb_summable)
  have htail_toReal :
      ENNReal.toReal (∑' n : ℕ, ENNReal.ofReal ((a (n + k)) ^ 2)) < r := by
    exact (ENNReal.lt_ofReal_iff_toReal_lt htail_ne_top).1 htail
  have htail_toReal_eq :
      ENNReal.toReal (∑' n : ℕ, ENNReal.ofReal ((a (n + k)) ^ 2)) =
        ∑' n : ℕ, (a (n + k)) ^ 2 := by
    -- Rewrite the `ENNReal` tail as the image of the real square series, then take `toReal`.
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun n ↦ shifted_sq_nonneg k n) hsummable]
    exact ENNReal.toReal_ofReal (tsum_nonneg fun n ↦ shifted_sq_nonneg k n)
  simpa [htail_toReal_eq] using htail_toReal

/-- Helper for Lemma 13.15: a strict `ENNReal` square-tail bound forces the shifted square series
to be summable in `ℝ`. -/
lemma summable_shifted_sq_of_ennreal_tail_lt
    {a : ℕ → ℝ} {k : ℕ} {r : ℝ}
    (htail : ∑' n : ℕ, ENNReal.ofReal ((a (n + k)) ^ 2) < ENNReal.ofReal r) :
    Summable (fun n ↦ (a (n + k)) ^ 2) := by
  let b : ℕ → NNReal := fun n ↦ ⟨(a (n + k)) ^ 2, shifted_sq_nonneg k n⟩
  have htail_ne_top :
      ∑' n : ℕ, ENNReal.ofReal ((a (n + k)) ^ 2) ≠ (⊤ : ENNReal) := ne_top_of_lt htail
  have hb_tsum_ne_top : (∑' n : ℕ, (b n : ENNReal)) ≠ (⊤ : ENNReal) := by
    simpa [b, ENNReal.ofReal_eq_coe_nnreal (shifted_sq_nonneg k _)] using htail_ne_top
  have hb_summable : Summable b := ENNReal.tsum_coe_ne_top_iff_summable.mp hb_tsum_ne_top
  simpa [b] using (NNReal.summable_coe.2 hb_summable)

/-- Helper for Lemma 13.15: the finite sum of `k^δ` over `Ico K (n + 1)` dominates the matching
integral lower bound. -/
lemma rpow_sum_Ico_lower_bound
    {δ : ℝ} (hδ : 0 < δ) {K n : ℕ} (hKn : K ≤ n) :
    (((n : ℝ) ^ (1 + δ) - (K : ℝ) ^ (1 + δ)) / (1 + δ)) ≤
      Finset.sum (Finset.Ico K (n + 1)) (fun k ↦ (k : ℝ) ^ δ) := by
  have hδ_nonneg : 0 ≤ δ := le_of_lt hδ
  have hIntegral :
      ∫ x in (K : ℝ)..(n : ℝ), x ^ δ =
        (((n : ℝ) ^ (1 + δ) - (K : ℝ) ^ (1 + δ)) / (1 + δ)) := by
    -- Compute the source antiderivative exactly.
    rw [_root_.integral_rpow (a := (K : ℝ)) (b := (n : ℝ)) (r := δ) (by left; linarith)]
    ring_nf
  have hIntervalBound :
      ∀ k ∈ Finset.Ico K n,
        ∫ x in (k : ℝ)..(((k + 1 : ℕ) : ℝ)), x ^ δ ≤ (((k + 1 : ℕ) : ℝ) ^ δ) := by
    intro k hk
    have hk_le : (k : ℝ) ≤ (((k + 1 : ℕ) : ℝ)) := by exact_mod_cast Nat.le_succ k
    have hδ_gt_neg_one : -1 < δ := by
      linarith
    have hfk :
        IntervalIntegrable (fun x : ℝ ↦ x ^ δ) MeasureTheory.volume (k : ℝ) (((k + 1 : ℕ) : ℝ)) := by
      exact intervalIntegral.intervalIntegrable_rpow' (a := (k : ℝ))
        (b := (((k + 1 : ℕ) : ℝ))) hδ_gt_neg_one
    have hgk :
        IntervalIntegrable (fun _ : ℝ ↦ (((k + 1 : ℕ) : ℝ) ^ δ)) MeasureTheory.volume
          (k : ℝ) (((k + 1 : ℕ) : ℝ)) := by
      exact continuous_const.intervalIntegrable _ _
    have hmono :
        ∀ x ∈ Set.Icc (k : ℝ) (((k + 1 : ℕ) : ℝ)), x ^ δ ≤ (((k + 1 : ℕ) : ℝ) ^ δ) := by
      intro x hx
      have hx_nonneg : 0 ≤ x := le_trans (Nat.cast_nonneg k) hx.1
      exact
        (Real.monotoneOn_rpow_Ici_of_exponent_nonneg hδ_nonneg)
          (show x ∈ Set.Ici (0 : ℝ) from hx_nonneg)
          (show (((k + 1 : ℕ) : ℝ)) ∈ Set.Ici (0 : ℝ) from by
            show 0 ≤ (((k + 1 : ℕ) : ℝ))
            positivity)
          hx.2
    -- Compare each unit-interval integral with the right endpoint value.
    calc
      ∫ x in (k : ℝ)..(((k + 1 : ℕ) : ℝ)), x ^ δ ≤
          ∫ x in (k : ℝ)..(((k + 1 : ℕ) : ℝ)), (((k + 1 : ℕ) : ℝ) ^ δ) :=
        intervalIntegral.integral_mono_on hk_le hfk hgk hmono
      _ = (((k + 1 : ℕ) : ℝ) ^ δ) := by
        simp [intervalIntegral.integral_const, hk_le]
  have hPartitionLe :
      ∫ x in (K : ℝ)..(n : ℝ), x ^ δ ≤
        Finset.sum (Finset.Ico K n) (fun k ↦ (((k + 1 : ℕ) : ℝ) ^ δ)) := by
    -- Partition the source integral into adjacent unit intervals, then sum the pointwise bounds.
    rw [← intervalIntegral.sum_integral_adjacent_intervals_Ico
      (f := fun x : ℝ ↦ x ^ δ) (μ := MeasureTheory.volume) hKn]
    · exact Finset.sum_le_sum hIntervalBound
    · intro k hk
      have hδ_gt_neg_one : -1 < δ := by
        linarith
      exact intervalIntegral.intervalIntegrable_rpow' (a := (k : ℝ))
        (b := (((k + 1 : ℕ) : ℝ))) hδ_gt_neg_one
  have hShift :
      Finset.sum (Finset.Ico K n) (fun k ↦ (((k + 1 : ℕ) : ℝ) ^ δ)) =
        Finset.sum (Finset.Ico (K + 1) (n + 1)) (fun k ↦ (k : ℝ) ^ δ) := by
    -- Shift the finite interval exactly as in the source proof.
    rw [Finset.sum_Ico_eq_sum_range, Finset.sum_Ico_eq_sum_range]
    simp [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]
  have hInsert :
      Finset.sum (Finset.Ico (K + 1) (n + 1)) (fun k ↦ (k : ℝ) ^ δ) ≤
        Finset.sum (Finset.Ico K (n + 1)) (fun k ↦ (k : ℝ) ^ δ) := by
    have hKterm_nonneg : 0 ≤ (K : ℝ) ^ δ := Real.rpow_nonneg (Nat.cast_nonneg K) δ
    -- Add back the missing left endpoint `K ^ δ`.
    rw [Finset.sum_eq_sum_Ico_succ_bot (Nat.lt_succ_of_le hKn) (fun k ↦ (k : ℝ) ^ δ)]
    simpa [add_comm] using (le_add_of_nonneg_left hKterm_nonneg :
      Finset.sum (Finset.Ico (K + 1) (n + 1)) (fun k ↦ (k : ℝ) ^ δ) ≤
        (K : ℝ) ^ δ +
          Finset.sum (Finset.Ico (K + 1) (n + 1)) (fun k ↦ (k : ℝ) ^ δ))
  -- Route correction: keep the source integral comparison explicit before the later double-sum step.
  calc
    (((n : ℝ) ^ (1 + δ) - (K : ℝ) ^ (1 + δ)) / (1 + δ)) =
        ∫ x in (K : ℝ)..(n : ℝ), x ^ δ := by
          rw [hIntegral]
    _ ≤ Finset.sum (Finset.Ico K n) (fun k ↦ (((k + 1 : ℕ) : ℝ) ^ δ)) := hPartitionLe
    _ = Finset.sum (Finset.Ico (K + 1) (n + 1)) (fun k ↦ (k : ℝ) ^ δ) := hShift
    _ ≤ Finset.sum (Finset.Ico K (n + 1)) (fun k ↦ (k : ℝ) ^ δ) := hInsert

/-- Helper for Lemma 13.15: after commuting the finite double sum, the source integral lower bound
gives the pointwise weight estimate needed for each square term. -/
lemma weighted_square_interval_lower_bound
    {a : ℕ → ℝ} {δ : ℝ} (hδ : 0 < δ) {K m : ℕ} (_hm : K ≤ m) :
    Finset.sum (Finset.Ico K (m + 1))
      (fun n ↦
        ((((n : ℝ) ^ (1 + δ) - (K : ℝ) ^ (1 + δ)) / (1 + δ)) * (a n) ^ 2)) ≤
      Finset.sum (Finset.Ico K (m + 1))
        (fun n ↦ (a n) ^ 2 * Finset.sum (Finset.Ico K (n + 1)) (fun k ↦ (k : ℝ) ^ δ)) := by
  -- Apply the source interval lower bound termwise after multiplying by the nonnegative square.
  refine Finset.sum_le_sum ?_
  intro n hn
  rcases Finset.mem_Ico.mp hn with ⟨hKn, _⟩
  have hsquare : 0 ≤ (a n) ^ 2 := sq_nonneg _
  have hbase :=
    rpow_sum_Ico_lower_bound (δ := δ) hδ (K := K) (n := n) hKn
  simpa [mul_comm, mul_left_comm, mul_assoc] using
    (mul_le_mul_of_nonneg_right hbase hsquare)

/-- Helper for Lemma 13.15: the commuted source double sum controls the weighted square partial sum
up to the single `K^(1+δ)` correction term. -/
lemma weighted_square_partial_sum_le_double_sum_add_correction
    {a : ℕ → ℝ} {δ : ℝ} (hδ : 0 < δ) {K m : ℕ} (hm : K ≤ m) :
    Finset.sum (Finset.Ico K (m + 1)) (fun n ↦ (n : ℝ) ^ (1 + δ) * (a n) ^ 2) ≤
      (1 + δ) *
          (Finset.sum (Finset.Ico K (m + 1))
            (fun n ↦ (a n) ^ 2 * Finset.sum (Finset.Ico K (n + 1)) (fun k ↦ (k : ℝ) ^ δ))) +
        (K : ℝ) ^ (1 + δ) *
          Finset.sum (Finset.Ico K (m + 1)) (fun n ↦ (a n) ^ 2) := by
  have hOnePlusδ_pos : 0 < 1 + δ := by
    linarith
  have hScaled' :
      Finset.sum (Finset.Ico K (m + 1))
        (fun n ↦ (((n : ℝ) ^ (1 + δ) - (K : ℝ) ^ (1 + δ)) * (a n) ^ 2)) ≤
        (1 + δ) *
          Finset.sum (Finset.Ico K (m + 1))
            (fun n ↦ (a n) ^ 2 * Finset.sum (Finset.Ico K (n + 1)) (fun k ↦ (k : ℝ) ^ δ)) := by
    -- Upgrade the interval estimate by multiplying pointwise by `1 + δ`.
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum ?_
    intro n hn
    rcases Finset.mem_Ico.mp hn with ⟨hKn, _⟩
    have hsquare : 0 ≤ (a n) ^ 2 := sq_nonneg _
    have hbase :=
      rpow_sum_Ico_lower_bound (δ := δ) hδ (K := K) (n := n) hKn
    have hscaled_base :
        (n : ℝ) ^ (1 + δ) - (K : ℝ) ^ (1 + δ) ≤
          (1 + δ) * Finset.sum (Finset.Ico K (n + 1)) (fun k ↦ (k : ℝ) ^ δ) := by
      calc
        (n : ℝ) ^ (1 + δ) - (K : ℝ) ^ (1 + δ) =
            (1 + δ) * (((n : ℝ) ^ (1 + δ) - (K : ℝ) ^ (1 + δ)) / (1 + δ)) := by
              field_simp [hOnePlusδ_pos.ne']
        _ ≤ (1 + δ) * Finset.sum (Finset.Ico K (n + 1)) (fun k ↦ (k : ℝ) ^ δ) :=
              mul_le_mul_of_nonneg_left hbase hOnePlusδ_pos.le
    calc
      ((n : ℝ) ^ (1 + δ) - (K : ℝ) ^ (1 + δ)) * (a n) ^ 2 ≤
          ((1 + δ) * Finset.sum (Finset.Ico K (n + 1)) (fun k ↦ (k : ℝ) ^ δ)) * (a n) ^ 2 := by
            simpa [mul_comm, mul_left_comm, mul_assoc] using
              (mul_le_mul_of_nonneg_right hscaled_base hsquare)
      _ = (1 + δ) *
            ((a n) ^ 2 * Finset.sum (Finset.Ico K (n + 1)) (fun k ↦ (k : ℝ) ^ δ)) := by
            ring
  have hDecomp :
      Finset.sum (Finset.Ico K (m + 1)) (fun n ↦ (n : ℝ) ^ (1 + δ) * (a n) ^ 2) =
        Finset.sum (Finset.Ico K (m + 1))
          (fun n ↦ (((n : ℝ) ^ (1 + δ) - (K : ℝ) ^ (1 + δ)) * (a n) ^ 2)) +
          (K : ℝ) ^ (1 + δ) *
            Finset.sum (Finset.Ico K (m + 1)) (fun n ↦ (a n) ^ 2) := by
    -- Split off the constant correction term exactly as in the source proof.
    calc
      Finset.sum (Finset.Ico K (m + 1)) (fun n ↦ (n : ℝ) ^ (1 + δ) * (a n) ^ 2) =
          Finset.sum (Finset.Ico K (m + 1))
            (fun n ↦
              (((n : ℝ) ^ (1 + δ) - (K : ℝ) ^ (1 + δ)) * (a n) ^ 2) +
                ((K : ℝ) ^ (1 + δ) * (a n) ^ 2)) := by
            refine Finset.sum_congr rfl ?_
            intro n hn
            ring
      _ =
          Finset.sum (Finset.Ico K (m + 1))
            (fun n ↦ (((n : ℝ) ^ (1 + δ) - (K : ℝ) ^ (1 + δ)) * (a n) ^ 2)) +
            Finset.sum (Finset.Ico K (m + 1))
              (fun n ↦ (K : ℝ) ^ (1 + δ) * (a n) ^ 2) := by
            rw [Finset.sum_add_distrib]
      _ =
          Finset.sum (Finset.Ico K (m + 1))
            (fun n ↦ (((n : ℝ) ^ (1 + δ) - (K : ℝ) ^ (1 + δ)) * (a n) ^ 2)) +
            (K : ℝ) ^ (1 + δ) *
              Finset.sum (Finset.Ico K (m + 1)) (fun n ↦ (a n) ^ 2) := by
            rw [Finset.mul_sum]
  -- Combine the normalized lower-bound block with the explicit correction term.
  rw [hDecomp]
  exact add_le_add hScaled' le_rfl

/-- Helper for Lemma 13.15: the finite source double sum is dominated by the inverse-power block
coming from the eventual square-tail estimate. -/
lemma double_sum_upper_bound_of_ennreal_tail_decay
    {a : ℕ → ℝ} {δ : ℝ} (hδ : 0 < δ) {K : ℕ} (hK : 1 ≤ K)
    (hTail :
      ∀ k ≥ K,
        ∑' n : ℕ, ENNReal.ofReal ((a (n + k)) ^ 2) <
          ENNReal.ofReal ((k : ℝ) ^ (-(1 + 2 * δ)))) :
    ∀ m ≥ K,
      Finset.sum (Finset.Ico K (m + 1))
        (fun k ↦ (k : ℝ) ^ δ * Finset.sum (Finset.Ico k (m + 1)) (fun n ↦ (a n) ^ 2)) ≤
        Finset.sum (Finset.Ico K (m + 1)) (fun k ↦ (k : ℝ) ^ (-(1 + δ))) := by
  intro m hm
  refine Finset.sum_le_sum ?_
  intro k hk
  rcases Finset.mem_Ico.mp hk with ⟨hkK, _⟩
  have hk_one : 1 ≤ k := le_trans hK hkK
  have hk_pos : 0 < (k : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hk_one)
  have hsummable :
      Summable (fun n : ℕ ↦ (a (n + k)) ^ 2) :=
    summable_shifted_sq_of_ennreal_tail_lt (a := a) (k := k) (r := (k : ℝ) ^ (-(1 + 2 * δ)))
      (hTail k hkK)
  have hfinite_le_tsum :
      Finset.sum (Finset.Ico k (m + 1)) (fun n ↦ (a n) ^ 2) ≤
        ∑' n : ℕ, (a (n + k)) ^ 2 := by
    -- Rewrite the finite square tail as a shifted `range` sum before comparing with the `tsum`.
    rw [Finset.sum_Ico_eq_sum_range]
    simpa [add_comm, add_left_comm, add_assoc] using
      hsummable.sum_le_tsum (Finset.range (m + 1 - k)) (fun n _ ↦ sq_nonneg _)
  have htail_real :
      ∑' n : ℕ, (a (n + k)) ^ 2 < (k : ℝ) ^ (-(1 + 2 * δ)) :=
    real_tail_sq_lt_of_ennreal_tail_sq_lt
      (a := a) (k := k) (r := (k : ℝ) ^ (-(1 + 2 * δ)))
      (Real.rpow_nonneg (Nat.cast_nonneg k) _) (hTail k hkK)
  have hkδ_nonneg : 0 ≤ (k : ℝ) ^ δ := Real.rpow_nonneg (Nat.cast_nonneg k) δ
  -- Multiply the finite-tail estimate by `k^δ` and insert the textbook tail bound.
  calc
    (k : ℝ) ^ δ * Finset.sum (Finset.Ico k (m + 1)) (fun n ↦ (a n) ^ 2) ≤
        (k : ℝ) ^ δ * ∑' n : ℕ, (a (n + k)) ^ 2 :=
      mul_le_mul_of_nonneg_left hfinite_le_tsum hkδ_nonneg
    _ ≤ (k : ℝ) ^ δ * (k : ℝ) ^ (-(1 + 2 * δ)) :=
      mul_le_mul_of_nonneg_left (le_of_lt htail_real) hkδ_nonneg
    _ = (k : ℝ) ^ (-(1 + δ)) := by
      rw [← Real.rpow_add hk_pos]
      congr 1
      ring

/-- Helper for Lemma 13.15: the separate correction block at the left endpoint `K` is uniformly
bounded by the single tail estimate at `k = K`. -/
lemma square_tail_correction_bound_at_K
    {a : ℕ → ℝ} {δ : ℝ} (hδ : 0 < δ) {K : ℕ} (hK : 1 ≤ K)
    (hTail :
      ∀ k ≥ K,
        ∑' n : ℕ, ENNReal.ofReal ((a (n + k)) ^ 2) <
          ENNReal.ofReal ((k : ℝ) ^ (-(1 + 2 * δ)))) :
    ∀ m ≥ K,
      (K : ℝ) ^ (1 + δ) * Finset.sum (Finset.Ico K (m + 1)) (fun n ↦ (a n) ^ 2) ≤
        (K : ℝ) ^ (-δ) := by
  intro m hm
  have hK_pos : 0 < (K : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hK)
  have hsummable :
      Summable (fun n : ℕ ↦ (a (n + K)) ^ 2) :=
    summable_shifted_sq_of_ennreal_tail_lt (a := a) (k := K) (r := (K : ℝ) ^ (-(1 + 2 * δ)))
      (hTail K le_rfl)
  have hfinite_le_tsum :
      Finset.sum (Finset.Ico K (m + 1)) (fun n ↦ (a n) ^ 2) ≤
        ∑' n : ℕ, (a (n + K)) ^ 2 := by
    -- This is the source tail block starting exactly at `K`.
    rw [Finset.sum_Ico_eq_sum_range]
    simpa [add_comm, add_left_comm, add_assoc] using
      hsummable.sum_le_tsum (Finset.range (m + 1 - K)) (fun n _ ↦ sq_nonneg _)
  have htail_real :
      ∑' n : ℕ, (a (n + K)) ^ 2 < (K : ℝ) ^ (-(1 + 2 * δ)) :=
    real_tail_sq_lt_of_ennreal_tail_sq_lt
      (a := a) (k := K) (r := (K : ℝ) ^ (-(1 + 2 * δ)))
      (Real.rpow_nonneg (Nat.cast_nonneg K) _) (hTail K le_rfl)
  have hKpow_nonneg : 0 ≤ (K : ℝ) ^ (1 + δ) :=
    Real.rpow_nonneg (Nat.cast_nonneg K) _
  -- Multiply the `k = K` tail bound by `K^(1+δ)` and simplify the exponents.
  calc
    (K : ℝ) ^ (1 + δ) * Finset.sum (Finset.Ico K (m + 1)) (fun n ↦ (a n) ^ 2) ≤
        (K : ℝ) ^ (1 + δ) * ∑' n : ℕ, (a (n + K)) ^ 2 :=
      mul_le_mul_of_nonneg_left hfinite_le_tsum hKpow_nonneg
    _ ≤ (K : ℝ) ^ (1 + δ) * (K : ℝ) ^ (-(1 + 2 * δ)) :=
      mul_le_mul_of_nonneg_left (le_of_lt htail_real) hKpow_nonneg
    _ = (K : ℝ) ^ (-δ) := by
      rw [← Real.rpow_add hK_pos]
      congr 1
      ring

/-- Helper for Lemma 13.15: the textbook double-sum argument gives a uniform bound on the weighted
square partial sums once the `ENNReal` square tails decay faster than `k ^ (-(1 + 2 δ))`. -/
lemma weighted_square_partial_sums_bounded_of_ennreal_tail_decay
    {a : ℕ → ℝ} {δ : ℝ} (hδ : 0 < δ) {K : ℕ} (hK : 1 ≤ K)
    (hTail :
      ∀ k ≥ K,
        ∑' n : ℕ, ENNReal.ofReal ((a (n + k)) ^ 2) <
          ENNReal.ofReal ((k : ℝ) ^ (-(1 + 2 * δ)))) :
    ∃ C : ℝ, ∀ m ≥ K,
      Finset.sum (Finset.Ico K (m + 1)) (fun n ↦ (n : ℝ) ^ (1 + δ) * (a n) ^ 2) ≤ C := by
  have hOnePlusδ_pos : 0 < 1 + δ := by
    linarith
  have hInvBase : Summable (fun n : ℕ ↦ (((n : ℝ) ^ (1 + δ))⁻¹)) := by
    exact (Real.summable_nat_rpow_inv).2 (by linarith)
  have hInvShift :
      Summable (fun n : ℕ ↦ ((((n + K : ℕ) : ℝ) ^ (1 + δ))⁻¹)) := by
    simpa [add_comm, add_left_comm, add_assoc] using
      (summable_nat_add_iff
        (f := fun n : ℕ ↦ (((n : ℝ) ^ (1 + δ))⁻¹)) K).2 hInvBase
  have hInv :
      Summable (fun n : ℕ ↦ (((n + K : ℕ) : ℝ) ^ (-(1 + δ)))) := by
    exact hInvShift.congr fun n ↦ by
      rw [Real.rpow_neg (by positivity : 0 ≤ (((n + K : ℕ) : ℝ)))]
  refine ⟨(1 + δ) * (∑' n : ℕ, (((n + K : ℕ) : ℝ) ^ (-(1 + δ)))) + (K : ℝ) ^ (-δ), ?_⟩
  intro m hm
  have hComm :
      Finset.sum (Finset.Ico K (m + 1))
        (fun n ↦ (a n) ^ 2 * Finset.sum (Finset.Ico K (n + 1)) (fun k ↦ (k : ℝ) ^ δ)) =
        Finset.sum (Finset.Ico K (m + 1))
          (fun k ↦ (k : ℝ) ^ δ * Finset.sum (Finset.Ico k (m + 1)) (fun n ↦ (a n) ^ 2)) := by
    -- Commute the source double sum into the `k`-first form used for the tail estimate.
    calc
      Finset.sum (Finset.Ico K (m + 1))
          (fun n ↦ (a n) ^ 2 * Finset.sum (Finset.Ico K (n + 1)) (fun k ↦ (k : ℝ) ^ δ)) =
          Finset.sum (Finset.Ico K (m + 1))
            (fun n ↦ ∑ k ∈ Finset.Ico K (n + 1), (k : ℝ) ^ δ * (a n) ^ 2) := by
          refine Finset.sum_congr rfl ?_
          intro n hn
          calc
            (a n) ^ 2 * Finset.sum (Finset.Ico K (n + 1)) (fun k ↦ (k : ℝ) ^ δ) =
                ∑ k ∈ Finset.Ico K (n + 1), (a n) ^ 2 * (k : ℝ) ^ δ := by
                  rw [Finset.mul_sum]
            _ =
                ∑ k ∈ Finset.Ico K (n + 1), (k : ℝ) ^ δ * (a n) ^ 2 := by
                  refine Finset.sum_congr rfl ?_
                  intro k hk
                  ring
      _ =
          Finset.sum (Finset.Ico K (m + 1))
            (fun k ↦ ∑ n ∈ Finset.Ico k (m + 1), (k : ℝ) ^ δ * (a n) ^ 2) := by
          simpa using
            (Finset.sum_Ico_Ico_comm K (m + 1) (fun k n ↦ (k : ℝ) ^ δ * (a n) ^ 2)).symm
      _ =
          Finset.sum (Finset.Ico K (m + 1))
            (fun k ↦ (k : ℝ) ^ δ * Finset.sum (Finset.Ico k (m + 1)) (fun n ↦ (a n) ^ 2)) := by
          refine Finset.sum_congr rfl ?_
          intro k hk
          rw [← Finset.mul_sum]
  have hMainBound :=
    weighted_square_partial_sum_le_double_sum_add_correction
      (a := a) (δ := δ) hδ (K := K) (m := m) hm
  have hDouble :
      Finset.sum (Finset.Ico K (m + 1))
        (fun n ↦ (a n) ^ 2 * Finset.sum (Finset.Ico K (n + 1)) (fun k ↦ (k : ℝ) ^ δ)) ≤
        Finset.sum (Finset.Ico K (m + 1)) (fun k ↦ (k : ℝ) ^ (-(1 + δ))) := by
    rw [hComm]
    exact double_sum_upper_bound_of_ennreal_tail_decay
      (a := a) (δ := δ) hδ hK hTail m hm
  have hCorrection :
      (K : ℝ) ^ (1 + δ) * Finset.sum (Finset.Ico K (m + 1)) (fun n ↦ (a n) ^ 2) ≤
        (K : ℝ) ^ (-δ) :=
    square_tail_correction_bound_at_K (a := a) (δ := δ) hδ hK hTail m hm
  have hInvPartial :
      Finset.sum (Finset.Ico K (m + 1)) (fun k ↦ (k : ℝ) ^ (-(1 + δ))) ≤
        ∑' n : ℕ, (((n + K : ℕ) : ℝ) ^ (-(1 + δ))) := by
    -- Rewrite the finite inverse-power block as a shifted `range` sum before using `sum_le_tsum`.
    rw [Finset.sum_Ico_eq_sum_range]
    simpa [add_comm, add_left_comm, add_assoc] using
      hInv.sum_le_tsum (Finset.range (m + 1 - K))
        (fun n _ ↦ Real.rpow_nonneg (Nat.cast_nonneg (n + K)) _)
  have hScaledDouble :
      (1 + δ) *
          Finset.sum (Finset.Ico K (m + 1))
            (fun n ↦ (a n) ^ 2 * Finset.sum (Finset.Ico K (n + 1)) (fun k ↦ (k : ℝ) ^ δ)) ≤
        (1 + δ) * ∑' n : ℕ, (((n + K : ℕ) : ℝ) ^ (-(1 + δ))) := by
    exact mul_le_mul_of_nonneg_left (hDouble.trans hInvPartial) hOnePlusδ_pos.le
  -- Combine the normalized lower bound with the two source upper bounds.
  calc
    Finset.sum (Finset.Ico K (m + 1)) (fun n ↦ (n : ℝ) ^ (1 + δ) * (a n) ^ 2) ≤
        (1 + δ) *
            Finset.sum (Finset.Ico K (m + 1))
              (fun n ↦ (a n) ^ 2 * Finset.sum (Finset.Ico K (n + 1)) (fun k ↦ (k : ℝ) ^ δ)) +
          (K : ℝ) ^ (1 + δ) * Finset.sum (Finset.Ico K (m + 1)) (fun n ↦ (a n) ^ 2) :=
      hMainBound
    _ ≤ (1 + δ) * ∑' n : ℕ, (((n + K : ℕ) : ℝ) ^ (-(1 + δ))) + (K : ℝ) ^ (-δ) :=
      add_le_add hScaledDouble hCorrection

/-- Helper for Lemma 13.15: the finite shifted Cauchy-Schwarz inequality used in the source
closing step. -/
lemma shifted_finite_cauchy_schwarz_abs_bound
    {a : ℕ → ℝ} {δ : ℝ} (m : ℕ) :
    Finset.sum (Finset.range m) (fun i ↦ |a (i + 1)|) ≤
      Real.sqrt
          (Finset.sum (Finset.range m)
            (fun i ↦ (((i + 1 : ℕ) : ℝ) ^ (1 + δ)) * (a (i + 1)) ^ 2)) *
        Real.sqrt
          (Finset.sum (Finset.range m)
            (fun i ↦ (((i + 1 : ℕ) : ℝ) ^ (-(1 + δ))))) := by
  -- Apply the finite Cauchy-Schwarz inequality in the source normalization.
  have hcs :
      Finset.sum (Finset.range m)
        (fun i ↦
          Real.sqrt ((((i + 1 : ℕ) : ℝ) ^ (1 + δ)) * (a (i + 1)) ^ 2) *
            Real.sqrt (((i + 1 : ℕ) : ℝ) ^ (-(1 + δ)))) ≤
        Real.sqrt
            (Finset.sum (Finset.range m)
              (fun i ↦ (((i + 1 : ℕ) : ℝ) ^ (1 + δ)) * (a (i + 1)) ^ 2)) *
          Real.sqrt
            (Finset.sum (Finset.range m)
              (fun i ↦ (((i + 1 : ℕ) : ℝ) ^ (-(1 + δ))))) := by
    simpa using
      Real.sum_sqrt_mul_sqrt_le
      (s := Finset.range m)
      (f := fun i ↦ (((i + 1 : ℕ) : ℝ) ^ (1 + δ)) * (a (i + 1)) ^ 2)
      (g := fun i ↦ (((i + 1 : ℕ) : ℝ) ^ (-(1 + δ))))
      (fun i ↦ by positivity)
      (fun i ↦ by positivity)
  -- Normalize the left-hand side termwise to recover `|a (i + 1)|`.
  have hleft :
      Finset.sum (Finset.range m)
        (fun i ↦
          Real.sqrt ((((i + 1 : ℕ) : ℝ) ^ (1 + δ)) * (a (i + 1)) ^ 2) *
            Real.sqrt (((i + 1 : ℕ) : ℝ) ^ (-(1 + δ)))) =
        Finset.sum (Finset.range m) (fun i ↦ |a (i + 1)|) := by
    refine Finset.sum_congr rfl ?_
    intro i hi
    have hbase_pos : 0 < (((i + 1 : ℕ) : ℝ)) := by positivity
    have hweight_nonneg :
        0 ≤ (((i + 1 : ℕ) : ℝ) ^ (1 + δ)) * (a (i + 1)) ^ 2 := by positivity
    have hcancel :
        (((i + 1 : ℕ) : ℝ) ^ (1 + δ)) * (((i + 1 : ℕ) : ℝ) ^ (-(1 + δ))) = 1 := by
      have hsum : (1 + δ) + (-(1 + δ)) = 0 := by
        ring
      rw [← Real.rpow_add hbase_pos, hsum, Real.rpow_zero]
    calc
      Real.sqrt ((((i + 1 : ℕ) : ℝ) ^ (1 + δ)) * (a (i + 1)) ^ 2) *
          Real.sqrt (((i + 1 : ℕ) : ℝ) ^ (-(1 + δ))) =
          Real.sqrt
            ((((i + 1 : ℕ) : ℝ) ^ (1 + δ) * (a (i + 1)) ^ 2) *
              (((i + 1 : ℕ) : ℝ) ^ (-(1 + δ)))) := by
            rw [Real.sqrt_mul hweight_nonneg]
      _ = Real.sqrt ((a (i + 1)) ^ 2 * 1) := by
            have hreassoc :
                ((((i + 1 : ℕ) : ℝ) ^ (1 + δ) * (a (i + 1)) ^ 2) *
                    (((i + 1 : ℕ) : ℝ) ^ (-(1 + δ)))) =
                  (a (i + 1)) ^ 2 *
                    ((((i + 1 : ℕ) : ℝ) ^ (1 + δ)) *
                      (((i + 1 : ℕ) : ℝ) ^ (-(1 + δ)))) := by
              ac_rfl
            rw [hreassoc, hcancel]
      _ = |a (i + 1)| := by rw [mul_one, Real.sqrt_sq_eq_abs]
  rw [hleft] at hcs
  exact hcs

/-- Helper for Lemma 13.15: summability of the weighted square series implies absolute
summability via the finite Cauchy-Schwarz argument from the source proof. -/
lemma summable_abs_of_summable_weighted_sq
    {a : ℕ → ℝ} {δ : ℝ} (hδ : 0 < δ)
    (hWeighted : Summable (fun n : ℕ ↦ (n : ℝ) ^ (1 + δ) * (a n) ^ 2)) :
    Summable (fun n ↦ |a n|) := by
  -- Shift by `1` so that the inverse-power factor never sees the singular index `0`.
  have hWeightedShift :
      Summable
        (fun n : ℕ ↦ (((n + 1 : ℕ) : ℝ) ^ (1 + δ)) * (a (n + 1)) ^ 2) := by
    simpa using
      (summable_nat_add_iff
        (f := fun n : ℕ ↦ (n : ℝ) ^ (1 + δ) * (a n) ^ 2) 1).2 hWeighted
  have hInv :
      Summable (fun n : ℕ ↦ (((n + 1 : ℕ) : ℝ) ^ (-(1 + δ)))) := by
    have hInvBase : Summable (fun n : ℕ ↦ (((n : ℝ) ^ (1 + δ))⁻¹)) := by
      exact (Real.summable_nat_rpow_inv).2 (by linarith)
    have hInvShift :
        Summable (fun n : ℕ ↦ ((((n + 1 : ℕ) : ℝ) ^ (1 + δ))⁻¹)) := by
      simpa using
        (summable_nat_add_iff
          (f := fun n : ℕ ↦ (((n : ℝ) ^ (1 + δ))⁻¹)) 1).2 hInvBase
    exact hInvShift.congr fun n ↦ by
      rw [Real.rpow_neg (by positivity : 0 ≤ (((n + 1 : ℕ) : ℝ)))]
  -- Bound every shifted absolute partial sum by the product of the two convergent `tsum`s.
  have hShiftedAbs :
      Summable (fun n : ℕ ↦ |a (n + 1)|) := by
    refine summable_of_sum_range_le
      (c :=
        Real.sqrt
            (∑' n : ℕ, (((n + 1 : ℕ) : ℝ) ^ (1 + δ)) * (a (n + 1)) ^ 2) *
          Real.sqrt
            (∑' n : ℕ, (((n + 1 : ℕ) : ℝ) ^ (-(1 + δ)))))
      (fun n ↦ abs_nonneg _) ?_
    intro m
    calc
      Finset.sum (Finset.range m) (fun i ↦ |a (i + 1)|) ≤
          Real.sqrt
              (Finset.sum (Finset.range m)
                (fun i ↦ (((i + 1 : ℕ) : ℝ) ^ (1 + δ)) * (a (i + 1)) ^ 2)) *
            Real.sqrt
              (Finset.sum (Finset.range m)
                (fun i ↦ (((i + 1 : ℕ) : ℝ) ^ (-(1 + δ))))) :=
        shifted_finite_cauchy_schwarz_abs_bound (a := a) (δ := δ) m
      _ ≤
          Real.sqrt
              (∑' n : ℕ, (((n + 1 : ℕ) : ℝ) ^ (1 + δ)) * (a (n + 1)) ^ 2) *
            Real.sqrt
              (∑' n : ℕ, (((n + 1 : ℕ) : ℝ) ^ (-(1 + δ)))) := by
        refine mul_le_mul ?_ ?_ (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
        · exact Real.sqrt_le_sqrt <|
            hWeightedShift.sum_le_tsum
              (Finset.range m) (fun n _ ↦ by positivity)
        · exact Real.sqrt_le_sqrt <|
            hInv.sum_le_tsum
              (Finset.range m) (fun n _ ↦ by positivity)
  -- Unshift the summable tail to recover the original absolute-value series.
  simpa [add_comm] using
    (summable_nat_add_iff (f := fun n : ℕ ↦ |a n|) 1).1 hShiftedAbs

/-- Helper for Lemma 13.15: the textbook weighted double-sum argument turns eventual decay of the
square tails into summability of `∑ |a n|`. -/
lemma summable_abs_of_eventually_sq_tail_decay
    {a : ℕ → ℝ} {δ : ℝ} (hδ : 0 < δ) {K : ℕ} (hK : 1 ≤ K)
    (hTail :
      ∀ k ≥ K,
        ∑' n : ℕ, ENNReal.ofReal ((a (n + k)) ^ 2) <
          ENNReal.ofReal ((k : ℝ) ^ (-(1 + 2 * δ)))) :
    Summable (fun n ↦ |a n|) := by
  -- Route correction: the remaining source-faithful blocker is the weighted double-sum bound,
  -- so this wrapper now only converts that bound into summability of the weighted-square series.
  obtain ⟨C, hC⟩ :=
    weighted_square_partial_sums_bounded_of_ennreal_tail_decay
      (a := a) hδ hK hTail
  let weighted : ℕ → ℝ := fun n ↦ (n : ℝ) ^ (1 + δ) * (a n) ^ 2
  have hWeightedTail : Summable (fun n : ℕ ↦ weighted (n + K)) := by
    refine summable_of_sum_range_le (c := C) (fun n ↦ by
      dsimp [weighted]
      positivity) ?_
    intro m
    calc
      Finset.sum (Finset.range m) (fun i ↦ weighted (i + K)) ≤
          Finset.sum (Finset.range (m + 1)) (fun i ↦ weighted (i + K)) := by
            rw [Finset.sum_range_succ]
            exact le_add_of_nonneg_right (by
              dsimp [weighted]
              positivity)
      _ = Finset.sum (Finset.Ico K (K + m + 1)) weighted := by
            rw [Finset.sum_Ico_eq_sum_range]
            simp [weighted, add_assoc, add_comm, add_left_comm]
      _ ≤ C := by
            simpa [weighted, add_assoc, add_comm, add_left_comm] using
              hC (K + m) (le_add_of_nonneg_right (Nat.zero_le m))
  have hWeighted :
      Summable weighted := (summable_nat_add_iff (f := weighted) K).1 hWeightedTail
  -- Finish with the closing Cauchy-Schwarz lemma that is now proved above.
  exact summable_abs_of_summable_weighted_sq (a := a) hδ hWeighted

/-- Lemma 13.15: if the series of absolute values `∑ |a n|` diverges, then for every `ε > 0`
there are infinitely many positive indices `k` whose square tail is at least `k ^ (-(1 + ε))`.
The tail of squares is expressed via the canonical nonnegative `ENNReal` series. -/
-- Proof sketch: argue by contradiction. If all sufficiently large square tails were strictly below
-- `k ^ (-(1 + ε))`, then a Cauchy-Schwarz estimate would reduce the convergence of `∑ |a n|` to
-- the convergence of `∑ n ^ (1 + ε) * a n^2`. Reindex the double sum of weighted square tails,
-- bound the inner weights below by an integral, and conclude that `∑ |a n|` is summable, a
-- contradiction.
theorem tail_sq_ge_rpow_neg_infinitely_often_of_not_summable_abs
    {a : ℕ → ℝ} (ha : ¬ Summable (fun n ↦ |a n|)) {ε : ℝ} (hε : 0 < ε) :
    Set.Infinite
      {k : ℕ |
        0 < k ∧
          ENNReal.ofReal ((k : ℝ) ^ (-(1 + ε))) ≤
            ∑' n : ℕ, ENNReal.ofReal ((a (n + k)) ^ 2)} := by
  classical
  -- Reduce the infinite-set claim to the negated eventual strict upper bound on large tails.
  by_contra hfinite
  obtain ⟨K, hK, hTailENN⟩ :=
    eventually_tail_sq_lt_of_not_infinite (a := a) (ε := ε) hfinite
  let δ : ℝ := ε / 2
  have hδ : 0 < δ := by
    -- Halving the exponent matches the source proof's `1 + 2 δ` notation.
    dsimp [δ]
    linarith
  have hTwoδ : 2 * δ = ε := by
    dsimp [δ]
    ring
  have hSummableAbs : Summable (fun n ↦ |a n|) := by
    -- Invoke the source proof's weighted double-sum argument at exponent `δ = ε / 2`.
    refine summable_abs_of_eventually_sq_tail_decay hδ hK ?_
    intro k hk
    simpa [hTwoδ] using hTailENN k hk
  exact ha hSummableAbs

/-- Bridge/view: the square-tail lower bound from Lemma 13.15 holds frequently along `atTop`. -/
theorem tail_sq_ge_rpow_neg_frequently_atTop_of_not_summable_abs
    {a : ℕ → ℝ} (ha : ¬ Summable (fun n ↦ |a n|)) {ε : ℝ} (hε : 0 < ε) :
    ∃ᶠ k : ℕ in Filter.atTop,
      0 < k ∧
        ENNReal.ofReal ((k : ℝ) ^ (-(1 + ε))) ≤
          ∑' n : ℕ, ENNReal.ofReal ((a (n + k)) ^ 2) := by
  rw [Filter.frequently_atTop']
  intro m
  obtain ⟨k, hk, hmk⟩ :=
    (tail_sq_ge_rpow_neg_infinitely_often_of_not_summable_abs ha hε).exists_gt m
  exact ⟨k, hmk, hk⟩
