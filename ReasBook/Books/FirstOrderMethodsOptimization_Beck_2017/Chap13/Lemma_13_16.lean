/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open Filter
open scoped Topology

/- Lemma 13.16 lies in the domain of infinite products of real sequences.
The owner abstraction is mathlib's `HasProd`/`Multipliable` API for infinite products.

Source/core/bridge triage:
- `source-facing`: the textbook partial products `∏ n ∈ Finset.range (m + 1), (1 - b n)`;
- `core/canonical`: mathlib's `range m` partial-product owner used by
  `HasProd.tendsto_prod_nat` and `Multipliable.tendsto_prod_tprod_nat`;
- `bridge/view`: the index shift from `range m` to `range (m + 1)`, together with the
  logarithmic comparison between `∑ b n` and `∑ log (1 - b n)`.

Relevant owner sampling in this domain:
- `HasProd.tendsto_prod_nat`;
- `Multipliable.tendsto_prod_tprod_nat`;
- `Real.multipliable_one_add_of_summable`;
- `Real.multipliable_of_summable_log'`.

Accordingly, the numbered theorem below keeps the textbook `range (m + 1)` surface, while the
`range m` formulation is kept only as a bridge to the canonical infinite-product API. -/

/-- Helper for Lemma 13.16: the finite partial products are bounded above by the exponential of
the negated partial sums. -/
lemma prod_one_sub_le_exp_neg_sum_range
    {b : ℕ → ℝ} (hb_lt_one : ∀ n, b n < 1) (m : ℕ) :
    ∏ n ∈ Finset.range m, (1 - b n) ≤ Real.exp (-∑ n ∈ Finset.range m, b n) := by
  -- Compare each factor with `exp (-b n)` and then collapse the exponential product.
  calc
    ∏ n ∈ Finset.range m, (1 - b n)
        ≤ ∏ n ∈ Finset.range m, Real.exp (-b n) := by
          refine Finset.prod_le_prod ?_ ?_
          · intro n hn
            exact sub_nonneg.mpr (le_of_lt (hb_lt_one n))
          · intro n hn
            simpa only using Real.one_sub_le_exp_neg (b n)
    _ = Real.exp (∑ n ∈ Finset.range m, -b n) := by
      symm
      exact Real.exp_sum (Finset.range m) fun n ↦ -b n
    _ = Real.exp (-∑ n ∈ Finset.range m, b n) := by
      congr 1
      simp

/-- Helper for Lemma 13.16: if `∑ b n` converges with `0 ≤ b n < 1`, then the associated infinite
product `∏' n, (1 - b n)` is nonzero. -/
lemma tprod_one_sub_ne_zero_of_summable
    {b : ℕ → ℝ} (hb_nonneg : ∀ n, 0 ≤ b n) (hb_lt_one : ∀ n, b n < 1)
    (h_summable : Summable b) :
    ∏' n, (1 - b n) ≠ 0 := by
  have h_norm_summable : Summable (fun n ↦ ‖-b n‖) := by
    -- The norm summability input matches `b` because the terms are already nonnegative.
    simpa only [Real.norm_eq_abs, abs_neg, abs_of_nonneg, hb_nonneg] using h_summable
  have h_nonzero : ∀ n, 1 + -b n ≠ 0 := by
    -- Each factor stays strictly positive because `b n < 1`.
    intro n
    linarith [hb_lt_one n]
  -- Rewrite `1 - b n` as `1 + (-b n)` to invoke the standard infinite-product lemma.
  simpa only [sub_eq_add_neg] using
    (tprod_one_add_ne_zero_of_summable (f := fun n ↦ -b n) h_nonzero h_norm_summable)

/-- Helper for Lemma 13.16: summability of `b` prevents the canonical partial products from
converging to `0`. -/
lemma summable_prod_one_sub_not_tendsto_zero_range
    {b : ℕ → ℝ} (hb_nonneg : ∀ n, 0 ≤ b n) (hb_lt_one : ∀ n, b n < 1)
    (h_summable : Summable b) :
    ¬ Tendsto (fun m : ℕ ↦ ∏ n ∈ Finset.range m, (1 - b n)) atTop (𝓝 0) := by
  intro h_tendsto_zero
  have h_multipliable : Multipliable (fun n ↦ 1 - b n) := by
    -- Summability of `b` gives multipliability of `1 + (-b n)`.
    simpa only [sub_eq_add_neg] using Real.multipliable_one_add_of_summable h_summable.neg
  have h_tendsto_tprod :
      Tendsto (fun m : ℕ ↦ ∏ n ∈ Finset.range m, (1 - b n)) atTop
        (𝓝 (∏' n, (1 - b n))) := by
    -- The canonical partial products converge to the infinite product.
    simpa only [sub_eq_add_neg] using h_multipliable.tendsto_prod_tprod_nat
  have h_tprod_ne_zero :
      ∏' n, (1 - b n) ≠ 0 :=
    tprod_one_sub_ne_zero_of_summable hb_nonneg hb_lt_one h_summable
  have h_tprod_eq_zero : ∏' n, (1 - b n) = 0 :=
    tendsto_nhds_unique h_tendsto_tprod h_tendsto_zero
  exact h_tprod_ne_zero h_tprod_eq_zero

/-- Bridge/view form of Lemma 13.16 on mathlib's canonical `range m` partial products. -/
theorem prod_one_sub_tendsto_zero_iff_not_summable_range
    {b : ℕ → ℝ} (hb_nonneg : ∀ n, 0 ≤ b n) (hb_lt_one : ∀ n, b n < 1) :
    Tendsto (fun m : ℕ ↦ ∏ n ∈ Finset.range m, (1 - b n)) atTop (𝓝 0) ↔
      ¬ Summable b := by
  constructor
  · intro h_tendsto h_summable
    -- In the summable case, the canonical infinite product converges to a nonzero limit.
    exact summable_prod_one_sub_not_tendsto_zero_range hb_nonneg hb_lt_one h_summable h_tendsto
  · intro h_not_summable
    have h_exp_tendsto :
        Tendsto (fun m : ℕ ↦ Real.exp (-∑ n ∈ Finset.range m, b n)) atTop (𝓝 0) := by
      -- Nonsummability of a nonnegative series forces its partial sums to diverge to `+∞`.
      have h_sum_tendsto :
          Tendsto (fun m : ℕ ↦ ∑ n ∈ Finset.range m, b n) atTop atTop :=
        (not_summable_iff_tendsto_nat_atTop_of_nonneg hb_nonneg).mp h_not_summable
      -- Exponentiating the negated partial sums gives a comparison sequence tending to `0`.
      simpa only [Function.comp_def] using
        (Real.tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp h_sum_tendsto))
    -- Squeeze the partial products between `0` and the exponential majorant.
    refine squeeze_zero ?_ ?_ h_exp_tendsto
    · intro m
      exact Finset.prod_nonneg fun n _ ↦ sub_nonneg.mpr (le_of_lt (hb_lt_one n))
    · intro m
      exact prod_one_sub_le_exp_neg_sum_range hb_lt_one m

/-- The textbook partial products `∏_{n=0}^m (1 - b n)` are the canonical `range m` partial
products viewed along the shift `m ↦ m + 1`. -/
theorem tendsto_prod_one_sub_range_add_one_iff {b : ℕ → ℝ} :
    Tendsto (fun m : ℕ ↦ ∏ n ∈ Finset.range (m + 1), (1 - b n)) atTop (𝓝 0) ↔
      Tendsto (fun m : ℕ ↦ ∏ n ∈ Finset.range m, (1 - b n)) atTop (𝓝 0) := by
  let p : ℕ → ℝ := fun k ↦ ∏ n ∈ Finset.range k, (1 - b n)
  change Tendsto (fun m : ℕ ↦ p (m + 1)) atTop (𝓝 0) ↔ Tendsto p atTop (𝓝 0)
  simpa only [p] using
    (show Tendsto (fun n : ℕ ↦ p (n + 1)) atTop (𝓝 0) ↔ Tendsto p atTop (𝓝 0) from
      tendsto_add_atTop_iff_nat 1)

/-- Lemma 13.16: for a real sequence with `0 ≤ b n < 1` for every `n`, the textbook partial
products `∏_{n=0}^m (1 - b n)` tend to `0` exactly when the series `∑ b n` diverges. -/
-- Proof sketch: apply the standard logarithmic criterion for infinite products. If `∑ b n`
-- is not summable, then `log (∏_{n < m} (1 - b n)) = ∑_{n < m} log (1 - b n)` is bounded above
-- by `- ∑_{n < m} b n`, forcing the product to tend to `0`. Conversely, if `∑ b n` is summable,
-- then eventually `b n ≤ 1 / 2`, so `log (1 - b n)` is bounded below by a negative multiple of
-- `b n`; hence the partial products stay uniformly away from `0`.
theorem prod_one_sub_tendsto_zero_iff_not_summable
    {b : ℕ → ℝ} (hb_nonneg : ∀ n, 0 ≤ b n) (hb_lt_one : ∀ n, b n < 1) :
    Tendsto (fun m : ℕ ↦ ∏ n ∈ Finset.range (m + 1), (1 - b n)) atTop (𝓝 0) ↔
      ¬ Summable b := by
  rw [tendsto_prod_one_sub_range_add_one_iff]
  exact prod_one_sub_tendsto_zero_iff_not_summable_range hb_nonneg hb_lt_one
