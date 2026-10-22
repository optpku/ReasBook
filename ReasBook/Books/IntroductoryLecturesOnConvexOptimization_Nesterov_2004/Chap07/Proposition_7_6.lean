/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open Asymptotics
open Filter

local notation "DimPair" => ℕ × ℕ

/- Proposition 7.6 lies in the chapter's asymptotic-complexity comparison domain.

Sampled owner-style declarations:
- mathlib `Asymptotics.IsBigO`, the canonical asymptotic owner behind `f =O[l] g`;
- mathlib `Filter.comap`, the canonical way to express the regime where only the first coordinate
  tends to infinity;
- mathlib `Filter.principal`, the canonical way to impose the side condition
  `0 < p < n (n + 1) / 2`.

Best owner abstraction:
- source-facing: the comparison between the gradient-method total complexity bound
  `n^2 p^2 + (1 / 8) n^(5 / 2) (p + n) log n` and the displayed short-step interior-point
  complexity scale `p n^(5 / 2) (p + n) log (n / δ)`;
- core/canonical: `Asymptotics.IsBigO` on the chapter's admissible-dimension filter;
- bridge/view: none beyond the filter owner itself.

Primitive data:
- the admissible dimension regime `0 < p < n (n + 1) / 2` with `n → ∞`;
- an accuracy profile `δ(n, p)`;
- the two displayed complexity profiles being compared.

Derived API:
- the existence of an absolute constant `C > 0` for which the displayed gradient-method
  complexity profile is asymptotically dominated by the displayed short-step interior-point
  complexity scale whenever `δ ≤ C / p`, under the displayed accuracy regime `0 < δ ≤ n`.

The source proposition compares two displayed complexity formulas rather than introducing a new
wrapper notion. This file therefore keeps the canonical filter owner for the admissible regime and
states that comparison directly on mathlib's `=O` surface between the source gradient profile and
the displayed interior-point scale.
-/

/-- The filter expressing statements that hold for all sufficiently large `n` and every positive
`p` satisfying `p < n (n + 1) / 2`. -/
def restrictedDimensionFilter : Filter DimPair :=
  comap Prod.fst atTop ⊓
    principal
      (setOf fun dims : DimPair ↦
        0 < dims.2 ∧ dims.2 < dims.1 * (dims.1 + 1) / 2)

/-- The restricted-dimension filter is nontrivial: for every sufficiently large ambient dimension
`n`, the admissible pair `(n, 1)` lies in the principal side condition once `n ≥ 2`. -/
lemma restrictedDimensionFilter_neBot : NeBot restrictedDimensionFilter := by
  rw [restrictedDimensionFilter]
  refine Filter.inf_principal_neBot_iff.2 ?_
  intro U hU
  rcases Filter.mem_comap.mp hU with ⟨V, hV, hVU⟩
  rcases Filter.mem_atTop_sets.mp hV with ⟨N, hN⟩
  refine ⟨(max N 2, 1), ?_, ?_⟩
  · exact hVU <| by simp [hN (max N 2) (le_max_left N 2)]
  · constructor
    · norm_num
    · have htwo : 2 ≤ max N 2 := le_max_right N 2
      have hthree : 3 ≤ max N 2 + 1 := by omega
      have hmult : 2 * 3 ≤ (max N 2) * (max N 2 + 1) := by
        gcongr
      have htwo_le_div : 2 ≤ (max N 2) * (max N 2 + 1) / 2 := by
        rw [Nat.le_div_iff_mul_le (by decide : 0 < 2)]
        exact le_trans (by norm_num) hmult
      exact lt_of_lt_of_le (by norm_num) htwo_le_div

-- Proof sketch: the principal side condition already enforces `p > 0`.
/-- Helper for Proposition 7.6: the restricted-dimension filter eventually stays in the positive
`p`-regime. -/
lemma restrictedDimensionFilter_eventually_snd_pos :
    ∀ᶠ dims in restrictedDimensionFilter, 0 < dims.2 := by
  -- Unpack the principal component of the filter and read off the first conjunct.
  rw [restrictedDimensionFilter, Filter.eventually_inf_principal]
  exact Filter.Eventually.of_forall fun _dims hmem ↦ hmem.1

-- Proof sketch: if `n = 0`, then the admissible upper bound on `p` becomes `p < 0`, which
-- contradicts the principal side condition `0 < p`.
/-- Helper for Proposition 7.6: the restricted-dimension filter also forces the ambient dimension
`n` to be eventually positive. -/
lemma restrictedDimensionFilter_eventually_fst_pos :
    ∀ᶠ dims in restrictedDimensionFilter, 0 < dims.1 := by
  rw [restrictedDimensionFilter, Filter.eventually_inf_principal]
  refine Filter.Eventually.of_forall fun dims hmem ↦ ?_
  rcases hmem with ⟨hp, hlt⟩
  by_contra hn
  have hz : dims.1 = 0 := Nat.eq_zero_of_not_pos hn
  have hlt_zero : dims.2 < 0 := by
    rwa [hz] at hlt
  exact (Nat.not_lt_zero _ ) hlt_zero

-- The displayed logarithmic scale itself vanishes at the extremal admissible accuracy
-- profile `δ(n, p) = n`; this is why Proposition 7.6 needs the stricter threshold
-- `δ(n, p) ≤ C / p`, not merely the ambient regime `0 < δ(n, p) ≤ n`.
/-- Helper for Proposition 7.6: at the full admissible accuracy `δ(n, p) = n`, the displayed
interior-point comparison scale vanishes eventually. -/
lemma fullAccuracyInteriorPointScale_eventually_zero :
    ∀ᶠ dims in restrictedDimensionFilter,
      (dims.2 : ℝ) * Real.rpow (dims.1 : ℝ) (5 / 2 : ℝ) *
        ((dims.2 : ℝ) + (dims.1 : ℝ)) * Real.log ((dims.1 : ℝ) / (dims.1 : ℝ)) = 0 := by
  -- Once `n > 0`, the ratio `n / n` is exactly `1`, so the logarithm term disappears.
  filter_upwards [restrictedDimensionFilter_eventually_fst_pos] with dims hn
  have hne : (dims.1 : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hn)
  have hdiv : ((dims.1 : ℝ) / (dims.1 : ℝ)) = 1 := div_self hne
  simp [hdiv, Real.log_one]

/-- Helper for Proposition 7.6: the displayed gradient-method complexity profile is eventually
strictly positive on the restricted-dimension filter. -/
lemma displayedGradientProfile_eventually_pos :
    ∀ᶠ dims in restrictedDimensionFilter,
      0 <
        (dims.1 : ℝ) ^ (2 : ℕ) * (dims.2 : ℝ) ^ (2 : ℕ) +
          (1 / (8 : ℝ)) * Real.rpow (dims.1 : ℝ) (5 / 2 : ℝ) *
            ((dims.2 : ℝ) + (dims.1 : ℝ)) * Real.log (dims.1 : ℝ) := by
  -- The leading polynomial term is already strictly positive, while the logarithmic correction is
  -- nonnegative once `n ≥ 1`.
  filter_upwards
    [restrictedDimensionFilter_eventually_fst_pos, restrictedDimensionFilter_eventually_snd_pos]
    with dims hn hp
  have hnr : 0 < (dims.1 : ℝ) := by
    exact_mod_cast hn
  have hpr : 0 < (dims.2 : ℝ) := by
    exact_mod_cast hp
  have hfirst :
      0 < (dims.1 : ℝ) ^ (2 : ℕ) * (dims.2 : ℝ) ^ (2 : ℕ) := by
    positivity
  have hn_one : (1 : ℝ) ≤ (dims.1 : ℝ) := by
    exact_mod_cast (Nat.succ_le_of_lt hn)
  have hlog_nonneg : 0 ≤ Real.log (dims.1 : ℝ) := Real.log_nonneg hn_one
  have hrpow_nonneg : 0 ≤ Real.rpow (dims.1 : ℝ) (5 / 2 : ℝ) := by
    exact Real.rpow_nonneg hnr.le _
  have hsum_nonneg : 0 ≤ (dims.2 : ℝ) + (dims.1 : ℝ) := by
    positivity
  have hprefix_nonneg :
      0 ≤ (1 / (8 : ℝ)) * Real.rpow (dims.1 : ℝ) (5 / 2 : ℝ) * ((dims.2 : ℝ) + (dims.1 : ℝ)) := by
    exact mul_nonneg (mul_nonneg (by positivity) hrpow_nonneg) hsum_nonneg
  have hsecond_nonneg :
      0 ≤
        (1 / (8 : ℝ)) * Real.rpow (dims.1 : ℝ) (5 / 2 : ℝ) *
          ((dims.2 : ℝ) + (dims.1 : ℝ)) * Real.log (dims.1 : ℝ) := by
    exact mul_nonneg hprefix_nonneg hlog_nonneg
  linarith

/-- Helper for Proposition 7.6: the displayed gradient-method complexity profile cannot be
asymptotically dominated by the zero profile on the restricted-dimension filter. -/
lemma displayedGradientProfile_not_isBigO_zero :
    ¬ ((fun dims : DimPair ↦
      (dims.1 : ℝ) ^ (2 : ℕ) * (dims.2 : ℝ) ^ (2 : ℕ) +
        (1 / (8 : ℝ)) * Real.rpow (dims.1 : ℝ) (5 / 2 : ℝ) *
          ((dims.2 : ℝ) + (dims.1 : ℝ)) * Real.log (dims.1 : ℝ)) =O[
            restrictedDimensionFilter] fun _ ↦ (0 : ℝ)) := by
  intro hzero
  have hEventuallyZero :
      (fun dims : DimPair ↦
        (dims.1 : ℝ) ^ (2 : ℕ) * (dims.2 : ℝ) ^ (2 : ℕ) +
          (1 / (8 : ℝ)) * Real.rpow (dims.1 : ℝ) (5 / 2 : ℝ) *
            ((dims.2 : ℝ) + (dims.1 : ℝ)) * Real.log (dims.1 : ℝ)) =ᶠ[
              restrictedDimensionFilter] fun _ ↦ (0 : ℝ) := by
    exact isBigO_zero_right_iff.mp hzero
  -- The eventual positivity contradicts the eventual equality to `0`.
  have hFalse : ∀ᶠ dims in restrictedDimensionFilter, False := by
    filter_upwards [hEventuallyZero, displayedGradientProfile_eventually_pos] with dims hEq hPos
    rw [hEq] at hPos
    exact (lt_irrefl (0 : ℝ)) hPos
  exact restrictedDimensionFilter_neBot.ne (Filter.eventually_false_iff_eq_bot.mp hFalse)

/-- Helper for Proposition 7.6: specializing the interior-point scale to the extremal admissible
accuracy `δ(n, p) = n` turns the comparison into an impossible `O(0)` claim for the displayed
gradient profile. -/
lemma displayedGradientProfile_not_isBigO_fullAccuracyInteriorPointScale :
    ¬ ((fun dims : DimPair ↦
      (dims.1 : ℝ) ^ (2 : ℕ) * (dims.2 : ℝ) ^ (2 : ℕ) +
        (1 / (8 : ℝ)) * Real.rpow (dims.1 : ℝ) (5 / 2 : ℝ) *
          ((dims.2 : ℝ) + (dims.1 : ℝ)) * Real.log (dims.1 : ℝ)) =O[
            restrictedDimensionFilter]
      (fun dims ↦
        (dims.2 : ℝ) * Real.rpow (dims.1 : ℝ) (5 / 2 : ℝ) *
          ((dims.2 : ℝ) + (dims.1 : ℝ)) * Real.log ((dims.1 : ℝ) / (dims.1 : ℝ)))) := by
  intro hcomparison
  have hzeroScale :
      (fun dims ↦
        (dims.2 : ℝ) * Real.rpow (dims.1 : ℝ) (5 / 2 : ℝ) *
          ((dims.2 : ℝ) + (dims.1 : ℝ)) * Real.log ((dims.1 : ℝ) / (dims.1 : ℝ))) =ᶠ[
            restrictedDimensionFilter] fun _ ↦ (0 : ℝ) := by
    exact fullAccuracyInteriorPointScale_eventually_zero
  have hzero :
      (fun dims : DimPair ↦
        (dims.1 : ℝ) ^ (2 : ℕ) * (dims.2 : ℝ) ^ (2 : ℕ) +
          (1 / (8 : ℝ)) * Real.rpow (dims.1 : ℝ) (5 / 2 : ℝ) *
            ((dims.2 : ℝ) + (dims.1 : ℝ)) * Real.log (dims.1 : ℝ)) =O[
              restrictedDimensionFilter] fun _ ↦ (0 : ℝ) :=
    hcomparison.trans_eventuallyEq hzeroScale
  exact displayedGradientProfile_not_isBigO_zero hzero

-- Proof sketch: the `comap Prod.fst atTop` component already forces `n` to eventually exceed any
-- fixed bound, so in particular it eventually enforces `2 ≤ n`.
/-- Helper for Proposition 7.6: the restricted-dimension filter eventually stays in the regime
`2 ≤ n`. -/
lemma restrictedDimensionFilter_eventually_fst_ge_two :
    ∀ᶠ dims in restrictedDimensionFilter, 2 ≤ dims.1 := by
  rw [restrictedDimensionFilter, Filter.eventually_inf_principal]
  have hcomap : ∀ᶠ dims : DimPair in comap Prod.fst atTop, 2 ≤ dims.1 := by
    refine Filter.mem_comap.2 ?_
    refine ⟨{n : ℕ | 2 ≤ n}, Filter.mem_atTop_sets.2 ?_, ?_⟩
    · exact ⟨2, fun n hn ↦ hn⟩
    · intro dims hdims
      simpa using hdims
  exact hcomap.mono fun _dims htwo _hAdmissible ↦ htwo

-- Proof sketch: the small-accuracy regime `δ ≤ 1 / p` forces `δ ≤ 1`, hence `n ≤ n / δ`; the
-- logarithm on the interior-point profile is therefore at least `log n`.
/-- Helper for Proposition 7.6: under the eventual upper threshold `δ ≤ 1 / p`, the logarithm in
the interior-point profile eventually dominates the source logarithm `log n`. -/
lemma interiorPointLog_eventually_ge_sourceLog
    (δ : DimPair → ℝ)
    (hδ_pos : ∀ᶠ dims in restrictedDimensionFilter, 0 < δ dims)
    (hδ_small : ∀ᶠ dims in restrictedDimensionFilter, δ dims ≤ 1 / (dims.2 : ℝ)) :
    ∀ᶠ dims in restrictedDimensionFilter,
      Real.log (dims.1 : ℝ) ≤ Real.log ((dims.1 : ℝ) / δ dims) := by
  filter_upwards
    [restrictedDimensionFilter_eventually_fst_pos, restrictedDimensionFilter_eventually_snd_pos,
      hδ_pos, hδ_small] with dims hn hp hδpos hδsmall
  have hnr : 0 < (dims.1 : ℝ) := by
    exact_mod_cast hn
  have hpr : 0 < (dims.2 : ℝ) := by
    exact_mod_cast hp
  have hp_one : (1 : ℝ) ≤ (dims.2 : ℝ) := by
    exact_mod_cast (Nat.succ_le_of_lt hp)
  have h_inv_le_one : 1 / (dims.2 : ℝ) ≤ 1 := by
    rw [div_le_iff₀ hpr]
    simpa using hp_one
  have hδ_le_one : δ dims ≤ 1 := le_trans hδsmall h_inv_le_one
  have hratio_ge_n : (dims.1 : ℝ) ≤ (dims.1 : ℝ) / δ dims := by
    refine (le_div_iff₀ hδpos).2 ?_
    nlinarith
  -- Compare the two positive logarithm arguments after enlarging `n` to `n / δ`.
  exact Real.log_le_log hnr hratio_ge_n

-- Proof sketch: once `n ≥ 2`, the exponent `5 / 2` dominates the polynomial power `2`, and the
-- lower bound `log 2 ≤ log (n / δ)` lets the interior-point logarithm absorb the polynomial
-- gradient term.
/-- Helper for Proposition 7.6: the polynomial summand of the displayed gradient profile is
eventually absorbed by a fixed multiple of the interior-point scale. -/
lemma gradientPolynomialTerm_eventually_le_scaledInteriorPoint
    (δ : DimPair → ℝ)
    (hδ_pos : ∀ᶠ dims in restrictedDimensionFilter, 0 < δ dims)
    (hδ_small : ∀ᶠ dims in restrictedDimensionFilter, δ dims ≤ 1 / (dims.2 : ℝ)) :
    ∀ᶠ dims in restrictedDimensionFilter,
      (dims.1 : ℝ) ^ (2 : ℕ) * (dims.2 : ℝ) ^ (2 : ℕ) ≤
        (1 / Real.log (2 : ℝ)) *
          ((dims.2 : ℝ) * Real.rpow (dims.1 : ℝ) (5 / 2 : ℝ) *
            ((dims.2 : ℝ) + (dims.1 : ℝ)) * Real.log ((dims.1 : ℝ) / δ dims)) := by
  filter_upwards
    [restrictedDimensionFilter_eventually_fst_ge_two, restrictedDimensionFilter_eventually_snd_pos,
      hδ_pos, hδ_small] with dims hn_two hp hδpos hδsmall
  have hnr : 0 < (dims.1 : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < (2 : ℕ)) hn_two)
  have hpr : 0 < (dims.2 : ℝ) := by
    exact_mod_cast hp
  have hp_one : (1 : ℝ) ≤ (dims.2 : ℝ) := by
    exact_mod_cast (Nat.succ_le_of_lt hp)
  have h_inv_le_one : 1 / (dims.2 : ℝ) ≤ 1 := by
    rw [div_le_iff₀ hpr]
    simpa using hp_one
  have hδ_le_one : δ dims ≤ 1 := le_trans hδsmall h_inv_le_one
  have hratio_ge_n : (dims.1 : ℝ) ≤ (dims.1 : ℝ) / δ dims := by
    refine (le_div_iff₀ hδpos).2 ?_
    nlinarith
  have htwo_le_ratio : (2 : ℝ) ≤ (dims.1 : ℝ) / δ dims := by
    exact le_trans (by exact_mod_cast hn_two) hratio_ge_n
  have hlog_two_pos : 0 < Real.log (2 : ℝ) := Real.log_pos one_lt_two
  have hlog_two_le :
      Real.log (2 : ℝ) ≤ Real.log ((dims.1 : ℝ) / δ dims) := by
    exact Real.log_le_log (by norm_num) htwo_le_ratio
  have hlog_factor_ge_one :
      1 ≤ (1 / Real.log (2 : ℝ)) * Real.log ((dims.1 : ℝ) / δ dims) := by
    have hdiv :
        1 ≤ Real.log ((dims.1 : ℝ) / δ dims) / Real.log (2 : ℝ) := by
      rw [one_le_div hlog_two_pos]
      exact hlog_two_le
    simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hdiv
  have hn_one : (1 : ℝ) ≤ (dims.1 : ℝ) := by
    exact_mod_cast (le_trans (by norm_num : 1 ≤ (2 : ℕ)) hn_two)
  have hpow_le :
      (dims.1 : ℝ) ^ (2 : ℕ) ≤ Real.rpow (dims.1 : ℝ) (5 / 2 : ℝ) := by
    calc
      (dims.1 : ℝ) ^ (2 : ℕ) = Real.rpow (dims.1 : ℝ) (2 : ℝ) := by
        exact (Real.rpow_natCast (dims.1 : ℝ) 2).symm
      _ ≤ Real.rpow (dims.1 : ℝ) (5 / 2 : ℝ) := by
        simpa using
          (Real.rpow_le_rpow_of_exponent_le hn_one (show (2 : ℝ) ≤ 5 / 2 by norm_num))
  have hrpow_nonneg : 0 ≤ Real.rpow (dims.1 : ℝ) (5 / 2 : ℝ) := by
    exact Real.rpow_nonneg hnr.le _
  have hsum_nonneg : 0 ≤ (dims.2 : ℝ) + (dims.1 : ℝ) := by
    positivity
  have hp_square_le :
      (dims.2 : ℝ) ^ (2 : ℕ) ≤ (dims.2 : ℝ) * ((dims.2 : ℝ) + (dims.1 : ℝ)) := by
    nlinarith
  have hproduct_le :
      (dims.1 : ℝ) ^ (2 : ℕ) * (dims.2 : ℝ) ^ (2 : ℕ) ≤
        Real.rpow (dims.1 : ℝ) (5 / 2 : ℝ) *
          ((dims.2 : ℝ) * ((dims.2 : ℝ) + (dims.1 : ℝ))) := by
    have hfirst :
        (dims.1 : ℝ) ^ (2 : ℕ) * (dims.2 : ℝ) ^ (2 : ℕ) ≤
          Real.rpow (dims.1 : ℝ) (5 / 2 : ℝ) * (dims.2 : ℝ) ^ (2 : ℕ) := by
      exact mul_le_mul_of_nonneg_right hpow_le (by positivity)
    have hsecond :
        Real.rpow (dims.1 : ℝ) (5 / 2 : ℝ) * (dims.2 : ℝ) ^ (2 : ℕ) ≤
          Real.rpow (dims.1 : ℝ) (5 / 2 : ℝ) *
            ((dims.2 : ℝ) * ((dims.2 : ℝ) + (dims.1 : ℝ))) := by
      exact mul_le_mul_of_nonneg_left hp_square_le hrpow_nonneg
    exact le_trans hfirst hsecond
  have hbase_nonneg :
      0 ≤
        (dims.2 : ℝ) * Real.rpow (dims.1 : ℝ) (5 / 2 : ℝ) *
          ((dims.2 : ℝ) + (dims.1 : ℝ)) := by
    exact mul_nonneg (mul_nonneg hpr.le hrpow_nonneg) hsum_nonneg
  calc
    (dims.1 : ℝ) ^ (2 : ℕ) * (dims.2 : ℝ) ^ (2 : ℕ) ≤
        Real.rpow (dims.1 : ℝ) (5 / 2 : ℝ) *
          ((dims.2 : ℝ) * ((dims.2 : ℝ) + (dims.1 : ℝ))) := hproduct_le
    _ = (dims.2 : ℝ) * Real.rpow (dims.1 : ℝ) (5 / 2 : ℝ) *
          ((dims.2 : ℝ) + (dims.1 : ℝ)) := by ring
    _ ≤ ((dims.2 : ℝ) * Real.rpow (dims.1 : ℝ) (5 / 2 : ℝ) *
          ((dims.2 : ℝ) + (dims.1 : ℝ))) *
        ((1 / Real.log (2 : ℝ)) * Real.log ((dims.1 : ℝ) / δ dims)) := by
      exact le_mul_of_one_le_right hbase_nonneg hlog_factor_ge_one
    _ = (1 / Real.log (2 : ℝ)) *
        ((dims.2 : ℝ) * Real.rpow (dims.1 : ℝ) (5 / 2 : ℝ) *
          ((dims.2 : ℝ) + (dims.1 : ℝ)) * Real.log ((dims.1 : ℝ) / δ dims)) := by
      ring

-- Proof sketch: the second summand already has the correct polynomial weight, so it suffices to
-- replace `log n` by the larger interior-point logarithm and absorb one extra factor of `p ≥ 1`.
/-- Helper for Proposition 7.6: the logarithmic correction summand of the displayed gradient
profile is eventually absorbed by the interior-point scale. -/
lemma gradientLogCorrection_eventually_le_scaledInteriorPoint
    (δ : DimPair → ℝ)
    (hδ_pos : ∀ᶠ dims in restrictedDimensionFilter, 0 < δ dims)
    (hδ_small : ∀ᶠ dims in restrictedDimensionFilter, δ dims ≤ 1 / (dims.2 : ℝ)) :
    ∀ᶠ dims in restrictedDimensionFilter,
      (1 / (8 : ℝ)) * Real.rpow (dims.1 : ℝ) (5 / 2 : ℝ) *
        ((dims.2 : ℝ) + (dims.1 : ℝ)) * Real.log (dims.1 : ℝ) ≤
          (1 / (8 : ℝ)) *
            ((dims.2 : ℝ) * Real.rpow (dims.1 : ℝ) (5 / 2 : ℝ) *
              ((dims.2 : ℝ) + (dims.1 : ℝ)) * Real.log ((dims.1 : ℝ) / δ dims)) := by
  filter_upwards
    [restrictedDimensionFilter_eventually_fst_ge_two, restrictedDimensionFilter_eventually_snd_pos,
      hδ_pos, hδ_small, interiorPointLog_eventually_ge_sourceLog δ hδ_pos hδ_small]
    with dims hn_two hp hδpos hδsmall hlog_le
  have hpr : 0 < (dims.2 : ℝ) := by
    exact_mod_cast hp
  have hp_one : (1 : ℝ) ≤ (dims.2 : ℝ) := by
    exact_mod_cast (Nat.succ_le_of_lt hp)
  have h_inv_le_one : 1 / (dims.2 : ℝ) ≤ 1 := by
    rw [div_le_iff₀ hpr]
    simpa using hp_one
  have hδ_le_one : δ dims ≤ 1 := le_trans hδsmall h_inv_le_one
  have hnr : 0 < (dims.1 : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < (2 : ℕ)) hn_two)
  have hratio_ge_n : (dims.1 : ℝ) ≤ (dims.1 : ℝ) / δ dims := by
    refine (le_div_iff₀ hδpos).2 ?_
    nlinarith
  have htwo_le_ratio : (2 : ℝ) ≤ (dims.1 : ℝ) / δ dims := by
    exact le_trans (by exact_mod_cast hn_two) hratio_ge_n
  have hlog_two_pos : 0 < Real.log (2 : ℝ) := Real.log_pos one_lt_two
  have hlog_ratio_nonneg : 0 ≤ Real.log ((dims.1 : ℝ) / δ dims) := by
    have hlog_two_le :
        Real.log (2 : ℝ) ≤ Real.log ((dims.1 : ℝ) / δ dims) := by
      exact Real.log_le_log (by norm_num) htwo_le_ratio
    exact le_trans (le_of_lt hlog_two_pos) hlog_two_le
  have hscaled_log :
      Real.log (dims.1 : ℝ) ≤ (dims.2 : ℝ) * Real.log ((dims.1 : ℝ) / δ dims) := by
    calc
      Real.log (dims.1 : ℝ) ≤ Real.log ((dims.1 : ℝ) / δ dims) := hlog_le
      _ ≤ (dims.2 : ℝ) * Real.log ((dims.1 : ℝ) / δ dims) := by
        nlinarith
  have hrpow_nonneg : 0 ≤ Real.rpow (dims.1 : ℝ) (5 / 2 : ℝ) := by
    exact Real.rpow_nonneg hnr.le _
  have hsum_nonneg : 0 ≤ (dims.2 : ℝ) + (dims.1 : ℝ) := by
    positivity
  have hbase_nonneg :
      0 ≤
        (1 / (8 : ℝ)) * Real.rpow (dims.1 : ℝ) (5 / 2 : ℝ) *
          ((dims.2 : ℝ) + (dims.1 : ℝ)) := by
    exact mul_nonneg (mul_nonneg (by positivity) hrpow_nonneg) hsum_nonneg
  calc
    (1 / (8 : ℝ)) * Real.rpow (dims.1 : ℝ) (5 / 2 : ℝ) *
        ((dims.2 : ℝ) + (dims.1 : ℝ)) * Real.log (dims.1 : ℝ) ≤
      ((1 / (8 : ℝ)) * Real.rpow (dims.1 : ℝ) (5 / 2 : ℝ) *
        ((dims.2 : ℝ) + (dims.1 : ℝ))) *
          ((dims.2 : ℝ) * Real.log ((dims.1 : ℝ) / δ dims)) := by
      gcongr
    _ = (1 / (8 : ℝ)) *
        ((dims.2 : ℝ) * Real.rpow (dims.1 : ℝ) (5 / 2 : ℝ) *
          ((dims.2 : ℝ) + (dims.1 : ℝ)) * Real.log ((dims.1 : ℝ) / δ dims)) := by
      ring

-- Semantic recall confirmed that `Asymptotics.IsBigO` is the right owner here, and the theorem
-- below keeps the source-displayed complexity comparison on the admissible-dimension filter.
/-- Proposition 7.6 [Chapter7_1.json:40]: along the admissible regime
`0 < p < n (n + 1) / 2` with `n → ∞`, if the accuracy profile `δ(n, p)` satisfies the displayed
regime `0 < δ(n, p) ≤ n`, then there exists an absolute constant `C > 0` such that the eventual
upper threshold `δ(n, p) ≤ C / p` implies that the displayed gradient-method complexity profile
`n^2 p^2 + (1 / 8) n^(5 / 2) (p + n) log n` is asymptotically dominated by the displayed
short-step path-following interior-point scale
`p n^(5 / 2) (p + n) log (n / δ(n, p))`, i.e. whenever the accuracy parameter satisfies
`δ(n, p) = O(1 / p)`.
-/
-- The declaration name is retained for compatibility, although the repaired threshold is the
-- upper bound `δ ≤ C / p`.
theorem gradientMethod_isBigO_interiorPointComplexity_of_const_inv_p_eventually_le_accuracy
    (δ : DimPair → ℝ)
    (hδ_pos : ∀ᶠ dims in restrictedDimensionFilter, 0 < δ dims)
    (hδ_le : ∀ᶠ dims in restrictedDimensionFilter, δ dims ≤ (dims.1 : ℝ)) :
    ∃ C > 0,
      (∀ᶠ dims in restrictedDimensionFilter,
          δ dims ≤ C / (dims.2 : ℝ)) →
        (fun dims : DimPair ↦
          (dims.1 : ℝ) ^ (2 : ℕ) * (dims.2 : ℝ) ^ (2 : ℕ) +
            (1 / (8 : ℝ)) * Real.rpow (dims.1 : ℝ) (5 / 2 : ℝ) *
              ((dims.2 : ℝ) + (dims.1 : ℝ)) * Real.log (dims.1 : ℝ)) =O[
                restrictedDimensionFilter]
          (fun dims ↦
            (dims.2 : ℝ) * Real.rpow (dims.1 : ℝ) (5 / 2 : ℝ) *
              ((dims.2 : ℝ) + (dims.1 : ℝ)) * Real.log ((dims.1 : ℝ) / δ dims)) := by
  -- Route correction: the old lower-threshold route `C / p ≤ δ` fails at full accuracy `δ = n`;
  -- the repaired theorem instead uses the source-faithful upper threshold `δ ≤ C / p`.
  let _ := hδ_le
  refine ⟨1, by norm_num, fun hδ_small ↦ ?_⟩
  refine Asymptotics.IsBigO.of_bound ((1 / Real.log (2 : ℝ)) + 1 / 8) ?_
  filter_upwards
    [restrictedDimensionFilter_eventually_fst_ge_two, restrictedDimensionFilter_eventually_snd_pos,
      hδ_pos, hδ_small, interiorPointLog_eventually_ge_sourceLog δ hδ_pos hδ_small,
      gradientPolynomialTerm_eventually_le_scaledInteriorPoint δ hδ_pos hδ_small,
      gradientLogCorrection_eventually_le_scaledInteriorPoint δ hδ_pos hδ_small]
    with dims hn_two hp hδpos hδsmall hlog_le hpoly hcorr
  have hpr : 0 < (dims.2 : ℝ) := by
    exact_mod_cast hp
  have hnr : 0 < (dims.1 : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < (2 : ℕ)) hn_two)
  have hp_one : (1 : ℝ) ≤ (dims.2 : ℝ) := by
    exact_mod_cast (Nat.succ_le_of_lt hp)
  have h_inv_le_one : 1 / (dims.2 : ℝ) ≤ 1 := by
    rw [div_le_iff₀ hpr]
    simpa using hp_one
  have hδ_le_one : δ dims ≤ 1 := le_trans hδsmall h_inv_le_one
  have hratio_ge_n : (dims.1 : ℝ) ≤ (dims.1 : ℝ) / δ dims := by
    refine (le_div_iff₀ hδpos).2 ?_
    nlinarith
  have htwo_le_ratio : (2 : ℝ) ≤ (dims.1 : ℝ) / δ dims := by
    exact le_trans (by exact_mod_cast hn_two) hratio_ge_n
  have hlog_two_pos : 0 < Real.log (2 : ℝ) := Real.log_pos one_lt_two
  have hlog_two_le :
      Real.log (2 : ℝ) ≤ Real.log ((dims.1 : ℝ) / δ dims) := by
    exact Real.log_le_log (by norm_num) htwo_le_ratio
  have hlog_nonneg : 0 ≤ Real.log (dims.1 : ℝ) := by
    have hn_one : (1 : ℝ) ≤ (dims.1 : ℝ) := by
      exact_mod_cast (le_trans (by norm_num : 1 ≤ (2 : ℕ)) hn_two)
    exact Real.log_nonneg hn_one
  have hrpow_nonneg : 0 ≤ Real.rpow (dims.1 : ℝ) (5 / 2 : ℝ) := by
    exact Real.rpow_nonneg hnr.le _
  have hsum_dims_nonneg : 0 ≤ (dims.2 : ℝ) + (dims.1 : ℝ) := by
    positivity
  have hratio_log_nonneg : 0 ≤ Real.log ((dims.1 : ℝ) / δ dims) := by
    exact le_trans (le_of_lt hlog_two_pos) hlog_two_le
  have htarget_nonneg :
      0 ≤
        (dims.2 : ℝ) * Real.rpow (dims.1 : ℝ) (5 / 2 : ℝ) *
          ((dims.2 : ℝ) + (dims.1 : ℝ)) * Real.log ((dims.1 : ℝ) / δ dims) := by
    exact mul_nonneg (mul_nonneg (mul_nonneg hpr.le hrpow_nonneg) hsum_dims_nonneg)
      hratio_log_nonneg
  have hcorrection_nonneg :
      0 ≤
        (1 / (8 : ℝ)) * Real.rpow (dims.1 : ℝ) (5 / 2 : ℝ) *
          ((dims.2 : ℝ) + (dims.1 : ℝ)) * Real.log (dims.1 : ℝ) := by
    exact mul_nonneg
      (mul_nonneg (mul_nonneg (by positivity) hrpow_nonneg) hsum_dims_nonneg) hlog_nonneg
  have hleft_nonneg :
      0 ≤
        (dims.1 : ℝ) ^ (2 : ℕ) * (dims.2 : ℝ) ^ (2 : ℕ) +
          (1 / (8 : ℝ)) * Real.rpow (dims.1 : ℝ) (5 / 2 : ℝ) *
            ((dims.2 : ℝ) + (dims.1 : ℝ)) * Real.log (dims.1 : ℝ) := by
    have hpoly_nonneg : 0 ≤ (dims.1 : ℝ) ^ (2 : ℕ) * (dims.2 : ℝ) ^ (2 : ℕ) := by
      positivity
    exact add_nonneg hpoly_nonneg hcorrection_nonneg
  -- Add the two summand bounds and then rewrite the eventual inequality into the normed `=O` form.
  have hsum :
      (dims.1 : ℝ) ^ (2 : ℕ) * (dims.2 : ℝ) ^ (2 : ℕ) +
          (1 / (8 : ℝ)) * Real.rpow (dims.1 : ℝ) (5 / 2 : ℝ) *
            ((dims.2 : ℝ) + (dims.1 : ℝ)) * Real.log (dims.1 : ℝ) ≤
        ((1 / Real.log (2 : ℝ)) + 1 / 8) *
          ((dims.2 : ℝ) * Real.rpow (dims.1 : ℝ) (5 / 2 : ℝ) *
            ((dims.2 : ℝ) + (dims.1 : ℝ)) * Real.log ((dims.1 : ℝ) / δ dims)) := by
    calc
      (dims.1 : ℝ) ^ (2 : ℕ) * (dims.2 : ℝ) ^ (2 : ℕ) +
          (1 / (8 : ℝ)) * Real.rpow (dims.1 : ℝ) (5 / 2 : ℝ) *
            ((dims.2 : ℝ) + (dims.1 : ℝ)) * Real.log (dims.1 : ℝ)
        ≤ (1 / Real.log (2 : ℝ)) *
            ((dims.2 : ℝ) * Real.rpow (dims.1 : ℝ) (5 / 2 : ℝ) *
              ((dims.2 : ℝ) + (dims.1 : ℝ)) * Real.log ((dims.1 : ℝ) / δ dims)) +
          (1 / (8 : ℝ)) *
            ((dims.2 : ℝ) * Real.rpow (dims.1 : ℝ) (5 / 2 : ℝ) *
              ((dims.2 : ℝ) + (dims.1 : ℝ)) * Real.log ((dims.1 : ℝ) / δ dims)) := by
        exact add_le_add hpoly hcorr
      _ = ((1 / Real.log (2 : ℝ)) + 1 / 8) *
          ((dims.2 : ℝ) * Real.rpow (dims.1 : ℝ) (5 / 2 : ℝ) *
            ((dims.2 : ℝ) + (dims.1 : ℝ)) * Real.log ((dims.1 : ℝ) / δ dims)) := by
        ring
  -- Rewrite the normed eventual bound back to the pointwise nonnegative inequality we proved.
  rw [Real.norm_of_nonneg hleft_nonneg, Real.norm_of_nonneg htarget_nonneg]
  exact hsum

end
