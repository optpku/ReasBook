/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import ComputationalMethodsInverseProblems_Vogel_2002.Chap07.Prop_7_19.KernelMoment
public import Mathlib.Analysis.Asymptotics.Lemmas
public import Mathlib.Analysis.PSeries
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
public import Mathlib.Analysis.SumIntegralComparisons
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.DistLEIntegral
public import Mathlib.Order.Filter.Prod
public import Mathlib.Topology.NhdsWithin

public section

open scoped Asymptotics KernelMoment.Notation

namespace KernelMoment

open MeasureTheory

/-- Helper for Proposition 7.19: summing over `Finset.Icc 1 n` agrees with summing over
`Finset.range n` after the index shift `k ↦ k + 1`. -/
lemma sum_Icc_one_eq_sumRangeShift {α : Type*} [AddCommMonoid α] (f : ℕ → α) :
    ∀ n : ℕ, ∑ k ∈ Finset.Icc 1 n, f k = ∑ k ∈ Finset.range n, f (k + 1)
  | n => by
      -- Rewrite the closed interval as a half-open interval, then shift it to a range sum.
      rw [← Finset.Ico_add_one_right_eq_Icc]
      rw [Finset.sum_Ico_eq_sum_range]
      simp [Nat.add_comm]

/-- Helper for Proposition 7.19: `S_{p,j}^s(n,h)` is the `range n` partial sum of the
shifted series defining `S_{p,j}^s(∞,h)`. -/
lemma quadratureSum_eq_sumRangeSeries (p : ℝ) (j : ℕ) (s : ℝ) (n : ℕ) (h : ℝ) :
    S_{p, j}^{s}(n, h) =
      ∑ k ∈ Finset.range n, h * integrand p j s (((k + 1 : ℕ) : ℝ) * h) := by
  -- Normalize the finite quadrature sum to the same shifted indexing used by the infinite series.
  rw [quadratureSum_def, Finset.mul_sum, sum_Icc_one_eq_sumRangeShift]

/-- Helper for Proposition 7.19: the source-side decay assumptions with `-1 < s` force `p > 0`. -/
lemma positive_p_of_decay {p s : ℝ} {j : ℕ}
    (hDecay : 0 < (j : ℝ) * p - s - 1) (hsLower : -1 < s) : 0 < p := by
  -- First exclude the degenerate case `j = 0`, which contradicts the two inequalities.
  have hj_nat_ne : j ≠ 0 := by
    intro hj
    subst hj
    norm_num at hDecay
    linarith
  have hj_pos : 0 < (j : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero hj_nat_ne
  -- Then `(j : ℝ) * p` is positive, so dividing by the positive factor `j` yields `p > 0`.
  have hjp_pos : 0 < (j : ℝ) * p := by
    linarith
  have : 0 < ((j : ℝ) * p) / (j : ℝ) := div_pos hjp_pos hj_pos
  simpa [hj_pos.ne'] using this

/-- Helper for Proposition 7.19: in the logarithmic case `s = -1`, the decay assumption again
forces `p > 0`. -/
lemma positive_p_of_negOneDecay {p : ℝ} {j : ℕ} (hDecay : 0 < (j : ℝ) * p) : 0 < p := by
  -- Excluding `j = 0` reduces the claim to the same division argument as above.
  have hj_nat_ne : j ≠ 0 := by
    intro hj
    subst hj
    norm_num at hDecay
  have hj_pos : 0 < (j : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero hj_nat_ne
  have : 0 < ((j : ℝ) * p) / (j : ℝ) := div_pos hDecay hj_pos
  simpa [hj_pos.ne'] using this

/-- Helper for Proposition 7.19: on `u ≥ 1`, the kernel integrand is dominated by the pure power
`u ^ (s - jp)`. -/
lemma integrand_le_rpow_tail {p s u : ℝ} {j : ℕ}
    (hp : 0 < p) (hu : 1 ≤ u) :
    integrand p j s u ≤ u ^ (s - (j : ℝ) * p) := by
  -- The denominator dominates `(u ^ p)^j` because `u ^ p ≥ 1` on `u ≥ 1`.
  have hu_nonneg : 0 ≤ u := le_trans (by norm_num) hu
  have hu_pos : 0 < u := lt_of_lt_of_le zero_lt_one hu
  have hpu_one : 1 ≤ u ^ p := by
    simpa using Real.rpow_le_rpow (show 0 ≤ (1 : ℝ) by norm_num) hu hp.le
  have hpu_nonneg : 0 ≤ u ^ p := Real.rpow_nonneg hu_nonneg p
  have hden_le : (u ^ p) ^ j ≤ (1 + u ^ p) ^ j := by
    exact pow_le_pow_left₀ (by positivity) (by linarith) j
  have hden_pos : 0 < (u ^ p) ^ j := by
    exact pow_pos (Real.rpow_pos_of_pos (lt_of_lt_of_le zero_lt_one hu) p) j
  have hnum_nonneg : 0 ≤ u ^ s := Real.rpow_nonneg hu_nonneg s
  have hdiv :
      u ^ s / (1 + u ^ p) ^ j ≤ u ^ s / (u ^ p) ^ j := by
    exact div_le_div_of_nonneg_left hnum_nonneg hden_pos hden_le
  -- Finally collapse the powers in the denominator into the exponent shift `s - jp`.
  calc
    integrand p j s u = u ^ s / (1 + u ^ p) ^ j := by rw [integrand_def]
    _ ≤ u ^ s / (u ^ p) ^ j := hdiv
    _ = u ^ s / u ^ ((j : ℝ) * p) := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul hu_nonneg]
          congr 1
          ring
    _ = u ^ (s - (j : ℝ) * p) := by
          rw [div_eq_mul_inv, ← Real.rpow_neg hu_nonneg, ← Real.rpow_add hu_pos]
          congr 1

/-- Helper for Proposition 7.19: the kernel integrand is nonnegative on `(0, ∞)`. -/
lemma integrand_nonneg {p s u : ℝ} {j : ℕ} (hu : 0 < u) :
    0 ≤ integrand p j s u := by
  -- Both the real power and the denominator are nonnegative on positive inputs.
  rw [integrand_def]
  refine div_nonneg ?_ ?_
  · exact Real.rpow_nonneg hu.le s
  · exact pow_nonneg (by positivity) j

/-- Helper for Proposition 7.19: on `(0, ∞)` the kernel integrand is bounded above by `u ^ s`
because its denominator is at least `1`. -/
lemma integrand_le_rpow_local {p s u : ℝ} {j : ℕ} (hu : 0 < u) :
    integrand p j s u ≤ u ^ s := by
  -- Drop the denominator using the elementary lower bound `(1 + u^p)^j ≥ 1`.
  rw [integrand_def]
  have hnum_nonneg : 0 ≤ u ^ s := Real.rpow_nonneg hu.le s
  have hden_ge_one : 1 ≤ (1 + u ^ p) ^ j := by
    have hbase : 1 ≤ 1 + u ^ p := by
      linarith [Real.rpow_nonneg hu.le p]
    simpa using
      (pow_le_pow_left₀ (by positivity : 0 ≤ (1 : ℝ)) hbase j : (1 : ℝ) ^ j ≤ (1 + u ^ p) ^ j)
  simpa using div_le_self hnum_nonneg hden_ge_one

/-- Helper for Proposition 7.19: when `s ≤ 0`, the kernel integrand decreases on `(0, ∞)`. -/
lemma integrandAntitoneOn_Ioi_nonpos {p s : ℝ} {j : ℕ}
    (hp : 0 < p) (hsUpper : s ≤ 0) :
    AntitoneOn (integrand p j s) (Set.Ioi 0) := by
  -- The numerator `u^s` is antitone and the denominator `(1 + u^p)^j` is monotone increasing.
  intro u hu v hv huv
  have hnum : v ^ s ≤ u ^ s :=
    (Real.antitoneOn_rpow_Ioi_of_exponent_nonpos hsUpper) hu hv huv
  have hpow : u ^ p ≤ v ^ p :=
    Real.rpow_le_rpow hu.le huv hp.le
  have hden :
      (1 + u ^ p) ^ j ≤ (1 + v ^ p) ^ j := by
    have hbase_nonneg : 0 ≤ 1 + u ^ p := by
      linarith [Real.rpow_nonneg hu.le p]
    exact pow_le_pow_left₀ hbase_nonneg (by linarith [hpow]) j
  have hnum_nonneg : 0 ≤ u ^ s := Real.rpow_nonneg hu.le s
  have hbaseu_pos : 0 < 1 + u ^ p := by
    have hbaseu_ge_one : 1 ≤ 1 + u ^ p := by
      linarith [Real.rpow_nonneg hu.le p]
    exact lt_of_lt_of_le zero_lt_one hbaseu_ge_one
  have hbasev_pos : 0 < 1 + v ^ p := by
    have hbasev_ge_one : 1 ≤ 1 + v ^ p := by
      linarith [Real.rpow_nonneg hv.le p]
    exact lt_of_lt_of_le zero_lt_one hbasev_ge_one
  have hdenu_pos : 0 < (1 + u ^ p) ^ j := pow_pos hbaseu_pos j
  have hdenv_nonneg : 0 ≤ (1 + v ^ p) ^ j := (pow_nonneg hbasev_pos.le j)
  calc
    integrand p j s v = v ^ s / (1 + v ^ p) ^ j := by rw [integrand_def]
    _ ≤ u ^ s / (1 + v ^ p) ^ j := by
          exact div_le_div_of_nonneg_right hnum hdenv_nonneg
    _ ≤ u ^ s / (1 + u ^ p) ^ j := by
          exact div_le_div_of_nonneg_left hnum_nonneg hdenu_pos hden
    _ = integrand p j s u := by rw [integrand_def]

/-- Helper for Proposition 7.19: for `-1 < s ≤ 0` and `jp - s - 1 > 0`, the kernel integrand is
integrable on `(0, ∞)`. -/
lemma integrandIntegrableOn_Ioi_nonpos {p s : ℝ} {j : ℕ}
    (hDecay : 0 < (j : ℝ) * p - s - 1)
    (hp : 0 < p) (hsLower : -1 < s) (_hsUpper : s ≤ 0) :
    IntegrableOn (fun u ↦ integrand p j s u) (Set.Ioi (0 : ℝ)) := by
  -- Split at `u = 1`: near `0` compare against `u^s`, and on the tail compare against
  -- `u^(s - jp)`.
  have ha : s - (j : ℝ) * p < -1 := by
    linarith
  have hlocalRpow : IntegrableOn (fun u : ℝ ↦ u ^ s) (Set.Ioc (0 : ℝ) 1) := by
    rw [integrableOn_Ioc_iff_integrableOn_Ioo]
    exact (intervalIntegral.integrableOn_Ioo_rpow_iff zero_lt_one).2 hsLower
  have hlocal :
      IntegrableOn (fun u ↦ integrand p j s u) (Set.Ioc (0 : ℝ) 1) := by
    -- The denominator only improves integrability on the compact-near-zero piece.
    refine Integrable.mono' hlocalRpow ?_ ?_
    · have hmeas : Measurable (fun u : ℝ ↦ integrand p j s u) := by
        simpa [integrand_def] using
          (by fun_prop : Measurable fun u : ℝ ↦ u ^ s / (1 + u ^ p) ^ j)
      exact hmeas.aestronglyMeasurable
    · filter_upwards [ae_restrict_mem measurableSet_Ioc] with u hu
      rw [Real.norm_eq_abs, abs_of_nonneg (integrand_nonneg hu.1)]
      exact integrand_le_rpow_local hu.1
  have htailRpow :
      IntegrableOn (fun u : ℝ ↦ u ^ (s - (j : ℝ) * p)) (Set.Ioi (1 : ℝ)) :=
    integrableOn_Ioi_rpow_of_lt ha zero_lt_one
  have htail :
      IntegrableOn (fun u ↦ integrand p j s u) (Set.Ioi (1 : ℝ)) := by
    -- On the tail, the exact kernel is dominated by the decaying pure power `u^(s-jp)`.
    refine Integrable.mono' htailRpow ?_ ?_
    · have hmeas : Measurable (fun u : ℝ ↦ integrand p j s u) := by
        simpa [integrand_def] using
          (by fun_prop : Measurable fun u : ℝ ↦ u ^ s / (1 + u ^ p) ^ j)
      exact hmeas.aestronglyMeasurable
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
      have hu_pos : 0 < u := lt_trans zero_lt_one hu
      rw [Real.norm_eq_abs, abs_of_nonneg (integrand_nonneg hu_pos)]
      exact integrand_le_rpow_tail hp hu.le
  -- The two integrable pieces cover `(0, ∞)`.
  simpa [Set.Ioc_union_Ioi_eq_Ioi (show (0 : ℝ) ≤ 1 by norm_num)] using hlocal.union htail

/-- Helper for Proposition 7.19: the pure-power model tail has the expected
`((n : ℝ) * h) ^ (a + 1)` decay. -/
lemma rpowSeriesTail_isBigO {l : Filter (ℕ × ℝ)} {a : ℝ}
    (ha : a < -1)
    (hh : Filter.Tendsto Prod.snd l (nhdsWithin (0 : ℝ) (Set.Ioi 0)))
    (hnh : Filter.Tendsto (fun x ↦ (x.1 : ℝ) * x.2) l Filter.atTop) :
    (fun x ↦
      (∑' k : ℕ, x.2 * (((k + 1 : ℕ) : ℝ) * x.2) ^ a) -
        ∑ k ∈ Finset.range x.1, x.2 * (((k + 1 : ℕ) : ℝ) * x.2) ^ a) =O[l]
      (fun x ↦ ((x.1 : ℝ) * x.2) ^ (a + 1)) := by
  have ha_nonpos : a ≤ 0 := by linarith
  refine Asymptotics.IsBigO.of_bound (|(-1 : ℝ) / (a + 1)|) ?_
  -- Enter the eventual region where both `h > 0` and `n * h ≥ 1`,
  -- so the power comparison is stable.
  filter_upwards
    [hh self_mem_nhdsWithin, hnh.eventually (Filter.eventually_ge_atTop (1 : ℝ))] with
      x hx hxnh
  have hx_pos : 0 < x.2 := by
    simpa using hx
  let f : ℝ → ℝ := fun t ↦ x.2 * (t * x.2) ^ a
  have hx_nonneg : 0 ≤ x.2 := hx_pos.le
  have hxnh_pos : 0 < (x.1 : ℝ) * x.2 := by linarith
  have hanti : AntitoneOn f (Set.Ici (x.1 : ℝ)) := by
    -- The scalar factor `x.2` is nonnegative, and `t ↦ (t * h)^a` is antitone for `a ≤ 0`.
    intro u hu v hv huv
    have huv_mul : u * x.2 ≤ v * x.2 := mul_le_mul_of_nonneg_right huv hx_nonneg
    have hu_pos : 0 < u * x.2 := by
      exact hxnh_pos.trans_le (mul_le_mul_of_nonneg_right hu hx_nonneg)
    have hv_pos : 0 < v * x.2 := by
      exact hxnh_pos.trans_le (mul_le_mul_of_nonneg_right hv hx_nonneg)
    exact mul_le_mul_of_nonneg_left
      ((Real.antitoneOn_rpow_Ioi_of_exponent_nonpos ha_nonpos) hu_pos hv_pos huv_mul) hx_nonneg
  have hintegrable :
      IntegrableOn f (Set.Ioi (x.1 : ℝ)) := by
    -- Change variables from `t` to `t * h` and reuse the standard improper-integral criterion.
    have hcore :
        IntegrableOn (fun t : ℝ ↦ t ^ a) (Set.Ioi ((x.1 : ℝ) * x.2)) :=
      integrableOn_Ioi_rpow_of_lt ha hxnh_pos
    have hscaled :
        IntegrableOn (fun t : ℝ ↦ (t * x.2) ^ a) (Set.Ioi (x.1 : ℝ)) :=
      (integrableOn_Ioi_comp_mul_right_iff (fun t : ℝ ↦ t ^ a) (x.1 : ℝ) hx_pos).2 hcore
    simpa [IntegrableOn, f] using hscaled.const_mul x.2
  have hnonneg : ∀ t ∈ Set.Ioi (x.1 : ℝ), 0 ≤ f t := by
    intro t ht
    have ht_pos : 0 < t * x.2 := by
      exact lt_of_lt_of_le hxnh_pos (mul_le_mul_of_nonneg_right ht.le hx_nonneg)
    exact mul_nonneg hx_nonneg (Real.rpow_nonneg ht_pos.le a)
  have hsummable : Summable (fun n : ℕ ↦ f n) :=
    AntitoneOn.summable_of_integrableOn_Ioi (N := x.1) hanti hintegrable hnonneg
  have hanti' : AntitoneOn f (Set.Ici (((x.1 + 1 : ℕ) : ℝ) - 1)) := by
    simpa using hanti
  have hintegrable' : IntegrableOn f (Set.Ioi (((x.1 + 1 : ℕ) : ℝ) - 1)) := by
    simpa using hintegrable
  have hnonneg' : ∀ t ∈ Set.Ioi (((x.1 + 1 : ℕ) : ℝ) - 1), 0 ≤ f t := by
    simpa using hnonneg
  have hbound :=
    AntitoneOn.abs_tsum_sub_sum_range_le_integral
      (f := f) (N := x.1 + 1) (Nat.succ_le_succ (Nat.zero_le _)) hanti' hintegrable' hnonneg'
  have hbound' :
      |(∑' n : ℕ, f n) - ∑ n ∈ Finset.range (x.1 + 1), f n| ≤ ∫ t in Set.Ioi (x.1 : ℝ), f t := by
    simpa using hbound
  have htsum :
      ∑' n : ℕ, f n = ∑' n : ℕ, x.2 * (((n + 1 : ℕ) : ℝ) * x.2) ^ a := by
    -- The `n = 0` term vanishes because `a ≠ 0`.
    rw [hsummable.tsum_eq_zero_add]
    simp [f, Real.zero_rpow (by linarith : a ≠ 0)]
  have hsum :
      ∑ n ∈ Finset.range (x.1 + 1), f n =
        ∑ n ∈ Finset.range x.1, x.2 * (((n + 1 : ℕ) : ℝ) * x.2) ^ a := by
    -- The same zero-term removal works for the finite partial sum.
    rw [Finset.sum_range_succ']
    simp [f, Real.zero_rpow (by linarith : a ≠ 0)]
  have hcalc :
      ‖(∑' k : ℕ, x.2 * (((k + 1 : ℕ) : ℝ) * x.2) ^ a) -
          ∑ k ∈ Finset.range x.1, x.2 * (((k + 1 : ℕ) : ℝ) * x.2) ^ a‖
        ≤ ‖∫ t in Set.Ioi (x.1 : ℝ), f t‖ := by
    -- Rewrite the left-hand side to the exact pure-power tail controlled by the integral test.
    rw [← htsum, ← hsum]
    have hIntegral_nonneg : 0 ≤ ∫ t in Set.Ioi (x.1 : ℝ), f t :=
      setIntegral_nonneg measurableSet_Ioi hnonneg
    simpa [Real.norm_eq_abs, abs_of_nonneg hIntegral_nonneg] using hbound'
  have hintegral :
      ∫ t in Set.Ioi (x.1 : ℝ), f t = -(((x.1 : ℝ) * x.2) ^ (a + 1)) / (a + 1) := by
    -- The multiplicative change of variables turns the model tail into the standard power integral.
    calc
      ∫ t in Set.Ioi (x.1 : ℝ), f t
          = x.2 * ∫ t in Set.Ioi (x.1 : ℝ), (t * x.2) ^ a := by
              simp [f, integral_const_mul]
      _ = x.2 * (x.2⁻¹ * ∫ t in Set.Ioi ((x.1 : ℝ) * x.2), t ^ a) := by
              rw [MeasureTheory.integral_comp_mul_right_Ioi (fun t : ℝ ↦ t ^ a) (x.1 : ℝ) hx_pos]
              simp [smul_eq_mul]
      _ = ∫ t in Set.Ioi ((x.1 : ℝ) * x.2), t ^ a := by
              field_simp [hx_pos.ne']
      _ = -(((x.1 : ℝ) * x.2) ^ (a + 1)) / (a + 1) := by
              rw [integral_Ioi_rpow_of_lt ha hxnh_pos]
  -- The explicit integral formula is already a fixed constant times the target comparison term.
  have hnorm :
      ‖∫ t in Set.Ioi (x.1 : ℝ), f t‖ =
        |(-1 : ℝ) / (a + 1)| * ‖((x.1 : ℝ) * x.2) ^ (a + 1)‖ := by
    rw [hintegral]
    have hmul :
        -(((x.1 : ℝ) * x.2) ^ (a + 1)) / (a + 1) =
          (((-1 : ℝ) / (a + 1)) * (((x.1 : ℝ) * x.2) ^ (a + 1))) := by
      ring
    rw [hmul, norm_mul, Real.norm_eq_abs]
  calc
    ‖((∑' k : ℕ, x.2 * (((k + 1 : ℕ) : ℝ) * x.2) ^ a) -
        ∑ k ∈ Finset.range x.1, x.2 * (((k + 1 : ℕ) : ℝ) * x.2) ^ a)‖
        ≤ ‖∫ t in Set.Ioi (x.1 : ℝ), f t‖ := hcalc
    _ = |(-1 : ℝ) / (a + 1)| * ‖((x.1 : ℝ) * x.2) ^ (a + 1)‖ := hnorm

/-- Helper for Proposition 7.19: the finite-to-infinite tail remainder is controlled by the
power tail `(nh)^(s - jp + 1)`. -/
lemma quadratureTail_isBigO_power {l : Filter (ℕ × ℝ)} {p s : ℝ} {j : ℕ}
    (hDecay : 0 < (j : ℝ) * p - s - 1)
    (hp : 0 < p)
    (_hn : Filter.Tendsto Prod.fst l Filter.atTop)
    (hh : Filter.Tendsto Prod.snd l (nhdsWithin (0 : ℝ) (Set.Ioi 0)))
    (hnh : Filter.Tendsto (fun x ↦ (x.1 : ℝ) * x.2) l Filter.atTop) :
    (fun x ↦ S_{p, j}^{s}(x.1, x.2) - S_{p, j}^{s}(∞, x.2)) =O[l]
      (fun x ↦ ((x.1 : ℝ) * x.2) ^ (s - (j : ℝ) * p + 1)) := by
  -- Route correction: reduce the exact kernel tail to a dominated pure-power tail first, then
  -- invoke the explicit `rpow` tail estimate instead of mixing both tasks in one proof.
  let a : ℝ := s - (j : ℝ) * p
  have ha : a < -1 := by
    dsimp [a]
    linarith
  have hcompare :
      ∀ᶠ x in l,
        ‖S_{p, j}^{s}(x.1, x.2) - S_{p, j}^{s}(∞, x.2)‖ ≤
          ‖(∑' k : ℕ, x.2 * (((k + 1 : ℕ) : ℝ) * x.2) ^ a) -
              ∑ k ∈ Finset.range x.1, x.2 * (((k + 1 : ℕ) : ℝ) * x.2) ^ a‖ := by
    filter_upwards
      [hh self_mem_nhdsWithin, hnh.eventually (Filter.eventually_ge_atTop (1 : ℝ))] with x hx hxnh
    have hx_pos : 0 < x.2 := by
      simpa using hx
    have hx_nonneg : 0 ≤ x.2 := hx_pos.le
    let actual : ℕ → ℝ := fun k ↦ x.2 * integrand p j s (((k + 1 : ℕ) : ℝ) * x.2)
    let pure : ℕ → ℝ := fun k ↦ x.2 * (((k + 1 : ℕ) : ℝ) * x.2) ^ a
    have hpureBase : Summable (fun k : ℕ ↦ ((k : ℝ) ^ a)) := by
      exact (Real.summable_nat_rpow).2 ha
    have hpureBaseShift : Summable (fun k : ℕ ↦ (((k + 1 : ℕ) : ℝ) ^ a)) := by
      simpa using ((summable_nat_add_iff 1).2 hpureBase)
    have hsummablePure : Summable pure := by
      -- Separate the `h`-dependence as a constant factor times the shifted `p`-series.
      have hscaled :
          Summable (fun k : ℕ ↦ x.2 ^ (a + 1) * (((k + 1 : ℕ) : ℝ) ^ a)) :=
        hpureBaseShift.mul_left (x.2 ^ (a + 1))
      refine hscaled.congr ?_
      intro k
      have hxpow : x.2 ^ (a + 1) = x.2 * x.2 ^ a := by
        calc
          x.2 ^ (a + 1) = x.2 ^ a * x.2 ^ (1 : ℝ) := by
            rw [show a + 1 = a + (1 : ℝ) by ring, Real.rpow_add hx_pos]
          _ = x.2 * x.2 ^ a := by simp [mul_comm]
      calc
        x.2 ^ (a + 1) * (((k + 1 : ℕ) : ℝ) ^ a)
            = (((k + 1 : ℕ) : ℝ) ^ a) * (x.2 * x.2 ^ a) := by
                rw [hxpow]
                ring
        _ = x.2 * ((((k + 1 : ℕ) : ℝ) * x.2) ^ a) := by
                rw [Real.mul_rpow (by positivity) hx_nonneg]
                ring
        _ = pure k := by simp [pure, mul_comm]
    have hsummablePureTail : Summable (fun k : ℕ ↦ pure (k + x.1)) := by
      simpa using ((summable_nat_add_iff x.1).2 hsummablePure)
    have hactualTail_le : ∀ k : ℕ, actual (k + x.1) ≤ pure (k + x.1) := by
      intro k
      have hk_nat : x.1 ≤ k + x.1 + 1 := by omega
      have hk_cast : (x.1 : ℝ) ≤ ((k + x.1 + 1 : ℕ) : ℝ) := by
        exact_mod_cast hk_nat
      have hu : 1 ≤ (((k + x.1 + 1 : ℕ) : ℝ) * x.2) := by
        have hmul := mul_le_mul_of_nonneg_right hk_cast hx_nonneg
        linarith
      -- The exact kernel tail is pointwise dominated by the power tail
      -- on the eventual `u ≥ 1` region.
      exact mul_le_mul_of_nonneg_left (integrand_le_rpow_tail (hp := hp) hu) hx_nonneg
    have hactualTail_nonneg : ∀ k : ℕ, 0 ≤ actual (k + x.1) := by
      intro k
      simp only [actual, integrand_def]
      refine mul_nonneg hx_nonneg ?_
      refine div_nonneg ?_ ?_
      · exact Real.rpow_nonneg (by positivity) s
      · exact pow_nonneg (by positivity) j
    have hsummableActualTail : Summable (fun k : ℕ ↦ actual (k + x.1)) :=
      Summable.of_nonneg_of_le hactualTail_nonneg hactualTail_le hsummablePureTail
    have hsummableActual : Summable actual := by
      exact (summable_nat_add_iff x.1).1 hsummableActualTail
    have hactualTail_eq :
        (∑' k : ℕ, actual k) - ∑ k ∈ Finset.range x.1, actual k =
          ∑' k : ℕ, actual (k + x.1) := by
      -- Rewrite the exact finite-vs-infinite difference as a genuine tail `tsum`.
      calc
        (∑' k : ℕ, actual k) - ∑ k ∈ Finset.range x.1, actual k
            = (∑ k ∈ Finset.range x.1, actual k + ∑' k : ℕ, actual (k + x.1)) -
                ∑ k ∈ Finset.range x.1, actual k := by
                  rw [hsummableActual.sum_add_tsum_nat_add x.1]
        _ = ∑' k : ℕ, actual (k + x.1) := by ring
    have hpureTail_eq :
        (∑' k : ℕ, pure k) - ∑ k ∈ Finset.range x.1, pure k =
          ∑' k : ℕ, pure (k + x.1) := by
      -- The same normalization identifies the model remainder with its shifted tail.
      calc
        (∑' k : ℕ, pure k) - ∑ k ∈ Finset.range x.1, pure k
            = (∑ k ∈ Finset.range x.1, pure k + ∑' k : ℕ, pure (k + x.1)) -
                ∑ k ∈ Finset.range x.1, pure k := by
                  rw [hsummablePure.sum_add_tsum_nat_add x.1]
        _ = ∑' k : ℕ, pure (k + x.1) := by ring
    have hactualTail_tsum_nonneg : 0 ≤ ∑' k : ℕ, actual (k + x.1) :=
      tsum_nonneg hactualTail_nonneg
    have hpureTail_nonneg : ∀ k : ℕ, 0 ≤ pure (k + x.1) := by
      intro k
      exact mul_nonneg hx_nonneg (Real.rpow_nonneg (by positivity) a)
    have hpureTail_tsum_nonneg : 0 ≤ ∑' k : ℕ, pure (k + x.1) :=
      tsum_nonneg hpureTail_nonneg
    calc
      ‖S_{p, j}^{s}(x.1, x.2) - S_{p, j}^{s}(∞, x.2)‖
          = ‖-((∑' k : ℕ, actual k) - ∑ k ∈ Finset.range x.1, actual k)‖ := by
              rw [quadratureSeries_def, quadratureSum_eq_sumRangeSeries]
              simp only [actual]
              ring_nf
      _ = ‖(∑' k : ℕ, actual k) - ∑ k ∈ Finset.range x.1, actual k‖ := by rw [norm_neg]
      _ = ∑' k : ℕ, actual (k + x.1) := by
            rw [hactualTail_eq, Real.norm_eq_abs, abs_of_nonneg hactualTail_tsum_nonneg]
      _ ≤ ∑' k : ℕ, pure (k + x.1) := hsummableActualTail.tsum_mono hsummablePureTail hactualTail_le
      _ = ‖(∑' k : ℕ, pure k) - ∑ k ∈ Finset.range x.1, pure k‖ := by
            rw [hpureTail_eq, Real.norm_eq_abs, abs_of_nonneg hpureTail_tsum_nonneg]
      _ = ‖(∑' k : ℕ, x.2 * (((k + 1 : ℕ) : ℝ) * x.2) ^ a) -
            ∑ k ∈ Finset.range x.1, x.2 * (((k + 1 : ℕ) : ℝ) * x.2) ^ a‖ := by
            simp [pure]
  exact hcompare.trans_isBigO (rpowSeriesTail_isBigO (l := l) (a := a) ha hh hnh)

/-- Helper for Proposition 7.19: a nonnegative antitone zero-based sampled tail differs from its
improper integral by at most the zeroth sample. -/
lemma zeroBasedAntitoneTailSandwich {φ : ℝ → ℝ}
    (hanti : AntitoneOn φ (Set.Ici (0 : ℝ)))
    (hint : IntegrableOn φ (Set.Ioi (0 : ℝ)))
    (hnonneg : ∀ t ∈ Set.Ici (0 : ℝ), 0 ≤ φ t) :
    0 ≤ (∑' n : ℕ, φ n) - ∫ t in Set.Ioi (0 : ℝ), φ t ∧
      ((∑' n : ℕ, φ n) - ∫ t in Set.Ioi (0 : ℝ), φ t ≤ φ 0) := by
  have hnonnegIoi : ∀ t ∈ Set.Ioi (0 : ℝ), 0 ≤ φ t := fun t ht ↦
    hnonneg t (by simpa [Set.mem_Ici] using ht.le)
  have hsummable : Summable (fun n : ℕ ↦ φ n) :=
    hanti.summable_of_integrableOn_Ioi_zero hint hnonnegIoi
  constructor
  · -- The integral-test lower bound gives the nonnegative side of the sandwich.
    exact sub_nonneg.mpr (hanti.integral_le_tsum hsummable hnonnegIoi)
  · -- The converse integral-test bound controls the excess by the first sample.
    have hupper := hanti.tsum_le_integral hint hnonnegIoi
    linarith

/-- Helper for Proposition 7.19: shifting the sampled kernel tail by one step moves the integrable
surface from `Ioi h` to the zero-based `Ioi 0` comparison surface. -/
lemma shiftedScaledIntegrableOn_Ioi_zero {f : ℝ → ℝ} {h : ℝ}
    (hh : 0 < h) (hintTail : IntegrableOn f (Set.Ioi h)) :
    IntegrableOn (fun t ↦ h * f ((t + 1) * h)) (Set.Ioi (0 : ℝ)) := by
  -- First scale `Ioi 1` onto `Ioi h`, so the tail starts at the correct physical location.
  have hintTail' : IntegrableOn f (Set.Ioi ((1 : ℝ) * h)) := by
    simpa [one_mul] using hintTail
  have hscaled : IntegrableOn (fun u : ℝ ↦ f (u * h)) (Set.Ioi (1 : ℝ)) :=
    (integrableOn_Ioi_comp_mul_right_iff f (1 : ℝ) hh).2 hintTail'
  have hpreimage : ((fun t : ℝ ↦ t + 1) ⁻¹' Set.Ioi (1 : ℝ)) = Set.Ioi (0 : ℝ) := by
    ext t
    simp
  -- Then shift `Ioi 0` to `Ioi 1`, which is measure preserving for Lebesgue measure.
  have htranslate :
      IntegrableOn ((fun u : ℝ ↦ f (u * h)) ∘ fun t : ℝ ↦ t + 1)
        ((fun t : ℝ ↦ t + 1) ⁻¹' Set.Ioi (1 : ℝ)) volume :=
    ((measurePreserving_add_right volume (1 : ℝ)).integrableOn_comp_preimage
      ((Homeomorph.addRight (1 : ℝ)).isClosedEmbedding.measurableEmbedding)
      (f := fun u : ℝ ↦ f (u * h)) (s := Set.Ioi (1 : ℝ))).2 hscaled
  -- The outer scalar factor `h` is harmless for integrability.
  change Integrable (fun t ↦ h * f ((t + 1) * h)) (volume.restrict (Set.Ioi (0 : ℝ)))
  simpa [IntegrableOn, Function.comp, hpreimage, one_mul, add_comm, add_left_comm, add_assoc]
    using htranslate.const_mul h

/-- Helper for Proposition 7.19: the zero-based shifted sampled integral is exactly the kernel tail
integral over `Ioi h`. -/
lemma shiftedScaledIntegral_eq_tailIntegral {f : ℝ → ℝ} {h : ℝ}
    (hh : 0 < h) (_hintTail : IntegrableOn f (Set.Ioi h)) :
    ∫ t in Set.Ioi (0 : ℝ), h * f ((t + 1) * h) = ∫ u in Set.Ioi h, f u := by
  have hpreimage : ((fun t : ℝ ↦ t + 1) ⁻¹' Set.Ioi (1 : ℝ)) = Set.Ioi (0 : ℝ) := by
    ext t
    simp
  -- Shift the zero-based integral to `Ioi 1`, keeping the same integrand shape.
  have hshift :
      ∫ t in Set.Ioi (0 : ℝ), h * f ((t + 1) * h) =
        ∫ u in Set.Ioi (1 : ℝ), h * f (u * h) := by
    simpa [hpreimage, one_mul, add_comm, add_left_comm, add_assoc] using
      (measurePreserving_add_right volume (1 : ℝ)).setIntegral_preimage_emb
        ((Homeomorph.addRight (1 : ℝ)).isClosedEmbedding.measurableEmbedding)
        (fun u : ℝ ↦ h * f (u * h)) (Set.Ioi (1 : ℝ))
  -- Then use the multiplicative change of variables on `Ioi`.
  calc
    ∫ t in Set.Ioi (0 : ℝ), h * f ((t + 1) * h) = ∫ u in Set.Ioi (1 : ℝ), h * f (u * h) := hshift
    _ = h * ∫ u in Set.Ioi (1 : ℝ), f (u * h) := by rw [integral_const_mul]
    _ = h * (h⁻¹ * ∫ u in Set.Ioi h, f u) := by
          rw [MeasureTheory.integral_comp_mul_right_Ioi f (1 : ℝ) hh]
          simp [smul_eq_mul]
    _ = ∫ u in Set.Ioi h, f u := by
          calc
            h * (h⁻¹ * ∫ u in Set.Ioi h, f u)
                = (h * h⁻¹) * ∫ u in Set.Ioi h, f u := by ring
            _ = ∫ u in Set.Ioi h, f u := by simp [hh.ne']

/-- Helper for Proposition 7.19: the difference between the shifted and unshifted `range m`
partial sums telescopes to the endpoint defect. -/
lemma sumRangeShift_sub_sumRange_eq {α : Type*} [AddCommGroup α] (f : ℕ → α) :
    ∀ m : ℕ, (∑ k ∈ Finset.range m, f (k + 1)) - ∑ k ∈ Finset.range m, f k = f m - f 0
  | 0 => by
      -- The empty prefix has no interior contribution, so only the endpoints remain.
      simp
  | m + 1 => by
      -- Extend the two range sums by one term, then telescope the interior defect inductively.
      rw [Finset.sum_range_succ, Finset.sum_range_succ]
      calc
        (∑ k ∈ Finset.range m, f (k + 1)) + f (m + 1) - ((∑ k ∈ Finset.range m, f k) + f m)
            = ((∑ k ∈ Finset.range m, f (k + 1)) - ∑ k ∈ Finset.range m, f k) +
                (f (m + 1) - f m) := by
                  simp [sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
        _ = (f m - f 0) + (f (m + 1) - f m) := by rw [sumRangeShift_sub_sumRange_eq]
        _ = f (m + 1) - f 0 := by abel_nf

/-- Helper for Proposition 7.19: translating the `Ioi` domain before scaling keeps the tail
integrable on the zero-based comparison surface. -/
lemma shiftedScaledIntegrableOn_Ioi_zero_offset {f : ℝ → ℝ} {h a : ℝ}
    (hh : 0 < h) (hintTail : IntegrableOn f (Set.Ioi (a * h))) :
    IntegrableOn (fun t ↦ h * f ((t + a) * h)) (Set.Ioi (0 : ℝ)) := by
  -- First scale the translated tail `Ioi a` onto the physical tail `Ioi (a * h)`.
  have hscaled : IntegrableOn (fun u : ℝ ↦ f (u * h)) (Set.Ioi a) :=
    (integrableOn_Ioi_comp_mul_right_iff f a hh).2 hintTail
  have hpreimage : ((fun t : ℝ ↦ t + a) ⁻¹' Set.Ioi a) = Set.Ioi (0 : ℝ) := by
    ext t
    simp
  -- Then translate `Ioi 0` to `Ioi a`, which preserves Lebesgue measure.
  have htranslate :
      IntegrableOn ((fun u : ℝ ↦ f (u * h)) ∘ fun t : ℝ ↦ t + a)
        ((fun t : ℝ ↦ t + a) ⁻¹' Set.Ioi a) volume :=
    ((measurePreserving_add_right volume a).integrableOn_comp_preimage
      ((Homeomorph.addRight a).isClosedEmbedding.measurableEmbedding)
      (f := fun u : ℝ ↦ f (u * h)) (s := Set.Ioi a)).2 hscaled
  -- The outside scalar `h` does not affect integrability.
  change Integrable (fun t ↦ h * f ((t + a) * h)) (volume.restrict (Set.Ioi (0 : ℝ)))
  simpa [IntegrableOn, Function.comp, hpreimage, mul_add, add_comm, add_left_comm, add_assoc]
    using htranslate.const_mul h

/-- Helper for Proposition 7.19: translating the `Ioi` domain before scaling preserves the exact
tail integral. -/
lemma shiftedScaledIntegral_eq_tailIntegral_offset {f : ℝ → ℝ} {h a : ℝ}
    (hh : 0 < h) (_hintTail : IntegrableOn f (Set.Ioi (a * h))) :
    ∫ t in Set.Ioi (0 : ℝ), h * f ((t + a) * h) = ∫ u in Set.Ioi (a * h), f u := by
  have hpreimage : ((fun t : ℝ ↦ t + a) ⁻¹' Set.Ioi a) = Set.Ioi (0 : ℝ) := by
    ext t
    simp
  -- Translate the zero-based tail back to `Ioi a` before applying the scaling change of variables.
  have hshift :
      ∫ t in Set.Ioi (0 : ℝ), h * f ((t + a) * h) =
        ∫ u in Set.Ioi a, h * f (u * h) := by
    simpa [hpreimage, mul_add, add_comm, add_left_comm, add_assoc] using
      (measurePreserving_add_right volume a).setIntegral_preimage_emb
        ((Homeomorph.addRight a).isClosedEmbedding.measurableEmbedding)
        (fun u : ℝ ↦ h * f (u * h)) (Set.Ioi a)
  -- Finish with the standard multiplicative change of variables on `Ioi`.
  calc
    ∫ t in Set.Ioi (0 : ℝ), h * f ((t + a) * h) = ∫ u in Set.Ioi a, h * f (u * h) := hshift
    _ = h * ∫ u in Set.Ioi a, f (u * h) := by rw [integral_const_mul]
    _ = h * (h⁻¹ * ∫ u in Set.Ioi (a * h), f u) := by
          rw [MeasureTheory.integral_comp_mul_right_Ioi f a hh]
          simp [smul_eq_mul]
    _ = ∫ u in Set.Ioi (a * h), f u := by
          calc
            h * (h⁻¹ * ∫ u in Set.Ioi (a * h), f u)
                = (h * h⁻¹) * ∫ u in Set.Ioi (a * h), f u := by ring
            _ = ∫ u in Set.Ioi (a * h), f u := by simp [hh.ne']

/-- Helper for Proposition 7.19: when `s > 0`, the kernel integrand is integrable on `(0, ∞)`. -/
lemma integrandIntegrableOn_Ioi_pos {p s : ℝ} {j : ℕ}
    (hDecay : 0 < (j : ℝ) * p - s - 1) (hs : 0 < s) :
    IntegrableOn (fun u ↦ integrand p j s u) (Set.Ioi (0 : ℝ)) := by
  have hp : 0 < p := positive_p_of_decay hDecay (by linarith)
  have hlocalCont : ContinuousOn (fun u ↦ integrand p j s u) (Set.Icc (0 : ℝ) 1) := by
    intro u hu
    have hnum :
        ContinuousAt (fun x : ℝ ↦ x ^ s) u :=
      Real.continuousAt_rpow_const u s (Or.inr hs.le)
    have hpow :
        ContinuousAt (fun x : ℝ ↦ x ^ p) u :=
      Real.continuousAt_rpow_const u p (Or.inr hp.le)
    have hden :
        ContinuousAt (fun x : ℝ ↦ (1 + x ^ p) ^ j) u := (hpow.const_add 1).pow j
    have hden_ne : (1 + u ^ p) ^ j ≠ 0 := by
      refine pow_ne_zero _ ?_
      have hbase_pos : 0 < 1 + u ^ p := by
        linarith [Real.rpow_nonneg hu.1 p]
      exact hbase_pos.ne'
    -- On the compact near-zero interval the positive exponent removes the singularity.
    have hquot :
        ContinuousAt (fun x : ℝ ↦ x ^ s / (1 + x ^ p) ^ j) u :=
      hnum.div hden hden_ne
    simpa [integrand_def] using hquot.continuousWithinAt
  have hlocal :
      IntegrableOn (fun u ↦ integrand p j s u) (Set.Ioc (0 : ℝ) 1) := by
    have hlocalIcc :
        IntegrableOn (fun u ↦ integrand p j s u) (Set.Icc (0 : ℝ) 1) :=
      hlocalCont.integrableOn_compact isCompact_Icc
    exact hlocalIcc.mono_set fun u hu ↦ ⟨hu.1.le, hu.2⟩
  have ha : s - (j : ℝ) * p < -1 := by
    linarith
  have htailRpow :
      IntegrableOn (fun u : ℝ ↦ u ^ (s - (j : ℝ) * p)) (Set.Ioi (1 : ℝ)) :=
    integrableOn_Ioi_rpow_of_lt ha zero_lt_one
  have htail :
      IntegrableOn (fun u ↦ integrand p j s u) (Set.Ioi (1 : ℝ)) := by
    -- Beyond `1`, the same pure-power domination as the nonpositive branch applies.
    refine Integrable.mono' htailRpow ?_ ?_
    · have hmeas : Measurable (fun u : ℝ ↦ integrand p j s u) := by
        simpa [integrand_def] using
          (by fun_prop : Measurable fun u : ℝ ↦ u ^ s / (1 + u ^ p) ^ j)
      exact hmeas.aestronglyMeasurable
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
      have hu_pos : 0 < u := lt_of_lt_of_le zero_lt_one hu.le
      rw [Real.norm_eq_abs, abs_of_nonneg (integrand_nonneg hu_pos)]
      exact integrand_le_rpow_tail hp hu.le
  -- The compact near-zero piece and the decaying pure-power tail cover `(0, ∞)`.
  simpa [Set.Ioc_union_Ioi_eq_Ioi (show (0 : ℝ) ≤ 1 by norm_num)] using hlocal.union htail

/-- Helper for Proposition 7.19: the explicit derivative formula for the kernel integrand. -/
@[expose] noncomputable def integrandDeriv (p : ℝ) (j : ℕ) (s u : ℝ) : ℝ :=
  u ^ (s - 1) * (s + (s - (j : ℝ) * p) * u ^ p) / (1 + u ^ p) ^ (j + 1)

/-- Helper for Proposition 7.19: `integrandDeriv` is just the closed derivative form used in the
positive-branch quadrature estimate. -/
@[simp] theorem integrandDeriv_def (p : ℝ) (j : ℕ) (s u : ℝ) :
    integrandDeriv p j s u =
      u ^ (s - 1) * (s + (s - (j : ℝ) * p) * u ^ p) / (1 + u ^ p) ^ (j + 1) := rfl

/-- Helper for Proposition 7.19: if `s > 0`, then the kernel integrand extends continuously to the
origin. -/
lemma integrandContinuousAt_zero_pos {p s : ℝ} {j : ℕ} (hp : 0 < p) (hs : 0 < s) :
    ContinuousAt (fun u : ℝ ↦ integrand p j s u) 0 := by
  -- The numerator `u^s` is continuous at `0`, while the denominator stays positive there.
  have hnum :
      ContinuousAt (fun u : ℝ ↦ u ^ s) 0 :=
    Real.continuousAt_rpow_const 0 s (Or.inr hs.le)
  have hpow :
      ContinuousAt (fun u : ℝ ↦ u ^ p) 0 :=
    Real.continuousAt_rpow_const 0 p (Or.inr hp.le)
  have hden :
      ContinuousAt (fun u : ℝ ↦ (1 + u ^ p) ^ j) 0 := (hpow.const_add 1).pow j
  have hden_ne : (1 + (0 : ℝ) ^ p) ^ j ≠ 0 := by
    have hzero : (0 : ℝ) ^ p = 0 := by
      rw [Real.zero_rpow (by linarith : p ≠ 0)]
    have : 0 < (1 + (0 : ℝ) ^ p) ^ j := by
      simp [hzero]
    exact this.ne'
  have hquot :
      ContinuousAt (fun u : ℝ ↦ u ^ s / (1 + u ^ p) ^ j) 0 :=
    hnum.div hden hden_ne
  simpa [integrand_def] using hquot

/-- Helper for Proposition 7.19: scaling preserves the positive-branch kernel integral on
`(0, ∞)`. -/
lemma scaledIntegrandIntegral_eq_integral {p s h : ℝ} {j : ℕ}
    (hh : 0 < h) :
    ∫ t in Set.Ioi (0 : ℝ), h * integrand p j s (t * h) = I_{p, j}^{s} := by
  -- A multiplicative change of variables converts the scaled half-line integral back to the
  -- original kernel integral.
  rw [integral_def]
  calc
    ∫ t in Set.Ioi (0 : ℝ), h * integrand p j s (t * h)
        = h * ∫ t in Set.Ioi (0 : ℝ), integrand p j s (t * h) := by
            rw [integral_const_mul]
    _ = h * (h⁻¹ * ∫ u in Set.Ioi (0 : ℝ), integrand p j s u) := by
          rw [MeasureTheory.integral_comp_mul_right_Ioi (fun u : ℝ ↦ integrand p j s u) 0 hh]
          simp [smul_eq_mul]
    _ = ∫ u in Set.Ioi (0 : ℝ), integrand p j s u := by
          field_simp [hh.ne']

/-- Helper for Proposition 7.19: `integrandDeriv` admits the quotient-rule split form used in the
positive-branch estimates. -/
lemma integrandDeriv_eq_split {p s u : ℝ} {j : ℕ} (hu : 0 < u) :
    integrandDeriv p j s u =
      s * u ^ (s - 1) / (1 + u ^ p) ^ j -
        ((j : ℝ) * p) * u ^ (s + p - 1) / (1 + u ^ p) ^ (j + 1) := by
  -- Normalize the closed derivative formula once, so later proofs can reuse the stable split form.
  simp [integrandDeriv_def, div_eq_mul_inv, sub_eq_add_neg, Real.rpow_add hu]
  field_simp [hu.ne']
  ring_nf

/-- Helper for Proposition 7.19: the exact quotient-rule normal form produced by
`HasDerivAt.div` simplifies to `integrandDeriv`. -/
lemma integrandDeriv_eq_quotientRule {p s u : ℝ} {j : ℕ} (hu : 0 < u) :
    ((s * u ^ (s - 1)) * (1 + u ^ p) ^ j -
        u ^ s * ((j : ℝ) * (1 + u ^ p) ^ (j - 1) * (p * u ^ (p - 1)))) /
      ((1 + u ^ p) ^ j) ^ 2 =
      integrandDeriv p j s u := by
  -- Reduce the raw quotient-rule expression to the stable split form first, then reuse the
  -- public closed derivative formula.
  have hden_pos : 0 < 1 + u ^ p := by
    linarith [Real.rpow_nonneg hu.le p]
  cases j with
  | zero =>
      rw [integrandDeriv_def]
      field_simp [hu.ne', hden_pos.ne']
      ring_nf
  | succ k =>
      have hrpow : u ^ s * u ^ (p - 1) = u ^ (s + p - 1) := by
        rw [← Real.rpow_add hu]
        congr 1
        ring
      have hrpow' :
          u ^ s * ↑(k + 1) * (1 + u ^ p) ^ k * p * u ^ (p - 1) =
            ↑(k + 1) * p * u ^ (s + p - 1) * (1 + u ^ p) ^ k := by
        calc
          u ^ s * ↑(k + 1) * (1 + u ^ p) ^ k * p * u ^ (p - 1)
              = ↑(k + 1) * p * (u ^ s * u ^ (p - 1)) * (1 + u ^ p) ^ k := by
                  ring
          _ = ↑(k + 1) * p * u ^ (s + p - 1) * (1 + u ^ p) ^ k := by
                rw [hrpow]
      have hpow :
          u ^ p * (1 + u ^ p) ^ (k + 1) * (1 + u ^ p) ^ k +
            (1 + u ^ p) ^ (k + 1) * (1 + u ^ p) ^ k =
            (1 + u ^ p) ^ ((k + 1) * 2) := by
        calc
          u ^ p * (1 + u ^ p) ^ (k + 1) * (1 + u ^ p) ^ k +
              (1 + u ^ p) ^ (k + 1) * (1 + u ^ p) ^ k
              = (u ^ p + 1) * ((1 + u ^ p) ^ (k + 1) * (1 + u ^ p) ^ k) := by
                  ring
          _ = (1 + u ^ p) * ((1 + u ^ p) ^ (k + 1) * (1 + u ^ p) ^ k) := by
                ring
          _ = (1 + u ^ p) ^ ((k + 1) * 2) := by
                calc
                  (1 + u ^ p) * ((1 + u ^ p) ^ (k + 1) * (1 + u ^ p) ^ k)
                      = (1 + u ^ p) ^ (k + 1) * ((1 + u ^ p) * (1 + u ^ p) ^ k) := by
                          ring
                  _ = (1 + u ^ p) ^ (k + 1) * (1 + u ^ p) ^ (k + 1) := by
                        rw [pow_succ']
                  _ = (1 + u ^ p) ^ ((k + 1) + (k + 1)) := by
                        rw [← pow_add]
                  _ = (1 + u ^ p) ^ ((k + 1) * 2) := by
                        congr 1
                        omega
      calc
        ((s * u ^ (s - 1)) * (1 + u ^ p) ^ (k + 1) -
              u ^ s * ((((k + 1 : ℕ) : ℝ)) * (1 + u ^ p) ^ k * (p * u ^ (p - 1)))) /
            ((1 + u ^ p) ^ (k + 1)) ^ 2
            =
              s * u ^ (s - 1) / (1 + u ^ p) ^ (k + 1) -
                (((k + 1 : ℕ) : ℝ) * p) * u ^ (s + p - 1) / (1 + u ^ p) ^ (k + 2) := by
                  field_simp [hu.ne', hden_pos.ne']
                  rw [hrpow']
                  ring_nf
        _ = integrandDeriv p (k + 1) s u := by
              rw [integrandDeriv_eq_split (p := p) (j := k + 1) (s := s) hu]

/-- Helper for Proposition 7.19: on `[0, ∞)`, the positive-branch kernel integrand is
nonnegative. -/
lemma integrand_nonneg_of_nonneg {p s u : ℝ} {j : ℕ} (hp : 0 < p) (hs : 0 < s) (hu : 0 ≤ u) :
    0 ≤ integrand p j s u := by
  by_cases hu0 : u = 0
  · -- At the origin, the positive exponent forces the numerator to vanish.
    subst hu0
    rw [integrand_def, Real.zero_rpow (by linarith : s ≠ 0), Real.zero_rpow (by linarith : p ≠ 0)]
    positivity
  · -- Away from the origin, reuse the positive-input nonnegativity lemma.
    have hu_pos : 0 < u := lt_of_le_of_ne hu (by simpa [eq_comm] using hu0)
    exact integrand_nonneg (p := p) (s := s) (j := j) hu_pos

lemma integrand_hasDerivAt_pos {p s u : ℝ} {j : ℕ} (hu : 0 < u) :
    HasDerivAt (fun x : ℝ ↦ x ^ s / (1 + x ^ p) ^ j)
      (integrandDeriv p j s u) u := by
  -- Route correction: differentiate the quotient directly, then rewrite the exact raw
  -- denominator-squared derivative once through `integrandDeriv_eq_quotientRule`.
  have hnum :
      HasDerivAt (fun x : ℝ ↦ x ^ s) (s * u ^ (s - 1)) u :=
    Real.hasDerivAt_rpow_const (Or.inl hu.ne')
  have hpow :
      HasDerivAt (fun x : ℝ ↦ x ^ p) (p * u ^ (p - 1)) u :=
    Real.hasDerivAt_rpow_const (Or.inl hu.ne')
  have hden := (hpow.const_add 1).pow j
  have hden_ne : (1 + u ^ p) ^ j ≠ 0 := by
    refine pow_ne_zero _ ?_
    linarith [Real.rpow_nonneg hu.le p]
  have hraw := hnum.div hden hden_ne
  refine (integrandDeriv_eq_quotientRule (p := p) (j := j) (s := s) hu).symm ▸ ?_
  change HasDerivAt ((fun x : ℝ ↦ x ^ s) / (fun x ↦ 1 + x ^ p) ^ j)
    (((s * u ^ (s - 1)) * (1 + u ^ p) ^ j -
        u ^ s * ((j : ℝ) * (1 + u ^ p) ^ (j - 1) * (p * u ^ (p - 1)))) /
      ((1 + u ^ p) ^ j) ^ 2) u
  exact hraw

/-- Helper for Proposition 7.19: the explicit derivative formula is integrable on `(0, ∞)` in the
positive-`s` regime. -/
lemma integrandDerivIntegrableOn_Ioi_pos {p s : ℝ} {j : ℕ}
    (hDecay : 0 < (j : ℝ) * p - s - 1) (hs : 0 < s) :
    IntegrableOn (fun u ↦ integrandDeriv p j s u) (Set.Ioi (0 : ℝ)) := by
  -- Split the closed derivative formula into two integrable kernel-shaped pieces and
  -- control each piece by a pure-power model near `0` and on the tail.
  have hp : 0 < p := positive_p_of_decay hDecay (by linarith)
  have hterm1LocalExp : -1 < s - 1 := by
    linarith
  have hterm2LocalExp : -1 < s + p - 1 := by
    linarith
  have htailExp : s - 1 - (j : ℝ) * p < -1 := by
    linarith
  have hterm1Model : IntegrableOn (fun u ↦ integrand p j (s - 1) u) (Set.Ioi (0 : ℝ)) := by
    have hlocalRpow : IntegrableOn (fun u : ℝ ↦ u ^ (s - 1)) (Set.Ioc (0 : ℝ) 1) := by
      rw [integrableOn_Ioc_iff_integrableOn_Ioo]
      exact (intervalIntegral.integrableOn_Ioo_rpow_iff zero_lt_one).2 hterm1LocalExp
    have hlocal :
        IntegrableOn (fun u ↦ integrand p j (s - 1) u) (Set.Ioc (0 : ℝ) 1) := by
      -- Near the origin, the denominator is harmless and we compare with `u^(s-1)`.
      refine Integrable.mono' hlocalRpow ?_ ?_
      · have hmeas : Measurable (fun u : ℝ ↦ integrand p j (s - 1) u) := by
          simpa [integrand_def] using
            (by fun_prop : Measurable fun u : ℝ ↦ u ^ (s - 1) / (1 + u ^ p) ^ j)
        exact hmeas.aestronglyMeasurable
      · filter_upwards [ae_restrict_mem measurableSet_Ioc] with u hu
        rw [Real.norm_eq_abs, abs_of_nonneg (integrand_nonneg hu.1)]
        exact integrand_le_rpow_local (p := p) (s := s - 1) (j := j) hu.1
    have htailRpow :
        IntegrableOn (fun u : ℝ ↦ u ^ ((s - 1) - (j : ℝ) * p)) (Set.Ioi (1 : ℝ)) :=
      integrableOn_Ioi_rpow_of_lt htailExp zero_lt_one
    have htail :
        IntegrableOn (fun u ↦ integrand p j (s - 1) u) (Set.Ioi (1 : ℝ)) := by
      -- On the tail, the denominator supplies the full `u^(jp)` decay.
      refine Integrable.mono' htailRpow ?_ ?_
      · have hmeas : Measurable (fun u : ℝ ↦ integrand p j (s - 1) u) := by
          simpa [integrand_def] using
            (by fun_prop : Measurable fun u : ℝ ↦ u ^ (s - 1) / (1 + u ^ p) ^ j)
        exact hmeas.aestronglyMeasurable
      · filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
        have hu_pos : 0 < u := lt_trans zero_lt_one hu
        rw [Real.norm_eq_abs, abs_of_nonneg (integrand_nonneg hu_pos)]
        exact integrand_le_rpow_tail (p := p) (s := s - 1) (j := j) hp hu.le
    simpa [Set.Ioc_union_Ioi_eq_Ioi (show (0 : ℝ) ≤ 1 by norm_num)] using hlocal.union htail
  have hterm2Model :
      IntegrableOn (fun u ↦ integrand p (j + 1) (s + p - 1) u) (Set.Ioi (0 : ℝ)) := by
    have hlocalRpow : IntegrableOn (fun u : ℝ ↦ u ^ (s + p - 1)) (Set.Ioc (0 : ℝ) 1) := by
      rw [integrableOn_Ioc_iff_integrableOn_Ioo]
      exact (intervalIntegral.integrableOn_Ioo_rpow_iff zero_lt_one).2 hterm2LocalExp
    have hlocal :
        IntegrableOn (fun u ↦ integrand p (j + 1) (s + p - 1) u) (Set.Ioc (0 : ℝ) 1) := by
      -- The second split term has exponent `s + p - 1`, which is still locally integrable.
      refine Integrable.mono' hlocalRpow ?_ ?_
      · have hmeas : Measurable (fun u : ℝ ↦ integrand p (j + 1) (s + p - 1) u) := by
          simpa [integrand_def] using
            (by fun_prop :
              Measurable fun u : ℝ ↦ u ^ (s + p - 1) / (1 + u ^ p) ^ (j + 1))
        exact hmeas.aestronglyMeasurable
      · filter_upwards [ae_restrict_mem measurableSet_Ioc] with u hu
        rw [Real.norm_eq_abs, abs_of_nonneg (integrand_nonneg hu.1)]
        exact integrand_le_rpow_local (p := p) (s := s + p - 1) (j := j + 1) hu.1
    have htailExp' : (s + p - 1) - ((j + 1 : ℕ) : ℝ) * p < -1 := by
      have hrewrite :
          (s + p - 1) - ((j + 1 : ℕ) : ℝ) * p = s - 1 - (j : ℝ) * p := by
        norm_num [Nat.cast_add]
        ring
      rw [hrewrite]
      exact htailExp
    have htailRpow :
        IntegrableOn (fun u : ℝ ↦ u ^ ((s + p - 1) - ((j + 1 : ℕ) : ℝ) * p)) (Set.Ioi (1 : ℝ)) :=
      integrableOn_Ioi_rpow_of_lt htailExp' zero_lt_one
    have htail :
        IntegrableOn (fun u ↦ integrand p (j + 1) (s + p - 1) u) (Set.Ioi (1 : ℝ)) := by
      -- The tail exponent again collapses to `s - jp - 1`.
      refine Integrable.mono' htailRpow ?_ ?_
      · have hmeas : Measurable (fun u : ℝ ↦ integrand p (j + 1) (s + p - 1) u) := by
          simpa [integrand_def] using
            (by fun_prop :
              Measurable fun u : ℝ ↦ u ^ (s + p - 1) / (1 + u ^ p) ^ (j + 1))
        exact hmeas.aestronglyMeasurable
      · filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
        have hu_pos : 0 < u := lt_trans zero_lt_one hu
        rw [Real.norm_eq_abs, abs_of_nonneg (integrand_nonneg hu_pos)]
        exact integrand_le_rpow_tail (p := p) (s := s + p - 1) (j := j + 1) hp hu.le
    simpa [Set.Ioc_union_Ioi_eq_Ioi (show (0 : ℝ) ≤ 1 by norm_num)] using hlocal.union htail
  have hterm1 :
      IntegrableOn
        (fun u ↦ s * u ^ (s - 1) / (1 + u ^ p) ^ j)
        (Set.Ioi (0 : ℝ)) := by
    -- Rewrite the first split term as a scalar multiple of the model kernel.
    simpa [MeasureTheory.IntegrableOn, integrand_def, div_eq_mul_inv, mul_comm, mul_left_comm,
      mul_assoc] using
      hterm1Model.const_mul s
  have hterm2 :
      IntegrableOn
        (fun u ↦ ((j : ℝ) * p) * u ^ (s + p - 1) / (1 + u ^ p) ^ (j + 1))
        (Set.Ioi (0 : ℝ)) := by
    -- Rewrite the second split term in the same kernel notation.
    simpa [MeasureTheory.IntegrableOn, integrand_def, div_eq_mul_inv, mul_comm, mul_left_comm,
      mul_assoc] using
      hterm2Model.const_mul ((j : ℝ) * p)
  have hsplit :
      Set.EqOn
        (fun u ↦ integrandDeriv p j s u)
        (fun u ↦
          s * u ^ (s - 1) / (1 + u ^ p) ^ j -
            ((j : ℝ) * p) * u ^ (s + p - 1) / (1 + u ^ p) ^ (j + 1))
        (Set.Ioi (0 : ℝ)) := by
    intro u hu
    exact integrandDeriv_eq_split (p := p) (j := j) (s := s) hu
  -- Assemble the two integrable split pieces back into `integrandDeriv`.
  exact (hterm1.sub hterm2).congr_fun hsplit.symm measurableSet_Ioi

/-- Helper for Proposition 7.19: continuity at both endpoints plus differentiability on the
interior gives continuity on a closed interval. -/
lemma continuousOn_Icc_of_continuousAt_differentiableOn {f : ℝ → ℝ} {a b : ℝ}
    (ha : ContinuousAt f a) (hb : ContinuousAt f b) (hd : DifferentiableOn ℝ f (Set.Ioo a b)) :
    ContinuousOn f (Set.Icc a b) := by
  by_cases hab : a ≤ b
  · exact Set.Ioo_union_both hab ▸ hd.continuousOn.union_continuousAt isOpen_Ioo
      (by simp [ha, hb])
  · simp [Set.Icc_eq_empty_of_lt (lt_of_not_ge hab)]

/-- Helper for Proposition 7.19: continuity at the left endpoint plus differentiability on the
open tail gives continuity on the closed tail. -/
lemma continuousOn_Ici_of_continuousAt_differentiableOn {f : ℝ → ℝ} {a : ℝ}
    (ha : ContinuousAt f a) (hd : DifferentiableOn ℝ f (Set.Ioi a)) :
    ContinuousOn f (Set.Ici a) := by
  rw [← Set.Ioi_union_left]
  exact hd.continuousOn.union_continuousAt isOpen_Ioi (by simp [ha])

/-- Helper for Proposition 7.19: a right-endpoint rectangle-rule cell error is controlled by the
integral of the derivative on that cell. -/
lemma rightSampleCellError_le_mulIntegralDeriv {f f' : ℝ → ℝ} {a b : ℝ}
    (hab : a ≤ b) (hcont : ContinuousOn f (Set.Icc a b))
    (hderiv : ∀ x ∈ Set.Ioo a b, HasDerivAt f (f' x) x)
    (hint : IntervalIntegrable f' volume a b) :
    ‖(b - a) * f b - ∫ x in a..b, f x‖ ≤ (b - a) * ∫ x in a..b, ‖f' x‖ := by
  -- Rewrite the cell defect as an integral of the endpoint displacement, then bound that
  -- displacement uniformly on the whole cell by the total derivative mass on `[a, b]`.
  have hfInt : IntervalIntegrable f volume a b := hcont.intervalIntegrable_of_Icc hab
  have hconstInt : IntervalIntegrable (fun _ : ℝ ↦ f b) volume a b := by simp
  have hnormInt : IntervalIntegrable (fun x ↦ ‖f' x‖) volume a b := hint.norm
  have hpoint :
      ∀ x ∈ Set.Ioc a b, ‖f b - f x‖ ≤ ∫ t in a..b, ‖f' t‖ := by
    intro x hx
    have hax : a ≤ x := hx.1.le
    have hxb : x ≤ b := hx.2
    have hcontTail : ContinuousOn f (Set.Icc x b) := hcont.mono (Set.Icc_subset_Icc hax le_rfl)
    have hderivTail : DifferentiableOn ℝ f (Set.Ioo x b) := by
      intro t ht
      exact (hderiv t ⟨lt_of_le_of_lt hax ht.1, ht.2⟩).differentiableAt.differentiableWithinAt
    have hnormIntTail : IntervalIntegrable (fun t ↦ ‖f' t‖) volume x b := by
      refine hnormInt.mono_set ?_
      rw [Set.uIcc_of_le hxb, Set.uIcc_of_le hab]
      exact Set.Icc_subset_Icc hax le_rfl
    have hnormIntLeft : IntervalIntegrable (fun t ↦ ‖f' t‖) volume a x := by
      refine hnormInt.mono_set ?_
      rw [Set.uIcc_of_le hax, Set.uIcc_of_le hab]
      exact Set.Icc_subset_Icc le_rfl hxb
    have hdisp :
        ‖f b - f x‖ ≤ ∫ t in x..b, ‖f' t‖ := by
      refine norm_sub_le_integral_of_norm_deriv_le_of_le hxb hcontTail hderivTail ?_ hnormIntTail
      refine Filter.Eventually.of_forall ?_
      intro t ht
      simp [(hderiv t ⟨lt_of_le_of_lt hax ht.1, ht.2⟩).deriv]
    have htail_le :
        ∫ t in x..b, ‖f' t‖ ≤ ∫ t in a..b, ‖f' t‖ := by
      have hsplit :
          (∫ t in a..x, ‖f' t‖) + ∫ t in x..b, ‖f' t‖ = ∫ t in a..b, ‖f' t‖ := by
        simpa using intervalIntegral.integral_add_adjacent_intervals hnormIntLeft hnormIntTail
      have hleft_nonneg : 0 ≤ ∫ t in a..x, ‖f' t‖ := by
        exact intervalIntegral.integral_nonneg hax (fun t _ ↦ norm_nonneg _)
      linarith
    exact hdisp.trans htail_le
  have hdefect :
      (b - a) * f b - ∫ x in a..b, f x = ∫ x in a..b, (f b - f x) := by
    -- Pull the constant sample term inside the cell integral.
    rw [intervalIntegral.integral_sub hconstInt hfInt, intervalIntegral.integral_const, smul_eq_mul]
  have hnormBound :
      ‖∫ x in a..b, (f b - f x)‖ ≤ ∫ x in a..b, ∫ t in a..b, ‖f' t‖ := by
    have hconstBound :
        IntervalIntegrable (fun _ : ℝ ↦ ∫ t in a..b, ‖f' t‖) volume a b := by
      simp
    refine intervalIntegral.norm_integral_le_of_norm_le hab ?_ hconstBound
    refine Filter.Eventually.of_forall ?_
    intro x hx
    simpa using hpoint x hx
  rw [hdefect]
  calc
    ‖∫ x in a..b, (f b - f x)‖ ≤ ∫ x in a..b, ∫ t in a..b, ‖f' t‖ := hnormBound
    _ = (b - a) * ∫ x in a..b, ‖f' x‖ := by rw [intervalIntegral.integral_const, smul_eq_mul]

/-- Helper for Proposition 7.19: for `s > 0`, the infinite-series versus integral gap is `O(h)`.
This is the step error in Proposition 7.19. -/
lemma quadratureSeriesGap_pos_isBigO {l : Filter (ℕ × ℝ)} {p s : ℝ} {j : ℕ}
    (hDecay : 0 < (j : ℝ) * p - s - 1)
    (hs : 0 < s)
    (hh : Filter.Tendsto Prod.snd l (nhdsWithin (0 : ℝ) (Set.Ioi 0))) :
    (fun x ↦ S_{p, j}^{s}(∞, x.2) - I_{p, j}^{s}) =O[l] (fun x ↦ x.2) := by
  have hp : 0 < p := positive_p_of_decay hDecay (by linarith)
  have hint :
      IntegrableOn (fun u ↦ integrand p j s u) (Set.Ioi (0 : ℝ)) :=
    integrandIntegrableOn_Ioi_pos hDecay hs
  have hderivInt :
      IntegrableOn (fun u ↦ integrandDeriv p j s u) (Set.Ioi (0 : ℝ)) :=
    integrandDerivIntegrableOn_Ioi_pos hDecay hs
  have hC_nonneg :
      0 ≤ ∫ u in Set.Ioi (0 : ℝ), ‖integrandDeriv p j s u‖ := by
    exact integral_nonneg fun _ ↦ norm_nonneg _
  refine Asymptotics.IsBigO.of_bound (∫ u in Set.Ioi (0 : ℝ), ‖integrandDeriv p j s u‖) ?_
  filter_upwards [hh self_mem_nhdsWithin] with x hx
  have hx_pos : 0 < x.2 := by
    simpa using hx
  let α : ℕ → ℝ := fun k ↦ (k : ℝ) * x.2
  let f : ℝ → ℝ := fun u ↦ integrand p j s u
  let f' : ℝ → ℝ := fun u ↦ integrandDeriv p j s u
  let cellIntegral : ℕ → ℝ := fun k ↦ ∫ u in α k..α (k + 1), f u
  let cellDeriv : ℕ → ℝ := fun k ↦ x.2 * ∫ u in α k..α (k + 1), ‖f' u‖
  let sample : ℕ → ℝ := fun k ↦ x.2 * f (α (k + 1))
  have hα_nonneg : ∀ k : ℕ, 0 ≤ α k := by
    intro k
    positivity
  have hα_mono : ∀ k : ℕ, α k ≤ α (k + 1) := by
    intro k
    have hk : (k : ℝ) ≤ (((k + 1 : ℕ) : ℝ)) := by
      exact_mod_cast Nat.le_succ k
    simpa [α] using mul_le_mul_of_nonneg_right hk hx_pos.le
  have hsample_nonneg : ∀ k : ℕ, 0 ≤ sample k := by
    intro k
    have hk_nonneg : 0 ≤ α (k + 1) := hα_nonneg (k + 1)
    exact mul_nonneg hx_pos.le <|
      integrand_nonneg_of_nonneg (p := p) (j := j) (s := s) hp hs hk_nonneg
  have hcellIntegral_nonneg : ∀ k : ℕ, 0 ≤ cellIntegral k := by
    intro k
    exact intervalIntegral.integral_nonneg (hα_mono k) fun u hu ↦
      integrand_nonneg_of_nonneg (p := p) (j := j) (s := s) hp hs
        (le_trans (hα_nonneg k) hu.1)
  have hcellDeriv_nonneg : ∀ k : ℕ, 0 ≤ cellDeriv k := by
    intro k
    refine mul_nonneg hx_pos.le ?_
    exact intervalIntegral.integral_nonneg (hα_mono k) fun u _ ↦ norm_nonneg _
  have hf_contAt_nonneg : ∀ u ≥ 0, ContinuousAt f u := by
    intro u hu
    by_cases hu0 : u = 0
    · subst hu0
      simpa [f] using integrandContinuousAt_zero_pos (p := p) (j := j) (s := s) hp hs
    · have hu_pos : 0 < u := lt_of_le_of_ne hu (by simpa [eq_comm] using hu0)
      change ContinuousAt (fun x : ℝ ↦ x ^ s / (1 + x ^ p) ^ j) u
      exact (integrand_hasDerivAt_pos (p := p) (j := j) (s := s) hu_pos).continuousAt
  have hcellFInt : ∀ k : ℕ, IntervalIntegrable f volume (α k) (α (k + 1)) := by
    intro k
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (hα_mono k)]
    exact hint.mono_set (by
      intro u hu
      exact lt_of_le_of_lt (hα_nonneg k) hu.1)
  have hcellDerivInt : ∀ k : ℕ, IntervalIntegrable f' volume (α k) (α (k + 1)) := by
    intro k
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (hα_mono k)]
    exact hderivInt.mono_set (by
      intro u hu
      exact lt_of_le_of_lt (hα_nonneg k) hu.1)
  have hcellError : ∀ k : ℕ, ‖sample k - cellIntegral k‖ ≤ cellDeriv k := by
    intro k
    have hcontCell :
        ContinuousOn f (Set.Icc (α k) (α (k + 1))) := by
      refine continuousOn_Icc_of_continuousAt_differentiableOn
        (hf_contAt_nonneg (α k) (hα_nonneg k))
        (hf_contAt_nonneg (α (k + 1)) (hα_nonneg (k + 1))) ?_
      intro u hu
      have hu_pos : 0 < u := lt_of_le_of_lt (hα_nonneg k) hu.1
      change DifferentiableWithinAt ℝ (fun x : ℝ ↦ x ^ s / (1 + x ^ p) ^ j)
        (Set.Ioo (α k) (α (k + 1))) u
      exact
        (HasDerivAt.differentiableAt
          (integrand_hasDerivAt_pos (p := p) (j := j) (s := s) hu_pos)).differentiableWithinAt
    have hderivCell :
        ∀ u ∈ Set.Ioo (α k) (α (k + 1)), HasDerivAt f (f' u) u := by
      intro u hu
      have hu_pos : 0 < u := lt_of_le_of_lt (hα_nonneg k) hu.1
      change HasDerivAt (fun x : ℝ ↦ x ^ s / (1 + x ^ p) ^ j) (integrandDeriv p j s u) u
      exact integrand_hasDerivAt_pos (p := p) (j := j) (s := s) hu_pos
    have hraw :=
      rightSampleCellError_le_mulIntegralDeriv
        (f := f) (f' := f') (a := α k) (b := α (k + 1))
        (hα_mono k) hcontCell hderivCell (hcellDerivInt k)
    have hstep : α (k + 1) - α k = x.2 := by
      simp [α, Nat.cast_add, Nat.cast_one, mul_add, sub_eq_add_neg, add_comm, add_assoc,
        mul_comm]
    simpa [sample, cellIntegral, cellDeriv, hstep] using hraw
  have hpartial_cellIntegral :
      ∀ m : ℕ, ∑ k ∈ Finset.range m, cellIntegral k = ∫ u in (0 : ℝ)..α m, f u := by
    intro m
    simpa [cellIntegral, α] using
      (intervalIntegral.sum_integral_adjacent_intervals
        (f := f) (a := α) (n := m) (fun k _ ↦ hcellFInt k))
  have hpartial_cellDeriv :
      ∀ m : ℕ, ∑ k ∈ Finset.range m, cellDeriv k = x.2 * ∫ u in (0 : ℝ)..α m, ‖f' u‖ := by
    intro m
    calc
      ∑ k ∈ Finset.range m, cellDeriv k
          = x.2 * ∑ k ∈ Finset.range m, ∫ u in α k..α (k + 1), ‖f' u‖ := by
              simp [cellDeriv, Finset.mul_sum]
      _ = x.2 * ∫ u in (0 : ℝ)..α m, ‖f' u‖ := by
            simpa [α] using
              congrArg (fun z : ℝ ↦ x.2 * z)
                (intervalIntegral.sum_integral_adjacent_intervals
                  (f := fun u ↦ ‖f' u‖) (a := α) (n := m) (fun k _ ↦ (hcellDerivInt k).norm))
  have hα_tendsto : Filter.Tendsto α Filter.atTop Filter.atTop := by
    simpa [α, mul_comm] using tendsto_natCast_atTop_atTop.atTop_mul_const hx_pos
  have hcellIntegral_hasSum : HasSum cellIntegral I_{p, j}^{s} := by
    rw [hasSum_iff_tendsto_nat_of_nonneg hcellIntegral_nonneg]
    have hlim :
        Filter.Tendsto (fun m : ℕ => ∫ u in (0 : ℝ)..α m, f u)
          Filter.atTop (nhds I_{p, j}^{s}) := by
      simpa [f, integral_def] using intervalIntegral_tendsto_integral_Ioi 0 hint hα_tendsto
    exact hlim.congr' (Filter.Eventually.of_forall fun m ↦ (hpartial_cellIntegral m).symm)
  have hcellDeriv_hasSum :
      HasSum cellDeriv (x.2 * ∫ u in Set.Ioi (0 : ℝ), ‖f' u‖) := by
    rw [hasSum_iff_tendsto_nat_of_nonneg hcellDeriv_nonneg]
    have hlim :
        Filter.Tendsto (fun m : ℕ => x.2 * ∫ u in (0 : ℝ)..α m, ‖f' u‖)
          Filter.atTop (nhds (x.2 * ∫ u in Set.Ioi (0 : ℝ), ‖f' u‖)) := by
      exact (intervalIntegral_tendsto_integral_Ioi 0 hderivInt.norm hα_tendsto).const_mul x.2
    exact hlim.congr' (Filter.Eventually.of_forall fun m ↦ (hpartial_cellDeriv m).symm)
  have hsample_le : ∀ k : ℕ, sample k ≤ cellIntegral k + cellDeriv k := by
    intro k
    have hsub : sample k - cellIntegral k ≤ cellDeriv k := by
      exact le_trans (le_abs_self (sample k - cellIntegral k)) (hcellError k)
    linarith [hsample_nonneg k]
  have hsample_summable : Summable sample :=
    Summable.of_nonneg_of_le hsample_nonneg hsample_le
      (hcellIntegral_hasSum.summable.add hcellDeriv_hasSum.summable)
  have hsample_hasSum : HasSum sample S_{p, j}^{s}(∞, x.2) := by
    simpa [sample, f, α, quadratureSeries_def] using hsample_summable.hasSum
  have hgap_hasSum :
      HasSum (fun k ↦ sample k - cellIntegral k) (S_{p, j}^{s}(∞, x.2) - I_{p, j}^{s}) := by
    simpa [sample, cellIntegral, f, α, quadratureSeries_def, sub_eq_add_neg] using
      hsample_hasSum.sub hcellIntegral_hasSum
  have hnorm_gap :
      ‖S_{p, j}^{s}(∞, x.2) - I_{p, j}^{s}‖ ≤ ∑' k : ℕ, cellDeriv k := by
    calc
      ‖S_{p, j}^{s}(∞, x.2) - I_{p, j}^{s}‖ = ‖∑' k : ℕ, (sample k - cellIntegral k)‖ := by
            rw [hgap_hasSum.tsum_eq]
      _ ≤ ∑' k : ℕ, ‖sample k - cellIntegral k‖ := by
            exact norm_tsum_le_tsum_norm hgap_hasSum.summable.norm
      _ ≤ ∑' k : ℕ, cellDeriv k := by
            exact Summable.tsum_le_tsum hcellError hgap_hasSum.summable.norm
              hcellDeriv_hasSum.summable
  calc
    ‖S_{p, j}^{s}(∞, x.2) - I_{p, j}^{s}‖ ≤ ∑' k : ℕ, cellDeriv k := hnorm_gap
    _ = x.2 * ∫ u in Set.Ioi (0 : ℝ), ‖f' u‖ := hcellDeriv_hasSum.tsum_eq
    _ = x.2 * ∫ u in Set.Ioi (0 : ℝ), ‖integrandDeriv p j s u‖ := by simp [f']
    _ = (∫ u in Set.Ioi (0 : ℝ), ‖integrandDeriv p j s u‖) * ‖x.2‖ := by
          rw [Real.norm_of_nonneg hx_pos.le, mul_comm]

/-- Helper for Proposition 7.19: for `-1 < s ≤ 0`, the infinite-series versus integral gap is
`O(h^(s + 1))`. This is the step error in Proposition 7.19. -/
lemma quadratureSeriesGap_nonpos_isBigO {l : Filter (ℕ × ℝ)} {p s : ℝ} {j : ℕ}
    (hDecay : 0 < (j : ℝ) * p - s - 1)
    (hsLower : -1 < s)
    (hsUpper : s ≤ 0)
    (hh : Filter.Tendsto Prod.snd l (nhdsWithin (0 : ℝ) (Set.Ioi 0))) :
    (fun x ↦ S_{p, j}^{s}(∞, x.2) - I_{p, j}^{s}) =O[l] (fun x ↦ x.2 ^ (s + 1)) := by
  refine Asymptotics.IsBigO.of_bound |(s + 1)⁻¹| ?_
  filter_upwards [hh self_mem_nhdsWithin] with x hx
  have hx_pos : 0 < x.2 := by
    simpa using hx
  have hp : 0 < p := positive_p_of_decay hDecay hsLower
  have hanti :
      AntitoneOn (integrand p j s) (Set.Ioi (0 : ℝ)) :=
    integrandAntitoneOn_Ioi_nonpos hp hsUpper
  have hint :
      IntegrableOn (fun u ↦ integrand p j s u) (Set.Ioi (0 : ℝ)) :=
    integrandIntegrableOn_Ioi_nonpos hDecay hp hsLower hsUpper
  have hintTail :
      IntegrableOn (fun u ↦ integrand p j s u) (Set.Ioi x.2) :=
    hint.mono_set (Set.Ioi_subset_Ioi hx_pos.le)
  let φ : ℝ → ℝ := fun t ↦ x.2 * integrand p j s ((t + 1) * x.2)
  have hφanti : AntitoneOn φ (Set.Ici (0 : ℝ)) := by
    intro u hu v hv huv
    have hu_nonneg : 0 ≤ u := hu
    have hv_nonneg : 0 ≤ v := hv
    have hu_one_pos : 0 < u + 1 := by linarith
    have hv_one_pos : 0 < v + 1 := by linarith
    have hu_shift_pos : 0 < (u + 1) * x.2 := mul_pos hu_one_pos hx_pos
    have hv_shift_pos : 0 < (v + 1) * x.2 := mul_pos hv_one_pos hx_pos
    have hscaled : (u + 1) * x.2 ≤ (v + 1) * x.2 := by
      nlinarith
    exact mul_le_mul_of_nonneg_left
      (hanti hu_shift_pos hv_shift_pos hscaled) hx_pos.le
  have hφint : IntegrableOn φ (Set.Ioi (0 : ℝ)) :=
    (shiftedScaledIntegrableOn_Ioi_zero (f := fun u ↦ integrand p j s u) hx_pos hintTail)
  have hφnonneg : ∀ t ∈ Set.Ici (0 : ℝ), 0 ≤ φ t := by
    intro t ht
    have ht_nonneg : 0 ≤ t := ht
    have ht_one_pos : 0 < t + 1 := by linarith
    have ht_shift_pos : 0 < (t + 1) * x.2 := mul_pos ht_one_pos hx_pos
    exact mul_nonneg hx_pos.le (integrand_nonneg ht_shift_pos)
  have hsandwich := zeroBasedAntitoneTailSandwich hφanti hφint hφnonneg
  have htailEq :
      ∫ t in Set.Ioi (0 : ℝ), φ t = ∫ u in Set.Ioi x.2, integrand p j s u :=
    shiftedScaledIntegral_eq_tailIntegral
      (f := fun u ↦ integrand p j s u) hx_pos hintTail
  have htailGap_nonneg :
      0 ≤ S_{p, j}^{s}(∞, x.2) - ∫ u in Set.Ioi x.2, integrand p j s u := by
    rw [← htailEq]
    simpa [quadratureSeries_def, φ] using hsandwich.1
  have htailGap_le_sample :
      S_{p, j}^{s}(∞, x.2) - ∫ u in Set.Ioi x.2, integrand p j s u ≤
        x.2 * integrand p j s x.2 := by
    rw [← htailEq]
    simpa [quadratureSeries_def, φ] using hsandwich.2
  have hintCell :
      IntervalIntegrable (fun u ↦ integrand p j s u) volume 0 x.2 := by
    rw [intervalIntegrable_iff, Set.uIoc_of_le hx_pos.le]
    exact hint.mono_set (by
      intro u hu
      exact hu.1)
  have hconstCell :
      IntervalIntegrable (fun _ : ℝ ↦ integrand p j s x.2) volume 0 x.2 := by
    simp
  have hsample_le_cell :
      x.2 * integrand p j s x.2 ≤ ∫ u in (0 : ℝ)..x.2, integrand p j s u := by
    have hmonoCell :
        ∀ u ∈ Set.Ioo (0 : ℝ) x.2, integrand p j s x.2 ≤ integrand p j s u := by
      intro u hu
      exact hanti hu.1 hx_pos hu.2.le
    calc
      x.2 * integrand p j s x.2 = ∫ u in (0 : ℝ)..x.2, integrand p j s x.2 := by
        simpa [smul_eq_mul] using
          (intervalIntegral.integral_const (a := (0 : ℝ)) (b := x.2)
            (integrand p j s x.2)).symm
      _ ≤ ∫ u in (0 : ℝ)..x.2, integrand p j s u := by
        exact intervalIntegral.integral_mono_on_of_le_Ioo hx_pos.le hconstCell hintCell hmonoCell
  have hpowInt :
      IntervalIntegrable (fun u : ℝ ↦ u ^ s) volume 0 x.2 := by
    rw [intervalIntegrable_iff, Set.uIoc_of_le hx_pos.le, integrableOn_Ioc_iff_integrableOn_Ioo]
    exact (intervalIntegral.integrableOn_Ioo_rpow_iff hx_pos).2 hsLower
  have hcell_le_power :
      ∫ u in (0 : ℝ)..x.2, integrand p j s u ≤ ∫ u in (0 : ℝ)..x.2, u ^ s := by
    exact intervalIntegral.integral_mono_on_of_le_Ioo hx_pos.le hintCell hpowInt
      (fun u hu ↦ integrand_le_rpow_local hu.1)
  have hpower_eval :
      ∫ u in (0 : ℝ)..x.2, u ^ s = x.2 ^ (s + 1) / (s + 1) := by
    rw [integral_rpow (a := (0 : ℝ)) (b := x.2) (r := s) (Or.inl hsLower)]
    have hs1_ne : s + 1 ≠ 0 := by linarith
    rw [Real.zero_rpow hs1_ne, sub_zero]
  have hmain_rewrite :
      S_{p, j}^{s}(∞, x.2) - I_{p, j}^{s} =
        (S_{p, j}^{s}(∞, x.2) - (∫ u in Set.Ioi x.2, integrand p j s u)) -
          (∫ u in (0 : ℝ)..x.2, integrand p j s u) := by
    have hsplit :
        I_{p, j}^{s} =
          (∫ u in Set.Ioi x.2, integrand p j s u) +
            (∫ u in (0 : ℝ)..x.2, integrand p j s u) := by
      rw [integral_def]
      linarith [intervalIntegral.integral_Ioi_sub_Ioi
        (μ := volume) (f := fun u ↦ integrand p j s u) hint hx_pos.le]
    rw [hsplit]
    ring_nf
  have hnorm_le_cell :
      ‖S_{p, j}^{s}(∞, x.2) - I_{p, j}^{s}‖ ≤ ∫ u in (0 : ℝ)..x.2, integrand p j s u := by
    rw [hmain_rewrite, Real.norm_eq_abs, abs_of_nonpos]
    · linarith [le_trans htailGap_le_sample hsample_le_cell]
    · exact sub_nonpos.mpr (le_trans htailGap_le_sample hsample_le_cell)
  have hs1_pos : 0 < s + 1 := by linarith
  have htarget_le :
      ∫ u in (0 : ℝ)..x.2, integrand p j s u ≤ |(s + 1)⁻¹| * ‖x.2 ^ (s + 1)‖ := by
    calc
      ∫ u in (0 : ℝ)..x.2, integrand p j s u ≤ ∫ u in (0 : ℝ)..x.2, u ^ s := hcell_le_power
      _ = x.2 ^ (s + 1) / (s + 1) := hpower_eval
      _ = |(s + 1)⁻¹| * ‖x.2 ^ (s + 1)‖ := by
            have hpow_nonneg : 0 ≤ x.2 ^ (s + 1) := Real.rpow_nonneg hx_pos.le _
            rw [div_eq_mul_inv, mul_comm, Real.norm_eq_abs, abs_of_nonneg hpow_nonneg,
              abs_of_pos (inv_pos.mpr hs1_pos)]
  exact le_trans hnorm_le_cell htarget_le

/-- Helper for Proposition 7.19: when `s = -1`, the finite-to-infinite tail is already `O(1)`.
This is the tail contribution used in the logarithmic case. -/
lemma quadratureTail_negOne_isBigO {l : Filter (ℕ × ℝ)} {p : ℝ} {j : ℕ}
    (hDecay : 0 < (j : ℝ) * p)
    (hn : Filter.Tendsto Prod.fst l Filter.atTop)
    (hh : Filter.Tendsto Prod.snd l (nhdsWithin (0 : ℝ) (Set.Ioi 0)))
    (hnh : Filter.Tendsto (fun x ↦ (x.1 : ℝ) * x.2) l Filter.atTop) :
    (fun x ↦ S_{p, j}^{(-1 : ℝ)}(x.1, x.2) - S_{p, j}^{(-1 : ℝ)}(∞, x.2)) =O[l]
      (fun _ ↦ (1 : ℝ)) := by
  -- TODO: first prove the sharper tail estimate `O((nh)^(-(j : ℝ) * p))`, then use
  -- `n * h → ∞` and the negative exponent to upgrade it to a bounded `O(1)` remainder.
  have htail :
      (fun x ↦ S_{p, j}^{(-1 : ℝ)}(x.1, x.2) - S_{p, j}^{(-1 : ℝ)}(∞, x.2)) =O[l]
        (fun x ↦ ((x.1 : ℝ) * x.2) ^ (-((j : ℝ) * p))) := by
    have hDecay' : 0 < (j : ℝ) * p - (-1 : ℝ) - 1 := by
      simpa using hDecay
    have htail' :
        (fun x ↦ S_{p, j}^{(-1 : ℝ)}(x.1, x.2) - S_{p, j}^{(-1 : ℝ)}(∞, x.2)) =O[l]
          (fun x ↦ ((x.1 : ℝ) * x.2) ^ ((-1 : ℝ) - (j : ℝ) * p + 1)) :=
      quadratureTail_isBigO_power (l := l) (p := p) (s := (-1 : ℝ)) (j := j)
        hDecay' (positive_p_of_negOneDecay hDecay) hn hh hnh
    -- The logarithmic case is the `s = -1` specialization of the general tail theorem.
    convert htail' using 1
    ext x
    ring_nf
  have hpow_tendsto :
      Filter.Tendsto (fun x ↦ ((x.1 : ℝ) * x.2) ^ (-((j : ℝ) * p))) l (nhds (0 : ℝ)) :=
    by
      change Filter.Tendsto
        ((fun y : ℝ ↦ y ^ (-((j : ℝ) * p))) ∘ fun x ↦ (x.1 : ℝ) * x.2)
        l (nhds (0 : ℝ))
      exact (tendsto_rpow_neg_atTop hDecay).comp hnh
  -- A function converging to `0` is automatically `O(1)`, so the sharper power tail is enough.
  exact htail.trans (Asymptotics.isBigO_const_of_tendsto hpow_tendsto one_ne_zero)

/-- Helper for Proposition 7.19: the reciprocal-power defect
`1 - ((1 + y)^n)⁻¹` is bounded by the linear term `n * y` for `y ≥ 0`. -/
lemma one_sub_inv_one_add_pow_le_mul (y : ℝ) (hy : 0 ≤ y) :
    ∀ n : ℕ, 0 ≤ 1 - ((1 + y) ^ n)⁻¹ ∧ 1 - ((1 + y) ^ n)⁻¹ ≤ (n : ℝ) * y
  | 0 => by
      -- The zeroth reciprocal power is exact, so the defect vanishes.
      simp
  | n + 1 => by
      rcases one_sub_inv_one_add_pow_le_mul y hy n with ⟨ih_nonneg, ih_le⟩
      have hy1_pos : 0 < 1 + y := by linarith
      have hy1_inv_nonneg : 0 ≤ (1 + y)⁻¹ := inv_nonneg.mpr hy1_pos.le
      have hy1_inv_le_one : (1 + y)⁻¹ ≤ 1 := by
        have hy1_ge_one : 1 ≤ 1 + y := by linarith
        exact inv_le_one_of_one_le₀ hy1_ge_one
      have hterm1_eq : 1 - (1 + y)⁻¹ = y * (1 + y)⁻¹ := by
        field_simp [hy1_pos.ne']
        ring
      have hterm1_nonneg : 0 ≤ 1 - (1 + y)⁻¹ := by
        rw [hterm1_eq]
        exact mul_nonneg hy hy1_inv_nonneg
      have hterm1_le : 1 - (1 + y)⁻¹ ≤ y := by
        rw [hterm1_eq]
        have hmul := mul_le_mul_of_nonneg_left hy1_inv_le_one hy
        simpa [one_mul, mul_comm] using hmul
      have hpow_ne : (1 + y) ^ n ≠ 0 := pow_ne_zero n hy1_pos.ne'
      have hdecomp :
          1 - ((1 + y) ^ (n + 1))⁻¹ =
            (1 - (1 + y)⁻¹) + (1 + y)⁻¹ * (1 - ((1 + y) ^ n)⁻¹) := by
        rw [pow_succ]
        field_simp [hy1_pos.ne', hpow_ne]
        ring
      have hterm2_le : (1 + y)⁻¹ * (1 - ((1 + y) ^ n)⁻¹) ≤ (n : ℝ) * y := by
        have hmul :
            (1 + y)⁻¹ * (1 - ((1 + y) ^ n)⁻¹) ≤
              1 * (1 - ((1 + y) ^ n)⁻¹) := by
          exact mul_le_mul_of_nonneg_right hy1_inv_le_one ih_nonneg
        exact hmul.trans (by simpa using ih_le)
      constructor
      · -- The inductive decomposition is a sum of two nonnegative pieces.
        rw [hdecomp]
        exact add_nonneg hterm1_nonneg (mul_nonneg hy1_inv_nonneg ih_nonneg)
      · -- Each piece is controlled separately by `y` and `n * y`.
        rw [hdecomp]
        calc
          (1 - (1 + y)⁻¹) + (1 + y)⁻¹ * (1 - ((1 + y) ^ n)⁻¹)
              ≤ y + (n : ℝ) * y := add_le_add hterm1_le hterm2_le
          _ = ((n + 1 : ℕ) : ℝ) * y := by
                rw [Nat.cast_add, Nat.cast_one, add_comm, add_mul, one_mul]

/-- Helper for Proposition 7.19: in the logarithmic case, the pointwise correction
`u⁻¹ - integrand p j (-1) u` is nonnegative and controlled by `j * u^(p - 1)`. -/
lemma invSubIntegrandNegOne_le_rpow {p u : ℝ} {j : ℕ}
    (_hp : 0 < p) (hu : 0 < u) :
    0 ≤ u⁻¹ - integrand p j (-1 : ℝ) u ∧
      u⁻¹ - integrand p j (-1 : ℝ) u ≤ (j : ℝ) * u ^ (p - 1) := by
  have hu_nonneg : 0 ≤ u := hu.le
  have hu_inv_nonneg : 0 ≤ u⁻¹ := inv_nonneg.mpr hu_nonneg
  have hpow_nonneg : 0 ≤ u ^ p := Real.rpow_nonneg hu_nonneg p
  have hcore :=
    one_sub_inv_one_add_pow_le_mul (y := u ^ p) hpow_nonneg j
  constructor
  · -- Dropping the denominator shows the correction is nonnegative.
    refine sub_nonneg.mpr ?_
    simpa [Real.rpow_neg_one] using
      integrand_le_rpow_local (p := p) (s := (-1 : ℝ)) (j := j) hu
  · -- Factor the correction into `u⁻¹` times the reciprocal-power defect.
    calc
      u⁻¹ - integrand p j (-1 : ℝ) u
          = u⁻¹ * (1 - ((1 + u ^ p) ^ j)⁻¹) := by
              rw [integrand_def, Real.rpow_neg_one, div_eq_mul_inv]
              ring
      _ ≤ u⁻¹ * ((j : ℝ) * u ^ p) := by
            exact mul_le_mul_of_nonneg_left hcore.2 hu_inv_nonneg
      _ = (j : ℝ) * u ^ (p - 1) := by
            calc
              u⁻¹ * ((j : ℝ) * u ^ p) = (j : ℝ) * (u⁻¹ * u ^ p) := by ring
              _ = (j : ℝ) * (u ^ (-1 : ℝ) * u ^ p) := by
                    rw [← Real.rpow_neg_one u]
              _ = (j : ℝ) * u ^ (p - 1) := by
                    rw [← Real.rpow_add hu]
                    congr 1
                    ring

/-- Helper for Proposition 7.19: in the logarithmic case, the kernel integrand is integrable on
every positive tail `(h, ∞)`. -/
lemma integrandIntegrableOn_Ioi_negOne {p h : ℝ} {j : ℕ}
    (hDecay : 0 < (j : ℝ) * p) (hp : 0 < p) (hh : 0 < h) :
    IntegrableOn (fun u ↦ integrand p j (-1 : ℝ) u) (Set.Ioi h) := by
  let M : ℝ := max 1 h
  have hM_pos : 0 < M := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have hlocalCont : ContinuousOn (fun u ↦ integrand p j (-1 : ℝ) u) (Set.Icc h M) := by
    intro u hu
    have hu_pos : 0 < u := lt_of_lt_of_le hh hu.1
    have hnum :
        ContinuousAt (fun x : ℝ ↦ x ^ (-1 : ℝ)) u :=
      Real.continuousAt_rpow_const u (-1 : ℝ) (Or.inl hu_pos.ne')
    have hpow :
        ContinuousAt (fun x : ℝ ↦ x ^ p) u :=
      Real.continuousAt_rpow_const u p (Or.inl hu_pos.ne')
    have hden :
        ContinuousAt (fun x : ℝ ↦ (1 + x ^ p) ^ j) u := (hpow.const_add 1).pow j
    have hden_ne : (1 + u ^ p) ^ j ≠ 0 := by
      refine pow_ne_zero _ ?_
      linarith [Real.rpow_nonneg hu_pos.le p]
    -- Stay on the positive side of the axis so the `u^(-1)` numerator is continuous.
    have hquot :
        ContinuousAt (fun x : ℝ ↦ x ^ (-1 : ℝ) / (1 + x ^ p) ^ j) u :=
      hnum.div hden hden_ne
    simpa [integrand_def] using hquot.continuousWithinAt
  have hlocal :
      IntegrableOn (fun u ↦ integrand p j (-1 : ℝ) u) (Set.Ioc h M) := by
    have hlocalIcc :
        IntegrableOn (fun u ↦ integrand p j (-1 : ℝ) u) (Set.Icc h M) :=
      hlocalCont.integrableOn_compact isCompact_Icc
    exact hlocalIcc.mono_set fun u hu ↦ ⟨hu.1.le, hu.2⟩
  have hexp : (-1 : ℝ) - (j : ℝ) * p < -1 := by
    linarith
  have htailRpow :
      IntegrableOn (fun u : ℝ ↦ u ^ ((-1 : ℝ) - (j : ℝ) * p)) (Set.Ioi M) :=
    integrableOn_Ioi_rpow_of_lt hexp hM_pos
  have htail :
      IntegrableOn (fun u ↦ integrand p j (-1 : ℝ) u) (Set.Ioi M) := by
    refine Integrable.mono' htailRpow ?_ ?_
    · have hmeas : Measurable (fun u : ℝ ↦ integrand p j (-1 : ℝ) u) := by
        simpa [integrand_def] using
          (by fun_prop : Measurable fun u : ℝ ↦ u ^ (-1 : ℝ) / (1 + u ^ p) ^ j)
      exact hmeas.aestronglyMeasurable
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
      have hu_one : 1 ≤ u := le_trans (le_max_left _ _) hu.le
      have hu_pos : 0 < u := lt_of_lt_of_le zero_lt_one hu_one
      rw [Real.norm_eq_abs, abs_of_nonneg (integrand_nonneg hu_pos)]
      simpa using
        integrand_le_rpow_tail (p := p) (s := (-1 : ℝ)) (j := j) hp hu_one
  -- The compact near-tail piece and the decaying pure-power tail cover `(h, ∞)`.
  simpa [M, Set.Ioc_union_Ioi_eq_Ioi (show h ≤ max 1 h by exact le_max_right _ _)] using
    hlocal.union htail

/-- Helper for Proposition 7.19: the logarithmically renormalized infinite series is `O(1)` in the
`s = -1` case. -/
lemma quadratureSeriesLogGap_isBigO {l : Filter (ℕ × ℝ)} {p : ℝ} {j : ℕ}
    (hDecay : 0 < (j : ℝ) * p)
    (hh : Filter.Tendsto Prod.snd l (nhdsWithin (0 : ℝ) (Set.Ioi 0))) :
    (fun x ↦ S_{p, j}^{(-1 : ℝ)}(∞, x.2) + Real.log x.2) =O[l] (fun _ ↦ (1 : ℝ)) := by
  have hp : 0 < p := positive_p_of_negOneDecay hDecay
  refine Asymptotics.IsBigO.of_bound
    (1 + ‖∫ u in Set.Ioi (1 : ℝ), integrand p j (-1 : ℝ) u‖ + |(j : ℝ) / p|) ?_
  filter_upwards
    [hh self_mem_nhdsWithin,
      hh.eventually (mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds zero_lt_one))] with x hx hxlt
  have hx_pos : 0 < x.2 := by
    simpa using hx
  have hx_le_one : x.2 ≤ 1 := hxlt.le
  let f : ℝ → ℝ := fun u ↦ integrand p j (-1 : ℝ) u
  have hanti : AntitoneOn f (Set.Ioi (0 : ℝ)) :=
    integrandAntitoneOn_Ioi_nonpos hp (by norm_num : (-1 : ℝ) ≤ 0)
  have hintTail : IntegrableOn f (Set.Ioi x.2) :=
    integrandIntegrableOn_Ioi_negOne hDecay hp hx_pos
  let φ : ℝ → ℝ := fun t ↦ x.2 * f ((t + 1) * x.2)
  have hφanti : AntitoneOn φ (Set.Ici (0 : ℝ)) := by
    -- The shifted-and-scaled tail inherits antitonicity from the kernel tail on `(0, ∞)`.
    intro u hu v hv huv
    have hu_one_pos : 0 < u + 1 := add_pos_of_nonneg_of_pos hu zero_lt_one
    have hv_one_pos : 0 < v + 1 := add_pos_of_nonneg_of_pos hv zero_lt_one
    have hu_shift_pos : 0 < (u + 1) * x.2 := mul_pos hu_one_pos hx_pos
    have hv_shift_pos : 0 < (v + 1) * x.2 := mul_pos hv_one_pos hx_pos
    have hscaled : (u + 1) * x.2 ≤ (v + 1) * x.2 := by
      nlinarith
    exact mul_le_mul_of_nonneg_left
      (hanti hu_shift_pos hv_shift_pos hscaled) hx_pos.le
  have hφint : IntegrableOn φ (Set.Ioi (0 : ℝ)) :=
    shiftedScaledIntegrableOn_Ioi_zero (f := f) hx_pos hintTail
  have hφnonneg : ∀ t ∈ Set.Ici (0 : ℝ), 0 ≤ φ t := by
    -- Every shifted sample stays in `(0, ∞)`, where the kernel integrand is nonnegative.
    intro t ht
    have ht_one_pos : 0 < t + 1 := add_pos_of_nonneg_of_pos ht zero_lt_one
    have ht_shift_pos : 0 < (t + 1) * x.2 := mul_pos ht_one_pos hx_pos
    exact mul_nonneg hx_pos.le (integrand_nonneg ht_shift_pos)
  have hsandwich := zeroBasedAntitoneTailSandwich hφanti hφint hφnonneg
  have htailEq :
      ∫ t in Set.Ioi (0 : ℝ), φ t = ∫ u in Set.Ioi x.2, f u :=
    shiftedScaledIntegral_eq_tailIntegral (f := f) hx_pos hintTail
  have htailGap_nonneg :
      0 ≤ S_{p, j}^{(-1 : ℝ)}(∞, x.2) - ∫ u in Set.Ioi x.2, f u := by
    -- The shifted antitone sandwich gives the lower half of the tail comparison.
    rw [← htailEq]
    simpa [quadratureSeries_def, φ, f] using hsandwich.1
  have htailGap_le_sample :
      S_{p, j}^{(-1 : ℝ)}(∞, x.2) - ∫ u in Set.Ioi x.2, f u ≤ x.2 * f x.2 := by
    -- The same sandwich bounds the gap by the first right-endpoint sample.
    rw [← htailEq]
    simpa [quadratureSeries_def, φ, f] using hsandwich.2
  have hden_ge_one : 1 ≤ (1 + x.2 ^ p) ^ j := by
    have hbase_ge_one : 1 ≤ 1 + x.2 ^ p := by
      linarith [Real.rpow_nonneg hx_pos.le p]
    simpa using
      (pow_le_pow_left₀ (by positivity : 0 ≤ (1 : ℝ)) hbase_ge_one j :
        (1 : ℝ) ^ j ≤ (1 + x.2 ^ p) ^ j)
  have hsample_le_one : x.2 * f x.2 ≤ 1 := by
    -- Multiplying the logarithmic kernel by `h` removes the singular numerator.
    change x.2 * integrand p j (-1 : ℝ) x.2 ≤ 1
    calc
      x.2 * integrand p j (-1 : ℝ) x.2
          = x.2 * (x.2⁻¹ / (1 + x.2 ^ p) ^ j) := by
              rw [integrand_def, Real.rpow_neg_one]
      _ = 1 / (1 + x.2 ^ p) ^ j := by
            field_simp [hx_pos.ne']
      _ ≤ 1 := by
            simpa [one_div] using inv_le_one_of_one_le₀ hden_ge_one
  have htailGap_norm_le :
      ‖S_{p, j}^{(-1 : ℝ)}(∞, x.2) - ∫ u in Set.Ioi x.2, f u‖ ≤ 1 := by
    -- The tail-versus-integral defect is nonnegative and bounded by the first sample.
    rw [Real.norm_eq_abs, abs_of_nonneg htailGap_nonneg]
    exact le_trans htailGap_le_sample hsample_le_one
  have htailOne :
      IntegrableOn f (Set.Ioi (1 : ℝ)) :=
    hintTail.mono_set (Set.Ioi_subset_Ioi hx_le_one)
  have hsplit :
      ∫ u in Set.Ioi x.2, f u = (∫ u in Set.Ioi (1 : ℝ), f u) + ∫ u in x.2..1, f u := by
    -- Split the improper tail at `1` so the logarithm is isolated on `(x.2, 1]`.
    let A : ℝ := ∫ u in Set.Ioi x.2, f u
    let B : ℝ := ∫ u in Set.Ioi (1 : ℝ), f u
    let C : ℝ := ∫ u in x.2..1, f u
    have hsub' :
        (∫ u in Set.Ioi x.2, f u) - ∫ u in Set.Ioi (1 : ℝ), f u = ∫ u in x.2..1, f u := by
      simpa using
        (intervalIntegral.integral_Ioi_sub_Ioi (μ := volume) (f := f) hintTail hx_le_one)
    have hABC : A - B = C := by simpa [A, B, C] using hsub'
    have hsum : A = B + C := sub_eq_iff_eq_add'.mp hABC
    simpa [A, B, C] using hsum
  have hintervalTail :
      IntervalIntegrable f volume x.2 1 := by
    rw [intervalIntegrable_iff, Set.uIoc_of_le hx_le_one]
    exact hintTail.mono_set fun u hu ↦ hu.1
  have hintervalInv :
      IntervalIntegrable (fun u : ℝ ↦ u⁻¹) volume x.2 1 := by
    rw [intervalIntegrable_iff, Set.uIoc_of_le hx_le_one]
    have hcont :
        ContinuousOn (fun u : ℝ ↦ u⁻¹) (Set.Icc x.2 1) := by
      refine continuousOn_inv₀.mono ?_
      intro u hu
      exact ne_of_gt (lt_of_lt_of_le hx_pos hu.1)
    exact (hcont.integrableOn_compact isCompact_Icc).mono_set fun u hu ↦ ⟨hu.1.le, hu.2⟩
  have hnormalize :
      (∫ u in Set.Ioi x.2, f u) + Real.log x.2 =
        (∫ u in Set.Ioi (1 : ℝ), f u) - ∫ u in x.2..1, (u⁻¹ - f u) := by
    -- Route correction: package the logarithmic algebra as one rewrite instead of scattering it.
    have hlog :
        ∫ u in x.2..1, u⁻¹ = -Real.log x.2 := by
      calc
        ∫ u in x.2..1, u⁻¹ = Real.log (1 / x.2) := by
          simpa using integral_inv_of_pos hx_pos zero_lt_one
        _ = -Real.log x.2 := by
          rw [one_div, Real.log_inv]
    have hlog' : Real.log x.2 = -∫ u in x.2..1, u⁻¹ := by
      simpa using (congrArg Neg.neg hlog).symm
    rw [hsplit, hlog', intervalIntegral.integral_sub hintervalInv hintervalTail]
    have hswap :
        (∫ u in Set.Ioi (1 : ℝ), f u) + ∫ u in x.2..1, f u =
          (∫ u in x.2..1, f u) + ∫ u in Set.Ioi (1 : ℝ), f u := by
      exact add_comm (∫ u in Set.Ioi (1 : ℝ), f u) (∫ u in x.2..1, f u)
    rw [hswap]
    ring_nf
  have hcorr_nonneg :
      0 ≤ ∫ u in x.2..1, (u⁻¹ - f u) := by
    -- The correction integrand is pointwise nonnegative on `(x.2, 1]`.
    refine intervalIntegral.integral_nonneg hx_le_one ?_
    intro u hu
    exact (invSubIntegrandNegOne_le_rpow hp (lt_of_lt_of_le hx_pos hu.1)).1
  have hpowInt :
      IntervalIntegrable (fun u : ℝ ↦ (j : ℝ) * u ^ (p - 1)) volume x.2 1 := by
    rw [intervalIntegrable_iff, Set.uIoc_of_le hx_le_one]
    have hcont :
        ContinuousOn (fun u : ℝ ↦ (j : ℝ) * u ^ (p - 1)) (Set.Icc x.2 1) := by
      refine ContinuousOn.const_mul ?_ _
      intro u hu
      exact
        (Real.continuousAt_rpow_const u (p - 1)
          (Or.inl (ne_of_gt (lt_of_lt_of_le hx_pos hu.1)))).continuousWithinAt
    exact (hcont.integrableOn_compact isCompact_Icc).mono_set fun u hu ↦ ⟨hu.1.le, hu.2⟩
  have hcorr_le_rpow :
      ∫ u in x.2..1, (u⁻¹ - f u) ≤ ∫ u in x.2..1, (j : ℝ) * u ^ (p - 1) := by
    -- Compare the correction directly to the explicit power bound from the pointwise helper.
    exact intervalIntegral.integral_mono_on_of_le_Ioo hx_le_one
      (hintervalInv.sub hintervalTail) hpowInt
      (fun u hu ↦ by
        have hu_pos : 0 < u := lt_trans hx_pos hu.1
        exact (invSubIntegrandNegOne_le_rpow hp hu_pos).2)
  have hpow_eval :
      ∫ u in x.2..1, (j : ℝ) * u ^ (p - 1) = (j : ℝ) * ((1 - x.2 ^ p) / p) := by
    -- Evaluate the model correction integral explicitly by `integral_rpow`.
    have hp_minus : -1 < p - 1 := by linarith
    have hcore :
        ∫ u in x.2..1, u ^ (p - 1) = (1 - x.2 ^ p) / p := by
      calc
        ∫ u in x.2..1, u ^ (p - 1)
            = (1 ^ ((p - 1) + 1) - x.2 ^ ((p - 1) + 1)) / ((p - 1) + 1) := by
                rw [integral_rpow (a := x.2) (b := (1 : ℝ)) (r := p - 1) (Or.inl hp_minus)]
        _ = (1 - x.2 ^ p) / p := by
              rw [show (p - 1) + 1 = p by ring, Real.one_rpow]
    calc
      ∫ u in x.2..1, (j : ℝ) * u ^ (p - 1)
          = (j : ℝ) * ∫ u in x.2..1, u ^ (p - 1) := by
              rw [intervalIntegral.integral_const_mul]
      _ = (j : ℝ) * ((1 - x.2 ^ p) / p) := by rw [hcore]
  have hj_div_p_nonneg : 0 ≤ (j : ℝ) / p := by
    exact div_nonneg (by exact_mod_cast Nat.zero_le j) hp.le
  have hpow_bound :
      ∫ u in x.2..1, (j : ℝ) * u ^ (p - 1) ≤ (j : ℝ) / p := by
    -- Since `0 < x.2 ≤ 1`, the factor `1 - x.2^p` stays in `[0, 1]`.
    have hxpow_le_one : x.2 ^ p ≤ 1 := by
      simpa [Real.one_rpow] using Real.rpow_le_rpow hx_pos.le hx_le_one hp.le
    have hfactor_le :
        (1 - x.2 ^ p) / p ≤ 1 / p := by
      exact div_le_div_of_nonneg_right (by linarith [Real.rpow_nonneg hx_pos.le p]) hp.le
    calc
      ∫ u in x.2..1, (j : ℝ) * u ^ (p - 1) = (j : ℝ) * ((1 - x.2 ^ p) / p) := hpow_eval
      _ ≤ (j : ℝ) * (1 / p) := by
            exact mul_le_mul_of_nonneg_left hfactor_le (by exact_mod_cast Nat.zero_le j)
      _ = (j : ℝ) / p := by ring
  have hnormalize_bound :
      ‖(∫ u in Set.Ioi x.2, f u) + Real.log x.2‖ ≤
        ‖∫ u in Set.Ioi (1 : ℝ), f u‖ + |(j : ℝ) / p| := by
    -- The normalized tail is the fixed tail beyond `1` minus a uniformly bounded correction.
    have hcorr_norm :
        ‖∫ u in x.2..1, (u⁻¹ - f u)‖ = ∫ u in x.2..1, (u⁻¹ - f u) := by
      rw [Real.norm_eq_abs, abs_of_nonneg hcorr_nonneg]
    rw [hnormalize]
    have hsubnorm :
        ‖(∫ u in Set.Ioi (1 : ℝ), f u) - ∫ u in x.2..1, (u⁻¹ - f u)‖ ≤
          ‖∫ u in Set.Ioi (1 : ℝ), f u‖ + ‖∫ u in x.2..1, (u⁻¹ - f u)‖ := by
      simpa using
        norm_sub_le (∫ u in Set.Ioi (1 : ℝ), f u) (∫ u in x.2..1, (u⁻¹ - f u))
    calc
      ‖(∫ u in Set.Ioi (1 : ℝ), f u) - ∫ u in x.2..1, (u⁻¹ - f u)‖
          ≤ ‖∫ u in Set.Ioi (1 : ℝ), f u‖ + ‖∫ u in x.2..1, (u⁻¹ - f u)‖ := hsubnorm
      _ = ‖∫ u in Set.Ioi (1 : ℝ), f u‖ + ∫ u in x.2..1, (u⁻¹ - f u) := by
            rw [hcorr_norm]
      _ ≤ ‖∫ u in Set.Ioi (1 : ℝ), f u‖ + |(j : ℝ) / p| := by
            rw [abs_of_nonneg hj_div_p_nonneg]
            gcongr
            exact le_trans hcorr_le_rpow hpow_bound
  have hmain :
      ‖S_{p, j}^{(-1 : ℝ)}(∞, x.2) + Real.log x.2‖ ≤
        1 + ‖∫ u in Set.Ioi (1 : ℝ), f u‖ + |(j : ℝ) / p| := by
    -- Combine the bounded shifted-tail defect with the bounded normalized tail integral.
    have hdecomp :
        S_{p, j}^{(-1 : ℝ)}(∞, x.2) + Real.log x.2 =
          (S_{p, j}^{(-1 : ℝ)}(∞, x.2) - ∫ u in Set.Ioi x.2, f u) +
            ((∫ u in Set.Ioi x.2, f u) + Real.log x.2) := by
      ring
    rw [hdecomp]
    calc
      ‖(S_{p, j}^{(-1 : ℝ)}(∞, x.2) - ∫ u in Set.Ioi x.2, f u) +
          ((∫ u in Set.Ioi x.2, f u) + Real.log x.2)‖
          ≤ ‖S_{p, j}^{(-1 : ℝ)}(∞, x.2) - ∫ u in Set.Ioi x.2, f u‖ +
              ‖(∫ u in Set.Ioi x.2, f u) + Real.log x.2‖ := norm_add_le _ _
      _ ≤ 1 + (‖∫ u in Set.Ioi (1 : ℝ), f u‖ + |(j : ℝ) / p|) := by
            exact add_le_add htailGap_norm_le hnormalize_bound
      _ = 1 + ‖∫ u in Set.Ioi (1 : ℝ), f u‖ + |(j : ℝ) / p| := by ring
  simpa [f] using hmain

/-- Proposition 7.19 (1). If `s > 0`, then the quadrature error
`S_{p,j}^s(n,h) - I_{p,j}^s` decomposes as
`O((nh)^(s - jp + 1)) + O(h)` along any filter with `n → ∞`, `h → 0+`, and
`n * h → ∞`. -/
theorem quadratureApproxPos {l : Filter (ℕ × ℝ)} {p s : ℝ} {j : ℕ}
    (hDecay : 0 < (j : ℝ) * p - s - 1)
    (hs : 0 < s)
    (hn : Filter.Tendsto Prod.fst l Filter.atTop)
    (hh : Filter.Tendsto Prod.snd l (nhdsWithin (0 : ℝ) (Set.Ioi 0)))
    (hnh : Filter.Tendsto (fun x ↦ (x.1 : ℝ) * x.2) l Filter.atTop) :
    ∃ rTail rStep : ℕ × ℝ → ℝ,
      rTail =O[l] (fun x ↦ ((x.1 : ℝ) * x.2) ^ (s - (j : ℝ) * p + 1)) ∧
      rStep =O[l] (fun x ↦ x.2) ∧
      ∀ᶠ x in l, S_{p, j}^{s}(x.1, x.2) - I_{p, j}^{s} = rTail x + rStep x := by
  refine ⟨fun x ↦ S_{p, j}^{s}(x.1, x.2) - S_{p, j}^{s}(∞, x.2),
    fun x ↦ S_{p, j}^{s}(∞, x.2) - I_{p, j}^{s}, ?_, ?_, ?_⟩
  · -- The tail remainder is exactly the truncation error from finite to infinite quadrature.
    exact quadratureTail_isBigO_power hDecay
      (positive_p_of_decay hDecay (by linarith [hs])) hn hh hnh
  · -- The step remainder is exactly the infinite-series versus integral quadrature gap.
    exact quadratureSeriesGap_pos_isBigO hDecay hs hh
  · -- The two exact remainders telescope to the full quadrature error.
    refine Filter.Eventually.of_forall fun x ↦ ?_
    ring

/-- Proposition 7.19 (1), packaged as a single Big-O estimate for the
quadrature error. -/
theorem quadratureApproxPos_isBigO {l : Filter (ℕ × ℝ)} {p s : ℝ} {j : ℕ}
    (hDecay : 0 < (j : ℝ) * p - s - 1)
    (hs : 0 < s)
    (hn : Filter.Tendsto Prod.fst l Filter.atTop)
    (hh : Filter.Tendsto Prod.snd l (nhdsWithin (0 : ℝ) (Set.Ioi 0)))
    (hnh : Filter.Tendsto (fun x ↦ (x.1 : ℝ) * x.2) l Filter.atTop) :
    (fun x ↦ S_{p, j}^{s}(x.1, x.2) - I_{p, j}^{s}) =O[l]
      (fun x ↦ ‖((x.1 : ℝ) * x.2) ^ (s - (j : ℝ) * p + 1)‖ + ‖x.2‖) := by
  rcases quadratureApproxPos hDecay hs hn hh hnh with ⟨rTail, rStep, hTail, hStep, hEq⟩
  have hEq' :
      (fun x ↦ S_{p, j}^{s}(x.1, x.2) - I_{p, j}^{s}) =ᶠ[l] fun x ↦ rTail x + rStep x := by
    filter_upwards [hEq] with x hx
    simpa using hx
  exact hEq'.trans_isBigO (hTail.add_add hStep)

/-- Proposition 7.19 (2). If `-1 < s ≤ 0`, then the quadrature error
`S_{p,j}^s(n,h) - I_{p,j}^s` decomposes as
`O((nh)^(s - jp + 1)) + O(h^(s + 1))` along any filter with `n → ∞`,
`h → 0+`, and `n * h → ∞`. -/
theorem quadratureApproxNonpos {l : Filter (ℕ × ℝ)} {p s : ℝ} {j : ℕ}
    (hDecay : 0 < (j : ℝ) * p - s - 1)
    (hsLower : -1 < s)
    (hsUpper : s ≤ 0)
    (hn : Filter.Tendsto Prod.fst l Filter.atTop)
    (hh : Filter.Tendsto Prod.snd l (nhdsWithin (0 : ℝ) (Set.Ioi 0)))
    (hnh : Filter.Tendsto (fun x ↦ (x.1 : ℝ) * x.2) l Filter.atTop) :
    ∃ rTail rStep : ℕ × ℝ → ℝ,
      rTail =O[l] (fun x ↦ ((x.1 : ℝ) * x.2) ^ (s - (j : ℝ) * p + 1)) ∧
      rStep =O[l] (fun x ↦ x.2 ^ (s + 1)) ∧
      ∀ᶠ x in l, S_{p, j}^{s}(x.1, x.2) - I_{p, j}^{s} = rTail x + rStep x := by
  refine ⟨fun x ↦ S_{p, j}^{s}(x.1, x.2) - S_{p, j}^{s}(∞, x.2),
    fun x ↦ S_{p, j}^{s}(∞, x.2) - I_{p, j}^{s}, ?_, ?_, ?_⟩
  · -- The same tail truncation estimate applies in the nonpositive-`s` regime.
    exact quadratureTail_isBigO_power hDecay (positive_p_of_decay hDecay hsLower) hn hh hnh
  · -- The step remainder is the infinite-series versus integral gap for `-1 < s ≤ 0`.
    exact quadratureSeriesGap_nonpos_isBigO hDecay hsLower hsUpper hh
  · -- The exact decomposition is again a telescoping identity.
    refine Filter.Eventually.of_forall fun x ↦ ?_
    ring

/-- Proposition 7.19 (2), packaged as a single Big-O estimate for the
quadrature error. -/
theorem quadratureApproxNonpos_isBigO {l : Filter (ℕ × ℝ)} {p s : ℝ} {j : ℕ}
    (hDecay : 0 < (j : ℝ) * p - s - 1)
    (hsLower : -1 < s)
    (hsUpper : s ≤ 0)
    (hn : Filter.Tendsto Prod.fst l Filter.atTop)
    (hh : Filter.Tendsto Prod.snd l (nhdsWithin (0 : ℝ) (Set.Ioi 0)))
    (hnh : Filter.Tendsto (fun x ↦ (x.1 : ℝ) * x.2) l Filter.atTop) :
    (fun x ↦ S_{p, j}^{s}(x.1, x.2) - I_{p, j}^{s}) =O[l]
      (fun x ↦ ‖((x.1 : ℝ) * x.2) ^ (s - (j : ℝ) * p + 1)‖ + ‖x.2 ^ (s + 1)‖) := by
  rcases quadratureApproxNonpos hDecay hsLower hsUpper hn hh hnh with
    ⟨rTail, rStep, hTail, hStep, hEq⟩
  have hEq' :
      (fun x ↦ S_{p, j}^{s}(x.1, x.2) - I_{p, j}^{s}) =ᶠ[l] fun x ↦ rTail x + rStep x := by
    filter_upwards [hEq] with x hx
    simpa using hx
  exact hEq'.trans_isBigO (hTail.add_add hStep)

/-- Proposition 7.19 (3). If `s = -1`, then the quadrature error
`S_{p,j}^{-1}(n,h) + log h` is `O(1)` along any filter with `n → ∞`,
`h → 0+`, and `n * h → ∞`. -/
theorem quadratureApproxNegOne {l : Filter (ℕ × ℝ)} {p : ℝ} {j : ℕ}
    (hDecay : 0 < (j : ℝ) * p)
    (hn : Filter.Tendsto Prod.fst l Filter.atTop)
    (hh : Filter.Tendsto Prod.snd l (nhdsWithin (0 : ℝ) (Set.Ioi 0)))
    (hnh : Filter.Tendsto (fun x ↦ (x.1 : ℝ) * x.2) l Filter.atTop) :
    ∃ r : ℕ × ℝ → ℝ,
      r =O[l] (fun _ ↦ (1 : ℝ)) ∧
      ∀ᶠ x in l, S_{p, j}^{(-1 : ℝ)}(x.1, x.2) + Real.log x.2 = r x := by
  refine ⟨fun x ↦
      (S_{p, j}^{(-1 : ℝ)}(x.1, x.2) - S_{p, j}^{(-1 : ℝ)}(∞, x.2)) +
      (S_{p, j}^{(-1 : ℝ)}(∞, x.2) + Real.log x.2), ?_, ?_⟩
  · -- Combine the bounded finite-tail remainder with the bounded logarithmic renormalization.
    exact (quadratureTail_negOne_isBigO hDecay hn hh hnh).add
      (quadratureSeriesLogGap_isBigO hDecay hh)
  · -- The chosen remainder is definitionally the full logarithmic quadrature error.
    refine Filter.Eventually.of_forall fun x ↦ ?_
    ring

/-- Proposition 7.19 (3), packaged as a direct Big-O estimate for the
quadrature error. -/
theorem quadratureApproxNegOne_isBigO {l : Filter (ℕ × ℝ)} {p : ℝ} {j : ℕ}
    (hDecay : 0 < (j : ℝ) * p)
    (hn : Filter.Tendsto Prod.fst l Filter.atTop)
    (hh : Filter.Tendsto Prod.snd l (nhdsWithin (0 : ℝ) (Set.Ioi 0)))
    (hnh : Filter.Tendsto (fun x ↦ (x.1 : ℝ) * x.2) l Filter.atTop) :
    (fun x ↦ S_{p, j}^{(-1 : ℝ)}(x.1, x.2) + Real.log x.2) =O[l] (fun _ ↦ (1 : ℝ)) := by
  rcases quadratureApproxNegOne hDecay hn hh hnh with ⟨r, hr, hEq⟩
  have hEq' :
      (fun x ↦ S_{p, j}^{(-1 : ℝ)}(x.1, x.2) + Real.log x.2) =ᶠ[l] fun x ↦ r x := by
    filter_upwards [hEq] with x hx
    simpa using hx
  exact hEq'.trans_isBigO hr

end KernelMoment

end
