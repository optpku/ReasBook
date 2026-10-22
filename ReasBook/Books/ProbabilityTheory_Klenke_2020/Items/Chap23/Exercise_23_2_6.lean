/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib
import Books.ProbabilityTheory_Klenke_2020.Items.Chap03.Example_3_4
import Books.ProbabilityTheory_Klenke_2020.Items.Chap23.Definition_23_6
import Books.ProbabilityTheory_Klenke_2020.Items.Chap23.Definition_23_7

-- Declarations for this item will be appended below by the statement pipeline.

open Filter MeasureTheory ProbabilityTheory
open scoped ENNReal Topology

noncomputable section

namespace ProbabilityTheory

/-- Helper for Exercise 23.2.6: the positive-parameter filter is nontrivial because the right
neighborhoods of `0` on `(0, ∞)` are nonempty. -/
private instance positiveParameterFilter_neBot :
    NeBot (positiveParameterFilter : Filter PositiveParameter) := by
  rw [positiveParameterFilter]
  exact (show NeBot (𝓝[>] (0 : ℝ)) from inferInstance).comap_of_range_mem (by
    simpa [PositiveParameter, Subtype.range_coe] using
      (self_mem_nhdsWithin : Set.Ioi (0 : ℝ) ∈ 𝓝[>] (0 : ℝ)))

/-- Helper for Exercise 23.2.6: forgetting the positivity subtype identifies the chapter's
positive-parameter filter with the standard right-neighborhood filter at `0`. -/
private theorem map_positiveParameterFilter :
    Filter.map ((↑) : PositiveParameter → ℝ) positiveParameterFilter = 𝓝[>] (0 : ℝ) := by
  -- Proof comment: `positiveParameterFilter` is defined as the comap of the subtype coercion, and
  -- the coercion range is exactly `(0, ∞)`, which belongs to `𝓝[>] 0`.
  rw [positiveParameterFilter]
  refine Filter.map_comap_of_mem ?_
  simpa [PositiveParameter, Subtype.range_coe] using
    (self_mem_nhdsWithin : Set.Ioi (0 : ℝ) ∈ 𝓝[>] (0 : ℝ))

private def poissonScaling (ε : PositiveParameter) : ℕ → ℝ :=
  fun n ↦ ε * (n : ℝ)

private theorem poissonScaling_measurable (ε : PositiveParameter) :
    Measurable (poissonScaling ε) :=
  measurable_of_countable (poissonScaling ε)

/-- The family `μ_ε` obtained by pushing forward the Poisson law with parameter `λ / ε` under the
scaling map `n ↦ ε n`. -/
def poissonScaledLaw (lam : ℝ) : PositiveProbabilityFamily ℝ :=
  fun ε ↦
    ProbabilityMeasure.map
      (⟨poissonMeasure (Real.toNNReal (lam / (ε : ℝ))), inferInstance⟩ : ProbabilityMeasure ℕ)
      (poissonScaling_measurable ε).aemeasurable

/-- The Poisson Cramér rate function `x log (x / λ) + λ - x` on `[0, ∞)` and `∞` on `(-∞, 0)`. -/
def poissonScaledRateFunction (lam : ℝ) (x : ℝ) : ENNReal :=
  if 0 ≤ x then ENNReal.ofReal (x * Real.log (x / lam) + lam - x) else ⊤

/-- Helper for Exercise 23.2.6: the real-valued entropy branch rewritten in terms of `x * log x`,
which is continuous at `0`. -/
private def poissonScaledRateReal (lam x : ℝ) : ℝ :=
  x * Real.log x - x * Real.log lam + lam - x

/-- Helper for Exercise 23.2.6: on `[0, ∞)`, the continuous real branch agrees with the textbook
entropy formula `x * log (x / lam) + lam - x`. -/
private theorem poissonScaledRateReal_eq_branch {lam x : ℝ} (hlam : 0 < lam) (_hx : 0 ≤ x) :
    poissonScaledRateReal lam x = x * Real.log (x / lam) + lam - x := by
  -- Proof comment: split off the boundary point `x = 0`; away from `0`, `log (x / lam)` expands as
  -- `log x - log lam`, and the algebraic normalization is linear.
  by_cases hx0 : x = 0
  · simp [poissonScaledRateReal, hx0]
  · rw [poissonScaledRateReal]
    rw [Real.log_div hx0 hlam.ne']
    ring

/-- Helper for Exercise 23.2.6: the real-valued entropy branch is continuous on `ℝ`. -/
private theorem continuous_poissonScaledRateReal (lam : ℝ) :
    Continuous (poissonScaledRateReal lam) := by
  -- Proof comment: `x ↦ x * log x` is the canonical continuous replacement for the singular
  -- logarithmic term, and the remaining operations are affine.
  simpa [poissonScaledRateReal] using
    ((Real.continuous_mul_log.sub (continuous_id.mul_const (Real.log lam))).add_const lam).sub
      continuous_id

/-- Helper for Exercise 23.2.6: every finite sublevel of the Poisson rate lies in a bounded
interval depending only on the sublevel height and `lam`. -/
private theorem mem_poissonScaledRateFunction_sublevel_le_bound {lam x : ℝ} (hlam : 0 < lam)
    {a : NNReal} (hxrate : poissonScaledRateFunction lam x ≤ (a : ENNReal)) :
    x ≤ max ((a : ℝ) + 1) (lam * Real.exp 2) := by
  -- Proof comment: finite sublevel membership already excludes `x < 0`; if `x` were larger than
  -- both `a + 1` and `lam * exp 2`, then `log (x / lam) ≥ 2` would force the entropy cost above
  -- `a`, contradicting the sublevel hypothesis.
  have hxnonneg : 0 ≤ x := by
    by_contra hxneg
    have htop : poissonScaledRateFunction lam x = ⊤ := by
      simp [poissonScaledRateFunction, hxneg]
    simp [htop] at hxrate
  by_contra hxb
  have hbound_lt : max ((a : ℝ) + 1) (lam * Real.exp 2) < x := lt_of_not_ge hxb
  have hx_gt_a : (a : ℝ) < x := by
    have hx_gt_a1 : (a : ℝ) + 1 < x := lt_of_le_of_lt (le_max_left _ _) hbound_lt
    linarith
  have hlamexp_lt : lam * Real.exp 2 < x := lt_of_le_of_lt (le_max_right _ _) hbound_lt
  have hxpos : 0 < x := lt_trans (mul_pos hlam (Real.exp_pos 2)) hlamexp_lt
  have hratio_pos : 0 < x / lam := div_pos hxpos hlam
  have hratio_ge : Real.exp 2 ≤ x / lam := by
    exact le_of_lt ((lt_div_iff₀ hlam).2 (by simpa [mul_comm] using hlamexp_lt))
  have hlog_ge : 2 ≤ Real.log (x / lam) := by
    exact (Real.le_log_iff_exp_le hratio_pos).2 hratio_ge
  have hreal_le : x * Real.log (x / lam) + lam - x ≤ (a : ℝ) := by
    have hxrate' : ENNReal.ofReal (x * Real.log (x / lam) + lam - x) ≤ (a : ENNReal) := by
      simpa [poissonScaledRateFunction, hxnonneg] using hxrate
    exact ENNReal.ofReal_le_coe.mp hxrate'
  have hreal_gt : (a : ℝ) < x * Real.log (x / lam) + lam - x := by
    nlinarith
  linarith

/-- Helper for Exercise 23.2.6: the finite sublevel sets of `poissonScaledRateFunction lam` are
compact. -/
private theorem poissonScaledRateFunction_compactSublevel {lam : ℝ} (hlam : 0 < lam)
    (a : NNReal) :
    IsCompact (poissonScaledRateFunction lam ⁻¹' Set.Iic (a : ENNReal)) := by
  let B : ℝ := max ((a : ℝ) + 1) (lam * Real.exp 2)
  have hsublevel :
      poissonScaledRateFunction lam ⁻¹' Set.Iic (a : ENNReal) =
        Set.Icc 0 B ∩ poissonScaledRateReal lam ⁻¹' Set.Iic (a : ℝ) := by
    -- Proof comment: finite sublevel points are nonnegative and bounded by the previous lemma;
    -- on that nonnegative branch, the rate reduces to the continuous real formula.
    ext x
    constructor
    · intro hx
      have hxrate : poissonScaledRateFunction lam x ≤ (a : ENNReal) := by
        simpa [Set.mem_preimage] using hx
      have hxnonneg : 0 ≤ x := by
        by_contra hxneg
        have htop : poissonScaledRateFunction lam x = ⊤ := by
          simp [poissonScaledRateFunction, hxneg]
        simp [htop] at hxrate
      have hxleB : x ≤ B := mem_poissonScaledRateFunction_sublevel_le_bound hlam hxrate
      have hreal : poissonScaledRateReal lam x ≤ (a : ℝ) := by
        have hbranch : x * Real.log (x / lam) + lam - x ≤ (a : ℝ) := by
          have hxrate' : ENNReal.ofReal (x * Real.log (x / lam) + lam - x) ≤ (a : ENNReal) := by
            simpa [poissonScaledRateFunction, hxnonneg] using hxrate
          exact ENNReal.ofReal_le_coe.mp hxrate'
        rw [poissonScaledRateReal_eq_branch hlam hxnonneg]
        exact hbranch
      exact ⟨⟨hxnonneg, hxleB⟩, hreal⟩
    · rintro ⟨hxB, hreal⟩
      have hreal' : poissonScaledRateReal lam x ≤ (a : ℝ) := by
        simpa [Set.mem_preimage] using hreal
      simpa [Set.mem_preimage, poissonScaledRateFunction, hxB.1,
        poissonScaledRateReal_eq_branch hlam hxB.1] using hreal'
  rw [hsublevel]
  have hclosed : IsClosed (poissonScaledRateReal lam ⁻¹' Set.Iic (a : ℝ)) := by
    -- Proof comment: the sublevel of the continuous real branch is closed, so intersecting with a
    -- compact interval yields compactness.
    exact IsClosed.preimage (continuous_poissonScaledRateReal lam) isClosed_Iic
  exact isCompact_Icc.inter_right hclosed

-- Proof sketch: unfold `poissonScaledRateFunction`; under the hypothesis `0 ≤ x`, the defining
-- `if` takes its finite branch.
/-- On `[0, ∞)`, `poissonScaledRateFunction` is given by the explicit Poisson entropy formula. -/
theorem poissonScaledRateFunction_of_nonneg (lam : ℝ) {x : ℝ} (hx : 0 ≤ x) :
    poissonScaledRateFunction lam x = ENNReal.ofReal (x * Real.log (x / lam) + lam - x) := by
  -- Proof comment: the sign hypothesis selects the finite branch of the defining `if`.
  simp [poissonScaledRateFunction, hx]

-- Proof sketch: verify lower semicontinuity of the explicit formula on `[0, ∞)`, show that every
-- finite sublevel set is closed and bounded, and conclude compactness by Heine-Borel.
/-- The explicit Poisson Cramér rate function is a good rate function for every positive
parameter `λ`. -/
theorem poissonScaledRateFunction_isGoodRateFunction {lam : ℝ} (hlam : 0 < lam) :
    IsGoodRateFunction (poissonScaledRateFunction lam) := by
  refine ⟨?_, ?_⟩
  · -- Proof comment: lower semicontinuity follows because every finite sublevel is compact, hence
    -- closed, while the infinite sublevel is all of `ℝ`.
    rw [lowerSemicontinuous_iff_isClosed_preimage]
    intro a
    by_cases ha : a = ⊤
    · simp [ha]
    · rw [← ENNReal.ofReal_toReal ha]
      simpa [ENNReal.coe_nnreal_eq] using
        (poissonScaledRateFunction_compactSublevel hlam
          ⟨a.toReal, ENNReal.toReal_nonneg⟩).isClosed
  · -- Proof comment: the compact sublevel lemma gives the finite-level compactness field
    -- directly.
    intro a
    exact poissonScaledRateFunction_compactSublevel hlam a

/-- Helper for Exercise 23.2.6: the singleton mass of `poissonMeasure r` is the explicit Poisson
weight `poissonPMFReal r n`. -/
private theorem poissonMeasure_apply_singleton_eq (r : NNReal) (n : ℕ) :
    poissonMeasure r ({n} : Set ℕ) = ENNReal.ofReal (poissonPMFReal r n) := by
  -- Proof comment: rewrite the Poisson measure through its underlying probability mass function.
  simpa [poissonMeasure, poissonPMFReal_ofReal_eq_poissonPMF] using
    (PMF.toMeasure_apply_singleton (poissonPMF r) n (measurableSet_singleton n))

/-- Helper for Exercise 23.2.6: the scaled Poisson law assigns the lattice atom `{ε n}` the
corresponding Poisson singleton mass at parameter `λ / ε`. -/
private theorem poissonScaledLaw_apply_singleton_scaled {lam : ℝ} (hlam : 0 < lam)
    (ε : PositiveParameter) (n : ℕ) :
    (poissonScaledLaw lam ε : Measure ℝ) ({((ε : ℝ) * n : ℝ)} : Set ℝ) =
      ENNReal.ofReal
        (poissonPMFReal (Real.toNNReal (lam / (ε : ℝ))) n) := by
  let _ := hlam
  have hεpos : 0 < (ε : ℝ) := ε.2
  have hpreimage :
      poissonScaling ε ⁻¹' ({((ε : ℝ) * n : ℝ)} : Set ℝ) = ({n} : Set ℕ) := by
    -- Proof comment: positive scaling on `ℕ` has the unique preimage `n` above the atom `ε n`.
    ext m
    simp [poissonScaling, mul_right_inj' (show (ε : ℝ) ≠ 0 from (ne_of_gt hεpos))]
  -- Proof comment: unfold the pushforward law and rewrite the singleton preimage through the
  -- explicit Poisson point mass.
  rw [poissonScaledLaw, ProbabilityMeasure.map_apply' _ (poissonScaling_measurable ε).aemeasurable
    (measurableSet_singleton _), hpreimage]
  exact poissonMeasure_apply_singleton_eq (Real.toNNReal (lam / (ε : ℝ))) n

/-- Helper for Exercise 23.2.6: for `x ≥ 0`, the upper lattice point
`ε * ceil (x / ε)` stays within the interval `[x, x + ε)`. -/
private theorem scaledCeil_mem_Icc {x : ℝ} (hx : 0 ≤ x) (ε : PositiveParameter) :
    x ≤ (ε : ℝ) * Nat.ceil (x / (ε : ℝ)) ∧
      (ε : ℝ) * Nat.ceil (x / (ε : ℝ)) < x + ε := by
  have hεpos : 0 < (ε : ℝ) := ε.2
  constructor
  · have hceil : x / (ε : ℝ) ≤ Nat.ceil (x / (ε : ℝ)) := Nat.le_ceil _
    have hmul := mul_le_mul_of_nonneg_left hceil (le_of_lt hεpos)
    simpa [hεpos.ne', div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hmul
  · have hceil : (Nat.ceil (x / (ε : ℝ)) : ℝ) < x / (ε : ℝ) + 1 := by
      exact Nat.ceil_lt_add_one (show 0 ≤ x / (ε : ℝ) by positivity)
    have hscaled : (ε : ℝ) * (Nat.ceil (x / (ε : ℝ)) : ℝ) < x + ε := by
      have hmul := mul_lt_mul_of_pos_left hceil hεpos
      have hEq : (ε : ℝ) * (x / (ε : ℝ) + 1) = x + ε := by
        field_simp [hεpos.ne']
      rw [hEq] at hmul
      exact hmul
    simpa using hscaled

/-- Helper for Exercise 23.2.6: a summable singleton-mass weighted norm series on `ℕ` gives an
integrable function for the corresponding countable measure. -/
private theorem integrable_natMeasure_of_summableNorm (μ : Measure ℕ) [IsFiniteMeasure μ]
    (f : ℕ → ℝ) (hf : Summable (fun n : ℕ ↦ (μ {n}).toReal * ‖f n‖)) :
    Integrable f μ := by
  refine ⟨(measurable_of_countable f).aestronglyMeasurable, ?_⟩
  -- Proof comment: expand the norm integral through the atomic decomposition
  -- `μ = ∑ n, μ {n} • dirac n`, then use the assumed summability of the singleton series.
  rw [hasFiniteIntegral_iff_norm, ← Measure.sum_smul_dirac (μ := μ), lintegral_sum_measure]
  have hterm :
      (fun n : ℕ ↦ ∫⁻ a, ENNReal.ofReal ‖f a‖ ∂μ {n} • Measure.dirac n) =
        fun n : ℕ ↦ ENNReal.ofReal ((μ {n}).toReal * ‖f n‖) := by
    funext n
    rw [lintegral_smul_measure, lintegral_dirac, smul_eq_mul]
    have hmass : μ {n} = ENNReal.ofReal (μ {n}).toReal :=
      (ENNReal.ofReal_toReal (measure_ne_top _ _)).symm
    calc
      μ {n} * ENNReal.ofReal ‖f n‖ = ENNReal.ofReal (μ {n}).toReal * ENNReal.ofReal ‖f n‖ := by
        simpa using congrArg (fun t : ℝ≥0∞ ↦ t * ENNReal.ofReal ‖f n‖) hmass
      _ = ENNReal.ofReal ((μ {n}).toReal * ‖f n‖) := by
        simpa using (ENNReal.ofReal_mul (p := (μ {n}).toReal) (q := ‖f n‖)
          (norm_nonneg _)).symm
  rw [hterm, ← ENNReal.ofReal_tsum_of_nonneg (fun n ↦ by positivity) hf]
  simp

/-- Helper for Exercise 23.2.6: the exact moment generating function of `ε X_(λ / ε)` at slope
`t / ε` is the Poisson exponential `exp ((λ / ε) (e^t - 1))`. -/
private theorem poissonScaledLaw_mgf {lam t : ℝ} (hlam : 0 < lam) (ε : PositiveParameter) :
    mgf id (poissonScaledLaw lam ε) (t / (ε : ℝ)) =
      Real.exp ((lam / (ε : ℝ)) * (Real.exp t - 1)) := by
  let r : NNReal := Real.toNNReal (lam / (ε : ℝ))
  have hmap := congrFun (mgf_id_map (μ := poissonMeasure r) (X := poissonScaling ε)
    (poissonScaling_measurable ε).aemeasurable) (t / (ε : ℝ))
  have hseries :
      HasSum (fun n : ℕ ↦ Real.exp (-((r : ℝ))) * (((r : ℝ) * Real.exp t) ^ n / ↑n.factorial))
        (Real.exp (-((r : ℝ))) * Real.exp ((r : ℝ) * Real.exp t)) := by
    simpa [Real.exp_eq_exp_ℝ] using
      (NormedSpace.expSeries_div_hasSum_exp ((r : ℝ) * Real.exp t)).mul_left
        (Real.exp (-((r : ℝ))))
  have hsummable :
      Summable (fun n : ℕ ↦
        (poissonMeasure r {n}).toReal * ‖Real.exp ((t / (ε : ℝ)) * poissonScaling ε n)‖) := by
    refine hseries.summable.congr ?_
    intro n
    rw [poissonMeasure_apply_singleton_eq]
    rw [ENNReal.toReal_ofReal poissonPMFReal_nonneg, poissonPMFReal]
    have hεne : (ε : ℝ) ≠ 0 := ne_of_gt ε.2
    have hfac : (↑n.factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)
    rw [Real.norm_of_nonneg (Real.exp_nonneg _)]
    have hscale : (t / (ε : ℝ)) * poissonScaling ε n = t * (n : ℝ) := by
      dsimp [poissonScaling]
      field_simp [hεne]
    rw [hscale, mul_comm t (n : ℝ), Real.exp_nat_mul, mul_pow]
    field_simp [hfac]
  have hint :
      Integrable (fun n : ℕ ↦ Real.exp ((t / (ε : ℝ)) * poissonScaling ε n)) (poissonMeasure r) := by
    exact integrable_natMeasure_of_summableNorm (μ := poissonMeasure r) _ hsummable
  -- Proof comment: rewrite the pushforward mgf as a discrete Poisson integral, expand that
  -- integral as a singleton-weighted series, and collapse it with the exponential power series.
  calc
    mgf id (poissonScaledLaw lam ε) (t / (ε : ℝ))
      = mgf (poissonScaling ε) (poissonMeasure r) (t / (ε : ℝ)) := by
          simpa [poissonScaledLaw, r] using hmap
    _ = ∫ n, Real.exp ((t / (ε : ℝ)) * poissonScaling ε n) ∂poissonMeasure r := by
          rfl
    _ = ∑' n : ℕ, ((poissonMeasure r) {n}).toReal *
          Real.exp ((t / (ε : ℝ)) * poissonScaling ε n) := by
          simpa [Measure.real, smul_eq_mul] using
            (integral_countable (μ := poissonMeasure r) hint)
    _ = ∑' n : ℕ, Real.exp (-((r : ℝ))) * (((r : ℝ) * Real.exp t) ^ n / ↑n.factorial) := by
          refine tsum_congr fun n ↦ ?_
          rw [poissonMeasure_apply_singleton_eq]
          rw [ENNReal.toReal_ofReal poissonPMFReal_nonneg, poissonPMFReal]
          have hεne : (ε : ℝ) ≠ 0 := ne_of_gt ε.2
          have hfac : (↑n.factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)
          have hscale : (t / (ε : ℝ)) * poissonScaling ε n = t * (n : ℝ) := by
            dsimp [poissonScaling]
            field_simp [hεne]
          rw [hscale, mul_comm t (n : ℝ), Real.exp_nat_mul, mul_pow]
          field_simp [hfac]
    _ = Real.exp (-((r : ℝ))) * Real.exp ((r : ℝ) * Real.exp t) := hseries.tsum_eq
    _ = Real.exp ((r : ℝ) * (Real.exp t - 1)) := by
          rw [← Real.exp_add]
          congr 1
          ring
    _ = Real.exp ((lam / (ε : ℝ)) * (Real.exp t - 1)) := by
          have hnonneg : 0 ≤ lam / (ε : ℝ) := le_of_lt (div_pos hlam ε.2)
          have hr : (r : ℝ) = lam / (ε : ℝ) := by
            simpa [r] using congrArg NNReal.toReal (Real.toNNReal_of_nonneg hnonneg)
          rw [hr]

/-- Helper for Exercise 23.2.6: every affine Poisson-Chernoff exponent lies below the explicit
rate function. -/
private theorem poissonAffine_le_rateFunction {lam x t : ℝ} (hlam : 0 < lam) :
    (((t * x - lam * (Real.exp t - 1) : ℝ) : EReal)) ≤
      (((poissonScaledRateFunction lam x : ENNReal) : EReal)) := by
  by_cases hxneg : x < 0
  · have hxnot : ¬ 0 ≤ x := not_le.mpr hxneg
    -- Proof comment: on `(-∞, 0)`, the rate is `⊤`, so the extended-real comparison is trivial.
    simp [poissonScaledRateFunction, hxnot]
  · have hxnonneg : 0 ≤ x := le_of_not_gt hxneg
    rw [poissonScaledRateFunction_of_nonneg lam hxnonneg]
    by_cases hx0 : x = 0
    · subst hx0
      -- Proof comment: at `x = 0`, the inequality reduces to the positivity of `exp t`.
      have hzero : -lam * (Real.exp t - 1) ≤ lam := by
        nlinarith [show 0 ≤ Real.exp t by positivity]
      have hzeroE : (((-lam * (Real.exp t - 1) : ℝ) : EReal)) ≤ ((lam : ℝ) : EReal) := by
        exact_mod_cast hzero
      simpa [hlam.le] using hzeroE
    · have hxpos : 0 < x := lt_of_le_of_ne hxnonneg (Ne.symm hx0)
      have hratio_pos : 0 < (lam * Real.exp t) / x := by
        positivity
      have hlog : t - Real.log (x / lam) ≤ (lam * Real.exp t) / x - 1 := by
        have hmain := Real.log_le_sub_one_of_pos hratio_pos
        have hrewrite : Real.log ((lam * Real.exp t) / x) = t - Real.log (x / lam) := by
          rw [Real.log_div (by positivity) hx0]
          rw [Real.log_mul hlam.ne' (Real.exp_pos t).ne']
          rw [Real.log_exp, Real.log_div hx0 hlam.ne']
          ring
        rw [hrewrite] at hmain
        exact hmain
      have hmul : x * (t - Real.log (x / lam)) ≤ x * ((lam * Real.exp t) / x - 1) := by
        exact mul_le_mul_of_nonneg_left hlog hxnonneg
      have hmul_right : x * ((lam * Real.exp t) / x - 1) = lam * Real.exp t - x := by
        field_simp [hx0]
      have hreal : t * x - lam * (Real.exp t - 1) ≤ x * Real.log (x / lam) + lam - x := by
        -- Proof comment: multiply the logarithmic inequality by `x > 0` and normalize the two
        -- affine sides into the target real inequality.
        rw [hmul_right] at hmul
        nlinarith [hmul]
      have hmain := Real.one_sub_inv_le_log_of_pos (div_pos hxpos hlam)
      have hmain' : 1 - lam / x ≤ Real.log (x / lam) := by
        simpa [div_eq_mul_inv, hx0, hlam.ne'] using hmain
      have hmul' : x * (1 - lam / x) ≤ x * Real.log (x / lam) := by
        exact mul_le_mul_of_nonneg_left hmain' hxnonneg
      have hmul_left : x * (1 - lam / x) = x - lam := by
        field_simp [hx0]
      have hrate_nonneg : 0 ≤ x * Real.log (x / lam) + lam - x := by
        -- Proof comment: the standard bound `1 - 1/u ≤ log u` at `u = x / λ` yields the
        -- nonnegativity needed to replace `ENNReal.ofReal` by a real cast in `EReal`.
        rw [hmul_left] at hmul'
        linarith
      have hgoal :
          (((ENNReal.ofReal (x * Real.log (x / lam) + lam - x) : ENNReal) : EReal)) =
            ((x * Real.log (x / lam) + lam - x : ℝ) : EReal) := by
        simp [hrate_nonneg]
      rw [hgoal]
      exact_mod_cast hreal

/-- Helper for Exercise 23.2.6: for the logarithmic mass, the union of two events costs only the
vanishing penalty `ε log 2` on top of the larger exponent. -/
private theorem scaledLogMassAlong_union_le_logTwo_add_max
    {E : Type*} [MeasurableSpace E] {ι : Type*}
    (μ : ι → Measure E) (ε : ι → PositiveParameter) (s t : Set E) (i : ι) :
    scaledLogMassAlong μ ε (s ∪ t) i ≤
      ((((ε i : ℝ) * Real.log 2 : ℝ) : EReal)) +
        max (scaledLogMassAlong μ ε s i) (scaledLogMassAlong μ ε t i) := by
  let α : EReal := ((ε i : ℝ) : EReal)
  let a : ℝ≥0∞ := μ i s
  let b : ℝ≥0∞ := μ i t
  have hα : (0 : EReal) ≤ α := by
    have hα_real : 0 ≤ (ε i : ℝ) := le_of_lt (show 0 < (ε i : ℝ) from (ε i).2)
    simpa [α] using (show (0 : EReal) ≤ ((ε i : ℝ) : EReal) from by
      exact_mod_cast hα_real)
  have hUnionMass : μ i (s ∪ t) ≤ a + b := by
    simpa [a, b] using measure_union_le s t (μ := μ i)
  have hAddLe : a + b ≤ (2 : ℝ≥0∞) * max a b := by
    calc
      a + b ≤ max a b + max a b := by
        exact add_le_add (le_max_left _ _) (le_max_right _ _)
      _ = (2 : ℝ≥0∞) * max a b := by
        simp [two_mul]
  have hLog :
      ENNReal.log (μ i (s ∪ t)) ≤ ENNReal.log ((2 : ℝ≥0∞) * max a b) := by
    exact ENNReal.log_monotone (hUnionMass.trans hAddLe)
  have hMul :
      α * ENNReal.log (μ i (s ∪ t)) ≤ α * ENNReal.log ((2 : ℝ≥0∞) * max a b) := by
    exact mul_le_mul_of_nonneg_left hLog hα
  have hα_ne_top : α ≠ ⊤ := by
    simp [α]
  have hlogTwo :
      ENNReal.log (2 : ℝ≥0∞) = ((Real.log 2 : ℝ) : EReal) := by
    rw [show (2 : ℝ≥0∞) = ENNReal.ofReal (2 : ℝ) by norm_num]
    simpa using (ENNReal.log_ofReal_of_pos (show 0 < (2 : ℝ) by norm_num))
  rw [scaledLogMassAlong_def, scaledLogMassAlong_def, scaledLogMassAlong_def]
  refine le_trans hMul ?_
  rw [ENNReal.log_mul_add, EReal.left_distrib_of_nonneg_of_ne_top hα hα_ne_top, hlogTwo]
  rcases le_total a b with hab | hba
  · -- Proof comment: when the right event has larger mass, the dominant exponent is the right
    -- one and the union only contributes the additive `ε log 2` penalty.
    have hmono : α * ENNReal.log a ≤ α * ENNReal.log b := by
      exact mul_le_mul_of_nonneg_left (ENNReal.log_monotone hab) hα
    rw [max_eq_right hab, max_eq_right hmono]
    simpa [α, mul_comm, mul_left_comm, mul_assoc]
  · -- Proof comment: the symmetric branch uses the left event as the dominant mass.
    have hmono : α * ENNReal.log b ≤ α * ENNReal.log a := by
      exact mul_le_mul_of_nonneg_left (ENNReal.log_monotone hba) hα
    rw [max_eq_left hba, max_eq_left hmono]
    simpa [α, mul_comm, mul_left_comm, mul_assoc]

/-- Helper for Exercise 23.2.6: every scaled logarithmic mass is nonpositive for a probability
family, since event masses are at most `1`. -/
private theorem scaledLogMassAlong_nonpos_of_probability
    {E : Type*} [MeasurableSpace E] {ι : Type*}
    (μ : ι → Measure E) [∀ i, IsProbabilityMeasure (μ i)]
    (ε : ι → PositiveParameter) (s : Set E) (i : ι) :
    scaledLogMassAlong μ ε s i ≤ 0 := by
  -- Proof comment: event masses are bounded by `1`, so their logarithms are nonpositive; the
  -- positive scale factor preserves that inequality.
  rw [scaledLogMassAlong_def]
  have hs_le_one : μ i s ≤ 1 := by
    calc
      μ i s ≤ μ i Set.univ := measure_mono (by simp)
      _ = 1 := by simpa using (IsProbabilityMeasure.measure_univ (μ := μ i))
  have hlog_nonpos : ENNReal.log (μ i s) ≤ 0 := by
    rw [ENNReal.log_le_zero_iff]
    exact hs_le_one
  have hε_nonneg : (0 : EReal) ≤ ((ε i : ℝ) : EReal) := by
    exact_mod_cast le_of_lt (ε i).2
  calc
    ((ε i : ℝ) : EReal) * ENNReal.log (μ i s) ≤ ((ε i : ℝ) : EReal) * 0 := by
      exact mul_le_mul_of_nonneg_left hlog_nonpos hε_nonneg
    _ = 0 := by simp

/-- Helper for Exercise 23.2.6: enlarging an event can only increase the scaled logarithmic
mass. -/
private theorem scaledLogMassAlong_mono_of_subset
    {E : Type*} [MeasurableSpace E] {ι : Type*}
    (μ : ι → Measure E) (ε : ι → PositiveParameter) {s t : Set E}
    (hst : s ⊆ t) (i : ι) :
    scaledLogMassAlong μ ε s i ≤ scaledLogMassAlong μ ε t i := by
  -- Proof comment: measure and `ENNReal.log` are monotone, and the scale parameter is
  -- nonnegative.
  rw [scaledLogMassAlong_def, scaledLogMassAlong_def]
  have hlog : ENNReal.log (μ i s) ≤ ENNReal.log (μ i t) := by
    exact ENNReal.log_monotone (measure_mono hst)
  have hε_nonneg : (0 : EReal) ≤ ((ε i : ℝ) : EReal) := by
    exact_mod_cast le_of_lt (ε i).2
  exact mul_le_mul_of_nonneg_left hlog hε_nonneg

/-- Helper for Exercise 23.2.6: the explicit Poisson rate is always nonnegative. -/
private theorem poissonScaledRateFunction_nonneg {lam x : ℝ} (hlam : 0 < lam) :
    (0 : EReal) ≤ (((poissonScaledRateFunction lam x : ENNReal) : EReal)) := by
  -- Proof comment: the affine lower bound at tilt `t = 0` is exactly `0`.
  simpa using (poissonAffine_le_rateFunction (hlam := hlam) (x := x) (t := 0))

/-- Helper for Exercise 23.2.6: the Poisson rate vanishes at its minimizer `x = λ`. -/
private theorem poissonScaledRateFunction_at_mean {lam : ℝ} (hlam : 0 < lam) :
    poissonScaledRateFunction lam lam = 0 := by
  -- Proof comment: substituting `x = λ` collapses the entropy term to `λ log 1 + λ - λ = 0`.
  rw [poissonScaledRateFunction_of_nonneg lam hlam.le]
  have hdiv : lam / lam = 1 := by field_simp [hlam.ne']
  simp [hdiv]

/-- Helper for Exercise 23.2.6: if a closed set misses the minimizer `λ`, then it is contained in
two closed tails separated by a neighborhood of `λ`. -/
private theorem exists_tailCover_of_isClosed_of_not_mem_mean {lam : ℝ} (hlam : 0 < lam)
    {C : Set ℝ} (hC : IsClosed C) (hlamC : lam ∉ C) :
    ∃ a b : ℝ, 0 < a ∧ a < lam ∧ lam < b ∧ C ⊆ Set.Iic a ∪ Set.Ici b := by
  have hnhds : Cᶜ ∈ 𝓝 lam := hC.isOpen_compl.mem_nhds hlamC
  rw [Metric.mem_nhds_iff] at hnhds
  rcases hnhds with ⟨r, hrpos, hrsub⟩
  let δ : ℝ := min r lam
  have hδpos : 0 < δ := by
    exact lt_min hrpos hlam
  refine ⟨lam - δ / 2, lam + δ / 2, ?_, ?_, ?_, ?_⟩
  · have hδle : δ ≤ lam := min_le_right _ _
    linarith
  · linarith
  · linarith
  · intro x hxC
    by_cases hxLeft : x ≤ lam - δ / 2
    · exact Or.inl hxLeft
    · by_cases hxRight : lam + δ / 2 ≤ x
      · exact Or.inr hxRight
      · have hxNear : |x - lam| < δ / 2 := by
          rw [abs_lt]
          constructor <;> linarith
        have hxBall : x ∈ Metric.ball lam r := by
          rw [Metric.mem_ball, Real.dist_eq]
          have hδle : δ ≤ r := min_le_left _ _
          linarith
        exfalso
        exact (hrsub hxBall) hxC

/-- Helper for Exercise 23.2.6: every scaled Poisson law is supported on `[0, ∞)`, so its mass on
`(-∞, 0)` vanishes. -/
private theorem poissonScaledLaw_Iio_zero {lam : ℝ} (ε : PositiveParameter) :
    (poissonScaledLaw lam ε : Measure ℝ) (Set.Iio 0) = 0 := by
  have hpreimage : poissonScaling ε ⁻¹' (Set.Iio (0 : ℝ)) = (∅ : Set ℕ) := by
    ext n
    have hnonneg : 0 ≤ (ε : ℝ) * (n : ℝ) := by
      exact mul_nonneg (le_of_lt ε.2) (Nat.cast_nonneg n)
    simp [poissonScaling, not_lt.mpr hnonneg]
  -- Proof comment: every lattice atom `ε n` is nonnegative, so the pushforward measure of the
  -- negative half-line is the Poisson mass of the empty preimage.
  rw [poissonScaledLaw,
    ProbabilityMeasure.map_apply' _ (poissonScaling_measurable ε).aemeasurable measurableSet_Iio,
    hpreimage]
  simp

/-- Helper for Exercise 23.2.6: Poisson masses satisfy the standard first-moment shift identity. -/
private lemma poissonPMFReal_succ_mul (μ : NNReal) (n : ℕ) :
    poissonPMFReal μ (n + 1) * (n + 1 : ℝ) = (μ : ℝ) * poissonPMFReal μ n := by
  -- Proof comment: rewrite the `(n + 1)`-st Poisson mass by separating one power of `μ`
  -- and one factorial factor.
  rw [poissonPMFReal, poissonPMFReal, pow_succ, Nat.factorial_succ]
  have hfac : ((n.factorial : ℕ) : ℝ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero n
  field_simp [hfac]
  norm_num [Nat.cast_add, Nat.cast_mul]
  ring

/-- Helper for Exercise 23.2.6: the two-step Poisson shift gives the factorial second-moment
identity at the level of coefficients. -/
private lemma poissonPMFReal_twoStep_mul (μ : NNReal) (n : ℕ) :
    poissonPMFReal μ (n + 2) * ((n + 2 : ℝ) * (n + 1 : ℝ)) =
      (μ : ℝ) ^ (2 : ℕ) * poissonPMFReal μ n := by
  -- Proof comment: apply the one-step identity twice and regroup the scalar factors.
  have htmp := poissonPMFReal_succ_mul μ (n + 1)
  have hsucc :
      poissonPMFReal μ (n + 2) * (n + 2 : ℝ) = (μ : ℝ) * poissonPMFReal μ (n + 1) := by
    norm_num [Nat.succ_eq_add_one, add_assoc] at htmp ⊢
    exact htmp
  calc
    poissonPMFReal μ (n + 2) * ((n + 2 : ℝ) * (n + 1 : ℝ))
      = (poissonPMFReal μ (n + 2) * (n + 2 : ℝ)) * (n + 1 : ℝ) := by ring
    _ = ((μ : ℝ) * poissonPMFReal μ (n + 1)) * (n + 1 : ℝ) := by rw [hsucc]
    _ = (μ : ℝ) * (poissonPMFReal μ (n + 1) * (n + 1 : ℝ)) := by ring
    _ = (μ : ℝ) * ((μ : ℝ) * poissonPMFReal μ n) := by
          rw [poissonPMFReal_succ_mul μ n]
    _ = (μ : ℝ) ^ (2 : ℕ) * poissonPMFReal μ n := by ring

/-- Helper for Exercise 23.2.6: the Poisson first-moment series is summable after shifting it to
the mass series with the one-step recursion. -/
private lemma summablePoissonFirstMoment (μ : NNReal) :
    Summable (fun n : ℕ ↦ poissonPMFReal μ n * (n : ℝ)) := by
  -- Proof comment: the shifted first-moment series agrees termwise with `(μ : ℝ)` times the
  -- summable Poisson mass series.
  have hshift :
      Summable (fun n : ℕ ↦ poissonPMFReal μ (n + 1) * ((n + 1 : ℕ) : ℝ)) := by
    have hbase : Summable (fun n : ℕ ↦ (μ : ℝ) * poissonPMFReal μ n) :=
      (poissonPMFRealSum μ).summable.mul_left (μ : ℝ)
    refine hbase.congr ?_
    intro n
    simpa using (poissonPMFReal_succ_mul μ n).symm
  exact (summable_nat_add_iff 1).mp <| by
    simpa [Nat.succ_eq_add_one] using hshift

/-- Helper for Exercise 23.2.6: the two-step Poisson recursion directly identifies the shifted
factorial second-moment series with `μ²` times the Poisson mass series. -/
private lemma hasSumPoissonShiftedFactorialSecondMoment (μ : NNReal) :
    HasSum
      (fun n : ℕ ↦ poissonPMFReal μ (n + 2) * ((n + 2 : ℝ) * (n + 1 : ℝ)))
      ((μ : ℝ) ^ (2 : ℕ)) := by
  -- Proof comment: the shifted series is exactly `μ²` times the mass series termwise.
  have hbase :
      HasSum (fun n : ℕ ↦ (μ : ℝ) ^ (2 : ℕ) * poissonPMFReal μ n) ((μ : ℝ) ^ (2 : ℕ)) := by
    simpa using (poissonPMFRealSum μ).mul_left ((μ : ℝ) ^ (2 : ℕ))
  simpa [poissonPMFReal_twoStep_mul, Nat.succ_eq_add_one, add_assoc] using hbase

/-- Helper for Exercise 23.2.6: the factorial second-moment series is summable after shifting by
two indices and using the stable shifted `HasSum` normal form. -/
private lemma summablePoissonFactorialSecondMoment (μ : NNReal) :
    Summable (fun n : ℕ ↦ poissonPMFReal μ n * ((n : ℝ) * ((n : ℝ) - 1))) := by
  -- Proof comment: the shifted tail is summable because it already has a `HasSum`; shifting back
  -- by two indices recovers the original factorial-moment series.
  have hshifted :
      Summable (fun n : ℕ ↦ poissonPMFReal μ (n + 2) * ((n + 2 : ℝ) * (n + 1 : ℝ))) :=
    (hasSumPoissonShiftedFactorialSecondMoment μ).summable
  have htail :
      Summable
        (fun n : ℕ ↦
          poissonPMFReal μ (n + 2) * (((n + 2 : ℕ) : ℝ) * (((n + 2 : ℕ) : ℝ) - 1))) := by
    refine hshifted.congr ?_
    intro n
    have hrewrite :
        (((n + 2 : ℕ) : ℝ) * (((n + 2 : ℕ) : ℝ) - 1)) = (n + 2 : ℝ) * (n + 1 : ℝ) := by
      have hcast2 : (((n + 2 : ℕ) : ℝ)) = (n : ℝ) + 2 := by
        norm_num [Nat.cast_add]
      rw [hcast2]
      ring
    rw [hrewrite]
  exact (_root_.summable_nat_add_iff
      (f := fun n : ℕ ↦ poissonPMFReal μ n * ((n : ℝ) * ((n : ℝ) - 1))) 2).mp <| by
    simpa [Nat.succ_eq_add_one, add_assoc] using htail

/-- Helper for Exercise 23.2.6: the Poisson first moment equals the rate parameter. -/
private lemma poissonFirstMoment_eq (μ : NNReal) :
    ∑' n : ℕ, poissonPMFReal μ n * (n : ℝ) = (μ : ℝ) := by
  -- Proof comment: peel off the zero term and rewrite the remaining tail by the one-step
  -- coefficient identity.
  have hs : Summable (fun n : ℕ ↦ poissonPMFReal μ n * (n : ℝ)) :=
    summablePoissonFirstMoment μ
  rw [← hs.sum_add_tsum_nat_add 1]
  simp
  calc
    ∑' n : ℕ, poissonPMFReal μ (n + 1) * ((n : ℝ) + 1)
      = ∑' n : ℕ, (μ : ℝ) * poissonPMFReal μ n := by
          refine tsum_congr fun n ↦ ?_
          simpa using poissonPMFReal_succ_mul μ n
    _ = (μ : ℝ) * ∑' n : ℕ, poissonPMFReal μ n := by
          rw [tsum_mul_left]
    _ = (μ : ℝ) := by
          rw [(poissonPMFRealSum μ).tsum_eq]
          ring

/-- Helper for Exercise 23.2.6: the Poisson factorial second moment equals `μ²`. -/
private lemma poissonFactorialSecondMoment_eq (μ : NNReal) :
    ∑' n : ℕ, poissonPMFReal μ n * ((n : ℝ) * ((n : ℝ) - 1)) = (μ : ℝ) ^ (2 : ℕ) := by
  -- Proof comment: the first two terms vanish, and the remaining tail is exactly the shifted
  -- `HasSum` from `hasSumPoissonShiftedFactorialSecondMoment`.
  have hs : Summable (fun n : ℕ ↦ poissonPMFReal μ n * ((n : ℝ) * ((n : ℝ) - 1))) :=
    summablePoissonFactorialSecondMoment μ
  have htail :
      ∑' n : ℕ, poissonPMFReal μ (n + 2) * (((n + 2 : ℕ) : ℝ) * (((n + 2 : ℕ) : ℝ) - 1)) =
        (μ : ℝ) ^ (2 : ℕ) := by
    calc
      ∑' n : ℕ, poissonPMFReal μ (n + 2) * (((n + 2 : ℕ) : ℝ) * (((n + 2 : ℕ) : ℝ) - 1))
        = ∑' n : ℕ, poissonPMFReal μ (n + 2) * ((n + 2 : ℝ) * (n + 1 : ℝ)) := by
            refine tsum_congr fun n ↦ ?_
            have hrewrite :
                (((n + 2 : ℕ) : ℝ) * (((n + 2 : ℕ) : ℝ) - 1)) = (n + 2 : ℝ) * (n + 1 : ℝ) := by
              have hcast2 : (((n + 2 : ℕ) : ℝ)) = (n : ℝ) + 2 := by
                norm_num [Nat.cast_add]
              rw [hcast2]
              ring
            rw [hrewrite]
      _ = (μ : ℝ) ^ (2 : ℕ) := (hasSumPoissonShiftedFactorialSecondMoment μ).tsum_eq
  calc
    ∑' n : ℕ, poissonPMFReal μ n * ((n : ℝ) * ((n : ℝ) - 1))
      = (∑ i ∈ Finset.range 2, poissonPMFReal μ i * ((i : ℝ) * ((i : ℝ) - 1))) +
          ∑' n : ℕ, poissonPMFReal μ (n + 2) * (((n + 2 : ℕ) : ℝ) * (((n + 2 : ℕ) : ℝ) - 1)) := by
            simpa using (hs.sum_add_tsum_nat_add 2).symm
    _ = ∑' n : ℕ, poissonPMFReal μ (n + 2) * (((n + 2 : ℕ) : ℝ) * (((n + 2 : ℕ) : ℝ) - 1)) := by
          norm_num [Finset.sum_range_succ, Nat.cast_add]
    _ = (μ : ℝ) ^ (2 : ℕ) := htail

/-- Helper for Exercise 23.2.6: the centered Poisson square series is summable. -/
private lemma summablePoissonCenteredSecondMoment (μ : NNReal) :
    Summable (fun n : ℕ ↦ (((n : ℝ) - μ) ^ (2 : ℕ)) * poissonPMFReal μ n) := by
  -- Proof comment: rewrite the centered square into factorial-second-moment, first-moment, and
  -- mass pieces, then sum those three already-controlled series.
  have hFactorial :
      Summable (fun n : ℕ ↦ poissonPMFReal μ n * ((n : ℝ) * ((n : ℝ) - 1))) :=
    summablePoissonFactorialSecondMoment μ
  have hFirst :
      Summable (fun n : ℕ ↦ ((1 : ℝ) - 2 * (μ : ℝ)) * (poissonPMFReal μ n * (n : ℝ))) :=
    (summablePoissonFirstMoment μ).mul_left ((1 : ℝ) - 2 * (μ : ℝ))
  have hMass :
      Summable (fun n : ℕ ↦ (μ : ℝ) ^ (2 : ℕ) * poissonPMFReal μ n) :=
    (poissonPMFRealSum μ).summable.mul_left ((μ : ℝ) ^ (2 : ℕ))
  refine (hFactorial.add (hFirst.add hMass)).congr ?_
  intro n
  ring

/-- Helper for Exercise 23.2.6: the centered second moment of a Poisson law equals its rate. -/
private lemma poissonCenteredSecondMoment_eq (μ : NNReal) :
    ∑' n : ℕ, (((n : ℝ) - μ) ^ (2 : ℕ)) * poissonPMFReal μ n = (μ : ℝ) := by
  -- Proof comment: after the additive decomposition of the centered square, each infinite sum is
  -- one of the three Poisson moment identities already proved.
  have hFactorial :
      Summable (fun n : ℕ ↦ poissonPMFReal μ n * ((n : ℝ) * ((n : ℝ) - 1))) :=
    summablePoissonFactorialSecondMoment μ
  have hFirst :
      Summable (fun n : ℕ ↦ ((1 : ℝ) - 2 * (μ : ℝ)) * (poissonPMFReal μ n * (n : ℝ))) :=
    (summablePoissonFirstMoment μ).mul_left ((1 : ℝ) - 2 * (μ : ℝ))
  have hMass :
      Summable (fun n : ℕ ↦ (μ : ℝ) ^ (2 : ℕ) * poissonPMFReal μ n) :=
    (poissonPMFRealSum μ).summable.mul_left ((μ : ℝ) ^ (2 : ℕ))
  let a : ℕ → ℝ := fun n : ℕ ↦ poissonPMFReal μ n * ((n : ℝ) * ((n : ℝ) - 1))
  let b : ℕ → ℝ := fun n : ℕ ↦ ((1 : ℝ) - 2 * (μ : ℝ)) * (poissonPMFReal μ n * (n : ℝ))
  let c : ℕ → ℝ := fun n : ℕ ↦ (μ : ℝ) ^ (2 : ℕ) * poissonPMFReal μ n
  calc
    ∑' n : ℕ, (((n : ℝ) - μ) ^ (2 : ℕ)) * poissonPMFReal μ n
      = ∑' n : ℕ, (a n + (b n + c n)) := by
              refine tsum_congr fun n ↦ ?_
              dsimp [a, b, c]
              ring
    _ = (∑' n : ℕ, a n) + ∑' n : ℕ, (b n + c n) := by
              exact hFactorial.tsum_add (hFirst.add hMass)
    _ = (∑' n : ℕ, a n) + ((∑' n : ℕ, b n) + ∑' n : ℕ, c n) := by
              rw [hFirst.tsum_add hMass]
    _ = (μ : ℝ) := by
          dsimp [a, b, c]
          rw [poissonFactorialSecondMoment_eq, tsum_mul_left, poissonFirstMoment_eq, tsum_mul_left,
            (poissonPMFRealSum μ).tsum_eq]
          ring

/-- Helper for Exercise 23.2.6: the Poisson relative-window tail is controlled by the centered
second moment via a direct Chebyshev-type comparison of series terms. -/
private lemma poissonRelativeWindowTail_le (δ : ℝ) (μ : NNReal)
    (hδ : 0 < δ) (hμ : 0 < (μ : ℝ)) :
    ∑' n : ℕ, (if δ * (μ : ℝ) ≤ |(n : ℝ) - μ| then poissonPMFReal μ n else 0) ≤
      1 / (δ ^ (2 : ℕ) * (μ : ℝ)) := by
  -- Proof comment: compare the indicator tail termwise with the centered-square series divided by
  -- `δ² μ²`, then evaluate that dominating series with the centered-moment identity.
  let tail : ℕ → ℝ := fun n : ℕ ↦
    if δ * (μ : ℝ) ≤ |(n : ℝ) - μ| then poissonPMFReal μ n else 0
  let bound : ℕ → ℝ := fun n : ℕ ↦
    ((((n : ℝ) - μ) ^ (2 : ℕ)) * poissonPMFReal μ n) / (δ ^ (2 : ℕ) * (μ : ℝ) ^ (2 : ℕ))
  have hden : 0 < δ ^ (2 : ℕ) * (μ : ℝ) ^ (2 : ℕ) := by
    positivity
  have hTailNonneg : ∀ n : ℕ, 0 ≤ tail n := by
    intro n
    by_cases h : δ * (μ : ℝ) ≤ |(n : ℝ) - μ|
    · simp [tail, h, poissonPMFReal_nonneg]
    · simp [tail, h]
  have hTailLeMass : ∀ n : ℕ, tail n ≤ poissonPMFReal μ n := by
    intro n
    by_cases h : δ * (μ : ℝ) ≤ |(n : ℝ) - μ|
    · simp [tail, h]
    · simp [tail, h, poissonPMFReal_nonneg]
  have hTailSummable : Summable tail :=
    Summable.of_nonneg_of_le hTailNonneg hTailLeMass (poissonPMFRealSum μ).summable
  have hBoundSummable : Summable bound := by
    simpa [bound] using
      (summablePoissonCenteredSecondMoment μ).div_const (δ ^ (2 : ℕ) * (μ : ℝ) ^ (2 : ℕ))
  have hTailLeBound : ∀ n : ℕ, tail n ≤ bound n := by
    intro n
    by_cases h : δ * (μ : ℝ) ≤ |(n : ℝ) - μ|
    · have habs : |δ * (μ : ℝ)| ≤ |(n : ℝ) - μ| := by
        have hleft : |δ * (μ : ℝ)| = δ * (μ : ℝ) := by
          rw [abs_of_nonneg]
          positivity
        rw [hleft]
        exact h
      have hsq' : (δ * (μ : ℝ)) ^ (2 : ℕ) ≤ ((n : ℝ) - μ) ^ (2 : ℕ) := by
        exact (sq_le_sq).2 habs
      have hsq :
          δ ^ (2 : ℕ) * (μ : ℝ) ^ (2 : ℕ) ≤ ((n : ℝ) - μ) ^ (2 : ℕ) := by
        simpa [pow_two, mul_assoc, mul_left_comm, mul_comm] using hsq'
      have hscale : 1 ≤ (((n : ℝ) - μ) ^ (2 : ℕ)) / (δ ^ (2 : ℕ) * (μ : ℝ) ^ (2 : ℕ)) := by
        rw [one_le_div hden]
        exact hsq
      have hMassNonneg : 0 ≤ poissonPMFReal μ n := poissonPMFReal_nonneg
      simp [tail, bound, h]
      calc
        poissonPMFReal μ n
          = 1 * poissonPMFReal μ n := by ring
        _ ≤ ((((n : ℝ) - μ) ^ (2 : ℕ)) / (δ ^ (2 : ℕ) * (μ : ℝ) ^ (2 : ℕ))) *
            poissonPMFReal μ n := by
              exact mul_le_mul_of_nonneg_right hscale hMassNonneg
        _ = ((((n : ℝ) - μ) ^ (2 : ℕ)) * poissonPMFReal μ n) /
              (δ ^ (2 : ℕ) * (μ : ℝ) ^ (2 : ℕ)) := by
              rw [div_eq_mul_inv]
              ring_nf
    · have hBoundNonneg : 0 ≤ bound n := by
        exact div_nonneg (mul_nonneg (sq_nonneg _) poissonPMFReal_nonneg) hden.le
      simpa [tail, h] using hBoundNonneg
  calc
    ∑' n : ℕ, (if δ * (μ : ℝ) ≤ |(n : ℝ) - μ| then poissonPMFReal μ n else 0)
      = ∑' n : ℕ, tail n := by rfl
    _ ≤ ∑' n : ℕ, bound n := by
          exact Summable.tsum_le_tsum hTailLeBound hTailSummable hBoundSummable
    _ = (∑' n : ℕ, (((n : ℝ) - μ) ^ (2 : ℕ)) * poissonPMFReal μ n) /
          (δ ^ (2 : ℕ) * (μ : ℝ) ^ (2 : ℕ)) := by
            rw [tsum_div_const]
    _ = (μ : ℝ) / (δ ^ (2 : ℕ) * (μ : ℝ) ^ (2 : ℕ)) := by
          rw [poissonCenteredSecondMoment_eq]
    _ = 1 / (δ ^ (2 : ℕ) * (μ : ℝ)) := by
          field_simp [pow_two, hδ.ne', hμ.ne']

/-- Helper for Exercise 23.2.6: the exact Poisson mgf gives the left-tail Chernoff bound in the
scaled logarithmic form. -/
private theorem poissonScaledLaw_closedLeftHalfline_le_tilt {lam a t : ℝ}
    (hlam : 0 < lam) (ht : t ≤ 0) (ε : PositiveParameter) :
    scaledLogMassAlong (fun ε ↦ (poissonScaledLaw lam ε : Measure ℝ)) id (Set.Iic a) ε ≤
      -(((t * a - lam * (Real.exp t - 1) : ℝ) : EReal)) := by
  let μ : Measure ℝ := (poissonScaledLaw lam ε : Measure ℝ)
  have hInt : Integrable (fun x : ℝ ↦ Real.exp ((t / (ε : ℝ)) * x)) μ := by
    -- Proof comment: the exact mgf formula is strictly positive, so the integrand cannot fall
    -- into the `mgf_undef` branch.
    by_contra hNotInt
    have hZero :
        mgf id μ (t / (ε : ℝ)) = 0 := mgf_undef (μ := μ) (X := id) (t := t / (ε : ℝ)) hNotInt
    have hMgf : mgf id μ (t / (ε : ℝ)) =
        Real.exp ((lam / (ε : ℝ)) * (Real.exp t - 1)) :=
      poissonScaledLaw_mgf (hlam := hlam) (t := t) ε
    rw [hZero] at hMgf
    exact (Real.exp_pos _).ne' hMgf.symm
  have hChernoff :
      μ.real (Set.Iic a) ≤ Real.exp (-(t / (ε : ℝ)) * a + cgf id μ (t / (ε : ℝ))) := by
    simpa using
      (measure_le_le_exp_cgf (μ := μ) (X := id) (ε := a) (t := t / (ε : ℝ))
        (div_nonpos_of_nonpos_of_nonneg ht (le_of_lt ε.2)) hInt)
  have hMassLe :
      μ (Set.Iic a) ≤ ENNReal.ofReal (Real.exp (-(t / (ε : ℝ)) * a + cgf id μ (t / (ε : ℝ)))) := by
    rw [← MeasureTheory.ofReal_measureReal (μ := μ) (s := Set.Iic a)]
    exact ENNReal.ofReal_le_ofReal hChernoff
  have hLogMass :
      ENNReal.log (μ (Set.Iic a)) ≤
        (((-(t / (ε : ℝ)) * a + cgf id μ (t / (ε : ℝ)) : ℝ) : EReal)) := by
    calc
      ENNReal.log (μ (Set.Iic a)) ≤
          ENNReal.log (ENNReal.ofReal (Real.exp (-(t / (ε : ℝ)) * a + cgf id μ (t / (ε : ℝ))))) :=
        ENNReal.log_monotone hMassLe
      _ = (((-(t / (ε : ℝ)) * a + cgf id μ (t / (ε : ℝ)) : ℝ) : EReal)) := by
        rw [ENNReal.log_ofReal_of_pos (Real.exp_pos _), Real.log_exp]
  have hε_nonneg : (0 : EReal) ≤ ((ε : ℝ) : EReal) := by
    exact_mod_cast le_of_lt ε.2
  have hEvalCgf :
      cgf id μ (t / (ε : ℝ)) = (lam / (ε : ℝ)) * (Real.exp t - 1) := by
    -- Proof comment: the Poisson mgf is an exact exponential, so its logarithm is linear.
    rw [cgf, poissonScaledLaw_mgf (hlam := hlam) (t := t) ε, Real.log_exp]
  have hAlg :
      (ε : ℝ) * (-(t / (ε : ℝ)) * a + (lam / (ε : ℝ)) * (Real.exp t - 1)) =
        -(t * a - lam * (Real.exp t - 1)) := by
    have hεne : (ε : ℝ) ≠ 0 := ne_of_gt ε.2
    field_simp [hεne]
    ring
  calc
    scaledLogMassAlong (fun ε ↦ (poissonScaledLaw lam ε : Measure ℝ)) id (Set.Iic a) ε
        = ((ε : ℝ) : EReal) * ENNReal.log (μ (Set.Iic a)) := by
            simp [μ, scaledLogMassAlong_def]
    _ ≤ ((ε : ℝ) : EReal) *
          (((-(t / (ε : ℝ)) * a + cgf id μ (t / (ε : ℝ)) : ℝ) : EReal)) := by
            exact mul_le_mul_of_nonneg_left hLogMass hε_nonneg
    _ = -(((t * a - lam * (Real.exp t - 1) : ℝ) : EReal)) := by
          rw [hEvalCgf]
          exact_mod_cast hAlg

/-- Helper for Exercise 23.2.6: the exact Poisson mgf gives the right-tail Chernoff bound in the
scaled logarithmic form. -/
private theorem poissonScaledLaw_closedRightHalfline_le_tilt {lam b t : ℝ}
    (hlam : 0 < lam) (ht : 0 ≤ t) (ε : PositiveParameter) :
    scaledLogMassAlong (fun ε ↦ (poissonScaledLaw lam ε : Measure ℝ)) id (Set.Ici b) ε ≤
      -(((t * b - lam * (Real.exp t - 1) : ℝ) : EReal)) := by
  let μ : Measure ℝ := (poissonScaledLaw lam ε : Measure ℝ)
  have hInt : Integrable (fun x : ℝ ↦ Real.exp ((t / (ε : ℝ)) * x)) μ := by
    -- Proof comment: as in the left-tail case, the exact mgf formula rules out the undefined
    -- branch.
    by_contra hNotInt
    have hZero :
        mgf id μ (t / (ε : ℝ)) = 0 := mgf_undef (μ := μ) (X := id) (t := t / (ε : ℝ)) hNotInt
    have hMgf : mgf id μ (t / (ε : ℝ)) =
        Real.exp ((lam / (ε : ℝ)) * (Real.exp t - 1)) :=
      poissonScaledLaw_mgf (hlam := hlam) (t := t) ε
    rw [hZero] at hMgf
    exact (Real.exp_pos _).ne' hMgf.symm
  have hChernoff :
      μ.real (Set.Ici b) ≤ Real.exp (-(t / (ε : ℝ)) * b + cgf id μ (t / (ε : ℝ))) := by
    simpa using
      (measure_ge_le_exp_cgf (μ := μ) (X := id) (ε := b) (t := t / (ε : ℝ))
        (div_nonneg ht (le_of_lt ε.2)) hInt)
  have hMassLe :
      μ (Set.Ici b) ≤ ENNReal.ofReal (Real.exp (-(t / (ε : ℝ)) * b + cgf id μ (t / (ε : ℝ)))) := by
    rw [← MeasureTheory.ofReal_measureReal (μ := μ) (s := Set.Ici b)]
    exact ENNReal.ofReal_le_ofReal hChernoff
  have hLogMass :
      ENNReal.log (μ (Set.Ici b)) ≤
        (((-(t / (ε : ℝ)) * b + cgf id μ (t / (ε : ℝ)) : ℝ) : EReal)) := by
    calc
      ENNReal.log (μ (Set.Ici b)) ≤
          ENNReal.log (ENNReal.ofReal (Real.exp (-(t / (ε : ℝ)) * b + cgf id μ (t / (ε : ℝ))))) :=
        ENNReal.log_monotone hMassLe
      _ = (((-(t / (ε : ℝ)) * b + cgf id μ (t / (ε : ℝ)) : ℝ) : EReal)) := by
        rw [ENNReal.log_ofReal_of_pos (Real.exp_pos _), Real.log_exp]
  have hε_nonneg : (0 : EReal) ≤ ((ε : ℝ) : EReal) := by
    exact_mod_cast le_of_lt ε.2
  have hEvalCgf :
      cgf id μ (t / (ε : ℝ)) = (lam / (ε : ℝ)) * (Real.exp t - 1) := by
    -- Proof comment: again, take logarithms of the exact Poisson mgf formula.
    rw [cgf, poissonScaledLaw_mgf (hlam := hlam) (t := t) ε, Real.log_exp]
  have hAlg :
      (ε : ℝ) * (-(t / (ε : ℝ)) * b + (lam / (ε : ℝ)) * (Real.exp t - 1)) =
        -(t * b - lam * (Real.exp t - 1)) := by
    have hεne : (ε : ℝ) ≠ 0 := ne_of_gt ε.2
    field_simp [hεne]
    ring
  calc
    scaledLogMassAlong (fun ε ↦ (poissonScaledLaw lam ε : Measure ℝ)) id (Set.Ici b) ε
        = ((ε : ℝ) : EReal) * ENNReal.log (μ (Set.Ici b)) := by
            simp [μ, scaledLogMassAlong_def]
    _ ≤ ((ε : ℝ) : EReal) *
          (((-(t / (ε : ℝ)) * b + cgf id μ (t / (ε : ℝ)) : ℝ) : EReal)) := by
            exact mul_le_mul_of_nonneg_left hLogMass hε_nonneg
    _ = -(((t * b - lam * (Real.exp t - 1) : ℝ) : EReal)) := by
          rw [hEvalCgf]
          exact_mod_cast hAlg

/-- Helper for Exercise 23.2.6: the optimizing Chernoff tilt `log (x / λ)` recovers the exact
Poisson rate at every positive point `x`. -/
private theorem poissonAffine_eq_rateFunction_at_logRatio {lam x : ℝ}
    (hlam : 0 < lam) (hx : 0 < x) :
    (((Real.log (x / lam) * x - lam * (Real.exp (Real.log (x / lam)) - 1) : ℝ) : EReal)) =
      (((poissonScaledRateFunction lam x : ENNReal) : EReal)) := by
  have hxnonneg : 0 ≤ x := le_of_lt hx
  rw [poissonScaledRateFunction_of_nonneg lam hxnonneg]
  have hratio_pos : 0 < x / lam := div_pos hx hlam
  have hexp : Real.exp (Real.log (x / lam)) = x / lam := by
    rw [Real.exp_log hratio_pos]
  have hreal :
      Real.log (x / lam) * x - lam * (Real.exp (Real.log (x / lam)) - 1) =
        x * Real.log (x / lam) + lam - x := by
    rw [hexp]
    field_simp [hlam.ne']
    ring
  have hmain := Real.one_sub_inv_le_log_of_pos (div_pos hx hlam)
  have hmain' : 1 - lam / x ≤ Real.log (x / lam) := by
    simpa [div_eq_mul_inv, hx.ne', hlam.ne'] using hmain
  have hmul' : x * (1 - lam / x) ≤ x * Real.log (x / lam) := by
    exact mul_le_mul_of_nonneg_left hmain' hxnonneg
  have hmul_left : x * (1 - lam / x) = x - lam := by
    field_simp [hx.ne']
  have hnonneg : 0 ≤ x * Real.log (x / lam) + lam - x := by
    -- Proof comment: the classical inequality `1 - λ / x ≤ log (x / λ)` gives the nonnegativity
    -- required to unwrap `ENNReal.ofReal` inside `EReal`.
    rw [hmul_left] at hmul'
    linarith
  have hgoal :
      (((ENNReal.ofReal (x * Real.log (x / lam) + lam - x) : ENNReal) : EReal)) =
        ((x * Real.log (x / lam) + lam - x : ℝ) : EReal) := by
    simp [hnonneg]
  rw [hgoal]
  exact_mod_cast hreal

/-- Helper for Exercise 23.2.6: on the left of `λ`, the Poisson rate decreases as `x` moves
toward `λ`. -/
private theorem poissonScaledRateFunction_leftRay_ge_endpoint {lam a x : ℝ}
    (hlam : 0 < lam) (ha : 0 < a) (haLam : a < lam) (hx : x ≤ a) :
    (((poissonScaledRateFunction lam a : ENNReal) : EReal)) ≤
      (((poissonScaledRateFunction lam x : ENNReal) : EReal)) := by
  by_cases hxneg : x < 0
  · have hxnot : ¬ 0 ≤ x := not_le.mpr hxneg
    -- Proof comment: once `x < 0`, the right-hand rate is `⊤`, so the comparison is immediate.
    simp [poissonScaledRateFunction, hxnot]
  · have hxnonneg : 0 ≤ x := le_of_not_gt hxneg
    let t : ℝ := Real.log (a / lam)
    have hratio_pos : 0 < a / lam := div_pos ha hlam
    have hratio_le : a / lam ≤ 1 := by
      exact (div_le_iff₀ hlam).2 (by simpa [one_mul] using haLam.le)
    have ht_nonpos : t ≤ 0 := by
      exact Real.log_nonpos hratio_pos.le hratio_le
    have hmono_real :
        t * a - lam * (Real.exp t - 1) ≤ t * x - lam * (Real.exp t - 1) := by
      dsimp [t]
      nlinarith
    have hmono :
        (((t * a - lam * (Real.exp t - 1) : ℝ) : EReal)) ≤
          (((t * x - lam * (Real.exp t - 1) : ℝ) : EReal)) := by
      exact_mod_cast hmono_real
    -- Proof comment: evaluate the affine lower support line at the endpoint `a`, then use its
    -- monotonicity on `(-∞, a]` and the general affine lower bound for the rate.
    calc
      (((poissonScaledRateFunction lam a : ENNReal) : EReal))
          = (((t * a - lam * (Real.exp t - 1) : ℝ) : EReal)) := by
              symm
              dsimp [t]
              simpa using poissonAffine_eq_rateFunction_at_logRatio (hlam := hlam) (x := a) ha
      _ ≤ (((t * x - lam * (Real.exp t - 1) : ℝ) : EReal)) := hmono
      _ ≤ (((poissonScaledRateFunction lam x : ENNReal) : EReal)) := by
            dsimp [t]
            exact poissonAffine_le_rateFunction (hlam := hlam) (x := x)
              (t := Real.log (a / lam))

/-- Helper for Exercise 23.2.6: on the right of `λ`, the Poisson rate increases as `x` moves away
from `λ`. -/
private theorem poissonScaledRateFunction_rightRay_ge_endpoint {lam b x : ℝ}
    (hlam : 0 < lam) (hLamB : lam < b) (hbx : b ≤ x) :
    (((poissonScaledRateFunction lam b : ENNReal) : EReal)) ≤
      (((poissonScaledRateFunction lam x : ENNReal) : EReal)) := by
  let t : ℝ := Real.log (b / lam)
  have hbpos : 0 < b := lt_trans hlam hLamB
  have hratio_pos : 0 < b / lam := div_pos hbpos hlam
  have hratio_ge : 1 ≤ b / lam := by
    rw [one_le_div hlam]
    simpa [one_mul] using hLamB.le
  have ht_nonneg : 0 ≤ t := by
    exact Real.log_nonneg hratio_ge
  have hmono_real :
      t * b - lam * (Real.exp t - 1) ≤ t * x - lam * (Real.exp t - 1) := by
    dsimp [t]
    nlinarith
  have hmono :
      (((t * b - lam * (Real.exp t - 1) : ℝ) : EReal)) ≤
        (((t * x - lam * (Real.exp t - 1) : ℝ) : EReal)) := by
    exact_mod_cast hmono_real
  -- Proof comment: the optimizing affine support line at `b` is monotone on `[b, ∞)`, so the
  -- general affine lower bound for the rate closes the comparison.
  calc
    (((poissonScaledRateFunction lam b : ENNReal) : EReal))
        = (((t * b - lam * (Real.exp t - 1) : ℝ) : EReal)) := by
            symm
            dsimp [t]
            simpa using
              poissonAffine_eq_rateFunction_at_logRatio (hlam := hlam) (x := b) hbpos
    _ ≤ (((t * x - lam * (Real.exp t - 1) : ℝ) : EReal)) := hmono
    _ ≤ (((poissonScaledRateFunction lam x : ENNReal) : EReal)) := by
          dsimp [t]
          exact poissonAffine_le_rateFunction (hlam := hlam) (x := x)
            (t := Real.log (b / lam))

/-- Helper for Exercise 23.2.6: the scaled logarithmic mass of the atom `{0}` is the constant
value `-λ`. -/
private theorem poissonScaledLaw_scaledLog_singleton_zero {lam : ℝ} (hlam : 0 < lam)
    (ε : PositiveParameter) :
    scaledLogMassAlong (fun ε ↦ (poissonScaledLaw lam ε : Measure ℝ)) id ({0} : Set ℝ) ε =
      -((lam : ℝ) : EReal) := by
  have hparam_nonneg : 0 ≤ lam / (ε : ℝ) := by
    exact le_of_lt (div_pos hlam ε.2)
  have hparam :
      (Real.toNNReal (lam / (ε : ℝ)) : ℝ) = lam / (ε : ℝ) := by
    simpa using congrArg NNReal.toReal (Real.toNNReal_of_nonneg hparam_nonneg)
  have hmass :
      (poissonScaledLaw lam ε : Measure ℝ) ({0} : Set ℝ) =
        ENNReal.ofReal (Real.exp (-(lam / (ε : ℝ)))) := by
    -- Proof comment: the atom `{0}` corresponds to the Poisson index `0`, whose mass is exactly
    -- `exp (-(λ / ε))`.
    simpa [poissonPMFReal, hparam] using
      (poissonScaledLaw_apply_singleton_scaled (hlam := hlam) ε 0)
  have hεne : (ε : ℝ) ≠ 0 := ne_of_gt ε.2
  have hAlg : (ε : ℝ) * (-(lam / (ε : ℝ))) = -lam := by
    field_simp [hεne]
  -- Proof comment: after taking logarithms, the Poisson atom contributes the deterministic
  -- exponent `-(λ / ε)`, and multiplying by `ε` collapses it to `-λ`.
  rw [scaledLogMassAlong_def, hmass, ENNReal.log_ofReal_of_pos (Real.exp_pos _), Real.log_exp]
  exact_mod_cast hAlg

/-- Helper for Exercise 23.2.6: the nonpositive half-line has the same scaled logarithmic mass as
the atom `{0}` because the negative slice carries no mass. -/
private theorem poissonScaledLaw_scaledLog_Iic_zero {lam : ℝ} (hlam : 0 < lam)
    (ε : PositiveParameter) :
    scaledLogMassAlong (fun ε ↦ (poissonScaledLaw lam ε : Measure ℝ)) id (Set.Iic 0) ε =
      -((lam : ℝ) : EReal) := by
  let μ : Measure ℝ := (poissonScaledLaw lam ε : Measure ℝ)
  have hsplit : Set.Iic (0 : ℝ) = Set.Iio 0 ∪ ({0} : Set ℝ) := by
    ext x
    constructor
    · intro hx
      have hx' : x ≤ 0 := by
        simpa [Set.mem_Iic] using hx
      rcases lt_or_eq_of_le hx' with hxlt | rfl
      · exact Or.inl (by simpa [Set.mem_Iio] using hxlt)
      · exact Or.inr rfl
    · rintro (hx | rfl)
      · exact by simpa [Set.mem_Iic, Set.mem_Iio] using hx.le
      · simp
  have hmass :
      μ (Set.Iic 0) = μ ({0} : Set ℝ) := by
    -- Proof comment: decompose `(-∞, 0]` into the negative half-line and the atom `{0}`, then
    -- use that the negative part has zero mass under the scaled Poisson law.
    calc
      μ (Set.Iic 0) = μ (Set.Iio 0 ∪ ({0} : Set ℝ)) := by rw [hsplit]
      _ = μ (Set.Iio 0) + μ ({0} : Set ℝ) := by
            rw [measure_union]
            · exact Set.disjoint_singleton_right.2 (by simp)
            · exact measurableSet_singleton 0
      _ = μ ({0} : Set ℝ) := by simp [μ, poissonScaledLaw_Iio_zero]
  rw [scaledLogMassAlong_def, hmass]
  simpa [μ, scaledLogMassAlong_def] using poissonScaledLaw_scaledLog_singleton_zero
    (hlam := hlam) ε

/-- Helper for Exercise 23.2.6: adding an `EReal` error term that tends to `0` does not change a
`limsup`. -/
private theorem limsup_add_tendsto_zero_right {α : Type*} {F : Filter α} [F.NeBot]
    (f g : α → EReal) (hg : Tendsto g F (nhds (0 : EReal))) :
    Filter.limsup (fun x ↦ f x + g x) F = Filter.limsup f F := by
  have hlimsup_g : Filter.limsup g F = 0 := hg.limsup_eq
  have hliminf_g : Filter.liminf g F = 0 := hg.liminf_eq
  apply le_antisymm
  · -- Proof comment: subadditivity of `limsup` controls the perturbation from above.
    have hupper :
        Filter.limsup (fun x ↦ f x + g x) F ≤ Filter.limsup f F + Filter.limsup g F :=
      EReal.limsup_add_le
        (Or.inr <| by rw [hlimsup_g]; simp)
        (Or.inr <| by rw [hlimsup_g]; simp)
    rw [hlimsup_g, add_zero] at hupper
    exact hupper
  · -- Proof comment: the companion `liminf` inequality recovers the reverse comparison once the
    -- error term has vanishing liminf.
    have hlower :
        Filter.limsup f F + Filter.liminf g F ≤ Filter.limsup (fun x ↦ f x + g x) F :=
      EReal.le_limsup_add
    rw [hliminf_g, add_zero] at hlower
    exact hlower

/-- Helper for Exercise 23.2.6: the deterministic union penalty `ε log 2` vanishes along the
positive-parameter filter. -/
private theorem scaledLogTwoCorrection_tendsto_zero :
    Tendsto
      (fun ε : PositiveParameter ↦ ((ε : ℝ) : EReal) * ENNReal.log (2 : ℝ≥0∞))
      positiveParameterFilter (nhds (0 : EReal)) := by
  have hlogTwo : ENNReal.log (2 : ℝ≥0∞) = ((Real.log 2 : ℝ) : EReal) := by
    rw [show (2 : ℝ≥0∞) = ENNReal.ofReal (2 : ℝ) by norm_num]
    simpa using (ENNReal.log_ofReal_of_pos (show 0 < (2 : ℝ) by norm_num))
  have hbaseReal :
      Tendsto (fun ε : ℝ ↦ ε * Real.log 2) (𝓝[>] (0 : ℝ)) (nhds (0 : ℝ)) := by
    have hCont : Continuous fun ε : ℝ ↦ ε * Real.log 2 := by
      continuity
    have hCont0 : ContinuousAt (fun ε : ℝ ↦ ε * Real.log 2) 0 := hCont.continuousAt
    simpa using hCont0.continuousWithinAt.tendsto
  have hbase :
      Tendsto (fun ε : ℝ ↦ ((ε * Real.log 2 : ℝ) : EReal))
        (𝓝[>] (0 : ℝ)) (nhds (0 : EReal)) := by
    simpa using (EReal.tendsto_coe.2 hbaseReal)
  have hcoe : Tendsto ((↑) : PositiveParameter → ℝ) positiveParameterFilter (𝓝[>] (0 : ℝ)) := by
    rw [positiveParameterFilter]
    exact Filter.map_comap_le
  -- Proof comment: reindex the standard small-noise logarithmic limit from `𝓝[>] 0` to the
  -- chapter's positive-parameter filter.
  simpa [hlogTwo, EReal.coe_mul] using hbase.comp hcoe

/-- Helper for Exercise 23.2.6: the scaled logarithmic mass of the lattice atom
`{ε * ceil (x / ε)}` converges to the negative Poisson rate at `x > 0`. -/
private theorem poissonScaledLaw_scaledLog_singleton_scaledCeil_tendsto {lam x : ℝ}
    (hlam : 0 < lam) (hx : 0 < x) :
    Tendsto
      (fun ε : PositiveParameter ↦
        scaledLogMassAlong
          (fun ε ↦ (poissonScaledLaw lam ε : Measure ℝ))
          id
          ({((ε : ℝ) * Nat.ceil (x / (ε : ℝ)) : ℝ)} : Set ℝ)
          ε)
      positiveParameterFilter
      (nhds (-(((poissonScaledRateFunction lam x : ENNReal) : EReal)))) := by
  let n : ℝ → ℕ := fun ε ↦ Nat.ceil (x / ε)
  let y : ℝ → ℝ := fun ε ↦ ε * n ε
  let f : ℝ → ℝ := fun ε ↦
    -lam + y ε * Real.log (lam / y ε) + y ε -
      ε * Real.log (Stirling.stirlingSeq (n ε)) -
      (ε / 2) * Real.log (2 * n ε)
  have hεReal :
      Tendsto (fun ε : ℝ ↦ ε) (𝓝[>] (0 : ℝ)) (nhds (0 : ℝ)) :=
    nhdsWithin_le_nhds
  have hy :
      Tendsto y (𝓝[>] (0 : ℝ)) (nhds x) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero_norm' ?_ hεReal
    filter_upwards [self_mem_nhdsWithin] with ε hε
    have hmem := scaledCeil_mem_Icc (x := x) hx.le ⟨ε, hε⟩
    have hnonneg : 0 ≤ y ε - x := sub_nonneg.mpr hmem.1
    have hlt : y ε - x < ε := by
      linarith
    simpa [Real.norm_eq_abs, abs_of_nonneg hnonneg] using hlt.le
  have hMain :
      Tendsto
        (fun ε : ℝ ↦ -lam + y ε * Real.log (lam / y ε) + y ε)
        (𝓝[>] (0 : ℝ))
        (nhds (-lam + x * Real.log (lam / x) + x)) := by
    have hCont :
        ContinuousAt (fun t : ℝ ↦ -lam + t * Real.log (lam / t) + t) x := by
      have hLog :
          ContinuousAt (fun t : ℝ ↦ Real.log (lam / t)) x := by
        refine (Real.continuousAt_log (by positivity : lam / x ≠ 0)).comp ?_
        exact continuousAt_const.div continuousAt_id hx.ne'
      simpa [add_assoc, add_left_comm, add_comm] using
        (continuousAt_const.add ((continuousAt_id.mul hLog).add continuousAt_id))
    exact hCont.tendsto.comp hy
  have hStirlingCorr :
      Tendsto
        (fun ε : ℝ ↦ ε * Real.log (Stirling.stirlingSeq (n ε)))
        (𝓝[>] (0 : ℝ))
        (nhds (0 : ℝ)) := by
    let M : ℝ := max |Real.log (Stirling.stirlingSeq 1)| |Real.log (Real.sqrt Real.pi)|
    have hBound :
        ∀ᶠ ε : ℝ in 𝓝[>] (0 : ℝ),
          ‖ε * Real.log (Stirling.stirlingSeq (n ε))‖ ≤ ε * M := by
      filter_upwards [self_mem_nhdsWithin] with ε hε
      have hn : 0 < n ε := Nat.ceil_pos.2 (div_pos hx hε)
      rcases Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn) with ⟨k, hk⟩
      have hLower :
          Real.log (Real.sqrt Real.pi) ≤ Real.log (Stirling.stirlingSeq (n ε)) := by
        rw [hk]
        exact Real.log_le_log (by positivity) (Stirling.sqrt_pi_le_stirlingSeq (Nat.succ_ne_zero k))
      have hUpperSeq : Stirling.stirlingSeq (n ε) ≤ Stirling.stirlingSeq 1 := by
        rw [hk]
        simpa using Stirling.stirlingSeq'_antitone (show 0 ≤ k by exact Nat.zero_le k)
      have hUpper :
          Real.log (Stirling.stirlingSeq (n ε)) ≤ Real.log (Stirling.stirlingSeq 1) := by
        rw [hk] at hUpperSeq ⊢
        exact Real.log_le_log (Stirling.stirlingSeq'_pos k) hUpperSeq
      have hAbsLe : |Real.log (Stirling.stirlingSeq (n ε))| ≤ M := by
        simpa [M, max_comm] using (abs_le_max_abs_abs hLower hUpper)
      have hεnonneg : 0 ≤ ε := le_of_lt hε
      calc
        ‖ε * Real.log (Stirling.stirlingSeq (n ε))‖
          = ε * |Real.log (Stirling.stirlingSeq (n ε))| := by
              rw [Real.norm_eq_abs, abs_mul, abs_of_pos hε]
        _ ≤ ε * M := by
              gcongr
    have hLim :
        Tendsto (fun ε : ℝ ↦ ε * M) (𝓝[>] (0 : ℝ)) (nhds (0 : ℝ)) := by
      simpa [zero_mul] using hεReal.mul_const M
    exact squeeze_zero_norm' hBound hLim
  have hHalfLogCorr :
      Tendsto
        (fun ε : ℝ ↦ (ε / 2) * Real.log (2 * n ε))
        (𝓝[>] (0 : ℝ))
        (nhds (0 : ℝ)) := by
    have hFirst :
        Tendsto
          (fun ε : ℝ ↦ (ε / 2) * Real.log (2 * y ε))
          (𝓝[>] (0 : ℝ))
          (nhds (0 : ℝ)) := by
      have hLog :
          Tendsto (fun ε : ℝ ↦ Real.log (2 * y ε))
            (𝓝[>] (0 : ℝ))
            (nhds (Real.log (2 * x))) := by
        have hCont :
            ContinuousAt (fun t : ℝ ↦ Real.log (2 * t)) x := by
          refine (Real.continuousAt_log (by positivity : 2 * x ≠ 0)).comp ?_
          exact (continuous_const.mul continuous_id).continuousAt
        exact hCont.tendsto.comp hy
      have hHalf :
          Tendsto (fun ε : ℝ ↦ ε / 2) (𝓝[>] (0 : ℝ)) (nhds (0 : ℝ)) := by
        simpa [div_eq_mul_inv] using hεReal.mul_const ((2 : ℝ)⁻¹)
      simpa [zero_mul] using hHalf.mul hLog
    have hSecond :
        Tendsto (fun ε : ℝ ↦ -(ε / 2) * Real.log ε) (𝓝[>] (0 : ℝ)) (nhds (0 : ℝ)) := by
      have hLogMul :
          Tendsto (fun ε : ℝ ↦ ε * Real.log ε) (𝓝[>] (0 : ℝ)) (nhds (0 : ℝ)) := by
        simpa [Real.rpow_one, mul_comm] using
          (tendsto_log_mul_rpow_nhdsGT_zero zero_lt_one :
            Tendsto (fun ε : ℝ ↦ Real.log ε * ε ^ (1 : ℝ)) (𝓝[>] (0 : ℝ)) (nhds (0 : ℝ)))
      simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using
        hLogMul.const_mul (-(1 / 2 : ℝ))
    have hRewrite :
        (fun ε : ℝ ↦ (ε / 2) * Real.log (2 * n ε)) =ᶠ[𝓝[>] (0 : ℝ)]
          fun ε : ℝ ↦ (ε / 2) * Real.log (2 * y ε) + (-(ε / 2) * Real.log ε) := by
      filter_upwards [self_mem_nhdsWithin] with ε hε
      have hn : 0 < (n ε : ℝ) := by
        exact_mod_cast Nat.ceil_pos.2 (div_pos hx hε)
      have hypos : 0 < y ε := by
        have hmem := scaledCeil_mem_Icc (x := x) hx.le ⟨ε, hε⟩
        exact lt_of_lt_of_le hx hmem.1
      have hEq : (2 * y ε) / ε = (2 * n ε : ℝ) := by
        dsimp [y, n]
        field_simp [show ε ≠ 0 from ne_of_gt hε]
      rw [← hEq, Real.log_div (by positivity) (show ε ≠ 0 from ne_of_gt hε)]
      ring
    simpa [sub_eq_add_neg] using (hFirst.add hSecond).congr' hRewrite.symm
  have hReal :
      Tendsto f (𝓝[>] (0 : ℝ)) (nhds (-lam + x * Real.log (lam / x) + x)) := by
    simpa [f, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
      (hMain.sub hStirlingCorr).sub hHalfLogCorr
  have hCast :
      Tendsto (fun ε : ℝ ↦ ((f ε : ℝ) : EReal))
        (𝓝[>] (0 : ℝ))
        (nhds (((-lam + x * Real.log (lam / x) + x : ℝ) : EReal))) := by
    simpa using (EReal.tendsto_coe.2 hReal)
  have hcoe :
      Tendsto ((↑) : PositiveParameter → ℝ) positiveParameterFilter (𝓝[>] (0 : ℝ)) := by
    rw [positiveParameterFilter]
    exact Filter.map_comap_le
  have hComp :
      Tendsto
        (fun ε : PositiveParameter ↦ ((f (ε : ℝ) : ℝ) : EReal))
        positiveParameterFilter
        (nhds (((-lam + x * Real.log (lam / x) + x : ℝ) : EReal))) :=
    hCast.comp hcoe
  have hEq :
      (fun ε : PositiveParameter ↦
        scaledLogMassAlong
          (fun ε ↦ (poissonScaledLaw lam ε : Measure ℝ))
          id
          ({((ε : ℝ) * Nat.ceil (x / (ε : ℝ)) : ℝ)} : Set ℝ)
          ε) =
        fun ε : PositiveParameter ↦ ((f (ε : ℝ) : ℝ) : EReal) := by
    funext ε
    have hparam :
        (Real.toNNReal (lam / (ε : ℝ)) : ℝ) = lam / (ε : ℝ) := by
      simpa using congrArg NNReal.toReal (Real.toNNReal_of_nonneg (le_of_lt (div_pos hlam ε.2)))
    have hmass :=
      poissonScaledLaw_apply_singleton_scaled
        (hlam := hlam) ε (Nat.ceil (x / (ε : ℝ)))
    have hlogMass :
        (ε : ℝ) * Real.log
          (poissonPMFReal (Real.toNNReal (lam / (ε : ℝ))) (Nat.ceil (x / (ε : ℝ)))) =
          f (ε : ℝ) := by
      have hn : 0 < (n (ε : ℝ) : ℝ) := by
        exact_mod_cast Nat.ceil_pos.2 (div_pos hx ε.2)
      have hypos : 0 < y (ε : ℝ) := by
        have hmem := scaledCeil_mem_Icc (x := x) hx.le ε
        exact lt_of_lt_of_le hx hmem.1
      have hFormula := Stirling.log_stirlingSeq_formula (n (ε : ℝ))
      have hLogExp :
          Real.log ((n (ε : ℝ) : ℝ) / Real.exp 1) =
            Real.log (n (ε : ℝ) : ℝ) - 1 := by
        rw [Real.log_div hn.ne' (Real.exp_ne_zero _), Real.log_exp]
      have hFactorial :
          Real.log (((n (ε : ℝ)).factorial : ℕ) : ℝ) =
            Real.log (Stirling.stirlingSeq (n (ε : ℝ))) +
              1 / 2 * Real.log (2 * n (ε : ℝ)) +
              (n (ε : ℝ) : ℝ) * Real.log (n (ε : ℝ) : ℝ) - n (ε : ℝ) := by
        calc
          Real.log (((n (ε : ℝ)).factorial : ℕ) : ℝ) =
              Real.log (Stirling.stirlingSeq (n (ε : ℝ))) +
                1 / 2 * Real.log (2 * n (ε : ℝ)) +
                (n (ε : ℝ) : ℝ) * Real.log ((n (ε : ℝ) : ℝ) / Real.exp 1) := by
                  linarith [hFormula]
          _ =
              Real.log (Stirling.stirlingSeq (n (ε : ℝ))) +
                1 / 2 * Real.log (2 * n (ε : ℝ)) +
                (n (ε : ℝ) : ℝ) * Real.log (n (ε : ℝ) : ℝ) - n (ε : ℝ) := by
                  rw [hLogExp]
                  ring
      have hLogDiv :
          Real.log (lam / (ε : ℝ)) - Real.log (n (ε : ℝ) : ℝ) =
            Real.log (lam / y (ε : ℝ)) := by
        rw [← Real.log_div (div_ne_zero hlam.ne' (ne_of_gt ε.2)) hn.ne']
        have hCalc : (lam / (ε : ℝ)) / (n (ε : ℝ) : ℝ) = lam / y (ε : ℝ) := by
          dsimp [y, n]
          field_simp [show (ε : ℝ) ≠ 0 from ne_of_gt ε.2]
        rw [hCalc]
      dsimp [f]
      rw [poissonPMFReal, hparam]
      rw [show
          Real.exp (-(lam / (ε : ℝ))) * (lam / (ε : ℝ)) ^ Nat.ceil (x / (ε : ℝ)) /
              ↑(Nat.ceil (x / (ε : ℝ))).factorial =
            Real.exp (-(lam / (ε : ℝ))) *
              ((lam / (ε : ℝ)) ^ Nat.ceil (x / (ε : ℝ)) /
                ↑(Nat.ceil (x / (ε : ℝ))).factorial) by ring]
      rw [Real.log_mul (Real.exp_pos _).ne'
        (div_pos (pow_pos (div_pos hlam ε.2) _) (by positivity)).ne']
      rw [Real.log_exp, Real.log_div (pow_ne_zero _ (div_ne_zero hlam.ne' ε.2.ne'))
        (by positivity), Real.log_pow, hFactorial]
      rw [show y (ε : ℝ) = (ε : ℝ) * (n (ε : ℝ) : ℝ) by rfl]
      rw [← hLogDiv]
      field_simp [show (ε : ℝ) ≠ 0 from ne_of_gt ε.2]
      ring
    rw [scaledLogMassAlong_def, hmass,
      ENNReal.log_ofReal_of_pos (poissonPMFReal_pos ((Real.toNNReal_pos.2 (div_pos hlam ε.2))))]
    simpa [EReal.coe_mul] using congrArg (fun t : ℝ ↦ ((t : ℝ) : EReal)) hlogMass
  have hRate :
      (((-lam + x * Real.log (lam / x) + x : ℝ) : EReal)) =
        -(((poissonScaledRateFunction lam x : ENNReal) : EReal)) := by
    have hAffine :
        (((x * Real.log (x / lam) + lam - x : ℝ) : EReal)) =
          (((poissonScaledRateFunction lam x : ENNReal) : EReal)) := by
      have h := poissonAffine_eq_rateFunction_at_logRatio (hlam := hlam) (x := x) hx
      have hRealEq :
          Real.log (x / lam) * x - lam * (Real.exp (Real.log (x / lam)) - 1) =
            x * Real.log (x / lam) + lam - x := by
        rw [Real.exp_log (div_pos hx hlam)]
        field_simp [hlam.ne']
        ring
      simpa [hRealEq] using h
    have hLogInv : Real.log (lam / x) = -Real.log (x / lam) := by
      have hCalc : lam / x = (x / lam)⁻¹ := by
        field_simp [hx.ne', hlam.ne']
      rw [hCalc, Real.log_inv]
    have hRealEq :
        -lam + x * Real.log (lam / x) + x = -(x * Real.log (x / lam) + lam - x) := by
      rw [hLogInv]
      ring
    have hNegAffine :
        (((-lam + x * Real.log (lam / x) + x : ℝ) : EReal)) =
          -(((x * Real.log (x / lam) + lam - x : ℝ) : EReal)) := by
      exact_mod_cast hRealEq
    exact hNegAffine.trans (by simpa using congrArg Neg.neg hAffine)
  simpa [hEq] using hRate ▸ hComp

/-- Helper for Exercise 23.2.6: on a closed left branch inside `[0, λ)`, the rate image attains
its infimum at the greatest branch point. -/
private theorem poissonScaledRateImage_isLeast_leftBranchEndpoint {lam a : ℝ} {S : Set ℝ}
    (hlam : 0 < lam) (hS : S ⊆ Set.Icc 0 lam) (ha : IsGreatest S a) (haLam : a < lam) :
    IsLeast ((fun x ↦ ((poissonScaledRateFunction lam x : ENNReal) : EReal)) '' S)
      (((poissonScaledRateFunction lam a : ENNReal) : EReal)) := by
  refine ⟨⟨a, ha.1, rfl⟩, ?_⟩
  rintro _ ⟨x, hx, rfl⟩
  have hxnonneg : 0 ≤ x := (hS hx).1
  have hxle : x ≤ a := ha.2 hx
  by_cases ha0 : a = 0
  · -- Proof comment: if the greatest point is `0`, then the whole left branch collapses to the
    -- singleton `{0}`.
    have hx0 : x = 0 := le_antisymm (ha0 ▸ hxle) hxnonneg
    simp [ha0, hx0]
  · -- Proof comment: otherwise `a > 0`, so the monotonicity of the left ray identifies the
    -- endpoint as the branch minimizer.
    have hapos : 0 < a := lt_of_le_of_ne (hS ha.1).1 (Ne.symm ha0)
    exact poissonScaledRateFunction_leftRay_ge_endpoint
      (hlam := hlam) (a := a) (x := x) hapos haLam hxle

/-- Helper for Exercise 23.2.6: on a closed right branch inside `[λ, ∞)`, the rate image attains
its infimum at the least branch point. -/
private theorem poissonScaledRateImage_isLeast_rightBranchEndpoint {lam b : ℝ} {S : Set ℝ}
    (hlam : 0 < lam) (hb : IsLeast S b) (hlamB : lam < b) :
    IsLeast ((fun x ↦ ((poissonScaledRateFunction lam x : ENNReal) : EReal)) '' S)
      (((poissonScaledRateFunction lam b : ENNReal) : EReal)) := by
  refine ⟨⟨b, hb.1, rfl⟩, ?_⟩
  rintro _ ⟨x, hx, rfl⟩
  exact poissonScaledRateFunction_rightRay_ge_endpoint
    (hlam := hlam) (b := b) (x := x) hlamB (hb.2 hx)

/-- Helper for Exercise 23.2.6: the closed-set upper bound follows from the exact Poisson Chernoff
estimates on the two tails around the minimizer `λ`. -/
private theorem poissonScaledLaw_closedUpperBound {lam : ℝ} (hlam : 0 < lam)
    {C : Set ℝ} (hC : IsClosed C) :
    Filter.limsup (scaledLogMassAlong (fun ε ↦ (poissonScaledLaw lam ε : Measure ℝ)) id C)
        positiveParameterFilter ≤
      -sInf ((fun x ↦ ((poissonScaledRateFunction lam x : ENNReal) : EReal)) '' C) := by
  by_cases hEmpty : C = ∅
  · have hEventually :
        ∀ᶠ ε : PositiveParameter in positiveParameterFilter,
          scaledLogMassAlong
              (fun ε ↦ (poissonScaledLaw lam ε : Measure ℝ)) id (∅ : Set ℝ) ε = ⊥ := by
      filter_upwards [Filter.Eventually.of_forall fun ε : PositiveParameter ↦ ε.2] with ε hε
      have hεE : (0 : EReal) < ((ε : ℝ) : EReal) := by
        exact_mod_cast hε
      rw [scaledLogMassAlong_def]
      simp [EReal.mul_bot_of_pos hεE]
    subst hEmpty
    rw [Filter.limsup_congr hEventually]
    simp
  by_cases hlamC : lam ∈ C
  · have hEventually :
        ∀ᶠ ε : PositiveParameter in positiveParameterFilter,
          scaledLogMassAlong
              (fun ε ↦ (poissonScaledLaw lam ε : Measure ℝ)) id C ε ≤ 0 := by
      exact Filter.Eventually.of_forall fun ε ↦
        scaledLogMassAlong_nonpos_of_probability
          (μ := fun ε ↦ (poissonScaledLaw lam ε : Measure ℝ)) id C ε
    have hLimsupNonpos :
        Filter.limsup
            (scaledLogMassAlong (fun ε ↦ (poissonScaledLaw lam ε : Measure ℝ)) id C)
            positiveParameterFilter ≤
          0 :=
      limsup_le_of_le
        (hf := by
          simpa [Filter.IsCoboundedUnder] using
            (Filter.isCobounded_le_of_bot :
              (Filter.map
                (scaledLogMassAlong
                  (fun ε ↦ (poissonScaledLaw lam ε : Measure ℝ)) id C)
                positiveParameterFilter).IsCobounded (· ≤ ·)))
        hEventually
    have hZeroMem :
        (0 : EReal) ∈ ((fun x ↦ ((poissonScaledRateFunction lam x : ENNReal) : EReal)) '' C) := by
      refine ⟨lam, hlamC, ?_⟩
      simpa [poissonScaledRateFunction_at_mean hlam]
    have hRateNonneg :
        ∀ z ∈ ((fun x ↦ ((poissonScaledRateFunction lam x : ENNReal) : EReal)) '' C),
          (0 : EReal) ≤ z := by
      intro z hz
      rcases hz with ⟨x, hx, rfl⟩
      exact poissonScaledRateFunction_nonneg (hlam := hlam)
    have hsInfEq :
        sInf ((fun x ↦ ((poissonScaledRateFunction lam x : ENNReal) : EReal)) '' C) = (0 : EReal) := by
      refine le_antisymm (sInf_le hZeroMem) (le_sInf hRateNonneg)
    simpa [hsInfEq] using hLimsupNonpos
  by_cases hNonneg : (C ∩ Set.Ici (0 : ℝ)).Nonempty
  · let L : Set ℝ := C ∩ Set.Icc 0 lam
    let R : Set ℝ := C ∩ Set.Ici lam
    have hSplit :
        C = (C ∩ Set.Iio 0) ∪ (L ∪ R) := by
      ext x
      constructor
      · intro hx
        by_cases hxneg : x < 0
        · exact Or.inl ⟨hx, hxneg⟩
        · have hxnonneg : 0 ≤ x := le_of_not_gt hxneg
          by_cases hxle : x ≤ lam
          · exact Or.inr (Or.inl ⟨hx, ⟨hxnonneg, hxle⟩⟩)
          · exact Or.inr (Or.inr ⟨hx, le_of_not_ge hxle⟩)
      · rintro (hx | (hx | hx))
        · exact hx.1
        · exact hx.1
        · exact hx.1
    have hNegNull :
        ∀ ε : PositiveParameter,
          (poissonScaledLaw lam ε : Measure ℝ) (C ∩ Set.Iio 0) = 0 := by
      intro ε
      exact measure_mono_null (by intro x hx; exact hx.2) (poissonScaledLaw_Iio_zero (lam := lam) ε)
    have hMassEq :
        ∀ ε : PositiveParameter,
          (poissonScaledLaw lam ε : Measure ℝ) C =
            (poissonScaledLaw lam ε : Measure ℝ) (L ∪ R) := by
      intro ε
      let μ : Measure ℝ := (poissonScaledLaw lam ε : Measure ℝ)
      have hDisj : Disjoint (C ∩ Set.Iio 0) (L ∪ R) := by
        refine Set.disjoint_left.2 ?_
        intro x hxNeg hxLR
        rcases hxLR with hxL | hxR
        · exact (not_lt_of_ge hxL.2.1) hxNeg.2
        · exact (not_lt_of_ge (le_trans hlam.le hxR.2)) hxNeg.2
      have hMeas : MeasurableSet (L ∪ R) := by
        exact (hC.inter isClosed_Icc).measurableSet.union (hC.inter isClosed_Ici).measurableSet
      calc
        μ C = μ ((C ∩ Set.Iio 0) ∪ (L ∪ R)) := by
              simpa using congrArg μ hSplit
        _ = μ ((L ∪ R) ∪ (C ∩ Set.Iio 0)) := by rw [Set.union_comm]
        _ = μ (L ∪ R) + μ (C ∩ Set.Iio 0) := by
              exact measure_union' (μ := μ) hDisj.symm hMeas
        _ = μ (C ∩ Set.Iio 0) + μ (L ∪ R) := by rw [add_comm]
        _ = μ (L ∪ R) := by simp [μ, hNegNull]
    have hEventuallyEq :
        ∀ᶠ ε : PositiveParameter in positiveParameterFilter,
          scaledLogMassAlong
              (fun ε ↦ (poissonScaledLaw lam ε : Measure ℝ)) id C ε =
            scaledLogMassAlong
              (fun ε ↦ (poissonScaledLaw lam ε : Measure ℝ)) id (L ∪ R) ε := by
      filter_upwards [Filter.Eventually.of_forall fun ε : PositiveParameter ↦ hMassEq ε] with ε hε
      rw [scaledLogMassAlong_def, scaledLogMassAlong_def, hε]
    rw [Filter.limsup_congr hEventuallyEq]
    rw [Filter.limsup_le_iff']
    intro y hy
    by_cases hyTop : y = ⊤
    · simp [hyTop]
    obtain ⟨z, hzLeft, hzRight⟩ := exists_between hy
    have hzBot : z ≠ ⊥ := ne_bot_of_gt hzLeft
    have hInfGt :
        -z <
          sInf ((fun x ↦ ((poissonScaledRateFunction lam x : ENNReal) : EReal)) '' C) := by
      simpa using (EReal.neg_strictAnti hzLeft)
    have hLeftLt :
        Filter.limsup
            (scaledLogMassAlong (fun ε ↦ (poissonScaledLaw lam ε : Measure ℝ)) id L)
            positiveParameterFilter < z := by
      by_cases hLempty : L = ∅
      · have hEventually :
            ∀ᶠ ε : PositiveParameter in positiveParameterFilter,
              scaledLogMassAlong
                  (fun ε ↦ (poissonScaledLaw lam ε : Measure ℝ)) id (∅ : Set ℝ) ε = ⊥ := by
          filter_upwards [Filter.Eventually.of_forall fun ε : PositiveParameter ↦ ε.2] with ε hε
          have hεE : (0 : EReal) < ((ε : ℝ) : EReal) := by
            exact_mod_cast hε
          rw [scaledLogMassAlong_def]
          simp [EReal.mul_bot_of_pos hεE]
        have hLimsupEmpty :
            Filter.limsup
                (scaledLogMassAlong (fun ε ↦ (poissonScaledLaw lam ε : Measure ℝ)) id L)
                positiveParameterFilter = ⊥ := by
          simpa [hLempty] using
            (show
              Filter.limsup
                  (scaledLogMassAlong (fun ε ↦ (poissonScaledLaw lam ε : Measure ℝ)) id
                    (∅ : Set ℝ))
                  positiveParameterFilter = ⊥ by
              rw [Filter.limsup_congr hEventually]
              simp)
        rw [hLimsupEmpty]
        exact bot_lt_iff_ne_bot.mpr hzBot
      · have hLnonempty : L.Nonempty := Set.nonempty_iff_ne_empty.mpr hLempty
        have hLcompact : IsCompact L := by
          simpa [L, Set.inter_left_comm, Set.inter_assoc, Set.inter_comm] using
            isCompact_Icc.inter_right hC
        rcases hLcompact.exists_isGreatest hLnonempty with ⟨a, ha⟩
        have haC : a ∈ C := ha.1.1
        have haLe : a ≤ lam := ha.1.2.2
        have hRateGt :
            -z < ((poissonScaledRateFunction lam a : ENNReal) : EReal) := by
          exact lt_of_lt_of_le hInfGt (sInf_le ⟨a, haC, rfl⟩)
        have hBound :
            Filter.limsup
                (scaledLogMassAlong (fun ε ↦ (poissonScaledLaw lam ε : Measure ℝ)) id L)
                positiveParameterFilter ≤
              -(((poissonScaledRateFunction lam a : ENNReal) : EReal)) := by
          have hMono :
              Filter.limsup
                  (scaledLogMassAlong (fun ε ↦ (poissonScaledLaw lam ε : Measure ℝ)) id L)
                  positiveParameterFilter ≤
                Filter.limsup
                  (scaledLogMassAlong
                    (fun ε ↦ (poissonScaledLaw lam ε : Measure ℝ)) id (Set.Iic a))
                  positiveParameterFilter := by
            exact Filter.limsup_le_limsup <|
              Filter.Eventually.of_forall fun ε ↦
                scaledLogMassAlong_mono_of_subset
                  (μ := fun ε ↦ (poissonScaledLaw lam ε : Measure ℝ)) id
                  (fun x hx ↦ ha.2 hx) ε
          refine hMono.trans ?_
          by_cases ha0 : a = 0
          · have hEventually :
                ∀ᶠ ε : PositiveParameter in positiveParameterFilter,
                  scaledLogMassAlong
                      (fun ε ↦ (poissonScaledLaw lam ε : Measure ℝ)) id (Set.Iic 0) ε =
                    -((lam : ℝ) : EReal) := by
              exact Filter.Eventually.of_forall fun ε ↦
                poissonScaledLaw_scaledLog_Iic_zero (hlam := hlam) ε
            subst ha0
            rw [Filter.limsup_congr hEventually]
            have hrate0 :
                (((poissonScaledRateFunction lam 0 : ENNReal) : EReal)) = ((lam : ℝ) : EReal) := by
              rw [poissonScaledRateFunction_of_nonneg lam le_rfl]
              simp [hlam.le]
            rw [hrate0]
            simp
          · have hapos : 0 < a := lt_of_le_of_ne ha.1.2.1 (Ne.symm ha0)
            have ht :
                Real.log (a / lam) ≤ 0 := by
              exact Real.log_nonpos (div_nonneg hapos.le hlam.le)
                ((div_le_iff₀ hlam).2 (by simpa [one_mul] using haLe))
            have hEventually :
                ∀ᶠ ε : PositiveParameter in positiveParameterFilter,
                  scaledLogMassAlong
                      (fun ε ↦ (poissonScaledLaw lam ε : Measure ℝ)) id (Set.Iic a) ε ≤
                    -(((Real.log (a / lam) * a - lam * (Real.exp (Real.log (a / lam)) - 1) :
                      ℝ) : EReal)) := by
              exact Filter.Eventually.of_forall fun ε ↦
                poissonScaledLaw_closedLeftHalfline_le_tilt
                  (hlam := hlam) (a := a) (t := Real.log (a / lam)) ht ε
            have hLimsup :=
              limsup_le_of_le
                (hf := by
                  simpa [Filter.IsCoboundedUnder] using
                    (Filter.isCobounded_le_of_bot :
                      (Filter.map
                        (scaledLogMassAlong
                          (fun ε ↦ (poissonScaledLaw lam ε : Measure ℝ)) id (Set.Iic a))
                        positiveParameterFilter).IsCobounded (· ≤ ·)))
                hEventually
            simpa using
              hLimsup.trans_eq
                (by
                  congr 1
                  exact poissonAffine_eq_rateFunction_at_logRatio
                    (hlam := hlam) (x := a) hapos)
        have hNegRateLt : -(((poissonScaledRateFunction lam a : ENNReal) : EReal)) < z := by
          simpa using (EReal.neg_strictAnti hRateGt)
        exact lt_of_le_of_lt hBound hNegRateLt
    have hRightLt :
        Filter.limsup
            (scaledLogMassAlong (fun ε ↦ (poissonScaledLaw lam ε : Measure ℝ)) id R)
            positiveParameterFilter < z := by
      by_cases hRempty : R = ∅
      · have hEventually :
            ∀ᶠ ε : PositiveParameter in positiveParameterFilter,
              scaledLogMassAlong
                  (fun ε ↦ (poissonScaledLaw lam ε : Measure ℝ)) id (∅ : Set ℝ) ε = ⊥ := by
          filter_upwards [Filter.Eventually.of_forall fun ε : PositiveParameter ↦ ε.2] with ε hε
          have hεE : (0 : EReal) < ((ε : ℝ) : EReal) := by
            exact_mod_cast hε
          rw [scaledLogMassAlong_def]
          simp [EReal.mul_bot_of_pos hεE]
        have hLimsupEmpty :
            Filter.limsup
                (scaledLogMassAlong (fun ε ↦ (poissonScaledLaw lam ε : Measure ℝ)) id R)
                positiveParameterFilter = ⊥ := by
          simpa [hRempty] using
            (show
              Filter.limsup
                  (scaledLogMassAlong (fun ε ↦ (poissonScaledLaw lam ε : Measure ℝ)) id
                    (∅ : Set ℝ))
                  positiveParameterFilter = ⊥ by
              rw [Filter.limsup_congr hEventually]
              simp)
        rw [hLimsupEmpty]
        exact bot_lt_iff_ne_bot.mpr hzBot
      · have hRnonempty : R.Nonempty := Set.nonempty_iff_ne_empty.mpr hRempty
        have hRclosed : IsClosed R := hC.inter isClosed_Ici
        have hRbdd : BddBelow R := by
          refine ⟨lam, ?_⟩
          intro x hx
          exact hx.2
        let b : ℝ := sInf R
        have hb : IsLeast R b := hRclosed.isLeast_csInf hRnonempty hRbdd
        have hbC : b ∈ C := hb.1.1
        have hLamB : lam < b := by
          have hle : lam ≤ b := hb.1.2
          by_contra hnot
          have hEq : b = lam := le_antisymm (le_of_not_gt hnot) hle
          exact hlamC (hEq ▸ hbC)
        have hbpos : 0 < b := lt_trans hlam hLamB
        have hRateGt :
            -z < ((poissonScaledRateFunction lam b : ENNReal) : EReal) := by
          exact lt_of_lt_of_le hInfGt (sInf_le ⟨b, hbC, rfl⟩)
        have hMono :
            Filter.limsup
                (scaledLogMassAlong (fun ε ↦ (poissonScaledLaw lam ε : Measure ℝ)) id R)
                positiveParameterFilter ≤
              Filter.limsup
                (scaledLogMassAlong
                  (fun ε ↦ (poissonScaledLaw lam ε : Measure ℝ)) id (Set.Ici b))
                positiveParameterFilter := by
          exact Filter.limsup_le_limsup <|
            Filter.Eventually.of_forall fun ε ↦
              scaledLogMassAlong_mono_of_subset
                (μ := fun ε ↦ (poissonScaledLaw lam ε : Measure ℝ)) id
                (fun x hx ↦ hb.2 hx) ε
        have ht : 0 ≤ Real.log (b / lam) := by
          apply Real.log_nonneg
          rw [one_le_div hlam]
          simpa [one_mul] using hLamB.le
        have hEventually :
            ∀ᶠ ε : PositiveParameter in positiveParameterFilter,
              scaledLogMassAlong
                  (fun ε ↦ (poissonScaledLaw lam ε : Measure ℝ)) id (Set.Ici b) ε ≤
                -(((Real.log (b / lam) * b - lam * (Real.exp (Real.log (b / lam)) - 1) :
                  ℝ) : EReal)) := by
          exact Filter.Eventually.of_forall fun ε ↦
            poissonScaledLaw_closedRightHalfline_le_tilt
              (hlam := hlam) (b := b) (t := Real.log (b / lam)) ht ε
        have hLimsup :=
          limsup_le_of_le
            (hf := by
              simpa [Filter.IsCoboundedUnder] using
                (Filter.isCobounded_le_of_bot :
                  (Filter.map
                    (scaledLogMassAlong
                      (fun ε ↦ (poissonScaledLaw lam ε : Measure ℝ)) id (Set.Ici b))
                    positiveParameterFilter).IsCobounded (· ≤ ·)))
            hEventually
        have hBound :
            Filter.limsup
                (scaledLogMassAlong (fun ε ↦ (poissonScaledLaw lam ε : Measure ℝ)) id R)
                positiveParameterFilter ≤
              -(((poissonScaledRateFunction lam b : ENNReal) : EReal)) := by
          refine hMono.trans ?_
          simpa using
            hLimsup.trans_eq
              (by
                congr 1
                exact poissonAffine_eq_rateFunction_at_logRatio
                  (hlam := hlam) (x := b) hbpos)
        have hNegRateLt : -(((poissonScaledRateFunction lam b : ENNReal) : EReal)) < z := by
          simpa using (EReal.neg_strictAnti hRateGt)
        exact lt_of_le_of_lt hBound hNegRateLt
    have hUnionPointwise :
        ∀ᶠ ε : PositiveParameter in positiveParameterFilter,
          scaledLogMassAlong
              (fun ε ↦ (poissonScaledLaw lam ε : Measure ℝ)) id (L ∪ R) ε ≤
            ((ε : ℝ) : EReal) * ENNReal.log (2 : ℝ≥0∞) +
              max
                (scaledLogMassAlong (fun ε ↦ (poissonScaledLaw lam ε : Measure ℝ)) id L ε)
                (scaledLogMassAlong (fun ε ↦ (poissonScaledLaw lam ε : Measure ℝ)) id R ε) := by
      exact Filter.Eventually.of_forall fun ε ↦ by
        have hlogTwo : ENNReal.log (2 : ℝ≥0∞) = ((Real.log 2 : ℝ) : EReal) := by
          rw [show (2 : ℝ≥0∞) = ENNReal.ofReal (2 : ℝ) by norm_num]
          simpa using (ENNReal.log_ofReal_of_pos (show 0 < (2 : ℝ) by norm_num))
        simpa [hlogTwo, EReal.coe_mul] using
          scaledLogMassAlong_union_le_logTwo_add_max
            (μ := fun ε ↦ (poissonScaledLaw lam ε : Measure ℝ)) id L R ε
    have hMaxLt :
        Filter.limsup
            (fun ε : PositiveParameter ↦
              max
                (scaledLogMassAlong (fun ε ↦ (poissonScaledLaw lam ε : Measure ℝ)) id L ε)
                (scaledLogMassAlong (fun ε ↦ (poissonScaledLaw lam ε : Measure ℝ)) id R ε))
            positiveParameterFilter < z := by
      rw [limsup_max
        (f := positiveParameterFilter)
        (u := scaledLogMassAlong (fun ε ↦ (poissonScaledLaw lam ε : Measure ℝ)) id L)
        (v := scaledLogMassAlong (fun ε ↦ (poissonScaledLaw lam ε : Measure ℝ)) id R)]
      exact max_lt hLeftLt hRightLt
    have hUnionLimsupLt :
        Filter.limsup
            (scaledLogMassAlong (fun ε ↦ (poissonScaledLaw lam ε : Measure ℝ)) id (L ∪ R))
            positiveParameterFilter < z := by
      calc
        Filter.limsup
            (scaledLogMassAlong (fun ε ↦ (poissonScaledLaw lam ε : Measure ℝ)) id (L ∪ R))
            positiveParameterFilter
          ≤ Filter.limsup
              (fun ε : PositiveParameter ↦
                ((ε : ℝ) : EReal) * ENNReal.log (2 : ℝ≥0∞) +
                  max
                    (scaledLogMassAlong
                      (fun ε ↦ (poissonScaledLaw lam ε : Measure ℝ)) id L ε)
                    (scaledLogMassAlong
                      (fun ε ↦ (poissonScaledLaw lam ε : Measure ℝ)) id R ε))
              positiveParameterFilter := by
                exact Filter.limsup_le_limsup hUnionPointwise
        _ =
            Filter.limsup
              (fun ε : PositiveParameter ↦
                max
                  (scaledLogMassAlong (fun ε ↦ (poissonScaledLaw lam ε : Measure ℝ)) id L ε)
                  (scaledLogMassAlong (fun ε ↦ (poissonScaledLaw lam ε : Measure ℝ)) id R ε))
              positiveParameterFilter := by
                simpa [add_comm] using
                  limsup_add_tendsto_zero_right
                  (f := fun ε : PositiveParameter ↦
                    max
                      (scaledLogMassAlong (fun ε ↦ (poissonScaledLaw lam ε : Measure ℝ)) id L ε)
                      (scaledLogMassAlong (fun ε ↦ (poissonScaledLaw lam ε : Measure ℝ)) id R ε))
                  (g := fun ε : PositiveParameter ↦
                    ((ε : ℝ) : EReal) * ENNReal.log (2 : ℝ≥0∞))
                  scaledLogTwoCorrection_tendsto_zero
        _ < z := hMaxLt
    exact (eventually_lt_of_limsup_lt (hUnionLimsupLt.trans hzRight)).mono fun _ hlt ↦ hlt.le
  · have hSubset : C ⊆ Set.Iio (0 : ℝ) := by
      intro x hx
      by_contra hxnonneg
      exact hNonneg ⟨x, hx, by simpa [Set.mem_Ici] using (le_of_not_gt hxnonneg : 0 ≤ x)⟩
    have hEventually :
        ∀ᶠ ε : PositiveParameter in positiveParameterFilter,
          scaledLogMassAlong
              (fun ε ↦ (poissonScaledLaw lam ε : Measure ℝ)) id C ε = ⊥ := by
      filter_upwards [Filter.Eventually.of_forall fun ε : PositiveParameter ↦ ε.2] with ε hε
      have hεE : (0 : EReal) < ((ε : ℝ) : EReal) := by
        exact_mod_cast hε
      have hmass : (poissonScaledLaw lam ε : Measure ℝ) C = 0 := by
        exact measure_mono_null hSubset (poissonScaledLaw_Iio_zero (lam := lam) ε)
      rw [scaledLogMassAlong_def, hmass, ENNReal.log_zero]
      simpa using EReal.mul_bot_of_pos hεE
    rw [Filter.limsup_congr hEventually]
    simp

-- Proof sketch: compute the logarithmic moment generating function of `ε X_(λ / ε)` from the
-- Poisson law, identify its Legendre transform as `poissonScaledRateFunction lam`, and then apply
-- the chapter's large-deviation theorem for exponentially tilted logarithmic moment generating
-- functions.
/-- Exercise 23.2.6: for `λ > 0`, the laws `μ_ε = P_(ε X_(λ / ε))` satisfy the large deviations
principle on `ℝ` with rate function `x log (x / λ) + λ - x` for `x ≥ 0` and `∞` for `x < 0`. -/
theorem poissonScaledLaw_satisfiesLDPWithRate {lam : ℝ} (hlam : 0 < lam) :
    HasLargeDeviationsPrinciple
      (poissonScaledLaw lam)
      (poissonScaledRateFunction lam) := by
  -- Route correction: the mgf/Chernoff and union-penalty front end is now stable, so the next
  -- pass starts from the remaining singleton lower-bound asymptotic. The closed upper bound is
  -- now packaged directly from the exact Poisson Chernoff estimates.
  refine
    { lowerSemicontinuous :=
        (poissonScaledRateFunction_isGoodRateFunction hlam).lowerSemicontinuous
      open_lower_bound := ?_
      closed_upper_bound := ?_ }
  · intro U hU
    by_cases hEmpty : U = ∅
    · subst hEmpty
      simp
    · rw [Filter.le_liminf_iff']
      intro y hy
      have hWitness :
          ∃ x ∈ U, y < -(((poissonScaledRateFunction lam x : ENNReal) : EReal)) := by
        by_contra hNo
        have hLower :
            -y ≤
              sInf ((fun x ↦ ((poissonScaledRateFunction lam x : ENNReal) : EReal)) '' U) := by
          refine le_sInf ?_
          rintro z ⟨x, hxU, rfl⟩
          have hNot : ¬ y < -(((poissonScaledRateFunction lam x : ENNReal) : EReal)) := by
            exact fun hlt ↦ hNo ⟨x, hxU, hlt⟩
          have hLe :
              -(((poissonScaledRateFunction lam x : ENNReal) : EReal)) ≤ y :=
            le_of_not_gt hNot
          exact (EReal.neg_le_neg_iff.mp (by simpa using hLe))
        have hUpper :
            -sInf ((fun x ↦ ((poissonScaledRateFunction lam x : ENNReal) : EReal)) '' U) ≤ y := by
          exact EReal.neg_le_neg_iff.mp (by simpa using hLower)
        exact (not_lt_of_ge hUpper hy).elim
      rcases hWitness with ⟨x, hxU, hxRate⟩
      by_cases hx0 : x = 0
      · have hy0 : y < -((lam : ℝ) : EReal) := by
          simpa [hx0, poissonScaledRateFunction_of_nonneg lam le_rfl, hlam.le] using hxRate
        have hMassLt :
            ∀ᶠ ε : PositiveParameter in positiveParameterFilter,
              y < scaledLogMassAlong
                (fun ε ↦ (poissonScaledLaw lam ε : Measure ℝ))
                id
                ({0} : Set ℝ)
                ε := by
          exact Filter.Eventually.of_forall fun ε ↦ by
            simpa [poissonScaledLaw_scaledLog_singleton_zero (hlam := hlam) ε] using hy0
        have hMono :
            ∀ᶠ ε : PositiveParameter in positiveParameterFilter,
              scaledLogMassAlong
                  (fun ε ↦ (poissonScaledLaw lam ε : Measure ℝ))
                  id
                  ({0} : Set ℝ)
                  ε ≤
                scaledLogMassAlong
                  (fun ε ↦ (poissonScaledLaw lam ε : Measure ℝ))
                  id
                  U
                  ε := by
          exact Filter.Eventually.of_forall fun ε ↦
            scaledLogMassAlong_mono_of_subset
              (μ := fun ε ↦ (poissonScaledLaw lam ε : Measure ℝ))
              id
              (by
                intro z hz
                have hz0 : z = 0 := by simpa using hz
                simpa [hz0, hx0] using hxU)
              ε
        filter_upwards [hMassLt, hMono] with ε hεLt hεMono
        exact hεLt.le.trans hεMono
      · have hxpos : 0 < x := lt_of_le_of_ne (by
            by_contra hxneg
            have htop : poissonScaledRateFunction lam x = ⊤ := by
              simp [poissonScaledRateFunction, hxneg]
            have : y < (⊥ : EReal) := by
              simpa [htop] using hxRate
            exact not_lt_bot this) (Ne.symm hx0)
        rcases Metric.isOpen_iff.mp hU x hxU with ⟨δ, hδpos, hBallSub⟩
        obtain ⟨z, hyz, hzRate⟩ := exists_between hxRate
        have hSmall :
            ∀ᶠ ε : PositiveParameter in positiveParameterFilter, (ε : ℝ) < δ := by
          have hSmallReal : Set.Iio δ ∈ 𝓝[>] (0 : ℝ) :=
            mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds hδpos)
          have hcoe :
              Tendsto ((↑) : PositiveParameter → ℝ) positiveParameterFilter (𝓝[>] (0 : ℝ)) := by
            rw [positiveParameterFilter]
            exact Filter.map_comap_le
          exact hcoe hSmallReal
        have hPointInU :
            ∀ᶠ ε : PositiveParameter in positiveParameterFilter,
              ((ε : ℝ) * Nat.ceil (x / (ε : ℝ)) : ℝ) ∈ U := by
          filter_upwards [hSmall] with ε hεδ
          have hmem := scaledCeil_mem_Icc (x := x) hxpos.le ε
          have hball :
              ((ε : ℝ) * Nat.ceil (x / (ε : ℝ)) : ℝ) ∈ Metric.ball x δ := by
            rw [Metric.mem_ball, Real.dist_eq, abs_lt]
            constructor
            · have hnonneg :
                  0 ≤ ((ε : ℝ) * Nat.ceil (x / (ε : ℝ)) : ℝ) - x := sub_nonneg.mpr hmem.1
              linarith
            · have hlt : ((ε : ℝ) * Nat.ceil (x / (ε : ℝ)) : ℝ) - x < ε := by
                linarith
              linarith
          exact hBallSub hball
        have hAtom :
            ∀ᶠ ε : PositiveParameter in positiveParameterFilter,
              z <
                scaledLogMassAlong
                  (fun ε ↦ (poissonScaledLaw lam ε : Measure ℝ))
                  id
                  ({((ε : ℝ) * Nat.ceil (x / (ε : ℝ)) : ℝ)} : Set ℝ)
                  ε := by
          exact
            (poissonScaledLaw_scaledLog_singleton_scaledCeil_tendsto
              (hlam := hlam) (x := x) hxpos)
              (Ioi_mem_nhds hzRate)
        filter_upwards [hPointInU, hAtom] with ε hεU hεAtom
        have hSubset :
            ({((ε : ℝ) * Nat.ceil (x / (ε : ℝ)) : ℝ)} : Set ℝ) ⊆ U := by
          intro u hu
          have huEq : u = ((ε : ℝ) * Nat.ceil (x / (ε : ℝ)) : ℝ) := by
            simpa using hu
          simpa [huEq] using hεU
        have hMono :=
          scaledLogMassAlong_mono_of_subset
            (μ := fun ε ↦ (poissonScaledLaw lam ε : Measure ℝ))
            id
            hSubset
            ε
        exact hyz.le.trans (hεAtom.le.trans hMono)
  · intro C hC
    exact poissonScaledLaw_closedUpperBound hlam hC

end ProbabilityTheory
