/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib
import Books.ProbabilityTheory_Klenke_2020.Items.Chap09.Theorem_9_35
import Books.ProbabilityTheory_Klenke_2020.Items.Chap11.Lemma_11_1

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory
open Finset

universe u

variable {Ω : Type u}

section DoobLp

variable {m0 : MeasurableSpace Ω}
variable {ℱ : Filtration ℕ m0} {μ : Measure Ω} [IsFiniteMeasure μ]
variable {X : ℕ → Ω → ℝ}

local macro:max "absMaxUpTo(" X:term ", " n:term ", " ω:term ")" : term =>
  `((range ($n + 1)).sup' nonempty_range_add_one fun k ↦ |($X k $ω)|)

local macro:max "terminalAbsRpow(" X:term ", " p:term ", " n:term ", " ω:term ")" : term =>
  `(Real.rpow |($X $n $ω)| $p)

local macro:max "absMaxUpToRpow(" X:term ", " p:term ", " n:term ", " ω:term ")" : term =>
  `(Real.rpow (absMaxUpTo($X, $n, $ω)) $p)

/- Theorem 11.2 is `source-facing`: it packages the textbook `L^p` corollaries of Doob's discrete
maximal inequality. Its `core/canonical` owner abstraction is `MeasureTheory.maximal_ineq`, and
its `bridge/view` layer for the transformed process `n ↦ |X n| ^ p` is the earlier project theorem
`submartingale_abs_rpow`; this file keeps only the source-level inequalities rather than a parallel
wrapper API for either ingredient. -/
recall MeasureTheory.maximal_ineq
recall submartingale_abs_rpow

/-- Helper for Theorem 11.2: if `X` is pointwise nonnegative, then the absolute running maximum
up to time `n` is the usual running maximum. -/
lemma absMaxUpTo_eq_sup_of_nonneg (hnonneg : 0 ≤ X) (n : ℕ) (ω : Ω) :
    absMaxUpTo(X, n, ω) = (range (n + 1)).sup' nonempty_range_add_one (fun k ↦ X k ω) := by
  -- Proof comment: every value in the finite supremum is nonnegative, so `abs` disappears termwise.
  simpa using
    (Finset.sup'_congr (s := range (n + 1)) (H := nonempty_range_add_one) rfl
      (fun k hk ↦ abs_of_nonneg (hnonneg k ω)))

omit [IsFiniteMeasure μ] in
/-- Helper for Theorem 11.2: the absolute value of a martingale is a submartingale. -/
lemma martingaleAbsSubmartingale (hX : Martingale X ℱ μ) :
    Submartingale (fun i ω ↦ |X i ω|) ℱ μ := by
  -- Proof comment: on `ℝ`, `|x| = x ⊔ (-x)`, and the supremum of two submartingales is again a
  -- submartingale.
  simpa [abs_eq_max_neg] using hX.submartingale.sup hX.neg.submartingale

/-- Helper for Theorem 11.2: Doob's maximal inequality at exponent `1` in the absolute-value form
used by the later `L^p` estimates. -/
lemma absMaxUpTo_l1_event_bound
    (hX : Martingale X ℱ μ ∨ Submartingale X ℱ μ ∧ 0 ≤ X)
    {threshold : ℝ} (hthreshold : 0 < threshold) (n : ℕ) :
    ENNReal.ofReal threshold * μ {ω | threshold ≤ absMaxUpTo(X, n, ω)} ≤
      ∫⁻ ω in {ω | threshold ≤ absMaxUpTo(X, n, ω)}, ENNReal.ofReal |X n ω| ∂μ := by
  let A : Set Ω := {ω | threshold ≤ absMaxUpTo(X, n, ω)}
  have hA_nonneg : 0 ≤ᵐ[μ.restrict A] fun ω ↦ |X n ω| := by
    filter_upwards with ω
    exact abs_nonneg (X n ω)
  rcases hX with hmart | ⟨hsub, hnonneg⟩
  · have hsubAbs : Submartingale (fun i ω ↦ |X i ω|) ℱ μ := martingaleAbsSubmartingale hmart
    have hboundReal :
        threshold * μ.real A ≤ ∫ ω in A, |X n ω| ∂μ := by
      exact (submartingale_maximal_event_expectation_bounds
        (X := fun i ω ↦ |X i ω|) hsubAbs n hthreshold).1
    have hlintegral :
        ENNReal.ofReal (∫ ω in A, |X n ω| ∂μ) =
          ∫⁻ ω in A, ENNReal.ofReal |X n ω| ∂μ := by
      -- Proof comment: on the restricted measure, the integrand is nonnegative, so the real set
      -- integral matches the `ENNReal` lower integral.
      rw [MeasureTheory.ofReal_integral_eq_lintegral_ofReal
        (μ := μ.restrict A) (hsubAbs.integrable n).integrableOn hA_nonneg]
    calc
      ENNReal.ofReal threshold * μ A = ENNReal.ofReal (threshold * μ.real A) := by
        rw [ENNReal.ofReal_mul hthreshold.le, ofReal_measureReal]
      _ ≤ ENNReal.ofReal (∫ ω in A, |X n ω| ∂μ) := ENNReal.ofReal_le_ofReal hboundReal
      _ = ∫⁻ ω in A, ENNReal.ofReal |X n ω| ∂μ := hlintegral
  · have hA_eq :
        A = {ω | threshold ≤ (range (n + 1)).sup' nonempty_range_add_one fun k ↦ X k ω} := by
      ext ω
      simp only [A, le_sup'_iff, Set.mem_setOf_eq]
      constructor
      · rintro ⟨b, hb, hbthreshold⟩
        exact ⟨b, hb, by simpa [abs_of_nonneg (hnonneg b ω)] using hbthreshold⟩
      · rintro ⟨b, hb, hbthreshold⟩
        exact ⟨b, hb, by simpa [abs_of_nonneg (hnonneg b ω)] using hbthreshold⟩
    have hboundReal :
        threshold * μ.real A ≤ ∫ ω in A, |X n ω| ∂μ := by
      rw [hA_eq]
      exact (submartingale_maximal_event_expectation_bounds (X := X) hsub n hthreshold).1.trans
        (submartingale_maximal_event_expectation_bounds (X := X) hsub n hthreshold).2
    have habsIntegrable : Integrable (fun ω ↦ |X n ω|) (μ.restrict A) := by
      simpa [Real.norm_eq_abs] using (hsub.integrable n).norm.integrableOn
    have hlintegral :
        ENNReal.ofReal (∫ ω in A, |X n ω| ∂μ) =
          ∫⁻ ω in A, ENNReal.ofReal |X n ω| ∂μ := by
      -- Proof comment: the terminal absolute value remains nonnegative on the restricted measure.
      rw [MeasureTheory.ofReal_integral_eq_lintegral_ofReal
        (μ := μ.restrict A) habsIntegrable hA_nonneg]
    calc
      ENNReal.ofReal threshold * μ A = ENNReal.ofReal (threshold * μ.real A) := by
        rw [ENNReal.ofReal_mul hthreshold.le, ofReal_measureReal]
      _ ≤ ENNReal.ofReal (∫ ω in A, |X n ω| ∂μ) := ENNReal.ofReal_le_ofReal hboundReal
      _ = ∫⁻ ω in A, ENNReal.ofReal |X n ω| ∂μ := hlintegral

omit [IsFiniteMeasure μ] in
/-- Helper for Theorem 11.2: under the martingale or positive-submartingale hypotheses, the
running absolute maximum up to time `n` is measurable. -/
lemma measurable_absMaxUpTo
    (hX : Martingale X ℱ μ ∨ Submartingale X ℱ μ ∧ 0 ≤ X) (n : ℕ) :
    Measurable fun ω ↦ absMaxUpTo(X, n, ω) := by
  -- Proof comment: each time slice is measurable, so the finite supremum of their absolute values
  -- is measurable as well.
  have hXsm : ∀ k, StronglyMeasurable (X k) := by
    intro k
    rcases hX with hmart | ⟨hsub, _⟩
    · exact ((hmart.stronglyMeasurable k).measurable.le (ℱ.le k)).stronglyMeasurable
    · exact ((hsub.stronglyMeasurable k).measurable.le (ℱ.le k)).stronglyMeasurable
  exact measurable_range_sup'' fun k _ ↦ (hXsm k).measurable.abs

/-- Helper for Theorem 11.2: pointwise, the terminal `p`-th power is bounded by the running
maximal `p`-th power. -/
lemma terminalAbsRpow_le_absMaxUpToRpow_pointwise
    {p : ℝ} (hp : 0 ≤ p) (n : ℕ) (ω : Ω) :
    ENNReal.ofReal (terminalAbsRpow(X, p, n, ω)) ≤
      ENNReal.ofReal (absMaxUpToRpow(X, p, n, ω)) := by
  -- Proof comment: the terminal absolute value is one term in the finite running maximum.
  have hle : |X n ω| ≤ absMaxUpTo(X, n, ω) := by
    exact Finset.le_sup' (s := range (n + 1)) (f := fun k ↦ |X k ω|) (Finset.self_mem_range_succ n)
  -- Proof comment: `x ↦ x^p` is monotone on `ℝ≥0` for `p ≥ 0`, and `ENNReal.ofReal` preserves
  -- the resulting order.
  have hrpow : terminalAbsRpow(X, p, n, ω) ≤ absMaxUpToRpow(X, p, n, ω) := by
    exact Real.rpow_le_rpow (abs_nonneg _) hle hp
  exact ENNReal.ofReal_le_ofReal hrpow

/-- The clause (i) tail estimate in Doob's `L^p` inequality: for a martingale or a nonnegative
submartingale, the event `{|X|*_n ≥ λ}` is controlled by the terminal `p`-th moment. -/
-- Proof sketch: if `X` is a martingale, apply the convex-function result from Theorem 9.35 to the
-- process `|X|^p`; if `X` is already a nonnegative submartingale, apply the same argument directly.
-- Then use Lemma 11.1, i.e. Doob's maximal inequality for nonnegative submartingales, with the
-- submartingale `k ↦ |X_k|^p`.
theorem doobLp_tail_bound
    (hX : Martingale X ℱ μ ∨ Submartingale X ℱ μ ∧ 0 ≤ X) {p threshold : ℝ}
    (hp : 1 ≤ p) (hthreshold : 0 < threshold)
    (n : ℕ) :
    ENNReal.ofReal (Real.rpow threshold p) *
        μ {ω | threshold ≤ absMaxUpTo(X, n, ω)} ≤
      ∫⁻ ω, ENNReal.ofReal (terminalAbsRpow(X, p, n, ω)) ∂μ := by
  let A : Set Ω := {ω | threshold ≤ absMaxUpTo(X, n, ω)}
  let f : Ω → ℝ≥0∞ := fun ω ↦ ENNReal.ofReal |X n ω|
  have hA_meas : MeasurableSet A := by
    exact measurableSet_le measurable_const (measurable_absMaxUpTo (X := X) hX n)
  have hXn_meas : Measurable fun ω ↦ X n ω := by
    rcases hX with hmart | ⟨hsub, _⟩
    · exact (hmart.stronglyMeasurable n).measurable.le (ℱ.le n)
    · exact (hsub.stronglyMeasurable n).measurable.le (ℱ.le n)
  have hf_meas : AEMeasurable f μ := by
    exact (hXn_meas.abs.ennreal_ofReal).aemeasurable
  rcases eq_or_lt_of_le hp with rfl | hp1
  · -- Proof comment: the endpoint `p = 1` is exactly the exponent-`1` maximal-event estimate.
    have hbound :=
      (absMaxUpTo_l1_event_bound (X := X) hX hthreshold n).trans
        (MeasureTheory.setLIntegral_le_lintegral A f)
    simpa [A, f, Real.rpow_one] using hbound
  · let q : ℝ := p / (p - 1)
    have hp0 : 0 ≤ p := le_of_lt (lt_of_lt_of_le zero_lt_one hp)
    have hpq : p.HolderConjugate q := Real.HolderConjugate.conjExponent hp1
    let g : Ω → ℝ≥0∞ := Set.indicator A (fun _ ↦ (1 : ℝ≥0∞))
    have hg_meas : AEMeasurable g μ := by
      exact (measurable_const.indicator hA_meas).aemeasurable
    have hset_eq : ∫⁻ ω in A, f ω ∂μ = ∫⁻ ω, (f * g) ω ∂μ := by
      have hfg : (fun ω ↦ f ω * g ω) = Set.indicator A f := by
        funext ω
        by_cases hω : ω ∈ A
        · simp [f, g, hω]
        · simp [f, g, hω]
      rw [show (fun ω ↦ (f * g) ω) = (fun ω ↦ f ω * g ω) by rfl]
      rw [hfg, MeasureTheory.lintegral_indicator hA_meas]
    have hgpow_eq : (fun ω ↦ g ω ^ q) = g := by
      funext ω
      by_cases hω : ω ∈ A
      · simp [g, hω]
      · simp [g, hω, hpq.symm.pos]
    have hfpow_eq :
        (fun ω ↦ f ω ^ p) = fun ω ↦ ENNReal.ofReal (terminalAbsRpow(X, p, n, ω)) := by
      funext ω
      simp [f, ENNReal.ofReal_rpow_of_nonneg (abs_nonneg (X n ω)) hp0]
    have hholder :
        ∫⁻ ω in A, f ω ∂μ ≤
          (∫⁻ ω, ENNReal.ofReal (terminalAbsRpow(X, p, n, ω)) ∂μ) ^ (1 / p) *
            (μ A) ^ (1 / q) := by
      have hbase := ENNReal.lintegral_mul_le_Lp_mul_Lq μ hpq hf_meas hg_meas
      rw [← hset_eq] at hbase
      rw [hfpow_eq, hgpow_eq] at hbase
      have hg_int : ∫⁻ ω, g ω ∂μ = μ A := by
        simpa [g] using (MeasureTheory.lintegral_indicator_one (μ := μ) (s := A) hA_meas)
      rw [hg_int] at hbase
      exact hbase
    have hbridge :
        ENNReal.ofReal threshold * μ A ≤
          (∫⁻ ω, ENNReal.ofReal (terminalAbsRpow(X, p, n, ω)) ∂μ) ^ (1 / p) *
            (μ A) ^ (1 / q) := by
      exact (absMaxUpTo_l1_event_bound (X := X) hX hthreshold n).trans hholder
    by_cases hA_zero : μ A = 0
    · change ENNReal.ofReal (Real.rpow threshold p) * μ A ≤
        ∫⁻ ω, ENNReal.ofReal (terminalAbsRpow(X, p, n, ω)) ∂μ
      simp [hA_zero]
    · have hA_top : μ A ≠ ∞ := measure_ne_top μ A
      have hA_factor : μ A = (μ A) ^ (1 / p) * (μ A) ^ (1 / q) := by
        rw [← ENNReal.rpow_add _ _ hA_zero hA_top]
        rw [show 1 / p + 1 / q = 1 by simpa [one_div] using hpq.inv_add_inv_eq_one]
        rw [ENNReal.rpow_one]
      have hAq_pos : 0 < (μ A) ^ (1 / q) := by
        exact ENNReal.rpow_pos (bot_lt_iff_ne_bot.mpr hA_zero) hA_top
      have hAq_top : (μ A) ^ (1 / q) ≠ ∞ := by
        exact ENNReal.rpow_ne_top_of_nonneg (le_of_lt (one_div_pos.mpr hpq.symm.pos)) hA_top
      have hcancel :
          ENNReal.ofReal threshold * (μ A) ^ (1 / p) ≤
            (∫⁻ ω, ENNReal.ofReal (terminalAbsRpow(X, p, n, ω)) ∂μ) ^ (1 / p) := by
        have hbridge' :
            (ENNReal.ofReal threshold * (μ A) ^ (1 / p)) * (μ A) ^ (1 / q) ≤
              (∫⁻ ω, ENNReal.ofReal (terminalAbsRpow(X, p, n, ω)) ∂μ) ^ (1 / p) *
                (μ A) ^ (1 / q) := by
          calc
            (ENNReal.ofReal threshold * (μ A) ^ (1 / p)) * (μ A) ^ (1 / q)
                = ENNReal.ofReal threshold * μ A := by
                    rw [mul_assoc, ← hA_factor]
            _ ≤ (∫⁻ ω, ENNReal.ofReal (terminalAbsRpow(X, p, n, ω)) ∂μ) ^ (1 / p) *
                  (μ A) ^ (1 / q) := hbridge
        exact (ENNReal.mul_le_mul_iff_left hAq_pos.ne' hAq_top).1 hbridge'
      have hpow := ENNReal.rpow_le_rpow hcancel hp0
      calc
        ENNReal.ofReal (Real.rpow threshold p) * μ A
            = (ENNReal.ofReal threshold * (μ A) ^ (1 / p)) ^ p := by
                rw [ENNReal.mul_rpow_of_nonneg _ _ hp0]
                rw [ENNReal.ofReal_rpow_of_nonneg hthreshold.le hp0]
                congr 1
                rw [← ENNReal.rpow_mul]
                have hpp : (1 / p) * p = 1 := by
                  field_simp [hp1.ne']
                rw [hpp, ENNReal.rpow_one]
        _ ≤ ((∫⁻ ω, ENNReal.ofReal (terminalAbsRpow(X, p, n, ω)) ∂μ) ^ (1 / p)) ^ p := hpow
        _ = ∫⁻ ω, ENNReal.ofReal (terminalAbsRpow(X, p, n, ω)) ∂μ := by
            rw [← ENNReal.rpow_mul]
            have hpp : (1 / p) * p = 1 := by
              field_simp [hp1.ne']
            rw [hpp, ENNReal.rpow_one]

omit [IsFiniteMeasure μ] in
/-- The left inequality in clause (ii) of Doob's `L^p` inequality: for every nonnegative exponent
`p`, the terminal `p`-th moment is bounded by the `p`-th moment of the running maximal process.
This is isolated in the minimal exponent range actually used by its pointwise proof. -/
-- Proof sketch: for every `ω`, the terminal absolute value `|X n ω|` is one of the terms entering
-- the maximum `|X|*_n ω`, so pointwise monotonicity of `x ↦ x^p` on `ℝ≥0` for `p ≥ 0` and
-- monotonicity of the lower integral give the estimate.
theorem doobLp_terminalMoment_le_runningMaxMoment
    {p : ℝ} (hp : 0 ≤ p) (n : ℕ) :
    ∫⁻ ω, ENNReal.ofReal (terminalAbsRpow(X, p, n, ω)) ∂μ ≤
      ∫⁻ ω, ENNReal.ofReal (absMaxUpToRpow(X, p, n, ω)) ∂μ := by
  -- Proof comment: integrate the pointwise comparison between the terminal value and the running
  -- maximum.
  refine MeasureTheory.lintegral_mono fun ω ↦ ?_
  exact terminalAbsRpow_le_absMaxUpToRpow_pointwise (X := X) hp n ω

/-- Helper for Theorem 11.2: the level set of the natural cutoff `min (|X|*_n) N` reduces to the
running-max event when `t ≤ N` and is empty otherwise. -/
lemma cutoffAbsMaxUpTo_event_eq_ite {t : ℝ} (n N : ℕ) :
    {ω | t ≤ min (absMaxUpTo(X, n, ω)) (N : ℝ)} =
      if t ≤ (N : ℝ) then {ω | t ≤ absMaxUpTo(X, n, ω)} else ∅ := by
  -- Proof comment: `t ≤ min a N` is equivalent to `t ≤ a` together with the deterministic scalar
  -- condition `t ≤ N`.
  ext x
  by_cases ht : t ≤ (N : ℝ)
  · simp [ht]
  · simp [ht]

omit [IsFiniteMeasure μ] in
/-- Helper for Theorem 11.2: the full running-max `p`-moment is the supremum of the moments of the
natural cutoffs `min (|X|*_n) N`. -/
lemma lintegral_absMaxUpToRpow_eq_iSup_cutoff
    (hX : Martingale X ℱ μ ∨ Submartingale X ℱ μ ∧ 0 ≤ X) {p : ℝ} (hp : 0 < p) (n : ℕ) :
    ∫⁻ ω, ENNReal.ofReal (absMaxUpToRpow(X, p, n, ω)) ∂μ =
      ⨆ N : ℕ, ∫⁻ ω, ENNReal.ofReal (Real.rpow (min (absMaxUpTo(X, n, ω)) (N : ℝ)) p) ∂μ := by
  let f : ℕ → Ω → ℝ≥0∞ := fun N ω ↦
    ENNReal.ofReal (Real.rpow (min (absMaxUpTo(X, n, ω)) (N : ℝ)) p)
  have hmeasAbsMax : Measurable fun ω ↦ absMaxUpTo(X, n, ω) :=
    measurable_absMaxUpTo (X := X) hX n
  have hmeas : ∀ N, Measurable (f N) := by
    intro N
    -- Proof comment: each cutoff is a measurable real function, and `ENNReal.ofReal` preserves
    -- measurability.
    have hcut : Measurable fun ω ↦ min (absMaxUpTo(X, n, ω)) (N : ℝ) :=
      hmeasAbsMax.min measurable_const
    exact ((Real.continuous_rpow_const hp.le).measurable.comp hcut).ennreal_ofReal
  have hmono : Monotone f := by
    intro N M hNM ω
    -- Proof comment: the cutoff increases with `N`, so monotonicity of `x ↦ x^p` on `ℝ≥0`
    -- gives monotonicity of the ENNReal integrand family.
    have habs_nonneg : 0 ≤ absMaxUpTo(X, n, ω) := by
      have hle : |X n ω| ≤ absMaxUpTo(X, n, ω) := by
        exact Finset.le_sup' (s := range (n + 1)) (f := fun k ↦ |X k ω|)
          (Finset.self_mem_range_succ n)
      exact le_trans (abs_nonneg _) hle
    have hmin_le :
        min (absMaxUpTo(X, n, ω)) (N : ℝ) ≤ min (absMaxUpTo(X, n, ω)) (M : ℝ) := by
      exact min_le_min le_rfl (by exact_mod_cast hNM)
    exact ENNReal.ofReal_le_ofReal <|
      Real.rpow_le_rpow (le_min habs_nonneg (Nat.cast_nonneg N)) hmin_le hp.le
  have hpointwise :
      (fun ω ↦ ENNReal.ofReal (absMaxUpToRpow(X, p, n, ω))) = fun ω ↦ ⨆ N : ℕ, f N ω := by
    funext ω
    apply le_antisymm
    · -- Proof comment: once the natural cutoff exceeds the running maximum, the cutoff integrand
      -- becomes exactly the full integrand.
      obtain ⟨N, hN⟩ := exists_nat_gt (absMaxUpTo(X, n, ω))
      have hmin : min (absMaxUpTo(X, n, ω)) (N : ℝ) = absMaxUpTo(X, n, ω) := by
        exact min_eq_left (le_of_lt hN)
      exact le_iSup_of_le N (by simp [f, hmin])
    · -- Proof comment: every cutoff integrand is pointwise bounded by the full running-max
      -- integrand.
      refine iSup_le fun N ↦ ?_
      have habs_nonneg : 0 ≤ absMaxUpTo(X, n, ω) := by
        have hle : |X n ω| ≤ absMaxUpTo(X, n, ω) := by
          exact Finset.le_sup' (s := range (n + 1)) (f := fun k ↦ |X k ω|)
            (Finset.self_mem_range_succ n)
        exact le_trans (abs_nonneg _) hle
      exact ENNReal.ofReal_le_ofReal <|
        Real.rpow_le_rpow (le_min habs_nonneg (Nat.cast_nonneg N))
          (min_le_left _ _) hp.le
  -- Proof comment: monotone convergence turns the pointwise supremum of the cutoff family into
  -- the supremum of their lower integrals.
  rw [hpointwise, MeasureTheory.lintegral_iSup hmeas hmono]

/-- Helper for Theorem 11.2: the `p`-moment of a natural cutoff of `|X|*_n` is controlled by the
corresponding weighted `(p - 1)`-moment. -/
lemma cutoffAbsMaxUpToMoment_le_weightedMoment
    (hX : Martingale X ℱ μ ∨ Submartingale X ℱ μ ∧ 0 ≤ X) {p : ℝ} (hp : 1 < p) (n N : ℕ) :
    ∫⁻ ω, ENNReal.ofReal (Real.rpow (min (absMaxUpTo(X, n, ω)) (N : ℝ)) p) ∂μ ≤
      ENNReal.ofReal (p / (p - 1)) *
        ∫⁻ ω, ENNReal.ofReal |X n ω| *
          ENNReal.ofReal (Real.rpow (min (absMaxUpTo(X, n, ω)) (N : ℝ)) (p - 1)) ∂μ := by
  let cutoff : Ω → ℝ := fun ω ↦ min (absMaxUpTo(X, n, ω)) (N : ℝ)
  let weight : Ω → ℝ≥0∞ := fun ω ↦ ENNReal.ofReal |X n ω|
  let ν : Measure Ω := μ.withDensity weight
  have hp0 : 0 < p := lt_trans zero_lt_one hp
  have hp0_le : 0 ≤ p := le_of_lt hp0
  have hp_sub : 0 < p - 1 := sub_pos.2 hp
  have habs_nonneg : ∀ ω, 0 ≤ absMaxUpTo(X, n, ω) := by
    intro ω
    have hle : |X n ω| ≤ absMaxUpTo(X, n, ω) := by
      exact Finset.le_sup' (s := range (n + 1)) (f := fun k ↦ |X k ω|)
        (Finset.self_mem_range_succ n)
    exact le_trans (abs_nonneg _) hle
  have hcut_nonneg : 0 ≤ᵐ[μ] cutoff := by
    filter_upwards with ω
    exact le_min (habs_nonneg ω) (Nat.cast_nonneg N)
  have hcut_nonneg_ν : 0 ≤ᵐ[ν] cutoff := by
    filter_upwards with ω
    exact le_min (habs_nonneg ω) (Nat.cast_nonneg N)
  have hcut_meas : Measurable cutoff := by
    exact (measurable_absMaxUpTo (X := X) hX n).min measurable_const
  have hXn_meas : Measurable fun ω ↦ X n ω := by
    rcases hX with hmart | ⟨hsub, _⟩
    · exact (hmart.stronglyMeasurable n).measurable.le (ℱ.le n)
    · exact (hsub.stronglyMeasurable n).measurable.le (ℱ.le n)
  have hweight_meas : Measurable weight := by
    exact hXn_meas.abs.ennreal_ofReal
  have hcutpow_meas :
      AEMeasurable (fun ω ↦ ENNReal.ofReal (Real.rpow (cutoff ω) (p - 1))) μ := by
    exact
      (Measurable.ennreal_ofReal
        ((Real.continuous_rpow_const (sub_nonneg.2 hp.le)).measurable.comp hcut_meas)).aemeasurable
  have hleft_layer :
      ∫⁻ ω, ENNReal.ofReal (Real.rpow (cutoff ω) p) ∂μ =
        ENNReal.ofReal p *
          ∫⁻ t in Set.Ioi 0, μ {ω | t ≤ cutoff ω} * ENNReal.ofReal (t ^ (p - 1)) := by
    simpa [cutoff] using
      (MeasureTheory.lintegral_rpow_eq_lintegral_meas_le_mul
        (μ := μ) hcut_nonneg hcut_meas.aemeasurable hp0)
  have hweighted_eq :
      ∫⁻ ω, ENNReal.ofReal (Real.rpow (cutoff ω) (p - 1)) ∂ν =
        ∫⁻ ω, weight ω * ENNReal.ofReal (Real.rpow (cutoff ω) (p - 1)) ∂μ := by
    exact
      MeasureTheory.lintegral_withDensity_eq_lintegral_mul₀
        hweight_meas.aemeasurable hcutpow_meas
  have hright_layer_raw :=
    MeasureTheory.lintegral_rpow_eq_lintegral_meas_le_mul (μ := ν)
      hcut_nonneg_ν hcut_meas.aemeasurable hp_sub
  have hright_layer :
      ∫⁻ ω, ENNReal.ofReal (Real.rpow (cutoff ω) (p - 1)) ∂ν =
        ENNReal.ofReal (p - 1) *
          ∫⁻ t in Set.Ioi 0, ν {ω | t ≤ cutoff ω} * ENNReal.ofReal (t ^ (p - 2)) := by
    convert hright_layer_raw using 1
    congr 1
    apply lintegral_congr_ae
    filter_upwards with t
    congr 1
    ring_nf
  have htail_compare :
      ∫⁻ t in Set.Ioi 0, μ {ω | t ≤ cutoff ω} * ENNReal.ofReal (t ^ (p - 1)) ≤
        ∫⁻ t in Set.Ioi 0, ν {ω | t ≤ cutoff ω} * ENNReal.ofReal (t ^ (p - 2)) := by
    refine MeasureTheory.setLIntegral_mono' measurableSet_Ioi ?_
    intro t ht
    have ht0 : 0 < t := Set.mem_Ioi.mp ht
    let At : Set Ω := {ω | t ≤ cutoff ω}
    have hAt_meas : MeasurableSet At := measurableSet_le measurable_const hcut_meas
    have hν_apply : ν At = ∫⁻ ω in At, weight ω ∂μ := by
      simpa [ν] using (withDensity_apply (μ := μ) (f := weight) (s := At) hAt_meas)
    have hbridge_t : ENNReal.ofReal t * μ At ≤ ν At := by
      by_cases htN : t ≤ (N : ℝ)
      · have hAt_eq : At = {ω | t ≤ absMaxUpTo(X, n, ω)} := by
          ext ω
          simp [At, cutoff, htN]
        calc
          ENNReal.ofReal t * μ At = ENNReal.ofReal t * μ {ω | t ≤ absMaxUpTo(X, n, ω)} := by
            rw [hAt_eq]
          _ ≤ ∫⁻ ω in {ω | t ≤ absMaxUpTo(X, n, ω)}, weight ω ∂μ := by
            simpa [weight] using (absMaxUpTo_l1_event_bound (X := X) hX ht0 n)
          _ = ∫⁻ ω in At, weight ω ∂μ := by rw [hAt_eq]
          _ = ν At := hν_apply.symm
      · have hAt_empty : At = ∅ := by
          ext ω
          simp [At, cutoff, htN]
        simp [hAt_empty, ν]
    have ht_split :
        ENNReal.ofReal (t ^ (p - 1)) =
          ENNReal.ofReal t * ENNReal.ofReal (t ^ (p - 2)) := by
      have hreal :
          t ^ (p - 1) = t * (t ^ (p - 2)) := by
        calc
          t ^ (p - 1) = t ^ (1 + (p - 2)) := by ring_nf
          _ = t ^ (1 : ℝ) * t ^ (p - 2) := by
              exact Real.rpow_add ht0 (1 : ℝ) (p - 2)
          _ = t * Real.rpow t (p - 2) := by simp
      rw [hreal, ENNReal.ofReal_mul ht0.le]
    calc
      μ At * ENNReal.ofReal (t ^ (p - 1))
          = (ENNReal.ofReal t * μ At) * ENNReal.ofReal (t ^ (p - 2)) := by
              rw [ht_split, mul_assoc, mul_left_comm]
      _ ≤ ν At * ENNReal.ofReal (t ^ (p - 2)) := by
        exact mul_le_mul_left hbridge_t _
  have hconst :
      ENNReal.ofReal (p / (p - 1)) * ENNReal.ofReal (p - 1) = ENNReal.ofReal p := by
    rw [← ENNReal.ofReal_mul (div_nonneg hp0_le (sub_nonneg.2 hp.le))]
    field_simp [hp.ne']
  calc
    ∫⁻ ω, ENNReal.ofReal (Real.rpow (min (absMaxUpTo(X, n, ω)) (N : ℝ)) p) ∂μ
        = ENNReal.ofReal p *
            ∫⁻ t in Set.Ioi 0, μ {ω | t ≤ cutoff ω} * ENNReal.ofReal (t ^ (p - 1)) := by
              simpa [cutoff] using hleft_layer
    _ ≤ ENNReal.ofReal p *
          ∫⁻ t in Set.Ioi 0, ν {ω | t ≤ cutoff ω} * ENNReal.ofReal (t ^ (p - 2)) := by
            exact mul_le_mul_right htail_compare _
    _ = ENNReal.ofReal (p / (p - 1)) *
          ∫⁻ ω, weight ω * ENNReal.ofReal (Real.rpow (cutoff ω) (p - 1)) ∂μ := by
            calc
              ENNReal.ofReal p *
                  ∫⁻ t in Set.Ioi 0, ν {ω | t ≤ cutoff ω} * ENNReal.ofReal (t ^ (p - 2))
                  = ENNReal.ofReal (p / (p - 1)) *
                      (ENNReal.ofReal (p - 1) *
                        ∫⁻ t in Set.Ioi 0,
                          ν {ω | t ≤ cutoff ω} * ENNReal.ofReal (t ^ (p - 2))) := by
                          rw [← hconst, mul_assoc]
              _ = ENNReal.ofReal (p / (p - 1)) *
                    ∫⁻ ω, weight ω * ENNReal.ofReal (Real.rpow (cutoff ω) (p - 1)) ∂μ := by
                      rw [← hright_layer, hweighted_eq]
    _ =
        ENNReal.ofReal (p / (p - 1)) *
          ∫⁻ ω, ENNReal.ofReal |X n ω| *
            ENNReal.ofReal (Real.rpow (min (absMaxUpTo(X, n, ω)) (N : ℝ)) (p - 1)) ∂μ := by
              simp [cutoff, weight]

/-- Helper for Theorem 11.2: rewriting the ENNReal cutoff power back to the original real-valued
cutoff moment removes the repeated `ofReal`/`rpow` transport from the Hölder step. -/
lemma cutoffEnnrealRpow_eq_ofRealRpow (n N : ℕ) {r : ℝ} (hr : 0 ≤ r) (ω : Ω) :
    (ENNReal.ofReal (min (absMaxUpTo(X, n, ω)) (N : ℝ))) ^ r =
      ENNReal.ofReal (Real.rpow (min (absMaxUpTo(X, n, ω)) (N : ℝ)) r) := by
  -- Proof comment: the natural cutoff is pointwise nonnegative, so `ENNReal.ofReal_rpow_of_nonneg`
  -- identifies the two spellings of the same power.
  have hcut_nonneg : 0 ≤ min (absMaxUpTo(X, n, ω)) (N : ℝ) := by
    have hmax_nonneg : 0 ≤ absMaxUpTo(X, n, ω) := by
      have hle : |X n ω| ≤ absMaxUpTo(X, n, ω) := by
        exact Finset.le_sup' (s := range (n + 1)) (f := fun k ↦ |X k ω|)
          (Finset.self_mem_range_succ n)
      exact le_trans (abs_nonneg _) hle
    exact le_min hmax_nonneg (Nat.cast_nonneg N)
  simpa using ENNReal.ofReal_rpow_of_nonneg hcut_nonneg hr

/-- Helper for Theorem 11.2: every natural cutoff moment is finite because the cutoff is bounded by
the deterministic constant `N`. -/
lemma cutoffMoment_neTop {p : ℝ} (hp : 0 ≤ p) (n N : ℕ) :
    (∫⁻ ω, ENNReal.ofReal (Real.rpow (min (absMaxUpTo(X, n, ω)) (N : ℝ)) p) ∂μ) ≠ ∞ := by
  -- Proof comment: compare the cutoff integrand with the constant bound `N^p` and use finiteness
  -- of the ambient measure.
  have hbound :
      ∫⁻ ω, ENNReal.ofReal (Real.rpow (min (absMaxUpTo(X, n, ω)) (N : ℝ)) p) ∂μ ≤
        ENNReal.ofReal ((N : ℝ) ^ p) * μ Set.univ := by
    calc
      ∫⁻ ω, ENNReal.ofReal (Real.rpow (min (absMaxUpTo(X, n, ω)) (N : ℝ)) p) ∂μ
          ≤ ∫⁻ ω, ENNReal.ofReal ((N : ℝ) ^ p) ∂μ := by
            refine MeasureTheory.lintegral_mono fun ω ↦ ?_
            have hcut_nonneg : 0 ≤ min (absMaxUpTo(X, n, ω)) (N : ℝ) := by
              have hmax_nonneg : 0 ≤ absMaxUpTo(X, n, ω) := by
                have hle : |X n ω| ≤ absMaxUpTo(X, n, ω) := by
                  exact Finset.le_sup' (s := range (n + 1)) (f := fun k ↦ |X k ω|)
                    (Finset.self_mem_range_succ n)
                exact le_trans (abs_nonneg _) hle
              exact le_min hmax_nonneg (Nat.cast_nonneg N)
            exact ENNReal.ofReal_le_ofReal <|
              Real.rpow_le_rpow hcut_nonneg (min_le_right _ _) hp
      _ = ENNReal.ofReal ((N : ℝ) ^ p) * μ Set.univ := by
            simp [MeasureTheory.lintegral_const]
  have hconst_ne_top : ENNReal.ofReal ((N : ℝ) ^ p) * μ Set.univ ≠ ∞ := by
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top μ Set.univ)
  -- Proof comment: if the cutoff moment were infinite, the finite constant upper bound would also
  -- have to be infinite.
  intro htop
  have hbound' := hbound
  rw [htop] at hbound'
  exact hconst_ne_top (top_le_iff.mp hbound')

/-- Helper for Theorem 11.2: once Hölder gives `I ≤ C * A^(1/p) * I^(1/q)`, the finite nonzero
factor `I^(1/q)` can be cancelled to recover the sharp constant `C^p`. -/
lemma cutoffMomentCancellation {I A C : ℝ≥0∞} {p q : ℝ}
    (hpq : p.HolderConjugate q) (hI0 : I ≠ 0) (hItop : I ≠ ∞)
    (h : I ≤ C * A ^ (1 / p) * I ^ (1 / q)) :
    I ≤ C ^ p * A := by
  have hp0 : 0 ≤ p := hpq.nonneg
  have hsplit : I = I ^ (1 / p) * I ^ (1 / q) := by
    -- Proof comment: the Hölder-conjugacy identity `1 / p + 1 / q = 1` splits the moment `I`
    -- into the cancellable factors needed for the standard Doob constant argument.
    rw [← ENNReal.rpow_add _ _ hI0 hItop]
    rw [show 1 / p + 1 / q = 1 by simpa [one_div] using hpq.inv_add_inv_eq_one]
    rw [ENNReal.rpow_one]
  have hIq_pos : 0 < I ^ (1 / q) := by
    exact ENNReal.rpow_pos (bot_lt_iff_ne_bot.mpr hI0) hItop
  have hIq_ne_top : I ^ (1 / q) ≠ ∞ := by
    exact ENNReal.rpow_ne_top_of_nonneg (le_of_lt (one_div_pos.mpr hpq.symm.pos)) hItop
  have hcancel : I ^ (1 / p) ≤ C * A ^ (1 / p) := by
    -- Proof comment: rewrite `I` as the product of its two conjugate powers and cancel the
    -- positive finite factor `I^(1/q)` on the right.
    have h' : I ^ (1 / p) * I ^ (1 / q) ≤ (C * A ^ (1 / p)) * I ^ (1 / q) := by
      calc
        I ^ (1 / p) * I ^ (1 / q) = I := hsplit.symm
        _ ≤ C * A ^ (1 / p) * I ^ (1 / q) := h
        _ = (C * A ^ (1 / p)) * I ^ (1 / q) := by rw [mul_assoc]
    exact (ENNReal.mul_le_mul_iff_left hIq_pos.ne' hIq_ne_top).1 h'
  have hpow := ENNReal.rpow_le_rpow hcancel hp0
  -- Proof comment: raising the cancelled inequality back to the `p`-th power recovers the sharp
  -- constant and removes the remaining fractional exponents.
  calc
    I = (I ^ (1 / p)) ^ p := by
          rw [← ENNReal.rpow_mul]
          have hpp : (1 / p) * p = 1 := by
            field_simp [hpq.ne_zero]
          rw [hpp, ENNReal.rpow_one]
    _ ≤ (C * A ^ (1 / p)) ^ p := hpow
    _ = C ^ p * A := by
          rw [ENNReal.mul_rpow_of_nonneg _ _ hp0]
          congr 1
          rw [← ENNReal.rpow_mul]
          have hpp : (1 / p) * p = 1 := by
            field_simp [hpq.ne_zero]
          rw [hpp, ENNReal.rpow_one]

/-- Helper for Theorem 11.2: each natural cutoff of the running maximum already satisfies the
Doob `L^p` bound with the sharp constant. -/
lemma cutoffAbsMaxUpToMoment_le_doobConstant
    (hX : Martingale X ℱ μ ∨ Submartingale X ℱ μ ∧ 0 ≤ X) {p : ℝ} (hp : 1 < p) (n N : ℕ) :
    ∫⁻ ω, ENNReal.ofReal (Real.rpow (min (absMaxUpTo(X, n, ω)) (N : ℝ)) p) ∂μ ≤
      ENNReal.ofReal (Real.rpow (p / (p - 1)) p) *
        ∫⁻ ω, ENNReal.ofReal (terminalAbsRpow(X, p, n, ω)) ∂μ := by
  -- Route correction: instead of extending the old inline ENNReal algebra, move to the stable
  -- spelling `g = ENNReal.ofReal (min (|X|*_n) N)`, apply Hölder once, and then cancel the finite
  -- factor `I^(1/q)` through a dedicated helper.
  let q : ℝ := p / (p - 1)
  let f : Ω → ℝ≥0∞ := fun ω ↦ ENNReal.ofReal |X n ω|
  let g : Ω → ℝ≥0∞ := fun ω ↦ ENNReal.ofReal (min (absMaxUpTo(X, n, ω)) (N : ℝ))
  let I : ℝ≥0∞ := ∫⁻ ω, g ω ^ p ∂μ
  let A : ℝ≥0∞ := ∫⁻ ω, ENNReal.ofReal (terminalAbsRpow(X, p, n, ω)) ∂μ
  let C : ℝ≥0∞ := ENNReal.ofReal (p / (p - 1))
  have hp0 : 0 < p := lt_trans zero_lt_one hp
  have hp0_le : 0 ≤ p := le_of_lt hp0
  have hpq : p.HolderConjugate q := by
    simpa [q] using Real.HolderConjugate.conjExponent hp
  have hXn_meas : Measurable fun ω ↦ X n ω := by
    rcases hX with hmart | ⟨hsub, _⟩
    · exact (hmart.stronglyMeasurable n).measurable.le (ℱ.le n)
    · exact (hsub.stronglyMeasurable n).measurable.le (ℱ.le n)
  have hf_meas : AEMeasurable f μ := by
    exact (hXn_meas.abs.ennreal_ofReal).aemeasurable
  have hg_meas : AEMeasurable g μ := by
    have hcut_meas : Measurable fun ω ↦ min (absMaxUpTo(X, n, ω)) (N : ℝ) := by
      exact (measurable_absMaxUpTo (X := X) hX n).min measurable_const
    exact hcut_meas.ennreal_ofReal.aemeasurable
  have hfpow :
      (fun ω ↦ f ω ^ p) = fun ω ↦ ENNReal.ofReal (terminalAbsRpow(X, p, n, ω)) := by
    -- Proof comment: the `p`-power of the ENNReal terminal value is the same as the original
    -- real-valued `p`-moment integrand.
    funext ω
    simp [f, ENNReal.ofReal_rpow_of_nonneg (abs_nonneg (X n ω)) hp0_le]
  have hgpow :
      (fun ω ↦ g ω ^ p) =
        fun ω ↦ ENNReal.ofReal (Real.rpow (min (absMaxUpTo(X, n, ω)) (N : ℝ)) p) := by
    -- Proof comment: rewrite the cutoff moment into the ENNReal spelling used by Hölder.
    funext ω
    simpa [g] using cutoffEnnrealRpow_eq_ofRealRpow (X := X) n N hp0_le ω
  have hgsub :
      (fun ω ↦ g ω ^ (p - 1)) =
        fun ω ↦ ENNReal.ofReal (Real.rpow (min (absMaxUpTo(X, n, ω)) (N : ℝ)) (p - 1)) := by
    -- Proof comment: the same normalization is needed for the weighted `(p - 1)`-moment on the
    -- right-hand side of the cutoff estimate.
    funext ω
    simpa [g] using
      cutoffEnnrealRpow_eq_ofRealRpow (X := X) n N (sub_nonneg.2 hp.le) ω
  have hweighted_rhs :
      ∫⁻ ω, f ω * g ω ^ (p - 1) ∂μ =
        ∫⁻ ω, ENNReal.ofReal |X n ω| *
          ENNReal.ofReal (Real.rpow (min (absMaxUpTo(X, n, ω)) (N : ℝ)) (p - 1)) ∂μ := by
    -- Proof comment: rewrite the weighted cutoff integrand into the exact source-facing form of
    -- the previously proved weighted inequality.
    refine MeasureTheory.lintegral_congr_ae ?_
    filter_upwards with ω
    simp [f, congrFun hgsub ω]
  have hI_eq :
      I = ∫⁻ ω, ENNReal.ofReal (Real.rpow (min (absMaxUpTo(X, n, ω)) (N : ℝ)) p) ∂μ := by
    -- Proof comment: the cutoff moment `I` is just the same integral written through `g^p`.
    simp [I, hgpow]
  have hweighted :
      I ≤ C * ∫⁻ ω, f ω * g ω ^ (p - 1) ∂μ := by
    -- Proof comment: this is exactly the previously proved weighted cutoff inequality, rewritten
    -- into the ENNReal Hölder normal form.
    calc
      I = ∫⁻ ω, ENNReal.ofReal (Real.rpow (min (absMaxUpTo(X, n, ω)) (N : ℝ)) p) ∂μ := hI_eq
      _ ≤ ENNReal.ofReal (p / (p - 1)) *
            ∫⁻ ω, ENNReal.ofReal |X n ω| *
              ENNReal.ofReal (Real.rpow (min (absMaxUpTo(X, n, ω)) (N : ℝ)) (p - 1)) ∂μ := by
            exact cutoffAbsMaxUpToMoment_le_weightedMoment (X := X) hX hp n N
      _ = C * ∫⁻ ω, f ω * g ω ^ (p - 1) ∂μ := by
            simpa [C] using
              congrArg (fun z ↦ ENNReal.ofReal (p / (p - 1)) * z) hweighted_rhs.symm
  have hholder :
      ∫⁻ ω, f ω * g ω ^ (p - 1) ∂μ ≤ A ^ (1 / p) * I ^ (1 / q) := by
    -- Proof comment: apply the ENNReal Hölder inequality once the two power integrals are written
    -- in the stable `f^p` and `g^p` forms.
    simpa [A, I, hfpow, hgpow] using
      (ENNReal.lintegral_mul_rpow_le_lintegral_rpow_mul_lintegral_rpow hpq hf_meas hg_meas)
  have hmain : I ≤ C * A ^ (1 / p) * I ^ (1 / q) := by
    -- Proof comment: compose the weighted cutoff estimate with Hölder and reassociate the product
    -- so the cancellation helper applies verbatim.
    calc
      I ≤ C * ∫⁻ ω, f ω * g ω ^ (p - 1) ∂μ := hweighted
      _ ≤ C * (A ^ (1 / p) * I ^ (1 / q)) := by
            exact mul_le_mul_right hholder C
      _ = C * A ^ (1 / p) * I ^ (1 / q) := by rw [mul_assoc]
  have hItop : I ≠ ∞ := by
    simpa [I, hgpow] using cutoffMoment_neTop (X := X) hp0_le n N
  by_cases hI0 : I = 0
  · -- Proof comment: if the cutoff moment vanishes, the target inequality is immediate.
    rw [← hI_eq, hI0]
    exact bot_le
  · have hcancel : I ≤ C ^ p * A := cutoffMomentCancellation hpq hI0 hItop hmain
    have hCp :
        C ^ p = ENNReal.ofReal (Real.rpow (p / (p - 1)) p) := by
      -- Proof comment: the cancellation helper returns the sharp constant as `C^p`; this final
      -- rewrite returns to the source-facing real-valued spelling.
      simp [C, ENNReal.ofReal_rpow_of_nonneg
        (div_nonneg hp0_le (sub_nonneg.2 hp.le)) hp0_le]
    simpa [I, A, hgpow, hCp] using hcancel

/-- Theorem 11.2: for `p > 1`, the `p`-th moment of the running maximal process is bounded by the
classical Doob constant `(p / (p - 1))^p` times the terminal `p`-th moment. This is the right
inequality in clause (ii). -/
-- Proof sketch: integrate the tail estimate from clause (1) against `p λ^(p-1)`, truncate the
-- running maximum at level `K`, apply Hölder's inequality to the truncated moments, and then pass
-- to the limit `K → ∞`.
theorem doobLp_runningMaxMoment_le
    (hX : Martingale X ℱ μ ∨ Submartingale X ℱ μ ∧ 0 ≤ X) {p : ℝ} (hp : 1 < p) (n : ℕ) :
    ∫⁻ ω, ENNReal.ofReal (absMaxUpToRpow(X, p, n, ω)) ∂μ ≤
      ENNReal.ofReal (Real.rpow (p / (p - 1)) p) *
        ∫⁻ ω, ENNReal.ofReal (terminalAbsRpow(X, p, n, ω)) ∂μ := by
  -- Route correction: rather than working directly with an unbounded truncation parameter, pass to
  -- natural cutoffs and finish by monotone convergence once each cutoff has the sharp bound.
  have hp0 : 0 < p := lt_trans zero_lt_one hp
  rw [lintegral_absMaxUpToRpow_eq_iSup_cutoff (X := X) hX hp0 n]
  -- Proof comment: each cutoff satisfies the same uniform Doob bound, so the supremum does too.
  refine iSup_le fun N ↦ ?_
  exact cutoffAbsMaxUpToMoment_le_doobConstant (X := X) hX hp n N

end DoobLp
