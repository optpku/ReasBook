/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Books.ProbabilityTheory_Klenke_2020.Items.Chap02.Definition_2_14
import Books.ProbabilityTheory_Klenke_2020.Items.Chap04.Theorem_4_26

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory
open Filter

universe u

variable {Ω : Type u}

noncomputable section

/-- The weighted exponential series from Exercise 5.1.4, written in the textbook indexing
`X 1, X 2, ...`. -/
def weightedExpSeries (X : ℕ → Ω → ℝ) (c : Set.Ioo (0 : ℝ) 1) (ω : Ω) : ℝ≥0∞ :=
  ∑' n, ENNReal.ofReal (Real.exp (X (n + 1) ω) * (c : ℝ) ^ (n + 1))

/-- Helper for Exercise 5.1.4: the threshold map `x ↦ max ((2 / a) * x) 0` is measurable. -/
lemma measurable_scaledMax (a : ℝ) : Measurable fun x : ℝ ↦ max ((2 / a) * x) 0 := by
  -- Proof comment: the positive-part map is measurable, and scalar multiplication is measurable.
  fun_prop

/-- Helper for Exercise 5.1.4: the threshold event for `max ((2 / a) * x) 0` agrees with the
corresponding linear threshold when the threshold level is nonnegative. -/
lemma scaledMax_mem_Ioi_iff {a x t : ℝ} (ha : 0 < a) (ht : 0 ≤ t) :
    max ((2 / a) * x) 0 ∈ Set.Ioi t ↔ (a / 2) * t < x := by
  -- Proof comment: because `t ≥ 0`, the strict inequality against the `max` reduces to the
  -- scaled coordinate, and then positive scalar multiplication clears the factor `2 / a`.
  constructor
  · intro hx
    have hx_or : t < (2 / a) * x ∨ t < 0 := by
      simpa [Set.mem_Ioi, lt_max_iff] using hx
    rcases hx_or with hx' | hx'
    · have hmul : (a / 2) * t < (a / 2) * ((2 / a) * x) := by
        exact mul_lt_mul_of_pos_left hx' (show 0 < a / 2 by positivity)
      have hcancel : (a / 2) * ((2 / a) * x) = x := by
        field_simp [ha.ne']
      simpa [hcancel] using hmul
    · exact (not_lt_of_ge ht hx').elim
  · intro hx
    have hmul : (2 / a) * ((a / 2) * t) < (2 / a) * x := by
      exact mul_lt_mul_of_pos_left hx (show 0 < 2 / a by positivity)
    have hcancel : (2 / a) * ((a / 2) * t) = t := by
      field_simp [ha.ne']
    have hx' : t < (2 / a) * x := by
      simpa [hcancel] using hmul
    have hmax : t < max ((2 / a) * x) 0 := lt_of_lt_of_le hx' (le_max_left _ _)
    simpa [Set.mem_Ioi] using hmax

/-- Helper for Exercise 5.1.4: the exponential weight `c^(n+1)` can be rewritten as an
exponential with exponent `(n + 1) * log c`. -/
lemma pow_eq_exp_nat_mul_log (c : Set.Ioo (0 : ℝ) 1) (n : ℕ) :
    (c : ℝ) ^ (n + 1) = Real.exp (((n + 1 : ℕ) : ℝ) * Real.log (c : ℝ)) := by
  -- Proof comment: rewrite the positive base as `exp (log c)` and collapse the repeated product
  -- with the standard `exp_nat_mul` identity.
  have hc : (c : ℝ) = Real.exp (Real.log (c : ℝ)) := by
    simpa using (Real.exp_log c.2.1).symm
  rw [hc]
  simpa using (Real.exp_nat_mul (Real.log (c : ℝ)) (n + 1)).symm

/-- Helper for Exercise 5.1.4: the threshold exponent `a = -log c` converts the product
`exp (a * n) * c^(n+1)` into the constant `c`. -/
lemma exp_threshold_mul_pow_eq (c : Set.Ioo (0 : ℝ) 1) (n : ℕ) :
    Real.exp ((-Real.log (c : ℝ)) * n) * (c : ℝ) ^ (n + 1) = (c : ℝ) := by
  -- Proof comment: after converting the power to an exponential, the two exponents combine to
  -- exactly `log c`.
  calc
    Real.exp ((-Real.log (c : ℝ)) * n) * (c : ℝ) ^ (n + 1)
        = Real.exp ((-Real.log (c : ℝ)) * n) *
            Real.exp (((n + 1 : ℕ) : ℝ) * Real.log (c : ℝ)) := by
            rw [pow_eq_exp_nat_mul_log]
    _ = Real.exp ((-Real.log (c : ℝ)) * n + (((n + 1 : ℕ) : ℝ) * Real.log (c : ℝ))) := by
          rw [← Real.exp_add]
    _ = Real.exp (Real.log (c : ℝ)) := by
          congr 1
          norm_num [Nat.cast_add, Nat.cast_one]
          ring
    _ = (c : ℝ) := by
          simpa using (Real.exp_log c.2.1)

/-- Helper for Exercise 5.1.4: a linear upper bound on the exponent produces a geometric
majorant for a single weighted term. -/
lemma weightedExpTerm_le_geometric_of_linearBound
    (c : Set.Ioo (0 : ℝ) 1) (n : ℕ) {x : ℝ}
    (hx : x ≤ ((-Real.log (c : ℝ)) / 2) * n) :
    Real.exp x * (c : ℝ) ^ (n + 1) ≤
      (c : ℝ) * (Real.exp (Real.log (c : ℝ) / 2)) ^ n := by
  -- Proof comment: convert the power to an exponential, combine the exponents once, and use the
  -- linear bound to compare against the geometric rate `exp (log c / 2)`.
  have hExponent :
      x + (((n + 1 : ℕ) : ℝ) * Real.log (c : ℝ)) ≤
        Real.log (c : ℝ) + ((n : ℕ) : ℝ) * (Real.log (c : ℝ) / 2) := by
    norm_num [Nat.cast_add, Nat.cast_one] at hx ⊢
    linarith
  calc
    Real.exp x * (c : ℝ) ^ (n + 1)
        = Real.exp x * Real.exp (((n + 1 : ℕ) : ℝ) * Real.log (c : ℝ)) := by
            rw [pow_eq_exp_nat_mul_log]
    _ = Real.exp (x + (((n + 1 : ℕ) : ℝ) * Real.log (c : ℝ))) := by
          rw [← Real.exp_add]
    _ ≤ Real.exp (Real.log (c : ℝ) + ((n : ℕ) : ℝ) * (Real.log (c : ℝ) / 2)) := by
          exact Real.exp_le_exp.mpr hExponent
    _ = Real.exp (Real.log (c : ℝ)) *
          Real.exp (((n : ℕ) : ℝ) * (Real.log (c : ℝ) / 2)) := by
            rw [Real.exp_add]
    _ = (c : ℝ) * (Real.exp (Real.log (c : ℝ) / 2)) ^ n := by
          rw [Real.exp_log c.2.1, Real.exp_nat_mul]

/-- Helper for Exercise 5.1.4: eventual linear upper bounds force the weighted exponential series
to be finite. -/
lemma weightedExpSeries_lt_top_of_eventually_linearBound
    (X : ℕ → Ω → ℝ) (c : Set.Ioo (0 : ℝ) 1) {ω : Ω}
    (hω : ∀ᶠ n in atTop, X (n + 1) ω ≤ ((-Real.log (c : ℝ)) / 2) * n) :
    weightedExpSeries X c ω < ∞ := by
  -- Route correction: isolate the exp/log/pow normalization in a one-term geometric majorant
  -- before applying the comparison test to the tail.
  let r : ℝ := Real.exp (Real.log (c : ℝ) / 2)
  let term : ℕ → ℝ := fun n ↦ Real.exp (X (n + 1) ω) * (c : ℝ) ^ (n + 1)
  have hr_nonneg : 0 ≤ r := by
    -- Proof comment: the geometric ratio is an exponential, so it is nonnegative.
    dsimp [r]
    positivity
  have hr_lt_one : r < 1 := by
    -- Proof comment: `log c < 0` for `0 < c < 1`, hence `exp (log c / 2)` lies strictly below `1`.
    dsimp [r]
    rw [Real.exp_lt_one_iff]
    linarith [Real.log_neg c.2.1 c.2.2]
  rcases Filter.eventually_atTop.mp hω with ⟨N, hN⟩
  have hterm_nonneg : ∀ n, 0 ≤ term n := by
    -- Proof comment: every weighted exponential term is a product of nonnegative real numbers.
    intro n
    exact mul_nonneg (Real.exp_pos _).le (pow_nonneg c.2.1.le _)
  have hgeom : Summable (fun n : ℕ ↦ (c : ℝ) * r ^ n) := by
    -- Proof comment: once the ratio is in `[0, 1)`, the standard geometric series is summable.
    simpa [r] using (summable_geometric_of_lt_one hr_nonneg hr_lt_one).mul_left (c : ℝ)
  have htail_summable : Summable (fun k : ℕ ↦ term (k + N)) := by
    -- Proof comment: compare each tail term with the same-index geometric term.
    refine Summable.of_nonneg_of_le (fun k ↦ hterm_nonneg (k + N)) ?_ hgeom
    intro k
    have hmajorant :
        term (k + N) ≤ (c : ℝ) * r ^ (k + N) := by
      exact
        weightedExpTerm_le_geometric_of_linearBound c (k + N)
          (x := X (k + N + 1) ω)
          (hN (k + N) (Nat.le_add_left N k))
    have hpowN : r ^ N ≤ 1 := by
      exact pow_le_one₀ hr_nonneg hr_lt_one.le
    have hk_nonneg : 0 ≤ (c : ℝ) * r ^ k := by
      exact mul_nonneg c.2.1.le (pow_nonneg hr_nonneg _)
    calc
      term (k + N) ≤ (c : ℝ) * r ^ (k + N) := hmajorant
      _ = ((c : ℝ) * r ^ k) * r ^ N := by
            rw [pow_add]
            ring
      _ ≤ ((c : ℝ) * r ^ k) * 1 := by
            exact mul_le_mul_of_nonneg_left hpowN hk_nonneg
      _ = (c : ℝ) * r ^ k := by ring
  have hterm_summable : Summable term := by
    -- Proof comment: summability of one tail is equivalent to summability of the whole series.
    exact (summable_nat_add_iff (f := term) N).mp htail_summable
  -- Proof comment: the ENNReal series is the image of a summable nonnegative real series.
  rw [weightedExpSeries, ← ENNReal.ofReal_tsum_of_nonneg hterm_nonneg hterm_summable]
  exact ENNReal.ofReal_lt_top

section MeasurableHelpers

variable [MeasurableSpace Ω]

/-- Helper for Exercise 5.1.4: a nonintegrable nonnegative measurable real random variable has a
divergent series of strict upper-tail probabilities. -/
lemma tailProbTsum_eq_top_of_notIntegrable_nonneg
    (P : Measure Ω) [IsProbabilityMeasure P] (Y : Ω → ℝ) (hY_meas : Measurable Y)
    (hY_nonneg : 0 ≤ᵐ[P] Y) (hY_not_integrable : ¬ Integrable Y P) :
    (∑' n : ℕ, P {ω | (n : ℝ) < Y ω}) = ∞ := by
  -- Proof comment: if the tail-probability series were finite, Chapter 4 would force the
  -- nonnegative integral of `Y` to be finite, contradicting nonintegrability.
  by_contra hfinite
  have hsum_lt_top : (∑' n : ℕ, P {ω | (n : ℝ) < Y ω}) < ∞ := lt_top_iff_ne_top.mpr hfinite
  have hlintegral_lt_top :
      ∫⁻ ω, ENNReal.ofReal (Y ω) ∂P < ∞ := by
    exact lt_of_le_of_lt
      (lintegral_le_tsum_measure_strict_superlevel_nat (μ := P) hY_meas hY_nonneg)
      hsum_lt_top
  have hY_integrable : Integrable Y P := by
    rw [← lintegral_ofReal_ne_top_iff_integrable hY_meas.aestronglyMeasurable hY_nonneg]
    exact hlintegral_lt_top.ne
  exact hY_not_integrable hY_integrable

/-- Helper for Exercise 5.1.4: a measurable version of the shifted i.i.d. family exists and
preserves the i.i.d. structure. -/
lemma measurableShiftedIidVersion
    (P : Measure Ω) [IsProbabilityMeasure P] (X : ℕ → Ω → ℝ)
    (hX_iid : IsIID (fun n ↦ X (n + 1)) P) :
    ∃ Y : ℕ → Ω → ℝ, (∀ n, Measurable (Y n)) ∧ (∀ n, Y n =ᵐ[P] X (n + 1)) ∧ IsIID Y P := by
  -- Proof comment: take the measurable representatives supplied by `AEMeasurable.mk` for each
  -- shifted coordinate and transport both independence and identical distribution across the
  -- coordinatewise a.e. equalities.
  let Y : ℕ → Ω → ℝ := fun n ↦ (hX_iid.identDistrib n 0).aemeasurable_fst.mk (X (n + 1))
  have hY_meas : ∀ n, Measurable (Y n) := by
    intro n
    exact ((hX_iid.identDistrib n 0).aemeasurable_fst).measurable_mk
  have hY_ae : ∀ n, Y n =ᵐ[P] X (n + 1) := by
    intro n
    exact ((hX_iid.identDistrib n 0).aemeasurable_fst).ae_eq_mk.symm
  have hY_indep : iIndepFun Y P := by
    exact hX_iid.iIndepFun.congr (fun n ↦ (hY_ae n).symm)
  have hY_ident : ∀ i j, IdentDistrib (Y i) (Y j) P P := by
    intro i j
    have hXi : IdentDistrib (X (i + 1)) (Y i) P P :=
      ((hX_iid.identDistrib i 0).aemeasurable_fst).identDistrib_mk
    have hXj : IdentDistrib (X (j + 1)) (Y j) P P :=
      ((hX_iid.identDistrib j 0).aemeasurable_fst).identDistrib_mk
    exact hXi.symm.trans ((hX_iid.identDistrib i j).trans hXj)
  exact ⟨Y, hY_meas, hY_ae, ⟨hY_indep, hY_ident⟩⟩

/-- Helper for Exercise 5.1.4: independent measurable coordinates yield an independent family of
measurable threshold-preimage events. -/
lemma iIndepSet_preimage_of_iIndepFun
    {E : Type*} [MeasurableSpace E] (μ : Measure Ω) (Y : ℕ → Ω → E)
    (hY_meas : ∀ n, Measurable (Y n)) (hY_indep : iIndepFun Y μ)
    (s : ℕ → Set E) (hs : ∀ n, MeasurableSet (s n)) :
    iIndepSet (fun n ↦ Y n ⁻¹' s n) μ := by
  -- Proof comment: reduce independence of events to the finite-product formula already packaged
  -- for independent measurable coordinates.
  rw [ProbabilityTheory.iIndepSet_iff_meas_biInter fun i => by
    simpa using (hY_meas i) (hs i)]
  intro t
  simpa using hY_indep.measure_inter_preimage_eq_mul t fun i _ ↦ hs i

end MeasurableHelpers

/-- Helper for Exercise 5.1.4: each threshold hit yields a fixed positive lower bound on the
corresponding weighted exponential term. -/
lemma shiftedWeightedTerm_ge_const_of_linearLowerBound
    (Y : ℕ → Ω → ℝ) (c : Set.Ioo (0 : ℝ) 1) {ω : Ω} (n : ℕ)
    (hn : (-Real.log (c : ℝ)) * n < Y n ω) :
    ENNReal.ofReal (c : ℝ) ≤
      ENNReal.ofReal (Real.exp (Y n ω) * (c : ℝ) ^ (n + 1)) := by
  -- Proof comment: monotonicity of `exp` upgrades the threshold hit to a lower bound on the
  -- exponential factor, and `exp_threshold_mul_pow_eq` turns the threshold term into `c`.
  have hExp :
      Real.exp ((-Real.log (c : ℝ)) * n) ≤ Real.exp (Y n ω) := by
    exact le_of_lt (Real.exp_lt_exp.mpr hn)
  have hPow_nonneg : 0 ≤ (c : ℝ) ^ (n + 1) := by
    exact pow_nonneg c.2.1.le _
  have hMul :
      Real.exp ((-Real.log (c : ℝ)) * n) * (c : ℝ) ^ (n + 1) ≤
        Real.exp (Y n ω) * (c : ℝ) ^ (n + 1) := by
    exact mul_le_mul_of_nonneg_right hExp hPow_nonneg
  have hThreshold :
      Real.exp ((-Real.log (c : ℝ)) * n) * (c : ℝ) ^ (n + 1) = (c : ℝ) := by
    -- Proof comment: rewrite the threshold term once in the spelling used by the monotonicity step.
    exact exp_threshold_mul_pow_eq c n
  have hReal : (c : ℝ) ≤ Real.exp (Y n ω) * (c : ℝ) ^ (n + 1) := by
    calc
      (c : ℝ) = Real.exp ((-Real.log (c : ℝ)) * n) * (c : ℝ) ^ (n + 1) := by
        simpa using hThreshold.symm
      _ ≤ Real.exp (Y n ω) * (c : ℝ) ^ (n + 1) := hMul
  exact ENNReal.ofReal_le_ofReal hReal

/-- Helper for Exercise 5.1.4: if the shifted linear lower threshold `(-log c) * n` is exceeded
infinitely often, then the corresponding shifted weighted exponential series diverges to `∞`. -/
lemma shiftedWeightedExpSeries_eq_top_of_frequently_linearLowerBound
    (Y : ℕ → Ω → ℝ) (c : Set.Ioo (0 : ℝ) 1) {ω : Ω}
    (hω : ∃ᶠ n in atTop, (-Real.log (c : ℝ)) * n < Y n ω) :
    (∑' n, ENNReal.ofReal (Real.exp (Y n ω) * (c : ℝ) ^ (n + 1))) = ∞ := by
  -- Route correction: stay in ENNReal and contradict `term n → 0` with the fixed lower bound
  -- contributed by infinitely many threshold hits.
  let term : ℕ → ℝ≥0∞ := fun n ↦ ENNReal.ofReal (Real.exp (Y n ω) * (c : ℝ) ^ (n + 1))
  by_contra hfinite
  have htend : Tendsto term atTop (nhds 0) := by
    -- Proof comment: a finite ENNReal sum forces its nonnegative summands to tend to zero.
    exact ENNReal.tendsto_atTop_zero_of_tsum_ne_top (by simpa [term] using hfinite)
  have hhalf_pos : 0 < ENNReal.ofReal ((c : ℝ) / 2) := by
    -- Proof comment: the contradiction threshold must stay strictly positive.
    refine ENNReal.ofReal_pos.2 ?_
    nlinarith [c.2.1]
  have hsmall : ∀ᶠ n in atTop, term n ≤ ENNReal.ofReal ((c : ℝ) / 2) := by
    -- Proof comment: eventual smallness comes directly from `term n → 0`.
    rcases (ENNReal.tendsto_atTop_zero.mp htend) (ENNReal.ofReal ((c : ℝ) / 2)) hhalf_pos with
      ⟨N, hN⟩
    exact Filter.eventually_atTop.mpr ⟨N, hN⟩
  have hhalf_lt_c : ENNReal.ofReal ((c : ℝ) / 2) < ENNReal.ofReal (c : ℝ) := by
    -- Proof comment: the frequent lower bound is strictly above the eventual threshold `c / 2`.
    refine (ENNReal.ofReal_lt_ofReal_iff c.2.1).2 ?_
    nlinarith [c.2.1]
  have hlarge : ∃ᶠ n in atTop, ENNReal.ofReal ((c : ℝ) / 2) < term n := by
    -- Proof comment: every threshold hit yields a term at least `c`, hence certainly above `c/2`.
    refine hω.mono ?_
    intro n hn
    have hconst : ENNReal.ofReal (c : ℝ) ≤ term n := by
      simpa [term] using shiftedWeightedTerm_ge_const_of_linearLowerBound Y c n hn
    exact lt_of_lt_of_le hhalf_lt_c hconst
  have hnot_large : ¬ ∃ᶠ n in atTop, ENNReal.ofReal ((c : ℝ) / 2) < term n := by
    -- Proof comment: eventual upper bounds exclude frequent visits above the same threshold.
    rw [Filter.not_frequently]
    exact hsmall.mono fun n hn => not_lt.mpr hn
  exact hnot_large hlarge

-- Proof sketch: apply the Borel--Cantelli lemma to the tail events
-- `{ω | X (n + 1) ω > -(n + 1) * Real.log (c : ℝ) - Real.log ((n + 1 : ℝ)^2)}`. Finite first
-- moment gives summability of the corresponding probabilities, hence eventually
-- `exp (X (n + 1) ω) * (c : ℝ)^(n + 1) ≤ (n + 1)⁻²`, which makes `weightedExpSeries X c ω`
-- surely by comparison with the convergent p-series.
section MainResults

variable [MeasurableSpace Ω]

/-- Exercise 5.1.4 (1): if `X₁, X₂, …` are i.i.d. nonnegative real random variables on a
probability space, `X₁` is almost surely nonnegative, and `X₁` has finite expectation,
equivalently `Integrable (X 1) P` under this nonnegativity hypothesis, then for every
`c ∈ (0, 1)` the weighted exponential series `∑ exp(Xₙ) cⁿ` is finite almost surely. -/
theorem ae_weightedExpSeries_lt_top_of_integrable (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℕ → Ω → ℝ) (c : Set.Ioo (0 : ℝ) 1) (hX_iid : IsIID (fun n ↦ X (n + 1)) P)
    (hX1_nonneg : 0 ≤ᵐ[P] X 1) (hX1_integrable : Integrable (X 1) P) :
    ∀ᵐ ω ∂P, weightedExpSeries X c ω < ∞ := by
  -- Proof comment: apply the first Borel-Cantelli lemma to the summable threshold events
  -- `{(a / 2) * n < X (n + 1)}` after transporting them to a single integrable coordinate.
  letI : MeasureSpace Ω := ⟨P⟩
  let a : ℝ := -Real.log (c : ℝ)
  let Z : Ω → ℝ := fun ω ↦ max ((2 / a) * X 1 ω) 0
  let A : ℕ → Set Ω := fun n ↦ (fun ω ↦ max ((2 / a) * X (n + 1) ω) 0) ⁻¹' Set.Ioi (n : ℝ)
  have ha : 0 < a := by
    dsimp [a]
    exact neg_pos.mpr (Real.log_neg c.2.1 c.2.2)
  have hZ_integrable : Integrable Z := by
    have hscaled : Integrable (fun ω ↦ (2 / a) * X 1 ω) := hX1_integrable.const_mul (2 / a)
    have hZ_eq : Z =ᵐ[P] fun ω ↦ (2 / a) * X 1 ω := by
      filter_upwards [hX1_nonneg] with ω hω
      have hs : 0 ≤ (2 / a) * X 1 ω := by
        exact mul_nonneg (by positivity) hω
      simp [Z, hs]
    simpa using hscaled.congr hZ_eq.symm
  have hZ_nonneg : 0 ≤ Z := by
    intro ω
    exact le_max_right _ _
  have hZ_tsum :
      (∑' n : ℕ, P {ω | Z ω ∈ Set.Ioi (n : ℝ)}) < ∞ := by
    simpa [Z] using ProbabilityTheory.tsum_prob_mem_Ioi_lt_top hZ_integrable hZ_nonneg
  have hZ_pre_tsum :
      (∑' n : ℕ, P ((fun ω ↦ max ((2 / a) * X 1 ω) 0) ⁻¹' Set.Ioi (n : ℝ))) < ∞ := by
    simpa [Set.preimage, Z, Set.mem_Ioi, lt_max_iff] using hZ_tsum
  have hA_tsum : (∑' n : ℕ, P (A n)) < ∞ := by
    calc
      (∑' n : ℕ, P (A n))
          = ∑' n : ℕ, P ((fun ω ↦ max ((2 / a) * X 1 ω) 0) ⁻¹' Set.Ioi (n : ℝ)) := by
              refine tsum_congr fun n ↦ ?_
              have hIdent :
                  IdentDistrib (fun ω ↦ max ((2 / a) * X (n + 1) ω) 0) Z P P := by
                simpa [Z] using (hX_iid.identDistrib n 0).comp (measurable_scaledMax a)
              simpa [A, Z] using hIdent.measure_mem_eq measurableSet_Ioi
      _ < ∞ := hZ_pre_tsum
  filter_upwards [MeasureTheory.ae_eventually_notMem hA_tsum.ne] with ω hω
  have hbound : ∀ᶠ n in atTop, X (n + 1) ω ≤ ((-Real.log (c : ℝ)) / 2) * n := by
    filter_upwards [hω] with n hn
    have hscaled_le : (2 / a) * X (n + 1) ω ≤ (n : ℝ) := by
      simpa [A, Set.preimage, Set.mem_Ioi, not_lt] using hn
    have hmul : (a / 2) * ((2 / a) * X (n + 1) ω) ≤ (a / 2) * (n : ℝ) := by
      exact mul_le_mul_of_nonneg_left hscaled_le (by positivity)
    have hcancel : (a / 2) * ((2 / a) * X (n + 1) ω) = X (n + 1) ω := by
      field_simp [ha.ne']
    simpa [hcancel, a] using hmul
  exact weightedExpSeries_lt_top_of_eventually_linearBound X c hbound

-- Proof sketch: use the same threshold events as in the finite-moment case. When `X 1` is not
-- integrable, equivalently its nonnegative expectation is infinite, a tail-integral estimate
-- together with identical distribution shows that the probabilities of these events have
-- divergent sum; independence and the second Borel--Cantelli lemma then yield infinitely many
-- occurrences almost surely, forcing the partial sums of the nonnegative series to diverge to
-- `∞`.
/-- Exercise 5.1.4 (2): if `X₁, X₂, …` are i.i.d. nonnegative real random variables on a
probability space, `X₁` is almost surely nonnegative, and `X₁` has infinite expectation,
equivalently `¬ Integrable (X 1) P` under this nonnegativity hypothesis, then for every
`c ∈ (0, 1)` the weighted exponential series `∑ exp(Xₙ) cⁿ` is equal to `∞` almost surely. -/
theorem ae_weightedExpSeries_eq_top_of_not_integrable (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℕ → Ω → ℝ) (c : Set.Ioo (0 : ℝ) 1) (hX_iid : IsIID (fun n ↦ X (n + 1)) P)
    (hX1_nonneg : 0 ≤ᵐ[P] X 1) (hX1_not_integrable : ¬ Integrable (X 1) P) :
    ∀ᵐ ω ∂P, weightedExpSeries X c ω = ∞ := by
  -- Proof comment: replace the shifted i.i.d. family by measurable representatives, apply the
  -- second Borel-Cantelli lemma to the exceedance events `{a * n < Y n}`, and finally transport
  -- the shifted series back to `weightedExpSeries`.
  -- Route correction: the divergence closer now lives on the measurable zero-index family `Y n`,
  -- avoiding the earlier brittle `(n)` versus `(n + 1)` transport inside the BC2 assembly.
  let a : ℝ := -Real.log (c : ℝ)
  have ha : 0 < a := by
    dsimp [a]
    exact neg_pos.mpr (Real.log_neg c.2.1 c.2.2)
  rcases measurableShiftedIidVersion P X hX_iid with ⟨Y, hY_meas, hY_ae, hY_iid⟩
  let W : Ω → ℝ := fun ω ↦ (1 / a) * Y 0 ω
  let B : ℕ → Set Ω := fun n ↦ {ω | a * n < Y n ω}
  have hY0_nonneg : 0 ≤ᵐ[P] Y 0 := by
    filter_upwards [hX1_nonneg, hY_ae 0] with ω hω hEq
    simpa [hEq] using hω
  have hW_meas : Measurable W := by
    dsimp [W]
    fun_prop
  have hW_nonneg : 0 ≤ᵐ[P] W := by
    have ha_inv : 0 ≤ 1 / a := by positivity
    filter_upwards [hY0_nonneg] with ω hω
    dsimp [W]
    exact mul_nonneg ha_inv hω
  have hW_not_integrable : ¬ Integrable W P := by
    intro hW_integrable
    have hY0_integrable : Integrable (Y 0) P := by
      simpa [W, mul_assoc, ha.ne'] using hW_integrable.const_mul a
    have hX1_integrable : Integrable (X 1) P := by
      simpa using hY0_integrable.congr (hY_ae 0)
    exact hX1_not_integrable hX1_integrable
  have hB_meas : ∀ n, MeasurableSet (B n) := by
    intro n
    simpa [B, Set.mem_Ioi, Set.preimage, Set.setOf_mem_eq] using
      (hY_meas n) measurableSet_Ioi
  have hB_indep : iIndepSet B P := by
    simpa [B, Set.mem_Ioi, Set.preimage, Set.setOf_mem_eq] using
      iIndepSet_preimage_of_iIndepFun (μ := P) (Y := Y) hY_meas hY_iid.iIndepFun
        (fun n ↦ Set.Ioi (a * n)) fun _ ↦ measurableSet_Ioi
  have hW_tail_eq_top : (∑' n : ℕ, P {ω | (n : ℝ) < W ω}) = ∞ :=
    tailProbTsum_eq_top_of_notIntegrable_nonneg P W hW_meas hW_nonneg hW_not_integrable
  have hB_tsum : (∑' n : ℕ, P (B n)) = ∞ := by
    calc
      (∑' n : ℕ, P (B n))
          = ∑' n : ℕ, P {ω | a * n < Y 0 ω} := by
              refine tsum_congr fun n ↦ ?_
              simpa [B, Set.mem_Ioi] using
                (hY_iid.identDistrib n 0).measure_mem_eq measurableSet_Ioi
      _ = ∑' n : ℕ, P {ω | (n : ℝ) < W ω} := by
            refine tsum_congr fun n ↦ ?_
            congr 1
            ext ω
            constructor
            · intro hω
              have hω' : (1 / a) * (a * (n : ℝ)) < (1 / a) * Y 0 ω := by
                exact mul_lt_mul_of_pos_left hω (one_div_pos.mpr ha)
              simpa [W, mul_assoc, ha.ne'] using hω'
            · intro hω
              have hω' : a * (n : ℝ) < a * W ω := by
                exact mul_lt_mul_of_pos_left hω ha
              simpa [W, mul_assoc, ha.ne'] using hω'
      _ = ∞ := hW_tail_eq_top
  have hB_limsup_one : P (limsup B atTop) = 1 := by
    simpa using ProbabilityTheory.measure_limsup_eq_one (μ := P) (s := B) hB_meas hB_indep hB_tsum
  have hB_limsup_ae : ∀ᵐ ω ∂P, ω ∈ limsup B atTop := by
    rw [ae_iff]
    have hcompl : P ((limsup B atTop)ᶜ) = 0 := by
      have hB_limsup_meas : MeasurableSet (limsup B atTop) := by
        rw [limsup_eq_iInf_iSup_of_nat]
        exact MeasurableSet.iInter fun n => MeasurableSet.iUnion fun m =>
          MeasurableSet.iUnion fun _ => hB_meas m
      rw [measure_compl hB_limsup_meas (measure_ne_top P _), hB_limsup_one, measure_univ]
      simp
    simpa [Set.setOf_mem_eq] using hcompl
  filter_upwards [hB_limsup_ae, ae_all_iff.2 hY_ae] with ω hω hEq
  have hshift_top :
      (∑' n, ENNReal.ofReal (Real.exp (Y n ω) * (c : ℝ) ^ (n + 1))) = ∞ := by
    have hfreq : ∃ᶠ n in atTop, (-Real.log (c : ℝ)) * n < Y n ω := by
      simpa [B, a, mem_limsup_iff_frequently_mem, Set.mem_setOf_eq] using hω
    exact shiftedWeightedExpSeries_eq_top_of_frequently_linearLowerBound Y c hfreq
  have hseries_eq :
      (∑' n, ENNReal.ofReal (Real.exp (Y n ω) * (c : ℝ) ^ (n + 1))) =
        weightedExpSeries X c ω := by
    rw [weightedExpSeries]
    refine tsum_congr fun n ↦ ?_
    rw [hEq n]
  simpa [hseries_eq] using hshift_top

end MainResults
