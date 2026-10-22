/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib
import Books.ProbabilityTheory_Klenke_2020.Items.Chap03.Definition_3_1

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators Topology

/-- Helper for Theorem 3.2: the real pgf is the scalar power-series sum attached to the
coefficients `(p n).toReal`. -/
theorem probabilityGeneratingFunctionReal_eq_ofScalarsSum (p : PMF ℕ) :
    probabilityGeneratingFunctionReal p =
      FormalMultilinearSeries.ofScalarsSum (E := ℝ) (fun n : ℕ => (p n).toReal) := by
  -- Rewrite the formal-series sum into the concrete scalar `tsum`.
  rw [FormalMultilinearSeries.ofScalarsSum_eq_tsum]
  funext z
  simp [probabilityGeneratingFunctionReal, smul_eq_mul]

/-- Helper for Theorem 3.2: the real pgf has its scalar formal power series expansion on the open
unit ball. -/
theorem probabilityGeneratingFunctionReal_hasFPowerSeriesOnBall_one (p : PMF ℕ) :
    HasFPowerSeriesOnBall (probabilityGeneratingFunctionReal p)
      (FormalMultilinearSeries.ofScalars ℝ (fun n : ℕ => (p n).toReal)) 0 1 := by
  let q : FormalMultilinearSeries ℝ ℝ ℝ :=
    FormalMultilinearSeries.ofScalars ℝ (fun n : ℕ => (p n).toReal)
  have hs : Summable (fun n : ℕ => ‖q n‖ * (1 : ℝ) ^ n) := by
    -- The PMF coefficients already have total mass `1`, so the scalar coefficients are summable.
    simpa [q] using ENNReal.summable_toReal p.tsum_coe_ne_top
  have hradius : (1 : ENNReal) ≤ q.radius := q.le_radius_of_summable hs
  have hq : HasFPowerSeriesOnBall (fun x : ℝ ↦ q.sum x) q 0 1 := by
    -- Restrict the full power-series expansion to the unit ball.
    refine (q.hasFPowerSeriesOnBall ?_).mono (by simp) hradius
    exact lt_of_lt_of_le (by simp) hradius
  simpa [q, probabilityGeneratingFunctionReal_eq_ofScalarsSum p] using hq

/-- Helper for Theorem 3.2: if the pgf coefficients are summable against `z^n` with `z > 1`, then
the same scalar power series represents the pgf on the larger ball of radius `z`. -/
theorem probabilityGeneratingFunctionReal_hasFPowerSeriesOnBall_of_summable
    (p : PMF ℕ) {z : ℝ} (hz₁ : 1 < z)
    (hpz : Summable (fun n : ℕ ↦ (p n).toReal * z ^ n)) :
    HasFPowerSeriesOnBall (probabilityGeneratingFunctionReal p)
      (FormalMultilinearSeries.ofScalars ℝ (fun n : ℕ => (p n).toReal)) 0 (Real.toNNReal z) := by
  have hz0 : 0 ≤ z := le_of_lt (lt_trans zero_lt_one hz₁)
  have hzt : 0 < z := lt_trans zero_lt_one hz₁
  let q : FormalMultilinearSeries ℝ ℝ ℝ :=
    FormalMultilinearSeries.ofScalars ℝ (fun n : ℕ => (p n).toReal)
  have hs : Summable (fun n : ℕ => ‖q n‖ * ((Real.toNNReal z : ℝ)) ^ n) := by
    -- Replace `toNNReal z` by `z` using positivity of `z`.
    simpa [q, Real.toNNReal_of_nonneg hz0] using hpz
  have hradius : (Real.toNNReal z : ENNReal) ≤ q.radius := q.le_radius_of_summable hs
  have hrpos : 0 < Real.toNNReal z := Real.toNNReal_pos.mpr hzt
  have hq : HasFPowerSeriesOnBall (fun x : ℝ ↦ q.sum x) q 0 (Real.toNNReal z) := by
    -- First obtain the full expansion on the convergence ball, then shrink to radius `z`.
    refine (q.hasFPowerSeriesOnBall (lt_of_lt_of_le (by exact_mod_cast hrpos) hradius)).mono ?_
      hradius
    exact_mod_cast hrpos
  simpa [q, probabilityGeneratingFunctionReal_eq_ofScalarsSum p] using hq

-- Proof sketch: view the pgf as a power series with nonnegative coefficients and use the standard
-- continuity of a convergent power series on the closed interval `[0,1]`.
/-- Theorem 3.2 (1): Item (i). The probability generating function is continuous on `[0,1]`. -/
theorem probabilityGeneratingFunctionReal_continuousOn_unitInterval (p : PMF ℕ) :
    ContinuousOn (probabilityGeneratingFunctionReal p) (Set.Icc (0 : ℝ) 1) := by
  let f : ℕ → ℝ → ℝ := fun n z ↦ (p n).toReal * z ^ n
  have hf : ∀ n, ContinuousOn (f n) (Set.Icc (0 : ℝ) 1) := by
    -- Each summand is a polynomial in `z`.
    intro n
    exact (continuous_const.mul (continuous_pow n)).continuousOn
  have hs : Summable (fun n : ℕ => (p n).toReal) := ENNReal.summable_toReal p.tsum_coe_ne_top
  have hbound : ∀ n z, z ∈ Set.Icc (0 : ℝ) 1 → ‖f n z‖ ≤ (p n).toReal := by
    intro n z hz
    rcases hz with ⟨hz0, hz1⟩
    have hzpow : z ^ n ≤ 1 := pow_le_one₀ hz0 hz1
    have hzpow_nonneg : 0 ≤ z ^ n := pow_nonneg hz0 _
    -- On `[0,1]`, every factor `z^n` is bounded by `1`, so the coefficients dominate uniformly.
    calc
      ‖f n z‖ = (p n).toReal * z ^ n := by
        simp [f, Real.norm_eq_abs, abs_of_nonneg hz0, abs_of_nonneg ENNReal.toReal_nonneg]
      _ ≤ (p n).toReal * 1 := by gcongr
      _ = (p n).toReal := by simp
  simpa [f, probabilityGeneratingFunctionReal] using continuousOn_tsum hf hs hbound

-- Proof sketch: a power series is real-analytic on the interior of its disk of convergence, hence
-- `C^∞` on `(0,1)`.
/-- Theorem 3.2 (2): Item (i). The probability generating function is infinitely often continuously
differentiable on `(0,1)`. -/
theorem probabilityGeneratingFunctionReal_contDiffOn_unitIntervalInterior (p : PMF ℕ) :
    ContDiffOn ℝ ⊤ (probabilityGeneratingFunctionReal p) (Set.Ioo (0 : ℝ) 1) := by
  have hanalytic : AnalyticOnNhd ℝ (probabilityGeneratingFunctionReal p) (Set.Ioo (0 : ℝ) 1) := by
    -- The interior interval sits inside the open unit ball where the pgf is represented by its
    -- scalar power series.
    refine (probabilityGeneratingFunctionReal_hasFPowerSeriesOnBall_one p).analyticOnNhd.mono ?_
    intro x hx
    rw [Metric.mem_eball, edist_zero_right, enorm_eq_nnnorm, ENNReal.coe_lt_one_iff,
      ← NNReal.coe_lt_one, coe_nnnorm]
    simpa [Real.norm_eq_abs, abs_of_pos hx.1] using hx.2
  -- Analyticity on a neighborhood gives `C^∞` regularity on the interval.
  exact hanalytic.contDiffOn_of_completeSpace

/-- Helper for Theorem 3.2: differentiating a scalar formal power series shifts the coefficients
and multiplies by the expected linear factor. -/
theorem probabilityGeneratingFunctionReal_ofScalars_derivSeries
    (c : ℕ → ℝ) :
    (ContinuousLinearMap.apply ℝ ℝ (1 : ℝ)).compFormalMultilinearSeries
        ((FormalMultilinearSeries.ofScalars ℝ c).derivSeries) =
      FormalMultilinearSeries.ofScalars ℝ (fun m : ℕ ↦ c (m + 1) * (m + 1 : ℝ)) := by
  -- Evaluate the derivative-series coefficient at `1`; for scalar series this is exactly
  -- `(m + 1) * c (m + 1)`.
  ext m
  simp [ContinuousLinearMap.compFormalMultilinearSeries_apply,
    FormalMultilinearSeries.derivSeries_coeff_one,
    FormalMultilinearSeries.coeff_ofScalars, smul_eq_mul, mul_comm]

/-- Helper for Theorem 3.2: every iterated derivative of the real pgf still has radius-`1`
power-series expansion, with the expected descending-factorial coefficients. -/
theorem probabilityGeneratingFunctionReal_iteratedDeriv_hasFPowerSeriesOnBall
    (p : PMF ℕ) (n : ℕ) :
    HasFPowerSeriesOnBall (iteratedDeriv n (probabilityGeneratingFunctionReal p))
      (FormalMultilinearSeries.ofScalars ℝ
        (fun m : ℕ ↦ (p (m + n)).toReal * (Nat.descFactorial (m + n) n : ℝ))) 0 1 := by
  induction n with
  | zero =>
      -- The zeroth derivative is the pgf itself.
      simpa using probabilityGeneratingFunctionReal_hasFPowerSeriesOnBall_one p
  | succ n ih =>
      have hderiv :
          HasFPowerSeriesOnBall (deriv (iteratedDeriv n (probabilityGeneratingFunctionReal p)))
            ((ContinuousLinearMap.apply ℝ ℝ (1 : ℝ)).compFormalMultilinearSeries
              ((FormalMultilinearSeries.ofScalars ℝ
                (fun m : ℕ ↦ (p (m + n)).toReal *
                  (Nat.descFactorial (m + n) n : ℝ))).derivSeries))
            0 1 := by
        -- Differentiate the already identified `n`th-derivative series once more.
        simpa [Function.comp] using
          (ContinuousLinearMap.apply ℝ ℝ (1 : ℝ)).comp_hasFPowerSeriesOnBall ih.fderiv
      -- Rewrite the differentiated coefficients into the `(n + 1)`st descending-factorial form.
      simpa [iteratedDeriv_succ, probabilityGeneratingFunctionReal_ofScalars_derivSeries,
        Nat.descFactorial_succ, Nat.cast_mul, add_assoc, add_left_comm, add_comm,
        mul_assoc, mul_left_comm, mul_comm] using hderiv

/-- Helper for Theorem 3.2: on the open unit interval, the `n`th derivative of the real pgf is
given by the shifted descending-factorial power series. -/
theorem probabilityGeneratingFunctionReal_iteratedDeriv_eq_series
    (p : PMF ℕ) (n : ℕ) {x : ℝ} (hx : x ∈ Set.Ioo (0 : ℝ) 1) :
    iteratedDeriv n (probabilityGeneratingFunctionReal p) x =
      ∑' m : ℕ, (p (m + n)).toReal * (Nat.descFactorial (m + n) n : ℝ) * x ^ m := by
  have hxball : x ∈ Metric.eball (0 : ℝ) 1 := by
    rw [Metric.mem_eball, edist_zero_right, enorm_eq_nnnorm, ENNReal.coe_lt_one_iff,
      ← NNReal.coe_lt_one, coe_nnnorm]
    simpa [Real.norm_eq_abs, abs_of_pos hx.1] using hx.2
  -- Evaluate the radius-`1` power series at the interior point `x`.
  simpa [FormalMultilinearSeries.ofScalars_apply_eq, smul_eq_mul, mul_assoc, mul_left_comm,
    mul_comm] using
    (probabilityGeneratingFunctionReal_iteratedDeriv_hasFPowerSeriesOnBall p n).hasSum_sub hxball
      |>.tsum_eq.symm

/-- Helper for Theorem 3.2: casting one shifted real-series term into `ENNReal` splits into the
coefficient factor and the power factor. -/
theorem probabilityGeneratingFunctionReal_shifted_series_term_ofReal
    (p : PMF ℕ) (m n : ℕ) {x : ℝ} (hx : x ∈ Set.Ioo (0 : ℝ) 1) :
    ENNReal.ofReal (((p (m + n)).toReal * (Nat.descFactorial (m + n) n : ℝ)) * x ^ m) =
      p (m + n) * (Nat.descFactorial (m + n) n : ENNReal) * ENNReal.ofReal (x ^ m) := by
  have hp : 0 ≤ (p (m + n)).toReal := ENNReal.toReal_nonneg
  have hdesc : 0 ≤ (Nat.descFactorial (m + n) n : ℝ) := by positivity
  have hpow : 0 ≤ x ^ m := pow_nonneg (le_of_lt hx.1) _
  -- Split the cast through the two nonnegative real factors.
  calc
    ENNReal.ofReal (((p (m + n)).toReal * (Nat.descFactorial (m + n) n : ℝ)) * x ^ m)
        =
          ENNReal.ofReal ((p (m + n)).toReal * (Nat.descFactorial (m + n) n : ℝ)) *
            ENNReal.ofReal (x ^ m) := by
          rw [ENNReal.ofReal_mul]
          positivity
    _ =
          (ENNReal.ofReal ((p (m + n)).toReal) *
              ENNReal.ofReal (Nat.descFactorial (m + n) n : ℝ)) *
            ENNReal.ofReal (x ^ m) := by
          rw [ENNReal.ofReal_mul]
          positivity
    _ =
          (p (m + n) * (Nat.descFactorial (m + n) n : ENNReal)) *
            ENNReal.ofReal (x ^ m) := by
          rw [ENNReal.ofReal_toReal (p.apply_ne_top (m + n)), ENNReal.ofReal_natCast]
    _ =
          p (m + n) * (Nat.descFactorial (m + n) n : ENNReal) *
            ENNReal.ofReal (x ^ m) := by
          rw [mul_assoc]

/-- Helper for Theorem 3.2: the interior derivative series becomes a nonnegative `ENNReal`
series after casting termwise. -/
theorem probabilityGeneratingFunctionReal_iteratedDeriv_eq_series_ennreal
    (p : PMF ℕ) (n : ℕ) {x : ℝ} (hx : x ∈ Set.Ioo (0 : ℝ) 1) :
    ENNReal.ofReal (iteratedDeriv n (probabilityGeneratingFunctionReal p) x) =
      ∑' m : ℕ, p (m + n) * (Nat.descFactorial (m + n) n : ENNReal) *
        ENNReal.ofReal (x ^ m) := by
  have hxball : x ∈ Metric.eball (0 : ℝ) 1 := by
    rw [Metric.mem_eball, edist_zero_right, enorm_eq_nnnorm, ENNReal.coe_lt_one_iff,
      ← NNReal.coe_lt_one, coe_nnnorm]
    simpa [Real.norm_eq_abs, abs_of_pos hx.1] using hx.2
  have hsum :
      HasSum (fun m : ℕ ↦
          (p (m + n)).toReal * (Nat.descFactorial (m + n) n : ℝ) * x ^ m)
        (iteratedDeriv n (probabilityGeneratingFunctionReal p) x) := by
    -- Reuse the already established real power-series identity as a `HasSum`.
    simpa [probabilityGeneratingFunctionReal_iteratedDeriv_eq_series p n hx,
      mul_assoc, mul_left_comm, mul_comm] using
      (probabilityGeneratingFunctionReal_iteratedDeriv_hasFPowerSeriesOnBall p n).hasSum_sub hxball
  have hnonneg :
      ∀ m : ℕ, 0 ≤ (p (m + n)).toReal * (Nat.descFactorial (m + n) n : ℝ) * x ^ m := by
    intro m
    exact mul_nonneg (mul_nonneg ENNReal.toReal_nonneg (by positivity))
      (pow_nonneg (le_of_lt hx.1) _)
  -- Route the whole `tsum` through `ENNReal.ofReal`, then normalize each term once and for all.
  rw [probabilityGeneratingFunctionReal_iteratedDeriv_eq_series p n hx]
  rw [ENNReal.ofReal_tsum_of_nonneg hnonneg hsum.summable]
  congr with m
  simpa [mul_assoc, mul_left_comm, mul_comm] using
    probabilityGeneratingFunctionReal_shifted_series_term_ofReal p m n hx

/-- Helper for Theorem 3.2: the shifted factorial-moment series is the same as the full series,
because the first `n` descending-factorial terms vanish. -/
theorem probabilityGeneratingFunctionReal_factorialMoment_tsum_eq_shifted
    (p : PMF ℕ) (n : ℕ) :
    (∑' m : ℕ, p (m + n) * (Nat.descFactorial (m + n) n : ENNReal)) =
      ∑' k : ℕ, p k * (Nat.descFactorial k n : ENNReal) := by
  let f : ℕ → ENNReal := fun k ↦ p k * (Nat.descFactorial k n : ENNReal)
  have hzero : ∑ i ∈ Finset.range n, f i = 0 := by
    -- The initial segment contributes nothing because `Nat.descFactorial k n = 0` for `k < n`.
    apply Finset.sum_eq_zero
    intro i hi
    have hi' : i < n := Finset.mem_range.mp hi
    simp [f, Nat.descFactorial_eq_zero_iff_lt.mpr hi']
  have hsplit :
      ∑ i ∈ Finset.range n, f i + ∑' i : ℕ, f (i + n) = ∑' i : ℕ, f i := by
    simpa using
      (ENNReal.summable (f := fun i : ℕ ↦ f (i + n))).sum_add_tsum_nat_add' (f := f)
  simpa [f, hzero]
    using hsplit

/-- Helper for Theorem 3.2: every finite shifted prefix of the `ENNReal` derivative series tends
to the corresponding factorial-moment prefix as `x ↑ 1`. -/
theorem probabilityGeneratingFunctionReal_shifted_prefix_tendsto_left_one
    (p : PMF ℕ) (n N : ℕ) :
    Filter.Tendsto
      (fun x : ℝ ↦
        Finset.sum (Finset.range N) fun m ↦
          p (m + n) * (Nat.descFactorial (m + n) n : ENNReal) * ENNReal.ofReal (x ^ m))
      (nhdsWithin (1 : ℝ) (Set.Iio 1))
      (nhds <| Finset.sum (Finset.range N) fun m ↦
        p (m + n) * (Nat.descFactorial (m + n) n : ENNReal)) := by
  -- Reduce the finite-prefix limit to convergence of each fixed summand.
  refine tendsto_finset_sum (Finset.range N) ?_
  intro m hm
  have hcoeff_ne_top :
      p (m + n) * (Nat.descFactorial (m + n) n : ENNReal) ≠ ⊤ := by
    exact ENNReal.mul_ne_top (p.apply_ne_top (m + n))
      (ENNReal.natCast_ne_top (Nat.descFactorial (m + n) n))
  have hpowWithin : ContinuousWithinAt (fun x : ℝ ↦ x ^ m) (Set.Iio 1) (1 : ℝ) :=
    continuousWithinAt_id.pow m
  have hpow :
      Filter.Tendsto (fun x : ℝ ↦ x ^ m)
        (nhdsWithin (1 : ℝ) (Set.Iio 1))
        (nhdsWithin ((1 : ℝ) ^ m) ((fun x : ℝ ↦ x ^ m) '' Set.Iio 1)) :=
    hpowWithin.tendsto_nhdsWithin_image
  have hofReal :
      Filter.Tendsto ENNReal.ofReal
        (nhdsWithin ((1 : ℝ) ^ m) ((fun x : ℝ ↦ x ^ m) '' Set.Iio 1))
        (nhdsWithin (ENNReal.ofReal ((1 : ℝ) ^ m))
          (ENNReal.ofReal '' ((fun x : ℝ ↦ x ^ m) '' Set.Iio 1))) :=
    ENNReal.continuous_ofReal.continuousAt.continuousWithinAt.tendsto_nhdsWithin_image
  have hbase :
      Filter.Tendsto (fun x : ℝ ↦ ENNReal.ofReal (x ^ m))
        (nhdsWithin (1 : ℝ) (Set.Iio 1))
        (nhdsWithin (ENNReal.ofReal ((1 : ℝ) ^ m))
          (ENNReal.ofReal '' ((fun x : ℝ ↦ x ^ m) '' Set.Iio 1))) := by
    simpa [Function.comp] using hofReal.comp hpow
  have hbase' :
      Filter.Tendsto (fun x : ℝ ↦ ENNReal.ofReal (x ^ m))
        (nhdsWithin (1 : ℝ) (Set.Iio 1))
        (nhds (1 : ENNReal)) := by
    have hle :
        nhdsWithin (ENNReal.ofReal ((1 : ℝ) ^ m))
          (ENNReal.ofReal '' ((fun x : ℝ ↦ x ^ m) '' Set.Iio 1)) ≤
          nhds (ENNReal.ofReal ((1 : ℝ) ^ m)) :=
      nhdsWithin_le_nhds
    simpa [one_pow, ENNReal.ofReal_one] using hbase.mono_right hle
  -- A finite `ENNReal` coefficient preserves the limit of the power factor.
  have hmul :
      Continuous
        (fun y : ENNReal ↦ p (m + n) * (Nat.descFactorial (m + n) n : ENNReal) * y) := by
    simpa [mul_assoc] using
      ENNReal.continuous_const_mul hcoeff_ne_top
  simpa [mul_assoc] using hmul.continuousAt.tendsto.comp hbase'

/-- Helper for Theorem 3.2: on `(0, 1)`, the `ENNReal` derivative series is bounded above by the
factorial-moment series at `1`. -/
theorem probabilityGeneratingFunctionReal_iteratedDeriv_le_factorialMoment_tsum
    (p : PMF ℕ) (n : ℕ) {x : ℝ} (hx : x ∈ Set.Ioo (0 : ℝ) 1) :
    ENNReal.ofReal (iteratedDeriv n (probabilityGeneratingFunctionReal p) x) ≤
      ∑' k : ℕ, p k * (Nat.descFactorial k n : ENNReal) := by
  have hterm_le :
      ∀ m : ℕ,
        p (m + n) * (Nat.descFactorial (m + n) n : ENNReal) * ENNReal.ofReal (x ^ m) ≤
          p (m + n) * (Nat.descFactorial (m + n) n : ENNReal) := by
    intro m
    have hpow_le : x ^ m ≤ 1 := pow_le_one₀ (le_of_lt hx.1) (le_of_lt hx.2)
    have hofReal_le_one : ENNReal.ofReal (x ^ m) ≤ 1 := by
      simpa [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal hpow_le
    -- Bound each shifted term by replacing `x ^ m` with `1`.
    simpa [mul_assoc] using
      mul_le_mul_right hofReal_le_one (p (m + n) * (Nat.descFactorial (m + n) n : ENNReal))
  -- Compare the entire derivative series termwise with the factorial-moment series at `1`.
  calc
    ENNReal.ofReal (iteratedDeriv n (probabilityGeneratingFunctionReal p) x)
        =
          ∑' m : ℕ,
            p (m + n) * (Nat.descFactorial (m + n) n : ENNReal) * ENNReal.ofReal (x ^ m) :=
      probabilityGeneratingFunctionReal_iteratedDeriv_eq_series_ennreal p n hx
    _ ≤ ∑' m : ℕ, p (m + n) * (Nat.descFactorial (m + n) n : ENNReal) :=
      ENNReal.tsum_le_tsum hterm_le
    _ = ∑' k : ℕ, p k * (Nat.descFactorial k n : ENNReal) :=
      probabilityGeneratingFunctionReal_factorialMoment_tsum_eq_shifted p n

-- Proof sketch: differentiate the power series termwise on `(0,1)`, identify the coefficients of
-- the `n`th derivative with the descending factorials, and then apply Abel's theorem to the
-- resulting nonnegative power series.
/-- Theorem 3.2 (3): Item (i). The left limit of the `n`th derivative at `1` is the factorial
moment series `∑' k, P[X = k] · k (k - 1) ··· (k - n + 1)`, interpreted in `ENNReal`. -/
theorem probabilityGeneratingFunctionReal_iteratedDeriv_tendsto_left_one (p : PMF ℕ) (n : ℕ) :
    Filter.Tendsto
      (fun z : ℝ ↦ ENNReal.ofReal (iteratedDeriv n (probabilityGeneratingFunctionReal p) z))
      (nhdsWithin (1 : ℝ) (Set.Iio 1))
      (𝓝 (∑' k : ℕ, p k * (Nat.descFactorial k n : ENNReal))) := by
  -- Route correction: isolate the ENNReal normalization and the finite-prefix convergence first,
  -- then close the left-limit statement with `tendsto_order`.
  let shiftedPrefix :
      ℕ → ℝ → ENNReal := fun N x ↦
        Finset.sum (Finset.range N) fun m ↦
          p (m + n) * (Nat.descFactorial (m + n) n : ENNReal) * ENNReal.ofReal (x ^ m)
  have hIoo :
      ∀ᶠ x in nhdsWithin (1 : ℝ) (Set.Iio 1), x ∈ Set.Ioo (0 : ℝ) 1 := by
    have hmem :
        Set.Ioi (0 : ℝ) ∩ Set.Iio (1 : ℝ) ∈ nhdsWithin (1 : ℝ) (Set.Iio 1) := by
      rw [nhdsWithin, Filter.mem_inf_iff]
      exact ⟨Set.Ioi (0 : ℝ), Ioi_mem_nhds zero_lt_one, Set.Iio (1 : ℝ), by simp, rfl⟩
    refine Filter.mem_of_superset hmem ?_
    intro x hx
    exact ⟨hx.1, hx.2⟩
  rw [tendsto_order]
  constructor
  · intro b hb
    have hb_shifted :
        b < ∑' m : ℕ, p (m + n) * (Nat.descFactorial (m + n) n : ENNReal) := by
      simpa [probabilityGeneratingFunctionReal_factorialMoment_tsum_eq_shifted p n] using hb
    rw [ENNReal.tsum_eq_iSup_nat] at hb_shifted
    rw [lt_iSup_iff] at hb_shifted
    rcases hb_shifted with ⟨N, hN⟩
    have hprefix :
        Filter.Tendsto (shiftedPrefix N)
          (nhdsWithin (1 : ℝ) (Set.Iio 1))
          (nhds <| Finset.sum (Finset.range N) fun m ↦
            p (m + n) * (Nat.descFactorial (m + n) n : ENNReal)) :=
      probabilityGeneratingFunctionReal_shifted_prefix_tendsto_left_one p n N
    have hprefix_event :
        ∀ᶠ x in nhdsWithin (1 : ℝ) (Set.Iio 1), b < shiftedPrefix N x :=
      (tendsto_order.1 hprefix).1 b hN
    filter_upwards [hprefix_event, hIoo] with x hxPrefix hxIoo
    have hprefix_le :
        shiftedPrefix N x ≤
          ENNReal.ofReal (iteratedDeriv n (probabilityGeneratingFunctionReal p) x) := by
      rw [probabilityGeneratingFunctionReal_iteratedDeriv_eq_series_ennreal p n hxIoo]
      exact ENNReal.sum_le_tsum (Finset.range N)
    exact lt_of_lt_of_le hxPrefix hprefix_le
  · intro b hb
    filter_upwards [hIoo] with x hxIoo
    exact lt_of_le_of_lt
      (probabilityGeneratingFunctionReal_iteratedDeriv_le_factorialMoment_tsum p n hxIoo) hb

/-- Helper for Theorem 3.2: agreement of the real pgfs on a neighborhood of `0` forces equality
of the underlying laws. -/
theorem pmf_eq_of_probabilityGeneratingFunctionReal_eventuallyEq
    {p q : PMF ℕ}
    (hEq : probabilityGeneratingFunctionReal p =ᶠ[𝓝 (0 : ℝ)] probabilityGeneratingFunctionReal q) :
    p = q := by
  -- Compare the Taylor expansions at the origin and read off the coefficients.
  have hp :
      HasFPowerSeriesAt (probabilityGeneratingFunctionReal p)
        (FormalMultilinearSeries.ofScalars ℝ (fun n : ℕ => (p n).toReal)) 0 :=
    (probabilityGeneratingFunctionReal_hasFPowerSeriesOnBall_one p).hasFPowerSeriesAt
  have hq :
      HasFPowerSeriesAt (probabilityGeneratingFunctionReal q)
        (FormalMultilinearSeries.ofScalars ℝ (fun n : ℕ => (q n).toReal)) 0 :=
    (probabilityGeneratingFunctionReal_hasFPowerSeriesOnBall_one q).hasFPowerSeriesAt
  have hseries :
      FormalMultilinearSeries.ofScalars ℝ (fun n : ℕ => (p n).toReal) =
        FormalMultilinearSeries.ofScalars ℝ (fun n : ℕ => (q n).toReal) :=
    hp.eq_formalMultilinearSeries_of_eventually hq hEq
  apply PMF.ext
  intro n
  have hcoeff :=
    congrArg (fun s : FormalMultilinearSeries ℝ ℝ ℝ => s.coeff n) hseries
  refine (ENNReal.toReal_eq_toReal_iff'
      (p.apply_ne_top n) (q.apply_ne_top n)).mp ?_
  -- The coefficient of the scalar formal power series is exactly the original mass.
  simpa [FormalMultilinearSeries.coeff_ofScalars] using hcoeff

-- Proof sketch: equality of power series on `[0,1]` gives equality of all Taylor coefficients at
-- `0`, so the masses `p n` and `q n` agree termwise; equivalently, use uniqueness of analytic
-- expansions at the origin.
/-- Theorem 3.2 (4): Item (ii). The law on `ℕ` is uniquely determined by its probability
generating function. -/
-- TODO: use the radius-`1` formal power-series representation at `0`, recover the scalar
-- coefficients via formal-series uniqueness, and finish with `PMF.ext`.
theorem probabilityGeneratingFunctionReal_injective :
    Function.Injective probabilityGeneratingFunctionReal := by
  intro p q hpgf
  -- Global equality certainly gives equality on every neighborhood of the origin.
  exact pmf_eq_of_probabilityGeneratingFunctionReal_eventuallyEq <| Filter.EventuallyEq.of_eq hpgf

/-- Helper for Theorem 3.2: the standard sampling sequence approaches `r` through points distinct
from `r`. -/
theorem samplingPoints_tendsto_puncturedNhds {r : ℝ} (hr₀ : 0 < r) :
    Filter.Tendsto (fun n : ℕ => r * (((n : ℝ) + 1) / ((n : ℝ) + 2))) Filter.atTop (𝓝[≠] r) := by
  rw [tendsto_nhdsWithin_iff]
  refine ⟨?_, ?_⟩
  · -- Rewrite the ratio as `1 - 1 / (n + 2)` to get the ambient limit.
    have hdiv :
        Filter.Tendsto (fun n : ℕ => (((n : ℝ) + 1) / ((n : ℝ) + 2))) Filter.atTop (𝓝 (1 : ℝ)) := by
      have hinv :
          Filter.Tendsto (fun n : ℕ => (((n : ℝ) + 2) : ℝ)⁻¹) Filter.atTop (𝓝 (0 : ℝ)) := by
        simpa using
          (tendsto_mul_add_inv_atTop_nhds_zero 1 2 one_ne_zero).comp tendsto_natCast_atTop_atTop
      have hone :
          Filter.Tendsto (fun n : ℕ => (1 : ℝ) - (((n : ℝ) + 2) : ℝ)⁻¹) Filter.atTop (𝓝 (1 : ℝ)) := by
        simpa using tendsto_const_nhds.sub hinv
      refine hone.congr' ?_
      exact Filter.Eventually.of_forall fun n => by
        field_simp
        ring
    simpa using hdiv.const_mul r
  · -- Every sampling point is strictly smaller than `r`, so the sequence stays punctured.
    exact Filter.Eventually.of_forall fun n => by
      have hfrac_pos : 0 < (((n : ℝ) + 1) / ((n : ℝ) + 2)) := by positivity
      have hfrac_lt : (((n : ℝ) + 1) / ((n : ℝ) + 2)) < 1 := by
        have hden : 0 < ((n : ℝ) + 2) := by positivity
        exact (div_lt_one hden).2 <| by linarith
      have hlt : r * (((n : ℝ) + 1) / ((n : ℝ) + 2)) < r := by
        nlinarith
      exact ne_of_lt hlt

-- Proof sketch: choose the countable sampling set `r * (n + 1) / (n + 2)`, which lies in `[0,r]`
-- and converges to `r`. Analytic uniqueness for power series on `(-1,1)` shows that agreement on
-- this set forces agreement of the two pgfs everywhere.
/-- Theorem 3.2 (5): Item (iii). For every `r ∈ (0,1)`, the pgf is determined by the countable
family of values at the points `r * (n + 1) / (n + 2) ∈ [0,r]`. -/
-- TODO: show the sampling sequence accumulates at `r` inside `(-1,1)` and apply the analytic
-- identity theorem on the open unit ball coming from `probabilityGeneratingFunctionReal_hasFPowerSeriesOnBall_one`.
theorem probabilityGeneratingFunctionReal_eq_of_agree_on_samplingPoints
    {p q : PMF ℕ} {r : ℝ} (hr₀ : 0 < r) (hr₁ : r < 1)
    (h_values :
      ∀ n : ℕ,
        probabilityGeneratingFunctionReal p (r * (((n : ℝ) + 1) / ((n : ℝ) + 2))) =
          probabilityGeneratingFunctionReal q (r * (((n : ℝ) + 1) / ((n : ℝ) + 2)))) :
    probabilityGeneratingFunctionReal p = probabilityGeneratingFunctionReal q := by
  let U : Set ℝ := Set.Ioo (-1 : ℝ) 1
  have hpAnalytic : AnalyticOnNhd ℝ (probabilityGeneratingFunctionReal p) U := by
    -- The open interval sits inside the radius-`1` convergence ball.
    refine (probabilityGeneratingFunctionReal_hasFPowerSeriesOnBall_one p).analyticOnNhd.mono ?_
    intro x hx
    rw [Metric.mem_eball, edist_zero_right, enorm_eq_nnnorm, ENNReal.coe_lt_one_iff,
      ← NNReal.coe_lt_one, coe_nnnorm]
    simpa [Real.norm_eq_abs, abs_lt] using hx
  have hqAnalytic : AnalyticOnNhd ℝ (probabilityGeneratingFunctionReal q) U := by
    -- The same analytic control holds for `q`.
    refine (probabilityGeneratingFunctionReal_hasFPowerSeriesOnBall_one q).analyticOnNhd.mono ?_
    intro x hx
    rw [Metric.mem_eball, edist_zero_right, enorm_eq_nnnorm, ENNReal.coe_lt_one_iff,
      ← NNReal.coe_lt_one, coe_nnnorm]
    simpa [Real.norm_eq_abs, abs_lt] using hx
  have hfreq :
      ∃ᶠ z in 𝓝[≠] r,
        probabilityGeneratingFunctionReal p z = probabilityGeneratingFunctionReal q z := by
    -- The prescribed sampling values give an infinite equality set accumulating at `r`.
    exact (samplingPoints_tendsto_puncturedNhds hr₀).frequently <|
      (Filter.Eventually.of_forall h_values).frequently
  have hEqOn :
      EqOn (probabilityGeneratingFunctionReal p) (probabilityGeneratingFunctionReal q) U := by
    refine hpAnalytic.eqOn_of_preconnected_of_frequently_eq hqAnalytic isPreconnected_Ioo ?_ hfreq
    exact ⟨by linarith, hr₁⟩
  have hEqZero :
      probabilityGeneratingFunctionReal p =ᶠ[𝓝 (0 : ℝ)] probabilityGeneratingFunctionReal q := by
    -- Route the global uniqueness through the common neighborhood of `0`.
    refine hEqOn.eventuallyEq_of_mem ?_
    exact IsOpen.mem_nhds isOpen_Ioo ⟨by norm_num, by norm_num⟩
  have hpq : p = q := pmf_eq_of_probabilityGeneratingFunctionReal_eventuallyEq hEqZero
  simpa [hpq]

-- Proof sketch: under convergence at a point `z > 1`, both pgfs extend analytically to `(-z, z)`;
-- the same sampling sequence inside `[0,r]` with `r < z` has accumulation point `r`, so analytic
-- continuation forces equality of the extended pgfs.
/-- Theorem 3.2 (6): Item (iii). If the pgf series converges at some `z > 1`, then for every
`r ∈ (0,z)` the pgf is already determined by the values at the countable family
`r * (n + 1) / (n + 2)`. -/
-- TODO: repeat the sampling-point identity-theorem argument on the larger analytic ball supplied
-- by `probabilityGeneratingFunctionReal_hasFPowerSeriesOnBall_of_summable`.
theorem probabilityGeneratingFunctionReal_eq_of_agree_on_samplingPoints_of_summable
    {p q : PMF ℕ} {z r : ℝ} (hz₁ : 1 < z)
    (hpz : Summable (fun n : ℕ ↦ (p n).toReal * z ^ n))
    (hqz : Summable (fun n : ℕ ↦ (q n).toReal * z ^ n))
    (hr₀ : 0 < r) (hrz : r < z)
    (h_values :
      ∀ n : ℕ,
        probabilityGeneratingFunctionReal p (r * (((n : ℝ) + 1) / ((n : ℝ) + 2))) =
          probabilityGeneratingFunctionReal q (r * (((n : ℝ) + 1) / ((n : ℝ) + 2)))) :
    probabilityGeneratingFunctionReal p = probabilityGeneratingFunctionReal q := by
  let U : Set ℝ := Set.Ioo (-z) z
  have hz0 : 0 ≤ z := le_of_lt (lt_trans zero_lt_one hz₁)
  have hpAnalytic : AnalyticOnNhd ℝ (probabilityGeneratingFunctionReal p) U := by
    -- Convergence at `z > 1` enlarges the analytic interval to `(-z, z)`.
    exact AnalyticOnNhd.mono
      ((probabilityGeneratingFunctionReal_hasFPowerSeriesOnBall_of_summable p hz₁ hpz).analyticOnNhd)
      (fun x hx => by
        simpa [Metric.mem_eball, edist_dist, Real.dist_eq, Real.toNNReal_of_nonneg hz0, abs_lt]
          using hx)
  have hqAnalytic : AnalyticOnNhd ℝ (probabilityGeneratingFunctionReal q) U := by
    -- The same enlarged radius is available for `q`.
    exact AnalyticOnNhd.mono
      ((probabilityGeneratingFunctionReal_hasFPowerSeriesOnBall_of_summable q hz₁ hqz).analyticOnNhd)
      (fun x hx => by
        simpa [Metric.mem_eball, edist_dist, Real.dist_eq, Real.toNNReal_of_nonneg hz0, abs_lt]
          using hx)
  have hfreq :
      ∃ᶠ z' in 𝓝[≠] r,
        probabilityGeneratingFunctionReal p z' = probabilityGeneratingFunctionReal q z' := by
    -- The same countable sampling family still accumulates at `r`.
    exact (samplingPoints_tendsto_puncturedNhds hr₀).frequently <|
      (Filter.Eventually.of_forall h_values).frequently
  have hEqOn :
      EqOn (probabilityGeneratingFunctionReal p) (probabilityGeneratingFunctionReal q) U := by
    refine hpAnalytic.eqOn_of_preconnected_of_frequently_eq hqAnalytic isPreconnected_Ioo ?_ hfreq
    exact ⟨by linarith [hz₁], hrz⟩
  have hEqZero :
      probabilityGeneratingFunctionReal p =ᶠ[𝓝 (0 : ℝ)] probabilityGeneratingFunctionReal q := by
    -- Once the pgfs agree on `(-z, z)`, they agree on a neighborhood of `0`.
    refine hEqOn.eventuallyEq_of_mem ?_
    exact IsOpen.mem_nhds isOpen_Ioo ⟨by linarith [hz₁], by linarith [hz₁]⟩
  have hpq : p = q := pmf_eq_of_probabilityGeneratingFunctionReal_eventuallyEq hEqZero
  simpa [hpq]

-- Proof sketch: convergence at some `z > 1` enlarges the radius of convergence beyond `1`, so the
-- differentiated series still converges at `1`; then Abel's theorem identifies the left limit with
-- the actual derivative value at `1`.
/-- Theorem 3.2 (7): Item (iii). If the pgf series converges at some `z > 1`, then every iterated
derivative has a finite left limit at `1`, equal to its value at `1`. -/
-- TODO: upgrade the radius with `probabilityGeneratingFunctionReal_hasFPowerSeriesOnBall_of_summable`,
-- then transport continuity of the iterated derivatives from a neighborhood of `1` to the left-hand
-- filter `𝓝[<] 1`.
theorem probabilityGeneratingFunctionReal_iteratedDeriv_tendsto_left_one_of_summable
    (p : PMF ℕ) {z : ℝ} (hz₁ : 1 < z)
    (hpz : Summable (fun n : ℕ ↦ (p n).toReal * z ^ n)) (n : ℕ) :
    Filter.Tendsto (fun x : ℝ ↦ iteratedDeriv n (probabilityGeneratingFunctionReal p) x)
      (nhdsWithin (1 : ℝ) (Set.Iio 1))
      (𝓝 (iteratedDeriv n (probabilityGeneratingFunctionReal p) 1)) := by
  have hz0 : 0 ≤ z := le_of_lt (lt_trans zero_lt_one hz₁)
  let hball := probabilityGeneratingFunctionReal_hasFPowerSeriesOnBall_of_summable p hz₁ hpz
  have hanalytic : AnalyticAt ℝ (probabilityGeneratingFunctionReal p) 1 := by
    -- Since `1 < z`, the point `1` lies inside the larger convergence ball.
    refine hball.analyticAt_of_mem ?_
    simpa [Metric.mem_eball, edist_dist, Real.dist_eq, Real.toNNReal_of_nonneg hz0,
      abs_of_nonneg zero_le_one] using hz₁
  -- Analyticity at `1` gives continuity of every iterated derivative there.
  simpa [iteratedDeriv_eq_iterate] using
    (hanalytic.iterated_deriv n).continuousAt.continuousWithinAt.tendsto

-- Proof sketch: convergence beyond `1` makes the pgf analytic on a neighborhood of `1`, so its
-- Taylor coefficients at `1` determine the analytic function uniquely on that neighborhood and
-- hence on the original interval.
/-- Theorem 3.2 (8): Item (iii). Under convergence at some `z > 1`, the pgf is uniquely determined
by the values of all derivatives at `1`. -/
-- TODO: use the enlarged analytic neighborhood of `1`, compare the Taylor series there via the
-- derivative data, and conclude by analytic uniqueness.
theorem probabilityGeneratingFunctionReal_eq_of_iteratedDeriv_eq_of_summable
    {p q : PMF ℕ} {z : ℝ} (hz₁ : 1 < z)
    (hpz : Summable (fun n : ℕ ↦ (p n).toReal * z ^ n))
    (hqz : Summable (fun n : ℕ ↦ (q n).toReal * z ^ n))
    (h_deriv :
      ∀ n : ℕ,
        iteratedDeriv n (probabilityGeneratingFunctionReal p) 1 =
          iteratedDeriv n (probabilityGeneratingFunctionReal q) 1) :
    probabilityGeneratingFunctionReal p = probabilityGeneratingFunctionReal q := by
  let U : Set ℝ := Set.Ioo (-z) z
  have hz0 : 0 ≤ z := le_of_lt (lt_trans zero_lt_one hz₁)
  have hmem1 : (1 : ℝ) ∈ Metric.eball (0 : ℝ) (Real.toNNReal z) := by
    simpa [Metric.mem_eball, edist_dist, Real.dist_eq, Real.toNNReal_of_nonneg hz0,
      abs_of_nonneg zero_le_one] using hz₁
  let hpBall := probabilityGeneratingFunctionReal_hasFPowerSeriesOnBall_of_summable p hz₁ hpz
  let hqBall := probabilityGeneratingFunctionReal_hasFPowerSeriesOnBall_of_summable q hz₁ hqz
  have hpAnalyticAt : AnalyticAt ℝ (probabilityGeneratingFunctionReal p) 1 := by
    -- The larger convergence radius makes the pgf analytic at `1`.
    exact hpBall.analyticAt_of_mem hmem1
  have hqAnalyticAt : AnalyticAt ℝ (probabilityGeneratingFunctionReal q) 1 := by
    -- The same holds for `q`.
    exact hqBall.analyticAt_of_mem hmem1
  have hpSeries :
      HasFPowerSeriesAt (probabilityGeneratingFunctionReal p)
        (FormalMultilinearSeries.ofScalars ℝ
          (fun n ↦ iteratedDeriv n (probabilityGeneratingFunctionReal p) 1 / n.factorial)) 1 :=
    hpAnalyticAt.hasFPowerSeriesAt
  have hqSeries :
      HasFPowerSeriesAt (probabilityGeneratingFunctionReal q)
        (FormalMultilinearSeries.ofScalars ℝ
          (fun n ↦ iteratedDeriv n (probabilityGeneratingFunctionReal p) 1 / n.factorial)) 1 := by
    -- Equal derivative data at `1` gives the same Taylor coefficients.
    simpa [h_deriv] using hqAnalyticAt.hasFPowerSeriesAt
  have hEqNearOne :
      probabilityGeneratingFunctionReal p =ᶠ[𝓝 (1 : ℝ)] probabilityGeneratingFunctionReal q := by
    -- Equal local Taylor series imply local equality of the represented functions.
    filter_upwards [hpSeries.eventually_hasSum_sub, hqSeries.eventually_hasSum_sub] with y hy₁ hy₂
    exact hy₁.unique hy₂
  have hpAnalytic : AnalyticOnNhd ℝ (probabilityGeneratingFunctionReal p) U := by
    -- Promote the summability hypothesis back to analyticity on the whole interval `(-z, z)`.
    exact AnalyticOnNhd.mono (hpBall.analyticOnNhd) (fun x hx => by
      simpa [Metric.mem_eball, edist_dist, Real.dist_eq, Real.toNNReal_of_nonneg hz0, abs_lt]
        using hx)
  have hqAnalytic : AnalyticOnNhd ℝ (probabilityGeneratingFunctionReal q) U := by
    -- The same analytic interval is available for `q`.
    exact AnalyticOnNhd.mono (hqBall.analyticOnNhd) (fun x hx => by
      simpa [Metric.mem_eball, edist_dist, Real.dist_eq, Real.toNNReal_of_nonneg hz0, abs_lt]
        using hx)
  have hEqOn :
      EqOn (probabilityGeneratingFunctionReal p) (probabilityGeneratingFunctionReal q) U := by
    -- Route the local equality near `1` through the analytic identity theorem.
    refine hpAnalytic.eqOn_of_preconnected_of_frequently_eq (z₀ := (1 : ℝ)) hqAnalytic
      isPreconnected_Ioo ?_ ?_
    · exact ⟨by linarith [hz₁], hz₁⟩
    · exact (hEqNearOne.filter_mono nhdsWithin_le_nhds).frequently
  have hEqZero :
      probabilityGeneratingFunctionReal p =ᶠ[𝓝 (0 : ℝ)] probabilityGeneratingFunctionReal q := by
    -- Global agreement on `(-z, z)` gives the neighborhood equality needed at the origin.
    refine hEqOn.eventuallyEq_of_mem ?_
    exact IsOpen.mem_nhds isOpen_Ioo ⟨by linarith [hz₁], by linarith [hz₁]⟩
  have hpq : p = q := pmf_eq_of_probabilityGeneratingFunctionReal_eventuallyEq hEqZero
  simpa [hpq]
