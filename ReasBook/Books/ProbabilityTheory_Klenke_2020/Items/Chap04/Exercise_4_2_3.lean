/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory Set
open scoped BigOperators Interval

universe u

variable {E : Type u} [NormedAddCommGroup E]

/-- Helper for Exercise 4.2.3: every sampled norm `t ↦ ‖f ((n + 1) * t)‖` is integrable on a
bounded-ratio interval `Icc a (2 * a)` once `f` is integrable on `Ici 0`. -/
lemma sampledNormIntegrableOnIccDouble (f : ℝ → E) (hf : IntegrableOn f (Ici 0))
    {a : ℝ} (ha : 0 < a) (n : ℕ) :
    IntegrableOn (fun t ↦ ‖f ((n + 1 : ℝ) * t)‖) (Icc a (2 * a)) := by
  have hn : 0 < (n + 1 : ℝ) := by
    positivity
  -- First move the integrability statement to the open half-line, where scaling preserves it.
  have hnorm : IntegrableOn (fun x ↦ ‖f x‖) (Ici 0) := hf.norm
  have hIoiSubset : Ioi (((n + 1 : ℝ) * 0)) ⊆ Ici 0 := by
    intro x hx
    simp only [Set.mem_Ioi, Set.mem_Ici, mul_zero] at hx ⊢
    exact le_of_lt hx
  have hIoi : IntegrableOn (fun t ↦ ‖f ((n + 1 : ℝ) * t)‖) (Ioi 0) := by
    rw [MeasureTheory.integrableOn_Ioi_comp_mul_left_iff (fun x ↦ ‖f x‖) (c := 0) hn]
    exact hnorm.mono_set hIoiSubset
  -- Then restrict from `Ioi 0` to the compact interval `Icc a (2 * a)`.
  have hIccSubset : Icc a (2 * a) ⊆ Ioi (0 : ℝ) := by
    intro t ht
    exact lt_of_lt_of_le ha ht.1
  exact hIoi.mono_set hIccSubset

/-- Helper for Exercise 4.2.3: the interval change of variables `x = (n + 1) * t` rewrites the
`n`-th sampled norm integral on `Icc a (2 * a)`. -/
lemma sampledNormIntervalIntegral_eq_invMul (f : ℝ → E) {a : ℝ} (n : ℕ) :
    ∫ t in a..(2 * a), ‖f ((n + 1 : ℝ) * t)‖ =
      ((n + 1 : ℝ)⁻¹) * ∫ x in (a * (n + 1 : ℝ))..((2 * a) * (n + 1 : ℝ)), ‖f x‖ := by
  have hn : (n + 1 : ℝ) ≠ 0 := by
    positivity
  -- This is exactly the standard interval-integral scaling formula.
  simpa [smul_eq_mul, mul_comm, mul_left_comm, mul_assoc] using
    (intervalIntegral.integral_comp_mul_left (f := fun x ↦ ‖f x‖) (a := a) (b := 2 * a)
      (c := (n + 1 : ℝ)) hn)

/-- Helper for Exercise 4.2.3: the reciprocal sum on a dyadic arithmetic block is uniformly
bounded. -/
lemma harmonicBlockSum_le_two (m : ℕ) (hm : 0 < m) :
    Finset.sum (Finset.Icc m (2 * m)) (fun k ↦ (k : ℝ)⁻¹) ≤ 2 := by
  have hm_real : 0 < (m : ℝ) := by
    exact_mod_cast hm
  have hcard : (Finset.Icc m (2 * m)).card = m + 1 := by
    calc
      (Finset.Icc m (2 * m)).card = 2 * m + 1 - m := Nat.card_Icc m (2 * m)
      _ = m + 1 := by omega
  have hm_nat : m + 1 ≤ 2 * m := by
    omega
  have hm_le_two_mul : (m + 1 : ℝ) ≤ 2 * m := by
    exact_mod_cast hm_nat
  calc
    Finset.sum (Finset.Icc m (2 * m)) (fun k ↦ (k : ℝ)⁻¹)
        ≤ Finset.sum (Finset.Icc m (2 * m)) (fun _k ↦ (m : ℝ)⁻¹) := by
          refine Finset.sum_le_sum ?_
          intro k hk
          have hk_real : (m : ℝ) ≤ k := by
            exact_mod_cast (Finset.mem_Icc.mp hk).1
          simpa [one_div] using one_div_le_one_div_of_le hm_real hk_real
    _ = ((m + 1 : ℝ) * (m : ℝ)⁻¹) := by
          simp [hcard]
    _ ≤ (2 * (m : ℝ)) * (m : ℝ)⁻¹ := by
          exact mul_le_mul_of_nonneg_right hm_le_two_mul (by positivity)
    _ = 2 := by
          field_simp [hm.ne']

/-- Helper for Exercise 4.2.3: the reciprocal sum on a dyadic arithmetic block is uniformly
bounded in `ℝ≥0`. -/
lemma harmonicBlockSumNNReal_le_two (m : ℕ) (hm : 0 < m) :
    Finset.sum (Finset.Icc m (2 * m)) (fun k ↦ (k : NNReal)⁻¹) ≤ 2 := by
  rw [← NNReal.coe_le_coe]
  simpa using harmonicBlockSum_le_two m hm

/-- Helper for Exercise 4.2.3: at a fixed positive point `x`, the reciprocal weights of the
sampling intervals `Ioc (a * k) ((2 * a) * k)` that contain `x` have total mass at most `2`. -/
lemma sampledWeightSum_range_le_two {a x : ℝ} (ha : 0 < a) (hx : 0 < x) (N : ℕ) :
    ∑ k ∈ Finset.range N,
        Set.indicator (Ioc (a * (k : ℝ)) ((2 * a) * (k : ℝ))) (fun _ ↦ ((k : NNReal)⁻¹)) x ≤ 2 := by
  classical
  have hsum_filter :
      ∑ k ∈ Finset.range N,
          Set.indicator (Ioc (a * (k : ℝ)) ((2 * a) * (k : ℝ))) (fun _ ↦ ((k : NNReal)⁻¹)) x =
        Finset.sum (((Finset.range N).filter
          (fun k : ℕ ↦ x ∈ Ioc (a * (k : ℝ)) ((2 * a) * (k : ℝ)))) ) fun k ↦
            ((k : NNReal)⁻¹) := by
    -- Keep the filtered finset nat-indexed so the arithmetic block stays in `ℕ`.
    rw [Finset.sum_indicator_eq_sum_filter]
  let m : ℕ := Nat.ceil (x / (2 * a))
  have hm_pos : 0 < m := by
    exact Nat.ceil_pos.2 (by positivity : 0 < x / (2 * a))
  have hsubset :
      ((Finset.range N).filter (fun k : ℕ ↦ x ∈ Ioc (a * (k : ℝ)) ((2 * a) * (k : ℝ)))) ⊆
        Finset.Icc m (2 * m) := by
    intro k hk
    rcases Finset.mem_filter.mp hk with ⟨_, hkx⟩
    have hm_le_k : m ≤ k := by
      refine Nat.ceil_le.2 ?_
      rw [div_le_iff₀ (by positivity : 0 < 2 * a)]
      simpa [mul_comm, mul_left_comm, mul_assoc] using hkx.2
    have hk_le_two_m : k ≤ 2 * m := by
      have hxm : x ≤ (2 * a) * m := by
        calc
          x = (x / (2 * a)) * (2 * a) := by field_simp [ha.ne']
          _ ≤ m * (2 * a) := by
            gcongr
            exact Nat.le_ceil (x / (2 * a))
          _ = (2 * a) * m := by ring
      have hk_lt : (k : ℝ) < 2 * m := by
        nlinarith [hkx.1, hxm]
      exact le_of_lt (Nat.cast_lt.mp (by simpa using hk_lt : (k : ℝ) < ((2 * m : ℕ) : ℝ)))
    exact Finset.mem_Icc.mpr ⟨hm_le_k, hk_le_two_m⟩
  calc
    ∑ k ∈ Finset.range N,
        Set.indicator (Ioc (a * (k : ℝ)) ((2 * a) * (k : ℝ))) (fun _ ↦ ((k : NNReal)⁻¹)) x
      = Finset.sum (((Finset.range N).filter
          (fun k : ℕ ↦ x ∈ Ioc (a * (k : ℝ)) ((2 * a) * (k : ℝ)))) ) fun k ↦
            ((k : NNReal)⁻¹) :=
          hsum_filter
    _ ≤ Finset.sum (Finset.Icc m (2 * m)) (fun k ↦ ((k : NNReal)⁻¹)) := by
          exact Finset.sum_le_sum_of_subset_of_nonneg hsubset (by
            intro k hk hk'
            positivity)
    _ ≤ 2 := harmonicBlockSumNNReal_le_two m hm_pos

/-- Helper for Exercise 4.2.3: the `k`-th block weight on the `x`-side change-of-variables
formula. -/
noncomputable def sampledBlockWeight (f : ℝ → E) (a : ℝ) (k : ℕ) (x : ℝ) : NNReal :=
  Set.indicator (Ioc (a * (k : ℝ)) ((2 * a) * (k : ℝ)))
    (fun y ↦ ((k : NNReal)⁻¹) * ‖f y‖₊) x

/-- Helper for Exercise 4.2.3: the block-weight function viewed as an `ℝ≥0∞`-valued integrand. -/
noncomputable def sampledBlockWeightENN (f : ℝ → E) (a : ℝ) (k : ℕ) : ℝ → ENNReal :=
  fun x ↦ (sampledBlockWeight f a k x : ENNReal)

/-- Helper for Exercise 4.2.3: the sampled norm series viewed as a single `ℝ≥0∞`-valued
integrand. -/
noncomputable def sampledNormSeries (f : ℝ → E) : ℝ → ENNReal :=
  fun t ↦ ∑' n : ℕ, ‖f ((n + 1 : ℝ) * t)‖ₑ

/-- Helper for Exercise 4.2.3: `sampledBlockWeight` factors into the interval indicator times the
pointwise norm. -/
lemma sampledBlockWeight_eq_indicator_mul_nnnorm (f : ℝ → E) {a x : ℝ} (k : ℕ) :
    sampledBlockWeight f a k x =
      Set.indicator (Ioc (a * (k : ℝ)) ((2 * a) * (k : ℝ))) (fun _ ↦ ((k : NNReal)⁻¹)) x *
        ‖f x‖₊ := by
  by_cases hkx : x ∈ Ioc (a * (k : ℝ)) ((2 * a) * (k : ℝ))
  · -- On the interval, both indicators evaluate to the same reciprocal weight.
    rw [sampledBlockWeight, Set.indicator_of_mem hkx, Set.indicator_of_mem hkx]
  · -- Outside the interval, both indicators vanish.
    rw [sampledBlockWeight, Set.indicator_of_notMem hkx, Set.indicator_of_notMem hkx]
    simp

/-- Helper for Exercise 4.2.3: each change-of-variables block weight is integrable on `ℝ` when
`f` is integrable on `Ici 0`. -/
lemma sampledBlockWeight_integrable (f : ℝ → E) (hf : IntegrableOn f (Ici 0)) {a : ℝ}
    (ha : 0 < a) (k : ℕ) : Integrable (fun x ↦ (sampledBlockWeight f a k x : ℝ)) := by
  have hnormIci : IntegrableOn (fun x ↦ ‖f x‖) (Ici 0) := by
    simpa using hf.norm
  have hsubset : Ioc (a * (k : ℝ)) ((2 * a) * (k : ℝ)) ⊆ Ici (0 : ℝ) := by
    intro x hx
    exact le_of_lt (lt_of_le_of_lt (by positivity) hx.1)
  have hnorm :
      IntegrableOn (fun x ↦ ‖f x‖) (Ioc (a * (k : ℝ)) ((2 * a) * (k : ℝ))) :=
    hnormIci.mono_set hsubset
  have hscaled :
      IntegrableOn (fun x ↦ (k : ℝ)⁻¹ * ‖f x‖)
        (Ioc (a * (k : ℝ)) ((2 * a) * (k : ℝ))) := by
    simpa [one_div] using hnorm.const_mul ((k : ℝ)⁻¹)
  simpa [sampledBlockWeight, one_div] using hscaled.integrable_indicator measurableSet_Ioc

/-- Helper for Exercise 4.2.3: the partial sums of the `x`-side block-weight series are bounded by
`2 * ‖f x‖₊`. -/
lemma sampledBlockWeight_sum_bound (f : ℝ → E) {a x : ℝ} (ha : 0 < a) (N : ℕ) :
    ∑ k ∈ Finset.range N, sampledBlockWeight f a k x ≤ (Ioi 0).indicator
      (fun y ↦ (2 : NNReal) * ‖f y‖₊) x := by
  by_cases hx : 0 < x
  · calc
      ∑ k ∈ Finset.range N, sampledBlockWeight f a k x
          = ∑ k ∈ Finset.range N,
              Set.indicator (Ioc (a * (k : ℝ)) ((2 * a) * (k : ℝ)))
                (fun _ ↦ ((k : NNReal)⁻¹)) x * ‖f x‖₊ := by
                  refine Finset.sum_congr rfl ?_
                  intro k hk
                  rw [sampledBlockWeight_eq_indicator_mul_nnnorm]
      _ = (∑ k ∈ Finset.range N,
              Set.indicator (Ioc (a * (k : ℝ)) ((2 * a) * (k : ℝ)))
                (fun _ ↦ ((k : NNReal)⁻¹)) x) * ‖f x‖₊ := by
              rw [Finset.sum_mul]
      _ ≤ 2 * ‖f x‖₊ := by
            gcongr
            exact sampledWeightSum_range_le_two ha hx N
      _ = (Ioi 0).indicator (fun y ↦ (2 : NNReal) * ‖f y‖₊) x := by
            simp [hx]
  · have hx' : x ≤ 0 := le_of_not_gt hx
    have hzero :
        ∑ k ∈ Finset.range N, sampledBlockWeight f a k x = 0 := by
      refine Finset.sum_eq_zero ?_
      intro k hk
      have hkx : x ∉ Ioc (a * (k : ℝ)) ((2 * a) * (k : ℝ)) := by
        intro hxk
        have hk_nonneg : 0 ≤ a * (k : ℝ) := by positivity
        exact (not_lt_of_ge (hx'.trans hk_nonneg)) hxk.1
      simp [sampledBlockWeight, Set.indicator_of_notMem, hkx]
    simp [hzero, hx]

/-- Helper for Exercise 4.2.3: the zero-th block weight vanishes because `Ioc 0 0` is empty. -/
lemma sampledBlockWeight_zero (f : ℝ → E) (a x : ℝ) :
    sampledBlockWeight f a 0 x = 0 := by
  simp [sampledBlockWeight]

/-- Helper for Exercise 4.2.3: the sampled norm lintegral on `Ioc a (2 * a)` matches the
corresponding `x`-side block weight. -/
lemma sampledBlockWeightLintegral_eq (f : ℝ → E) (hf : IntegrableOn f (Ici 0))
    {a : ℝ} (ha : 0 < a) (n : ℕ) :
    MeasureTheory.lintegral (volume.restrict (Ioc a (2 * a)))
        (fun t ↦ ENNReal.ofReal ‖f ((n + 1 : ℝ) * t)‖) =
      MeasureTheory.lintegral volume (sampledBlockWeightENN f a (n + 1)) := by
  have hIntLeft :
      Integrable (fun t ↦ ‖f ((n + 1 : ℝ) * t)‖) (volume.restrict (Ioc a (2 * a))) := by
    exact (sampledNormIntegrableOnIccDouble f hf ha n).mono_set Ioc_subset_Icc_self
  have hLeftNonneg :
      0 ≤ᵐ[volume.restrict (Ioc a (2 * a))] fun t ↦ ‖f ((n + 1 : ℝ) * t)‖ :=
    Filter.Eventually.of_forall fun t ↦ norm_nonneg _
  have hLeft :
      MeasureTheory.lintegral (volume.restrict (Ioc a (2 * a)))
          (fun t ↦ ENNReal.ofReal ‖f ((n + 1 : ℝ) * t)‖) =
        ENNReal.ofReal (∫ t, ‖f ((n + 1 : ℝ) * t)‖ ∂(volume.restrict (Ioc a (2 * a)))) := by
    -- Convert the `t`-side lintegral back to the corresponding integral on the restricted measure.
    symm
    exact MeasureTheory.ofReal_integral_eq_lintegral_ofReal hIntLeft hLeftNonneg
  have hIntRight :
      Integrable (fun x ↦ (sampledBlockWeight f a (n + 1) x : ℝ)) :=
    sampledBlockWeight_integrable f hf (a := a) ha (n + 1)
  have hRight :
      MeasureTheory.lintegral volume (sampledBlockWeightENN f a (n + 1)) =
        ENNReal.ofReal (∫ x, (sampledBlockWeight f a (n + 1) x : ℝ)) := by
    simpa [sampledBlockWeightENN] using
      (MeasureTheory.lintegral_coe_eq_integral (sampledBlockWeight f a (n + 1)) hIntRight)
  have hInterval :
      ∫ t, ‖f ((n + 1 : ℝ) * t)‖ ∂(volume.restrict (Ioc a (2 * a))) =
        ∫ t in a..(2 * a), ‖f ((n + 1 : ℝ) * t)‖ := by
    -- Rewrite the restricted-measure integral as the interval integral on the same block.
    symm
    exact intervalIntegral.integral_of_le (show a ≤ 2 * a by nlinarith [ha])
  have hWeight :
      ∫ x, (sampledBlockWeight f a (n + 1) x : ℝ) =
        ((n + 1 : ℝ)⁻¹) *
          ∫ x in Ioc (a * (n + 1 : ℝ)) ((2 * a) * (n + 1 : ℝ)), ‖f x‖ := by
    -- Rewrite the indicator-valued definition as a set integral, then pull out the constant.
    calc
      ∫ x, (sampledBlockWeight f a (n + 1) x : ℝ)
          = ∫ x, Set.indicator (Ioc (a * (n + 1 : ℝ)) ((2 * a) * (n + 1 : ℝ)))
              (fun x ↦ ((n + 1 : ℝ)⁻¹) * ‖f x‖) x := by
                simp [sampledBlockWeight]
      _ = ∫ x in Ioc (a * (n + 1 : ℝ)) ((2 * a) * (n + 1 : ℝ)),
              ((n + 1 : ℝ)⁻¹) * ‖f x‖ := by
                rw [MeasureTheory.integral_indicator measurableSet_Ioc]
      _ = ((n + 1 : ℝ)⁻¹) *
            ∫ x in Ioc (a * (n + 1 : ℝ)) ((2 * a) * (n + 1 : ℝ)), ‖f x‖ := by
              rw [integral_const_mul]
  have hIocToInterval :
      ∫ x in Ioc (a * (n + 1 : ℝ)) ((2 * a) * (n + 1 : ℝ)), ‖f x‖ =
        ∫ x in (a * (n + 1 : ℝ))..((2 * a) * (n + 1 : ℝ)), ‖f x‖ := by
    have hmul_le : a * (n + 1 : ℝ) ≤ (2 * a) * (n + 1 : ℝ) := by
      nlinarith [ha]
    rw [← intervalIntegral.integral_of_le hmul_le]
  calc
    MeasureTheory.lintegral (volume.restrict (Ioc a (2 * a)))
        (fun t ↦ ENNReal.ofReal ‖f ((n + 1 : ℝ) * t)‖)
        = ENNReal.ofReal (∫ t, ‖f ((n + 1 : ℝ) * t)‖ ∂(volume.restrict (Ioc a (2 * a)))) := hLeft
    _ = ENNReal.ofReal (∫ t in a..(2 * a), ‖f ((n + 1 : ℝ) * t)‖) := by
          rw [hInterval]
    _ = ENNReal.ofReal
          (((n + 1 : ℝ)⁻¹) *
            ∫ x in (a * (n + 1 : ℝ))..((2 * a) * (n + 1 : ℝ)), ‖f x‖) := by
          rw [sampledNormIntervalIntegral_eq_invMul]
    _ = ENNReal.ofReal (∫ x, (sampledBlockWeight f a (n + 1) x : ℝ)) := by
          rw [hWeight, hIocToInterval]
    _ = MeasureTheory.lintegral volume (sampledBlockWeightENN f a (n + 1)) :=
          hRight.symm

/-- Helper for Exercise 4.2.3: shifting the block index from `k` to `n + 1` preserves the partial
sum bound because the `k = 0` term vanishes. -/
lemma sampledBlockWeight_shift_sum_bound (f : ℝ → E) {a x : ℝ} (ha : 0 < a) (N : ℕ) :
    ∑ n ∈ Finset.range N, sampledBlockWeight f a (n + 1) x ≤ (Ioi 0).indicator
      (fun y ↦ (2 : NNReal) * ‖f y‖₊) x := by
  -- Rewrite the unshifted partial sum at range `N + 1`, then drop the zero-th term.
  simpa [Finset.sum_range_succ', sampledBlockWeight_zero, add_comm, add_left_comm, add_assoc] using
    sampledBlockWeight_sum_bound f (a := a) (x := x) ha (N + 1)

/-- Helper for Exercise 4.2.3: the local lintegral of the sampled norm series on `Ioc a (2 * a)`
is finite. -/
lemma sampledNormTsumLintegral_neTopOnIocDouble (f : ℝ → E) (hf : IntegrableOn f (Ici 0))
    {a : ℝ} (ha : 0 < a) :
    (MeasureTheory.lintegral (volume.restrict (Ioc a (2 * a))) (sampledNormSeries f)) ≠ ⊤ := by
  let μ : Measure ℝ := volume.restrict (Ioc a (2 * a))
  let G : ℕ → ℝ → NNReal := fun n x ↦ sampledBlockWeight f a (n + 1) x
  let B : ℝ → NNReal := (Ioi 0).indicator (fun y ↦ (2 : NNReal) * ‖f y‖₊)
  have hSampleInt :
      ∀ n : ℕ, Integrable (fun t ↦ ‖f ((n + 1 : ℝ) * t)‖) μ := by
    intro n
    exact (sampledNormIntegrableOnIccDouble f hf ha n).mono_set Ioc_subset_Icc_self
  have hSampleMeas :
      ∀ n : ℕ, AEMeasurable (fun t ↦ ENNReal.ofReal ‖f ((n + 1 : ℝ) * t)‖) μ := by
    intro n
    -- Use local integrability to obtain the measurability needed for `lintegral_tsum`.
    simpa [μ, enorm_eq_nnnorm] using (hSampleInt n).aestronglyMeasurable.enorm
  have hGInt : ∀ n : ℕ, Integrable (fun x ↦ (G n x : ℝ)) := by
    intro n
    simpa [G] using sampledBlockWeight_integrable f hf (a := a) ha (n + 1)
  have hGMeas : ∀ n : ℕ, AEMeasurable (G n) volume := by
    intro n
    simpa [G] using (hGInt n).aemeasurable.nnnorm
  have hGMeasENN :
      ∀ n : ℕ, AEMeasurable (fun x ↦ (G n x : ENNReal)) volume := by
    intro n
    exact (hGMeas n).coe_nnreal_ennreal
  have hBInt : Integrable (fun x ↦ (B x : ℝ)) := by
    -- The envelope inherits integrability from `hf.norm` after restricting to `Ioi 0`.
    have hnormIci : IntegrableOn (fun x ↦ ‖f x‖) (Ici 0) := by
      simpa using hf.norm
    have hnorm_Ioi : IntegrableOn (fun x ↦ ‖f x‖) (Ioi (0 : ℝ)) :=
      hnormIci.mono_set Ioi_subset_Ici_self
    have hscaled :
        IntegrableOn (fun x ↦ (2 : ℝ) * ‖f x‖) (Ioi (0 : ℝ)) := by
      simpa using hnorm_Ioi.const_mul (2 : ℝ)
    simpa [B] using hscaled.integrable_indicator measurableSet_Ioi
  have hBLintegral_ne_top : (∫⁻ x, (B x : ENNReal) ∂volume) ≠ ⊤ := by
    rw [MeasureTheory.lintegral_coe_eq_integral B hBInt]
    exact ENNReal.ofReal_ne_top
  have hPartial :
      ∀ N : ℕ,
        ∑ n ∈ Finset.range N,
            MeasureTheory.lintegral (volume.restrict (Ioc a (2 * a)))
              (fun t ↦ ENNReal.ofReal ‖f ((n + 1 : ℝ) * t)‖) ≤
          MeasureTheory.lintegral volume (fun x ↦ (B x : ENNReal)) := by
    intro N
    calc
      ∑ n ∈ Finset.range N,
          MeasureTheory.lintegral (volume.restrict (Ioc a (2 * a)))
            (fun t ↦ ENNReal.ofReal ‖f ((n + 1 : ℝ) * t)‖)
          = ∑ n ∈ Finset.range N,
              MeasureTheory.lintegral volume (fun x ↦ (G n x : ENNReal)) := by
              refine Finset.sum_congr rfl ?_
              intro n hn
              simpa [G] using sampledBlockWeightLintegral_eq f hf ha n
      _ = MeasureTheory.lintegral volume
            (fun x ↦ ∑ n ∈ Finset.range N, (G n x : ENNReal)) := by
            symm
            exact MeasureTheory.lintegral_finset_sum' (Finset.range N) fun n hn ↦ hGMeasENN n
      _ ≤ MeasureTheory.lintegral volume (fun x ↦ (B x : ENNReal)) := by
            refine MeasureTheory.lintegral_mono ?_
            intro x
            -- First prove the pointwise domination in `NNReal`, then coerce once to `ENNReal`.
            have hboundNNReal : ∑ n ∈ Finset.range N, G n x ≤ B x := by
              simpa [G, B] using sampledBlockWeight_shift_sum_bound f (a := a) (x := x) ha N
            simpa [ENNReal.coe_finset_sum] using
              (show ((∑ n ∈ Finset.range N, G n x : NNReal) : ENNReal) ≤ (B x : ENNReal) from by
                exact_mod_cast hboundNNReal)
  have hSeriesLintegral_ne_top :
      (∑' n : ℕ,
          MeasureTheory.lintegral (volume.restrict (Ioc a (2 * a)))
            (fun t ↦ ENNReal.ofReal ‖f ((n + 1 : ℝ) * t)‖)) ≠ ⊤ := by
    -- The partial sums are uniformly dominated by an integrable envelope,
    -- so the full tsum is finite.
    apply ne_of_lt
    calc
      (∑' n : ℕ,
          MeasureTheory.lintegral (volume.restrict (Ioc a (2 * a)))
            (fun t ↦ ENNReal.ofReal ‖f ((n + 1 : ℝ) * t)‖))
          ≤ MeasureTheory.lintegral volume (fun x ↦ (B x : ENNReal)) := by
            exact ENNReal.tsum_le_of_sum_range_le hPartial
      _ < ⊤ := lt_top_iff_ne_top.2 hBLintegral_ne_top
  have hLintegralTsum :
      MeasureTheory.lintegral μ (sampledNormSeries f) =
        ∑' n : ℕ,
          MeasureTheory.lintegral μ (fun t ↦ ENNReal.ofReal ‖f ((n + 1 : ℝ) * t)‖) := by
    -- Record the `lintegral_tsum` normalization explicitly before using the finiteness bound.
    simpa [sampledNormSeries] using (MeasureTheory.lintegral_tsum hSampleMeas)
  have hFinal : MeasureTheory.lintegral μ (sampledNormSeries f) ≠ ⊤ := by
    rw [hLintegralTsum]
    exact hSeriesLintegral_ne_top
  simpa [μ] using hFinal

/-- Helper for Exercise 4.2.3: on every block `Ioc a (2 * a)`, the sampled series is absolutely
summable for almost every point. -/
lemma aeSummableNormOnIocDouble (f : ℝ → E) (hf : IntegrableOn f (Ici 0))
    {a : ℝ} (ha : 0 < a) :
    ∀ᵐ t ∂(volume.restrict (Ioc a (2 * a))), Summable (fun n : ℕ ↦ ‖f ((n + 1 : ℝ) * t)‖) := by
  let μ : Measure ℝ := volume.restrict (Ioc a (2 * a))
  have hInt :
      ∀ n : ℕ, Integrable (fun t ↦ ‖f ((n + 1 : ℝ) * t)‖) μ := by
    intro n
    exact (sampledNormIntegrableOnIccDouble f hf ha n).mono_set Ioc_subset_Icc_self
  have hMeas :
      ∀ n : ℕ, AEMeasurable (fun t ↦ ENNReal.ofReal ‖f ((n + 1 : ℝ) * t)‖) μ := by
    intro n
    -- The local lintegral argument uses the same sampled integrability as measurability input.
    simpa [μ, enorm_eq_nnnorm] using (hInt n).aestronglyMeasurable.enorm
  have hSeriesLintegral_ne_top :
      (∫⁻ t, ∑' n : ℕ, ENNReal.ofReal ‖f ((n + 1 : ℝ) * t)‖ ∂μ) ≠ ⊤ := by
    simpa [μ, sampledNormSeries, enorm_eq_nnnorm] using
      sampledNormTsumLintegral_neTopOnIocDouble f hf ha
  refine
    (MeasureTheory.ae_lt_top' (AEMeasurable.ennreal_tsum hMeas) hSeriesLintegral_ne_top).mono ?_
  intro t ht
  have ht_ne_top :
      (∑' n : ℕ, (‖f ((n + 1 : ℝ) * t)‖₊ : ENNReal)) ≠ ⊤ := by
    simpa [sampledNormSeries, enorm_eq_nnnorm] using ht.ne
  have hsum :
      Summable (fun n : ℕ ↦ (‖f ((n + 1 : ℝ) * t)‖₊ : ℝ)) :=
    (ENNReal.tsum_coe_ne_top_iff_summable_coe
      (f := fun n : ℕ ↦ ‖f ((n + 1 : ℝ) * t)‖₊)).1 ht_ne_top
  simpa using hsum

theorem ae_summable_norm_at_nat_multiples_of_integrableOn_Ici (f : ℝ → E)
    (hf : IntegrableOn f (Ici 0)) :
    ∀ᵐ t ∂(volume.restrict (Ici 0)), Summable (fun n : ℕ ↦ ‖f ((n + 1 : ℝ) * t)‖) := by
  -- Route correction: the naive global Tonelli argument diverges because the harmonic series
  -- appears after integrating over all of `Ici 0`.
  have hUpper :
      ∀ m : ℕ,
        ∀ᵐ t ∂volume, (2 : ℝ) ^ m < t → t ≤ (2 : ℝ) ^ (m + 1) →
          Summable (fun n : ℕ ↦ ‖f ((n + 1 : ℝ) * t)‖) := by
    intro m
    simpa [pow_succ, mul_comm, mul_left_comm, mul_assoc] using
      (ae_restrict_iff' measurableSet_Ioc).1
        (aeSummableNormOnIocDouble f hf (a := (2 : ℝ) ^ m) (by positivity))
  have hLower :
      ∀ m : ℕ,
        ∀ᵐ t ∂volume, (1 / 2 : ℝ) ^ (m + 1) < t → t ≤ (1 / 2 : ℝ) ^ m →
          Summable (fun n : ℕ ↦ ‖f ((n + 1 : ℝ) * t)‖) := by
    intro m
    simpa [pow_succ, mul_comm, mul_left_comm, mul_assoc] using
      (ae_restrict_iff' measurableSet_Ioc).1
        (aeSummableNormOnIocDouble f hf (a := (1 / 2 : ℝ) ^ (m + 1)) (by positivity))
  have hAllUpper :
      ∀ᵐ t ∂volume, ∀ m : ℕ,
        (2 : ℝ) ^ m < t → t ≤ (2 : ℝ) ^ (m + 1) →
          Summable (fun n : ℕ ↦ ‖f ((n + 1 : ℝ) * t)‖) :=
    ae_all_iff.2 hUpper
  have hAllLower :
      ∀ᵐ t ∂volume, ∀ m : ℕ,
        (1 / 2 : ℝ) ^ (m + 1) < t → t ≤ (1 / 2 : ℝ) ^ m →
          Summable (fun n : ℕ ↦ ‖f ((n + 1 : ℝ) * t)‖) :=
    ae_all_iff.2 hLower
  have hNotPow :
      ∀ᵐ t ∂volume, ∀ m : ℕ, t ≠ (2 : ℝ) ^ m := by
    refine ae_all_iff.2 ?_
    intro m
    rw [ae_iff]
    simp [measure_singleton]
  have hIoi :
      ∀ᵐ t ∂volume, t ∈ Ioi (0 : ℝ) →
        Summable (fun n : ℕ ↦ ‖f ((n + 1 : ℝ) * t)‖) := by
    filter_upwards [hAllUpper, hAllLower, hNotPow] with t htUpper htLower htPow ht
    by_cases h1 : 1 ≤ t
    · rcases exists_nat_pow_near h1 one_lt_two with ⟨m, hm₁, hm₂⟩
      have hm₁_lt : (2 : ℝ) ^ m < t := by
        refine lt_of_le_of_ne hm₁ ?_
        exact fun hEq => htPow m hEq.symm
      exact htUpper m hm₁_lt hm₂.le
    · have ht_le_one : t ≤ 1 := le_of_not_ge h1
      rcases exists_nat_pow_near_of_lt_one ht ht_le_one (by positivity : 0 < (1 / 2 : ℝ))
          (by norm_num : (1 / 2 : ℝ) < 1) with ⟨m, hm₁, hm₂⟩
      exact htLower m hm₁ hm₂
  refine (ae_restrict_iff' measurableSet_Ici).2 ?_
  have hne_zero :
      ∀ᵐ t ∂volume, t ≠ (0 : ℝ) := by
    rw [ae_iff]
    simp [measure_singleton]
  filter_upwards [hIoi, hne_zero] with t ht hne ht0
  exact ht (lt_of_le_of_ne ht0 fun h => hne h.symm)

/-- Exercise 4.2.3: if `f` is Lebesgue integrable on `[0, ∞)`, then for Lebesgue-almost every
`t ∈ [0, ∞)` the sampled series `∑ n = 1 to ∞, f (n t)` converges absolutely. In Lean's `0`-based
indexing, this is the summability of `n ↦ |f ((n + 1) * t)|`. -/
theorem ae_summable_abs_at_nat_multiples_of_integrableOn_Ici (f : ℝ → ℝ)
    (hf : IntegrableOn f (Ici 0)) :
    ∀ᵐ t ∂(volume.restrict (Ici 0)), Summable (fun n : ℕ ↦ |f ((n + 1 : ℝ) * t)|) := by
  simpa [Real.norm_eq_abs] using ae_summable_norm_at_nat_multiples_of_integrableOn_Ici f hf
