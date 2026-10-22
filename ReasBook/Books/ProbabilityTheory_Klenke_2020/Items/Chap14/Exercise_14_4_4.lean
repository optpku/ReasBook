/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Books.ProbabilityTheory_Klenke_2020.Items.Chap14.Definition_14_46

-- Declarations for this item will be appended below by the statement pipeline.

open Filter MeasureTheory
open scoped MeasureTheory Topology

namespace IsContinuousConvolutionSemigroup

/-- Helper for Exercise 14.4.4: convolving two probability measures on `ℝ` that are supported in
`[0, ∞)` again yields a probability measure supported in `[0, ∞)`. -/
private lemma measureIioZero_mul (μ ν : ProbabilityMeasure ℝ)
    (hμ : (μ : Measure ℝ) (Set.Iio 0) = 0)
    (hν : (ν : Measure ℝ) (Set.Iio 0) = 0) :
    (((μ * ν : ProbabilityMeasure ℝ) : Measure ℝ) (Set.Iio 0) = 0) := by
  -- Proof comment: rewrite convolution as the pushforward of the product measure under addition,
  -- then `x + y < 0` forces at least one coordinate to lie in `(-∞, 0)`.
  rw [show (((μ * ν : ProbabilityMeasure ℝ) : Measure ℝ)) =
      (μ : Measure ℝ) ∗ (ν : Measure ℝ) by rfl]
  rw [Measure.conv, Measure.map_apply measurable_add measurableSet_Iio]
  have hsubset :
      (fun p : ℝ × ℝ ↦ p.1 + p.2) ⁻¹' Set.Iio 0 ⊆
        (Set.Iio 0 ×ˢ (Set.univ : Set ℝ)) ∪ ((Set.univ : Set ℝ) ×ˢ Set.Iio 0) := by
    intro z hz
    rcases z with ⟨x, y⟩
    simp only [Set.mem_preimage, Set.mem_Iio, Set.mem_union, Set.mem_prod, Set.mem_univ,
      true_and, and_true] at hz ⊢
    by_cases hx : x < 0
    · exact Or.inl hx
    · right
      linarith
  have hleft :
      ((μ : Measure ℝ).prod (ν : Measure ℝ)) (Set.Iio 0 ×ˢ (Set.univ : Set ℝ)) = 0 := by
    rw [Measure.prod_prod]
    simp [hμ]
  have hright :
      ((μ : Measure ℝ).prod (ν : Measure ℝ)) ((Set.univ : Set ℝ) ×ˢ Set.Iio 0) = 0 := by
    rw [Measure.prod_prod]
    simp [hν]
  have hnull_union :
      ((μ : Measure ℝ).prod (ν : Measure ℝ))
        ((Set.Iio 0 ×ˢ (Set.univ : Set ℝ)) ∪ ((Set.univ : Set ℝ) ×ˢ Set.Iio 0)) = 0 := by
    refine le_antisymm ?_ bot_le
    refine le_trans (measure_union_le _ _) ?_
    simp [hleft, hright]
  exact measure_mono_null hsubset hnull_union

/-- Helper for Exercise 14.4.4: if the self-convolution `μ * μ` gives no mass to `(-∞, 0)`, then
`μ` already gives no mass to `(-∞, 0)`. -/
private lemma measureIioZero_of_selfMul_measureIioZero (μ : ProbabilityMeasure ℝ)
    (hμ :
      (((μ * μ : ProbabilityMeasure ℝ) : Measure ℝ) (Set.Iio 0) = 0)) :
    (μ : Measure ℝ) (Set.Iio 0) = 0 := by
  -- Proof comment: the negative rectangle `(-∞, 0) × (-∞, 0)` maps into `(-∞, 0)` under
  -- addition, so vanishing of the convolved mass forces the square of the negative mass to be `0`.
  rw [show (((μ * μ : ProbabilityMeasure ℝ) : Measure ℝ)) =
      (μ : Measure ℝ) ∗ (μ : Measure ℝ) by rfl,
    Measure.conv, Measure.map_apply measurable_add measurableSet_Iio] at hμ
  have hrect :
      ((μ : Measure ℝ).prod (μ : Measure ℝ)) (Set.Iio 0 ×ˢ Set.Iio 0) = 0 := by
    refine measure_mono_null ?_ hμ
    intro z hz
    rcases z with ⟨x, y⟩
    simp only [Set.mem_preimage, Set.mem_Iio, Set.mem_prod] at hz ⊢
    linarith
  have hsquare :
      (μ : Measure ℝ) (Set.Iio 0) * (μ : Measure ℝ) (Set.Iio 0) = 0 := by
    simpa [Measure.prod_prod] using hrect
  rcases mul_eq_zero.mp hsquare with hzero | hzero
  · exact hzero
  · exact hzero

/-- Helper for Exercise 14.4.4: convolution is continuous on `ProbabilityMeasure ℝ`. -/
private lemma continuousMulProbabilityMeasure :
    Continuous (fun p : ProbabilityMeasure ℝ × ProbabilityMeasure ℝ ↦ p.1 * p.2) := by
  -- Proof comment: convolution is product-measure formation followed by pushforward along
  -- addition.
  have hprod :
      Continuous (fun p : ProbabilityMeasure ℝ × ProbabilityMeasure ℝ ↦ p.1.prod p.2) :=
    ProbabilityMeasure.continuous_prod
  have hmap :
      Continuous (fun η : ProbabilityMeasure (ℝ × ℝ) ↦
        ProbabilityMeasure.map η continuous_add.measurable.aemeasurable) :=
    ProbabilityMeasure.continuous_map continuous_add
  simpa [ProbabilityMeasure.conv_eq_map] using hmap.comp hprod

/-- Helper for Exercise 14.4.4: a continuous convolution semigroup is right-continuous at every
time. -/
private lemma tendsto_add_right {ν : NNReal → ProbabilityMeasure ℝ}
    [IsContinuousConvolutionSemigroup ν] (t : NNReal) :
    Tendsto (fun u : NNReal ↦ ν (t + u)) (𝓝 0) (𝓝 (ν t)) := by
  -- Proof comment: write `ν (t + u)` as `ν t * ν u` and use that `ν u → δ₀` as `u → 0`.
  have hpair :
      Tendsto (fun u : NNReal ↦ (ν t, ν u)) (𝓝 0)
        (𝓝 (ν t, diracProba (0 : ℝ))) := by
    exact tendsto_const_nhds.prodMk_nhds (IsContinuousConvolutionSemigroup.tendsto_zero (ν := ν))
  have hmul :
      Tendsto (fun u : NNReal ↦ ν t * ν u) (𝓝 0)
        (𝓝 (ν t * diracProba (0 : ℝ))) :=
    continuousMulProbabilityMeasure.continuousAt.tendsto.comp hpair
  have hconv :
      Tendsto (fun u : NNReal ↦ ν (t + u)) (𝓝 0) (𝓝 (ν t * diracProba (0 : ℝ))) := by
    simpa [IsConvolutionSemigroup.convolution_eq] using hmul
  have hlimit : ν t * diracProba (0 : ℝ) = ν t := by
    rw [← ProbabilityMeasure.one_eq_diracProba, mul_one]
  simpa [hlimit] using hconv

/-- Helper for Exercise 14.4.4: the standard right-dyadic approximation of a nonnegative real. -/
private noncomputable def dyadicRightApprox (t : NNReal) (n : ℕ) : NNReal :=
  ((Nat.ceil ((t : ℝ) * (2 : ℝ) ^ n) : ℕ) : NNReal) / (2 : NNReal) ^ n

/-- Helper for Exercise 14.4.4: the right-dyadic approximation stays to the right of the target
time. -/
private lemma le_dyadicRightApprox (t : NNReal) (n : ℕ) :
    t ≤ dyadicRightApprox t n := by
  -- Proof comment: `Nat.ceil` rounds the scaled time upward, so dividing back by `2^n` stays on
  -- or to the right of `t`.
  unfold dyadicRightApprox
  have hpow_pos : 0 < (2 : NNReal) ^ n := by positivity
  have hceil :
      (t : ℝ) * (2 : ℝ) ^ n ≤ (Nat.ceil ((t : ℝ) * (2 : ℝ) ^ n) : ℝ) := by
    exact Nat.le_ceil _
  rw [le_div_iff₀ hpow_pos]
  exact_mod_cast hceil

/-- Helper for Exercise 14.4.4: the right-dyadic approximations converge down to the target. -/
private lemma tendsto_dyadicRightApprox (t : NNReal) :
    Tendsto (dyadicRightApprox t) atTop (𝓝 t) := by
  -- Proof comment: this is the standard limit `ceil (t x) / x → t` along the powers `x = 2^n`.
  refine (NNReal.tendsto_coe).mp ?_
  simpa [dyadicRightApprox] using
    (tendsto_nat_ceil_mul_div_atTop (a := (t : ℝ)) t.2).comp
      (tendsto_pow_atTop_atTop_of_one_lt one_lt_two)

/-- Exercise 14.4.4: if a continuous real convolution semigroup has one positive-time marginal
with zero mass on the negative half-line `(-∞, 0)`, then it satisfies the owner predicate
`IsNonnegativeConvolutionSemigroup`. -/
-- Proof sketch: use the convolution semigroup property to propagate the support condition from one
-- positive time to its rational subdivisions and multiples, then combine continuity at `0` with
-- weak convergence to extend the zero-mass property on `(-∞, 0)` to every time `t ≥ 0`.
theorem isNonnegative_of_exists_pos_measure_Iio_zero
    (ν : NNReal → ProbabilityMeasure ℝ)
    [IsContinuousConvolutionSemigroup ν]
    (h_nonneg_time : ∃ t > 0, (ν t : Measure ℝ) (Set.Iio 0) = 0) :
    IsNonnegativeConvolutionSemigroup ν := by
  -- Proof comment: define the good times by vanishing mass on `(-∞, 0)`, propagate that property
  -- through addition and halving, then approximate an arbitrary time from above by dyadic good
  -- times and pass to the limit using right continuity and Portmanteau.
  rcases h_nonneg_time with ⟨t0, ht0, ht0_zero⟩
  let good : NNReal → Prop := fun t ↦ (ν t : Measure ℝ) (Set.Iio 0) = 0
  have hgood_zero : good 0 := by
    -- Proof comment: the time-zero marginal is `δ₀`, so it has no mass on `(-∞, 0)`.
    simp [good]
  have hgood_add : ∀ {s t : NNReal}, good s → good t → good (s + t) := by
    intro s t hs ht
    -- Proof comment: convolution of two nonnegative laws remains nonnegative.
    change (ν (s + t) : Measure ℝ) (Set.Iio 0) = 0
    rw [IsConvolutionSemigroup.convolution_eq_toMeasure (ν := ν) s t]
    exact measureIioZero_mul (ν s) (ν t) hs ht
  have hgood_half : ∀ {t : NNReal}, good t → good (t / 2) := by
    intro t ht
    -- Proof comment: if `ν t = ν (t / 2) * ν (t / 2)` has no negative mass, then neither does
    -- `ν (t / 2)`.
    have hhalf_eq : t / 2 + t / 2 = t := by
      exact_mod_cast add_halves (t : ℝ)
    have hconv :
        (((ν (t / 2) * ν (t / 2) : ProbabilityMeasure ℝ) : Measure ℝ) (Set.Iio 0) = 0) := by
      have htime : (ν (t / 2 + t / 2) : Measure ℝ) (Set.Iio 0) = 0 := by
        simpa [hhalf_eq, good] using ht
      rw [IsConvolutionSemigroup.convolution_eq_toMeasure (ν := ν) (t / 2) (t / 2)] at htime
      exact htime
    exact measureIioZero_of_selfMul_measureIioZero (μ := ν (t / 2)) hconv
  have hgood_natMul : ∀ {s : NNReal}, good s → ∀ m : ℕ, good ((m : NNReal) * s) := by
    intro s hs m
    induction m with
    | zero =>
        simpa using hgood_zero
    | succ m hm =>
        -- Proof comment: nat-multiples are built by one more addition of the base good time.
        simpa [Nat.cast_add, add_mul, one_mul, add_comm, add_left_comm, add_assoc] using
          hgood_add hm hs
  have hgood_dyadic : ∀ n : ℕ, good (t0 / (2 : NNReal) ^ n) := by
    intro n
    induction n with
    | zero =>
        simpa [good] using ht0_zero
    | succ n ih =>
        -- Proof comment: repeated halving propagates the support property to every dyadic mesh
        -- point below `t0`.
        simpa [pow_succ, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using
          hgood_half ih
  refine
    { toIsConvolutionSemigroup := inferInstance
      measure_Iio_zero := ?_ }
  intro t
  let ratio : NNReal := t / t0
  let approx : ℕ → NNReal := fun n ↦ dyadicRightApprox ratio n * t0
  have happrox_good : ∀ n : ℕ, good (approx n) := by
    intro n
    -- Proof comment: each approximation is a natural multiple of the dyadic mesh `t0 / 2^n`.
    simpa [good, approx, ratio, dyadicRightApprox, div_eq_mul_inv, mul_assoc, mul_left_comm,
      mul_comm] using
      (hgood_natMul (s := t0 / (2 : NNReal) ^ n) (hgood_dyadic n)
        (Nat.ceil ((ratio : ℝ) * (2 : ℝ) ^ n)))
  have hle_approx : ∀ n : ℕ, t ≤ approx n := by
    intro n
    -- Proof comment: the dyadic ceiling stays on the right of `t / t0`, and multiplying by the
    -- positive scale `t0` preserves the inequality.
    calc
      t = ratio * t0 := by
        simp [ratio, ht0.ne']
      _ ≤ dyadicRightApprox ratio n * t0 := by
        exact mul_le_mul_of_nonneg_right (le_dyadicRightApprox ratio n) ht0.le
      _ = approx n := rfl
  have happrox_tendsto : Tendsto approx atTop (𝓝 t) := by
    -- Proof comment: dyadic ceilings converge to the scaled ratio, so after multiplying by `t0`
    -- they converge back to `t`.
    have hratio :
        Tendsto (dyadicRightApprox ratio) atTop (𝓝 ratio) :=
      tendsto_dyadicRightApprox ratio
    have hscaled :
        Tendsto (fun n : ℕ ↦ t0 * dyadicRightApprox ratio n) atTop (𝓝 (t0 * ratio)) := by
      exact hratio.const_mul t0
    have hscaled' : Tendsto approx atTop (𝓝 (ratio * t0)) := by
      simpa [approx, mul_comm, mul_left_comm, mul_assoc] using hscaled
    simpa [ratio, ht0.ne', div_mul_cancel₀] using hscaled'
  have hrem_tendsto : Tendsto (fun n : ℕ ↦ approx n - t) atTop (𝓝 (0 : NNReal)) := by
    -- Proof comment: each approximation lies to the right of `t`, so the remainders are genuine
    -- nonnegative errors and vanish because `approx n → t`.
    have happrox_real :
        Tendsto (fun n : ℕ ↦ ((approx n : NNReal) : ℝ)) atTop (𝓝 (t : ℝ)) :=
      (NNReal.tendsto_coe).mpr happrox_tendsto
    have hsub :
        Tendsto (fun n : ℕ ↦ ((approx n : NNReal) : ℝ) - (t : ℝ)) atTop (𝓝 (0 : ℝ)) := by
      simpa using
        happrox_real.sub
          (tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ (t : ℝ)) atTop (𝓝 (t : ℝ)))
    have hsub' :
        Tendsto (fun n : ℕ ↦ (((approx n - t : NNReal) : NNReal) : ℝ)) atTop (𝓝 (0 : ℝ)) := by
      convert hsub using 1
      ext n
      rw [NNReal.coe_sub (hle_approx n)]
    exact (NNReal.tendsto_coe).mp hsub'
  have hν_approx_tendsto : Tendsto (fun n : ℕ ↦ ν (approx n)) atTop (𝓝 (ν t)) := by
    -- Proof comment: write each approximation time as `t + (approx n - t)` and apply right
    -- continuity at `t`.
    have hright :
        Tendsto (fun n : ℕ ↦ ν (t + (approx n - t))) atTop (𝓝 (ν t)) :=
      (tendsto_add_right (ν := ν) t).comp hrem_tendsto
    convert hright using 1
    ext n
    rw [add_comm, tsub_add_cancel_of_le (hle_approx n)]
  have hport :
      (ν t : Measure ℝ) (Set.Iio 0) ≤ atTop.liminf
        (fun n : ℕ ↦ (ν (approx n) : Measure ℝ) (Set.Iio 0)) := by
    exact ProbabilityMeasure.le_liminf_measure_open_of_tendsto hν_approx_tendsto isOpen_Iio
  have hvalues :
      (fun n : ℕ ↦ (ν (approx n) : Measure ℝ) (Set.Iio 0)) = fun _ ↦ 0 := by
    funext n
    simpa [good] using happrox_good n
  exact le_antisymm (by simpa [hvalues] using hport) bot_le

end IsContinuousConvolutionSemigroup
