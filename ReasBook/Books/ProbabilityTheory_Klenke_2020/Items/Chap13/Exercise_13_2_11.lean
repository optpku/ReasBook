/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib
import Books.ProbabilityTheory_Klenke_2020.Items.Chap01.Theorem_1_60
import Books.ProbabilityTheory_Klenke_2020.Items.Chap13.Theorem_13_23
import Books.ProbabilityTheory_Klenke_2020.Items.Chap13.Definition_13_4

-- Declarations for this item will be appended below by the statement pipeline.

open Filter MeasureTheory ProbabilityTheory
open scoped Topology

noncomputable section

/- Exercise 13.2.11 is source-facing. Its owner abstraction is weak convergence in
`ProbabilityMeasure ℝ`, and the scaled geometric law is the derived pushforward of the geometric
probability measure along `k ↦ k / n`, so no separate public wrapper definition is needed. -/

private noncomputable def geometricProbabilityMeasure (p : ℝ) (hp_pos : 0 < p) (hp_lt_one : p < 1) :
    ProbabilityMeasure ℕ :=
  ⟨geometricMeasure hp_pos (le_of_lt hp_lt_one),
    isProbabilityMeasure_geometricMeasure hp_pos (le_of_lt hp_lt_one)⟩

private noncomputable def expProbabilityMeasure (α : ℝ) (hα : 0 < α) : ProbabilityMeasure ℝ :=
  ⟨expMeasure α, isProbabilityMeasure_expMeasure hα⟩

/-- Helper for Exercise 13.2.11: the scaled geometric law is the pushforward of the geometric
probability measure along `k ↦ k / n`. -/
private noncomputable def scaledGeometricProbabilityMeasure
    (p : ℕ+ → ℝ) (hp_pos : ∀ n, 0 < p n) (hp_lt_one : ∀ n, p n < 1) (n : ℕ+) :
    ProbabilityMeasure ℝ :=
  (geometricProbabilityMeasure (p n) (hp_pos n) (hp_lt_one n)).map
    ((measurable_of_countable fun k : ℕ ↦ (k : ℝ) / (n : ℝ)).aemeasurable)

/-- Helper for Exercise 13.2.11: for `x < 0`, the scaled map `k ↦ k / n` has empty `Iic x`
preimage because all scaled values are nonnegative. -/
private lemma scaledNatDiv_preimage_Iic_of_neg (n : ℕ+) {x : ℝ} (hx : x < 0) :
    (fun k : ℕ ↦ (k : ℝ) / (n : ℝ)) ⁻¹' Set.Iic x = (∅ : Set ℕ) := by
  -- Proof comment: every point mass sits on the nonnegative half-line, so no atom can land below
  -- a negative threshold.
  ext k
  constructor
  · intro hk
    have hk_nonneg : 0 ≤ (k : ℝ) / (n : ℝ) := by positivity
    have hk_le : (k : ℝ) / (n : ℝ) ≤ x := by simpa using hk
    linarith
  · intro hk
    simp at hk

/-- Helper for Exercise 13.2.11: for `x ≥ 0`, the scaled map `k ↦ k / n` pulls `Iic x` back to
the initial segment `{0, ..., ⌊n x⌋}`. -/
private lemma scaledNatDiv_preimage_Iic_of_nonneg (n : ℕ+) {x : ℝ} (hx : 0 ≤ x) :
    (fun k : ℕ ↦ (k : ℝ) / (n : ℝ)) ⁻¹' Set.Iic x =
      (Finset.range (Nat.floor ((n : ℝ) * x) + 1) : Set ℕ) := by
  -- Proof comment: convert the inequality `k / n ≤ x` into `k ≤ n x`, then package the integer
  -- bound through `Nat.floor`.
  ext k
  constructor
  · intro hk
    have hn : 0 < (n : ℝ) := by positivity
    have hk' : (k : ℝ) ≤ (n : ℝ) * x := by
      have hmul : (k : ℝ) ≤ x * (n : ℝ) := (div_le_iff₀ hn).1 hk
      simpa [mul_comm] using hmul
    have hfloor :
        k ≤ Nat.floor ((n : ℝ) * x) := by
      exact
        (Nat.le_floor_iff (show 0 ≤ (n : ℝ) * x by positivity)).2 hk'
    exact Finset.mem_range.mpr (Nat.lt_succ_of_le hfloor)
  · intro hk
    have hn : 0 < (n : ℝ) := by positivity
    have hk_floor : k ≤ Nat.floor ((n : ℝ) * x) := Nat.le_of_lt_succ (Finset.mem_range.mp hk)
    have hk' : (k : ℝ) ≤ (n : ℝ) * x := by
      exact
        le_trans
          (by exact_mod_cast hk_floor)
          (Nat.floor_le (show 0 ≤ (n : ℝ) * x by positivity))
    have hmul : (k : ℝ) ≤ x * (n : ℝ) := by simpa [mul_comm] using hk'
    exact (div_le_iff₀ hn).2 hmul

/-- Helper for Exercise 13.2.11: the geometric law assigns mass `1 - (1 - p)^m` to the prefix
`{0, ..., m - 1}`. -/
private lemma geometricPrefixMass_eq (p : ℝ) (hp_pos : 0 < p) (hp_lt_one : p < 1) (m : ℕ) :
    (geometricMeasure hp_pos (le_of_lt hp_lt_one) (Finset.range m : Set ℕ)).toReal =
      1 - (1 - p) ^ m := by
  -- Proof comment: rewrite the prefix mass as a finite PMF sum and close it with the standard
  -- finite geometric-series identity.
  rw [geometricMeasure, PMF.toMeasure_apply_finset]
  rw [ENNReal.toReal_sum (fun a _ha ↦ (geometricPMF hp_pos (le_of_lt hp_lt_one)).apply_ne_top a)]
  have hsum :
      ∑ x ∈ Finset.range m, (geometricPMF hp_pos (le_of_lt hp_lt_one) x).toReal =
        (∑ i ∈ Finset.range m, (1 - p) ^ i) * p := by
    calc
      ∑ x ∈ Finset.range m, (geometricPMF hp_pos (le_of_lt hp_lt_one) x).toReal
          = ∑ x ∈ Finset.range m, (1 - p) ^ x * p := by
              refine Finset.sum_congr rfl fun x hx ↦ ?_
              change ENNReal.toReal (ENNReal.ofReal (geometricPMFReal p x)) = (1 - p) ^ x * p
              have hnonneg : 0 ≤ geometricPMFReal p x :=
                geometricPMFReal_nonneg hp_pos (le_of_lt hp_lt_one)
              rw [ENNReal.toReal_ofReal hnonneg]
              simp [geometricPMFReal, mul_comm]
      _ = (∑ i ∈ Finset.range m, (1 - p) ^ i) * p := by
            rw [Finset.sum_mul]
  rw [hsum]
  have hp_sub : 1 - (1 - p) = p := by ring
  simpa [hp_sub] using geom_sum_mul_neg (1 - p) m

/-- Helper for Exercise 13.2.11: the cdf of the scaled geometric law is the explicit floor
formula coming from the geometric prefix mass. -/
private lemma scaledGeometric_cdf_eq
    (p : ℕ+ → ℝ) (hp_pos : ∀ n, 0 < p n) (hp_lt_one : ∀ n, p n < 1) (n : ℕ+) (x : ℝ) :
    cdf ((scaledGeometricProbabilityMeasure p hp_pos hp_lt_one n : ProbabilityMeasure ℝ) :
        Measure ℝ) x =
      if x < 0 then 0 else 1 - (1 - p n) ^ (Nat.floor ((n : ℝ) * x) + 1) := by
  -- Proof comment: rewrite the cdf as the pushed-forward mass of `Iic x`, identify the preimage,
  -- and evaluate the resulting geometric prefix.
  have hMeas :
      AEMeasurable (fun k : ℕ ↦ (k : ℝ) / (n : ℝ))
        (geometricProbabilityMeasure (p n) (hp_pos n) (hp_lt_one n)) :=
    (measurable_of_countable fun k : ℕ ↦ (k : ℝ) / (n : ℝ)).aemeasurable
  rw [ProbabilityTheory.cdf_eq_real, Measure.real_def]
  have hMapApply :
      (((scaledGeometricProbabilityMeasure p hp_pos hp_lt_one n : ProbabilityMeasure ℝ) :
          Measure ℝ) (Set.Iic x)) =
        (((geometricProbabilityMeasure (p n) (hp_pos n) (hp_lt_one n) : ProbabilityMeasure ℕ) :
          Measure ℕ) (((fun k : ℕ ↦ (k : ℝ) / (n : ℝ)) ⁻¹' Set.Iic x))) := by
    rw [scaledGeometricProbabilityMeasure]
    exact ProbabilityMeasure.map_apply' _ hMeas measurableSet_Iic
  rw [hMapApply]
  by_cases hx : x < 0
  · rw [if_pos hx, scaledNatDiv_preimage_Iic_of_neg n hx]
    simp [geometricProbabilityMeasure]
  · have hx0 : 0 ≤ x := le_of_not_gt hx
    rw [if_neg hx, scaledNatDiv_preimage_Iic_of_nonneg n hx0]
    simpa [geometricProbabilityMeasure] using
      geometricPrefixMass_eq (p n) (hp_pos n) (hp_lt_one n) (Nat.floor ((n : ℝ) * x) + 1)

/-- Helper for Exercise 13.2.11: at `0`, the scaled geometric cdf equals the success probability
`p n`. -/
private lemma scaledGeometric_cdf_zero
    (p : ℕ+ → ℝ) (hp_pos : ∀ n, 0 < p n) (hp_lt_one : ∀ n, p n < 1) (n : ℕ+) :
    cdf ((scaledGeometricProbabilityMeasure p hp_pos hp_lt_one n : ProbabilityMeasure ℝ) :
        Measure ℝ) 0 = p n := by
  -- Proof comment: specialize the explicit cdf formula at `x = 0`, where the floor term is `0`.
  rw [scaledGeometric_cdf_eq p hp_pos hp_lt_one n 0, if_neg (show ¬ (0 : ℝ) < 0 by norm_num)]
  simp

/-- Helper for Exercise 13.2.11: at `1`, the scaled geometric cdf is
`1 - (1 - p n)^((n : ℕ) + 1)`. -/
private lemma scaledGeometric_cdf_one
    (p : ℕ+ → ℝ) (hp_pos : ∀ n, 0 < p n) (hp_lt_one : ∀ n, p n < 1) (n : ℕ+) :
    cdf ((scaledGeometricProbabilityMeasure p hp_pos hp_lt_one n : ProbabilityMeasure ℝ) :
        Measure ℝ) 1 =
      1 - (1 - p n) ^ ((n : ℕ) + 1) := by
  -- Proof comment: at `x = 1`, the floor term is exactly `n`, so the cdf reads off the unit-step
  -- geometric tail.
  rw [scaledGeometric_cdf_eq p hp_pos hp_lt_one n 1, if_neg (show ¬ (1 : ℝ) < 0 by norm_num)]
  simp

/-- Helper for Exercise 13.2.11: the exponential cdf can be rewritten in the continuous normal
form `1 - exp (-(α * max x 0))`. -/
private lemma expProbabilityMeasure_cdf_eq_max (α : ℝ) (hα : 0 < α) (x : ℝ) :
    cdf ((expProbabilityMeasure α hα : ProbabilityMeasure ℝ) : Measure ℝ) x =
      1 - Real.exp (-(α * max x 0)) := by
  -- Proof comment: this packages the left and right branches of the exponential cdf into one
  -- continuous expression through `max x 0`.
  by_cases hx : 0 ≤ x
  · simpa [expProbabilityMeasure, hx, max_eq_left hx] using cdf_expMeasure_eq hα x
  · have hx' : x < 0 := lt_of_not_ge hx
    simpa [expProbabilityMeasure, hx, hx', max_eq_right (le_of_lt hx')] using cdf_expMeasure_eq hα x

/-- Helper for Exercise 13.2.11: the exponential limit cdf is continuous at every real point. -/
private lemma continuousAt_expProbabilityMeasure_cdf (α : ℝ) (hα : 0 < α) (x : ℝ) :
    ContinuousAt (cdf ((expProbabilityMeasure α hα : ProbabilityMeasure ℝ) : Measure ℝ)) x := by
  -- Proof comment: rewrite the cdf through the continuous `max`-normal form and appeal to
  -- continuity of `exp`.
  have hEq :
      cdf ((expProbabilityMeasure α hα : ProbabilityMeasure ℝ) : Measure ℝ) =
        fun y : ℝ ↦ 1 - Real.exp (-(α * max y 0)) := by
    funext y
    exact expProbabilityMeasure_cdf_eq_max α hα y
  rw [hEq]
  have hcont : Continuous fun y : ℝ ↦ 1 - Real.exp (-(α * max y 0)) := by
    refine continuous_const.sub ?_
    exact
      Real.continuous_exp.comp
        ((continuous_const.mul (continuous_id.max continuous_const)).neg)
  exact hcont.continuousAt

/-- Helper for Exercise 13.2.11: at a continuity point of the limiting cdf, weak convergence of
probability measures forces convergence of the cdf values. -/
private lemma tendsto_cdf_of_tendsto_probabilityMeasure
    {νs : ℕ → ProbabilityMeasure ℝ} {ν : ProbabilityMeasure ℝ}
    (hν : Tendsto νs atTop (𝓝 ν)) (x : ℝ)
    (hx : ContinuousAt (cdf ((ν : ProbabilityMeasure ℝ) : Measure ℝ)) x) :
    Tendsto (fun n ↦ cdf ((νs n : ProbabilityMeasure ℝ) : Measure ℝ) x) atTop
      (𝓝 (cdf ((ν : ProbabilityMeasure ℝ) : Measure ℝ) x)) := by
  have hsubν : ν.toFiniteMeasure.mass ≤ 1 := by
    simpa using ν.mass_toFiniteMeasure.le
  have hsubνs : ∀ n, (νs n).toFiniteMeasure.mass ≤ 1 := by
    intro n
    simpa using (νs n).mass_toFiniteMeasure.le
  have hcdfν :
      cdf ((ν : ProbabilityMeasure ℝ) : Measure ℝ) =
        measureDistributionFunction ((ν : ProbabilityMeasure ℝ) : Measure ℝ) :=
    cdf_eq_measureDistributionFunction ((ν : ProbabilityMeasure ℝ) : Measure ℝ)
  have hcdfνs :
      ∀ n,
        cdf ((νs n : ProbabilityMeasure ℝ) : Measure ℝ) =
          measureDistributionFunction ((νs n : ProbabilityMeasure ℝ) : Measure ℝ) :=
    fun n ↦ cdf_eq_measureDistributionFunction ((νs n : ProbabilityMeasure ℝ) : Measure ℝ)
  have hdf :
      distribution_function_weakly_converges_to
        (fun n ↦ measureDistributionFunction ((νs n : ProbabilityMeasure ℝ) : Measure ℝ))
        (measureDistributionFunction ((ν : ProbabilityMeasure ℝ) : Measure ℝ)) := by
    rw [ProbabilityMeasure.tendsto_nhds_iff_toFiniteMeasure_tendsto_nhds] at hν
    exact
      (tendsto_iff_measureDistributionFunction_tendsto
        (fun n ↦ (νs n).toFiniteMeasure) ν.toFiniteMeasure hsubν hsubνs).1 hν
  have hpoint :=
    (measureDistributionFunction_weakly_converges_to_iff
      (fun n ↦ (νs n).toFiniteMeasure) ν.toFiniteMeasure hsubν hsubνs).1 hdf
  have hx' :
      ContinuousAt (measureDistributionFunction ((ν : ProbabilityMeasure ℝ) : Measure ℝ)) x := by
    simpa [hcdfν] using hx
  simpa [hcdfν, hcdfνs] using hpoint.2 hx'

/-- Helper for Exercise 13.2.11: on `ProbabilityMeasure ℝ`, cdf convergence at every continuity
point of the limit cdf implies weak convergence. -/
private lemma tendsto_probabilityMeasure_of_cdf_tendsto
    {νs : ℕ → ProbabilityMeasure ℝ} {ν : ProbabilityMeasure ℝ}
    (hcont :
      ∀ x : ℝ,
        ContinuousAt (cdf ((ν : ProbabilityMeasure ℝ) : Measure ℝ)) x →
          Tendsto (fun n ↦ cdf ((νs n : ProbabilityMeasure ℝ) : Measure ℝ) x) atTop
            (𝓝 (cdf ((ν : ProbabilityMeasure ℝ) : Measure ℝ) x))) :
    Tendsto νs atTop (𝓝 ν) := by
  have hsubν : ν.toFiniteMeasure.mass ≤ 1 := by
    simpa using ν.mass_toFiniteMeasure.le
  have hsubνs : ∀ n, (νs n).toFiniteMeasure.mass ≤ 1 := by
    intro n
    simpa using (νs n).mass_toFiniteMeasure.le
  have hcdfν :
      cdf ((ν : ProbabilityMeasure ℝ) : Measure ℝ) =
        measureDistributionFunction ((ν : ProbabilityMeasure ℝ) : Measure ℝ) :=
    cdf_eq_measureDistributionFunction ((ν : ProbabilityMeasure ℝ) : Measure ℝ)
  have hcdfνs :
      ∀ n,
        cdf ((νs n : ProbabilityMeasure ℝ) : Measure ℝ) =
          measureDistributionFunction ((νs n : ProbabilityMeasure ℝ) : Measure ℝ) :=
    fun n ↦ cdf_eq_measureDistributionFunction ((νs n : ProbabilityMeasure ℝ) : Measure ℝ)
  have hdf :
      distribution_function_weakly_converges_to
        (fun n ↦ measureDistributionFunction ((νs n : ProbabilityMeasure ℝ) : Measure ℝ))
        (measureDistributionFunction ((ν : ProbabilityMeasure ℝ) : Measure ℝ)) := by
    refine
      (measureDistributionFunction_weakly_converges_to_iff
        (fun n ↦ (νs n).toFiniteMeasure) ν.toFiniteMeasure hsubν hsubνs).2 ?_
    refine ⟨?_, ?_⟩
    · simp
    · intro x hx
      have hx' : ContinuousAt (cdf ((ν : ProbabilityMeasure ℝ) : Measure ℝ)) x := by
        simpa [hcdfν] using hx
      simpa [hcdfν, hcdfνs] using hcont x hx'
  rw [ProbabilityMeasure.tendsto_nhds_iff_toFiniteMeasure_tendsto_nhds]
  exact
    (tendsto_iff_measureDistributionFunction_tendsto
      (fun n ↦ (νs n).toFiniteMeasure) ν.toFiniteMeasure hsubν hsubνs).2 hdf

/-- Helper for Exercise 13.2.11: weak convergence of real probability measures is equivalent to
cdf convergence at every continuity point of the limit cdf. -/
private lemma probabilityMeasure_tendsto_iff_cdf_tendsto
    {νs : ℕ → ProbabilityMeasure ℝ} {ν : ProbabilityMeasure ℝ} :
    Tendsto νs atTop (𝓝 ν) ↔
      ∀ x : ℝ,
        ContinuousAt (cdf ((ν : ProbabilityMeasure ℝ) : Measure ℝ)) x →
          Tendsto (fun n ↦ cdf ((νs n : ProbabilityMeasure ℝ) : Measure ℝ) x) atTop
            (𝓝 (cdf ((ν : ProbabilityMeasure ℝ) : Measure ℝ) x)) := by
  constructor
  · intro hν x hx
    exact tendsto_cdf_of_tendsto_probabilityMeasure hν x hx
  · intro hcdf
    exact tendsto_probabilityMeasure_of_cdf_tendsto hcdf

/-- Helper for Exercise 13.2.11: reindexing a `ℕ+`-sequence along `Nat.succPNat` preserves its
`atTop` limit. -/
private lemma tendsto_pnat_atTop_iff_succPNat {β : Type*} [TopologicalSpace β]
    {f : ℕ+ → β} {l : Filter β} :
    Tendsto f atTop l ↔ Tendsto (fun n : ℕ ↦ f (Nat.succPNat n)) atTop l := by
  constructor
  · intro hf
    -- Proof comment: compose the `ℕ+`-indexed limit with the order isomorphism `ℕ ≃o ℕ+`.
    simpa [OrderIso.pnatIsoNat_symm_apply] using hf.comp OrderIso.pnatIsoNat.symm.tendsto_atTop
  · intro hf
    -- Proof comment: compose the shifted sequence with `PNat.natPred` to recover the original
    -- `ℕ+`-indexing.
    have hcomp := hf.comp OrderIso.pnatIsoNat.tendsto_atTop
    convert hcomp using 1
    ext n
    simp

/-- Helper for Exercise 13.2.11: near `0`, the remainder in the expansion
`Real.log (1 - u) = -u + O(u^2)` is bounded by `2 * u^2`. -/
private lemma logOneSub_add_abs_le_two_mul_sq {u : ℝ} (hu0 : 0 ≤ u) (hu : u < 1 / 2) :
    |Real.log (1 - u) + u| ≤ 2 * u ^ 2 := by
  -- Proof comment: instantiate the standard Taylor-remainder estimate with one term, then bound
  -- the denominator `1 - u` from below by `1 / 2`.
  have hu1 : |u| < 1 := by
    rw [abs_of_nonneg hu0]
    linarith
  have hbase := Real.abs_log_sub_add_sum_range_le (x := u) hu1 1
  have hbase' : |Real.log (1 - u) + u| ≤ u ^ 2 / (1 - u) := by
    simpa [abs_of_nonneg hu0, add_comm, add_left_comm, add_assoc, pow_two] using hbase
  have hhalf : (1 / 2 : ℝ) ≤ 1 - u := by
    linarith
  have hinv : (1 - u)⁻¹ ≤ 2 := by
    simpa using one_div_le_one_div_of_le (show (0 : ℝ) < 1 / 2 by norm_num) hhalf
  have hbound : u ^ 2 / (1 - u) ≤ 2 * u ^ 2 := by
    rw [div_eq_mul_inv]
    have hmul := mul_le_mul_of_nonneg_left hinv (sq_nonneg u)
    simpa [two_mul, mul_comm, mul_left_comm, mul_assoc] using hmul
  exact le_trans hbase' hbound

/-- Helper for Exercise 13.2.11: a bounded scaled product `mₙ qₙ` makes the logarithmic
remainder `mₙ * (log (1 - qₙ) + qₙ)` negligible when `qₙ → 0`. -/
private lemma tendsto_mul_logOneSub_add_of_boundedScaledRate
    (m q : ℕ → ℝ) (C : ℝ) (hq_zero : Tendsto q atTop (𝓝 0))
    (hq_nonneg : ∀ᶠ n : ℕ in atTop, 0 ≤ q n)
    (hq_half : ∀ᶠ n : ℕ in atTop, q n < 1 / 2)
    (hBound : ∀ᶠ n : ℕ in atTop, |m n * q n| ≤ C) :
    Tendsto (fun n : ℕ ↦ m n * (Real.log (1 - q n) + q n)) atTop (𝓝 0) := by
  -- Proof comment: first bound the logarithmic remainder by `2 * qₙ²`, then absorb one `qₙ`
  -- into the bounded scaled product `mₙ qₙ` and squeeze the absolute value to zero.
  rw [tendsto_zero_iff_abs_tendsto_zero]
  have hQuad : ∀ᶠ n : ℕ in atTop, |Real.log (1 - q n) + q n| ≤ 2 * (q n) ^ 2 := by
    filter_upwards [hq_nonneg, hq_half] with n hq0 hqhalf
    exact logOneSub_add_abs_le_two_mul_sq hq0 hqhalf
  have hAbsBound :
      ∀ᶠ n : ℕ in atTop, |m n * (Real.log (1 - q n) + q n)| ≤ |m n * q n| * |2 * q n| := by
    filter_upwards [hq_nonneg, hQuad] with n hq0 hn
    rw [abs_mul]
    have hq_abs : |q n| = q n := abs_of_nonneg hq0
    have h2q_abs : |2 * q n| = 2 * q n := abs_of_nonneg (by positivity)
    have hle : |Real.log (1 - q n) + q n| ≤ q n * (2 * q n) := by
      simpa [pow_two, mul_assoc, mul_left_comm, mul_comm] using hn
    calc
      |m n| * |Real.log (1 - q n) + q n| ≤ |m n| * (q n * (2 * q n)) :=
        mul_le_mul_of_nonneg_left hle (abs_nonneg _)
      _ = (|m n| * q n) * (2 * q n) := by ring
      _ = |m n * q n| * |2 * q n| := by
        rw [abs_mul, hq_abs, h2q_abs]
  have hQg0 : Tendsto (fun n : ℕ ↦ |2 * q n|) atTop (𝓝 0) := by
    have : Tendsto (fun n : ℕ ↦ 2 * q n) atTop (𝓝 (2 * 0)) :=
      (tendsto_const_nhds.mul hq_zero)
    simpa using this.abs
  have hBound' : ∀ᶠ n : ℕ in atTop, |(fun n : ℕ ↦ |m n * q n|) n| ≤ |C| := by
    filter_upwards [hBound] with n hn
    simpa [abs_abs] using hn.trans (le_abs_self C)
  have hprod0 : Tendsto (fun n : ℕ ↦ |m n * q n| * |2 * q n|) atTop (𝓝 0) :=
    bdd_le_mul_tendsto_zero' |C| hBound' hQg0
  exact squeeze_zero' (Eventually.of_forall fun _ ↦ abs_nonneg _) hAbsBound hprod0

/-- Helper for Exercise 13.2.11: for `u < 1 / 2`, the logarithmic decrement
`-log (1 - u)` dominates `u`. -/
private lemma self_le_neg_logOneSub {u : ℝ} (hu : u < 1 / 2) :
    u ≤ -Real.log (1 - u) := by
  -- Proof comment: apply the standard upper bound `log y ≤ y - 1` at `y = 1 - u`.
  have hpos : 0 < 1 - u := by linarith
  have hlog : Real.log (1 - u) ≤ -u := by
    simpa using (Real.log_le_sub_one_of_pos hpos)
  linarith

/-- Helper for Exercise 13.2.11: after shifting the `ℕ+`-indexed rate sequence to `ℕ`, the
geometric tail terms should converge to the exponential tail. -/
private lemma tendsto_scaledGeometricTail_of_rateLimitNat
    (α : ℝ) (p : ℕ+ → ℝ) (hp_pos : ∀ n, 0 < p n) (hp_lt_one : ∀ n, p n < 1)
    (hRate : Tendsto (fun n : ℕ ↦ (n + 1 : ℝ) * p (Nat.succPNat n)) atTop (𝓝 α))
    {x : ℝ} (hx : 0 ≤ x) :
    Tendsto (fun n : ℕ ↦ (1 - p (Nat.succPNat n)) ^ (Nat.floor (((n + 1 : ℝ) * x)) + 1))
      atTop (𝓝 (Real.exp (-(α * x)))) := by
  -- Proof comment: write the exponent as `mₙ = ⌊(n + 1) x⌋ + 1`, show that
  -- `mₙ / (n + 1) → x`, deduce `mₙ qₙ → α x`, and then exponentiate the logarithmic asymptotic.
  let q : ℕ → ℝ := fun n ↦ p (Nat.succPNat n)
  let N : ℕ → ℝ := fun n ↦ n + 1
  let mNat : ℕ → ℕ := fun n ↦ Nat.floor (N n * x) + 1
  let m : ℕ → ℝ := fun n ↦ mNat n
  let a : ℕ → ℝ := fun n ↦ m n / N n
  have hNAtTop : Tendsto N atTop atTop := by
    -- Proof comment: the shifted index `n + 1` still tends to infinity.
    simpa [N] using
      (tendsto_atTop_add_const_right atTop (1 : ℝ) tendsto_natCast_atTop_atTop)
  have hInv : Tendsto (fun n : ℕ ↦ 1 / N n) atTop (𝓝 0) := by
    -- Proof comment: reciprocals of `n + 1` vanish at infinity.
    simpa [N] using (tendsto_one_div_add_atTop_nhds_zero_nat : Tendsto (fun n : ℕ ↦ 1 / (n + 1 : ℝ)) atTop (𝓝 0))
  have hZero : Tendsto q atTop (𝓝 0) := by
    -- Proof comment: divide the convergent scaled rates by `n + 1`.
    have hProd :
        Tendsto (fun n : ℕ ↦ (N n * q n) * (1 / N n)) atTop (𝓝 0) := by
      simpa using hRate.mul hInv
    convert hProd using 1
    ext n
    field_simp [N]
  have hHalf : ∀ᶠ n : ℕ in atTop, q n < 1 / 2 := by
    -- Proof comment: once `qₙ → 0`, the Taylor neighborhood `qₙ < 1 / 2` is eventually valid.
    simpa [q] using hZero.eventually (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2))
  have hNonneg : ∀ᶠ n : ℕ in atTop, 0 ≤ q n := by
    -- Proof comment: positivity of the geometric parameter gives nonnegativity on every index.
    exact Eventually.of_forall fun n ↦ (hp_pos (Nat.succPNat n)).le
  have hFloorRatio :
      Tendsto (fun n : ℕ ↦ ((Nat.floor (N n * x) : ℕ) : ℝ) / N n) atTop (𝓝 x) := by
    -- Proof comment: `⌊(n + 1) x⌋ / (n + 1)` has the same limit `x` as the exact ratio.
    simpa [N, mul_comm] using (tendsto_nat_floor_mul_div_atTop hx).comp hNAtTop
  have hRatio :
      Tendsto a atTop (𝓝 x) := by
    -- Proof comment: adding the negligible correction `1 / (n + 1)` converts the floor ratio into
    -- `mₙ / (n + 1)`.
    have hEq :
        a = fun n : ℕ ↦ ((Nat.floor (N n * x) : ℕ) : ℝ) / N n + 1 / N n := by
      funext n
      simp [a, m, mNat, N, add_div]
    rw [hEq]
    simpa using hFloorRatio.add hInv
  have hScaled :
      Tendsto (fun n : ℕ ↦ m n * q n) atTop (𝓝 (α * x)) := by
    -- Proof comment: multiply the convergent rate `(n + 1) qₙ` by the convergent ratio
    -- `mₙ / (n + 1)`.
    have hEq :
        (fun n : ℕ ↦ m n * q n) = fun n : ℕ ↦ a n * (N n * q n) := by
      funext n
      calc
        m n * q n = (m n / N n) * (N n * q n) := by
          field_simp [N]
        _ = a n * (N n * q n) := by
          simp [a]
    rw [hEq]
    simpa [mul_comm, mul_left_comm, mul_assoc] using hRatio.mul hRate
  have hScaledBound :
      ∀ᶠ n : ℕ in atTop, |m n * q n| ≤ |α * x| + 1 := by
    -- Proof comment: the convergent scaled sequence `mₙ qₙ` is eventually bounded.
    have hNear :
        ∀ᶠ n : ℕ in atTop, |m n * q n - α * x| < 1 := by
      exact hScaled.eventually (Metric.ball_mem_nhds (α * x) (by norm_num))
    filter_upwards [hNear] with n hn
    have htriangle :
        |m n * q n| ≤ |m n * q n - α * x| + |α * x| := by
      calc
        |m n * q n| = |(m n * q n - α * x) + α * x| := by ring_nf
        _ ≤ |m n * q n - α * x| + |α * x| := abs_add_le _ _
    have hle : |m n * q n - α * x| + |α * x| ≤ |α * x| + 1 := by
      linarith [le_of_lt hn]
    exact htriangle.trans hle
  have hRemainder :
      Tendsto (fun n : ℕ ↦ m n * (Real.log (1 - q n) + q n)) atTop (𝓝 0) :=
    tendsto_mul_logOneSub_add_of_boundedScaledRate m q (|α * x| + 1) hZero hNonneg hHalf
      hScaledBound
  have hScaledLog :
      Tendsto (fun n : ℕ ↦ m n * Real.log (1 - q n)) atTop (𝓝 (-(α * x))) := by
    -- Proof comment: the quadratic remainder is negligible, so the logarithmic exponent has limit
    -- `-(α x)`.
    have hEq :
        (fun n : ℕ ↦ m n * Real.log (1 - q n)) =
          (fun n : ℕ ↦ m n * (Real.log (1 - q n) + q n) - m n * q n) := by
      funext n
      ring
    rw [hEq]
    simpa using hRemainder.sub hScaled
  have hExp :
      Tendsto (fun n : ℕ ↦ Real.exp (m n * Real.log (1 - q n))) atTop
        (𝓝 (Real.exp (-(α * x)))) :=
    Real.continuous_exp.continuousAt.tendsto.comp hScaledLog
  have hEqExp :
      (fun n : ℕ ↦ (1 - q n) ^ mNat n) = fun n : ℕ ↦ Real.exp (m n * Real.log (1 - q n)) := by
    -- Proof comment: rewrite the natural power using `exp (log (1 - qₙ))`.
    funext n
    have hpos : 0 < 1 - q n := sub_pos.2 (hp_lt_one (Nat.succPNat n))
    rw [← Real.exp_log hpos, ← Real.exp_nat_mul]
    congr 1
    simp [m, mNat, mul_comm]
  have hTargetEq :
      (fun n : ℕ ↦ (1 - p (Nat.succPNat n)) ^ (Nat.floor (((n + 1 : ℝ) * x)) + 1)) =
        (fun n : ℕ ↦ (1 - q n) ^ mNat n) := by
    funext n
    simp [q, N, mNat]
  rw [hTargetEq, hEqExp]
  exact hExp

/-- Helper for Exercise 13.2.11: once the shifted success probabilities vanish and the unit-step
geometric tails converge to `exp (-α)`, the shifted rates converge to `α`. -/
private lemma rateLimit_of_zeroMass_and_unitTailNat
    (α : ℝ) (p : ℕ+ → ℝ) (hp_pos : ∀ n, 0 < p n) (hp_lt_one : ∀ n, p n < 1)
    (hZero : Tendsto (fun n : ℕ ↦ p (Nat.succPNat n)) atTop (𝓝 0))
    (hUnitTail :
      Tendsto (fun n : ℕ ↦ (1 - p (Nat.succPNat n)) ^ (n + 2)) atTop
        (𝓝 (Real.exp (-α)))) :
    Tendsto (fun n : ℕ ↦ (n + 1 : ℝ) * p (Nat.succPNat n)) atTop (𝓝 α) := by
  -- Proof comment: take logarithms of the convergent tail, convert the logarithm back to the
  -- linear term `-(n + 2) * pₙ` using the quadratic remainder estimate, and then subtract the
  -- already-known `pₙ → 0`.
  let q : ℕ → ℝ := fun n ↦ p (Nat.succPNat n)
  let m : ℕ → ℝ := fun n ↦ n + 2
  have hHalf : ∀ᶠ n : ℕ in atTop, q n < 1 / 2 := by
    -- Proof comment: the success probabilities vanish, so eventually they lie in the Taylor
    -- neighborhood where the logarithmic remainder estimate is valid.
    simpa [q] using hZero.eventually (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2))
  have hNonneg : ∀ᶠ n : ℕ in atTop, 0 ≤ q n := by
    -- Proof comment: positivity of the geometric parameter gives nonnegativity on every index.
    exact Eventually.of_forall fun n ↦ (hp_pos (Nat.succPNat n)).le
  have hLogTail :
      Tendsto (fun n : ℕ ↦ Real.log ((1 - q n) ^ (n + 2))) atTop (𝓝 (-α)) := by
    -- Proof comment: the logarithm is continuous at the positive limit `exp (-α)`.
    simpa [Real.log_exp] using hUnitTail.log (Real.exp_ne_zero (-α))
  have hScaledLog :
      Tendsto (fun n : ℕ ↦ m n * Real.log (1 - q n)) atTop (𝓝 (-α)) := by
    -- Proof comment: rewrite `log ((1 - qₙ)^(n+2))` as `(n + 2) * log (1 - qₙ)`.
    simpa [m, q, Real.log_pow, mul_comm] using hLogTail
  have hScaledLogBound :
      ∀ᶠ n : ℕ in atTop, |m n * Real.log (1 - q n)| ≤ |α| + 1 := by
    -- Proof comment: every convergent real sequence is eventually bounded.
    have hNear :
        ∀ᶠ n : ℕ in atTop, |m n * Real.log (1 - q n) - (-α)| < 1 := by
      exact hScaledLog.eventually (Metric.ball_mem_nhds (-α) (by norm_num))
    filter_upwards [hNear] with n hn
    have htriangle :
        |m n * Real.log (1 - q n)| ≤ |m n * Real.log (1 - q n) - (-α)| + |-α| := by
      calc
        |m n * Real.log (1 - q n)|
            = |(m n * Real.log (1 - q n) - (-α)) + (-α)| := by ring_nf
        _ ≤ |m n * Real.log (1 - q n) - (-α)| + |-α| := abs_add_le _ _
    have hle : |m n * Real.log (1 - q n) - (-α)| + |-α| ≤ |α| + 1 := by
      have hle' : |m n * Real.log (1 - q n) - (-α)| ≤ 1 := le_of_lt hn
      have habsα : |-α| = |α| := abs_neg α
      linarith
    exact htriangle.trans hle
  have hScaledBound :
      ∀ᶠ n : ℕ in atTop, |m n * q n| ≤ |α| + 1 := by
    -- Proof comment: for small `qₙ`, the quantity `-log (1 - qₙ)` dominates `qₙ`, so the bounded
    -- logarithmic scale controls the boundedness of `(n + 2) * qₙ`.
    filter_upwards [hHalf, hScaledLogBound] with n hqhalf hlogbound
    have hq0 : 0 ≤ q n := (hp_pos (Nat.succPNat n)).le
    have hm_nonneg : 0 ≤ m n := by positivity
    have hq_le : q n ≤ -Real.log (1 - q n) := self_le_neg_logOneSub hqhalf
    have hlog_nonneg : 0 ≤ -Real.log (1 - q n) := by
      linarith
    have hmul_le : m n * q n ≤ -(m n * Real.log (1 - q n)) := by
      have := mul_le_mul_of_nonneg_left hq_le hm_nonneg
      simpa [m, mul_comm, mul_left_comm, mul_assoc] using this
    have habs_log :
        |m n * Real.log (1 - q n)| = -(m n * Real.log (1 - q n)) := by
      have hnonpos : m n * Real.log (1 - q n) ≤ 0 := by
        have hlog_le_zero : Real.log (1 - q n) ≤ 0 := by
          have hpos : 0 < 1 - q n := sub_pos.2 (hp_lt_one (Nat.succPNat n))
          have hle_one : 1 - q n ≤ 1 := by linarith
          exact Real.log_nonpos hpos.le hle_one
        exact mul_nonpos_of_nonneg_of_nonpos hm_nonneg hlog_le_zero
      exact abs_of_nonpos hnonpos
    have habs_q : |m n * q n| = m n * q n := abs_of_nonneg (mul_nonneg hm_nonneg hq0)
    rw [habs_q]
    exact hmul_le.trans (by simpa [habs_log] using hlogbound)
  have hRemainder :
      Tendsto (fun n : ℕ ↦ m n * (Real.log (1 - q n) + q n)) atTop (𝓝 0) :=
    tendsto_mul_logOneSub_add_of_boundedScaledRate m q (|α| + 1) hZero hNonneg hHalf hScaledBound
  have hRateTwo :
      Tendsto (fun n : ℕ ↦ m n * q n) atTop (𝓝 α) := by
    -- Proof comment: the remainder tends to zero, so `mₙ qₙ` and `-mₙ log (1 - qₙ)` have the
    -- same limit.
    have hEq :
        (fun n : ℕ ↦ m n * q n) =
          (fun n : ℕ ↦ m n * (Real.log (1 - q n) + q n) - m n * Real.log (1 - q n)) := by
      funext n
      ring
    rw [hEq]
    simpa using hRemainder.sub hScaledLog
  have hFinalEq :
      (fun n : ℕ ↦ (n + 1 : ℝ) * q n) =
        (fun n : ℕ ↦ m n * q n - q n) := by
    -- Proof comment: split off one copy of `qₙ` from `(n + 2) * qₙ`.
    funext n
    simp [m]
    ring
  rw [hFinalEq]
  simpa [q] using hRateTwo.sub hZero

/-- Exercise 13.2.11: the laws of the scaled geometric variables `Xₙ / n` converge weakly to the
exponential distribution with rate `α` exactly when the success probabilities satisfy
`n * pₙ → α`. -/
-- Proof sketch: view the law of `Xₙ / n` directly as the pushforward of the geometric
-- probability measure under `k ↦ k / n`, compute the associated distribution functions from the
-- explicit geometric and exponential formulas, and use the limit
-- `(1 - pₙ)^(n x) → exp (-α * x)` to show that weak convergence is equivalent to
-- `n * pₙ → α`.
theorem scaled_geometric_law_tendsto_expMeasure_iff
    (α : ℝ) (hα : 0 < α) (p : ℕ+ → ℝ) (hp_pos : ∀ n, 0 < p n)
    (hp_lt_one : ∀ n, p n < 1) :
    Tendsto
      (fun n ↦
        scaledGeometricProbabilityMeasure p hp_pos hp_lt_one n)
      atTop
      (𝓝 (expProbabilityMeasure α hα)) ↔
    Tendsto (fun n : ℕ+ ↦ (n : ℝ) * p n) atTop (𝓝 α) := by
  -- Route correction: the proof should now pass through the explicit cdf formulas already proved
  -- above instead of unfolding the pushed-forward measure directly inside the main theorem.
  let νs : ℕ → ProbabilityMeasure ℝ :=
    fun n ↦ scaledGeometricProbabilityMeasure p hp_pos hp_lt_one (Nat.succPNat n)
  let ν : ProbabilityMeasure ℝ := expProbabilityMeasure α hα
  have hweakNat_iff :
      Tendsto νs atTop (𝓝 ν) ↔
        ∀ x : ℝ,
          ContinuousAt (cdf ((ν : ProbabilityMeasure ℝ) : Measure ℝ)) x →
            Tendsto (fun n ↦ cdf ((νs n : ProbabilityMeasure ℝ) : Measure ℝ) x) atTop
              (𝓝 (cdf ((ν : ProbabilityMeasure ℝ) : Measure ℝ) x)) :=
    probabilityMeasure_tendsto_iff_cdf_tendsto
  constructor
  · intro hWeak
    have hWeakNat : Tendsto νs atTop (𝓝 ν) := by
      -- Proof comment: transport the weak convergence statement to the shifted `ℕ` indexing.
      simpa [νs, ν] using
        (tendsto_pnat_atTop_iff_succPNat
          (f := fun n ↦ scaledGeometricProbabilityMeasure p hp_pos hp_lt_one n)
          (l := 𝓝 (expProbabilityMeasure α hα))).1 hWeak
    have hν_zero : cdf ((ν : ProbabilityMeasure ℝ) : Measure ℝ) 0 = 0 := by
      simpa [ν] using expProbabilityMeasure_cdf_eq_max α hα 0
    have hν_one : cdf ((ν : ProbabilityMeasure ℝ) : Measure ℝ) 1 = 1 - Real.exp (-α) := by
      simpa [ν] using expProbabilityMeasure_cdf_eq_max α hα 1
    have hcdf := hweakNat_iff.1 hWeakNat
    have hZero :
        Tendsto (fun n : ℕ ↦ p (Nat.succPNat n)) atTop (𝓝 0) := by
      -- Proof comment: evaluate the converging cdfs at the continuity point `0`.
      have hzeroCdf :=
        hcdf 0 (by simpa [ν] using continuousAt_expProbabilityMeasure_cdf α hα 0)
      have hzeroCdf' :
          Tendsto (fun n : ℕ ↦ p (Nat.succPNat n)) atTop
            (𝓝 (cdf ((ν : ProbabilityMeasure ℝ) : Measure ℝ) 0)) := by
        simpa [νs, scaledGeometric_cdf_zero] using hzeroCdf
      simpa [hν_zero] using hzeroCdf'
    have hUnitTail :
        Tendsto (fun n : ℕ ↦ (1 - p (Nat.succPNat n)) ^ (n + 2)) atTop (𝓝 (Real.exp (-α))) := by
      -- Proof comment: evaluate at `1`, then subtract the cdf from `1` to isolate the geometric
      -- tail term.
      have honeCdf :=
        hcdf 1 (by simpa [ν] using continuousAt_expProbabilityMeasure_cdf α hα 1)
      have htailCdf :
          Tendsto
            (fun n : ℕ ↦ 1 - cdf ((νs n : ProbabilityMeasure ℝ) : Measure ℝ) 1)
            atTop
            (𝓝 (1 - cdf ((ν : ProbabilityMeasure ℝ) : Measure ℝ) 1)) :=
        tendsto_const_nhds.sub honeCdf
      have htailCdf' :
          Tendsto
            (fun n : ℕ ↦ (1 - p (Nat.succPNat n)) ^ (n + 2))
            atTop
            (𝓝 (1 - cdf ((ν : ProbabilityMeasure ℝ) : Measure ℝ) 1)) := by
        simpa [νs, scaledGeometric_cdf_one] using htailCdf
      simpa [hν_one] using htailCdf'
    have hRateNat :=
      rateLimit_of_zeroMass_and_unitTailNat α p hp_pos hp_lt_one hZero hUnitTail
    exact
      (tendsto_pnat_atTop_iff_succPNat
        (f := fun n : ℕ+ ↦ (n : ℝ) * p n) (l := 𝓝 α)).2
        (by simpa using hRateNat)
  · intro hRate
    have hRateNat :
        Tendsto (fun n : ℕ ↦ (n + 1 : ℝ) * p (Nat.succPNat n)) atTop (𝓝 α) := by
      -- Proof comment: switch from the positive-natural index to the ordinary natural index.
      simpa using
        (tendsto_pnat_atTop_iff_succPNat
          (f := fun n : ℕ+ ↦ (n : ℝ) * p n) (l := 𝓝 α)).1 hRate
    have hcdf :
        ∀ x : ℝ,
          ContinuousAt (cdf ((ν : ProbabilityMeasure ℝ) : Measure ℝ)) x →
            Tendsto (fun n ↦ cdf ((νs n : ProbabilityMeasure ℝ) : Measure ℝ) x) atTop
              (𝓝 (cdf ((ν : ProbabilityMeasure ℝ) : Measure ℝ) x)) := by
      intro x hx_cont
      by_cases hx_neg : x < 0
      · -- Proof comment: for negative thresholds both the scaled geometric and exponential cdfs
        -- are already identically zero.
        have hsrc :
            (fun n : ℕ ↦ cdf ((νs n : ProbabilityMeasure ℝ) : Measure ℝ) x) =
              fun _ : ℕ ↦ 0 := by
          funext n
          simp [νs, scaledGeometric_cdf_eq, hx_neg]
        have htarget : cdf ((ν : ProbabilityMeasure ℝ) : Measure ℝ) x = 0 := by
          simpa [ν, hx_neg, max_eq_right (le_of_lt hx_neg)] using
            expProbabilityMeasure_cdf_eq_max α hα x
        simpa [hsrc, htarget] using
          (tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ (0 : ℝ)) atTop (𝓝 0))
      · have hx_nonneg : 0 ≤ x := le_of_not_gt hx_neg
        have htail :
            Tendsto
              (fun n : ℕ ↦
                (1 - p (Nat.succPNat n)) ^ (Nat.floor (((n + 1 : ℝ) * x)) + 1))
              atTop (𝓝 (Real.exp (-(α * x)))) :=
          tendsto_scaledGeometricTail_of_rateLimitNat α p hp_pos hp_lt_one hRateNat hx_nonneg
        have hsrc :
            (fun n : ℕ ↦ cdf ((νs n : ProbabilityMeasure ℝ) : Measure ℝ) x) =
              (fun n : ℕ ↦
                1 - (1 - p (Nat.succPNat n)) ^ (Nat.floor (((n + 1 : ℝ) * x)) + 1)) := by
          funext n
          simp [νs, scaledGeometric_cdf_eq, hx_neg]
        have htarget :
            cdf ((ν : ProbabilityMeasure ℝ) : Measure ℝ) x = 1 - Real.exp (-(α * x)) := by
          simpa [ν, hx_nonneg, max_eq_left hx_nonneg] using
            expProbabilityMeasure_cdf_eq_max α hα x
        simpa [hsrc, htarget] using (tendsto_const_nhds.sub htail)
    have hWeakNat : Tendsto νs atTop (𝓝 ν) := hweakNat_iff.2 hcdf
    simpa [νs, ν] using
      (tendsto_pnat_atTop_iff_succPNat
        (f := fun n ↦ scaledGeometricProbabilityMeasure p hp_pos hp_lt_one n)
        (l := 𝓝 (expProbabilityMeasure α hα))).2 hWeakNat
