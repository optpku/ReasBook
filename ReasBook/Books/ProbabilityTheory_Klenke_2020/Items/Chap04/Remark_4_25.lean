/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory Set Filter
open scoped Topology

/-- Helper for Remark 4.25: on finite intervals `[0, b]`, integration by parts rewrites
`∫ x in 0..b, sin x / (1 + x)` into a boundary term and an absolutely integrable remainder. -/
lemma intervalIntegral_sineDecay_eq_boundary_sub_cosRemainder {b : ℝ} (hb : 0 ≤ b) :
    ∫ x in (0 : ℝ)..b, Real.sin x / (1 + x)
      = 1 - Real.cos b / (1 + b) - ∫ x in (0 : ℝ)..b, Real.cos x / (1 + x)^2 := by
  have hu :
      ∀ x ∈ uIcc (0 : ℝ) b, HasDerivAt (fun y : ℝ ↦ (1 + y)⁻¹) (-((1 + x)^2)⁻¹) x := by
    intro x hx
    have hx' : x ∈ Icc (0 : ℝ) b := by
      simpa [uIcc_of_le hb] using hx
    have hx_ne : 1 + x ≠ 0 := by
      have hx_nonneg : 0 ≤ x := hx'.1
      nlinarith
    -- Differentiate the decay factor on `[0, b]`, where the denominator stays positive.
    simpa [pow_two, div_eq_mul_inv] using (((hasDerivAt_id x).const_add 1).inv hx_ne)
  have hv :
      ∀ x ∈ uIcc (0 : ℝ) b, HasDerivAt (fun y : ℝ ↦ -Real.cos y) (Real.sin x) x := by
    intro x hx
    -- Use `-cos` as a primitive of `sin`.
    simpa using (Real.hasDerivAt_cos x).neg
  have hu' : IntervalIntegrable (fun x : ℝ ↦ -((1 + x)^2)⁻¹) volume (0 : ℝ) b := by
    -- The derivative of the decay factor is continuous on `[0, b]`.
    have h_cont : ContinuousOn (fun x : ℝ ↦ -((1 + x)^2)⁻¹) (uIcc (0 : ℝ) b) := by
      intro x hx
      have hx' : x ∈ Icc (0 : ℝ) b := by
        simpa [uIcc_of_le hb] using hx
      have hx_pos : 0 < 1 + x := by
        linarith [hx'.1]
      have h_inv :
          ContinuousWithinAt (fun y : ℝ ↦ ((1 + y)^2)⁻¹) (uIcc (0 : ℝ) b) x := by
        exact (((continuous_const.add continuous_id).pow 2).continuousWithinAt.inv₀
          (pow_ne_zero 2 hx_pos.ne'))
      simpa using h_inv.neg
    exact h_cont.intervalIntegrable
  have hv' : IntervalIntegrable (fun x : ℝ ↦ Real.sin x) volume (0 : ℝ) b := by
    exact Continuous.intervalIntegrable (by fun_prop) _ _
  calc
    ∫ x in (0 : ℝ)..b, Real.sin x / (1 + x)
      = ∫ x in (0 : ℝ)..b, (fun x : ℝ ↦ (1 + x)⁻¹) x * (fun x : ℝ ↦ Real.sin x) x := by
          -- Rewrite the integrand into the `u * v'` shape required for integration by parts.
          refine intervalIntegral.integral_congr ?_
          intro x hx
          simp [div_eq_mul_inv, mul_comm]
    _ = (fun x : ℝ ↦ (1 + x)⁻¹) b * (fun x : ℝ ↦ -Real.cos x) b
          - (fun x : ℝ ↦ (1 + x)⁻¹) 0 * (fun x : ℝ ↦ -Real.cos x) 0
          - ∫ x in (0 : ℝ)..b, (fun x : ℝ ↦ -((1 + x)^2)⁻¹) x * (fun x : ℝ ↦ -Real.cos x) x := by
          -- Apply finite-interval integration by parts.
          exact intervalIntegral.integral_mul_deriv_eq_deriv_mul hu hv hu' hv'
    _ = 1 - Real.cos b / (1 + b) - ∫ x in (0 : ℝ)..b, Real.cos x / (1 + x)^2 := by
          -- Normalize the boundary term and the remainder back to the desired form.
          congr 1
          · simpa [div_eq_mul_inv, sub_eq_add_neg, mul_comm] using
              add_comm (-((1 + b)⁻¹ * Real.cos b)) (1 : ℝ)
          · refine intervalIntegral.integral_congr ?_
            intro x hx
            ring

/-- Helper for Remark 4.25: the remainder `x ↦ cos x / (1 + x)^2` is Lebesgue integrable on
`(0, ∞)`. -/
lemma integrableOn_cos_div_oneAdd_sq_Ioi :
    IntegrableOn (fun x : ℝ ↦ Real.cos x / (1 + x)^2) (Ioi (0 : ℝ)) := by
  have h_decay_rpow :
      IntegrableOn (fun x : ℝ ↦ (1 + x) ^ (-2 : ℝ)) (Ioi (0 : ℝ)) := by
    -- The square decay is an `L¹` function on `(0, ∞)`.
    simpa [add_comm] using
      (integrableOn_add_rpow_Ioi_of_lt (a := (-2 : ℝ)) (c := (0 : ℝ)) (m := (1 : ℝ))
        (by norm_num) (by linarith : -(1 : ℝ) < 0))
  have h_decay :
      IntegrableOn (fun x : ℝ ↦ ((1 + x)^2)⁻¹) (Ioi (0 : ℝ)) := by
    refine h_decay_rpow.congr_fun ?_ measurableSet_Ioi
    intro x hx
    have hx_pos : 0 < 1 + x := by
      have hx0 : 0 < x := hx
      nlinarith
    simpa [show (-2 : ℝ) = -(2 : ℝ) by norm_num, Real.rpow_neg (le_of_lt hx_pos),
      Real.rpow_natCast, one_div]
  rw [IntegrableOn] at h_decay ⊢
  refine Integrable.mono' h_decay ?_ ?_
  · -- The remainder is continuous on `(0, ∞)`, hence strongly measurable for the restricted measure.
    have h_cont : ContinuousOn (fun x : ℝ ↦ Real.cos x / (1 + x)^2) (Ioi (0 : ℝ)) := by
      intro x hx
      have hx_pos : 0 < 1 + x := by
        have hx0 : 0 < x := hx
        nlinarith
      exact Real.continuous_cos.continuousWithinAt.div
        (((continuous_const.add continuous_id).pow 2).continuousWithinAt)
        (pow_ne_zero 2 hx_pos.ne')
    exact h_cont.aestronglyMeasurable measurableSet_Ioi
  · -- Bound the oscillatory remainder by the integrable envelope `(1 + x)⁻²`.
    refine (ae_restrict_iff' measurableSet_Ioi).2 <| Filter.Eventually.of_forall ?_
    intro x hx
    have hx_pos : 0 < 1 + x := by
      have hx0 : 0 < x := hx
      nlinarith
    have hsq_pos : 0 < (1 + x)^2 := by
      positivity
    calc
      ‖Real.cos x / (1 + x)^2‖ = |Real.cos x| / (1 + x)^2 := by
        rw [Real.norm_eq_abs, abs_div, abs_of_pos hsq_pos]
      _ ≤ 1 / (1 + x)^2 := by
        exact div_le_div_of_nonneg_right (Real.abs_cos_le_one x) (by positivity)
      _ = ((1 + x)^2)⁻¹ := by
        rw [one_div]

/-- Helper for Remark 4.25: the improper Riemann integrals
`∫ x in 0..b, sin x / (1 + x)` converge as `b → ∞`. -/
lemma tendsto_intervalIntegral_sineDecay_atTop :
    Tendsto
      (fun b : ℝ ↦ ∫ x in (0 : ℝ)..b, Real.sin x / (1 + x))
      atTop
      (𝓝 (1 - ∫ x in Ioi (0 : ℝ), Real.cos x / (1 + x)^2)) := by
  have h_boundary :
      Tendsto (fun b : ℝ ↦ Real.cos b / (1 + b)) atTop (𝓝 0) := by
    have h_inv : Tendsto (fun b : ℝ ↦ (1 + b)⁻¹) atTop (𝓝 0) := by
      have h_add : Tendsto (fun b : ℝ ↦ (1 : ℝ) + b) atTop atTop := by
        exact tendsto_atTop_add_const_left atTop (1 : ℝ) tendsto_id
      simpa using Tendsto.inv_tendsto_atTop h_add
    -- The boundary term vanishes because `cos` is bounded while `(1 + b)⁻¹ → 0`.
    refine squeeze_zero_norm' ?_ h_inv
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with b hb
    have hb_pos : 0 < 1 + b := by
      linarith
    calc
      ‖Real.cos b / (1 + b)‖ = |Real.cos b| / (1 + b) := by
        rw [Real.norm_eq_abs, abs_div, abs_of_pos hb_pos]
      _ ≤ 1 / (1 + b) := by
        exact div_le_div_of_nonneg_right (Real.abs_cos_le_one b) (by positivity)
      _ = (1 + b)⁻¹ := by
        rw [one_div]
  have h_remainder :
      Tendsto
        (fun b : ℝ ↦ ∫ x in (0 : ℝ)..b, Real.cos x / (1 + x)^2)
        atTop
        (𝓝 (∫ x in Ioi (0 : ℝ), Real.cos x / (1 + x)^2)) := by
    -- Pass the remainder term to the improper Lebesgue integral on `(0, ∞)`.
    exact MeasureTheory.intervalIntegral_tendsto_integral_Ioi 0
      integrableOn_cos_div_oneAdd_sq_Ioi tendsto_id
  have h_eventual :
      (fun b : ℝ ↦ 1 - Real.cos b / (1 + b) - ∫ x in (0 : ℝ)..b, Real.cos x / (1 + x)^2)
        =ᶠ[atTop]
      (fun b : ℝ ↦ ∫ x in (0 : ℝ)..b, Real.sin x / (1 + x)) := by
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with b hb
    symm
    exact intervalIntegral_sineDecay_eq_boundary_sub_cosRemainder hb
  refine Tendsto.congr' h_eventual ?_
  -- Combine the integration-by-parts formula with the two limiting pieces.
  have h_one : Tendsto (fun _ : ℝ ↦ (1 : ℝ)) atTop (𝓝 1) := tendsto_const_nhds
  simpa using ((h_one.sub h_boundary).sub h_remainder)

/-- Helper for Remark 4.25: each interval of length `π` contains the same total mass of `|sin|`. -/
lemma absSin_intervalIntegral_natMulPi (n : ℕ) :
    ∫ x in ((n : ℝ) * Real.pi)..((((n + 1 : ℕ) : ℝ)) * Real.pi), |Real.sin x| = 2 := by
  have h_periodic : Function.Periodic (fun x : ℝ ↦ |Real.sin x|) Real.pi := by
    intro x
    simpa [abs_neg] using congrArg abs (Real.sin_add_pi x)
  calc
    ∫ x in ((n : ℝ) * Real.pi)..((((n + 1 : ℕ) : ℝ)) * Real.pi), |Real.sin x|
      = ∫ x in (0 : ℝ)..Real.pi, |Real.sin x| := by
          -- Translate the interval back to `[0, π]` using the `π`-periodicity of `|sin|`.
          have h_endpoint :
              ((((n + 1 : ℕ) : ℝ)) * Real.pi) = (n : ℝ) * Real.pi + Real.pi := by
            calc
              ((((n + 1 : ℕ) : ℝ)) * Real.pi) = (((n : ℝ) + 1) * Real.pi) := by norm_num
              _ = (n : ℝ) * Real.pi + Real.pi := by ring
          rw [h_endpoint]
          simpa using h_periodic.intervalIntegral_add_eq ((n : ℝ) * Real.pi) 0
    _ = ∫ x in (0 : ℝ)..Real.pi, Real.sin x := by
          -- On `[0, π]`, the sine is nonnegative, so the absolute value disappears.
          refine intervalIntegral.integral_congr ?_
          intro x hx
          have hx' : x ∈ Icc (0 : ℝ) Real.pi := by
            simpa [uIcc_of_le Real.pi_pos.le] using hx
          exact abs_of_nonneg (Real.sin_nonneg_of_mem_Icc hx')
    _ = 2 := by
          have h_int :
              ∫ x in (0 : ℝ)..Real.pi, Real.sin x = 1 - (-1 : ℝ) := by
            simpa [Real.cos_zero, Real.cos_pi] using (integral_sin (a := (0 : ℝ)) (b := Real.pi))
          nlinarith

/-- Helper for Remark 4.25: the absolute-value integrand is continuous on `[0, ∞)`. -/
lemma continuousOn_absSineDecay_Ici :
    ContinuousOn (fun x : ℝ ↦ |Real.sin x / (1 + x)|) (Ici (0 : ℝ)) := by
  intro x hx
  have hx_pos : 0 < 1 + x := by
    have hx_nonneg : 0 ≤ x := hx
    linarith
  have h_div :
      ContinuousWithinAt (fun y : ℝ ↦ Real.sin y / (1 + y)) (Ici (0 : ℝ)) x := by
    exact Real.continuous_sin.continuousWithinAt.div
      ((continuous_const.add continuous_id).continuousWithinAt) hx_pos.ne'
  exact h_div.abs

/-- Helper for Remark 4.25: the absolute-value integrand is interval integrable on every block
`[n * π, (n + 1) * π]`. -/
lemma absSineDecay_block_intervalIntegrable (n : ℕ) :
    IntervalIntegrable
      (fun x : ℝ ↦ |Real.sin x / (1 + x)|)
      volume
      ((n : ℝ) * Real.pi)
      ((((n + 1 : ℕ) : ℝ)) * Real.pi) := by
  -- Continuity on `[0, ∞)` gives integrability on each positive `π`-block.
  have h_block :
      ((n : ℝ) * Real.pi) ≤ ((((n + 1 : ℕ) : ℝ)) * Real.pi) := by
    have h_cast : (n : ℝ) ≤ (((n + 1 : ℕ) : ℝ)) := by
      exact_mod_cast Nat.le_succ n
    exact mul_le_mul_of_nonneg_right h_cast Real.pi_pos.le
  refine ContinuousOn.intervalIntegrable <|
    continuousOn_absSineDecay_Ici.mono ?_
  intro x hx
  have h_block' : ((n : ℝ) * Real.pi) ≤ (((n : ℝ) + 1) * Real.pi) := by
    have h_cast' : (n : ℝ) ≤ (n : ℝ) + 1 := by linarith
    exact mul_le_mul_of_nonneg_right h_cast' Real.pi_pos.le
  have hx_cast : x ∈ uIcc ((n : ℝ) * Real.pi) (((n : ℝ) + 1) * Real.pi) := by
    simpa [Nat.cast_add, add_mul, one_mul, add_assoc, add_left_comm, add_comm] using hx
  have hx' : x ∈ Icc ((n : ℝ) * Real.pi) (((n : ℝ) + 1) * Real.pi) := by
    rwa [uIcc_of_le h_block'] at hx_cast
  have hnpi_nonneg : 0 ≤ (n : ℝ) * Real.pi := by
    positivity
  exact hnpi_nonneg.trans hx'.1

/-- Helper for Remark 4.25: each block `[n * π, (n + 1) * π]` contributes at least a harmonic-size
amount to the integral of `|sin x / (1 + x)|`. -/
lemma absSineDecay_block_lower (n : ℕ) :
    (2 / (1 + Real.pi)) * (1 / (n + 1 : ℝ))
      ≤ ∫ x in ((n : ℝ) * Real.pi)..((((n + 1 : ℕ) : ℝ)) * Real.pi),
          |Real.sin x / (1 + x)| := by
  let c : ℝ := (1 + ((((n + 1 : ℕ) : ℝ)) * Real.pi))⁻¹
  have h_block :
      ((n : ℝ) * Real.pi) ≤ ((((n + 1 : ℕ) : ℝ)) * Real.pi) := by
    have h_cast : (n : ℝ) ≤ (((n + 1 : ℕ) : ℝ)) := by
      exact_mod_cast Nat.le_succ n
    exact mul_le_mul_of_nonneg_right h_cast Real.pi_pos.le
  have h_compare :
      ∫ x in ((n : ℝ) * Real.pi)..((((n + 1 : ℕ) : ℝ)) * Real.pi), c * |Real.sin x|
        ≤ ∫ x in ((n : ℝ) * Real.pi)..((((n + 1 : ℕ) : ℝ)) * Real.pi),
            |Real.sin x / (1 + x)| := by
    refine intervalIntegral.integral_mono_on h_block ?_ ?_ ?_
    · exact Continuous.intervalIntegrable (by fun_prop) _ _
    · exact absSineDecay_block_intervalIntegrable n
    · intro x hx
      have hx' : x ∈ Icc ((n : ℝ) * Real.pi) ((((n + 1 : ℕ) : ℝ)) * Real.pi) := by
        simpa [uIcc_of_le h_block] using hx
      have hx_upper : x ≤ (((n + 1 : ℕ) : ℝ) * Real.pi) := by
        exact hx'.2
      have hx_pos : 0 < 1 + x := by
        have hnpi_nonneg : 0 ≤ (n : ℝ) * Real.pi := by
          nlinarith [Real.pi_pos]
        nlinarith [hnpi_nonneg.trans hx'.1]
      have hc_pos : 0 < 1 + (((n + 1 : ℕ) : ℝ) * Real.pi) := by
        positivity
      have h_inv :
          c ≤ (1 + x)⁻¹ := by
        dsimp [c]
        exact (inv_le_inv₀ hc_pos hx_pos).2 (by linarith)
      -- Replace the varying denominator by the largest one on the current block.
      calc
        c * |Real.sin x| ≤ (1 + x)⁻¹ * |Real.sin x| := by
          exact mul_le_mul_of_nonneg_right h_inv (abs_nonneg _)
        _ = |Real.sin x| / (1 + x) := by
          rw [div_eq_mul_inv, mul_comm]
        _ = |Real.sin x / (1 + x)| := by
          rw [abs_div, abs_of_pos hx_pos]
  have h_scaled_mass :
      c * 2
        ≤ ∫ x in ((n : ℝ) * Real.pi)..((((n + 1 : ℕ) : ℝ)) * Real.pi),
            |Real.sin x / (1 + x)| := by
    -- Pull out the constant lower envelope and insert the exact `|sin|` mass.
    calc
      c * 2
        = ∫ x in ((n : ℝ) * Real.pi)..((((n + 1 : ℕ) : ℝ)) * Real.pi), c * |Real.sin x| := by
            rw [intervalIntegral.integral_const_mul, absSin_intervalIntegral_natMulPi]
      _ ≤ ∫ x in ((n : ℝ) * Real.pi)..((((n + 1 : ℕ) : ℝ)) * Real.pi),
            |Real.sin x / (1 + x)| := h_compare
  have h_harmonic_compare : (2 / (1 + Real.pi)) * (1 / (n + 1 : ℝ)) ≤ c * 2 := by
    have hn_pos : (0 : ℝ) < n + 1 := by
      positivity
    have hpi_pos : 0 < 1 + Real.pi := by
      positivity
    have hc_pos : 0 < 1 + (((n + 1 : ℕ) : ℝ) * Real.pi) := by
      positivity
    have h_den :
        1 + (((n + 1 : ℕ) : ℝ) * Real.pi) ≤ (1 + Real.pi) * (n + 1 : ℝ) := by
      have hn_nonneg : (0 : ℝ) ≤ n := by
        exact_mod_cast Nat.zero_le n
      calc
        1 + (((n + 1 : ℕ) : ℝ) * Real.pi)
            ≤ (n + 1 : ℝ) + (((n + 1 : ℕ) : ℝ) * Real.pi) := by
                nlinarith
        _ = (1 + Real.pi) * (n + 1 : ℝ) := by
            rw [Nat.cast_add]
            ring
    have h_inv :
        (((1 + Real.pi) * (n + 1 : ℝ))⁻¹) ≤ c := by
      dsimp [c]
      exact (inv_le_inv₀ (by positivity) hc_pos).2 h_den
    calc
      (2 / (1 + Real.pi)) * (1 / (n + 1 : ℝ))
          = 2 * (((1 + Real.pi) * (n + 1 : ℝ))⁻¹) := by
              field_simp [hpi_pos.ne', hn_pos.ne']
      _ ≤ 2 * c := by
          exact mul_le_mul_of_nonneg_left h_inv (by positivity)
      _ = c * 2 := by ring
  exact h_harmonic_compare.trans h_scaled_mass

/-- Helper for Remark 4.25: the absolute value `x ↦ |sin x / (1 + x)|` is not integrable on
`[0, ∞)`. -/
lemma notIntegrableOn_absSineDecay_Ici :
    ¬ IntegrableOn (fun x : ℝ ↦ |Real.sin x / (1 + x)|) (Ici (0 : ℝ)) := by
  intro h_integrable
  let f : ℕ → ℝ := fun n ↦
    ∫ x in (0 : ℝ)..((n : ℝ) * Real.pi), |Real.sin x / (1 + x)|
  let g : ℕ → ℝ := fun n ↦
    (2 / (1 + Real.pi)) * ((Finset.range n).sum fun k ↦ (1 / (k + 1 : ℝ)))
  have h_integrable_Ioi :
      IntegrableOn (fun x : ℝ ↦ |Real.sin x / (1 + x)|) (Ioi (0 : ℝ)) := by
    simpa [IntegrableOn, MeasureTheory.restrict_Ioi_eq_restrict_Ici] using h_integrable
  have h_sum_blocks :
      ∀ n : ℕ,
        (Finset.range n).sum
            (fun k ↦ ∫ x in ((k : ℝ) * Real.pi)..((((k + 1 : ℕ) : ℝ)) * Real.pi),
              |Real.sin x / (1 + x)|)
          = f n := by
    intro n
    -- Decompose the truncation at `n * π` into adjacent `π`-blocks.
    simpa [f, zero_mul] using
      (intervalIntegral.sum_integral_adjacent_intervals
        (f := fun x : ℝ ↦ |Real.sin x / (1 + x)|)
        (a := fun k : ℕ ↦ (k : ℝ) * Real.pi)
        (n := n)
        (fun k hk ↦ absSineDecay_block_intervalIntegrable k))
  have h_lower : ∀ n : ℕ, g n ≤ f n := by
    intro n
    calc
      g n = (Finset.range n).sum (fun k ↦ (2 / (1 + Real.pi)) * (1 / (k + 1 : ℝ))) := by
        simp [g, Finset.mul_sum]
      _ ≤ (Finset.range n).sum
            (fun k ↦ ∫ x in ((k : ℝ) * Real.pi)..((((k + 1 : ℕ) : ℝ)) * Real.pi),
              |Real.sin x / (1 + x)|) := by
            exact Finset.sum_le_sum fun k hk ↦ absSineDecay_block_lower k
      _ = f n := h_sum_blocks n
  have hg_atTop : Tendsto g atTop atTop := by
    -- The comparison sequence is a positive multiple of the harmonic partial sums.
    exact Real.tendsto_sum_range_one_div_nat_succ_atTop.const_mul_atTop (by positivity)
  have hf_limit :
      Tendsto f atTop (𝓝 (∫ x in Ioi (0 : ℝ), |Real.sin x / (1 + x)|)) := by
    have hpi_atTop :
        Tendsto (fun n : ℕ ↦ (n : ℝ) * Real.pi) atTop atTop := by
      simpa [mul_comm] using tendsto_natCast_atTop_atTop.const_mul_atTop Real.pi_pos
    -- Integrability on `(0, ∞)` forces the truncated interval integrals to converge.
    simpa [f] using
      (MeasureTheory.intervalIntegral_tendsto_integral_Ioi 0 h_integrable_Ioi hpi_atTop)
  have hf_atTop : Tendsto f atTop atTop := by
    exact Filter.tendsto_atTop_mono h_lower hg_atTop
  have h_lt :
      ∀ᶠ n : ℕ in atTop, f n < (∫ x in Ioi (0 : ℝ), |Real.sin x / (1 + x)|) + 1 := by
    exact hf_limit.eventually_lt_const (by linarith)
  have h_gt :
      ∀ᶠ n : ℕ in atTop, (∫ x in Ioi (0 : ℝ), |Real.sin x / (1 + x)|) + 1 < f n := by
    exact hf_atTop.eventually_gt_atTop
      ((∫ x in Ioi (0 : ℝ), |Real.sin x / (1 + x)|) + 1)
  have h_false : ∀ᶠ n : ℕ in atTop, False := by
    filter_upwards [h_lt, h_gt] with n hn_lt hn_gt
    exact (not_lt_of_gt hn_gt) hn_lt
  exact (show Filter.NeBot (Filter.atTop : Filter ℕ) from inferInstance).ne
    (Filter.eventually_false_iff_eq_bot.mp h_false)

-- Proof sketch: show that the oscillatory primitive `b ↦ ∫ x in 0..b, sin x / (1 + x)` converges
-- as `b → ∞` by Dirichlet's test or integration by parts, and use the failure of absolute
-- integrability on `[0, ∞)` to conclude that this gives only an improper Riemann integral.
/-- Remark 4.25: the function `x ↦ sin x / (1 + x)` on `[0, ∞)` has a convergent improper
Riemann integral, but its absolute value does not have finite Lebesgue integral on `[0, ∞)`. -/
theorem sine_decay_improper_integrable_not_hasFiniteIntegral_on_Ici :
    (∃ c : ℝ,
      Tendsto
        (fun b : ℝ ↦ ∫ x in (0 : ℝ)..b, Real.sin x / (1 + x))
        atTop (𝓝 c)) ∧
    ¬ HasFiniteIntegral (fun x : ℝ ↦ Real.sin x / (1 + x))
      (volume.restrict (Set.Ici (0 : ℝ))) := by
  constructor
  · -- The improper Riemann integral converges by the integration-by-parts decomposition above.
    exact ⟨1 - ∫ x in Ioi (0 : ℝ), Real.cos x / (1 + x)^2, tendsto_intervalIntegral_sineDecay_atTop⟩
  · intro h_finite
    have h_norm_finite :
        HasFiniteIntegral (fun x : ℝ ↦ |Real.sin x / (1 + x)|)
          (volume.restrict (Set.Ici (0 : ℝ))) := by
      -- Finite Lebesgue integral implies finite integral of the absolute value.
      simpa only [Real.norm_eq_abs] using
        (MeasureTheory.hasFiniteIntegral_norm_iff (fun x : ℝ ↦ Real.sin x / (1 + x))).2 h_finite
    have h_meas :
        AEStronglyMeasurable (fun x : ℝ ↦ |Real.sin x / (1 + x)|)
          (volume.restrict (Set.Ici (0 : ℝ))) := by
      -- The absolute-value integrand is continuous on `[0, ∞)`.
      exact continuousOn_absSineDecay_Ici.aestronglyMeasurable measurableSet_Ici
    exact notIntegrableOn_absSineDecay_Ici ⟨h_meas, h_norm_finite⟩

theorem not_integrableOn_abs_sine_decay_on_Ici :
    ¬ IntegrableOn (fun x : ℝ ↦ |Real.sin x / (1 + x)|) (Set.Ici (0 : ℝ)) := by
  intro h_integrable
  refine sine_decay_improper_integrable_not_hasFiniteIntegral_on_Ici.2 ?_
  rw [← hasFiniteIntegral_norm_iff (fun x : ℝ ↦ Real.sin x / (1 + x))]
  simpa only [Real.norm_eq_abs] using h_integrable.2
