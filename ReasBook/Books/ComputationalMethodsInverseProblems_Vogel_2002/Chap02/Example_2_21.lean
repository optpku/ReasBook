/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import ComputationalMethodsInverseProblems_Vogel_2002.Chap01.Exercise_1_16.Landweber
public import Mathlib.Algebra.Order.Floor.Semifield
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Analysis.SpecialFunctions.Sqrt

public section

open Filter
open scoped Topology

/-- Helper for Example 2.21: the Landweber base `1 - s^2 / ‖K‖^2` lies in `[0, 1)`. -/
lemma landweberBase_nonneg_lt_one
    {Knorm s : ℝ}
    (hs : 0 < s) (hsK : s ≤ Knorm) :
    0 ≤ 1 - s ^ 2 / Knorm ^ 2 ∧ 1 - s ^ 2 / Knorm ^ 2 < 1 := by
  -- First show that `s^2 / ‖K‖^2` lies in `(0, 1]`.
  have hKnorm : 0 < Knorm := lt_of_lt_of_le hs hsK
  have hsq_le : s ^ 2 ≤ Knorm ^ 2 := by
    nlinarith [sq_nonneg (Knorm - s)]
  have hsq_div_le : s ^ 2 / Knorm ^ 2 ≤ 1 := by
    have hKsq : 0 < Knorm ^ 2 := by positivity
    rw [div_le_iff₀ hKsq]
    simpa using hsq_le
  have hsq_div_pos : 0 < s ^ 2 / Knorm ^ 2 := by
    positivity
  constructor <;> nlinarith

/-- Helper for Example 2.21: on `[0, 1]`, the Bernoulli remainder is bounded by
the linear term `v * x`. -/
lemma one_sub_pow_le_natCast_mul
    {x : ℝ} {v : ℕ}
    (hx_nonneg : 0 ≤ x) (hx_le_one : x ≤ 1) :
    1 - (1 - x) ^ v ≤ (v : ℝ) * x := by
  induction v with
  | zero =>
      simp
  | succ v ih =>
      -- Expand one step and bound the remaining power by `1`.
      have hbase_nonneg : 0 ≤ 1 - x := sub_nonneg.mpr hx_le_one
      have hbase_le_one : 1 - x ≤ 1 := by linarith
      have hpow_le_one : (1 - x) ^ v ≤ 1 := pow_le_one₀ hbase_nonneg hbase_le_one
      calc
        1 - (1 - x) ^ (v + 1)
            = (1 - (1 - x) ^ v) + (1 - x) ^ v * x := by
                ring
        _ ≤ (v : ℝ) * x + (1 - x) ^ v * x := by
              gcongr
        _ ≤ (v : ℝ) * x + x := by
              have hmul : (1 - x) ^ v * x ≤ x := by
                simpa [one_mul] using mul_le_mul_of_nonneg_right hpow_le_one hx_nonneg
              simpa [add_comm] using add_le_add_left hmul ((v : ℝ) * x)
        _ = ((v + 1 : ℕ) : ℝ) * x := by
              norm_num [Nat.cast_add, add_mul]

/-- Helper for Example 2.21: the chosen parameter
`v = ⌊‖K‖^2 / δ⌋` gives the right-hand side of `(2.30)` at most `√δ`. -/
lemma deltaMulSqrtFloorNormSqDivDelta_le_sqrtDelta
    {Knorm δ : ℝ}
    (hKnorm : 0 < Knorm) (hδ : 0 < δ) :
    δ * (Real.sqrt (⌊Knorm ^ 2 / δ⌋₊ : ℝ) / Knorm) ≤ Real.sqrt δ := by
  -- Compare the floor term to `‖K‖^2 / δ`, then simplify the resulting square-root expression.
  have hfloor_le :
      Real.sqrt (⌊Knorm ^ 2 / δ⌋₊ : ℝ) ≤ Real.sqrt (Knorm ^ 2 / δ) := by
    apply Real.sqrt_le_sqrt
    exact Nat.floor_le (by positivity : 0 ≤ Knorm ^ 2 / δ)
  have hscale_nonneg : 0 ≤ δ / Knorm := by
    positivity
  have hscaled := mul_le_mul_of_nonneg_left hfloor_le hscale_nonneg
  calc
    δ * (Real.sqrt (⌊Knorm ^ 2 / δ⌋₊ : ℝ) / Knorm)
        = (δ / Knorm) * Real.sqrt (⌊Knorm ^ 2 / δ⌋₊ : ℝ) := by ring
    _ ≤ (δ / Knorm) * Real.sqrt (Knorm ^ 2 / δ) := hscaled
    _ = Real.sqrt δ := by
          have hsqrtδ_ne : Real.sqrt δ ≠ 0 := Real.sqrt_ne_zero'.2 hδ
          rw [Real.sqrt_div (sq_nonneg Knorm), Real.sqrt_sq hKnorm.le]
          calc
            (δ / Knorm) * (Knorm / Real.sqrt δ) = δ / Real.sqrt δ := by
              field_simp [hKnorm.ne']
            _ = Real.sqrt δ := by
              apply (div_eq_iff hsqrtδ_ne).2
              simpa [sq, mul_comm] using (Real.sq_sqrt hδ.le).symm

/-- Example 2.21 (1): for the Landweber filter with step size `1 / ‖K‖^2`, the
Chapter 2 filter-limit condition `(2.28)` holds with `α_* = v_* = ∞`, expressed
as `w_v (s ^ 2) → 1` as `v → ∞` for each `s` with `0 < s ≤ ‖K‖`. -/
theorem landweberFilterLimit
    {Knorm s : ℝ}
    (hs : 0 < s) (hsK : s ≤ Knorm) :
    Tendsto
      (fun v : ℕ ↦ SpectralFilter.landweber (1 / Knorm ^ 2) v (s ^ 2))
      atTop
      (𝓝 (1 : ℝ)) := by
  -- Rewrite to the geometric-power form and send that power to `0`.
  have hbase := landweberBase_nonneg_lt_one hs hsK
  have hpow :
      Tendsto (fun v : ℕ ↦ (1 - s ^ 2 / Knorm ^ 2) ^ v) atTop (𝓝 (0 : ℝ)) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one hbase.1 hbase.2
  simpa [SpectralFilter.landweber_eq, div_eq_mul_inv, sub_eq_add_neg, mul_comm, mul_left_comm,
    mul_assoc] using (tendsto_const_nhds.sub hpow)

/-- Example 2.21 (2): the displayed Landweber inequality `(2.31)` states that
`w_v (s ^ 2) / s ≤ Real.sqrt v / ‖K‖` whenever `0 < s ≤ ‖K‖`. -/
theorem landweberInverseBound
    {Knorm s : ℝ} {v : ℕ}
    (hs : 0 < s) (hsK : s ≤ Knorm) :
    SpectralFilter.landweber (1 / Knorm ^ 2) v (s ^ 2) / s ≤
      Real.sqrt (v : ℝ) / Knorm := by
  -- Split off the trivial `v = 0` case before comparing the small- and large-`s` regimes.
  rcases Nat.eq_zero_or_pos v with rfl | hv
  · simp [SpectralFilter.landweber_eq]
  · have hKnorm : 0 < Knorm := lt_of_lt_of_le hs hsK
    have hbase := landweberBase_nonneg_lt_one hs hsK
    have hx_nonneg : 0 ≤ s ^ 2 / Knorm ^ 2 := by positivity
    have hx_le_one : s ^ 2 / Knorm ^ 2 ≤ 1 := by
      nlinarith [hbase.1]
    have hw_linear :
        SpectralFilter.landweber (1 / Knorm ^ 2) v (s ^ 2) ≤ (v : ℝ) * (s ^ 2 / Knorm ^ 2) := by
      -- Bound the Landweber numerator by the Bernoulli linear term.
      simpa [SpectralFilter.landweber_eq, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using
        (one_sub_pow_le_natCast_mul (v := v) hx_nonneg hx_le_one)
    have hw_one :
        SpectralFilter.landweber (1 / Knorm ^ 2) v (s ^ 2) ≤ 1 := by
      -- The filter never exceeds `1` because the remaining power is nonnegative.
      have hpow_nonneg : 0 ≤ (1 - s ^ 2 / Knorm ^ 2) ^ v := pow_nonneg hbase.1 v
      have hw_one' : 1 - (1 - s ^ 2 / Knorm ^ 2) ^ v ≤ 1 := by
        linarith
      simpa [SpectralFilter.landweber_eq, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using
        hw_one'
    have hsqrtv_pos : 0 < Real.sqrt (v : ℝ) := by
      positivity
    by_cases hsmall : s ≤ Knorm / Real.sqrt (v : ℝ)
    · -- For small `s`, the linear Landweber estimate is sharp enough.
      have hdiv_linear :
          SpectralFilter.landweber (1 / Knorm ^ 2) v (s ^ 2) / s ≤
            (v : ℝ) * (s ^ 2 / Knorm ^ 2) / s := by
        have := div_le_div_of_nonneg_right hw_linear hs.le
        simpa using this
      refine hdiv_linear.trans ?_
      calc
        (v : ℝ) * (s ^ 2 / Knorm ^ 2) / s = (v : ℝ) * s / Knorm ^ 2 := by
          field_simp [hs.ne', hKnorm.ne']
        _ ≤ (v : ℝ) * (Knorm / Real.sqrt (v : ℝ)) / Knorm ^ 2 := by
          gcongr
        _ = Real.sqrt (v : ℝ) / Knorm := by
            field_simp [hKnorm.ne', hsqrtv_pos.ne']
            rw [Real.sq_sqrt (show 0 ≤ (v : ℝ) by positivity)]
    · -- For large `s`, the trivial bound `w_v ≤ 1` is enough.
      have hlarge : Knorm / Real.sqrt (v : ℝ) ≤ s := le_of_not_ge hsmall
      have hdiv_one :
          SpectralFilter.landweber (1 / Knorm ^ 2) v (s ^ 2) / s ≤ 1 / s := by
        have := div_le_div_of_nonneg_right hw_one hs.le
        simpa using this
      refine hdiv_one.trans ?_
      have hKdiv_pos : 0 < Knorm / Real.sqrt (v : ℝ) := by
        positivity
      have hrecip :
          1 / s ≤ 1 / (Knorm / Real.sqrt (v : ℝ)) :=
        one_div_le_one_div_of_le hKdiv_pos hlarge
      calc
        1 / s ≤ 1 / (Knorm / Real.sqrt (v : ℝ)) := hrecip
        _ = Real.sqrt (v : ℝ) / Knorm := by
            field_simp [hKnorm.ne', hsqrtv_pos.ne']

/-- Example 2.21 (3): the parameter choice `v = ⌊‖K‖^2 / δ⌋` satisfies the
Chapter 2 parameter-limit condition `(2.29)`, namely `⌊‖K‖^2 / δ⌋ → ∞` as
`δ → 0+`. -/
theorem floorNormSqDivDelta_tendstoAtTop
    {Knorm : ℝ} (hKnorm : 0 < Knorm) :
    Tendsto
      (fun δ : ℝ ↦ ⌊Knorm ^ 2 / δ⌋₊)
      (nhdsWithin (0 : ℝ) (Set.Ioi 0))
      atTop := by
  -- Transport `δ → 0+` to `δ⁻¹ → +∞`, then multiply by the positive constant `‖K‖^2`.
  have hdiv :
      Tendsto (fun δ : ℝ ↦ Knorm ^ 2 / δ) (𝓝[>] (0 : ℝ)) atTop := by
    have hKsq : 0 < Knorm ^ 2 := by positivity
    simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using
      (tendsto_inv_nhdsGT_zero.const_mul_atTop hKsq)
  convert (tendsto_nat_floor_atTop.comp hdiv) using 1
  funext δ
  rfl

/-- Example 2.21 (4): the same parameter choice `v = ⌊‖K‖^2 / δ⌋` satisfies the
Chapter 2 inverse-bound limit condition `(2.30)`, namely
`δ * (Real.sqrt ⌊‖K‖^2 / δ⌋ / ‖K‖) → 0` as `δ → 0+`. -/
theorem deltaMulSqrtFloorNormSqDivDelta_tendstoZero
    {Knorm : ℝ} (hKnorm : 0 < Knorm) :
    Tendsto
      (fun δ : ℝ ↦
        δ * (Real.sqrt (⌊Knorm ^ 2 / δ⌋₊ : ℝ) / Knorm))
      (nhdsWithin (0 : ℝ) (Set.Ioi 0))
      (𝓝 (0 : ℝ)) := by
  -- Squeeze the displayed expression between `0` and `√δ` on the right neighborhood of `0`.
  have hsqrt :
      Tendsto (fun δ : ℝ ↦ Real.sqrt δ) (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)) := by
    have hsqrt0 : Tendsto (fun δ : ℝ ↦ Real.sqrt δ) (𝓝 (0 : ℝ)) (𝓝 (0 : ℝ)) := by
      simpa using (Filter.Tendsto.sqrt (f := fun δ : ℝ ↦ δ) (l := 𝓝 (0 : ℝ)) (x := 0) tendsto_id)
    change Tendsto (fun δ : ℝ ↦ Real.sqrt δ) (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (𝓝 (0 : ℝ))
    exact hsqrt0.mono_left inf_le_left
  have h_nonneg :
      ∀ᶠ δ : ℝ in 𝓝[>] (0 : ℝ),
        0 ≤ δ * (Real.sqrt (⌊Knorm ^ 2 / δ⌋₊ : ℝ) / Knorm) := by
    filter_upwards [self_mem_nhdsWithin] with δ hδ
    have hδpos : 0 < δ := hδ
    positivity
  have h_bound :
      ∀ᶠ δ : ℝ in 𝓝[>] (0 : ℝ),
        δ * (Real.sqrt (⌊Knorm ^ 2 / δ⌋₊ : ℝ) / Knorm) ≤ Real.sqrt δ := by
    filter_upwards [self_mem_nhdsWithin] with δ hδ
    exact deltaMulSqrtFloorNormSqDivDelta_le_sqrtDelta hKnorm hδ
  simpa using
    (tendsto_of_tendsto_of_tendsto_of_le_of_le'
      (f := fun δ : ℝ ↦ δ * (Real.sqrt (⌊Knorm ^ 2 / δ⌋₊ : ℝ) / Knorm))
      (g := fun _ : ℝ ↦ (0 : ℝ))
      (h := fun δ : ℝ ↦ Real.sqrt δ)
      tendsto_const_nhds hsqrt h_nonneg h_bound)
