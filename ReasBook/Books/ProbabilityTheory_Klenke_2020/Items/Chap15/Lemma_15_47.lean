/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib
import Books.ProbabilityTheory_Klenke_2020.Items.Chap15.Definition_15_1

-- Declarations for this item will be appended below by the statement pipeline.

open BoundedContinuousFunction
open Filter
open Set
open scoped BoundedContinuousFunction Topology

universe u

noncomputable section

/-- The auxiliary function `f_t` used in the characteristic-function proof of the central limit
theorem. -/
def cltAuxiliaryFunction (t : ℝ) : ℝ → ℂ :=
  fun x ↦
    if x = 0 then
      (-(t ^ (2 : ℕ) / 2 : ℝ) : ℂ)
    else
      (((1 + x ^ (2 : ℕ)) / x ^ (2 : ℕ) : ℝ) : ℂ) *
        (Complex.exp (((t * x : ℝ) : ℂ) * Complex.I) - 1 -
          Complex.I * (t * x / (1 + x ^ (2 : ℕ)) : ℝ))

-- Proof sketch: unfold `cltAuxiliaryFunction` at `x = 0`; the definition uses the continuous
-- extension value `-t^2 / 2` at the origin.
/-- The auxiliary function `cltAuxiliaryFunction t` takes the value `-t^2 / 2` at `0`. -/
theorem cltAuxiliaryFunction_apply_zero (t : ℝ) :
    cltAuxiliaryFunction t 0 = (-(t ^ (2 : ℕ) / 2 : ℝ) : ℂ) := by
  -- The zero branch of the defining `if` is the prescribed continuous extension value.
  simp [cltAuxiliaryFunction]

-- Proof sketch: unfold `cltAuxiliaryFunction` and simplify the defining `if` using `x ≠ 0`.
/-- Away from `0`, the auxiliary function is the textbook expression
`((1 + x^2) / x^2) * (exp (itx) - 1 - i t x / (1 + x^2))`. -/
theorem cltAuxiliaryFunction_apply_ne_zero (t x : ℝ) (hx : x ≠ 0) :
    cltAuxiliaryFunction t x =
      (((1 + x ^ (2 : ℕ)) / x ^ (2 : ℕ) : ℝ) : ℂ) *
        (Complex.exp (((t * x : ℝ) : ℂ) * Complex.I) - 1 -
          Complex.I * (t * x / (1 + x ^ (2 : ℕ)) : ℝ)) := by
  -- Away from the origin, the defining `if` immediately collapses to the textbook formula.
  simp [cltAuxiliaryFunction, hx]

/-- Helper for Lemma 15.47: the first-order Taylor correction in `cltAuxiliaryFunction` reduces to
`I * (t * x)`. -/
lemma cltAuxiliaryFunction_linearCorrection (t x : ℝ) (hx : x ≠ 0) :
    ((((1 + x ^ (2 : ℕ)) / x ^ (2 : ℕ) : ℝ) : ℂ) *
        ((((t * x : ℝ) : ℂ) * Complex.I) - Complex.I * (t * x / (1 + x ^ (2 : ℕ)) : ℝ))) =
      Complex.I * (t * x : ℝ) := by
  have hx2 : (x ^ (2 : ℕ) : ℝ) ≠ 0 := pow_ne_zero 2 hx
  have h1x2 : (1 + x ^ (2 : ℕ) : ℝ) ≠ 0 := by positivity
  have hreal :
      ((1 + x ^ (2 : ℕ)) / x ^ (2 : ℕ)) * ((t * x) - t * x / (1 + x ^ (2 : ℕ))) = t * x := by
    -- Clearing the `x^2` denominator leaves a scalar identity in `ℝ`.
    field_simp [hx2, h1x2]
    ring
  -- Pull out the common factor `I`, then finish with the real identity above.
  calc
    ((((1 + x ^ (2 : ℕ)) / x ^ (2 : ℕ) : ℝ) : ℂ) *
        ((((t * x : ℝ) : ℂ) * Complex.I) - Complex.I * (t * x / (1 + x ^ (2 : ℕ)) : ℝ))) =
        Complex.I *
          ((((1 + x ^ (2 : ℕ)) / x ^ (2 : ℕ)) * ((t * x) - t * x / (1 + x ^ (2 : ℕ))) : ℝ) : ℂ) := by
            simp [sub_eq_add_neg]
            ring
    _ = Complex.I * (t * x : ℝ) := by rw [hreal]

/-- Helper for Lemma 15.47: the quadratic Taylor correction and the prescribed value at `0`
combine to `-(t^2 * x^2) / 2`. -/
lemma cltAuxiliaryFunction_quadraticCorrection (t x : ℝ) (hx : x ≠ 0) :
    ((((1 + x ^ (2 : ℕ)) / x ^ (2 : ℕ) : ℝ) : ℂ) *
        ((((t * x : ℝ) : ℂ) * Complex.I) ^ (2 : ℕ) / 2)) + ((t ^ (2 : ℕ) / 2 : ℝ) : ℂ) =
      -((t ^ (2 : ℕ) * x ^ (2 : ℕ) / 2 : ℝ) : ℂ) := by
  have hx2 : (x ^ (2 : ℕ) : ℝ) ≠ 0 := pow_ne_zero 2 hx
  have hreal :
      ((1 + x ^ (2 : ℕ)) / x ^ (2 : ℕ)) * (-(t * x) ^ (2 : ℕ) / 2) + t ^ (2 : ℕ) / 2 =
        -(t ^ (2 : ℕ) * x ^ (2 : ℕ) / 2) := by
    -- Clearing the `x^2` denominator again reduces the goal to a real polynomial identity.
    field_simp [hx2]
    ring
  have hzsq : ((((t * x : ℝ) : ℂ) * Complex.I) ^ (2 : ℕ)) = -(((t * x) ^ (2 : ℕ) : ℝ) : ℂ) := by
    -- The quadratic term of `exp (itx)` is `-(t*x)^2`.
    apply Complex.ext <;> simp [pow_two, Complex.I_sq, mul_assoc, mul_left_comm, mul_comm]
  -- Normalize `I^2 = -1`, then rewrite the remaining real scalar identity.
  calc
    ((((1 + x ^ (2 : ℕ)) / x ^ (2 : ℕ) : ℝ) : ℂ) *
        ((((t * x : ℝ) : ℂ) * Complex.I) ^ (2 : ℕ) / 2)) + ((t ^ (2 : ℕ) / 2 : ℝ) : ℂ) =
        ((((1 + x ^ (2 : ℕ)) / x ^ (2 : ℕ)) * (-(t * x) ^ (2 : ℕ) / 2) + t ^ (2 : ℕ) / 2 : ℝ) : ℂ) := by
          rw [hzsq]
          simp
    _ = -((t ^ (2 : ℕ) * x ^ (2 : ℕ) / 2 : ℝ) : ℂ) := by
          simpa using congrArg (fun r : ℝ ↦ (r : ℂ)) hreal

/-- Helper for Lemma 15.47: the third-order Taylor remainder of `exp (u I)` is controlled by
`(2 / 9) * |u|^3` on the unit interval. -/
lemma norm_expMulI_sub_taylorTwo_le (u : ℝ) (hu : |u| ≤ 1) :
    ‖Complex.exp (((u : ℝ) : ℂ) * Complex.I) -
        ∑ m ∈ Finset.range 3, ((((u : ℝ) : ℂ) * Complex.I) ^ m / m.factorial)‖ ≤
      (2 / 9 : ℝ) * |u| ^ 3 := by
  have huComplex : ‖(((u : ℝ) : ℂ) * Complex.I)‖ ≤ 1 := by
    simpa [norm_mul, RCLike.norm_ofReal] using hu
  have hnorm : ‖(((u : ℝ) : ℂ) * Complex.I)‖ = |u| := by
    simp [norm_mul, RCLike.norm_ofReal]
  -- Apply the general complex exponential Taylor bound with `n = 3`.
  calc
    ‖Complex.exp (((u : ℝ) : ℂ) * Complex.I) -
        ∑ m ∈ Finset.range 3, ((((u : ℝ) : ℂ) * Complex.I) ^ m / m.factorial)‖ ≤
        ‖(((u : ℝ) : ℂ) * Complex.I)‖ ^ 3 * ((4 : ℝ) * ((Nat.factorial 3 : ℕ) * 3 : ℝ)⁻¹) := by
          simpa using (Complex.exp_bound (x := (((u : ℝ) : ℂ) * Complex.I)) huComplex
            (n := 3) (by decide : 0 < 3))
    _ = (2 / 9 : ℝ) * |u| ^ 3 := by
          rw [hnorm]
          norm_num
          ring

/-- Helper for Lemma 15.47: multiplying a real scalar by `Complex.I` does not change its norm. -/
lemma norm_I_mul_ofReal (r : ℝ) : ‖Complex.I * (r : ℂ)‖ = |r| := by
  -- This is the only recurring norm/coercion bridge needed in the remaining estimates.
  simp [norm_mul, RCLike.norm_ofReal]

/-- Helper for Lemma 15.47: after subtracting the value at `0`, the auxiliary function splits into
the cubic exponential remainder plus the linear and quadratic correction terms. -/
lemma cltAuxiliaryFunction_sub_apply_zero_eq (t x : ℝ) (hx : x ≠ 0) :
    cltAuxiliaryFunction t x - cltAuxiliaryFunction t 0 =
      ((((1 + x ^ (2 : ℕ)) / x ^ (2 : ℕ) : ℝ) : ℂ) *
          (Complex.exp (((t * x : ℝ) : ℂ) * Complex.I) -
            ∑ m ∈ Finset.range 3, ((((t * x : ℝ) : ℂ) * Complex.I) ^ m / m.factorial))) +
        (Complex.I * (t * x : ℝ) - ((t ^ (2 : ℕ) * x ^ (2 : ℕ) / 2 : ℝ) : ℂ)) := by
  let a : ℂ := (((1 + x ^ (2 : ℕ)) / x ^ (2 : ℕ) : ℝ) : ℂ)
  let z : ℂ := (((t * x : ℝ) : ℂ) * Complex.I)
  have hsum : ∑ m ∈ Finset.range 3, z ^ m / m.factorial = 1 + z + z ^ (2 : ℕ) / 2 := by
    norm_num [Finset.sum_range_succ, z, pow_two]
  have hlin : a * (z - Complex.I * (t * x / (1 + x ^ (2 : ℕ)) : ℝ)) = Complex.I * (t * x : ℝ) := by
    simpa [a, z] using cltAuxiliaryFunction_linearCorrection t x hx
  have hquad :
      a * (z ^ (2 : ℕ) / 2) + ((t ^ (2 : ℕ) / 2 : ℝ) : ℂ) =
        -((t ^ (2 : ℕ) * x ^ (2 : ℕ) / 2 : ℝ) : ℂ) := by
    simpa [a, z] using cltAuxiliaryFunction_quadraticCorrection t x hx
  -- Expand the third-order Taylor polynomial and fold the linear and quadratic corrections into
  -- their dedicated helper lemmas.
  calc
    cltAuxiliaryFunction t x - cltAuxiliaryFunction t 0 =
        a * (Complex.exp z - 1 - Complex.I * (t * x / (1 + x ^ (2 : ℕ)) : ℝ)) +
          ((t ^ (2 : ℕ) / 2 : ℝ) : ℂ) := by
            rw [cltAuxiliaryFunction_apply_ne_zero t x hx, cltAuxiliaryFunction_apply_zero]
            simp [a, z]
    _ = a * (Complex.exp z - ∑ m ∈ Finset.range 3, z ^ m / m.factorial) +
          (a * (z - Complex.I * (t * x / (1 + x ^ (2 : ℕ)) : ℝ)) +
            (a * (z ^ (2 : ℕ) / 2) + ((t ^ (2 : ℕ) / 2 : ℝ) : ℂ))) := by
              rw [hsum]
              ring
    _ = a * (Complex.exp z - ∑ m ∈ Finset.range 3, z ^ m / m.factorial) +
          (Complex.I * (t * x : ℝ) - ((t ^ (2 : ℕ) * x ^ (2 : ℕ) / 2 : ℝ) : ℂ)) := by
            rw [hlin, hquad]
            ring
    _ = ((((1 + x ^ (2 : ℕ)) / x ^ (2 : ℕ) : ℝ) : ℂ) *
          (Complex.exp (((t * x : ℝ) : ℂ) * Complex.I) -
            ∑ m ∈ Finset.range 3, ((((t * x : ℝ) : ℂ) * Complex.I) ^ m / m.factorial))) +
        (Complex.I * (t * x : ℝ) - ((t ^ (2 : ℕ) * x ^ (2 : ℕ) / 2 : ℝ) : ℂ)) := by
          simp [a, z]

/-- Helper for Lemma 15.47: near `0`, the auxiliary function differs from its value at `0`
by at most a fixed linear multiple of `|x|`. -/
lemma norm_cltAuxiliaryFunction_sub_apply_zero_eventually_le (t : ℝ) :
    ∀ᶠ x in nhds 0,
      ‖cltAuxiliaryFunction t x - cltAuxiliaryFunction t 0‖ ≤
        (|t| ^ 3 + |t| + t ^ (2 : ℕ) / 2) * |x| := by
  have hx_small : ∀ᶠ x : ℝ in 𝓝 0, |x| ≤ 1 := by
    -- Work in a neighborhood where `x` stays inside the unit ball.
    filter_upwards [Metric.ball_mem_nhds (0 : ℝ) zero_lt_one] with x hx
    exact le_of_lt (by simpa [Metric.mem_ball, Real.dist_eq] using hx)
  have htx_small : ∀ᶠ x : ℝ in 𝓝 0, |t * x| ≤ 1 := by
    -- The Taylor remainder estimate also needs `|t * x| ≤ 1`.
    have hmul : Tendsto (fun x : ℝ ↦ t * x) (𝓝 0) (𝓝 0) := by
      simpa [zero_mul] using (continuous_const.mul continuous_id).tendsto (0 : ℝ)
    filter_upwards [hmul (Metric.ball_mem_nhds (0 : ℝ) zero_lt_one)] with x hx
    exact le_of_lt (by simpa [Metric.mem_ball, Real.dist_eq] using hx)
  filter_upwards [hx_small, htx_small] with x hxabs htxabs
  by_cases hx0 : x = 0
  · -- At the origin the desired estimate is immediate.
    simp [hx0]
  · -- Away from `0`, rewrite with the repaired Taylor decomposition and bound each summand.
    have hxsq_le_one_abs : |x| ^ (2 : ℕ) ≤ 1 := by
      nlinarith [abs_nonneg x, hxabs]
    have hxsq_le_one : x ^ (2 : ℕ) ≤ 1 := by
      simpa [sq_abs] using hxsq_le_one_abs
    have hxsq_le_abs : x ^ (2 : ℕ) ≤ |x| := by
      have : |x| ^ (2 : ℕ) ≤ |x| := by
        nlinarith [abs_nonneg x, hxabs]
      simpa [sq_abs] using this
    let A : ℝ := (1 + x ^ (2 : ℕ)) / x ^ (2 : ℕ)
    let R : ℂ :=
      Complex.exp (((t * x : ℝ) : ℂ) * Complex.I) -
        ∑ m ∈ Finset.range 3, ((((t * x : ℝ) : ℂ) * Complex.I) ^ m / m.factorial)
    have hA_nonneg : 0 ≤ A := by
      have hx2pos : 0 < x ^ (2 : ℕ) := by
        simpa [pow_two] using sq_pos_of_ne_zero hx0
      dsimp [A]
      exact div_nonneg (by positivity) hx2pos.le
    have hR_bound : ‖R‖ ≤ (2 / 9 : ℝ) * |t * x| ^ 3 := by
      simpa [R] using norm_expMulI_sub_taylorTwo_le (t * x) htxabs
    have hR_term :
        ‖(A : ℂ) * R‖ ≤ |t| ^ 3 * |x| := by
      have habs0 : |x| ≠ 0 := abs_ne_zero.mpr hx0
      have hfactor :
          A * ((2 / 9 : ℝ) * |t * x| ^ 3) =
            (2 / 9 : ℝ) * (1 + x ^ (2 : ℕ)) * |t| ^ 3 * |x| := by
        dsimp [A]
        rw [abs_mul, mul_pow]
        rw [show (x ^ (2 : ℕ) : ℝ) = |x| ^ (2 : ℕ) by rw [sq_abs]]
        field_simp [habs0]
      have hsmallFactor : (2 / 9 : ℝ) * (1 + x ^ (2 : ℕ)) ≤ 1 := by
        nlinarith
      have hnonneg_tx : 0 ≤ |t| ^ 3 * |x| := by
        positivity
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hA_nonneg]
      calc
        A * ‖R‖ ≤ A * ((2 / 9 : ℝ) * |t * x| ^ 3) := by
          gcongr
        _ = (2 / 9 : ℝ) * (1 + x ^ (2 : ℕ)) * |t| ^ 3 * |x| := hfactor
        _ ≤ 1 * (|t| ^ 3 * |x|) := by
          simpa [mul_assoc, mul_left_comm, mul_comm] using
            mul_le_mul_of_nonneg_right hsmallFactor hnonneg_tx
        _ = |t| ^ 3 * |x| := by ring
    have hcorrection :
        ‖Complex.I * (t * x : ℝ) - ((t ^ (2 : ℕ) * x ^ (2 : ℕ) / 2 : ℝ) : ℂ)‖ ≤
          |t| * |x| + (t ^ (2 : ℕ) / 2) * |x| := by
      -- The linear and quadratic correction terms are each `O(|x|)` on `|x| ≤ 1`.
      calc
        ‖Complex.I * (t * x : ℝ) - ((t ^ (2 : ℕ) * x ^ (2 : ℕ) / 2 : ℝ) : ℂ)‖
            ≤ ‖Complex.I * (t * x : ℝ)‖ +
                ‖((t ^ (2 : ℕ) * x ^ (2 : ℕ) / 2 : ℝ) : ℂ)‖ := by
                  exact norm_sub_le _ _
        _ = |t * x| + |t ^ (2 : ℕ) * x ^ (2 : ℕ) / 2| := by
              rw [norm_I_mul_ofReal, Complex.norm_real, Real.norm_eq_abs]
        _ = |t| * |x| + t ^ (2 : ℕ) * x ^ (2 : ℕ) / 2 := by
              have hquad_nonneg : 0 ≤ t ^ (2 : ℕ) * x ^ (2 : ℕ) / 2 := by
                positivity
              rw [abs_mul, abs_of_nonneg hquad_nonneg]
        _ ≤ |t| * |x| + (t ^ (2 : ℕ) / 2) * |x| := by
              nlinarith
    have hsplit := cltAuxiliaryFunction_sub_apply_zero_eq t x hx0
    have hsplit' :
        cltAuxiliaryFunction t x - cltAuxiliaryFunction t 0 =
          (A : ℂ) * R +
            (Complex.I * (t * x : ℝ) - ((t ^ (2 : ℕ) * x ^ (2 : ℕ) / 2 : ℝ) : ℂ)) := by
      simpa [A, R] using hsplit
    calc
      ‖cltAuxiliaryFunction t x - cltAuxiliaryFunction t 0‖
          = ‖(A : ℂ) * R +
              (Complex.I * (t * x : ℝ) - ((t ^ (2 : ℕ) * x ^ (2 : ℕ) / 2 : ℝ) : ℂ))‖ := by
                rw [hsplit']
      _ ≤ ‖(A : ℂ) * R‖ +
              ‖Complex.I * (t * x : ℝ) - ((t ^ (2 : ℕ) * x ^ (2 : ℕ) / 2 : ℝ) : ℂ)‖ := by
                exact norm_add_le _ _
      _ ≤ |t| ^ 3 * |x| + (|t| * |x| + (t ^ (2 : ℕ) / 2) * |x|) := by
            gcongr
      _ = (|t| ^ 3 + |t| + t ^ (2 : ℕ) / 2) * |x| := by
            ring

/-- Helper for Lemma 15.47: outside the unit interval, the textbook auxiliary function satisfies
the uniform estimate used in the central-limit proof. -/
lemma norm_cltAuxiliaryFunction_le_of_one_le_abs (t x : ℝ) (hx : 1 ≤ |x|) :
    ‖cltAuxiliaryFunction t x‖ ≤ 4 + 2 * |t| := by
  have hx0 : x ≠ 0 := by
    exact abs_ne_zero.mp (ne_of_gt (lt_of_lt_of_le zero_lt_one hx))
  have hxsq_ge_one_abs : 1 ≤ |x| ^ (2 : ℕ) := by
    nlinarith [abs_nonneg x, hx]
  have hxsq_ge_one : 1 ≤ x ^ (2 : ℕ) := by
    simpa [sq_abs] using hxsq_ge_one_abs
  have hprefactor_nonneg : 0 ≤ ((1 + x ^ (2 : ℕ)) / x ^ (2 : ℕ) : ℝ) := by
    have hx2pos : 0 < x ^ (2 : ℕ) := by
      simpa [pow_two] using sq_pos_of_ne_zero hx0
    exact div_nonneg (by positivity) hx2pos.le
  have hprefactor_le_two : ((1 + x ^ (2 : ℕ)) / x ^ (2 : ℕ) : ℝ) ≤ 2 := by
    have hx2pos : 0 < x ^ (2 : ℕ) := by
      simpa [pow_two] using sq_pos_of_ne_zero hx0
    refine (div_le_iff₀ hx2pos).2 ?_
    nlinarith
  have hratio_le_one : |x| / (1 + x ^ (2 : ℕ)) ≤ 1 := by
    have hden : 0 < 1 + x ^ (2 : ℕ) := by positivity
    have hx_le_den : |x| ≤ 1 + x ^ (2 : ℕ) := by
      have hxsq_ge_abs : |x| ≤ x ^ (2 : ℕ) := by
        nlinarith [abs_nonneg x, hx, sq_abs x]
      nlinarith
    exact (div_le_iff₀ hden).2 (by simpa using hx_le_den)
  have hcorrection_le : |t * x / (1 + x ^ (2 : ℕ))| ≤ |t| := by
    have hden : 0 < 1 + x ^ (2 : ℕ) := by positivity
    calc
      |t * x / (1 + x ^ (2 : ℕ))|
          = |t| * (|x| / (1 + x ^ (2 : ℕ))) := by
              rw [abs_div, abs_mul, abs_of_pos hden]
              ring
      _ ≤ |t| * 1 := by
            gcongr
      _ = |t| := by ring
  -- Bound the explicit off-zero branch term-by-term, then use the textbook prefactor estimate.
  rw [cltAuxiliaryFunction_apply_ne_zero t x hx0]
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hprefactor_nonneg]
  calc
    ((1 + x ^ (2 : ℕ)) / x ^ (2 : ℕ) : ℝ) *
        ‖Complex.exp (((t * x : ℝ) : ℂ) * Complex.I) - 1 -
            Complex.I * (t * x / (1 + x ^ (2 : ℕ)) : ℝ)‖
        ≤ ((1 + x ^ (2 : ℕ)) / x ^ (2 : ℕ) : ℝ) * (2 + |t|) := by
            gcongr
            calc
              ‖Complex.exp (((t * x : ℝ) : ℂ) * Complex.I) - 1 -
                  Complex.I * (t * x / (1 + x ^ (2 : ℕ)) : ℝ)‖
                  ≤ ‖Complex.exp (((t * x : ℝ) : ℂ) * Complex.I) - 1‖ +
                      ‖Complex.I * (t * x / (1 + x ^ (2 : ℕ)) : ℝ)‖ := by
                        exact norm_sub_le _ _
              _ ≤ (‖Complex.exp (((t * x : ℝ) : ℂ) * Complex.I)‖ + ‖(1 : ℂ)‖) +
                    ‖Complex.I * (t * x / (1 + x ^ (2 : ℕ)) : ℝ)‖ := by
                      gcongr
                      exact norm_sub_le _ _
              _ = 2 + |t * x / (1 + x ^ (2 : ℕ))| := by
                    rw [Complex.norm_exp_ofReal_mul_I (t * x), norm_I_mul_ofReal]
                    norm_num
              _ ≤ 2 + |t| := by
                    gcongr
    _ ≤ 2 * (2 + |t|) := by
          gcongr
    _ = 4 + 2 * |t| := by
          ring

-- Proof sketch: use the Taylor expansion argument from Lemma 15.30 at the origin and the
-- textbook estimate away from the origin to prove continuity of the explicit formula.
/-- The textbook auxiliary function `f_t` is continuous on `ℝ`. -/
theorem continuous_cltAuxiliaryFunction (t : ℝ) :
    Continuous (cltAuxiliaryFunction t) := by
  refine continuous_iff_continuousAt.2 ?_
  intro x
  by_cases hx : x = 0
  · subst hx
    -- Route correction: use the eventual linear bound to squeeze the difference to `0`.
    show Tendsto (cltAuxiliaryFunction t) (𝓝 0) (𝓝 (cltAuxiliaryFunction t 0))
    have hbound := norm_cltAuxiliaryFunction_sub_apply_zero_eventually_le t
    have habs : Tendsto (fun y : ℝ ↦ |y|) (𝓝 0) (𝓝 0) := by
      simpa using (continuous_abs.tendsto (0 : ℝ))
    have hlim :
        Tendsto (fun y : ℝ ↦ (|t| ^ 3 + |t| + t ^ (2 : ℕ) / 2) * |y|) (𝓝 0) (𝓝 0) := by
      simpa [zero_mul] using (continuous_const.mul continuous_abs).tendsto (0 : ℝ)
    have hzero :
        Tendsto (fun y : ℝ ↦ cltAuxiliaryFunction t y - cltAuxiliaryFunction t 0) (𝓝 0) (𝓝 0) :=
      squeeze_zero_norm' hbound hlim
    have hsum :
        Tendsto
          (fun y : ℝ ↦
            (cltAuxiliaryFunction t y - cltAuxiliaryFunction t 0) + cltAuxiliaryFunction t 0)
          (𝓝 0) (𝓝 (0 + cltAuxiliaryFunction t 0)) :=
      hzero.add tendsto_const_nhds
    simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hsum
  · -- Away from `0`, the function agrees locally with its explicit rational-exponential branch.
    let g : ℝ → ℂ := fun y ↦
      (((1 + y ^ (2 : ℕ)) / y ^ (2 : ℕ) : ℝ) : ℂ) *
        (Complex.exp (((t * y : ℝ) : ℂ) * Complex.I) - 1 -
          Complex.I * (t * y / (1 + y ^ (2 : ℕ)) : ℝ))
    have hEq : cltAuxiliaryFunction t =ᶠ[𝓝 x] g := by
      have hne : ∀ᶠ y in 𝓝 x, y ≠ 0 := by
        exact IsOpen.mem_nhds isOpen_ne hx
      filter_upwards [hne] with y hy
      simp [cltAuxiliaryFunction, g, hy]
    refine (continuousAt_congr hEq).2 ?_
    have hx2 : x ^ (2 : ℕ) ≠ 0 := pow_ne_zero 2 hx
    have hone_add_sq : (1 + x ^ (2 : ℕ) : ℝ) ≠ 0 := by positivity
    -- The explicit branch is a product of continuous operations at any nonzero point.
    dsimp [g]
    have hpow : ContinuousAt (fun y : ℝ ↦ y ^ (2 : ℕ)) x := by
      fun_prop
    have hpowC : ContinuousAt (fun y : ℝ ↦ (y : ℂ) ^ (2 : ℕ)) x := by
      simpa using (Complex.continuous_ofReal.pow 2).continuousAt
    have hxC : (x : ℂ) ≠ 0 := by
      exact_mod_cast hx
    have hx2C : (x : ℂ) ^ (2 : ℕ) ≠ 0 := pow_ne_zero 2 hxC
    have hpref : ContinuousAt (fun y : ℝ ↦ (((1 + y ^ (2 : ℕ)) / y ^ (2 : ℕ) : ℝ) : ℂ)) x := by
      simpa using (continuousAt_const.add hpowC).div hpowC hx2C
    have htx : ContinuousAt (fun y : ℝ ↦ t * y) x := by
      fun_prop
    have hexp :
        ContinuousAt (fun y : ℝ ↦ Complex.exp (((t * y : ℝ) : ℂ) * Complex.I)) x := by
      exact Complex.continuous_exp.continuousAt.comp
        ((Complex.continuous_ofReal.continuousAt.comp htx).mul continuousAt_const)
    have hcorrReal : ContinuousAt (fun y : ℝ ↦ t * y / (1 + y ^ (2 : ℕ))) x := by
      exact htx.div (continuousAt_const.add hpow) hone_add_sq
    have hcorr : ContinuousAt
        (fun y : ℝ ↦ Complex.I * (t * y / (1 + y ^ (2 : ℕ)) : ℝ)) x := by
      exact continuousAt_const.mul (Complex.continuous_ofReal.continuousAt.comp hcorrReal)
    exact hpref.mul ((hexp.sub continuousAt_const).sub hcorr)

-- Proof sketch: on `|x| ≥ 1`, use the uniform estimate from the proof of Lemma 15.47; near the
-- origin, continuity gives local boundedness, so the whole range is bounded.
/-- The range of the textbook auxiliary function `f_t` is bounded in `ℂ`. -/
theorem isBounded_range_cltAuxiliaryFunction (t : ℝ) :
    Bornology.IsBounded (Set.range (cltAuxiliaryFunction t)) := by
  -- Bound the compact core `[-1,1]` by continuity, then use the exterior estimate outside it.
  obtain ⟨Ccore, hcore⟩ :=
    isCompact_Icc.exists_bound_of_continuousOn (f := cltAuxiliaryFunction t)
      (continuous_cltAuxiliaryFunction t).continuousOn
  refine (isBounded_iff_forall_norm_le).2 ?_
  refine ⟨max Ccore (4 + 2 * |t|), ?_⟩
  intro z hz
  rcases hz with ⟨x, rfl⟩
  by_cases hx : |x| ≤ 1
  · -- On the compact core, reuse the bound extracted from continuity.
    have hx_mem : x ∈ Set.Icc (-1 : ℝ) 1 := by
      simpa [abs_le] using hx
    exact (hcore x hx_mem).trans (le_max_left _ _)
  · -- Outside the core, the explicit textbook estimate is uniform.
    have hx' : 1 ≤ |x| := by
      linarith
    exact (norm_cltAuxiliaryFunction_le_of_one_le_abs t x hx').trans (le_max_right _ _)

-- Proof sketch: bundle the already established continuity and bounded-range statements into the
-- canonical owner object `ℝ →ᵇ ℂ` from `Definition_15_1`.
/-- Lemma 15.47: for every real `t`, the textbook auxiliary function `f_t` is canonically an
element of `C_b(ℝ, ℂ) = ℝ →ᵇ ℂ`. -/
def cltAuxiliaryFunctionBCF (t : ℝ) : ℝ →ᵇ ℂ :=
  { toContinuousMap := ⟨cltAuxiliaryFunction t, continuous_cltAuxiliaryFunction t⟩
    map_bounded' := Metric.isBounded_range_iff.1 (isBounded_range_cltAuxiliaryFunction t) }

/-- Coercing the bundled bounded continuous map from Lemma 15.47 recovers the explicit textbook
formula for `f_t`. -/
@[simp] theorem coe_cltAuxiliaryFunctionBCF (t : ℝ) :
    (cltAuxiliaryFunctionBCF t : ℝ → ℂ) = cltAuxiliaryFunction t := rfl
