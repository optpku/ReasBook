/-
Authors: Zichen Wang, Wanli Ma, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Mathlib

section Chap04
section Section05

open scoped Topology

/-- Definition 4.5.1 (Exponential function): for every real number x,
the exponential function is given by the power series
exp(x) := ∑' n : ℕ, x^n / n!. -/
noncomputable def realExpSeries (x : ℝ) : ℝ :=
  ∑' n : ℕ, x ^ n / (n.factorial : ℝ)

/-- Definition 4.5.2 (Euler's number): Euler's number `e` is the real number
defined by `e := exp(1)`, with series expansion `e = ∑' n : ℕ, 1 / n!`. -/
noncomputable def realEulerNumber : ℝ :=
  Real.exp 1

/-- Definition 4.5.3 (Natural logarithm): the natural logarithm is the function
`log : (0, ∞) → ℝ`, also denoted `ln`, defined as the inverse of `exp : ℝ → (0, ∞)`. -/
noncomputable def naturalLog : Set.Ioi (0 : ℝ) → ℝ :=
  fun x => Real.log x

/-- The restricted natural logarithm and exponential satisfy
`exp (naturalLog x) = x` for `x > 0` and `naturalLog (exp y) = y`. -/
theorem naturalLog_inverse_exp :
    (∀ x : Set.Ioi (0 : ℝ), Real.exp (naturalLog x) = x.1) ∧
    (∀ y : ℝ, naturalLog ⟨Real.exp y, Real.exp_pos y⟩ = y) := by
  constructor
  · intro x
    simpa [naturalLog] using (Real.exp_log x.2)
  · intro y
    simpa [naturalLog] using (Real.log_exp y)

/-- The defining series `∑ n, 1 / n!` for Euler's number is summable in `ℝ`. -/
lemma summable_one_div_factorial :
    Summable (fun n : ℕ => (1 : ℝ) / (n.factorial : ℝ)) := by
  simpa using (Real.summable_pow_div_factorial (1 : ℝ))

/-- Series characterization of Euler's number via the exponential series at `x = 1`. -/
lemma realEulerNumber_eq_tsum :
    realEulerNumber = ∑' n : ℕ, (1 : ℝ) / (n.factorial : ℝ) := by
  rw [realEulerNumber, Real.exp_eq_exp_ℝ]
  simpa using
    congrArg (fun f : ℝ → ℝ => f 1) (NormedSpace.exp_eq_tsum_div (𝔸 := ℝ))

/-- Helper for Proposition 4.5.1: rewrite `Real.exp x` as `(Real.exp 1) ^ x`. -/
lemma helperForProposition_4_5_1_exp_eq_expOne_rpow (x : ℝ) :
    Real.exp x = (Real.exp 1) ^ x := by
  simpa using (Real.exp_one_rpow x).symm

/-- Helper for Proposition 4.5.1: rewrite `(Real.exp 1) ^ x` using `realEulerNumber`. -/
lemma helperForProposition_4_5_1_realEulerNumber_rpow_rewrite (x : ℝ) :
    (Real.exp 1) ^ x = realEulerNumber ^ x := by
  simp [realEulerNumber]

/-- Proposition 4.5.1: for every real number `x`, the exponential function satisfies
`Real.exp x = realEulerNumber ^ x` (that is, `exp(x) = e^x`). -/
theorem real_exp_eq_eulerNumber_rpow :
    ∀ x : ℝ, Real.exp x = realEulerNumber ^ x := by
  intro x
  calc
    Real.exp x = (Real.exp 1) ^ x := helperForProposition_4_5_1_exp_eq_expOne_rpow x
    _ = realEulerNumber ^ x := helperForProposition_4_5_1_realEulerNumber_rpow_rewrite x

/-- Theorem 4.5.1 (Basic properties of exp, part (a)): for every real number `x`,
the series `∑' n : ℕ, x^n / n!` is absolutely convergent. In particular,
`Real.exp x = ∑' n : ℕ, x^n / n!` for all `x`, the associated power series has
infinite radius of convergence, and `Real.exp` is real analytic on `ℝ`. -/
theorem exp_basic_properties_part_a :
    (∀ x : ℝ, Summable (fun n : ℕ => |x ^ n / (n.factorial : ℝ)|)) ∧
    (∀ x : ℝ, Real.exp x = ∑' n : ℕ, x ^ n / (n.factorial : ℝ)) ∧
    (NormedSpace.expSeries ℝ ℝ).radius = ⊤ ∧
    AnalyticOn ℝ Real.exp Set.univ := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x
    refine Summable.congr (NormedSpace.norm_expSeries_div_summable (𝔸 := ℝ) (x := x)) ?_
    intro n
    rw [Real.norm_eq_abs]
  · intro x
    rw [Real.exp_eq_exp_ℝ]
    simpa using
      congrArg (fun f : ℝ → ℝ => f x) (NormedSpace.exp_eq_tsum_div (𝔸 := ℝ))
  · simpa using (NormedSpace.expSeries_radius_eq_top (𝕂 := ℝ) (𝔸 := ℝ))
  · simpa using (analyticOn_rexp : AnalyticOn ℝ Real.exp Set.univ)

/-- Theorem 4.5.2 (Basic properties of `exp`, part (b)): the function `exp : ℝ → ℝ`
is differentiable on `ℝ`, and for every `x : ℝ`, we have `exp'(x) = exp(x)`. -/
theorem exp_basic_properties_part_b :
    Differentiable ℝ Real.exp ∧ ∀ x : ℝ, deriv Real.exp x = Real.exp x := by
  constructor
  · simpa using (Real.differentiable_exp : Differentiable ℝ Real.exp)
  · intro x
    simpa using congrArg (fun f : ℝ → ℝ => f x) (Real.deriv_exp : deriv Real.exp = Real.exp)

/-- Theorem 4.5.3 (Basic properties of `exp`, part (c)): the function `exp` is
continuous on `ℝ`. Moreover, for every `a, b : ℝ`,
`∫ x in a..b, exp x = exp b - exp a`. -/
theorem exp_basic_properties_part_c :
    Continuous Real.exp ∧
    ∀ a b : ℝ, (∫ x in a..b, Real.exp x) = Real.exp b - Real.exp a := by
  constructor
  · simpa using (Real.continuous_exp : Continuous Real.exp)
  · intro a b
    simpa using (intervalIntegral.integral_exp a b)

/-- Theorem 4.5.4 (Basic properties of `exp`, part (d)): for all `x, y : ℝ`,
`exp (x + y) = exp x * exp y`. -/
theorem exp_basic_properties_part_d :
    ∀ x y : ℝ, Real.exp (x + y) = Real.exp x * Real.exp y := by
  intro x y
  simpa using (Real.exp_add x y)

/-- Theorem 4.5.5 (Basic properties of `exp`, part (e)): `exp 0 = 1`. Moreover,
for every `x : ℝ`, we have `exp x > 0` and `exp (-x) = 1 / exp x`. -/
theorem exp_basic_properties_part_e :
    Real.exp 0 = 1 ∧ ∀ x : ℝ, Real.exp x > 0 ∧ Real.exp (-x) = 1 / Real.exp x := by
  constructor
  · simpa using (Real.exp_zero : Real.exp 0 = 1)
  · intro x
    constructor
    · exact Real.exp_pos x
    · simpa [one_div] using (Real.exp_neg x)

/-- Theorem 4.5.6 (Basic properties of `exp`, part (f)): the function `exp` is
strictly increasing on `ℝ`. Equivalently, for all `x, y : ℝ`,
`y > x ↔ Real.exp y > Real.exp x`. -/
theorem exp_basic_properties_part_f :
    StrictMono Real.exp ∧ ∀ x y : ℝ, y > x ↔ Real.exp y > Real.exp x := by
  constructor
  · intro x y hxy
    exact (Real.exp_lt_exp).2 hxy
  · intro x y
    simpa [gt_iff_lt] using (Real.exp_lt_exp : Real.exp x < Real.exp y ↔ x < y).symm

/-- Helper for Theorem 4.5.7: derivative of `Real.log` at positive inputs. -/
lemma helperForTheorem_4_5_7_deriv_log_of_pos (x : ℝ) (_hx : 0 < x) :
    deriv Real.log x = 1 / x := by
  simpa [one_div] using (Real.deriv_log x)

/-- Helper for Theorem 4.5.7: positivity of the right endpoint from `0 < a < b`. -/
lemma helperForTheorem_4_5_7_rightEndpoint_pos
    (a b : ℝ) (ha : 0 < a) (hab : a < b) :
    0 < b := by
  exact lt_trans ha hab

/-- Helper for Theorem 4.5.7: integral of `1 / x` on a positive interval. -/
lemma helperForTheorem_4_5_7_integral_one_div_eq_log_div
    (a b : ℝ) (ha : 0 < a) (hab : a < b) :
    (∫ x in a..b, (1 / x)) = Real.log (b / a) := by
  have hb : 0 < b := helperForTheorem_4_5_7_rightEndpoint_pos a b ha hab
  simpa using integral_one_div_of_pos ha hb

/-- Helper for Theorem 4.5.7: convert `log (b / a)` into `log b - log a`. -/
lemma helperForTheorem_4_5_7_log_div_eq_sub
    (a b : ℝ) (ha : 0 < a) (hab : a < b) :
    Real.log (b / a) = Real.log b - Real.log a := by
  have hb : 0 < b := helperForTheorem_4_5_7_rightEndpoint_pos a b ha hab
  exact Real.log_div hb.ne' ha.ne'

/-- Theorem 4.5.7 (Logarithm properties, part (a)): for every `x > 0`,
the derivative of `ln` is `ln'(x) = 1 / x`. In particular, for any `0 < a < b`,
`∫ x in a..b, (1 / x) = ln(b) - ln(a)`. -/
theorem logarithm_properties_part_a :
    (∀ x : ℝ, 0 < x → deriv Real.log x = 1 / x) ∧
    (∀ a b : ℝ, 0 < a → a < b → (∫ x in a..b, (1 / x)) = Real.log b - Real.log a) := by
  constructor
  · intro x hx
    exact helperForTheorem_4_5_7_deriv_log_of_pos x hx
  · intro a b ha hab
    calc
      (∫ x in a..b, (1 / x)) = Real.log (b / a) :=
        helperForTheorem_4_5_7_integral_one_div_eq_log_div a b ha hab
      _ = Real.log b - Real.log a :=
        helperForTheorem_4_5_7_log_div_eq_sub a b ha hab

/-- Theorem 4.5.8 (Logarithm properties, part (b)): for all `x, y > 0`,
`ln (xy) = ln x + ln y`. -/
theorem logarithm_properties_part_b :
    ∀ x y : ℝ, 0 < x → 0 < y → Real.log (x * y) = Real.log x + Real.log y := by
  intro x y hx hy
  exact Real.log_mul (ne_of_gt hx) (ne_of_gt hy)

/-- Helper for Theorem 4.5.9: the logarithm of `1` is `0`. -/
lemma helperForTheorem_4_5_9_log_one : Real.log 1 = 0 := by
  simpa using (Real.log_one : Real.log 1 = 0)

/-- Helper for Theorem 4.5.9: reciprocal inside `log` gives negation. -/
lemma helperForTheorem_4_5_9_log_one_div_eq_neg_log (x : ℝ) :
    Real.log (1 / x) = -Real.log x := by
  simpa [one_div] using (Real.log_inv x)

/-- Helper for Theorem 4.5.9: the reciprocal-log identity in the `x > 0` form. -/
lemma helperForTheorem_4_5_9_log_one_div_eq_neg_log_of_pos (x : ℝ) (_hx : 0 < x) :
    Real.log (1 / x) = -Real.log x := by
  exact helperForTheorem_4_5_9_log_one_div_eq_neg_log x

/-- Theorem 4.5.9 (Logarithm properties, part (c)): `ln(1) = 0`. Moreover,
for every `x > 0`, `ln(1 / x) = -ln(x)`. -/
theorem logarithm_properties_part_c :
    Real.log 1 = 0 ∧ ∀ x : ℝ, 0 < x → Real.log (1 / x) = -Real.log x := by
  constructor
  · exact helperForTheorem_4_5_9_log_one
  · intro x hx
    exact helperForTheorem_4_5_9_log_one_div_eq_neg_log_of_pos x hx

/-- Helper for Theorem 4.5.10: rewrite `x ^ y` with the `exp (y * log x)`
definition when `x > 0`. -/
lemma helperForTheorem_4_5_10_rpow_def_of_pos {x y : ℝ} (hx : 0 < x) :
    x ^ y = Real.exp (y * Real.log x) := by
  calc
    x ^ y = Real.exp (Real.log x * y) := by
      simpa using (Real.rpow_def_of_pos hx y)
    _ = Real.exp (y * Real.log x) := by
      rw [mul_comm]

/-- Helper for Theorem 4.5.10: the logarithm of a real power for positive base. -/
lemma helperForTheorem_4_5_10_log_rpow_of_pos {x y : ℝ} (hx : 0 < x) :
    Real.log (x ^ y) = y * Real.log x := by
  simpa using (Real.log_rpow hx y)

/-- Theorem 4.5.10 (Logarithm properties, part (d)): for any `x > 0` and
`y : ℝ`, one has `ln (x^y) = y ln x`, where `x^y` is defined by
`x^y = exp (y ln x)`. -/
theorem logarithm_properties_part_d :
    ∀ x y : ℝ, 0 < x → Real.log (x ^ y) = y * Real.log x := by
  intro x y hx
  exact helperForTheorem_4_5_10_log_rpow_of_pos hx

/-- Helper for Theorem 4.5.11: the logarithm series identity on `(-1, 1)`. -/
lemma helperForTheorem_4_5_11_log_one_sub_eq_neg_tsum_of_mem_Ioo_neg_one_one
    {x : ℝ} (hx : x ∈ Set.Ioo (-1 : ℝ) 1) :
    Real.log (1 - x) = -∑' n : ℕ, x ^ (n + 1) / ((n + 1 : ℕ) : ℝ) := by
  rcases hx with ⟨hx_left, hx_right⟩
  have h_abs : |x| < 1 := by
    exact (abs_lt).2 ⟨hx_left, hx_right⟩
  have hHasSum := Real.hasSum_pow_div_log_of_abs_lt_one h_abs
  have hTsum : (∑' n : ℕ, x ^ (n + 1) / (↑n + 1)) = -Real.log (1 - x) := hHasSum.tsum_eq
  calc
    Real.log (1 - x) = -(-Real.log (1 - x)) := by ring
    _ = -∑' n : ℕ, x ^ (n + 1) / (↑n + 1) := by rw [← hTsum]
    _ = -∑' n : ℕ, x ^ (n + 1) / ((n + 1 : ℕ) : ℝ) := by simp [Nat.cast_add, Nat.cast_one]

/-- Helper for Theorem 4.5.11: rewrite the centered logarithm-series term. -/
lemma helperForTheorem_4_5_11_term_rewrite_center_one (x : ℝ) (n : ℕ) :
    ((-1 : ℝ) ^ n / ((n + 1 : ℕ) : ℝ)) * (x - 1) ^ (n + 1) =
      -((1 - x) ^ (n + 1) / ((n + 1 : ℕ) : ℝ)) := by
  let d : ℝ := ((n + 1 : ℕ) : ℝ)
  let p : ℝ := (x - 1) ^ (n + 1)
  have hbase : (1 - x) ^ (n + 1) = (-1 : ℝ) ^ (n + 1) * p := by
    dsimp [p]
    have hsub : 1 - x = (-1 : ℝ) * (x - 1) := by ring
    rw [hsub, mul_pow]
  calc
    ((-1 : ℝ) ^ n / d) * p = (((-1 : ℝ) ^ n) * p) / d := by ring
    _ = ((-((-1 : ℝ) ^ (n + 1))) * p) / d := by
      congr 1
      simp [pow_succ]
    _ = -(((-1 : ℝ) ^ (n + 1) * p) / d) := by ring
    _ = -((1 - x) ^ (n + 1) / d) := by rw [hbase]
    _ = -((1 - x) ^ (n + 1) / ((n + 1 : ℕ) : ℝ)) := by rfl

/-- Helper for Theorem 4.5.11: on `(0, 2)`, `log` equals its centered
power series at `1`, and that series is summable. -/
lemma helperForTheorem_4_5_11_log_eq_and_summable_inside_radius
    {x : ℝ} (hx : x ∈ Set.Ioo (0 : ℝ) 2) :
    (Real.log x = ∑' n : ℕ,
      ((-1 : ℝ) ^ n / ((n + 1 : ℕ) : ℝ)) * (x - 1) ^ (n + 1)) ∧
    Summable (fun n : ℕ =>
      ((-1 : ℝ) ^ n / ((n + 1 : ℕ) : ℝ)) * (x - 1) ^ (n + 1)) := by
  rcases hx with ⟨hx0, hx2⟩
  let u : ℝ := 1 - x
  have hu_abs : |u| < 1 := by
    have hu_left : -1 < u := by
      dsimp [u]
      linarith
    have hu_right : u < 1 := by
      dsimp [u]
      linarith
    exact (abs_lt).2 ⟨hu_left, hu_right⟩
  have hHasSum := Real.hasSum_pow_div_log_of_abs_lt_one hu_abs
  have hHasSumNeg : HasSum (fun n : ℕ => -(u ^ (n + 1) / (↑n + 1))) (Real.log (1 - u)) := by
    simpa using hHasSum.mul_left (-1 : ℝ)
  have hHasSumCenter :
      HasSum (fun n : ℕ =>
        ((-1 : ℝ) ^ n / (↑n + 1)) * (x - 1) ^ (n + 1)) (Real.log (1 - u)) := by
    refine hHasSumNeg.congr_fun ?_
    intro n
    dsimp [u]
    simpa [Nat.cast_add, Nat.cast_one] using
      helperForTheorem_4_5_11_term_rewrite_center_one x n
  have hHasSumCenter' :
      HasSum (fun n : ℕ =>
        ((-1 : ℝ) ^ n / (↑n + 1)) * (x - 1) ^ (n + 1)) (Real.log x) := by
    simpa [u] using hHasSumCenter
  refine ⟨?_, ?_⟩
  · simpa [Nat.cast_add, Nat.cast_one] using hHasSumCenter'.tsum_eq.symm
  · simpa [Nat.cast_add, Nat.cast_one] using hHasSumCenter'.summable

/-- Helper for Theorem 4.5.11: outside radius `1` about `1`, the centered
logarithm series is not summable. -/
lemma helperForTheorem_4_5_11_not_summable_outside_radius
    {x : ℝ} (hx : 1 < |x - 1|) :
    ¬Summable (fun n : ℕ =>
      ((-1 : ℝ) ^ n / ((n + 1 : ℕ) : ℝ)) * (x - 1) ^ (n + 1)) := by
  let f : ℕ → ℝ := fun n =>
    ((-1 : ℝ) ^ n / ((n + 1 : ℕ) : ℝ)) * (x - 1) ^ (n + 1)
  intro hs
  have hsNorm : Summable (fun n : ℕ => ‖f n‖) := hs.norm
  have hle : ∀ n : ℕ, (1 / ((n + 1 : ℕ) : ℝ)) ≤ ‖f n‖ := by
    intro n
    have hd : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by positivity
    have hden : (1 / ((n + 1 : ℕ) : ℝ)) = (1 / |((n + 1 : ℕ) : ℝ)|) := by
      rw [abs_of_pos hd]
    have hpow : (1 : ℝ) ≤ |x - 1| ^ (n + 1) := by
      have hbase : (1 : ℝ) ≤ |x - 1| := le_of_lt hx
      have hpow' :=
        pow_le_pow_left₀ (a := (1 : ℝ)) (b := |x - 1|) (by positivity) hbase (n + 1)
      simpa using hpow'
    have hAbsTerm :
        |(((-1 : ℝ) ^ n / ((n + 1 : ℕ) : ℝ)) * (x - 1) ^ (n + 1))| =
          (1 / |((n + 1 : ℕ) : ℝ)|) * |x - 1| ^ (n + 1) := by
      calc
        |(((-1 : ℝ) ^ n / ((n + 1 : ℕ) : ℝ)) * (x - 1) ^ (n + 1))|
            = |(-1 : ℝ) ^ n / ((n + 1 : ℕ) : ℝ)| * |(x - 1) ^ (n + 1)| := by
                rw [abs_mul]
        _ = (|(-1 : ℝ)| ^ n / |((n + 1 : ℕ) : ℝ)|) * |x - 1| ^ (n + 1) := by
                rw [abs_div, abs_pow, abs_pow]
        _ = (1 / |((n + 1 : ℕ) : ℝ)|) * |x - 1| ^ (n + 1) := by
                have h1 : |(-1 : ℝ)| ^ n = 1 := by simp
                rw [h1]
    have hnorm_eq :
        ‖f n‖ = |(((-1 : ℝ) ^ n / ((n + 1 : ℕ) : ℝ)) * (x - 1) ^ (n + 1))| := by
      dsimp [f]
    calc
      (1 / ((n + 1 : ℕ) : ℝ)) = (1 / |((n + 1 : ℕ) : ℝ)|) := hden
      _ = (1 / |((n + 1 : ℕ) : ℝ)|) * 1 := by ring
      _ ≤ (1 / |((n + 1 : ℕ) : ℝ)|) * |x - 1| ^ (n + 1) := by
            have hnonneg : 0 ≤ (1 / |((n + 1 : ℕ) : ℝ)|) := by positivity
            exact mul_le_mul_of_nonneg_left hpow hnonneg
      _ = |(((-1 : ℝ) ^ n / ((n + 1 : ℕ) : ℝ)) * (x - 1) ^ (n + 1))| := by
            rw [hAbsTerm]
      _ = ‖f n‖ := by
            exact hnorm_eq.symm
  have hsHarmShift : Summable (fun n : ℕ => (1 : ℝ) / ((n + 1 : ℕ) : ℝ)) :=
    Summable.of_nonneg_of_le
      (fun n : ℕ => by positivity)
      hle
      hsNorm
  have hsHarm : Summable (fun n : ℕ => (1 : ℝ) / (n : ℝ)) :=
    (summable_nat_add_iff 1).1 (by
      simpa [Nat.cast_add, Nat.cast_one, add_comm, add_left_comm, add_assoc] using hsHarmShift)
  exact Real.not_summable_one_div_natCast hsHarm

theorem logarithm_properties_part_e :
    (∀ x : ℝ, x ∈ Set.Ioo (-1 : ℝ) 1 →
      Real.log (1 - x) =
        -∑' n : ℕ, x ^ (n + 1) / ((n + 1 : ℕ) : ℝ)) ∧
    AnalyticAt ℝ Real.log 1 ∧
    (∀ x : ℝ, x ∈ Set.Ioo (0 : ℝ) 2 →
      Real.log x =
        ∑' n : ℕ,
          ((-1 : ℝ) ^ n / ((n + 1 : ℕ) : ℝ)) * (x - 1) ^ (n + 1)) ∧
    (∀ x : ℝ, |x - 1| < 1 →
      Summable
        (fun n : ℕ =>
          ((-1 : ℝ) ^ n / ((n + 1 : ℕ) : ℝ)) * (x - 1) ^ (n + 1))) ∧
    (∀ x : ℝ, 1 < |x - 1| →
      ¬Summable
        (fun n : ℕ =>
          ((-1 : ℝ) ^ n / ((n + 1 : ℕ) : ℝ)) * (x - 1) ^ (n + 1))) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro x hx
    exact helperForTheorem_4_5_11_log_one_sub_eq_neg_tsum_of_mem_Ioo_neg_one_one hx
  · simpa using (analyticAt_log (x := (1 : ℝ)) (by norm_num : (0 : ℝ) < 1))
  · intro x hx
    exact (helperForTheorem_4_5_11_log_eq_and_summable_inside_radius hx).1
  · intro x hx
    have hxAbs := (abs_lt.mp hx)
    have hx0 : 0 < x := by linarith [hxAbs.1]
    have hx2 : x < 2 := by linarith [hxAbs.2]
    exact (helperForTheorem_4_5_11_log_eq_and_summable_inside_radius ⟨hx0, hx2⟩).2
  · intro x hx
    exact helperForTheorem_4_5_11_not_summable_outside_radius hx

/-- Helper for Proposition 4.5.2: each alternating-harmonic term has absolute value
`1 / (n + 1)`. -/
lemma helperForProposition_4_5_2_abs_alternating_harmonic_term
    (n : ℕ) :
    |(-1 : ℝ) ^ n / ((n + 1 : ℕ) : ℝ)| = (1 : ℝ) / ((n + 1 : ℕ) : ℝ) := by
  have hdenNonneg : (0 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by positivity
  calc
    |(-1 : ℝ) ^ n / ((n + 1 : ℕ) : ℝ)|
        = |(-1 : ℝ) ^ n| / |((n + 1 : ℕ) : ℝ)| := by rw [abs_div]
    _ = (1 : ℝ) / |((n + 1 : ℕ) : ℝ)| := by simp
    _ = (1 : ℝ) / ((n + 1 : ℕ) : ℝ) := by rw [abs_of_nonneg hdenNonneg]

/-- Helper for Proposition 4.5.2: unconditional summability of the alternating
harmonic series implies summability of the harmonic series. -/
lemma helperForProposition_4_5_2_summable_alternating_implies_summable_harmonic :
    Summable (fun n : ℕ => (-1 : ℝ) ^ n / ((n + 1 : ℕ) : ℝ)) →
      Summable (fun n : ℕ => (1 : ℝ) / (n : ℝ)) := by
  intro hAlt
  have hAbs : Summable (fun n : ℕ => |(-1 : ℝ) ^ n / ((n + 1 : ℕ) : ℝ)|) := hAlt.abs
  have hShiftHarmonic : Summable (fun n : ℕ => (1 : ℝ) / ((n + 1 : ℕ) : ℝ)) := by
    refine hAbs.congr ?_
    intro n
    simpa using helperForProposition_4_5_2_abs_alternating_harmonic_term n
  exact (summable_nat_add_iff 1).1 (by
    simpa [Nat.cast_add, Nat.cast_one, add_assoc, add_comm, add_left_comm] using hShiftHarmonic)

/-- Helper for Proposition 4.5.2: under Lean's default (unconditional) `Summable`,
the alternating harmonic series is not summable. -/
lemma helperForProposition_4_5_2_not_summable_unconditional_alternating_harmonic :
    ¬ Summable (fun n : ℕ => (-1 : ℝ) ^ n / ((n + 1 : ℕ) : ℝ)) := by
  intro hAlt
  exact Real.not_summable_one_div_natCast
    (helperForProposition_4_5_2_summable_alternating_implies_summable_harmonic hAlt)

/-- Helper for Proposition 4.5.2: any putative witness of the target conjunction
would force a `Summable` claim that is already refuted under Lean's
unconditional `Summable` semantics on `ℕ`. -/
lemma helperForProposition_4_5_2_target_conjunction_implies_not_summable :
    (Summable (fun n : ℕ => (-1 : ℝ) ^ n / ((n + 1 : ℕ) : ℝ)) ∧
      (∑' n : ℕ, (-1 : ℝ) ^ n / ((n + 1 : ℕ) : ℝ)) = Real.log 2) →
      ¬ Summable (fun n : ℕ => (-1 : ℝ) ^ n / ((n + 1 : ℕ) : ℝ)) := by
  intro _h
  exact helperForProposition_4_5_2_not_summable_unconditional_alternating_harmonic

/-- Helper for Proposition 4.5.2: `Real.log 2` is nonzero. -/
lemma helperForProposition_4_5_2_log_two_ne_zero :
    Real.log 2 ≠ (0 : ℝ) := by
  exact ne_of_gt (Real.log_pos (by norm_num : (1 : ℝ) < 2))

/-- Helper for Proposition 4.5.2: under Lean's default unconditional `Summable`
semantics on `ℕ`, the alternating-harmonic `tsum` is forced to be `0`. -/
lemma helperForProposition_4_5_2_tsum_eq_zero_unconditional :
    (∑' n : ℕ, (-1 : ℝ) ^ n / ((n + 1 : ℕ) : ℝ)) = 0 := by
  exact tsum_eq_zero_of_not_summable
    helperForProposition_4_5_2_not_summable_unconditional_alternating_harmonic

/-- Helper for Proposition 4.5.2: under Lean's default unconditional `Summable`
semantics on `ℕ`, the asserted `tsum = log 2` identity cannot hold. -/
lemma helperForProposition_4_5_2_not_tsum_eq_log_two_unconditional :
    ¬ ((∑' n : ℕ, (-1 : ℝ) ^ n / ((n + 1 : ℕ) : ℝ)) = Real.log 2) := by
  intro hEq
  have hLogTwoEqZero : Real.log 2 = 0 :=
    hEq.symm.trans helperForProposition_4_5_2_tsum_eq_zero_unconditional
  exact helperForProposition_4_5_2_log_two_ne_zero hLogTwoEqZero

/-- Helper for Proposition 4.5.2: any proof of the target conjunction forces
`Real.log 2 = 0` under unconditional `tsum` semantics. -/
lemma helperForProposition_4_5_2_target_conjunction_implies_log_two_eq_zero :
    (Summable (fun n : ℕ => (-1 : ℝ) ^ n / ((n + 1 : ℕ) : ℝ)) ∧
      (∑' n : ℕ, (-1 : ℝ) ^ n / ((n + 1 : ℕ) : ℝ)) = Real.log 2) →
      Real.log 2 = 0 := by
  intro h
  have hTsumZero :
      (∑' n : ℕ, (-1 : ℝ) ^ n / ((n + 1 : ℕ) : ℝ)) = 0 :=
    helperForProposition_4_5_2_tsum_eq_zero_unconditional
  exact h.2.symm.trans hTsumZero

/-- Helper for Proposition 4.5.2: any proof of the target conjunction directly
contradicts `Real.log 2 ≠ 0`. -/
lemma helperForProposition_4_5_2_target_conjunction_implies_false_via_log_two :
    (Summable (fun n : ℕ => (-1 : ℝ) ^ n / ((n + 1 : ℕ) : ℝ)) ∧
      (∑' n : ℕ, (-1 : ℝ) ^ n / ((n + 1 : ℕ) : ℝ)) = Real.log 2) → False := by
  intro h
  exact helperForProposition_4_5_2_log_two_ne_zero
    (helperForProposition_4_5_2_target_conjunction_implies_log_two_eq_zero h)

/-- Helper for Proposition 4.5.2: the target conjunction is inconsistent under
Lean's default (unconditional) `Summable` on `ℕ`. -/
lemma helperForProposition_4_5_2_not_target_conjunction_unconditional :
    ¬ (Summable (fun n : ℕ => (-1 : ℝ) ^ n / ((n + 1 : ℕ) : ℝ)) ∧
      (∑' n : ℕ, (-1 : ℝ) ^ n / ((n + 1 : ℕ) : ℝ)) = Real.log 2) := by
  intro h
  exact helperForProposition_4_5_2_not_tsum_eq_log_two_unconditional h.2

/-- Helper for Proposition 4.5.2: any proof of the target conjunction would force
summability of the (unshifted) harmonic series. -/
lemma helperForProposition_4_5_2_target_conjunction_implies_summable_harmonic :
    (Summable (fun n : ℕ => (-1 : ℝ) ^ n / ((n + 1 : ℕ) : ℝ)) ∧
      (∑' n : ℕ, (-1 : ℝ) ^ n / ((n + 1 : ℕ) : ℝ)) = Real.log 2) →
      Summable (fun n : ℕ => (1 : ℝ) / (n : ℝ)) := by
  intro h
  exact helperForProposition_4_5_2_summable_alternating_implies_summable_harmonic h.1

/-- Helper for Proposition 4.5.2: the target conjunction yields a contradiction
with `Real.not_summable_one_div_natCast`. -/
lemma helperForProposition_4_5_2_target_conjunction_implies_false_via_harmonic :
    (Summable (fun n : ℕ => (-1 : ℝ) ^ n / ((n + 1 : ℕ) : ℝ)) ∧
      (∑' n : ℕ, (-1 : ℝ) ^ n / ((n + 1 : ℕ) : ℝ)) = Real.log 2) → False := by
  intro h
  exact Real.not_summable_one_div_natCast
    (helperForProposition_4_5_2_target_conjunction_implies_summable_harmonic h)

/-- Helper for Proposition 4.5.2: contradiction with harmonic divergence yields
direct negation of the target conjunction. -/
lemma helperForProposition_4_5_2_not_target_conjunction_via_harmonic_divergence :
    ¬ (Summable (fun n : ℕ => (-1 : ℝ) ^ n / ((n + 1 : ℕ) : ℝ)) ∧
      (∑' n : ℕ, (-1 : ℝ) ^ n / ((n + 1 : ℕ) : ℝ)) = Real.log 2) := by
  intro h
  exact helperForProposition_4_5_2_target_conjunction_implies_false_via_harmonic h

/-- Helper for Proposition 4.5.2: under Lean's default unconditional `Summable`
semantics on `ℕ`, the target conjunction is equivalent to `False`. -/
lemma helperForProposition_4_5_2_target_conjunction_iff_false :
    (Summable (fun n : ℕ => (-1 : ℝ) ^ n / ((n + 1 : ℕ) : ℝ)) ∧
      (∑' n : ℕ, (-1 : ℝ) ^ n / ((n + 1 : ℕ) : ℝ)) = Real.log 2) ↔ False := by
  constructor
  · intro h
    exact helperForProposition_4_5_2_not_target_conjunction_unconditional h
  · intro h
    exact False.elim h

/-- Helper for Proposition 4.5.2: under Lean's default unconditional
`Summable` semantics on `ℕ`, both asserted claims in the target conjunction are
blocked. -/
lemma helperForProposition_4_5_2_unconditional_obstructions :
    (¬ Summable (fun n : ℕ => (-1 : ℝ) ^ n / ((n + 1 : ℕ) : ℝ))) ∧
    ¬ ((∑' n : ℕ, (-1 : ℝ) ^ n / ((n + 1 : ℕ) : ℝ)) = Real.log 2) := by
  refine ⟨
    helperForProposition_4_5_2_not_summable_unconditional_alternating_harmonic,
    helperForProposition_4_5_2_not_tsum_eq_log_two_unconditional
  ⟩

/-- Helper for Proposition 4.5.2: the alternating harmonic partial sums converge
conditionally (as a limit of finite sums), even though unconditional
`Summable` on `ℕ` fails for this series in Lean. -/
lemma helperForProposition_4_5_2_partial_sums_tendsto_some_limit :
    ∃ l : ℝ, Filter.Tendsto
      (fun n : ℕ => ∑ i ∈ Finset.range n, (-1 : ℝ) ^ i / ((i + 1 : ℕ) : ℝ))
      Filter.atTop (nhds l) := by
  have hAntitone : Antitone (fun n : ℕ => (1 : ℝ) / ((n + 1 : ℕ) : ℝ)) := by
    intro m n hmn
    simpa [Nat.cast_add, Nat.cast_one, add_assoc, add_comm, add_left_comm] using
      (Nat.one_div_le_one_div (α := ℝ) hmn)
  have hZero : Filter.Tendsto
      (fun n : ℕ => (1 : ℝ) / ((n + 1 : ℕ) : ℝ))
      Filter.atTop (nhds (0 : ℝ)) := by
    simpa [Nat.cast_add, Nat.cast_one, add_assoc, add_comm, add_left_comm] using
      (tendsto_one_div_add_atTop_nhds_zero_nat :
        Filter.Tendsto (fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 1))
          Filter.atTop (nhds (0 : ℝ)))
  obtain ⟨l, hl⟩ := Antitone.tendsto_alternating_series_of_tendsto_zero hAntitone hZero
  refine ⟨l, ?_⟩
  convert hl using 1 with n
  simp [div_eq_mul_inv]

/-- Helper for Proposition 4.5.2: if the target conjunction held, then the ordered
partial sums would converge to `Real.log 2`. -/
lemma helperForProposition_4_5_2_target_conjunction_implies_partial_sums_tendsto_log_two :
    (Summable (fun n : ℕ => (-1 : ℝ) ^ n / ((n + 1 : ℕ) : ℝ)) ∧
      (∑' n : ℕ, (-1 : ℝ) ^ n / ((n + 1 : ℕ) : ℝ)) = Real.log 2) →
      Filter.Tendsto
        (fun n : ℕ => ∑ i ∈ Finset.range n, (-1 : ℝ) ^ i / ((i + 1 : ℕ) : ℝ))
        Filter.atTop (nhds (Real.log 2)) := by
  intro h
  have hTendstoTsum :
      Filter.Tendsto
        (fun n : ℕ => ∑ i ∈ Finset.range n, (-1 : ℝ) ^ i / ((i + 1 : ℕ) : ℝ))
        Filter.atTop
        (nhds (∑' n : ℕ, (-1 : ℝ) ^ n / ((n + 1 : ℕ) : ℝ))) := by
    exact Summable.tendsto_sum_tsum_nat h.1
  exact h.2 ▸ hTendstoTsum

/-- Helper for Proposition 4.5.2: the limit of alternating-harmonic partial sums,
when it exists, is unique. -/
lemma helperForProposition_4_5_2_partial_sums_limit_unique
    {l₁ l₂ : ℝ}
    (h₁ : Filter.Tendsto
      (fun n : ℕ => ∑ i ∈ Finset.range n, (-1 : ℝ) ^ i / ((i + 1 : ℕ) : ℝ))
      Filter.atTop (nhds l₁))
    (h₂ : Filter.Tendsto
      (fun n : ℕ => ∑ i ∈ Finset.range n, (-1 : ℝ) ^ i / ((i + 1 : ℕ) : ℝ))
      Filter.atTop (nhds l₂)) :
    l₁ = l₂ := by
  exact tendsto_nhds_unique h₁ h₂

/-- Helper for Proposition 4.5.2: under the target conjunction, any candidate
limit of alternating-harmonic partial sums must equal `Real.log 2`. -/
lemma helperForProposition_4_5_2_target_conjunction_forces_unique_limit_log_two
    (h : Summable (fun n : ℕ => (-1 : ℝ) ^ n / ((n + 1 : ℕ) : ℝ)) ∧
      (∑' n : ℕ, (-1 : ℝ) ^ n / ((n + 1 : ℕ) : ℝ)) = Real.log 2)
    {l : ℝ}
    (hl : Filter.Tendsto
      (fun n : ℕ => ∑ i ∈ Finset.range n, (-1 : ℝ) ^ i / ((i + 1 : ℕ) : ℝ))
      Filter.atTop (nhds l)) :
    l = Real.log 2 := by
  exact helperForProposition_4_5_2_partial_sums_limit_unique hl
    (helperForProposition_4_5_2_target_conjunction_implies_partial_sums_tendsto_log_two h)

/-- Proposition 4.5.2: the alternating harmonic series converges to `ln(2)`,
encoded in Lean as convergence of ordered partial sums:
`∑_{n=1}^∞ (-1)^{n+1}/n = ln(2)` becomes
`Tendsto (fun N => ∑ n < N, (-1)^n/(n+1)) atTop (𝓝 (log 2))`. -/
theorem alternating_harmonic_summable_and_tsum_eq_log_two :
    Filter.Tendsto
      (fun N : ℕ => ∑ n ∈ Finset.range N, (-1 : ℝ) ^ n / ((n + 1 : ℕ) : ℝ))
      Filter.atTop
      (nhds (Real.log 2)) := by
  obtain ⟨l, hlim⟩ := helperForProposition_4_5_2_partial_sums_tendsto_some_limit
  have hAbel :
      Filter.Tendsto
        (fun x : ℝ => ∑' n : ℕ, ((-1 : ℝ) ^ n / ((n + 1 : ℕ) : ℝ)) * x ^ n)
        (𝓝[<] (1 : ℝ))
        (nhds l) := by
    exact Real.tendsto_tsum_powerSeries_nhdsWithin_lt hlim
  have hAbelLog :
      Filter.Tendsto
        (fun x : ℝ => Real.log (1 + x) / x)
        (𝓝[<] (1 : ℝ))
        (nhds l) := by
    refine hAbel.congr' ?_
    filter_upwards [Ioo_mem_nhdsLT (show (1 / 2 : ℝ) < 1 by norm_num)] with x hx
    have hx_pos : 0 < x := by linarith [hx.1]
    have hx_ne : x ≠ 0 := ne_of_gt hx_pos
    have hx_abs_neg : |(-x : ℝ)| < 1 := by
      rw [abs_neg, abs_lt]
      constructor <;> linarith [hx.1, hx.2]
    have hHasSumScaled :
        HasSum
          (fun n : ℕ => ((-x : ℝ)⁻¹) * ((-x : ℝ) ^ (n + 1) / ((n + 1 : ℕ) : ℝ)))
          (((-x : ℝ)⁻¹) * (-Real.log (1 - (-x : ℝ)))) := by
      simpa using
        (Real.hasSum_pow_div_log_of_abs_lt_one (x := -x) hx_abs_neg).mul_left ((-x : ℝ)⁻¹)
    have hSeriesEq :
        (∑' n : ℕ, ((-1 : ℝ) ^ n / ((n + 1 : ℕ) : ℝ)) * x ^ n) = Real.log (1 + x) / x := by
      calc
        (∑' n : ℕ, ((-1 : ℝ) ^ n / ((n + 1 : ℕ) : ℝ)) * x ^ n)
            = ∑' n : ℕ, ((-x : ℝ)⁻¹) * ((-x : ℝ) ^ (n + 1) / ((n + 1 : ℕ) : ℝ)) := by
                apply tsum_congr
                intro n
                have hnegx_ne : (-x : ℝ) ≠ 0 := neg_ne_zero.mpr hx_ne
                calc
                  ((-1 : ℝ) ^ n / ((n + 1 : ℕ) : ℝ)) * x ^ n
                      = (((-1 : ℝ) ^ n) * x ^ n) / ((n + 1 : ℕ) : ℝ) := by ring
                  _ = ((-x : ℝ) ^ n) / ((n + 1 : ℕ) : ℝ) := by
                        congr 1
                        simpa [neg_mul, one_mul] using (mul_pow (-1 : ℝ) x n).symm
                  _ = ((-x : ℝ)⁻¹) * ((-x : ℝ) ^ (n + 1) / ((n + 1 : ℕ) : ℝ)) := by
                        rw [pow_succ]
                        field_simp [hnegx_ne]
        _ = ((-x : ℝ)⁻¹) * (-Real.log (1 - (-x : ℝ))) := hHasSumScaled.tsum_eq
        _ = Real.log (1 + x) / x := by
              calc
                ((-x : ℝ)⁻¹) * (-Real.log (1 - (-x : ℝ)))
                    = (-(x⁻¹)) * (-Real.log (1 + x)) := by simp
                _ = x⁻¹ * Real.log (1 + x) := by ring
                _ = Real.log (1 + x) / x := by
                      rw [div_eq_mul_inv, mul_comm]
    exact hSeriesEq
  have hLogCont :
      Filter.Tendsto
        (fun x : ℝ => Real.log (1 + x) / x)
        (𝓝[<] (1 : ℝ))
        (nhds (Real.log 2)) := by
    have hContAt :
        ContinuousAt (fun x : ℝ => Real.log (1 + x) / x) (1 : ℝ) := by
      refine ((Real.continuousAt_log (by norm_num : (1 + (1 : ℝ)) ≠ 0)).comp ?_).div
        continuousAt_id (by norm_num)
      simpa using (continuousAt_const.add continuousAt_id)
    have hNhd :
        Filter.Tendsto
          (fun x : ℝ => Real.log (1 + x) / x)
          (nhds (1 : ℝ))
          (nhds (Real.log 2)) := by
      convert hContAt.tendsto using 1
      norm_num
    exact hNhd.mono_left (tendsto_nhdsWithin_of_tendsto_nhds fun _ h => h)
  have hl : l = Real.log 2 := tendsto_nhds_unique hAbelLog hLogCont
  simpa [hl] using hlim

end Section05
end Chap04
