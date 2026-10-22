/-
Authors: Zichen Wang, Wanli Ma, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Mathlib

section Chap04
section Section07

/-- Definition 4.7.1 (Trigonometric functions): for each `z : ℂ`,
`cos z = (exp (i z) + exp (-i z)) / 2` and
`sin z = (exp (i z) - exp (-i z)) / (2i)`. -/
theorem complex_trigonometric_function_definitions (z : ℂ) :
    Complex.cos z = (Complex.exp (Complex.I * z) + Complex.exp (-(Complex.I * z))) / (2 : ℂ) ∧
    Complex.sin z = (Complex.exp (Complex.I * z) - Complex.exp (-(Complex.I * z))) /
      ((2 : ℂ) * Complex.I) := by
  constructor
  · simp [Complex.cos, mul_comm]
  · simp [Complex.sin, div_eq_mul_inv, Complex.inv_I, mul_comm, mul_left_comm, mul_assoc]
    ring

/-- Helper for Proposition 4.7.1: the absolute-value even cosine-series coefficients are
summable over `ℝ`. -/
lemma helperForProposition_4_7_1_abs_even_series_summable (x : ℝ) :
    Summable (fun n : ℕ => |(((-1 : ℝ) ^ n * x ^ (2 * n)) / (Nat.factorial (2 * n) : ℝ))|) := by
  simpa [abs_mul, abs_div, abs_pow] using (Real.hasSum_cosh |x|).summable

/-- Helper for Proposition 4.7.1: the absolute-value odd sine-series coefficients are
summable over `ℝ`. -/
lemma helperForProposition_4_7_1_abs_odd_series_summable (x : ℝ) :
    Summable
      (fun n : ℕ => |(((-1 : ℝ) ^ n * x ^ (2 * n + 1)) / (Nat.factorial (2 * n + 1) : ℝ))|) := by
  simpa [abs_mul, abs_div, abs_pow] using (Real.hasSum_sinh |x|).summable

/-- Helper for Proposition 4.7.1: the signed cosine and sine coefficient series are
summable over `ℝ`. -/
lemma helperForProposition_4_7_1_signed_series_summable (x : ℝ) :
    Summable (fun n : ℕ => (((-1 : ℝ) ^ n) * x ^ (2 * n)) / (Nat.factorial (2 * n) : ℝ)) ∧
    Summable (fun n : ℕ => (((-1 : ℝ) ^ n) * x ^ (2 * n + 1)) / (Nat.factorial (2 * n + 1) : ℝ)) := by
  constructor
  · simpa [mul_comm, mul_left_comm, mul_assoc, div_eq_mul_inv] using (Real.hasSum_cos x).summable
  · simpa [mul_comm, mul_left_comm, mul_assoc, div_eq_mul_inv] using (Real.hasSum_sin x).summable

/-- Helper for Proposition 4.7.1: assemble the final conjunction for the let-bound
series definitions. -/
lemma helperForProposition_4_7_1_assemble_let_bound_goal (x : ℝ) :
    let a : ℕ → ℝ :=
      fun n => (((-1 : ℝ) ^ n) * x ^ (2 * n)) / (Nat.factorial (2 * n) : ℝ)
    let b : ℕ → ℝ :=
      fun n => (((-1 : ℝ) ^ n) * x ^ (2 * n + 1)) / (Nat.factorial (2 * n + 1) : ℝ)
    Summable (fun n : ℕ => |a n|) ∧
    Summable (fun n : ℕ => |b n|) ∧
    Summable a ∧ Summable b := by
  dsimp
  rcases helperForProposition_4_7_1_signed_series_summable x with ⟨hEvenSigned, hOddSigned⟩
  exact ⟨
    helperForProposition_4_7_1_abs_even_series_summable x,
    helperForProposition_4_7_1_abs_odd_series_summable x,
    hEvenSigned,
    hOddSigned
  ⟩

/-- Proposition 4.7.1 (Reality and absolute convergence on `ℝ`): for every `x : ℝ`,
the series `∑' n, (-1)^n * x^(2n) / (2n)!` and `∑' n, (-1)^n * x^(2n+1) / (2n+1)!`
converge absolutely. Consequently, defining `cos(x)` and `sin(x)` by these series
gives real-valued quantities for each real input. -/
theorem real_trigonometric_series_absolutely_convergent (x : ℝ) :
    let a : ℕ → ℝ :=
      fun n => (((-1 : ℝ) ^ n) * x ^ (2 * n)) / (Nat.factorial (2 * n) : ℝ)
    let b : ℕ → ℝ :=
      fun n => (((-1 : ℝ) ^ n) * x ^ (2 * n + 1)) / (Nat.factorial (2 * n + 1) : ℝ)
    Summable (fun n : ℕ => |a n|) ∧
    Summable (fun n : ℕ => |b n|) ∧
    Summable a ∧ Summable b := by
  simpa using helperForProposition_4_7_1_assemble_let_bound_goal x

/-- Helper for Proposition 4.7.2: a nonzero derivative at `x₀` forces nearby punctured
points to have function value different from `f x₀`. -/
lemma helperForProposition_4_7_2_eventually_ne_value_at_x0
    (f : ℝ → ℝ) (x₀ : ℝ)
    (hf_diff : DifferentiableAt ℝ f x₀)
    (hf_deriv_ne_zero : deriv f x₀ ≠ 0) :
    ∀ᶠ y in nhdsWithin x₀ (({x₀} : Set ℝ)ᶜ), f y ≠ f x₀ := by
  simpa [nhdsWithin, Set.compl_singleton_eq] using
    (hf_diff.hasDerivAt.eventually_ne (c := f x₀) hf_deriv_ne_zero)

/-- Helper for Proposition 4.7.2: rewriting local inequality against `f x₀` as local
inequality against `0` when `f x₀ = 0`. -/
lemma helperForProposition_4_7_2_eventually_ne_zero
    (f : ℝ → ℝ) (x₀ : ℝ)
    (hf_zero : f x₀ = 0)
    (h_ne_value_at_x0 : ∀ᶠ y in nhdsWithin x₀ (({x₀} : Set ℝ)ᶜ), f y ≠ f x₀) :
    ∀ᶠ y in nhdsWithin x₀ (({x₀} : Set ℝ)ᶜ), f y ≠ 0 := by
  filter_upwards [h_ne_value_at_x0] with y hy
  simpa [hf_zero] using hy

/-- Helper for Proposition 4.7.2: an eventual punctured-neighborhood property yields a
positive radius with the textbook `0 < |y - x₀| < c` form. -/
lemma helperForProposition_4_7_2_radius_from_eventually_punctured
    (x₀ : ℝ) {P : ℝ → Prop}
    (hP : ∀ᶠ y in nhdsWithin x₀ (({x₀} : Set ℝ)ᶜ), P y) :
    ∃ c > 0, ∀ y : ℝ, 0 < |y - x₀| ∧ |y - x₀| < c → P y := by
  rcases (Metric.mem_nhdsWithin_iff.mp hP) with ⟨c, hc_pos, hc_subset⟩
  refine ⟨c, hc_pos, ?_⟩
  intro y hy
  rcases hy with ⟨hy_pos, hy_lt⟩
  have hy_ball : y ∈ Metric.ball x₀ c := by
    rw [Metric.mem_ball, Real.dist_eq]
    simpa [abs_sub_comm] using hy_lt
  have hy_ne : y ≠ x₀ := by
    exact sub_ne_zero.mp (abs_pos.mp hy_pos)
  have hy_punctured : y ∈ ({x₀} : Set ℝ)ᶜ := by
    simp [hy_ne]
  exact hc_subset ⟨hy_ball, hy_punctured⟩

/-- Proposition 4.7.2: If `f : ℝ → ℝ` is differentiable at `x₀`, with `f x₀ = 0`
and `f' x₀ ≠ 0`, then there exists `c > 0` such that for every `y : ℝ`,
`0 < |y - x₀| < c` implies `f y ≠ 0`. -/
theorem isolated_zero_of_differentiableAt_deriv_ne_zero
    (f : ℝ → ℝ) (x₀ : ℝ)
    (hf_diff : DifferentiableAt ℝ f x₀)
    (hf_zero : f x₀ = 0)
    (hf_deriv_ne_zero : deriv f x₀ ≠ 0) :
    ∃ c > 0, ∀ y : ℝ, 0 < |y - x₀| ∧ |y - x₀| < c → f y ≠ 0 := by
  have h_ne_value_at_x0 : ∀ᶠ y in nhdsWithin x₀ (({x₀} : Set ℝ)ᶜ), f y ≠ f x₀ :=
    helperForProposition_4_7_2_eventually_ne_value_at_x0 f x₀ hf_diff hf_deriv_ne_zero
  have h_ne_zero : ∀ᶠ y in nhdsWithin x₀ (({x₀} : Set ℝ)ᶜ), f y ≠ 0 :=
    helperForProposition_4_7_2_eventually_ne_zero f x₀ hf_zero h_ne_value_at_x0
  exact helperForProposition_4_7_2_radius_from_eventually_punctured x₀ h_ne_zero

/-- Proposition 4.7.3: There exists a real number `c > 0` such that for every
real `x` with `0 < x < c`, one has `sin x ≠ 0`. -/
theorem exists_pos_radius_sine_ne_zero_right_of_zero :
    ∃ c > 0, ∀ x : ℝ, 0 < x ∧ x < c → Real.sin x ≠ 0 := by
  have hdiff : DifferentiableAt ℝ Real.sin 0 := (Real.hasDerivAt_sin 0).differentiableAt
  have hderiv_ne_zero : deriv Real.sin 0 ≠ 0 := by
    rw [(Real.hasDerivAt_sin 0).deriv]
    simp [Real.cos_zero]
  rcases
    isolated_zero_of_differentiableAt_deriv_ne_zero
      Real.sin 0 hdiff Real.sin_zero hderiv_ne_zero with ⟨c, hc_pos, hc_nonzero⟩
  refine ⟨c, hc_pos, ?_⟩
  intro x hx
  rcases hx with ⟨hx_pos, hx_lt⟩
  have hx_abs : |x - 0| = x := by
    simpa using (abs_of_pos hx_pos)
  have hx_ne : x ≠ 0 := ne_of_gt hx_pos
  have hx_abs_pos : 0 < |x - 0| := by
    have : 0 < |x| := abs_pos.mpr hx_ne
    simpa using this
  have hx_abs_lt : |x - 0| < c := by
    calc
      |x - 0| = x := hx_abs
      _ < c := hx_lt
  have hx_punctured : 0 < |x - 0| ∧ |x - 0| < c := by
    constructor
    · exact hx_abs_pos
    · exact hx_abs_lt
  exact hc_nonzero x hx_punctured

/-- Helper for Theorem 4.7.1: every real sine value lies in `[-1, 1]`. -/
lemma helperForTheorem_4_7_1_sine_mem_Icc (x : ℝ) :
    Real.sin x ∈ Set.Icc (-1) 1 := by
  exact ⟨Real.neg_one_le_sin x, Real.sin_le_one x⟩

/-- Helper for Theorem 4.7.1: every real cosine value lies in `[-1, 1]`. -/
lemma helperForTheorem_4_7_1_cosine_mem_Icc (x : ℝ) :
    Real.cos x ∈ Set.Icc (-1) 1 := by
  exact ⟨Real.neg_one_le_cos x, Real.cos_le_one x⟩

/-- Theorem 4.7.1: For every real number `x`, one has
`sin(x)^2 + cos(x)^2 = 1`; in particular `sin(x), cos(x) ∈ [-1, 1]`. -/
theorem real_sine_cosine_pythagorean_identity_and_bounds (x : ℝ) :
    Real.sin x ^ 2 + Real.cos x ^ 2 = 1 ∧
    Real.sin x ∈ Set.Icc (-1) 1 ∧
    Real.cos x ∈ Set.Icc (-1) 1 := by
  refine ⟨Real.sin_sq_add_cos_sq x, ?_⟩
  exact ⟨helperForTheorem_4_7_1_sine_mem_Icc x, helperForTheorem_4_7_1_cosine_mem_Icc x⟩

/-- Helper for Theorem 4.7.2: pointwise derivative formula for `Real.sin`. -/
lemma helperForTheorem_4_7_2_sin_deriv_pointwise (x : ℝ) :
    deriv Real.sin x = Real.cos x := by
  exact (Real.hasDerivAt_sin x).deriv

/-- Helper for Theorem 4.7.2: pointwise derivative formula for `Real.cos`. -/
lemma helperForTheorem_4_7_2_cos_deriv_pointwise (x : ℝ) :
    deriv Real.cos x = -Real.sin x := by
  exact (Real.hasDerivAt_cos x).deriv

/-- Theorem 4.7.2: For every real number `x`,
`(Real.sin)'(x) = Real.cos x` and `(Real.cos)'(x) = -Real.sin x`. -/

theorem real_sine_cosine_derivative_formulas (x : ℝ) :
    deriv Real.sin x = Real.cos x ∧
    deriv Real.cos x = -Real.sin x := by
  constructor
  · exact helperForTheorem_4_7_2_sin_deriv_pointwise x
  · exact helperForTheorem_4_7_2_cos_deriv_pointwise x

/-- Theorem 4.7.3: For every real number `x`,
`sin(-x) = -sin(x)` and `cos(-x) = cos(x)`. -/
theorem real_sine_odd_and_cosine_even (x : ℝ) :
    Real.sin (-x) = -Real.sin x ∧
    Real.cos (-x) = Real.cos x := by
  constructor
  · simp [Real.sin_neg]
  · simp [Real.cos_neg]

/-- Theorem 4.7.4: For all real numbers `x, y`,
`cos(x + y) = cos(x)cos(y) - sin(x)sin(y)` and
`sin(x + y) = sin(x)cos(y) + cos(x)sin(y)`. -/
theorem real_sine_cosine_addition_formulas (x y : ℝ) :
    Real.cos (x + y) = Real.cos x * Real.cos y - Real.sin x * Real.sin y ∧
    Real.sin (x + y) = Real.sin x * Real.cos y + Real.cos x * Real.sin y := by
  constructor
  · simpa using Real.cos_add x y
  · simpa using Real.sin_add x y

/-- Theorem 4.7.5: We have `sin(0) = 0` and `cos(0) = 1`. -/
theorem real_sine_and_cosine_at_zero :
    Real.sin 0 = 0 ∧ Real.cos 0 = 1 := by
  constructor
  · simp
  · simp

/-- Lemma 4.7.1: There exists a real number `x > 0` such that `sin x = 0`. -/
lemma exists_positive_real_with_sine_zero :
    ∃ x : ℝ, 0 < x ∧ Real.sin x = 0 := by
  refine ⟨Real.pi, ?_⟩
  constructor
  · exact Real.pi_pos
  · simpa using Real.sin_pi

/-- Definition 4.7.2: Define `π` to be
`inf {x ∈ (0, ∞) : Real.sin x = 0}`. -/
noncomputable def firstPositiveSineZero : ℝ :=
  sInf {x : ℝ | x ∈ Set.Ioi (0 : ℝ) ∧ Real.sin x = 0}

/-- Definition 4.7.3: The tangent function is the map
`tan : (-π/2, π/2) → ℝ` defined by `tan(x) = sin x / cos x`. -/
noncomputable def tangentFunction : Set.Ioo (-(firstPositiveSineZero / 2)) (firstPositiveSineZero / 2) → ℝ :=
  fun x => Real.sin x / Real.cos x

/-- Definition 4.7.4: Define `f : ℝ → ℝ` by
`f(x) = ∑' n = 1..∞, 4^{-n} * cos(32^n * π * x)`.
Equivalently (reindexing by `n : ℕ`),
`f(x) = ∑' n, (1 / 4^(n+1)) * cos(32^(n+1) * π * x)`. -/
noncomputable def scaledCosineSeriesFunction : ℝ → ℝ :=
  fun x =>
    ∑' n : ℕ,
      (1 / (4 : ℝ) ^ (n + 1)) * Real.cos (((32 : ℝ) ^ (n + 1)) * firstPositiveSineZero * x)

/-- Helper for Proposition 4.7.8: every positive real zero of `Real.sin` is at least `π`. -/
lemma helperForProposition_4_7_8_pi_le_of_positive_sine_zero
    (t : ℝ) (ht_pos : 0 < t) (ht_sin : Real.sin t = 0) :
    Real.pi ≤ t := by
  rcases (Real.sin_eq_zero_iff.mp ht_sin) with ⟨n, hn⟩
  have hn_pos_real : (0 : ℝ) < (n : ℝ) := by
    have hmul_pos : 0 < (n : ℝ) * Real.pi := by
      simpa [hn] using ht_pos
    exact (mul_pos_iff_of_pos_right Real.pi_pos).mp hmul_pos
  have hn_pos_int : (0 : ℤ) < n := Int.cast_pos.mp hn_pos_real
  have hn_ge_one : (1 : ℤ) ≤ n := Int.add_one_le_iff.mpr hn_pos_int
  have hn_ge_one_real : (1 : ℝ) ≤ (n : ℝ) := by
    exact_mod_cast hn_ge_one
  have hmul_le : Real.pi ≤ (n : ℝ) * Real.pi := by
    calc
      Real.pi = (1 : ℝ) * Real.pi := by ring
      _ ≤ (n : ℝ) * Real.pi :=
        mul_le_mul_of_nonneg_right hn_ge_one_real (le_of_lt Real.pi_pos)
  calc
    Real.pi ≤ (n : ℝ) * Real.pi := hmul_le
    _ = t := hn

/-- Helper for Proposition 4.7.8: the infimum defining `firstPositiveSineZero` equals `π`. -/
lemma helperForProposition_4_7_8_firstPositiveSineZero_eq_pi :
    firstPositiveSineZero = Real.pi := by
  let S : Set ℝ := {t : ℝ | t ∈ Set.Ioi (0 : ℝ) ∧ Real.sin t = 0}
  have hS_nonempty : Set.Nonempty S := by
    refine ⟨Real.pi, ?_⟩
    exact ⟨Real.pi_pos, Real.sin_pi⟩
  have hS_bddBelow : BddBelow S := by
    refine ⟨0, ?_⟩
    intro t ht
    exact le_of_lt ht.1
  have hpi_mem : Real.pi ∈ S := by
    exact ⟨Real.pi_pos, Real.sin_pi⟩
  have hsInf_le_pi : sInf S ≤ Real.pi := csInf_le hS_bddBelow hpi_mem
  have hpi_le_sInf : Real.pi ≤ sInf S := by
    refine le_csInf hS_nonempty ?_
    intro t ht
    exact helperForProposition_4_7_8_pi_le_of_positive_sine_zero t ht.1 ht.2
  have hsInf_eq_pi : sInf S = Real.pi := le_antisymm hsInf_le_pi hpi_le_sInf
  simpa [firstPositiveSineZero, S] using hsInf_eq_pi

/-- Helper for Proposition 4.7.8: `Real.tan` is differentiable on `(-π/2, π/2)`. -/
lemma helperForProposition_4_7_8_differentiableOn_tan_Ioo :
    DifferentiableOn ℝ Real.tan (Set.Ioo (-(Real.pi / 2)) (Real.pi / 2)) := by
  intro x hx
  exact (Real.differentiableAt_tan_of_mem_Ioo hx).differentiableWithinAt

/-- Helper for Proposition 4.7.8: the derivative formula `tan' = 1 + tan^2` on `(-π/2, π/2)`. -/
lemma helperForProposition_4_7_8_deriv_tan_eq_one_add_tan_sq_on_Ioo :
    ∀ x ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2),
      deriv Real.tan x = 1 + Real.tan x ^ 2 := by
  intro x hx
  have hcos_pos : 0 < Real.cos x := Real.cos_pos_of_mem_Ioo hx
  have hcos_ne : Real.cos x ≠ 0 := ne_of_gt hcos_pos
  have hcos_sq_ne : Real.cos x ^ 2 ≠ 0 := pow_ne_zero 2 hcos_ne
  have htan_sq : 1 + Real.tan x ^ 2 = 1 / Real.cos x ^ 2 := by
    apply (eq_div_iff hcos_sq_ne).2
    simpa [mul_comm, mul_left_comm, mul_assoc] using
      (Real.one_add_tan_sq_mul_cos_sq_eq_one hcos_ne)
  calc
    deriv Real.tan x = 1 / Real.cos x ^ 2 := (Real.hasDerivAt_tan_of_mem_Ioo hx).deriv
    _ = 1 + Real.tan x ^ 2 := by
      symm
      exact htan_sq

/-- Helper for Proposition 4.7.8: `Real.tan` is bijective from `(-π/2, π/2)` to `ℝ`. -/
lemma helperForProposition_4_7_8_bijective_tan_subtype :
    Function.Bijective (fun x : Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) => Real.tan x.1) := by
  simpa using Real.tanOrderIso.bijective

/-- Proposition 4.7.8: Define `tan : (-π/2, π/2) → ℝ` by
`tan(x) = sin x / cos x`. Then `tan` is differentiable on `(-π/2, π/2)` and
`(d/dx) tan(x) = 1 + tan(x)^2` for `x ∈ (-π/2, π/2)`.
In particular, `tan` is strictly increasing on `(-π/2, π/2)`,
`lim_{x→(π/2)^-} tan(x) = +∞`, `lim_{x→(-π/2)^+} tan(x) = -∞`, and hence
`tan` is a bijection from `(-π/2, π/2)` onto `ℝ`. -/
theorem tangent_differentiableOn_deriv_strictMono_limits_and_bijective :
    DifferentiableOn ℝ (fun x : ℝ => Real.sin x / Real.cos x)
      (Set.Ioo (-(firstPositiveSineZero / 2)) (firstPositiveSineZero / 2)) ∧
    (∀ x ∈ Set.Ioo (-(firstPositiveSineZero / 2)) (firstPositiveSineZero / 2),
      deriv (fun y : ℝ => Real.sin y / Real.cos y) x =
        1 + (Real.sin x / Real.cos x) ^ 2) ∧
    StrictMonoOn (fun x : ℝ => Real.sin x / Real.cos x)
      (Set.Ioo (-(firstPositiveSineZero / 2)) (firstPositiveSineZero / 2)) ∧
    Filter.Tendsto (fun x : ℝ => Real.sin x / Real.cos x)
      (nhdsWithin (firstPositiveSineZero / 2) (Set.Iio (firstPositiveSineZero / 2))) Filter.atTop ∧
    Filter.Tendsto (fun x : ℝ => Real.sin x / Real.cos x)
      (nhdsWithin (-(firstPositiveSineZero / 2)) (Set.Ioi (-(firstPositiveSineZero / 2)))) Filter.atBot ∧
    Function.Bijective
      (fun x : Set.Ioo (-(firstPositiveSineZero / 2)) (firstPositiveSineZero / 2) =>
        Real.sin x.1 / Real.cos x.1) := by
  have hpi : firstPositiveSineZero = Real.pi :=
    helperForProposition_4_7_8_firstPositiveSineZero_eq_pi
  rw [hpi]
  have htan_fun : (fun x : ℝ => Real.sin x / Real.cos x) = Real.tan := by
    funext x
    symm
    exact Real.tan_eq_sin_div_cos x
  have htan_subtype :
      (fun x : Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) => Real.sin x.1 / Real.cos x.1) =
      (fun x : Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) => Real.tan x.1) := by
    funext x
    symm
    exact Real.tan_eq_sin_div_cos x.1
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [htan_fun] using helperForProposition_4_7_8_differentiableOn_tan_Ioo
  · intro x hx
    have hderiv : deriv Real.tan x = 1 + Real.tan x ^ 2 :=
      helperForProposition_4_7_8_deriv_tan_eq_one_add_tan_sq_on_Ioo x hx
    simpa [htan_fun, Real.tan_eq_sin_div_cos] using hderiv
  · simpa [htan_fun] using Real.strictMonoOn_tan
  · simpa [htan_fun] using Real.tendsto_tan_pi_div_two
  · simpa [htan_fun] using Real.tendsto_tan_neg_pi_div_two
  · simpa [htan_subtype] using helperForProposition_4_7_8_bijective_tan_subtype

/-- Helper for Proposition 4.7.9: `Real.arctan` is differentiable on all real numbers. -/
lemma helperForProposition_4_7_9_differentiable_arctan_global :
    Differentiable ℝ Real.arctan := by
  simpa using Real.differentiable_arctan

/-- Helper for Proposition 4.7.9: pointwise derivative formula for `Real.arctan`. -/
lemma helperForProposition_4_7_9_deriv_arctan_pointwise (x : ℝ) :
    deriv Real.arctan x = 1 / (1 + x ^ 2) := by
  simpa using (Real.hasDerivAt_arctan x).deriv

/-- Helper for Proposition 4.7.9: alternate pointwise derivative formula from
`Real.deriv_arctan`. -/
lemma helperForProposition_4_7_9_deriv_arctan_pointwise_alt (x : ℝ) :
    deriv Real.arctan x = 1 / (1 + x ^ 2) := by
  simpa using congrArg (fun f : ℝ → ℝ => f x) Real.deriv_arctan

/-- Proposition 4.7.9: Let `tan⁻¹ : ℝ → (-π/2, π/2)` be the inverse of
`tan : (-π/2, π/2) → ℝ`. Then `Real.arctan` is differentiable on `ℝ` and
for every `x : ℝ`, `(d/dx) arctan(x) = 1 / (1 + x^2)`. -/
theorem arctan_differentiable_and_deriv :
    Differentiable ℝ Real.arctan ∧
    ∀ x : ℝ, deriv Real.arctan x = 1 / (1 + x ^ 2) := by
  constructor
  · exact helperForProposition_4_7_9_differentiable_arctan_global
  · intro x
    exact helperForProposition_4_7_9_deriv_arctan_pointwise x

/-- Proposition 4.7.10: For every real number `x` with `|x| < 1`,
the arctangent function has the power series expansion
`arctan x = ∑' n, (-1)^n * x^(2n+1) / (2n+1)`. -/
theorem arctan_eq_tsum_powerSeries_of_abs_lt_one
    {x : ℝ} (hx : |x| < 1) :
    Real.arctan x =
      ∑' n : ℕ, (((-1 : ℝ) ^ n) * x ^ (2 * n + 1)) / (2 * n + 1 : ℝ) := by
  have hnorm : ‖x‖ < 1 := by
    simpa [Real.norm_eq_abs] using hx
  have hsum :
      HasSum (fun n : ℕ => (((-1 : ℝ) ^ n) * x ^ (2 * n + 1)) / (2 * n + 1 : ℝ))
        (Real.arctan x) := by
    simpa using Real.hasSum_arctan hnorm
  exact hsum.tsum_eq.symm

/-- Helper for Proposition 4.7.4: the positive-zero set used in the definition of
`firstPositiveSineZero` is nonempty and bounded below. -/
lemma helperForProposition_4_7_4_positiveSineZeroSet_nonempty_bddBelow :
    Set.Nonempty {t : ℝ | t ∈ Set.Ioi (0 : ℝ) ∧ Real.sin t = 0} ∧
    BddBelow {t : ℝ | t ∈ Set.Ioi (0 : ℝ) ∧ Real.sin t = 0} := by
  constructor
  · exact ⟨Real.pi, Real.pi_pos, Real.sin_pi⟩
  · refine ⟨0, ?_⟩
    intro t ht
    exact le_of_lt ht.1

/-- Helper for Proposition 4.7.4: every positive real zero of `Real.sin` is at least `π`. -/
lemma helperForProposition_4_7_4_pi_le_of_positive_sine_zero
    (t : ℝ) (ht_pos : 0 < t) (ht_sin : Real.sin t = 0) :
    Real.pi ≤ t := by
  rcases (Real.sin_eq_zero_iff.mp ht_sin) with ⟨n, hn⟩
  have hn_pos_real : (0 : ℝ) < (n : ℝ) := by
    have hmul_pos : 0 < (n : ℝ) * Real.pi := by
      simpa [hn] using ht_pos
    exact (mul_pos_iff_of_pos_right Real.pi_pos).mp hmul_pos
  have hn_pos_int : (0 : ℤ) < n := Int.cast_pos.mp hn_pos_real
  have hn_ge_one : (1 : ℤ) ≤ n := Int.add_one_le_iff.mpr hn_pos_int
  have hn_ge_one_real : (1 : ℝ) ≤ (n : ℝ) := by
    exact_mod_cast hn_ge_one
  have hmul_le : Real.pi ≤ (n : ℝ) * Real.pi := by
    calc
      Real.pi = (1 : ℝ) * Real.pi := by ring
      _ ≤ (n : ℝ) * Real.pi :=
        mul_le_mul_of_nonneg_right hn_ge_one_real (le_of_lt Real.pi_pos)
  calc
    Real.pi ≤ (n : ℝ) * Real.pi := hmul_le
    _ = t := hn

/-- Helper for Proposition 4.7.4: the definition of `firstPositiveSineZero` agrees with
the standard constant `Real.pi`. -/
lemma helperForProposition_4_7_4_firstPositiveSineZero_eq_pi :
    firstPositiveSineZero = Real.pi := by
  let S : Set ℝ := {t : ℝ | t ∈ Set.Ioi (0 : ℝ) ∧ Real.sin t = 0}
  have hS_nonempty_bdd : Set.Nonempty S ∧ BddBelow S :=
    helperForProposition_4_7_4_positiveSineZeroSet_nonempty_bddBelow
  have hS_nonempty : Set.Nonempty S := hS_nonempty_bdd.1
  have hS_bddBelow : BddBelow S := hS_nonempty_bdd.2
  have hpi_mem : Real.pi ∈ S := by
    exact ⟨Real.pi_pos, Real.sin_pi⟩
  have hsInf_le_pi : sInf S ≤ Real.pi := csInf_le hS_bddBelow hpi_mem
  have hpi_le_sInf : Real.pi ≤ sInf S := by
    refine le_csInf hS_nonempty ?_
    intro t ht
    exact helperForProposition_4_7_4_pi_le_of_positive_sine_zero t ht.1 ht.2
  have hsInf_eq_pi : sInf S = Real.pi := le_antisymm hsInf_le_pi hpi_le_sInf
  simpa [firstPositiveSineZero, S] using hsInf_eq_pi

/-- Helper for Proposition 4.7.4: existence of an angle in `(-π, π]` with prescribed
`sin` and `cos` coordinates on the unit circle. -/
lemma helperForProposition_4_7_4_exists_angle_in_Ioc_neg_pi_pi
    (x y : ℝ) (hxy : x ^ 2 + y ^ 2 = 1) :
    ∃ θ : ℝ, θ ∈ Set.Ioc (-Real.pi) Real.pi ∧ Real.sin θ = x ∧ Real.cos θ = y := by
  let z : ℂ := y + x * Complex.I
  have hz_norm_sq : ‖z‖ ^ 2 = 1 := by
    calc
      ‖z‖ ^ 2 = Complex.normSq z := Complex.sq_norm z
      _ = y ^ 2 + x ^ 2 := by
        simpa [z] using (Complex.normSq_add_mul_I y x)
      _ = 1 := by nlinarith [hxy]
  have hz_norm : ‖z‖ = 1 := by
    have hz_nonneg : 0 ≤ ‖z‖ := norm_nonneg z
    nlinarith [hz_norm_sq, hz_nonneg]
  have hz_ne : z ≠ 0 := by
    intro hz0
    have hz_norm_ne_zero : ‖z‖ ≠ 0 := by
      rw [hz_norm]
      norm_num
    have hz_norm_eq_zero : ‖z‖ = 0 := by
      simpa [hz0]
    exact hz_norm_ne_zero hz_norm_eq_zero
  refine ⟨Complex.arg z, ?_⟩
  have harg_mem : Complex.arg z ∈ Set.Ioc (-Real.pi) Real.pi := Complex.arg_mem_Ioc z
  have hsin : Real.sin (Complex.arg z) = x := by
    calc
      Real.sin (Complex.arg z) = z.im / ‖z‖ := Complex.sin_arg z
      _ = x / ‖z‖ := by simp [z]
      _ = x := by rw [hz_norm, div_one]
  have hcos : Real.cos (Complex.arg z) = y := by
    calc
      Real.cos (Complex.arg z) = z.re / ‖z‖ := Complex.cos_arg hz_ne
      _ = y / ‖z‖ := by simp [z]
      _ = y := by rw [hz_norm, div_one]
  exact ⟨harg_mem, hsin, hcos⟩

/-- Helper for Proposition 4.7.4: uniqueness of the angle in `(-π, π]` with fixed
`sin` and `cos` values. -/
lemma helperForProposition_4_7_4_angle_unique_in_Ioc_neg_pi_pi
    (x y θ₁ θ₂ : ℝ)
    (hθ₁ : θ₁ ∈ Set.Ioc (-Real.pi) Real.pi)
    (hθ₂ : θ₂ ∈ Set.Ioc (-Real.pi) Real.pi)
    (hsin₁ : Real.sin θ₁ = x)
    (hcos₁ : Real.cos θ₁ = y)
    (hsin₂ : Real.sin θ₂ = x)
    (hcos₂ : Real.cos θ₂ = y) :
    θ₁ = θ₂ := by
  have harg₁ : Complex.arg (y + x * Complex.I) = θ₁ := by
    have hz₁ : y + x * Complex.I = Real.cos θ₁ + Real.sin θ₁ * Complex.I := by
      simpa [hcos₁, hsin₁]
    calc
      Complex.arg (y + x * Complex.I)
          = Complex.arg (Real.cos θ₁ + Real.sin θ₁ * Complex.I) := by rw [hz₁]
      _ = θ₁ := by
        simpa using (Complex.arg_cos_add_sin_mul_I hθ₁)
  have harg₂ : Complex.arg (y + x * Complex.I) = θ₂ := by
    have hz₂ : y + x * Complex.I = Real.cos θ₂ + Real.sin θ₂ * Complex.I := by
      simpa [hcos₂, hsin₂]
    calc
      Complex.arg (y + x * Complex.I)
          = Complex.arg (Real.cos θ₂ + Real.sin θ₂ * Complex.I) := by rw [hz₂]
      _ = θ₂ := by
        simpa using (Complex.arg_cos_add_sin_mul_I hθ₂)
  calc
    θ₁ = Complex.arg (y + x * Complex.I) := by
      symm
      exact harg₁
    _ = θ₂ := harg₂

/-- Proposition 4.7.4: If `x, y : ℝ` satisfy `x^2 + y^2 = 1`, then there exists a unique
`θ ∈ (-π, π]` such that `sin θ = x` and `cos θ = y`. -/
theorem existsUnique_angle_in_Ioc_neg_pi_pi_of_sq_add_sq_eq_one
    (x y : ℝ) (hxy : x ^ 2 + y ^ 2 = 1) :
    ∃! θ : ℝ,
      θ ∈ Set.Ioc (-firstPositiveSineZero) firstPositiveSineZero ∧
      Real.sin θ = x ∧ Real.cos θ = y := by
  have hpi : firstPositiveSineZero = Real.pi :=
    helperForProposition_4_7_4_firstPositiveSineZero_eq_pi
  rcases helperForProposition_4_7_4_exists_angle_in_Ioc_neg_pi_pi x y hxy with
    ⟨θ, hθ_mem_pi, hsinθ, hcosθ⟩
  have hθ_mem_first : θ ∈ Set.Ioc (-firstPositiveSineZero) firstPositiveSineZero := by
    simpa [hpi] using hθ_mem_pi
  refine ⟨θ, ?_, ?_⟩
  · exact ⟨hθ_mem_first, hsinθ, hcosθ⟩
  · intro θ' hθ'
    rcases hθ' with ⟨hθ'_mem_first, hsinθ', hcosθ'⟩
    have hθ'_mem_pi : θ' ∈ Set.Ioc (-Real.pi) Real.pi := by
      simpa [hpi] using hθ'_mem_first
    exact
      helperForProposition_4_7_4_angle_unique_in_Ioc_neg_pi_pi
        x y θ' θ hθ'_mem_pi hθ_mem_pi hsinθ' hcosθ' hsinθ hcosθ

/-- Helper for Proposition 4.7.5: the norm of `exp(i x)` is `1` for real `x`. -/
lemma helperForProposition_4_7_5_norm_exp_I_mul_real (x : ℝ) :
    ‖Complex.exp (Complex.I * (x : ℂ))‖ = 1 := by
  calc
    ‖Complex.exp (Complex.I * (x : ℂ))‖
        = Real.exp (Complex.re (Complex.I * (x : ℂ))) := by
          simpa using (Complex.norm_exp (Complex.I * (x : ℂ)))
    _ = Real.exp 0 := by simp
    _ = 1 := by simp

/-- Helper for Proposition 4.7.5: equality of scaled polar exponentials with positive
radii forces equality of radii. -/
lemma helperForProposition_4_7_5_radius_eq_of_scaled_exp_eq
    (r s θ α : ℝ)
    (hr : 0 < r)
    (hs : 0 < s)
    (hEq : (r : ℂ) * Complex.exp (Complex.I * (θ : ℂ)) =
      (s : ℂ) * Complex.exp (Complex.I * (α : ℂ))) :
    r = s := by
  have hNorm : ‖(r : ℂ) * Complex.exp (Complex.I * (θ : ℂ))‖ =
      ‖(s : ℂ) * Complex.exp (Complex.I * (α : ℂ))‖ :=
    congrArg (fun z : ℂ => ‖z‖) hEq
  have hAbs : |r| = |s| := by
    simpa [Complex.norm_mul, Complex.norm_real,
      helperForProposition_4_7_5_norm_exp_I_mul_real θ,
      helperForProposition_4_7_5_norm_exp_I_mul_real α] using hNorm
  have hrabs : |r| = r := abs_of_pos hr
  have hsabs : |s| = s := abs_of_pos hs
  calc
    r = |r| := by simpa [hrabs] using hrabs.symm
    _ = |s| := hAbs
    _ = s := hsabs

/-- Helper for Proposition 4.7.5: after identifying radii, one can cancel the nonzero
real scalar and deduce equality of the exponential factors. -/
lemma helperForProposition_4_7_5_exp_eq_of_radius_eq
    (r s θ α : ℝ)
    (hr : 0 < r)
    (hrs : r = s)
    (hEq : (r : ℂ) * Complex.exp (Complex.I * (θ : ℂ)) =
      (s : ℂ) * Complex.exp (Complex.I * (α : ℂ))) :
    Complex.exp (Complex.I * (θ : ℂ)) = Complex.exp (Complex.I * (α : ℂ)) := by
  subst s
  have hr_ne : (r : ℂ) ≠ 0 := by
    exact_mod_cast (ne_of_gt hr)
  exact mul_left_cancel₀ hr_ne hEq

/-- Helper for Proposition 4.7.5: equality of `exp(iθ)` and `exp(iα)` forces an integer
`2π` angle shift between `θ` and `α`. -/
lemma helperForProposition_4_7_5_angle_shift_of_exp_I_eq
    (θ α : ℝ)
    (hExpEq : Complex.exp (Complex.I * (θ : ℂ)) = Complex.exp (Complex.I * (α : ℂ))) :
    ∃ k : ℤ, θ = α + 2 * Real.pi * (k : ℝ) := by
  rcases (Complex.exp_eq_exp_iff_exists_int).mp hExpEq with ⟨k, hk⟩
  refine ⟨k, ?_⟩
  have hkIm : θ = α + (k : ℝ) * (2 * Real.pi) := by
    simpa [Complex.mul_re, Complex.mul_im, mul_assoc, mul_comm, mul_left_comm,
      add_comm, add_left_comm, add_assoc, two_mul] using congrArg Complex.im hk
  calc
    θ = α + (k : ℝ) * (2 * Real.pi) := hkIm
    _ = α + 2 * Real.pi * (k : ℝ) := by ring

/-- Proposition 4.7.5: if `r, s > 0` and `θ, α : ℝ` satisfy
`(r : ℂ) * exp(iθ) = (s : ℂ) * exp(iα)`, then `r = s` and
`θ = α + 2πk` for some `k : ℤ`. -/
theorem complex_polar_exp_eq_iff
    (r s θ α : ℝ)
    (hr : 0 < r)
    (hs : 0 < s)
    (hEq : (r : ℂ) * Complex.exp (Complex.I * (θ : ℂ)) =
      (s : ℂ) * Complex.exp (Complex.I * (α : ℂ))) :
    r = s ∧ ∃ k : ℤ, θ = α + 2 * Real.pi * (k : ℝ) := by
  have hrs : r = s :=
    helperForProposition_4_7_5_radius_eq_of_scaled_exp_eq r s θ α hr hs hEq
  have hExpEq : Complex.exp (Complex.I * (θ : ℂ)) = Complex.exp (Complex.I * (α : ℂ)) :=
    helperForProposition_4_7_5_exp_eq_of_radius_eq r s θ α hr hrs hEq
  have hShift : ∃ k : ℤ, θ = α + 2 * Real.pi * (k : ℝ) :=
    helperForProposition_4_7_5_angle_shift_of_exp_I_eq θ α hExpEq
  exact ⟨hrs, hShift⟩

/-- Helper for Proposition 4.7.6: the canonical witness `(‖z‖, arg z)` satisfies
the required positivity, interval, and reconstruction properties. -/
lemma helperForProposition_4_7_6_exists_polar_witness
    (z : ℂ) (hz : z ≠ 0) :
    ∃ p : ℝ × ℝ,
      0 < p.1 ∧
      p.2 ∈ Set.Ioc (-firstPositiveSineZero) firstPositiveSineZero ∧
      z = (p.1 : ℂ) * Complex.exp (Complex.I * (p.2 : ℂ)) := by
  refine ⟨(‖z‖, Complex.arg z), ?_⟩
  have hnorm_pos : 0 < ‖z‖ := norm_pos_iff.mpr hz
  have harg_mem_pi : Complex.arg z ∈ Set.Ioc (-Real.pi) Real.pi :=
    Complex.arg_mem_Ioc z
  have hpi : firstPositiveSineZero = Real.pi :=
    helperForProposition_4_7_4_firstPositiveSineZero_eq_pi
  have harg_mem : Complex.arg z ∈ Set.Ioc (-firstPositiveSineZero) firstPositiveSineZero := by
    simpa [hpi] using harg_mem_pi
  have hz_eq : z = (‖z‖ : ℂ) * Complex.exp (Complex.I * (Complex.arg z : ℂ)) := by
    simpa [mul_comm] using (Complex.norm_mul_exp_arg_mul_I z).symm
  exact ⟨hnorm_pos, harg_mem, hz_eq⟩

/-- Helper for Proposition 4.7.6: if two angles lie in `(-π, π]` and differ by
an integer multiple of `2π`, then the integer shift is zero. -/
lemma helperForProposition_4_7_6_int_shift_zero_of_interval_bounds
    {θ α : ℝ} {k : ℤ}
    (hθ : θ ∈ Set.Ioc (-firstPositiveSineZero) firstPositiveSineZero)
    (hα : α ∈ Set.Ioc (-firstPositiveSineZero) firstPositiveSineZero)
    (hEq : θ = α + 2 * Real.pi * (k : ℝ)) :
    k = 0 := by
  have hpi : firstPositiveSineZero = Real.pi :=
    helperForProposition_4_7_4_firstPositiveSineZero_eq_pi
  have hθ_pi : θ ∈ Set.Ioc (-Real.pi) Real.pi := by
    simpa [hpi] using hθ
  have hα_pi : α ∈ Set.Ioc (-Real.pi) Real.pi := by
    simpa [hpi] using hα
  rcases hθ_pi with ⟨hθ_lower, hθ_upper⟩
  rcases hα_pi with ⟨hα_lower, hα_upper⟩
  have hk_le : α + 2 * Real.pi * (k : ℝ) ≤ Real.pi := by
    simpa [hEq] using hθ_upper
  have hk_gt : -Real.pi < α + 2 * Real.pi * (k : ℝ) := by
    simpa [hEq] using hθ_lower
  have hk_lt_one : (k : ℝ) < 1 := by
    nlinarith [hα_lower, hk_le, Real.pi_pos]
  have hneg_one_lt_k : (-1 : ℝ) < (k : ℝ) := by
    nlinarith [hα_upper, hk_gt, Real.pi_pos]
  have hk_lt_one_int : k < 1 := by
    exact_mod_cast hk_lt_one
  have hk_gt_neg_one_int : (-1 : ℤ) < k := by
    exact_mod_cast hneg_one_lt_k
  have hk_nonpos : k ≤ 0 := by
    simpa using (Int.lt_add_one_iff.mp hk_lt_one_int)
  have hk_nonneg : 0 ≤ k := by
    have htmp : (-1 : ℤ) + 1 ≤ k := Int.add_one_le_iff.mpr hk_gt_neg_one_int
    simpa using htmp
  exact le_antisymm hk_nonpos hk_nonneg

/-- Helper for Proposition 4.7.6: two admissible polar representations of the same
nonzero complex number have identical radius and angle. -/
lemma helperForProposition_4_7_6_radius_angle_unique
    {z : ℂ} {r s θ α : ℝ}
    (hr : 0 < r)
    (hs : 0 < s)
    (hθ : θ ∈ Set.Ioc (-firstPositiveSineZero) firstPositiveSineZero)
    (hα : α ∈ Set.Ioc (-firstPositiveSineZero) firstPositiveSineZero)
    (hEqR : z = (r : ℂ) * Complex.exp (Complex.I * (θ : ℂ)))
    (hEqS : z = (s : ℂ) * Complex.exp (Complex.I * (α : ℂ))) :
    r = s ∧ θ = α := by
  have hEqRS : (r : ℂ) * Complex.exp (Complex.I * (θ : ℂ)) =
      (s : ℂ) * Complex.exp (Complex.I * (α : ℂ)) := by
    calc
      (r : ℂ) * Complex.exp (Complex.I * (θ : ℂ)) = z := by
        simpa using hEqR.symm
      _ = (s : ℂ) * Complex.exp (Complex.I * (α : ℂ)) := hEqS
  rcases complex_polar_exp_eq_iff r s θ α hr hs hEqRS with ⟨hrs, hk⟩
  rcases hk with ⟨k, hkEq⟩
  have hk0 : k = 0 :=
    helperForProposition_4_7_6_int_shift_zero_of_interval_bounds hθ hα hkEq
  have hθα : θ = α := by
    simpa [hk0] using hkEq
  exact ⟨hrs, hθα⟩

/-- Proposition 4.7.6: for every nonzero complex number `z`, there exists a unique
pair `(r, θ)` with `r > 0` and `θ ∈ (-π, π]` (where `π` is `firstPositiveSineZero`)
such that `z = r * exp(iθ)`. -/
theorem complex_existsUnique_polar_coordinates_Ioc
    (z : ℂ) (hz : z ≠ 0) :
    ∃! p : ℝ × ℝ,
      0 < p.1 ∧
      p.2 ∈ Set.Ioc (-firstPositiveSineZero) firstPositiveSineZero ∧
      z = (p.1 : ℂ) * Complex.exp (Complex.I * (p.2 : ℂ)) := by
  rcases helperForProposition_4_7_6_exists_polar_witness z hz with ⟨p, hp_pos, hp_mem, hp_eq⟩
  refine ⟨p, ?_, ?_⟩
  · exact ⟨hp_pos, hp_mem, hp_eq⟩
  · intro q hq
    rcases hq with ⟨hq_pos, hq_mem, hq_eq⟩
    have hqp : q.1 = p.1 ∧ q.2 = p.2 :=
      helperForProposition_4_7_6_radius_angle_unique hq_pos hp_pos hq_mem hp_mem hq_eq hp_eq
    rcases hqp with ⟨hqp1, hqp2⟩
    exact Prod.ext hqp1 hqp2

/-- Helper for Theorem 4.7.6: Euler's formula in the `exp(i x)` direction for real `x`. -/
lemma helperForTheorem_4_7_6_exp_I_mul_ofReal (x : ℝ) :
    Complex.exp (Complex.I * (x : ℂ)) = (Real.cos x : ℂ) + Complex.I * (Real.sin x : ℂ) := by
  simpa [mul_comm] using (Complex.exp_mul_I (x : ℂ))

/-- Helper for Theorem 4.7.6: Euler's formula in the `exp(-i x)` direction for real `x`. -/
lemma helperForTheorem_4_7_6_exp_neg_I_mul_ofReal (x : ℝ) :
    Complex.exp (-Complex.I * (x : ℂ)) = (Real.cos x : ℂ) - Complex.I * (Real.sin x : ℂ) := by
  have hmul : -Complex.I * (x : ℂ) = (-(x : ℂ)) * Complex.I := by
    ring
  rw [hmul]
  simpa [sub_eq_add_neg, mul_comm, mul_left_comm, mul_assoc] using (Complex.exp_mul_I (-(x : ℂ)))

/-- Helper for Theorem 4.7.6: real and imaginary parts of `exp(i x)` for real `x`. -/
lemma helperForTheorem_4_7_6_re_im_of_exp_I_mul (x : ℝ) :
    Real.cos x = Complex.re (Complex.exp (Complex.I * (x : ℂ))) ∧
    Real.sin x = Complex.im (Complex.exp (Complex.I * (x : ℂ))) := by
  constructor
  · simpa [mul_comm] using (Complex.exp_ofReal_mul_I_re x).symm
  · simpa [mul_comm] using (Complex.exp_ofReal_mul_I_im x).symm

/-- Theorem 4.7.6: for every real number `x`,
`exp(ix) = cos(x) + i sin(x)` and `exp(-ix) = cos(x) - i sin(x)`.
In particular, `cos(x) = Re(exp(ix))` and `sin(x) = Im(exp(ix))`. -/
theorem real_euler_formula_and_real_imag_parts (x : ℝ) :
    Complex.exp (Complex.I * (x : ℂ)) = (Real.cos x : ℂ) + Complex.I * (Real.sin x : ℂ) ∧
    Complex.exp (-Complex.I * (x : ℂ)) = (Real.cos x : ℂ) - Complex.I * (Real.sin x : ℂ) ∧
    Real.cos x = Complex.re (Complex.exp (Complex.I * (x : ℂ))) ∧
    Real.sin x = Complex.im (Complex.exp (Complex.I * (x : ℂ))) := by
  refine ⟨helperForTheorem_4_7_6_exp_I_mul_ofReal x, ?_⟩
  refine ⟨helperForTheorem_4_7_6_exp_neg_I_mul_ofReal x, ?_⟩
  exact helperForTheorem_4_7_6_re_im_of_exp_I_mul x

/-- Helper for Proposition 4.7.7: rewrite `cos θ + i sin θ` as `exp(iθ)`. -/
lemma helperForProposition_4_7_7_base_as_exp (θ : ℝ) :
    ((Real.cos θ : ℂ) + Complex.I * (Real.sin θ : ℂ)) =
      Complex.exp (Complex.I * (θ : ℂ)) := by
  simpa [mul_comm] using (Complex.exp_mul_I (θ : ℂ)).symm

/-- Helper for Proposition 4.7.7: normalize the scaled exponential argument
for integer powers. -/
lemma helperForProposition_4_7_7_exp_int_argument_rewrite (θ : ℝ) (n : ℤ) :
    (n : ℂ) * (Complex.I * (θ : ℂ)) = Complex.I * (((n : ℝ) * θ : ℝ) : ℂ) := by
  norm_num [Int.cast_mul, mul_assoc, mul_left_comm, mul_comm]

/-- Helper for Proposition 4.7.7: convert `(cos θ + i sin θ)^n` to one
exponential at argument `(n : ℝ) * θ`. -/
lemma helperForProposition_4_7_7_power_as_exp_scaled (θ : ℝ) (n : ℤ) :
    (((Real.cos θ : ℂ) + Complex.I * (Real.sin θ : ℂ)) ^ n) =
      Complex.exp (Complex.I * (((n : ℝ) * θ : ℝ) : ℂ)) := by
  calc
    (((Real.cos θ : ℂ) + Complex.I * (Real.sin θ : ℂ)) ^ n)
        = (Complex.exp (Complex.I * (θ : ℂ))) ^ n := by
          rw [helperForProposition_4_7_7_base_as_exp θ]
    _ = Complex.exp ((n : ℂ) * (Complex.I * (θ : ℂ))) := by
          rw [← Complex.exp_int_mul (Complex.I * (θ : ℂ)) n]
    _ = Complex.exp (Complex.I * (((n : ℝ) * θ : ℝ) : ℂ)) := by
          rw [helperForProposition_4_7_7_exp_int_argument_rewrite θ n]

/-- Helper for Proposition 4.7.7: identify `cos(nθ)` and `sin(nθ)` as the real
and imaginary parts of `(cos θ + i sin θ)^n`. -/
lemma helperForProposition_4_7_7_re_im_from_power (θ : ℝ) (n : ℤ) :
    Real.cos ((n : ℝ) * θ) =
      Complex.re (((Real.cos θ : ℂ) + Complex.I * (Real.sin θ : ℂ)) ^ n) ∧
    Real.sin ((n : ℝ) * θ) =
      Complex.im (((Real.cos θ : ℂ) + Complex.I * (Real.sin θ : ℂ)) ^ n) := by
  constructor
  · calc
      Real.cos ((n : ℝ) * θ)
          = Complex.re (Complex.exp (Complex.I * (((n : ℝ) * θ : ℝ) : ℂ))) := by
              simpa [mul_comm] using (Complex.exp_ofReal_mul_I_re ((n : ℝ) * θ)).symm
      _ = Complex.re (((Real.cos θ : ℂ) + Complex.I * (Real.sin θ : ℂ)) ^ n) := by
            rw [helperForProposition_4_7_7_power_as_exp_scaled θ n]
  · calc
      Real.sin ((n : ℝ) * θ)
          = Complex.im (Complex.exp (Complex.I * (((n : ℝ) * θ : ℝ) : ℂ))) := by
              simpa [mul_comm] using (Complex.exp_ofReal_mul_I_im ((n : ℝ) * θ)).symm
      _ = Complex.im (((Real.cos θ : ℂ) + Complex.I * (Real.sin θ : ℂ)) ^ n) := by
            rw [helperForProposition_4_7_7_power_as_exp_scaled θ n]

/-- Proposition 4.7.7 (de Moivre identities): for every `θ : ℝ` and `n : ℤ`,
`cos(nθ)` and `sin(nθ)` are the real and imaginary parts of
`(cos θ + i sin θ)^n`; equivalently,
`(cos θ + i sin θ)^n = cos(nθ) + i sin(nθ)`. -/
theorem de_moivre_identities_integer_powers (θ : ℝ) (n : ℤ) :
    Real.cos ((n : ℝ) * θ) =
      Complex.re (((Real.cos θ : ℂ) + Complex.I * (Real.sin θ : ℂ)) ^ n) ∧
    Real.sin ((n : ℝ) * θ) =
      Complex.im (((Real.cos θ : ℂ) + Complex.I * (Real.sin θ : ℂ)) ^ n) ∧
    (((Real.cos θ : ℂ) + Complex.I * (Real.sin θ : ℂ)) ^ n) =
      (Real.cos ((n : ℝ) * θ) : ℂ) + Complex.I * (Real.sin ((n : ℝ) * θ) : ℂ) := by
  rcases helperForProposition_4_7_7_re_im_from_power θ n with ⟨hRe, hIm⟩
  refine ⟨hRe, hIm, ?_⟩
  calc
    (((Real.cos θ : ℂ) + Complex.I * (Real.sin θ : ℂ)) ^ n)
        = Complex.exp (Complex.I * (((n : ℝ) * θ : ℝ) : ℂ)) :=
          helperForProposition_4_7_7_power_as_exp_scaled θ n
    _ = (Real.cos ((n : ℝ) * θ) : ℂ) + Complex.I * (Real.sin ((n : ℝ) * θ) : ℂ) :=
          (real_euler_formula_and_real_imag_parts ((n : ℝ) * θ)).1

/-- Helper for Theorem 4.7.7: the positive sine-zero set is nonempty and bounded below. -/
lemma helperForTheorem_4_7_7_positiveSineZeroSet_nonempty_bddBelow :
    Set.Nonempty {x : ℝ | x ∈ Set.Ioi (0 : ℝ) ∧ Real.sin x = 0} ∧
    BddBelow {x : ℝ | x ∈ Set.Ioi (0 : ℝ) ∧ Real.sin x = 0} := by
  constructor
  · refine ⟨Real.pi, ?_⟩
    exact ⟨Real.pi_pos, Real.sin_pi⟩
  · refine ⟨0, ?_⟩
    intro y hy
    exact le_of_lt hy.1

/-- Helper for Theorem 4.7.7: every positive real zero of sine is at least `π`. -/
lemma helperForTheorem_4_7_7_pi_is_lower_bound_of_positive_sine_zeros
    (y : ℝ) (hy_pos : 0 < y) (hy_sin : Real.sin y = 0) :
    Real.pi ≤ y := by
  rcases (Real.sin_eq_zero_iff.mp hy_sin) with ⟨n, hn⟩
  have hn_real_pos : 0 < (n : ℝ) := by
    have hmul_pos : 0 < (n : ℝ) * Real.pi := by
      simpa [hn] using hy_pos
    exact (mul_pos_iff_of_pos_right Real.pi_pos).mp hmul_pos
  have hn_int_pos : 0 < n := (Int.cast_pos.mp hn_real_pos)
  have hn_one_le : (1 : ℤ) ≤ n := by
    exact (Int.add_one_le_iff.mpr hn_int_pos)
  have hcast_one_le : (1 : ℝ) ≤ (n : ℝ) := by
    exact_mod_cast hn_one_le
  have hmul_le : (1 : ℝ) * Real.pi ≤ (n : ℝ) * Real.pi := by
    exact mul_le_mul_of_nonneg_right hcast_one_le (le_of_lt Real.pi_pos)
  have hpi_le : Real.pi ≤ (n : ℝ) * Real.pi := by
    simpa using hmul_le
  simpa [hn] using hpi_le

/-- Helper for Theorem 4.7.7: the definition of `firstPositiveSineZero` agrees with `Real.pi`. -/
lemma helperForTheorem_4_7_7_firstPositiveSineZero_eq_pi :
    firstPositiveSineZero = Real.pi := by
  let S : Set ℝ := {x : ℝ | x ∈ Set.Ioi (0 : ℝ) ∧ Real.sin x = 0}
  have hSB : Set.Nonempty S ∧ BddBelow S := by
    simpa [S] using helperForTheorem_4_7_7_positiveSineZeroSet_nonempty_bddBelow
  have hS_nonempty : Set.Nonempty S := hSB.1
  have hS_bddBelow : BddBelow S := hSB.2
  have hpi_mem_S : Real.pi ∈ S := by
    exact ⟨Real.pi_pos, Real.sin_pi⟩
  have hsInf_le_pi : sInf S ≤ Real.pi := csInf_le hS_bddBelow hpi_mem_S
  have hpi_le_sInf : Real.pi ≤ sInf S := by
    refine le_csInf hS_nonempty ?_
    intro y hy
    exact helperForTheorem_4_7_7_pi_is_lower_bound_of_positive_sine_zeros y hy.1 hy.2
  have hsInf_eq_pi : sInf S = Real.pi := le_antisymm hsInf_le_pi hpi_le_sInf
  simpa [firstPositiveSineZero, S] using hsInf_eq_pi

/-- Helper for Theorem 4.7.7: transport `π`-identities to `firstPositiveSineZero`. -/
lemma helperForTheorem_4_7_7_transport_antiperiodic_periodic
    (hpi : firstPositiveSineZero = Real.pi) :
    (∀ x : ℝ,
      Real.cos (x + firstPositiveSineZero) = -Real.cos x ∧
      Real.sin (x + firstPositiveSineZero) = -Real.sin x) ∧
    (∀ x : ℝ,
      Real.cos (x + 2 * firstPositiveSineZero) = Real.cos x ∧
      Real.sin (x + 2 * firstPositiveSineZero) = Real.sin x) ∧
    Function.Periodic Real.cos (2 * firstPositiveSineZero) ∧
    Function.Periodic Real.sin (2 * firstPositiveSineZero) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x
    constructor
    · simpa [hpi] using (Real.cos_add_pi x)
    · simpa [hpi] using (Real.sin_add_pi x)
  · intro x
    constructor
    · simpa [hpi] using (Real.cos_add_two_pi x)
    · simpa [hpi] using (Real.sin_add_two_pi x)
  · simpa [hpi] using (Real.cos_periodic)
  · simpa [hpi] using (Real.sin_periodic)

/-- Theorem 4.7.7: For every real number x (with π from Definition 4.7.2),
cos (x + π) = -cos x and sin (x + π) = -sin x.
In particular, cos (x + 2π) = cos x and sin (x + 2π) = sin x,
so sin and cos are periodic with period 2π. -/
theorem real_sine_cosine_pi_antiperiodicity_and_two_pi_periodicity :
    (∀ x : ℝ,
      Real.cos (x + firstPositiveSineZero) = -Real.cos x ∧
      Real.sin (x + firstPositiveSineZero) = -Real.sin x) ∧
    (∀ x : ℝ,
      Real.cos (x + 2 * firstPositiveSineZero) = Real.cos x ∧
      Real.sin (x + 2 * firstPositiveSineZero) = Real.sin x) ∧
    Function.Periodic Real.cos (2 * firstPositiveSineZero) ∧
    Function.Periodic Real.sin (2 * firstPositiveSineZero) := by
  have hpi : firstPositiveSineZero = Real.pi :=
    helperForTheorem_4_7_7_firstPositiveSineZero_eq_pi
  exact helperForTheorem_4_7_7_transport_antiperiodic_periodic hpi

/-- Helper for Theorem 4.7.8: `firstPositiveSineZero` is nonzero. -/
lemma helperForTheorem_4_7_8_firstPositiveSineZero_ne_zero :
    firstPositiveSineZero ≠ 0 := by
  have hpi : firstPositiveSineZero = Real.pi :=
    helperForTheorem_4_7_7_firstPositiveSineZero_eq_pi
  simpa [hpi] using (Real.pi_ne_zero : Real.pi ≠ 0)

/-- Helper for Theorem 4.7.8: divide-by-`firstPositiveSineZero` form equals
integer-multiple-of-`π` form. -/
lemma helperForTheorem_4_7_8_div_eq_int_iff_mul_eq_int_pi (x : ℝ) (n : ℤ) :
    x / firstPositiveSineZero = (n : ℝ) ↔ x = (n : ℝ) * Real.pi := by
  have hpi : firstPositiveSineZero = Real.pi :=
    helperForTheorem_4_7_7_firstPositiveSineZero_eq_pi
  constructor
  · intro hdiv
    have hmul : x = (n : ℝ) * firstPositiveSineZero := by
      exact (div_eq_iff helperForTheorem_4_7_8_firstPositiveSineZero_ne_zero).mp hdiv
    calc
      x = (n : ℝ) * firstPositiveSineZero := hmul
      _ = (n : ℝ) * Real.pi := by rw [hpi]
  · intro hmulPi
    have hmul : x = (n : ℝ) * firstPositiveSineZero := by
      calc
        x = (n : ℝ) * Real.pi := hmulPi
        _ = (n : ℝ) * firstPositiveSineZero := by rw [hpi]
    exact (div_eq_iff helperForTheorem_4_7_8_firstPositiveSineZero_ne_zero).mpr hmul

/-- Helper for Theorem 4.7.8: the integer-existence formulations using
division by `firstPositiveSineZero` and multiplication by `π` are equivalent. -/
lemma helperForTheorem_4_7_8_exists_div_eq_int_iff_exists_mul_eq_int_pi (x : ℝ) :
    (∃ n : ℤ, x / firstPositiveSineZero = (n : ℝ)) ↔
      (∃ n : ℤ, x = (n : ℝ) * Real.pi) := by
  constructor
  · intro h
    rcases h with ⟨n, hn⟩
    refine ⟨n, ?_⟩
    exact (helperForTheorem_4_7_8_div_eq_int_iff_mul_eq_int_pi x n).mp hn
  · intro h
    rcases h with ⟨n, hn⟩
    refine ⟨n, ?_⟩
    exact (helperForTheorem_4_7_8_div_eq_int_iff_mul_eq_int_pi x n).mpr hn

/-- Theorem 4.7.8: For every real number `x` (with `π` given by Definition 4.7.2),
`Real.sin x = 0` if and only if `x / π` is an integer. -/
theorem real_sine_eq_zero_iff_div_firstPositiveSineZero_integer (x : ℝ) :
    Real.sin x = 0 ↔ ∃ n : ℤ, x / firstPositiveSineZero = (n : ℝ) := by
  constructor
  · intro hsin
    have hmul : ∃ n : ℤ, (n : ℝ) * Real.pi = x := (Real.sin_eq_zero_iff).mp hsin
    have hmul' : ∃ n : ℤ, x = (n : ℝ) * Real.pi := by
      rcases hmul with ⟨n, hn⟩
      exact ⟨n, hn.symm⟩
    exact (helperForTheorem_4_7_8_exists_div_eq_int_iff_exists_mul_eq_int_pi x).mpr hmul'
  · intro hdiv
    have hmul : ∃ n : ℤ, x = (n : ℝ) * Real.pi :=
      (helperForTheorem_4_7_8_exists_div_eq_int_iff_exists_mul_eq_int_pi x).mp hdiv
    have hmul' : ∃ n : ℤ, (n : ℝ) * Real.pi = x := by
      rcases hmul with ⟨n, hn⟩
      exact ⟨n, hn.symm⟩
    exact (Real.sin_eq_zero_iff).mpr hmul'

end Section07
end Chap04
