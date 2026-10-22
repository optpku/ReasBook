/-
Authors: Zichen Wang, Wanli Ma, Shu Miao, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Mathlib

section Chap05
section Section02

/-- Definition 5.2.1 (Inner product): for `f, g ∈ C(ℝ/ℤ;ℂ)` (modeled as continuous,
`ℤ`-periodic functions `ℝ → ℂ`), define
`⟪f, g⟫ = ∫ x in [0,1], f x * conj (g x) dx`. -/
noncomputable def periodicInnerProduct
    (f g : {h : ℝ → ℂ // Continuous h ∧ Function.Periodic h 1}) : ℂ :=
  ∫ x in Set.Icc (0 : ℝ) 1, f.1 x * star (g.1 x)

/-- Orthogonality for continuous, `1`-periodic complex-valued functions. -/
def periodicOrthogonal
    (f g : {h : ℝ → ℂ // Continuous h ∧ Function.Periodic h 1}) : Prop :=
  periodicInnerProduct f g = 0

/-- The `L^2` metric on continuous, `1`-periodic complex-valued functions. -/
noncomputable def periodicL2Metric
    (f g : {h : ℝ → ℂ // Continuous h ∧ Function.Periodic h 1}) : ℝ :=
  Real.sqrt (∫ x in Set.Icc (0 : ℝ) 1, ‖f.1 x - g.1 x‖ ^ (2 : ℕ))

/-- Definition 5.2.2 (Orthogonality and the `L^2` metric): for
`f, g ∈ C(ℝ/ℤ;ℂ)` (modeled as continuous, `1`-periodic functions `ℝ → ℂ`),
(i) `f` and `g` are orthogonal iff `⟪f, g⟫ = 0`; and
(ii) `d_{L^2}(f,g) = (∫_[0,1] ‖f(x) - g(x)‖^2 dx)^(1/2)`. -/
noncomputable def periodicOrthogonalityAndL2Metric :
    ({h : ℝ → ℂ // Continuous h ∧ Function.Periodic h 1} →
      {h : ℝ → ℂ // Continuous h ∧ Function.Periodic h 1} → Prop) ×
    ({h : ℝ → ℂ // Continuous h ∧ Function.Periodic h 1} →
      {h : ℝ → ℂ // Continuous h ∧ Function.Periodic h 1} → ℝ) :=
  (periodicOrthogonal, periodicL2Metric)

/-- Definition 5.2.3 (`L^2`-convergence): for a sequence `(f_n)` in
`C(ℝ/ℤ;ℂ)` and `f ∈ C(ℝ/ℤ;ℂ)`, `(f_n)` converges to `f` in `L^2` when
`d_{L^2}(f_n, f) → 0` as `n → ∞`. -/
def periodicL2ConvergesTo
    (fSeq : ℕ → {h : ℝ → ℂ // Continuous h ∧ Function.Periodic h 1})
    (f : {h : ℝ → ℂ // Continuous h ∧ Function.Periodic h 1}) : Prop :=
  Filter.Tendsto (fun n => periodicL2Metric (fSeq n) f) Filter.atTop (nhds (0 : ℝ))

/-- The constant function `x ↦ 1` is continuous and `1`-periodic. -/
lemma continuous_periodic_constOne :
    Continuous (fun _ : ℝ => (1 : ℂ)) ∧ Function.Periodic (fun _ : ℝ => (1 : ℂ)) 1 := by
  constructor
  · simpa using (continuous_const : Continuous (fun _ : ℝ => (1 : ℂ)))
  · intro x
    simp

/-- The function `x ↦ exp(2πix)` is continuous and `1`-periodic. -/
lemma continuous_periodic_expTwoPiI :
    Continuous (fun x : ℝ => Complex.exp (2 * Real.pi * Complex.I * x)) ∧
      Function.Periodic (fun x : ℝ => Complex.exp (2 * Real.pi * Complex.I * x)) 1 := by
  constructor
  · have hPhase : Continuous (fun x : ℝ => (2 * Real.pi * Complex.I) * (x : ℂ)) :=
      continuous_const.mul Complex.continuous_ofReal
    simpa [mul_assoc] using Complex.continuous_exp.comp hPhase
  · intro x
    calc
      Complex.exp (2 * Real.pi * Complex.I * (x + 1 : ℝ))
          = Complex.exp ((2 * Real.pi * Complex.I * (x : ℂ)) + (2 * Real.pi * Complex.I)) := by
              simp [mul_add, mul_assoc, add_comm, add_left_comm, add_assoc]
      _ = Complex.exp (2 * Real.pi * Complex.I * (x : ℂ)) * Complex.exp (2 * Real.pi * Complex.I) := by
            simpa using Complex.exp_add (2 * Real.pi * Complex.I * (x : ℂ)) (2 * Real.pi * Complex.I)
      _ = Complex.exp (2 * Real.pi * Complex.I * (x : ℂ)) := by
            simp [Complex.exp_two_pi_mul_I]
      _ = Complex.exp (2 * Real.pi * Complex.I * x) := by simp

/-- The `1`-periodic function induced by the constant function `x ↦ 1`. -/
noncomputable def constOnePeriodicFunction :
    {h : ℝ → ℂ // Continuous h ∧ Function.Periodic h 1} :=
  ⟨fun _ : ℝ => (1 : ℂ), continuous_periodic_constOne⟩

/-- The `1`-periodic function induced by `x ↦ exp(2πix)`. -/
noncomputable def expTwoPiIPeriodicFunction :
    {h : ℝ → ℂ // Continuous h ∧ Function.Periodic h 1} :=
  ⟨fun x : ℝ => Complex.exp (2 * Real.pi * Complex.I * x), continuous_periodic_expTwoPiI⟩

/-- Helper for Example 5.2.3: rewrite the integrand as an exponential with negative coefficient. -/
lemma helperForExample_5_2_3_integrand_rewrite (x : ℝ) :
    (1 : ℂ) * star (Complex.exp (2 * Real.pi * Complex.I * x)) =
      Complex.exp ((-(2 * Real.pi * Complex.I)) * x) := by
  set z : ℂ := 2 * Real.pi * Complex.I * x
  have hExp : star (Complex.exp z) = Complex.exp (star z) := by
    simpa using (Complex.exp_conj z).symm
  calc
    (1 : ℂ) * star (Complex.exp (2 * Real.pi * Complex.I * x))
        = (1 : ℂ) * star (Complex.exp z) := by simp [z]
    _ = star (Complex.exp z) := by simp
    _ = Complex.exp (star z) := hExp
    _ = Complex.exp ((-(2 * Real.pi * Complex.I)) * x) := by
          simp [z, mul_comm, mul_left_comm]

/-- Helper for Example 5.2.3: the exponential coefficient is nonzero. -/
lemma helperForExample_5_2_3_coeff_ne_zero :
    ((-(2 * Real.pi * Complex.I)) : ℂ) ≠ 0 := by
  exact neg_ne_zero.mpr Complex.two_pi_I_ne_zero

/-- Helper for Example 5.2.3: the endpoint value `exp(-2πi)` equals `1`. -/
lemma helperForExample_5_2_3_exp_neg_twoPiI_eq_one :
    Complex.exp (-(2 * Real.pi * Complex.I)) = 1 := by
  simpa [Int.cast_neg, Int.cast_one, one_mul] using Complex.exp_int_mul_two_pi_mul_I (-1)

/-- Helper for Example 5.2.3: the relevant exponential integral on `[0,1]` vanishes. -/
lemma helperForExample_5_2_3_interval_integral_exp_neg_twoPiI :
    ∫ x in Set.Icc (0 : ℝ) 1, Complex.exp ((-(2 * Real.pi * Complex.I)) * x) = 0 := by
  have h01 : (0 : ℝ) ≤ 1 := by norm_num
  rw [MeasureTheory.integral_Icc_eq_integral_Ioc]
  rw [← intervalIntegral.integral_of_le
    (f := fun x : ℝ => Complex.exp ((-(2 * Real.pi * Complex.I)) * x)) h01]
  rw [integral_exp_mul_complex (a := (0 : ℝ)) (b := (1 : ℝ))
    (c := (-(2 * Real.pi * Complex.I))) helperForExample_5_2_3_coeff_ne_zero]
  simp [helperForExample_5_2_3_exp_neg_twoPiI_eq_one]

/-- Example 5.2.3: let `f(x) = 1` and `g(x) = exp(2πix)`. Then `⟪f, g⟫ = 0`. -/
theorem periodicInnerProduct_constOne_expTwoPiI :
    periodicInnerProduct constOnePeriodicFunction expTwoPiIPeriodicFunction = 0 := by
  simp [periodicInnerProduct, constOnePeriodicFunction, expTwoPiIPeriodicFunction]
  have hInt :
      (∫ x in Set.Icc (0 : ℝ) 1, (starRingEnd ℂ) (Complex.exp (2 * Real.pi * Complex.I * x))) =
        ∫ x in Set.Icc (0 : ℝ) 1, Complex.exp ((-(2 * Real.pi * Complex.I)) * x) := by
    refine MeasureTheory.integral_congr_ae ?_
    filter_upwards with x
    simpa using (helperForExample_5_2_3_integrand_rewrite x)
  rw [hInt]
  exact helperForExample_5_2_3_interval_integral_exp_neg_twoPiI

/-- The `L^2` norm on continuous, `1`-periodic complex-valued functions induced by
the inner product `⟪f, g⟫ = ∫_[0,1] f \overline{g}`. -/
noncomputable def periodicL2Norm
    (f : {h : ℝ → ℂ // Continuous h ∧ Function.Periodic h 1}) : ℝ :=
  Real.sqrt (periodicInnerProduct f f).re

/-- Helper for Example 5.2.6: the self-inner-product integrand is identically `1`. -/
lemma helperForExample_5_2_6_pointwise_selfInner_integrand_eq_one (x : ℝ) :
    Complex.exp (2 * Real.pi * Complex.I * x) *
        star (Complex.exp (2 * Real.pi * Complex.I * x)) = (1 : ℂ) := by
  let z : ℂ := Complex.exp (2 * Real.pi * Complex.I * x)
  have hzNorm : ‖z‖ = 1 := by
    dsimp [z]
    simpa [mul_assoc, mul_comm, mul_left_comm] using
      (Complex.norm_exp_ofReal_mul_I (2 * Real.pi * x))
  calc
    Complex.exp (2 * Real.pi * Complex.I * x) * star (Complex.exp (2 * Real.pi * Complex.I * x))
        = ((Complex.normSq z : ℝ) : ℂ) := by
            simpa [z] using (Complex.mul_conj z)
    _ = ((‖z‖ ^ (2 : ℕ) : ℝ) : ℂ) := by
          simp [Complex.normSq_eq_norm_sq]
    _ = (1 : ℂ) := by simp [hzNorm]

/-- Helper for Example 5.2.6: the self-inner product of `exp(2πix)` equals `1`. -/
lemma helperForExample_5_2_6_innerProduct_self_eq_one :
    periodicInnerProduct expTwoPiIPeriodicFunction expTwoPiIPeriodicFunction = (1 : ℂ) := by
  unfold periodicInnerProduct
  have hInt :
      (∫ x in Set.Icc (0 : ℝ) 1,
          expTwoPiIPeriodicFunction.1 x * star (expTwoPiIPeriodicFunction.1 x))
        = ∫ x in Set.Icc (0 : ℝ) 1, (1 : ℂ) := by
    refine MeasureTheory.integral_congr_ae ?_
    filter_upwards with x
    simpa [expTwoPiIPeriodicFunction] using
      (helperForExample_5_2_6_pointwise_selfInner_integrand_eq_one x)
  rw [hInt]
  simp

/-- Helper for Example 5.2.6: the real part of the self-inner product is `1`. -/
lemma helperForExample_5_2_6_realpart_selfInner_eq_one :
    (periodicInnerProduct expTwoPiIPeriodicFunction expTwoPiIPeriodicFunction).re = 1 := by
  rw [helperForExample_5_2_6_innerProduct_self_eq_one]
  norm_num

/-- Example 5.2.6: for `f(x) = exp(2πix)`, one has `‖f‖_2 = 1`. -/
theorem expTwoPiIPeriodicFunction_l2Norm_eq_one :
    periodicL2Norm expTwoPiIPeriodicFunction = 1 := by
  simp [periodicL2Norm, helperForExample_5_2_6_realpart_selfInner_eq_one]

/-- Helper for Lemma 5.2.7a: rewrite `Re ⟪f,f⟫` as an interval integral of `normSq`. -/
lemma helperForLemma_5_2_7a_re_eq_intervalIntegral_normSq
    (f : {h : ℝ → ℂ // Continuous h ∧ Function.Periodic h 1}) :
    (periodicInnerProduct f f).re = ∫ x in (0 : ℝ)..1, Complex.normSq (f.1 x) := by
  have hInt :
      MeasureTheory.Integrable
        (fun x : ℝ => ((Complex.normSq (f.1 x) : ℝ) : ℂ))
        (MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) 1)) := by
    exact (Complex.continuous_ofReal.comp (Complex.continuous_normSq.comp f.2.1)).integrableOn_Icc
  have hSet :
      (periodicInnerProduct f f).re =
        ∫ x in Set.Icc (0 : ℝ) 1, Complex.normSq (f.1 x) := by
    unfold periodicInnerProduct
    have hMul :
        (∫ x in Set.Icc (0 : ℝ) 1, f.1 x * star (f.1 x)) =
          ∫ x in Set.Icc (0 : ℝ) 1, ((Complex.normSq (f.1 x) : ℝ) : ℂ) := by
      refine MeasureTheory.integral_congr_ae ?_
      filter_upwards with x
      simpa using (Complex.mul_conj (f.1 x))
    rw [hMul]
    have hReInt :
        (∫ x in Set.Icc (0 : ℝ) 1, Complex.normSq (f.1 x)) =
          (∫ x in Set.Icc (0 : ℝ) 1, ((Complex.normSq (f.1 x) : ℝ) : ℂ)).re := by
      simpa using (integral_re hInt)
    exact hReInt.symm
  have h01 : (0 : ℝ) ≤ 1 := by norm_num
  rw [hSet, MeasureTheory.integral_Icc_eq_integral_Ioc]
  rw [← intervalIntegral.integral_of_le (f := fun x : ℝ => Complex.normSq (f.1 x)) h01]

/-- Helper for Lemma 5.2.7a: a nonzero periodic function is nonzero at some point
of the unit interval. -/
lemma helperForLemma_5_2_7a_exists_nonzero_in_unit_interval
    (f : {h : ℝ → ℂ // Continuous h ∧ Function.Periodic h 1})
    (hne : f.1 ≠ 0) :
    ∃ x ∈ Set.Icc (0 : ℝ) 1, f.1 x ≠ 0 := by
  rcases not_forall.mp (by
      intro hAll
      apply hne
      ext x
      exact hAll x) with ⟨x0, hx0⟩
  let y : ℝ := x0 - (Int.floor x0 : ℤ) • (1 : ℝ)
  have hz : ((Int.floor x0 : ℤ) • (1 : ℝ)) = (Int.floor x0 : ℝ) := by simp
  have hy_mem : y ∈ Set.Icc (0 : ℝ) 1 := by
    constructor
    · dsimp [y]
      rw [hz]
      have hfloor : (Int.floor x0 : ℝ) ≤ x0 := Int.floor_le x0
      linarith
    · dsimp [y]
      rw [hz]
      have hlt : x0 < (Int.floor x0 : ℝ) + 1 := Int.lt_floor_add_one x0
      linarith
  have hy_eq : f.1 y = f.1 x0 := by
    dsimp [y]
    simpa using (f.2.2.sub_zsmul_eq (x := x0) (n := Int.floor x0))
  refine ⟨y, hy_mem, ?_⟩
  rw [hy_eq]
  exact hx0

/-- Helper for Lemma 5.2.7a: if a periodic function is nonzero, then `Re ⟪f,f⟫` is
strictly positive. -/
lemma helperForLemma_5_2_7a_re_pos_of_nonzero
    (f : {h : ℝ → ℂ // Continuous h ∧ Function.Periodic h 1})
    (hne : f.1 ≠ 0) :
    0 < (periodicInnerProduct f f).re := by
  rcases helperForLemma_5_2_7a_exists_nonzero_in_unit_interval f hne with ⟨x0, hx0mem, hx0ne⟩
  have hcontOn :
      ContinuousOn (fun x : ℝ => Complex.normSq (f.1 x)) (Set.Icc (0 : ℝ) 1) :=
    (Complex.continuous_normSq.comp f.2.1).continuousOn
  have hIntPos : 0 < ∫ x in (0 : ℝ)..1, Complex.normSq (f.1 x) := by
    refine intervalIntegral.integral_pos (a := (0 : ℝ)) (b := (1 : ℝ)) ?_ hcontOn ?_ ?_
    · norm_num
    · intro x hx
      exact Complex.normSq_nonneg (f.1 x)
    · refine ⟨x0, hx0mem, ?_⟩
      exact Complex.normSq_pos.mpr hx0ne
  rw [helperForLemma_5_2_7a_re_eq_intervalIntegral_normSq]
  exact hIntPos

/-- Helper for Lemma 5.2.7a: vanishing real part of the self-inner product is
equivalent to the function being zero. -/
lemma helperForLemma_5_2_7a_re_eq_zero_iff_fun_zero
    (f : {h : ℝ → ℂ // Continuous h ∧ Function.Periodic h 1}) :
    (periodicInnerProduct f f).re = 0 ↔ f.1 = 0 := by
  constructor
  · intro hReZero
    by_contra hne
    have hPos : 0 < (periodicInnerProduct f f).re :=
      helperForLemma_5_2_7a_re_pos_of_nonzero f hne
    linarith
  · intro hfZero
    simpa [periodicInnerProduct, hfZero]

/-- Helper for Lemma 5.2.7a: `‖f‖_2 = 0` is equivalent to vanishing real part of
the self-inner product. -/
lemma helperForLemma_5_2_7a_l2_eq_zero_iff_re_eq_zero
    (f : {h : ℝ → ℂ // Continuous h ∧ Function.Periodic h 1}) :
    periodicL2Norm f = 0 ↔ (periodicInnerProduct f f).re = 0 := by
  have hNonneg : 0 ≤ (periodicInnerProduct f f).re := by
    have h01 : (0 : ℝ) ≤ 1 := by norm_num
    rw [helperForLemma_5_2_7a_re_eq_intervalIntegral_normSq]
    exact intervalIntegral.integral_nonneg h01 (fun x hx => Complex.normSq_nonneg (f.1 x))
  simpa [periodicL2Norm] using (Real.sqrt_eq_zero hNonneg)

/-- Lemma 5.2.7a (Basic properties of `‖·‖_2` (a), non-degeneracy): for
`f ∈ C(ℝ/ℤ; ℂ)` (modeled as a continuous, `1`-periodic function `ℝ → ℂ`),
`‖f‖_2 = 0` iff `f` is the zero function. -/
lemma periodicL2Norm_eq_zero_iff
    (f : {h : ℝ → ℂ // Continuous h ∧ Function.Periodic h 1}) :
    periodicL2Norm f = 0 ↔ f.1 = 0 := by
  exact (helperForLemma_5_2_7a_l2_eq_zero_iff_re_eq_zero f).trans
    (helperForLemma_5_2_7a_re_eq_zero_iff_fun_zero f)

/-- Helper for Lemma 5.2.7b: continuity on `[0,1]` gives `L²` membership on the restricted measure. -/
lemma helperForLemma_5_2_7b_memLp_two_restrict_Icc
    (u : {h : ℝ → ℂ // Continuous h ∧ Function.Periodic h 1}) :
    MeasureTheory.MemLp (fun x => u.1 x) 2
      (MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) 1)) := by
  have hInt :
      MeasureTheory.Integrable
        (fun x : ℝ => ‖u.1 x‖ ^ (2 : ℕ))
        (MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) 1)) := by
    exact (u.2.1.norm.pow 2).integrableOn_Icc
  exact
    (MeasureTheory.memLp_two_iff_integrable_sq_norm
      (μ := MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) 1))
      (hf := u.2.1.aestronglyMeasurable)).2 hInt

/-- Helper for Lemma 5.2.7b: pointwise norm of the inner-product integrand factors. -/
lemma helperForLemma_5_2_7b_pointwise_norm_mul_star
    (f g : {h : ℝ → ℂ // Continuous h ∧ Function.Periodic h 1}) (x : ℝ) :
    ‖f.1 x * star (g.1 x)‖ = ‖f.1 x‖ * ‖g.1 x‖ := by
  simpa [norm_star] using norm_mul (f.1 x) (star (g.1 x))

/-- Helper for Lemma 5.2.7b: Hölder with `p = q = 2` on `[0,1]` for norm-products. -/
lemma helperForLemma_5_2_7b_holder_norm_on_Icc
    (f g : {h : ℝ → ℂ // Continuous h ∧ Function.Periodic h 1}) :
    ∫ x in Set.Icc (0 : ℝ) 1, ‖f.1 x‖ * ‖g.1 x‖
      ≤ (∫ x in Set.Icc (0 : ℝ) 1, ‖f.1 x‖ ^ (2 : ℝ)) ^ (1 / (2 : ℝ))
          * (∫ x in Set.Icc (0 : ℝ) 1, ‖g.1 x‖ ^ (2 : ℝ)) ^ (1 / (2 : ℝ)) := by
  let μ : MeasureTheory.Measure ℝ := MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) 1)
  have hpq : (2 : ℝ).HolderConjugate (2 : ℝ) := by
    rw [Real.holderConjugate_iff]
    norm_num
  have hfMem : MeasureTheory.MemLp (fun x => f.1 x) (ENNReal.ofReal (2 : ℝ)) μ := by
    simpa [μ] using helperForLemma_5_2_7b_memLp_two_restrict_Icc f
  have hgMem : MeasureTheory.MemLp (fun x => g.1 x) (ENNReal.ofReal (2 : ℝ)) μ := by
    simpa [μ] using helperForLemma_5_2_7b_memLp_two_restrict_Icc g
  simpa [μ] using
    (MeasureTheory.integral_mul_norm_le_Lp_mul_Lq
      (μ := μ) (f := fun x => f.1 x) (g := fun x => g.1 x)
      (p := (2 : ℝ)) (q := (2 : ℝ)) hpq hfMem hgMem)

/-- Helper for Lemma 5.2.7b: each Hölder `L²` factor is exactly `periodicL2Norm`. -/
lemma helperForLemma_5_2_7b_rhs_factor_eq_periodicL2Norm
    (u : {h : ℝ → ℂ // Continuous h ∧ Function.Periodic h 1}) :
    (∫ x in Set.Icc (0 : ℝ) 1, ‖u.1 x‖ ^ (2 : ℝ)) ^ (1 / (2 : ℝ)) = periodicL2Norm u := by
  have h01 : (0 : ℝ) ≤ 1 := by norm_num
  have hReEq :
      (periodicInnerProduct u u).re =
        ∫ x in Set.Icc (0 : ℝ) 1, ‖u.1 x‖ ^ (2 : ℝ) := by
    calc
      (periodicInnerProduct u u).re
          = ∫ x in (0 : ℝ)..1, Complex.normSq (u.1 x) :=
            helperForLemma_5_2_7a_re_eq_intervalIntegral_normSq u
      _ = ∫ x in Set.Icc (0 : ℝ) 1, Complex.normSq (u.1 x) := by
            rw [MeasureTheory.integral_Icc_eq_integral_Ioc]
            rw [← intervalIntegral.integral_of_le (f := fun x : ℝ => Complex.normSq (u.1 x)) h01]
      _ = ∫ x in Set.Icc (0 : ℝ) 1, ‖u.1 x‖ ^ (2 : ℝ) := by
            refine MeasureTheory.integral_congr_ae ?_
            filter_upwards with x
            simp [Complex.normSq_eq_norm_sq, Real.rpow_natCast]
  rw [periodicL2Norm, ← hReEq]
  rw [Real.sqrt_eq_rpow]

/-- Lemma 5.2.7b (Basic properties of `‖·‖_2` (b), Cauchy--Schwarz): for
`f, g ∈ C(ℝ/ℤ; ℂ)` (modeled as continuous, `1`-periodic functions `ℝ → ℂ`),
`|⟪f, g⟫| ≤ ‖f‖_2 ‖g‖_2`. -/
lemma periodicInnerProduct_abs_le_periodicL2Norm_mul
    (f g : {h : ℝ → ℂ // Continuous h ∧ Function.Periodic h 1}) :
    ‖periodicInnerProduct f g‖ ≤ periodicL2Norm f * periodicL2Norm g := by
  have hNormIntegral :
      ‖periodicInnerProduct f g‖ ≤
        ∫ x in Set.Icc (0 : ℝ) 1, ‖f.1 x * star (g.1 x)‖ := by
    unfold periodicInnerProduct
    simpa using
      (MeasureTheory.norm_integral_le_integral_norm
        (f := fun x : ℝ => f.1 x * star (g.1 x))
        (μ := MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) 1)))
  have hPointwiseNormRewrite :
      (∫ x in Set.Icc (0 : ℝ) 1, ‖f.1 x * star (g.1 x)‖)
        = ∫ x in Set.Icc (0 : ℝ) 1, ‖f.1 x‖ * ‖g.1 x‖ := by
    refine MeasureTheory.integral_congr_ae ?_
    filter_upwards with x
    exact helperForLemma_5_2_7b_pointwise_norm_mul_star f g x
  have hHolder :
      ∫ x in Set.Icc (0 : ℝ) 1, ‖f.1 x‖ * ‖g.1 x‖
        ≤ (∫ x in Set.Icc (0 : ℝ) 1, ‖f.1 x‖ ^ (2 : ℝ)) ^ (1 / (2 : ℝ))
            * (∫ x in Set.Icc (0 : ℝ) 1, ‖g.1 x‖ ^ (2 : ℝ)) ^ (1 / (2 : ℝ)) :=
    helperForLemma_5_2_7b_holder_norm_on_Icc f g
  have hfFactor :
      (∫ x in Set.Icc (0 : ℝ) 1, ‖f.1 x‖ ^ (2 : ℝ)) ^ (1 / (2 : ℝ)) = periodicL2Norm f :=
    helperForLemma_5_2_7b_rhs_factor_eq_periodicL2Norm f
  have hgFactor :
      (∫ x in Set.Icc (0 : ℝ) 1, ‖g.1 x‖ ^ (2 : ℝ)) ^ (1 / (2 : ℝ)) = periodicL2Norm g :=
    helperForLemma_5_2_7b_rhs_factor_eq_periodicL2Norm g
  refine hNormIntegral.trans ?_
  rw [hPointwiseNormRewrite]
  calc
    ∫ x in Set.Icc (0 : ℝ) 1, ‖f.1 x‖ * ‖g.1 x‖
        ≤ (∫ x in Set.Icc (0 : ℝ) 1, ‖f.1 x‖ ^ (2 : ℝ)) ^ (1 / (2 : ℝ))
            * (∫ x in Set.Icc (0 : ℝ) 1, ‖g.1 x‖ ^ (2 : ℝ)) ^ (1 / (2 : ℝ)) := hHolder
    _ = periodicL2Norm f * periodicL2Norm g := by rw [hfFactor, hgFactor]

/-- Helper for Lemma 5.2.5a: swapping the two arguments in the integrand gives
its complex conjugate pointwise. -/
lemma helperForLemma_5_2_5a_pointwise_swap_to_conj
    (f g : {h : ℝ → ℂ // Continuous h ∧ Function.Periodic h 1}) (x : ℝ) :
    g.1 x * star (f.1 x) = star (f.1 x * star (g.1 x)) := by
  simp [mul_comm, mul_left_comm, mul_assoc]

/-- Helper for Lemma 5.2.5a: conjugation commutes with integration over `[0,1]`. -/
lemma helperForLemma_5_2_5a_conj_of_setIntegral_Icc
    (f g : {h : ℝ → ℂ // Continuous h ∧ Function.Periodic h 1}) :
    (∫ x in Set.Icc (0 : ℝ) 1, star (f.1 x * star (g.1 x))) =
      star (∫ x in Set.Icc (0 : ℝ) 1, f.1 x * star (g.1 x)) := by
  simpa using
    (integral_conj
      (μ := MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) 1))
      (f := fun x : ℝ => f.1 x * star (g.1 x)))

/-- Lemma 5.2.5a (Properties of the inner product (a), Hermitian): if
`f, g ∈ C(ℝ/ℤ; ℂ)` (modeled as continuous, `1`-periodic functions `ℝ → ℂ`), then
`⟪g, f⟫ = \overline{⟪f, g⟫}`. -/
lemma periodicInnerProduct_hermitian
    (f g : {h : ℝ → ℂ // Continuous h ∧ Function.Periodic h 1}) :
    periodicInnerProduct g f = star (periodicInnerProduct f g) := by
  unfold periodicInnerProduct
  calc
    ∫ x in Set.Icc (0 : ℝ) 1, g.1 x * star (f.1 x)
      = ∫ x in Set.Icc (0 : ℝ) 1, star (f.1 x * star (g.1 x)) := by
          refine MeasureTheory.integral_congr_ae ?_
          filter_upwards with x
          exact helperForLemma_5_2_5a_pointwise_swap_to_conj f g x
    _ = star (∫ x in Set.Icc (0 : ℝ) 1, f.1 x * star (g.1 x)) :=
          helperForLemma_5_2_5a_conj_of_setIntegral_Icc f g
    _ = star (∫ x in Set.Icc (0 : ℝ) 1, f.1 x * star (g.1 x)) := rfl

/-- Helper for Lemma 5.2.5b: rewrite `⟪f,f⟫` as the integral of `normSq`. -/
lemma helperForLemma_5_2_5b_self_eq_setIntegral_normSq
    (f : {h : ℝ → ℂ // Continuous h ∧ Function.Periodic h 1}) :
    periodicInnerProduct f f =
      ∫ x in Set.Icc (0 : ℝ) 1, ((Complex.normSq (f.1 x) : ℝ) : ℂ) := by
  unfold periodicInnerProduct
  refine MeasureTheory.integral_congr_ae ?_
  filter_upwards with x
  simpa using (Complex.mul_conj (f.1 x))

/-- Helper for Lemma 5.2.5b: the real part of `⟪f,f⟫` is an interval integral
of `normSq`. -/
lemma helperForLemma_5_2_5b_re_eq_intervalIntegral_normSq
    (f : {h : ℝ → ℂ // Continuous h ∧ Function.Periodic h 1}) :
    (periodicInnerProduct f f).re = ∫ x in (0 : ℝ)..1, Complex.normSq (f.1 x) := by
  have hInt :
      MeasureTheory.Integrable
        (fun x : ℝ => ((Complex.normSq (f.1 x) : ℝ) : ℂ))
        (MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) 1)) := by
    exact (Complex.continuous_ofReal.comp (Complex.continuous_normSq.comp f.2.1)).integrableOn_Icc
  have hSet :
      (periodicInnerProduct f f).re =
        ∫ x in Set.Icc (0 : ℝ) 1, Complex.normSq (f.1 x) := by
    rw [helperForLemma_5_2_5b_self_eq_setIntegral_normSq]
    have hReInt :
        (∫ x in Set.Icc (0 : ℝ) 1, Complex.normSq (f.1 x)) =
          (∫ x in Set.Icc (0 : ℝ) 1, ((Complex.normSq (f.1 x) : ℝ) : ℂ)).re := by
      simpa using (integral_re hInt)
    exact hReInt.symm
  have h01 : (0 : ℝ) ≤ 1 := by norm_num
  rw [hSet, MeasureTheory.integral_Icc_eq_integral_Ioc]
  rw [← intervalIntegral.integral_of_le (f := fun x : ℝ => Complex.normSq (f.1 x)) h01]

/-- Helper for Lemma 5.2.5b: a nonzero periodic function is nonzero at some point
in one fundamental domain. -/
lemma helperForLemma_5_2_5b_exists_nonzero_in_unit_interval
    (f : {h : ℝ → ℂ // Continuous h ∧ Function.Periodic h 1})
    (hne : f.1 ≠ 0) :
    ∃ x ∈ Set.Icc (0 : ℝ) 1, f.1 x ≠ 0 := by
  rcases not_forall.mp (by
      intro hAll
      apply hne
      ext x
      exact hAll x) with ⟨x0, hx0⟩
  let y : ℝ := x0 - (Int.floor x0 : ℤ) • (1 : ℝ)
  have hz : ((Int.floor x0 : ℤ) • (1 : ℝ)) = (Int.floor x0 : ℝ) := by simp
  have hy_mem : y ∈ Set.Icc (0 : ℝ) 1 := by
    constructor
    · dsimp [y]
      rw [hz]
      have hfloor : (Int.floor x0 : ℝ) ≤ x0 := Int.floor_le x0
      linarith
    · dsimp [y]
      rw [hz]
      have hlt : x0 < (Int.floor x0 : ℝ) + 1 := Int.lt_floor_add_one x0
      linarith
  have hy_eq : f.1 y = f.1 x0 := by
    dsimp [y]
    simpa using (f.2.2.sub_zsmul_eq (x := x0) (n := Int.floor x0))
  refine ⟨y, hy_mem, ?_⟩
  rw [hy_eq]
  exact hx0

/-- Helper for Lemma 5.2.5b: a nonzero value on `[0,1]` forces strict
positivity of `Re ⟪f,f⟫`. -/
lemma helperForLemma_5_2_5b_re_pos_of_exists_nonzero_in_unit_interval
    (f : {h : ℝ → ℂ // Continuous h ∧ Function.Periodic h 1})
    (hExists : ∃ x ∈ Set.Icc (0 : ℝ) 1, f.1 x ≠ 0) :
    0 < (periodicInnerProduct f f).re := by
  rcases hExists with ⟨x0, hx0mem, hx0ne⟩
  have hcontOn : ContinuousOn (fun x : ℝ => Complex.normSq (f.1 x)) (Set.Icc (0 : ℝ) 1) :=
    (Complex.continuous_normSq.comp f.2.1).continuousOn
  have hIntPos : 0 < ∫ x in (0 : ℝ)..1, Complex.normSq (f.1 x) := by
    refine intervalIntegral.integral_pos (a := (0 : ℝ)) (b := (1 : ℝ)) ?_ hcontOn ?_ ?_
    · norm_num
    · intro x hx
      exact Complex.normSq_nonneg (f.1 x)
    · refine ⟨x0, hx0mem, ?_⟩
      exact Complex.normSq_pos.mpr hx0ne
  rw [helperForLemma_5_2_5b_re_eq_intervalIntegral_normSq]
  exact hIntPos

/-- Helper for Lemma 5.2.5b: the imaginary part of `⟪f,f⟫` vanishes. -/
lemma helperForLemma_5_2_5b_self_im_eq_zero
    (f : {h : ℝ → ℂ // Continuous h ∧ Function.Periodic h 1}) :
    (periodicInnerProduct f f).im = 0 := by
  have hSelfConj : star (periodicInnerProduct f f) = periodicInnerProduct f f := by
    simpa using (periodicInnerProduct_hermitian f f).symm
  exact (Complex.conj_eq_iff_im.mp hSelfConj)

/-- Lemma 5.2.5b (Properties of the inner product (b), Positivity): if
`f ∈ C(ℝ/ℤ; ℂ)` (modeled as a continuous, `1`-periodic function `ℝ → ℂ`), then
`⟪f, f⟫` is real and nonnegative, and `⟪f, f⟫ = 0` iff `f` is the zero function. -/
lemma periodicInnerProduct_positivity
    (f : {h : ℝ → ℂ // Continuous h ∧ Function.Periodic h 1}) :
    (0 : ℝ) ≤ (periodicInnerProduct f f).re ∧
      (periodicInnerProduct f f).im = 0 ∧
      (periodicInnerProduct f f = 0 ↔ f.1 = 0) := by
  constructor
  · have h01 : (0 : ℝ) ≤ 1 := by norm_num
    rw [helperForLemma_5_2_5b_re_eq_intervalIntegral_normSq]
    exact intervalIntegral.integral_nonneg h01 (fun x hx => Complex.normSq_nonneg (f.1 x))
  constructor
  · exact helperForLemma_5_2_5b_self_im_eq_zero f
  · constructor
    · intro hInnerZero
      by_contra hne
      have hExists : ∃ x ∈ Set.Icc (0 : ℝ) 1, f.1 x ≠ 0 :=
        helperForLemma_5_2_5b_exists_nonzero_in_unit_interval f hne
      have hPos : 0 < (periodicInnerProduct f f).re :=
        helperForLemma_5_2_5b_re_pos_of_exists_nonzero_in_unit_interval f hExists
      have hReZero : (periodicInnerProduct f f).re = 0 := by simpa [hInnerZero]
      linarith
    · intro hfZero
      simp [periodicInnerProduct, hfZero]

/-- The sum of two continuous, `1`-periodic complex-valued functions is continuous and
`1`-periodic. -/
lemma continuous_periodic_add
    (f g : {h : ℝ → ℂ // Continuous h ∧ Function.Periodic h 1}) :
    Continuous (f.1 + g.1) ∧ Function.Periodic (f.1 + g.1) 1 := by
  constructor
  · exact f.2.1.add g.2.1
  · simpa using f.2.2.add g.2.2

/-- A scalar multiple of a continuous, `1`-periodic complex-valued function is continuous
and `1`-periodic. -/
lemma continuous_periodic_smul
    (c : ℂ) (f : {h : ℝ → ℂ // Continuous h ∧ Function.Periodic h 1}) :
    Continuous (c • f.1) ∧ Function.Periodic (c • f.1) 1 := by
  constructor
  · simpa [Pi.smul_apply] using (continuous_const.mul f.2.1)
  · simpa [Pi.smul_apply] using f.2.2.smul c

/-- The pointwise sum in `C(ℝ/ℤ; ℂ)` modeled as continuous, `1`-periodic functions
`ℝ → ℂ`. -/
noncomputable def addPeriodicFunction
    (f g : {h : ℝ → ℂ // Continuous h ∧ Function.Periodic h 1}) :
    {h : ℝ → ℂ // Continuous h ∧ Function.Periodic h 1} :=
  ⟨f.1 + g.1, continuous_periodic_add f g⟩

/-- Scalar multiplication in `C(ℝ/ℤ; ℂ)` modeled as continuous, `1`-periodic functions
`ℝ → ℂ`. -/
noncomputable def smulPeriodicFunction
    (c : ℂ) (f : {h : ℝ → ℂ // Continuous h ∧ Function.Periodic h 1}) :
    {h : ℝ → ℂ // Continuous h ∧ Function.Periodic h 1} :=
  ⟨c • f.1, continuous_periodic_smul c f⟩

/-- Helper for Lemma 5.2.7c: pointwise expansion of
`(f + g) * conj (f + g)`. -/
lemma helperForLemma_5_2_7c_pointwise_add_self_integrand_expand
    (f g : {h : ℝ → ℂ // Continuous h ∧ Function.Periodic h 1}) (x : ℝ) :
    ((f.1 + g.1) x) * star ((f.1 + g.1) x) =
      f.1 x * star (f.1 x) + f.1 x * star (g.1 x) + g.1 x * star (f.1 x) +
        g.1 x * star (g.1 x) := by
  simp [add_mul, mul_add, add_assoc, add_left_comm, add_comm]

/-- Helper for Lemma 5.2.7c: expansion of `⟪f + g, f + g⟫` into diagonal and
cross terms. -/
lemma helperForLemma_5_2_7c_inner_add_self_expand
    (f g : {h : ℝ → ℂ // Continuous h ∧ Function.Periodic h 1}) :
    periodicInnerProduct (addPeriodicFunction f g) (addPeriodicFunction f g) =
      periodicInnerProduct f f + periodicInnerProduct f g +
        periodicInnerProduct g f + periodicInnerProduct g g := by
  have hIntFF :
      MeasureTheory.Integrable
        (fun x : ℝ => f.1 x * star (f.1 x))
        (MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) 1)) := by
    exact (f.2.1.mul (continuous_star.comp f.2.1)).integrableOn_Icc
  have hIntFG :
      MeasureTheory.Integrable
        (fun x : ℝ => f.1 x * star (g.1 x))
        (MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) 1)) := by
    exact (f.2.1.mul (continuous_star.comp g.2.1)).integrableOn_Icc
  have hIntGF :
      MeasureTheory.Integrable
        (fun x : ℝ => g.1 x * star (f.1 x))
        (MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) 1)) := by
    exact (g.2.1.mul (continuous_star.comp f.2.1)).integrableOn_Icc
  have hIntGG :
      MeasureTheory.Integrable
        (fun x : ℝ => g.1 x * star (g.1 x))
        (MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) 1)) := by
    exact (g.2.1.mul (continuous_star.comp g.2.1)).integrableOn_Icc
  have hIntLeft :
      MeasureTheory.Integrable
        (fun x : ℝ => f.1 x * star (f.1 x) + f.1 x * star (g.1 x))
        (MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) 1)) :=
    hIntFF.add hIntFG
  have hIntRight :
      MeasureTheory.Integrable
        (fun x : ℝ => g.1 x * star (f.1 x) + g.1 x * star (g.1 x))
        (MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) 1)) :=
    hIntGF.add hIntGG
  unfold periodicInnerProduct
  calc
    ∫ x in Set.Icc (0 : ℝ) 1,
        (addPeriodicFunction f g).1 x * star ((addPeriodicFunction f g).1 x)
        = ∫ x in Set.Icc (0 : ℝ) 1,
            (f.1 x * star (f.1 x) + f.1 x * star (g.1 x)) +
              (g.1 x * star (f.1 x) + g.1 x * star (g.1 x)) := by
            refine MeasureTheory.integral_congr_ae ?_
            filter_upwards with x
            have hPointwise :
                ((addPeriodicFunction f g).1 x) * star ((addPeriodicFunction f g).1 x) =
                  f.1 x * star (f.1 x) + f.1 x * star (g.1 x) + g.1 x * star (f.1 x) +
                    g.1 x * star (g.1 x) := by
              simpa [addPeriodicFunction] using
                (helperForLemma_5_2_7c_pointwise_add_self_integrand_expand f g x)
            calc
              ((addPeriodicFunction f g).1 x) * star ((addPeriodicFunction f g).1 x)
                  = f.1 x * star (f.1 x) + f.1 x * star (g.1 x) + g.1 x * star (f.1 x) +
                      g.1 x * star (g.1 x) := hPointwise
              _ = (f.1 x * star (f.1 x) + f.1 x * star (g.1 x)) +
                    (g.1 x * star (f.1 x) + g.1 x * star (g.1 x)) := by
                    ring
    _ = (∫ x in Set.Icc (0 : ℝ) 1, f.1 x * star (f.1 x) + f.1 x * star (g.1 x)) +
          (∫ x in Set.Icc (0 : ℝ) 1, g.1 x * star (f.1 x) + g.1 x * star (g.1 x)) := by
            rw [MeasureTheory.integral_add hIntLeft hIntRight]
    _ = (∫ x in Set.Icc (0 : ℝ) 1, f.1 x * star (f.1 x)) +
          (∫ x in Set.Icc (0 : ℝ) 1, f.1 x * star (g.1 x)) +
          ((∫ x in Set.Icc (0 : ℝ) 1, g.1 x * star (f.1 x)) +
            (∫ x in Set.Icc (0 : ℝ) 1, g.1 x * star (g.1 x))) := by
            rw [MeasureTheory.integral_add hIntFF hIntFG,
              MeasureTheory.integral_add hIntGF hIntGG]
    _ = (∫ x in Set.Icc (0 : ℝ) 1, f.1 x * star (f.1 x)) +
          (∫ x in Set.Icc (0 : ℝ) 1, f.1 x * star (g.1 x)) +
          (∫ x in Set.Icc (0 : ℝ) 1, g.1 x * star (f.1 x)) +
          (∫ x in Set.Icc (0 : ℝ) 1, g.1 x * star (g.1 x)) := by
            ring

/-- Helper for Lemma 5.2.7c: diagonal terms satisfy
`Re ⟪u, u⟫ = ‖u‖_2^2`. -/
lemma helperForLemma_5_2_7c_re_self_eq_sq_l2Norm
    (u : {h : ℝ → ℂ // Continuous h ∧ Function.Periodic h 1}) :
    (periodicInnerProduct u u).re = periodicL2Norm u ^ (2 : ℕ) := by
  have hNonneg : 0 ≤ (periodicInnerProduct u u).re :=
    (periodicInnerProduct_positivity u).1
  have hSq : (Real.sqrt (periodicInnerProduct u u).re) ^ (2 : ℕ) =
      (periodicInnerProduct u u).re := by
    simpa [pow_two] using (Real.sq_sqrt hNonneg)
  simpa [periodicL2Norm] using hSq.symm

/-- Helper for Lemma 5.2.7c: the real parts of the cross terms are bounded by
`2 ‖f‖_2 ‖g‖_2`. -/
lemma helperForLemma_5_2_7c_cross_re_sum_le_two_mul
    (f g : {h : ℝ → ℂ // Continuous h ∧ Function.Periodic h 1}) :
    (periodicInnerProduct f g).re + (periodicInnerProduct g f).re ≤
      2 * (periodicL2Norm f * periodicL2Norm g) := by
  have hReLeNorm : (periodicInnerProduct f g).re ≤ ‖periodicInnerProduct f g‖ :=
    Complex.re_le_norm (periodicInnerProduct f g)
  have hNormLe : ‖periodicInnerProduct f g‖ ≤ periodicL2Norm f * periodicL2Norm g :=
    periodicInnerProduct_abs_le_periodicL2Norm_mul f g
  have hReLe : (periodicInnerProduct f g).re ≤ periodicL2Norm f * periodicL2Norm g :=
    hReLeNorm.trans hNormLe
  have hSwapRe : (periodicInnerProduct g f).re = (periodicInnerProduct f g).re := by
    calc
      (periodicInnerProduct g f).re = (star (periodicInnerProduct f g)).re := by
        rw [periodicInnerProduct_hermitian]
      _ = (periodicInnerProduct f g).re := by simp
  calc
    (periodicInnerProduct f g).re + (periodicInnerProduct g f).re
        = 2 * (periodicInnerProduct f g).re := by
            rw [hSwapRe]
            ring
    _ ≤ 2 * (periodicL2Norm f * periodicL2Norm g) := by
          gcongr

/-- Helper for Lemma 5.2.7c: the real part of `⟪f+g, f+g⟫` is bounded by
`(‖f‖_2 + ‖g‖_2)^2`. -/
lemma helperForLemma_5_2_7c_re_addSelf_le_sq_sum
    (f g : {h : ℝ → ℂ // Continuous h ∧ Function.Periodic h 1}) :
    (periodicInnerProduct (addPeriodicFunction f g) (addPeriodicFunction f g)).re ≤
      (periodicL2Norm f + periodicL2Norm g) ^ (2 : ℕ) := by
  have hExpandRe :
      (periodicInnerProduct (addPeriodicFunction f g) (addPeriodicFunction f g)).re =
        (periodicInnerProduct f f).re + (periodicInnerProduct f g).re +
          (periodicInnerProduct g f).re + (periodicInnerProduct g g).re := by
    rw [helperForLemma_5_2_7c_inner_add_self_expand f g]
    simp [Complex.add_re, add_assoc, add_left_comm, add_comm]
  have hSelfF : (periodicInnerProduct f f).re = periodicL2Norm f ^ (2 : ℕ) :=
    helperForLemma_5_2_7c_re_self_eq_sq_l2Norm f
  have hSelfG : (periodicInnerProduct g g).re = periodicL2Norm g ^ (2 : ℕ) :=
    helperForLemma_5_2_7c_re_self_eq_sq_l2Norm g
  have hCross :
      (periodicInnerProduct f g).re + (periodicInnerProduct g f).re ≤
        2 * (periodicL2Norm f * periodicL2Norm g) :=
    helperForLemma_5_2_7c_cross_re_sum_le_two_mul f g
  rw [hExpandRe, hSelfF, hSelfG]
  calc
    periodicL2Norm f ^ (2 : ℕ) + (periodicInnerProduct f g).re +
        (periodicInnerProduct g f).re + periodicL2Norm g ^ (2 : ℕ)
        ≤ periodicL2Norm f ^ (2 : ℕ) +
            2 * (periodicL2Norm f * periodicL2Norm g) + periodicL2Norm g ^ (2 : ℕ) := by
              linarith
    _ = (periodicL2Norm f + periodicL2Norm g) ^ (2 : ℕ) := by
          ring

/-- Lemma 5.2.7c (Basic properties of `‖·‖_2` (c), triangle inequality): for
`f, g ∈ C(ℝ/ℤ; ℂ)` (modeled as continuous, `1`-periodic functions `ℝ → ℂ`),
`‖f + g‖_2 ≤ ‖f‖_2 + ‖g‖_2`. -/
lemma periodicL2Norm_add_le
    (f g : {h : ℝ → ℂ // Continuous h ∧ Function.Periodic h 1}) :
    periodicL2Norm (addPeriodicFunction f g) ≤ periodicL2Norm f + periodicL2Norm g := by
  have hSumNonneg : 0 ≤ periodicL2Norm f + periodicL2Norm g := by
    unfold periodicL2Norm
    exact add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have hSquareBound :
      (periodicInnerProduct (addPeriodicFunction f g) (addPeriodicFunction f g)).re ≤
        (periodicL2Norm f + periodicL2Norm g) ^ (2 : ℕ) :=
    helperForLemma_5_2_7c_re_addSelf_le_sq_sum f g
  have hSqrtLe :
      Real.sqrt (periodicInnerProduct (addPeriodicFunction f g) (addPeriodicFunction f g)).re ≤
        periodicL2Norm f + periodicL2Norm g :=
    (Real.sqrt_le_iff).2 ⟨hSumNonneg, hSquareBound⟩
  simpa [periodicL2Norm] using hSqrtLe

/-- Helper for Lemma 5.2.7d: orthogonality is preserved when swapping arguments
by Hermitian symmetry. -/
lemma helperForLemma_5_2_7d_swap_inner_eq_zero_of_orthogonal
    (f g : {h : ℝ → ℂ // Continuous h ∧ Function.Periodic h 1})
    (hfg : periodicInnerProduct f g = 0) :
    periodicInnerProduct g f = 0 := by
  calc
    periodicInnerProduct g f = star (periodicInnerProduct f g) :=
      periodicInnerProduct_hermitian f g
    _ = 0 := by simp [hfg]

/-- Helper for Lemma 5.2.7d: the sum of the real parts of the two cross terms
vanishes under orthogonality. -/
lemma helperForLemma_5_2_7d_cross_re_sum_eq_zero_of_orthogonal
    (f g : {h : ℝ → ℂ // Continuous h ∧ Function.Periodic h 1})
    (hfg : periodicInnerProduct f g = 0) :
    (periodicInnerProduct f g).re + (periodicInnerProduct g f).re = 0 := by
  have hgf : periodicInnerProduct g f = 0 :=
    helperForLemma_5_2_7d_swap_inner_eq_zero_of_orthogonal f g hfg
  simp [hfg, hgf]

/-- Helper for Lemma 5.2.7d: the real part of `⟪f+g, f+g⟫` equals the sum of
the squared `L^2` norms when `⟪f, g⟫ = 0`. -/
lemma helperForLemma_5_2_7d_re_addSelf_eq_sq_sum_of_orthogonal
    (f g : {h : ℝ → ℂ // Continuous h ∧ Function.Periodic h 1})
    (hfg : periodicInnerProduct f g = 0) :
    (periodicInnerProduct (addPeriodicFunction f g) (addPeriodicFunction f g)).re =
      periodicL2Norm f ^ (2 : ℕ) + periodicL2Norm g ^ (2 : ℕ) := by
  have hExpandRe :
      (periodicInnerProduct (addPeriodicFunction f g) (addPeriodicFunction f g)).re =
        (periodicInnerProduct f f).re + (periodicInnerProduct f g).re +
          (periodicInnerProduct g f).re + (periodicInnerProduct g g).re := by
    rw [helperForLemma_5_2_7c_inner_add_self_expand f g]
    simp [Complex.add_re, add_assoc, add_left_comm, add_comm]
  have hSelfF : (periodicInnerProduct f f).re = periodicL2Norm f ^ (2 : ℕ) :=
    helperForLemma_5_2_7c_re_self_eq_sq_l2Norm f
  have hSelfG : (periodicInnerProduct g g).re = periodicL2Norm g ^ (2 : ℕ) :=
    helperForLemma_5_2_7c_re_self_eq_sq_l2Norm g
  have hCrossZero :
      (periodicInnerProduct f g).re + (periodicInnerProduct g f).re = 0 :=
    helperForLemma_5_2_7d_cross_re_sum_eq_zero_of_orthogonal f g hfg
  rw [hExpandRe, hSelfF, hSelfG]
  calc
    periodicL2Norm f ^ (2 : ℕ) + (periodicInnerProduct f g).re +
        (periodicInnerProduct g f).re + periodicL2Norm g ^ (2 : ℕ)
        = periodicL2Norm f ^ (2 : ℕ) +
            ((periodicInnerProduct f g).re + (periodicInnerProduct g f).re) +
            periodicL2Norm g ^ (2 : ℕ) := by ring
    _ = periodicL2Norm f ^ (2 : ℕ) + 0 + periodicL2Norm g ^ (2 : ℕ) := by
          rw [hCrossZero]
    _ = periodicL2Norm f ^ (2 : ℕ) + periodicL2Norm g ^ (2 : ℕ) := by ring

/-- Lemma 5.2.7d (Basic properties of `‖·‖_2` (d), Pythagoras): for
`f, g ∈ C(ℝ/ℤ; ℂ)` (modeled as continuous, `1`-periodic functions `ℝ → ℂ`),
if `⟪f, g⟫ = 0`, then `‖f + g‖_2^2 = ‖f‖_2^2 + ‖g‖_2^2`. -/
lemma periodicL2Norm_pythagoras
    (f g : {h : ℝ → ℂ // Continuous h ∧ Function.Periodic h 1})
    (hfg : periodicInnerProduct f g = 0) :
    periodicL2Norm (addPeriodicFunction f g) ^ (2 : ℕ) =
      periodicL2Norm f ^ (2 : ℕ) + periodicL2Norm g ^ (2 : ℕ) := by
  calc
    periodicL2Norm (addPeriodicFunction f g) ^ (2 : ℕ)
        = (periodicInnerProduct (addPeriodicFunction f g) (addPeriodicFunction f g)).re :=
          (helperForLemma_5_2_7c_re_self_eq_sq_l2Norm (addPeriodicFunction f g)).symm
    _ = periodicL2Norm f ^ (2 : ℕ) + periodicL2Norm g ^ (2 : ℕ) :=
          helperForLemma_5_2_7d_re_addSelf_eq_sq_sum_of_orthogonal f g hfg

/-- Helper for Lemma 5.2.7e: pointwise scaling of `normSq` under scalar multiplication. -/
lemma helperForLemma_5_2_7e_pointwise_normSq_smul
    (c : ℂ) (f : {h : ℝ → ℂ // Continuous h ∧ Function.Periodic h 1}) (x : ℝ) :
    Complex.normSq ((smulPeriodicFunction c f).1 x) =
      (‖c‖ ^ (2 : ℕ)) * Complex.normSq (f.1 x) := by
  calc
    Complex.normSq ((smulPeriodicFunction c f).1 x)
        = Complex.normSq (c * f.1 x) := by
            simp [smulPeriodicFunction]
    _ = Complex.normSq c * Complex.normSq (f.1 x) := by
          rw [Complex.normSq_mul]
    _ = (‖c‖ ^ (2 : ℕ)) * Complex.normSq (f.1 x) := by
          simp [Complex.normSq_eq_norm_sq]

/-- Helper for Lemma 5.2.7e: nonnegativity of the real part of `⟪f,f⟫`. -/
lemma helperForLemma_5_2_7e_re_self_nonneg
    (f : {h : ℝ → ℂ // Continuous h ∧ Function.Periodic h 1}) :
    0 ≤ (periodicInnerProduct f f).re :=
  (periodicInnerProduct_positivity f).1

/-- Helper for Lemma 5.2.7e: the real part of `⟪cf,cf⟫` scales by `‖c‖²`. -/
lemma helperForLemma_5_2_7e_re_inner_self_smul
    (c : ℂ) (f : {h : ℝ → ℂ // Continuous h ∧ Function.Periodic h 1}) :
    (periodicInnerProduct (smulPeriodicFunction c f) (smulPeriodicFunction c f)).re =
      (‖c‖ ^ (2 : ℕ)) * (periodicInnerProduct f f).re := by
  calc
    (periodicInnerProduct (smulPeriodicFunction c f) (smulPeriodicFunction c f)).re
        = ∫ x in (0 : ℝ)..1, Complex.normSq ((smulPeriodicFunction c f).1 x) := by
            rw [helperForLemma_5_2_7a_re_eq_intervalIntegral_normSq]
    _ = ∫ x in (0 : ℝ)..1, (‖c‖ ^ (2 : ℕ)) * Complex.normSq (f.1 x) := by
          refine intervalIntegral.integral_congr_ae ?_
          filter_upwards with x hx
          rw [helperForLemma_5_2_7e_pointwise_normSq_smul]
    _ = (‖c‖ ^ (2 : ℕ)) * ∫ x in (0 : ℝ)..1, Complex.normSq (f.1 x) := by
          rw [intervalIntegral.integral_const_mul]
    _ = (‖c‖ ^ (2 : ℕ)) * (periodicInnerProduct f f).re := by
          rw [← helperForLemma_5_2_7a_re_eq_intervalIntegral_normSq]

/-- Helper for Lemma 5.2.7e: pull `‖c‖²` out of a square root. -/
lemma helperForLemma_5_2_7e_sqrt_mul_sq_norm
    (c : ℂ) {t : ℝ} (ht : 0 ≤ t) :
    Real.sqrt ((‖c‖ ^ (2 : ℕ)) * t) = ‖c‖ * Real.sqrt t := by
  calc
    Real.sqrt ((‖c‖ ^ (2 : ℕ)) * t)
        = Real.sqrt (t * (‖c‖ ^ (2 : ℕ))) := by ring
    _ = Real.sqrt t * Real.sqrt (‖c‖ ^ (2 : ℕ)) := by
          rw [Real.sqrt_mul ht]
    _ = Real.sqrt t * ‖c‖ := by
          rw [Real.sqrt_sq_eq_abs]
          simp [abs_of_nonneg (norm_nonneg c)]
    _ = ‖c‖ * Real.sqrt t := by ring

/-- Lemma 5.2.7e (Basic properties of `‖·‖_2` (e), homogeneity): for
`f ∈ C(ℝ/ℤ; ℂ)` (modeled as a continuous, `1`-periodic function `ℝ → ℂ`) and
`c ∈ ℂ`, `‖cf‖_2 = ‖c‖ ‖f‖_2`. -/
lemma periodicL2Norm_smul
    (c : ℂ) (f : {h : ℝ → ℂ // Continuous h ∧ Function.Periodic h 1}) :
    periodicL2Norm (smulPeriodicFunction c f) = ‖c‖ * periodicL2Norm f := by
  have hReNonneg : 0 ≤ (periodicInnerProduct f f).re :=
    helperForLemma_5_2_7e_re_self_nonneg f
  unfold periodicL2Norm
  rw [helperForLemma_5_2_7e_re_inner_self_smul]
  simpa using helperForLemma_5_2_7e_sqrt_mul_sq_norm c hReNonneg

/-- Helper for Lemma 5.2.5c: the product integrand defining `⟪u, v⟫` is integrable
on `[0,1]`. -/
lemma helperForLemma_5_2_5c_integrableOn_mul_star
    (u v : {h : ℝ → ℂ // Continuous h ∧ Function.Periodic h 1}) :
    MeasureTheory.IntegrableOn (fun x : ℝ => u.1 x * star (v.1 x)) (Set.Icc (0 : ℝ) 1) := by
  exact (u.2.1.mul (continuous_star.comp v.2.1)).integrableOn_Icc

/-- Helper for Lemma 5.2.5c: expand the additive integrand pointwise. -/
lemma helperForLemma_5_2_5c_addIntegrand_expand
    (f g h : {h : ℝ → ℂ // Continuous h ∧ Function.Periodic h 1}) (x : ℝ) :
    ((f.1 + g.1) x) * star (h.1 x) =
      f.1 x * star (h.1 x) + g.1 x * star (h.1 x) := by
  simp [add_mul]

/-- Helper for Lemma 5.2.5c: factor a scalar from the first-slot integrand. -/
lemma helperForLemma_5_2_5c_smulIntegrand_factor
    (c : ℂ) (f g : {h : ℝ → ℂ // Continuous h ∧ Function.Periodic h 1}) (x : ℝ) :
    (c • f.1) x * star (g.1 x) = c * (f.1 x * star (g.1 x)) := by
  simp [mul_assoc]


end Section02
end Chap05
