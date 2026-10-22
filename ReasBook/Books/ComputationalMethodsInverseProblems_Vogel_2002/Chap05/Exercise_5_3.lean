/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import Mathlib.Analysis.Fourier.Inversion
public import Mathlib.Analysis.Fourier.Convolution
public import Mathlib.Analysis.Real.Pi.Bounds
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.Data.Complex.Basic
public import Mathlib.Data.Set.Function

public section

noncomputable section

open scoped FourierTransform RealInnerProductSpace Convolution

/-- The interval indicator `A` from Exercise 5.3, viewed as a complex-valued
function on `ℝ`. -/
def unitBoxIndicator : ℝ → ℂ :=
  Set.indicator (Set.Icc (-1 : ℝ) 1) (fun _ ↦ (1 : ℂ))

/-- `unitBoxIndicator` is `1` on `[-1, 1]`. -/
@[simp] theorem unitBoxIndicator_of_mem {x : ℝ} (hx : x ∈ Set.Icc (-1 : ℝ) 1) :
    unitBoxIndicator x = 1 := by
  simp [unitBoxIndicator, hx]

/-- `unitBoxIndicator` vanishes off `[-1, 1]`. -/
@[simp] theorem unitBoxIndicator_of_not_mem {x : ℝ} (hx : x ∉ Set.Icc (-1 : ℝ) 1) :
    unitBoxIndicator x = 0 := by
  simp [unitBoxIndicator, hx]

/-- Pointwise source-style formula for `unitBoxIndicator`. -/
theorem unitBoxIndicator_apply (x : ℝ) :
    unitBoxIndicator x =
      if x ∈ Set.Icc (-1 : ℝ) 1 then
        (1 : ℂ)
      else
        0 := by
  by_cases hx : x ∈ Set.Icc (-1 : ℝ) 1
  · rw [if_pos hx, unitBoxIndicator_of_mem hx]
  · rw [if_neg hx, unitBoxIndicator_of_not_mem hx]

/-- The source term `|𝓕⁻ A|^2` for `A = unitBoxIndicator`, viewed as a
complex-valued function via `Complex.ofReal`. -/
def inverseUnitBoxPowerSpectrum : ℝ → ℂ :=
  fun x ↦ Complex.ofReal (Complex.normSq ((𝓕⁻ unitBoxIndicator) x))

/-- The triangular ramp from Exercise 5.3, written as the explicit complex-valued
function `x ↦ max (2 - |x|) 0`. -/
def triangleRamp : ℝ → ℂ :=
  fun x ↦ ((max (2 - |x|) 0 : ℝ) : ℂ)

/-- `triangleRamp` is the affine profile `2 - |x|` on `[-2, 2]`. -/
@[simp] theorem triangleRamp_of_mem {x : ℝ} (hx : x ∈ Set.Icc (-2 : ℝ) 2) :
    triangleRamp x = ((2 - |x| : ℝ) : ℂ) := by
  rcases hx with ⟨hx₁, hx₂⟩
  have habs : |x| ≤ 2 := abs_le.2 ⟨hx₁, hx₂⟩
  simp [triangleRamp, max_eq_left (sub_nonneg.2 habs)]

/-- `triangleRamp` vanishes off `[-2, 2]`. -/
@[simp] theorem triangleRamp_of_not_mem {x : ℝ} (hx : x ∉ Set.Icc (-2 : ℝ) 2) :
    triangleRamp x = 0 := by
  have habs : ¬ |x| ≤ 2 := by
    intro h
    exact hx (abs_le.1 h)
  simp [triangleRamp, max_eq_right (sub_nonpos.2 (le_of_not_ge habs))]

/-- Pointwise source-style formula for `triangleRamp` on `[-2, 2]` and its
vanishing outside that interval. -/
theorem triangleRamp_eq_piecewise (x : ℝ) :
    triangleRamp x =
      if x ∈ Set.Icc (-2 : ℝ) 2 then
        ((2 - |x| : ℝ) : ℂ)
      else
        0 := by
  by_cases hx : x ∈ Set.Icc (-2 : ℝ) 2
  · rw [if_pos hx, triangleRamp_of_mem hx]
  · rw [if_neg hx, triangleRamp_of_not_mem hx]

/-- Helper for Exercise 5.3: `unitBoxIndicator` is integrable because it is constant on the finite
interval `[-1, 1]`. -/
lemma unitBoxIndicator_integrable : MeasureTheory.Integrable unitBoxIndicator := by
  -- Restrict the constant function `1` to a finite-measure interval.
  refine (MeasureTheory.integrableOn_const (s := Set.Icc (-1 : ℝ) 1) ?_).integrable_indicator
    measurableSet_Icc
  simp [Real.volume_Icc]

/-- Helper for Exercise 5.3: the shifted unit-box membership rewritten in the convolution
variable. -/
lemma mem_unitBoxShift_iff {x t : ℝ} :
    x - t ∈ Set.Icc (-1 : ℝ) 1 ↔ t ∈ Set.Icc (x - 1) (x + 1) := by
  constructor
  · intro h
    rcases h with ⟨h₁, h₂⟩
    constructor <;> linarith
  · intro h
    rcases h with ⟨h₁, h₂⟩
    constructor <;> linarith

/-- Helper for Exercise 5.3: the convolution integrand is the indicator of the overlap interval. -/
lemma unitBoxIndicator_mul_shift_eq_indicator (x t : ℝ) :
    unitBoxIndicator t * unitBoxIndicator (x - t) =
      (Set.Icc (-1 : ℝ) 1 ∩ Set.Icc (x - 1) (x + 1)).indicator (fun _ ↦ (1 : ℂ)) t := by
  -- Rewrite both factors into indicator form and match the shifted interval.
  by_cases h₁ : t ∈ Set.Icc (-1 : ℝ) 1
  · by_cases h₂ : t ∈ Set.Icc (x - 1) (x + 1)
    · have hxt : x - t ∈ Set.Icc (-1 : ℝ) 1 := (mem_unitBoxShift_iff).2 h₂
      simp [h₁, h₂, hxt]
    · have hxt : x - t ∉ Set.Icc (-1 : ℝ) 1 := by
        exact mt (mem_unitBoxShift_iff.mp) h₂
      simp [h₁, h₂, hxt]
  · by_cases h₂ : t ∈ Set.Icc (x - 1) (x + 1)
    · have hxt : x - t ∈ Set.Icc (-1 : ℝ) 1 := (mem_unitBoxShift_iff).2 h₂
      simp [h₁, h₂, hxt]
    · have hxt : x - t ∉ Set.Icc (-1 : ℝ) 1 := by
        exact mt (mem_unitBoxShift_iff.mp) h₂
      simp [h₁, h₂, hxt]

/-- Helper for Exercise 5.3: for `0 ≤ x ≤ 2`, the overlap of the two unit boxes is
`[x - 1, 1]`. -/
lemma unitBoxIntersection_nonneg {x : ℝ} (hx₀ : 0 ≤ x) (_hx₂ : x ≤ 2) :
    Set.Icc (-1 : ℝ) 1 ∩ Set.Icc (x - 1) (x + 1) = Set.Icc (x - 1) 1 := by
  ext t
  constructor
  · intro ht
    rcases ht with ⟨ht₁, ht₂⟩
    rcases ht₂ with ⟨ht₂₁, ht₂₂⟩
    exact ⟨ht₂₁, ht₁.2⟩
  · intro ht
    rcases ht with ⟨ht₁, ht₂⟩
    constructor
    · have hleft : -1 ≤ t := by
        linarith
      exact ⟨hleft, ht₂⟩
    · have hright : t ≤ x + 1 := by
        linarith
      exact ⟨ht₁, hright⟩

/-- Helper for Exercise 5.3: for `-2 ≤ x ≤ 0`, the overlap of the two unit boxes is
`[-1, x + 1]`. -/
lemma unitBoxIntersection_nonpos {x : ℝ} (hx₀ : x ≤ 0) (_hx₂ : -2 ≤ x) :
    Set.Icc (-1 : ℝ) 1 ∩ Set.Icc (x - 1) (x + 1) = Set.Icc (-1 : ℝ) (x + 1) := by
  ext t
  constructor
  · intro ht
    rcases ht with ⟨ht₁, ht₂⟩
    rcases ht₂ with ⟨ht₂₁, ht₂₂⟩
    exact ⟨ht₁.1, ht₂₂⟩
  · intro ht
    rcases ht with ⟨ht₁, ht₂⟩
    constructor
    · have hright : t ≤ 1 := by
        linarith
      exact ⟨ht₁, hright⟩
    · have hleft : x - 1 ≤ t := by
        linarith
      exact ⟨hleft, ht₂⟩

/-- Helper for Exercise 5.3: for `x > 2`, the two unit boxes do not overlap. -/
lemma unitBoxIntersection_gt_two {x : ℝ} (hx : 2 < x) :
    Set.Icc (-1 : ℝ) 1 ∩ Set.Icc (x - 1) (x + 1) = ∅ := by
  ext t
  constructor
  · intro ht
    rcases ht with ⟨ht₁, ht₂⟩
    have : x - 1 ≤ 1 := le_trans ht₂.1 ht₁.2
    linarith
  · intro ht
    simpa using ht

/-- Helper for Exercise 5.3: for `x < -2`, the two unit boxes do not overlap. -/
lemma unitBoxIntersection_lt_negTwo {x : ℝ} (hx : x < -2) :
    Set.Icc (-1 : ℝ) 1 ∩ Set.Icc (x - 1) (x + 1) = ∅ := by
  ext t
  constructor
  · intro ht
    rcases ht with ⟨ht₁, ht₂⟩
    have : -1 ≤ x + 1 := le_trans ht₁.1 ht₂.2
    linarith
  · intro ht
    simpa using ht

/-- Helper for Exercise 5.3: the Fourier transform of the interval indicator is the usual sinc
profile. -/
lemma fourier_unitBoxIndicator_eq_twoSinc (x : ℝ) :
    𝓕 unitBoxIndicator x = (((2 * Real.sinc (2 * Real.pi * x)) : ℝ) : ℂ) := by
  let c : ℝ := -2 * Real.pi * x
  have hrewrite :
      (∫ v : ℝ, Complex.exp (↑(-2 * Real.pi * v * x) * Complex.I) • unitBoxIndicator v) =
        ∫ v : ℝ in Set.Icc (-1 : ℝ) 1, Complex.exp (↑(-2 * Real.pi * v * x) * Complex.I) := by
    -- Replace the indicator-valued source by a set integral over its support.
    calc
      ∫ v : ℝ, Complex.exp (↑(-2 * Real.pi * v * x) * Complex.I) • unitBoxIndicator v =
          ∫ v : ℝ, (Set.Icc (-1 : ℝ) 1).indicator
            (fun v ↦ Complex.exp (↑(-2 * Real.pi * v * x) * Complex.I)) v := by
            refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall ?_)
            intro v
            by_cases hv : v ∈ Set.Icc (-1 : ℝ) 1 <;> simp [unitBoxIndicator, hv, smul_eq_mul]
      _ = ∫ v : ℝ in Set.Icc (-1 : ℝ) 1, Complex.exp (↑(-2 * Real.pi * v * x) * Complex.I) := by
            rw [MeasureTheory.integral_indicator measurableSet_Icc]
  by_cases hx : x = 0
  · -- At the origin the Fourier integral is just the interval length.
    subst hx
    rw [Real.fourier_real_eq_integral_exp_smul, hrewrite]
    norm_num [Real.sinc_zero]
  · have hc : c ≠ 0 := by
      dsimp [c]
      have hcoeff : (-2 * Real.pi : ℝ) ≠ 0 := by
        nlinarith [Real.pi_pos]
      exact mul_ne_zero hcoeff hx
    -- Rewrite the integral over the support and rescale it to the standard sinc integral.
    rw [Real.fourier_real_eq_integral_exp_smul, hrewrite]
    have hIcc :
        (∫ t in Set.Icc (-1 : ℝ) 1, Complex.exp ((-2 * Real.pi * t * x : ℝ) * Complex.I)) =
          ∫ t in Set.Ioc (-1 : ℝ) 1, Complex.exp ((-2 * Real.pi * t * x : ℝ) * Complex.I) := by
      exact MeasureTheory.integral_Icc_eq_integral_Ioc
    rw [hIcc]
    have hIoc :
        (∫ t in Set.Ioc (-1 : ℝ) 1, Complex.exp ((-2 * Real.pi * t * x : ℝ) * Complex.I)) =
          ∫ t in (-1 : ℝ)..1, Complex.exp ((t * c : ℝ) * Complex.I) := by
      -- The interval integral uses the same set because `-1 ≤ 1`.
      simpa [c, Set.uIoc_of_le (show (-1 : ℝ) ≤ 1 by norm_num), mul_assoc, mul_left_comm,
        mul_comm] using
        (intervalIntegral.intervalIntegral_eq_integral_uIoc
          (f := fun t : ℝ ↦ Complex.exp ((t * c : ℝ) * Complex.I)) (-1) 1
          MeasureTheory.volume).symm
    rw [hIoc]
    have hrescale :
        (∫ t in (-1 : ℝ)..1, Complex.exp ((t * c : ℝ) * Complex.I)) =
          c⁻¹ • ∫ u in -c..c, Complex.exp (u * Complex.I) := by
      simpa [c, mul_assoc] using
        (intervalIntegral.integral_comp_mul_right
          (f := fun u : ℝ ↦ Complex.exp (u * Complex.I)) (a := -1) (b := 1) (c := c) hc)
    have hscale : (c⁻¹ : ℝ) * (2 * c * Real.sinc c) = 2 * Real.sinc c := by
      field_simp [hc]
    calc
      ∫ t in (-1 : ℝ)..1, Complex.exp ((t * c : ℝ) * Complex.I)
          = c⁻¹ • ∫ u in -c..c, Complex.exp (u * Complex.I) := hrescale
      _ = (((2 * Real.sinc c) : ℝ) : ℂ) := by
          rw [integral_exp_mul_I_eq_sinc]
          simpa [smul_eq_mul, Complex.ofReal_mul, mul_assoc, mul_left_comm, mul_comm] using
            congrArg Complex.ofReal hscale
      _ = (((2 * Real.sinc (2 * Real.pi * x)) : ℝ) : ℂ) := by
          simp [c, Real.sinc_neg, mul_assoc, mul_left_comm, mul_comm]

/-- Helper for Exercise 5.3: the ramp is the self-convolution of the unit-box indicator. -/
lemma triangleRamp_eq_unitBoxIndicator_convolution :
    triangleRamp =
      unitBoxIndicator ⋆[ContinuousLinearMap.mul ℂ ℂ] unitBoxIndicator := by
  ext x
  rw [MeasureTheory.convolution_mul]
  have hintegrand :
      (fun t : ℝ ↦ unitBoxIndicator t * unitBoxIndicator (x - t)) =
        (Set.Icc (-1 : ℝ) 1 ∩ Set.Icc (x - 1) (x + 1)).indicator (fun _ ↦ (1 : ℂ)) := by
    -- The product of the two indicators records the overlap interval.
    funext t
    simpa using unitBoxIndicator_mul_shift_eq_indicator x t
  rw [hintegrand]
  by_cases hx : x ∈ Set.Icc (-2 : ℝ) 2
  · -- Inside `[-2,2]` the overlap interval has length `2 - |x|`.
    rw [triangleRamp_of_mem hx]
    rcases hx with ⟨hx₁, hx₂⟩
    by_cases hx₀ : 0 ≤ x
    · rw [unitBoxIntersection_nonneg hx₀ hx₂,
        MeasureTheory.integral_indicator_const (e := (1 : ℂ)) (s_meas := measurableSet_Icc)]
      have hnonneg' : 0 ≤ 1 - (x - 1) := by linarith
      simp [abs_of_nonneg hx₀, Real.volume_Icc, hnonneg']
      ring_nf
    · have hx₀' : x ≤ 0 := le_of_not_ge hx₀
      rw [unitBoxIntersection_nonpos hx₀' hx₁,
        MeasureTheory.integral_indicator_const (e := (1 : ℂ)) (s_meas := measurableSet_Icc)]
      have hnonneg : 0 ≤ x + 1 + 1 := by linarith
      simp [abs_of_nonpos hx₀', Real.volume_Icc]
      rw [max_eq_left hnonneg]
      rw [Complex.ofReal_add, Complex.ofReal_one, Complex.ofReal_add]
      have htwo : (2 : ℂ) = 1 + 1 := by norm_num
      simpa [htwo, add_assoc, add_left_comm, add_comm]
  · -- Outside `[-2,2]` the two intervals do not overlap, so the convolution vanishes.
    rw [triangleRamp_of_not_mem hx]
    rw [MeasureTheory.integral_indicator_const (e := (1 : ℂ))
      (s_meas := measurableSet_Icc.inter measurableSet_Icc)]
    have houtside : x < -2 ∨ 2 < x := by
      by_contra h
      push_neg at h
      exact hx ⟨h.1, h.2⟩
    rcases houtside with hlt | hgt
    ·
      rw [unitBoxIntersection_lt_negTwo hlt]
      simp
    ·
      rw [unitBoxIntersection_gt_two hgt]
      simp

/-- Helper for Exercise 5.3: the source term is the square of the sinc profile. -/
lemma inverseUnitBoxPowerSpectrum_eq_fourSincSq (x : ℝ) :
    inverseUnitBoxPowerSpectrum x =
      (((4 * Real.sinc (2 * Real.pi * x) ^ 2) : ℝ) : ℂ) := by
  -- Rewrite the inverse Fourier transform using the explicit sinc formula.
  rw [inverseUnitBoxPowerSpectrum, Real.fourierInv_eq_fourier_neg,
    fourier_unitBoxIndicator_eq_twoSinc (-x)]
  have hsinc :
      Real.sinc (2 * Real.pi * -x) = Real.sinc (2 * Real.pi * x) := by
    simpa [mul_assoc, mul_left_comm, mul_comm] using Real.sinc_neg (2 * Real.pi * x)
  simp [Complex.normSq_ofReal]
  ring

/-- Helper for Exercise 5.3: `inverseUnitBoxPowerSpectrum` is the Fourier transform of the ramp. -/
lemma inverseUnitBoxPowerSpectrum_eq_fourier_triangleRamp :
    inverseUnitBoxPowerSpectrum = 𝓕 triangleRamp := by
  ext x
  -- Combine the self-convolution identity with the Fourier convolution theorem.
  rw [inverseUnitBoxPowerSpectrum_eq_fourSincSq x, triangleRamp_eq_unitBoxIndicator_convolution]
  have hconv :
      𝓕 (unitBoxIndicator ⋆[ContinuousLinearMap.mul ℂ ℂ] unitBoxIndicator) x =
        𝓕 unitBoxIndicator x * 𝓕 unitBoxIndicator x :=
    Real.fourier_mul_convolution_eq unitBoxIndicator_integrable unitBoxIndicator_integrable x
  rw [hconv]
  simp [fourier_unitBoxIndicator_eq_twoSinc, Complex.ofReal_mul]
  ring

/-- Helper for Exercise 5.3: the ramp is an even function. -/
lemma triangleRamp_even (x : ℝ) : triangleRamp (-x) = triangleRamp x := by
  -- The formula only depends on `|x|`.
  simp [triangleRamp, abs_neg]

/-- Helper for Exercise 5.3: the ramp is continuous. -/
lemma triangleRamp_continuous : Continuous triangleRamp := by
  -- Compose the real ramp profile with `Complex.ofReal`.
  have hcont : Continuous (fun x : ℝ ↦ max (2 - |x|) 0) := by
    fun_prop
  change Continuous (fun x : ℝ ↦ Complex.ofReal (max (2 - |x|) 0))
  exact Complex.continuous_ofReal.comp hcont

/-- Helper for Exercise 5.3: the ramp has compact support in `[-2, 2]`. -/
lemma triangleRamp_hasCompactSupport : HasCompactSupport triangleRamp := by
  -- Outside `[-2,2]` the explicit formula vanishes, so the support stays in that compact interval.
  have hsubset : tsupport triangleRamp ⊆ Set.Icc (-2 : ℝ) 2 := by
    rw [tsupport]
    refine closure_minimal ?_ isClosed_Icc
    intro x hx
    by_contra hnot
    exact hx (by simpa [triangleRamp_of_not_mem hnot])
  exact (isCompact_Icc : IsCompact (Set.Icc (-2 : ℝ) 2)).of_isClosed_subset
    (isClosed_tsupport triangleRamp) hsubset

/-- Helper for Exercise 5.3: the triangular ramp is integrable. -/
lemma triangleRamp_integrable : MeasureTheory.Integrable triangleRamp := by
  -- A continuous compactly supported function is integrable.
  exact triangleRamp_continuous.integrable_of_hasCompactSupport triangleRamp_hasCompactSupport

/-- Helper for Exercise 5.3: the explicit `sinc²` source is controlled by an `L¹` majorant. -/
lemma inverseUnitBoxPowerSpectrum_bound (x : ℝ) :
    ‖((((4 * Real.sinc (2 * Real.pi * x) ^ 2) : ℝ) : ℂ))‖ ≤ 16 * (1 + x ^ 2)⁻¹ := by
  -- Separate the bounded region `|x| ≤ 1` from the decay region `|x| > 1`.
  have hnorm :
      ‖((((4 * Real.sinc (2 * Real.pi * x) ^ 2) : ℝ) : ℂ))‖ =
        4 * |Real.sinc (2 * Real.pi * x)| ^ 2 := by
    have hnonneg : 0 ≤ 4 * Real.sinc (2 * Real.pi * x) ^ 2 := by positivity
    simpa [RCLike.norm_ofReal, abs_of_nonneg hnonneg, sq_abs]
  rw [hnorm]
  by_cases hx : |x| ≤ 1
  · have hsinc : |Real.sinc (2 * Real.pi * x)| ^ 2 ≤ 1 := by
      have h := Real.abs_sinc_le_one (2 * Real.pi * x)
      have hsq := mul_self_le_mul_self (abs_nonneg _) h
      simpa [pow_two] using hsq
    have hxsq : x ^ 2 ≤ 1 := by
      have hsq := mul_self_le_mul_self (abs_nonneg x) hx
      have : |x| ^ 2 ≤ 1 := by simpa [pow_two] using hsq
      simpa [sq_abs] using this
    have hden : 1 + x ^ 2 ≤ 2 := by
      nlinarith
    have hinv : (1 / 2 : ℝ) ≤ (1 + x ^ 2)⁻¹ := by
      simpa [one_div] using
        (one_div_le_one_div_of_le (show 0 < 1 + x ^ 2 by positivity) hden)
    nlinarith
  · have hxgt : 1 < |x| := by linarith
    have hxne : x ≠ 0 := by
      exact abs_ne_zero.mp (ne_of_gt (by linarith : 0 < |x|))
    have hyne : 2 * Real.pi * x ≠ 0 := by
      exact mul_ne_zero (by positivity) hxne
    have hsinc_abs :
        |Real.sinc (2 * Real.pi * x)| ≤ |2 * Real.pi * x|⁻¹ := by
      calc
        |Real.sinc (2 * Real.pi * x)| =
            |Real.sin (2 * Real.pi * x) / (2 * Real.pi * x)| := by
              rw [Real.sinc_of_ne_zero hyne]
        _ = |Real.sin (2 * Real.pi * x)| / |2 * Real.pi * x| := by
              rw [abs_div]
        _ ≤ 1 / |2 * Real.pi * x| := by
              gcongr
              exact Real.abs_sin_le_one (2 * Real.pi * x)
        _ = |2 * Real.pi * x|⁻¹ := by rw [one_div]
    have hscale : |x| ≤ |2 * Real.pi * x| := by
      rw [abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2), abs_of_pos Real.pi_pos]
      have hcoeff : 1 ≤ 2 * Real.pi := by
        nlinarith [Real.pi_gt_three]
      nlinarith [abs_nonneg x]
    have hinv_scale : |2 * Real.pi * x|⁻¹ ≤ |x|⁻¹ := by
      exact inv_anti₀ (by linarith : 0 < |x|) hscale
    have hsinc_sq : |Real.sinc (2 * Real.pi * x)| ^ 2 ≤ |x|⁻¹ ^ 2 := by
      have hsinc_abs' : |Real.sinc (2 * Real.pi * x)| ≤ |x|⁻¹ := hsinc_abs.trans hinv_scale
      have hsq := mul_self_le_mul_self (abs_nonneg _) hsinc_abs'
      simpa [pow_two] using hsq
    have hxsq : 1 ≤ x ^ 2 := by
      have hsq : 1 * 1 < |x| * |x| := by
        nlinarith
      have : 1 < |x| ^ 2 := by simpa [pow_two] using hsq
      simpa [sq_abs] using le_of_lt this
    have hden : 1 + x ^ 2 ≤ 4 * x ^ 2 := by
      nlinarith
    have hinv_den : (4 * x ^ 2)⁻¹ ≤ (1 + x ^ 2)⁻¹ := by
      exact inv_anti₀ (by positivity : 0 < 1 + x ^ 2) hden
    have hrewriteAbs : |x|⁻¹ ^ 2 = (x ^ 2)⁻¹ := by
      have habsne : |x| ≠ 0 := abs_ne_zero.mpr hxne
      field_simp [habsne, hxne]
      rw [sq_abs]
    have hrewrite : 4 * |x|⁻¹ ^ 2 = 16 * (4 * x ^ 2)⁻¹ := by
      rw [hrewriteAbs]
      field_simp [hxne]
      ring
    calc
      4 * |Real.sinc (2 * Real.pi * x)| ^ 2 ≤ 4 * |x|⁻¹ ^ 2 := by
        gcongr
      _ = 16 * (4 * x ^ 2)⁻¹ := hrewrite
      _ ≤ 16 * (1 + x ^ 2)⁻¹ := by
        gcongr

/-- Helper for Exercise 5.3: the source term is integrable. -/
lemma inverseUnitBoxPowerSpectrum_integrable :
    MeasureTheory.Integrable inverseUnitBoxPowerSpectrum := by
  -- Use the explicit `sinc²` formula and dominate it by `(1 + x²)⁻¹`.
  have hmajor : MeasureTheory.Integrable (fun x : ℝ ↦ (16 : ℝ) * (1 + x ^ 2)⁻¹) := by
    simpa using integrable_inv_one_add_sq.const_mul (16 : ℝ)
  have hmeas :
      MeasureTheory.AEStronglyMeasurable
        (fun x : ℝ ↦ ((((4 * Real.sinc (2 * Real.pi * x) ^ 2) : ℝ) : ℂ))) := by
    have hcont :
        Continuous (fun x : ℝ ↦ ((((4 * Real.sinc (2 * Real.pi * x) ^ 2) : ℝ) : ℂ))) := by
      refine Complex.continuous_ofReal.comp ?_
      fun_prop
    exact hcont.aestronglyMeasurable
  have hsincInt :
      MeasureTheory.Integrable
        (fun x : ℝ ↦ ((((4 * Real.sinc (2 * Real.pi * x) ^ 2) : ℝ) : ℂ))) := by
    refine MeasureTheory.Integrable.mono' hmajor hmeas ?_
    exact Filter.Eventually.of_forall inverseUnitBoxPowerSpectrum_bound
  have hEq :
      (fun x : ℝ ↦ ((((4 * Real.sinc (2 * Real.pi * x) ^ 2) : ℝ) : ℂ))) =
        inverseUnitBoxPowerSpectrum := by
    funext x
    symm
    exact inverseUnitBoxPowerSpectrum_eq_fourSincSq x
  rw [← hEq]
  exact hsincInt

/-- Exercise 5.3. For the interval indicator `A = unitBoxIndicator`, the Fourier
transform of `inverseUnitBoxPowerSpectrum`, i.e. of `|𝓕⁻ A|^2` for
`A = unitBoxIndicator`, is the triangular ramp `triangleRamp`. -/
theorem fourierNormSqInverseUnitBox_eq_triangleRamp :
    𝓕 inverseUnitBoxPowerSpectrum = triangleRamp := by
  -- Route correction: identify the source as `𝓕 triangleRamp`, then use the evenness of
  -- `triangleRamp` to replace `𝓕` by `𝓕⁻` before applying Fourier inversion.
  have hFourierEq : 𝓕 triangleRamp = 𝓕⁻ triangleRamp := by
    rw [Real.fourierInv_eq_fourier_comp_neg]
    congr 1
    ext x
    simpa using (triangleRamp_even x).symm
  have hSource : MeasureTheory.Integrable (𝓕 triangleRamp) := by
    simpa [inverseUnitBoxPowerSpectrum_eq_fourier_triangleRamp] using
      inverseUnitBoxPowerSpectrum_integrable
  calc
    𝓕 inverseUnitBoxPowerSpectrum = 𝓕 (𝓕 triangleRamp) := by
      rw [inverseUnitBoxPowerSpectrum_eq_fourier_triangleRamp]
    _ = 𝓕 (𝓕⁻ triangleRamp) := by
      rw [hFourierEq]
    _ = triangleRamp := by
      simpa using
        Continuous.fourier_fourierInv_eq triangleRamp_continuous triangleRamp_integrable hSource
