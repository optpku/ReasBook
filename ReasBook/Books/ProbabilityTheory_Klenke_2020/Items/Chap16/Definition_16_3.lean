/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib
import Books.ProbabilityTheory_Klenke_2020.Items.Chap02.Definition_2_32
import Books.ProbabilityTheory_Klenke_2020.Items.Chap16.Definition_16_1

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory ProbabilityTheory
open scoped ENNReal

noncomputable section

/-- The `n`-fold additive convolution power of a measure on `ℝ`, normalized so that the zeroth
power is the Dirac mass at `0`. -/
noncomputable def compoundPoissonConvolutionPower (ν : Measure ℝ) : ℕ → Measure ℝ
  | 0 => Measure.dirac 0
  | n + 1 => compoundPoissonConvolutionPower ν n ∗ ν

/-- The successor convolution powers are obtained by convolving once more with the base measure
`ν`. -/
theorem compoundPoissonConvolutionPower_succ (ν : Measure ℝ) (n : ℕ) :
    compoundPoissonConvolutionPower ν (n + 1) =
      compoundPoissonConvolutionPower ν n ∗ ν := rfl

/-- Helper for Definition 16.3: every convolution power of a finite measure is again finite. -/
private theorem compoundPoissonConvolutionPower_isFiniteMeasure
    (ν : Measure ℝ) [IsFiniteMeasure ν] :
    ∀ n : ℕ, IsFiniteMeasure (compoundPoissonConvolutionPower ν n)
  | 0 => by
      simpa [compoundPoissonConvolutionPower] using
        (inferInstance : IsFiniteMeasure (Measure.dirac (0 : ℝ)))
  | n + 1 => by
      rw [compoundPoissonConvolutionPower_succ]
      letI : IsFiniteMeasure (compoundPoissonConvolutionPower ν n) :=
        compoundPoissonConvolutionPower_isFiniteMeasure ν n
      infer_instance

private noncomputable def compoundPoissonMeasureData (ν : Measure ℝ) [IsFiniteMeasure ν] :
    Measure ℝ :=
  Measure.sum fun n ↦
    ENNReal.ofReal (Real.exp (-ν.real Set.univ) / n.factorial) •
      compoundPoissonConvolutionPower ν n

/-- Helper for Definition 16.3: the characteristic function of the `n`-fold convolution power is
the `n`th power of the characteristic function of the base measure. -/
private theorem charFun_compoundPoissonConvolutionPower
    (ν : Measure ℝ) [IsFiniteMeasure ν] (n : ℕ) (t : ℝ) :
    charFun (compoundPoissonConvolutionPower ν n) t = charFun ν t ^ n := by
  induction n with
  | zero =>
      -- Proof comment: the zeroth convolution power is `δ₀`, whose characteristic function is `1`.
      simp [compoundPoissonConvolutionPower, MeasureTheory.charFun_dirac]
  | succ n ih =>
      -- Proof comment: the successor convolution power adds one more convolution factor, so the
      -- characteristic function picks up one more multiplicative factor `charFun ν t`.
      letI : IsFiniteMeasure (compoundPoissonConvolutionPower ν n) :=
        compoundPoissonConvolutionPower_isFiniteMeasure ν n
      rw [compoundPoissonConvolutionPower_succ, MeasureTheory.charFun_conv, ih, pow_succ]

/-- Helper for Definition 16.3: the total mass of the `n`th convolution power is `ν(ℝ)^n`. -/
private theorem compoundPoissonConvolutionPower_real_univ
    (ν : Measure ℝ) [IsFiniteMeasure ν] (n : ℕ) :
    (compoundPoissonConvolutionPower ν n).real Set.univ = ν.real Set.univ ^ n := by
  -- Proof comment: evaluate the characteristic-function identity at `t = 0`, where `charFun`
  -- records the total mass of a finite measure.
  apply Complex.ofReal_injective
  simpa using charFun_compoundPoissonConvolutionPower ν n 0

/-- Helper for Definition 16.3: the total mass of the `n`th convolution power, viewed as an
`ℝ≥0∞` value, is `ENNReal.ofReal (ν(ℝ)^n)`. -/
private theorem compoundPoissonConvolutionPower_univ
    (ν : Measure ℝ) [IsFiniteMeasure ν] (n : ℕ) :
    compoundPoissonConvolutionPower ν n Set.univ =
      ENNReal.ofReal (ν.real Set.univ ^ n) := by
  letI : IsFiniteMeasure (compoundPoissonConvolutionPower ν n) :=
    compoundPoissonConvolutionPower_isFiniteMeasure ν n
  rw [← MeasureTheory.ofReal_measureReal (μ := compoundPoissonConvolutionPower ν n) (s := Set.univ),
    compoundPoissonConvolutionPower_real_univ]

-- Proof sketch: compute the total mass of each term using the convolution-power recursion, then
-- identify the resulting scalar series with the exponential series of total mass `ν(ℝ)`.
private theorem compoundPoissonMeasureData_isProbabilityMeasure
    (ν : Measure ℝ) [IsFiniteMeasure ν] :
    IsProbabilityMeasure (compoundPoissonMeasureData ν) := by
  let r : NNReal := Real.toNNReal (ν.real Set.univ)
  have hν_nonneg : 0 ≤ ν.real Set.univ := by positivity
  have hr : ((r : NNReal) : ℝ) = ν.real Set.univ := by
    -- Proof comment: normalize the Poisson rate once so later coefficient rewrites stay in one
    -- scalar spelling world.
    simp [r, hν_nonneg]
  -- Proof comment: the mass of the raw series is the Poisson pmf sum with rate `ν(ℝ)`.
  rw [MeasureTheory.isProbabilityMeasure_iff]
  rw [compoundPoissonMeasureData, Measure.sum_apply _ MeasurableSet.univ]
  have hterm :
      (fun n ↦
        (ENNReal.ofReal (Real.exp (-ν.real Set.univ) / n.factorial) •
            compoundPoissonConvolutionPower ν n) Set.univ) =
        fun n ↦ ENNReal.ofReal (ProbabilityTheory.poissonPMFReal r n) := by
    funext n
    rw [Measure.smul_apply, smul_eq_mul, compoundPoissonConvolutionPower_univ]
    rw [ProbabilityTheory.poissonPMFReal]
    rw [← ENNReal.ofReal_mul]
    · congr 1
      simp [hr]
      rw [div_eq_mul_inv, div_eq_mul_inv]
      ring
    · positivity
  rw [hterm]
  calc
    ∑' n, ENNReal.ofReal (ProbabilityTheory.poissonPMFReal r n)
        = ENNReal.ofReal (∑' n, ProbabilityTheory.poissonPMFReal r n) := by
            symm
            exact ENNReal.ofReal_tsum_of_nonneg
              (fun n ↦ ProbabilityTheory.poissonPMFReal_nonneg)
              (ProbabilityTheory.poissonPMFRealSum r).summable
    _ = ENNReal.ofReal 1 := by rw [(ProbabilityTheory.poissonPMFRealSum r).tsum_eq]
    _ = 1 := by simp

/-- Definition 16.3: The compound Poisson distribution with finite intensity measure `ν` is the
probability law on `ℝ` given by the Poisson-weighted series
`e^{-ν(ℝ)} \sum_{n=0}^\infty ν^{*n} / n!`. -/
noncomputable def compoundPoissonMeasure (ν : Measure ℝ) [IsFiniteMeasure ν] :
    ProbabilityMeasure ℝ :=
  ⟨compoundPoissonMeasureData ν, compoundPoissonMeasureData_isProbabilityMeasure ν⟩

/-- The compound Poisson measure is the Poisson-weighted sum of the convolution powers of its
intensity measure. -/
theorem compoundPoissonMeasure_def (ν : Measure ℝ) [IsFiniteMeasure ν] :
    (compoundPoissonMeasure ν : Measure ℝ) =
      Measure.sum fun n ↦
        ENNReal.ofReal (Real.exp (-ν.real Set.univ) / n.factorial) •
          compoundPoissonConvolutionPower ν n := rfl

/-- Helper for Definition 16.3: scaling the intensity measure by `c` scales the `n`th convolution
power by `c ^ n`. -/
private theorem compoundPoissonConvolutionPower_smul
    (ν : Measure ℝ) [IsFiniteMeasure ν] (c : ℝ≥0∞) :
    ∀ n : ℕ,
      compoundPoissonConvolutionPower (c • ν) n =
        c ^ n • compoundPoissonConvolutionPower ν n := by
  intro n
  induction n with
  | zero =>
      -- Proof comment: the zeroth convolution power is independent of the intensity measure.
      simp [compoundPoissonConvolutionPower]
  | succ n ih =>
      -- Route correction: rewrite the convolution-scaling step at the measure level before
      -- taking setwise values; direct `rw` on the applied measure was too brittle.
      -- Proof comment: convolution is bilinear with respect to measure scaling, so the recursive
      -- convolution power picks up one extra factor of `c`.
      rw [compoundPoissonConvolutionPower_succ, compoundPoissonConvolutionPower_succ, ih, pow_succ]
      rw [Measure.conv_smul_right, Measure.conv_smul_left]
      simp [smul_smul, mul_comm]

/-- Helper for Definition 16.3: a nonnegative real rate, viewed in `ℝ≥0∞`, has the same `n`th
power as `ENNReal.ofReal (r ^ n)`. -/
private theorem ennrealPow_toNNReal_eq_ofReal_pow (r : ℝ) (hr : 0 ≤ r) (n : ℕ) :
    (((Real.toNNReal r : NNReal) : ℝ≥0∞) ^ n) = ENNReal.ofReal (r ^ n) := by
  -- Proof comment: `ENNReal.ofReal_pow` is the canonical bridge from real powers to the
  -- nonnegative scalar world.
  have hcoe : (((Real.toNNReal r : NNReal) : ℝ≥0∞)) = ENNReal.ofReal r := by
    simpa [Real.toNNReal_of_nonneg hr] using (ENNReal.ofReal_eq_coe_nnreal hr).symm
  rw [hcoe]
  simpa using (ENNReal.ofReal_pow hr n).symm

-- Proof sketch: expand `compoundPoissonMeasure ((Real.toNNReal r) • ν)` with
-- `compoundPoissonMeasure_def`, use the bilinearity of convolution to rewrite the `n`th
-- convolution power of the scaled intensity measure as `r ^ n` times the `n`th convolution power
-- of `ν`, and simplify the total mass of the scaled measure to `r * ν(ℝ)`.
/-- The textbook parameterization by a rate `r` and a jump measure `ν` is the owner
compound-Poisson law for the finite intensity measure `r • ν`. -/
theorem compoundPoissonMeasure_smul_eq (r : ℝ) (hr : 0 ≤ r) (ν : Measure ℝ)
    [IsFiniteMeasure ν] :
    (compoundPoissonMeasure ((Real.toNNReal r) • ν) : Measure ℝ) =
      Measure.sum fun n ↦
        ENNReal.ofReal (Real.exp (-r * ν.real Set.univ) * r ^ n / n.factorial) •
          compoundPoissonConvolutionPower ν n := by
  -- Proof comment: compare both measures on a measurable set, rewrite the scaled convolution
  -- powers setwise, and then collapse the remaining scalar coefficient in `ENNReal`.
  ext s hs
  rw [compoundPoissonMeasure_def, Measure.sum_apply _ hs, Measure.sum_apply _ hs]
  refine tsum_congr fun n ↦ ?_
  rw [Measure.smul_apply, smul_eq_mul]
  let c : ℝ≥0∞ := ((Real.toNNReal r : NNReal) : ℝ≥0∞)
  have hpowApply :
      (compoundPoissonConvolutionPower (((Real.toNNReal r : NNReal) : ℝ≥0∞) • ν) n) s =
        (c ^ n • compoundPoissonConvolutionPower ν n) s := by
    -- Proof comment: rewrite the scaled convolution power before expanding the outer scalar.
    simpa [c] using congrArg (fun μ : Measure ℝ ↦ μ s)
      (compoundPoissonConvolutionPower_smul (ν := ν) (c := c) n)
  have hpowApply' :
      (compoundPoissonConvolutionPower (r.toNNReal • ν) n) s =
        (c ^ n • compoundPoissonConvolutionPower ν n) s := by
    simpa [c] using hpowApply
  rw [hpowApply', Measure.smul_apply, smul_eq_mul]
  have hrate : c ^ n = ENNReal.ofReal (r ^ n) := by
    simpa [c] using ennrealPow_toNNReal_eq_ofReal_pow r hr n
  have hmass : (c • ν).real Set.univ = r * ν.real Set.univ := by
    simp [c, Real.toNNReal_of_nonneg hr]
  have hmass' : (r.toNNReal • ν).real Set.univ = r * ν.real Set.univ := by
    simpa [c] using hmass
  have hcoeff_nonneg : 0 ≤ Real.exp (-(r * ν.real Set.univ)) / n.factorial := by
    positivity
  rw [hmass', hrate, ← mul_assoc, ← ENNReal.ofReal_mul hcoeff_nonneg]
  congr 1
  rw [div_eq_mul_inv, div_eq_mul_inv]
  ring

/-- Helper for Definition 16.3: the Fourier kernel `x ↦ exp (t * x * I)` is integrable against
every finite measure on `ℝ`. -/
private theorem integrable_complexExpKernel (μ : Measure ℝ) [IsFiniteMeasure μ] (t : ℝ) :
    Integrable (fun x : ℝ ↦ Complex.exp (t * x * Complex.I)) (μ := μ) := by
  -- Proof comment: the Fourier kernel has constant norm `1`, so a finite measure integrates it.
  refine Integrable.of_bound (by fun_prop) 1 ?_
  exact Filter.Eventually.of_forall fun x ↦ by
    exact le_of_eq (by simpa using (Complex.norm_exp_ofReal_mul_I (t * x)))

/-- Helper for Definition 16.3: the characteristic function of the raw Poisson series is the
Poisson-weighted exponential series in `charFun ν t`. -/
private theorem charFun_compoundPoissonMeasureData_eq_series
    (ν : Measure ℝ) [IsFiniteMeasure ν] (t : ℝ) :
    charFun (compoundPoissonMeasureData ν) t =
      Complex.exp (-ν.real Set.univ) * ∑' n, charFun ν t ^ n / n.factorial := by
  have hprob : IsProbabilityMeasure (compoundPoissonMeasureData ν) :=
    compoundPoissonMeasureData_isProbabilityMeasure ν
  letI : IsProbabilityMeasure (compoundPoissonMeasureData ν) := hprob
  -- Proof comment: move the characteristic-function integral through the countable measure sum and
  -- rewrite each summand via the convolution-power characteristic function.
  rw [MeasureTheory.charFun_apply_real, compoundPoissonMeasureData]
  rw [integral_sum_measure (integrable_complexExpKernel (μ := compoundPoissonMeasureData ν) t)]
  trans ∑' n, Complex.exp (-ν.real Set.univ) * (charFun ν t ^ n / n.factorial)
  · refine tsum_congr fun n ↦ ?_
    rw [integral_smul_measure, ← MeasureTheory.charFun_apply_real,
      charFun_compoundPoissonConvolutionPower]
    have hcoeff_nonneg : 0 ≤ Real.exp (-ν.real Set.univ) / n.factorial := by
      positivity
    have hcoeffReal :
        (ENNReal.ofReal (Real.exp (-ν.real Set.univ) / n.factorial)).toReal =
          Real.exp (-ν.real Set.univ) / n.factorial := by
      exact ENNReal.toReal_ofReal hcoeff_nonneg
    have hcoeffComplex :
        (((Real.exp (-ν.real Set.univ) / n.factorial : ℝ) : ℂ)) =
          Complex.exp (-ν.real Set.univ) / n.factorial := by
      rw [Complex.ofReal_div, Complex.ofReal_exp]
      norm_num
    calc
      (((ENNReal.ofReal (Real.exp (-ν.real Set.univ) / n.factorial)).toReal : ℂ) *
          charFun ν t ^ n)
          = ((((Real.exp (-ν.real Set.univ) / n.factorial : ℝ) : ℂ)) * charFun ν t ^ n) := by
              rw [hcoeffReal]
      _ = (Complex.exp (-ν.real Set.univ) / n.factorial) * charFun ν t ^ n := by
            rw [hcoeffComplex]
      _ = Complex.exp (-ν.real Set.univ) * (charFun ν t ^ n / n.factorial) := by
            rw [div_eq_mul_inv, div_eq_mul_inv]
            ring
  · rw [tsum_mul_left]

-- Proof sketch: expand `compoundPoissonMeasure` as a weighted series, use linearity of the
-- characteristic function on countable measure sums and multiplicativity under convolution, and
-- sum the resulting exponential series.
/-- The characteristic function of the compound Poisson measure is
`exp (∫ (exp (i t x) - 1) dν)`. -/
theorem charFun_compoundPoissonMeasure (ν : Measure ℝ) [IsFiniteMeasure ν] (t : ℝ) :
    charFun (compoundPoissonMeasure ν : Measure ℝ) t =
      Complex.exp (∫ x, (Complex.exp (t * x * Complex.I) - 1) ∂ν) := by
  have hseriesFormula :
      charFun (compoundPoissonMeasure ν : Measure ℝ) t =
        Complex.exp (-ν.real Set.univ) * ∑' n, charFun ν t ^ n / n.factorial := by
    simpa [compoundPoissonMeasure_def] using charFun_compoundPoissonMeasureData_eq_series ν t
  rw [hseriesFormula]
  have hseries : HasSum (fun n ↦ charFun ν t ^ n / n.factorial) (Complex.exp (charFun ν t)) := by
    simpa [Complex.exp_eq_exp_ℂ] using
      (NormedSpace.expSeries_div_hasSum_exp (charFun ν t))
  rw [hseries.tsum_eq, ← Complex.exp_add]
  have hsub :
      ∫ x, (Complex.exp (t * x * Complex.I) - 1) ∂ν =
        ∫ x, Complex.exp (t * x * Complex.I) ∂ν - ∫ x, (1 : ℂ) ∂ν :=
    integral_sub (integrable_complexExpKernel (μ := ν) t) (integrable_const (1 : ℂ))
  have hcentered :
      (-ν.real Set.univ : ℂ) + charFun ν t =
        ∫ x, (Complex.exp (t * x * Complex.I) - 1) ∂ν := by
    have hrealOne : (ν.real Set.univ : ℂ) = ν.real Set.univ • (1 : ℂ) := by
      simp
    calc
      (-ν.real Set.univ : ℂ) + charFun ν t
          = charFun ν t - (ν.real Set.univ : ℂ) := by
              simp [sub_eq_add_neg, add_comm]
      _ = charFun ν t - ∫ x, (1 : ℂ) ∂ν := by
            rw [integral_const, hrealOne]
            rfl
      _ = ∫ x, Complex.exp (t * x * Complex.I) ∂ν - ∫ x, (1 : ℂ) ∂ν := by
            rw [MeasureTheory.charFun_apply_real]
      _ = ∫ x, (Complex.exp (t * x * Complex.I) - 1) ∂ν := by
            rw [← hsub]
  rw [hcentered]

-- Proof sketch: compare the characteristic functions of both sides using
-- `charFun_compoundPoissonMeasure`, reduce the exponent for `μ + ν` to the sum of the separate
-- exponents, use uniqueness of characteristic functions for finite measures on `ℝ`, and then
-- pass back to bundled probability measures via extensionality of the underlying measures.
/-- Compound Poisson measures form an additive convolution semigroup in the intensity measure. -/
theorem compoundPoissonMeasure_add (μ ν : Measure ℝ) [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    compoundPoissonMeasure (μ + ν) = compoundPoissonMeasure μ * compoundPoissonMeasure ν := by
  letI :
      IsFiniteMeasure (((compoundPoissonMeasure (μ + ν) : ProbabilityMeasure ℝ) :
        Measure ℝ)) := by infer_instance
  letI :
      IsFiniteMeasure (((compoundPoissonMeasure μ * compoundPoissonMeasure ν :
        ProbabilityMeasure ℝ) : Measure ℝ)) := by infer_instance
  apply ProbabilityMeasure.toMeasure_injective
  apply Measure.ext_of_charFun
  funext t
  have hμint : Integrable (fun x : ℝ ↦ Complex.exp (t * x * Complex.I) - 1) (μ := μ) :=
    (integrable_complexExpKernel (μ := μ) t).sub (integrable_const (1 : ℂ))
  have hνint : Integrable (fun x : ℝ ↦ Complex.exp (t * x * Complex.I) - 1) (μ := ν) :=
    (integrable_complexExpKernel (μ := ν) t).sub (integrable_const (1 : ℂ))
  -- Proof comment: the Lévy exponents add under `μ + ν`, and convolution multiplies
  -- characteristic functions.
  rw [MeasureTheory.ProbabilityMeasure.toMeasure_mul, MeasureTheory.charFun_conv,
    charFun_compoundPoissonMeasure, charFun_compoundPoissonMeasure,
    charFun_compoundPoissonMeasure]
  rw [integral_add_measure hμint hνint, Complex.exp_add]

/-- Helper for Definition 16.3: the `(n + 1)`st convolution power of `CPoi_{c • ν}` has intensity
`((n + 1 : ℝ≥0) * c) • ν`. -/
private theorem compoundPoissonMeasure_pow_succ
    (ν : Measure ℝ) [IsFiniteMeasure ν] (c : NNReal) :
    ∀ n : ℕ,
      (compoundPoissonMeasure (c • ν)) ^ (n + 1) =
        compoundPoissonMeasure ((((n + 1 : ℕ) : NNReal) * c) • ν) := by
  intro n
  induction n with
  | zero =>
      -- Proof comment: the first convolution power is the measure itself, with intensity `1 * c`.
      simp
  | succ n ih =>
      -- Proof comment: apply the additive semigroup law once more and normalize the resulting
      -- intensity measure on each measurable set.
      rw [pow_succ, ih, ← compoundPoissonMeasure_add]
      congr 1
      ext s hs
      simp [Measure.add_apply, Measure.smul_apply]
      ring_nf

-- Proof sketch: for each `n`, apply `compoundPoissonMeasure_add` repeatedly to split the
-- intensity measure into `n + 1` equal parts, yielding an `(n + 1)`-fold convolution root.
/-- Every compound Poisson measure is infinitely divisible. -/
theorem compoundPoissonMeasure_infinitelyDivisible (ν : Measure ℝ) [IsFiniteMeasure ν] :
    ProbabilityMeasure.IsInfinitelyDivisible (compoundPoissonMeasure ν) := by
  refine ⟨fun n ↦ ?_⟩
  refine ⟨compoundPoissonMeasure ((((n : ℕ) : NNReal)⁻¹) • ν), ?_⟩
  have hpow := compoundPoissonMeasure_pow_succ ν ((((n : ℕ) : NNReal)⁻¹)) n.natPred
  rw [n.natPred_add_one] at hpow
  have hn0 : (((n : ℕ) : NNReal)) ≠ 0 := by
    exact_mod_cast n.ne_zero
  have hcancel : (((n : ℕ) : NNReal) * (((n : ℕ) : NNReal)⁻¹)) = 1 :=
    mul_inv_cancel₀ hn0
  rw [hcancel] at hpow
  letI : IsFiniteMeasure ((((1 : NNReal) : ℝ≥0∞) • ν)) := by
    simpa [one_smul] using (inferInstance : IsFiniteMeasure ν)
  have hone : compoundPoissonMeasure (((1 : NNReal) : ℝ≥0∞) • ν) = compoundPoissonMeasure ν := by
    simp [one_smul]
  exact hpow.trans hone
