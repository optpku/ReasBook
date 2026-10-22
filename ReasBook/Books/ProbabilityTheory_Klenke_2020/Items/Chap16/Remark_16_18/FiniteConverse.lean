/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib
import Books.ProbabilityTheory_Klenke_2020.Items.Chap16.Definition_16_3
import Books.ProbabilityTheory_Klenke_2020.Items.Chap16.Lemma_16_24

open MeasureTheory ProbabilityTheory

noncomputable section

namespace MeasureTheory.ProbabilityMeasure

/-- Helper for Remark 16.18: the canonical centering cutoff is uniformly bounded by `1`. -/
private lemma norm_levyKhinchinCanonicalCentering_le_one (x : ℝ) :
    ‖levyKhinchinCanonicalCentering x‖ ≤ 1 := by
  by_cases hx : |x| < 1
  · -- Proof comment: on the unit ball the cutoff equals `x`.
    simpa [levyKhinchinCanonicalCentering, hx, Real.norm_eq_abs] using le_of_lt hx
  · -- Proof comment: outside the unit ball the cutoff vanishes.
    simp [levyKhinchinCanonicalCentering, hx]

/-- Helper for Remark 16.18: a finite measure with no atom at `0` already satisfies the canonical
Lévy-measure condition. -/
private lemma isCanonicalMeasure_of_isFiniteMeasure_of_measure_singleton_zero
    (ν : Measure ℝ) [IsFiniteMeasure ν] (hν0 : ν ({0} : Set ℝ) = 0) :
    IsCanonicalMeasure ν := by
  refine ⟨hν0, ?_⟩
  -- Proof comment: the canonical integrand is bounded by `1`, so finiteness of `ν` gives
  -- integrability.
  refine (integrable_const (1 : ℝ)).mono' (by fun_prop) ?_
  exact Filter.Eventually.of_forall fun x ↦ by
    have h_nonneg : 0 ≤ min (x ^ (2 : ℕ)) 1 := by positivity
    have h_le : min (x ^ (2 : ℕ)) 1 ≤ 1 := min_le_right _ _
    simpa [Real.norm_eq_abs, abs_of_nonneg h_nonneg] using h_le

/-- Helper for Remark 16.18: the complex cutoff correction is integrable against every finite
measure because the canonical centering is uniformly bounded by `1`. -/
private lemma integrable_complexCenteringCorrection_of_isFiniteMeasure
    (ν : Measure ℝ) [IsFiniteMeasure ν] (t : ℝ) :
    Integrable
      (fun x : ℝ ↦ (((t * levyKhinchinCanonicalCentering x : ℝ) : ℂ) * Complex.I)) ν := by
  -- Proof comment: the complex correction has norm at most `|t|`, so finiteness of `ν` gives
  -- integrability immediately.
  refine (integrable_const ‖t‖).mono'
    (((Complex.measurable_ofReal.comp
      (measurable_const.mul measurable_levyKhinchinCanonicalCentering)).mul_const
        Complex.I).aestronglyMeasurable) ?_
  exact Filter.Eventually.of_forall (fun x ↦ by
    calc
      ‖(((t * levyKhinchinCanonicalCentering x : ℝ) : ℂ) * Complex.I)‖
          = ‖t * levyKhinchinCanonicalCentering x‖ := by simp
      _ = ‖t‖ * ‖levyKhinchinCanonicalCentering x‖ := by simp [norm_mul]
      _ ≤ ‖t‖ * 1 := by
            exact mul_le_mul_of_nonneg_left
              (norm_levyKhinchinCanonicalCentering_le_one x) (norm_nonneg t)
      _ = ‖t‖ := by ring)

/-- Helper for Remark 16.18: the compound-Poisson kernel `x ↦ exp(i t x) - 1` is integrable
against every finite measure. -/
private lemma integrable_compoundPoissonKernel_of_isFiniteMeasure
    (ν : Measure ℝ) [IsFiniteMeasure ν] (t : ℝ) :
    Integrable (fun x : ℝ ↦ Complex.exp (((t * x : ℝ) : ℂ) * Complex.I) - 1) ν := by
  -- Proof comment: the oscillatory exponential has norm `1`, so subtracting `1` leaves a
  -- uniform bound by `2`.
  refine (integrable_const (2 : ℝ)).mono' (by fun_prop) ?_
  exact Filter.Eventually.of_forall (fun x ↦ by
    calc
      ‖Complex.exp (((t * x : ℝ) : ℂ) * Complex.I) - 1‖
          ≤ ‖Complex.exp (((t * x : ℝ) : ℂ) * Complex.I)‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
      _ = 1 + 1 := by
            rw [Complex.norm_exp_ofReal_mul_I]
            simp
      _ = 2 := by norm_num)

/-- Helper for Remark 16.18: the Gaussian law `N(m, σ²)` is represented by the canonical triple
`(σ², m, 0)`. -/
private lemma gaussian_hasLevyKhinchinRepresentation (m : ℝ) (σ2 : NNReal) :
    HasLevyKhinchinRepresentation
      (⟨gaussianReal m σ2, inferInstance⟩ : ProbabilityMeasure ℝ)
      { sigma2 := (σ2 : ℝ), b := m, ν := (0 : Measure ℝ) } := by
  constructor
  · -- Proof comment: the Gaussian coefficient is nonnegative and the zero jump measure is
    -- canonical.
    refine ⟨by exact_mod_cast σ2.2, inferInstance⟩
  · intro t
    -- Proof comment: with zero jump measure, the Lévy--Khinchin exponent is exactly the Gaussian
    -- characteristic exponent.
    calc
      charFun (⟨gaussianReal m σ2, inferInstance⟩ : ProbabilityMeasure ℝ) t
          = Complex.exp (t * m * Complex.I - ((σ2 : ℝ) * t ^ (2 : ℕ) / 2 : ℝ)) := by
              simpa [mul_assoc, mul_left_comm, mul_comm, div_eq_mul_inv] using
                (ProbabilityTheory.charFun_gaussianReal (μ := m) (v := σ2) t)
      _ =
          Complex.exp
            (levyKhinchinExponent { sigma2 := (σ2 : ℝ), b := m, ν := (0 : Measure ℝ) } t) := by
              congr 1
              simp [levyKhinchinExponent, levyKhinchinExponentWithCentering, sub_eq_add_neg,
                mul_assoc, mul_left_comm, mul_comm, div_eq_mul_inv]
              ring

/-- Helper for Remark 16.18: the integrated complex cutoff correction equals the linear drift
term `i t ∫ x 𝟙_{|x|<1} ν(dx)`. -/
private lemma integral_complexCenteringCorrection_eq
    (ν : Measure ℝ) [IsFiniteMeasure ν] (t : ℝ) :
    ∫ x : ℝ, (((t * levyKhinchinCanonicalCentering x : ℝ) : ℂ) * Complex.I) ∂ν =
      ((((t * ∫ x : ℝ, levyKhinchinCanonicalCentering x ∂ν : ℝ) : ℂ)) * Complex.I) := by
  -- Proof comment: move the constant `Complex.I` through the integral, then rewrite the
  -- remaining complex integral as the image of the real one.
  calc
    ∫ x : ℝ, (((t * levyKhinchinCanonicalCentering x : ℝ) : ℂ) * Complex.I) ∂ν
        = (∫ x : ℝ, ((t * levyKhinchinCanonicalCentering x : ℝ) : ℂ) ∂ν) * Complex.I := by
            simpa using
              (integral_mul_const (μ := ν) Complex.I
                (fun x : ℝ ↦ ((t * levyKhinchinCanonicalCentering x : ℝ) : ℂ)))
    _ = ((((∫ x : ℝ, t * levyKhinchinCanonicalCentering x ∂ν : ℝ)) : ℂ)) * Complex.I := by
          rw [integral_complex_ofReal]
    _ = ((((t * ∫ x : ℝ, levyKhinchinCanonicalCentering x ∂ν : ℝ)) : ℂ)) * Complex.I := by
          rw [integral_const_mul]

/-- Helper for Remark 16.18: a finite jump intensity with no atom at `0` already gives the
canonical compound-Poisson representation. -/
private lemma compoundPoisson_hasLevyKhinchinRepresentation
    (ν : Measure ℝ) [IsFiniteMeasure ν] (hν0 : ν ({0} : Set ℝ) = 0) :
    HasLevyKhinchinRepresentation
      (compoundPoissonMeasure ν)
      { sigma2 := 0
        b := ∫ x : ℝ, levyKhinchinCanonicalCentering x ∂ν
        ν := ν } := by
  constructor
  · -- Proof comment: finite jump intensities with no atom at `0` are canonical, and the
    -- Gaussian coefficient vanishes.
    refine ⟨by simp, isCanonicalMeasure_of_isFiniteMeasure_of_measure_singleton_zero ν hν0⟩
  · intro t
    have hkernel :
        Integrable (fun x : ℝ ↦ Complex.exp (((t * x : ℝ) : ℂ) * Complex.I) - 1) ν :=
      integrable_compoundPoissonKernel_of_isFiniteMeasure ν t
    have hcorr :
        Integrable
          (fun x : ℝ ↦ (((t * levyKhinchinCanonicalCentering x : ℝ) : ℂ) * Complex.I)) ν :=
      integrable_complexCenteringCorrection_of_isFiniteMeasure ν t
    have hsplit :
        ∫ x : ℝ,
            (Complex.exp (((t * x : ℝ) : ℂ) * Complex.I) - 1 -
              (((t * levyKhinchinCanonicalCentering x : ℝ) : ℂ) * Complex.I)) ∂ν =
          ∫ x : ℝ, (Complex.exp (((t * x : ℝ) : ℂ) * Complex.I) - 1) ∂ν -
            ∫ x : ℝ, (((t * levyKhinchinCanonicalCentering x : ℝ) : ℂ) * Complex.I) ∂ν := by
      -- Proof comment: split the centered jump kernel into the raw compound-Poisson kernel minus
      -- the centering correction.
      rw [integral_sub hkernel hcorr]
    have hexponent :
        levyKhinchinExponent
            { sigma2 := 0
              b := ∫ x : ℝ, levyKhinchinCanonicalCentering x ∂ν
              ν := ν } t =
          ∫ x : ℝ, (Complex.exp (((t * x : ℝ) : ℂ) * Complex.I) - 1) ∂ν := by
      -- Proof comment: the explicit drift term cancels the integrated centering correction.
      calc
        levyKhinchinExponent
            { sigma2 := 0
              b := ∫ x : ℝ, levyKhinchinCanonicalCentering x ∂ν
              ν := ν } t
            =
          ((((t * ∫ x : ℝ, levyKhinchinCanonicalCentering x ∂ν : ℝ) : ℂ)) * Complex.I) +
            ∫ x : ℝ,
              (Complex.exp (((t * x : ℝ) : ℂ) * Complex.I) - 1 -
                (((t * levyKhinchinCanonicalCentering x : ℝ) : ℂ) * Complex.I)) ∂ν := by
              simp [levyKhinchinExponent, levyKhinchinExponentWithCentering,
                mul_assoc, mul_left_comm, mul_comm]
        _ = ((((t * ∫ x : ℝ, levyKhinchinCanonicalCentering x ∂ν : ℝ) : ℂ)) * Complex.I) +
              (∫ x : ℝ, (Complex.exp (((t * x : ℝ) : ℂ) * Complex.I) - 1) ∂ν -
                ∫ x : ℝ, (((t * levyKhinchinCanonicalCentering x : ℝ) : ℂ) * Complex.I) ∂ν) := by
              rw [hsplit]
        _ = ∫ x : ℝ, (Complex.exp (((t * x : ℝ) : ℂ) * Complex.I) - 1) ∂ν := by
              rw [integral_complexCenteringCorrection_eq]
              simpa using
                (mul_comm (((∫ x : ℝ, levyKhinchinCanonicalCentering x ∂ν : ℝ) : ℂ)) (t : ℂ))
    -- Proof comment: the compound-Poisson characteristic function is the exponential of the raw
    -- jump integral, which matches the simplified exponent above.
    rw [charFun_compoundPoissonMeasure]
    simpa [hexponent]

/-- Helper for Remark 16.18: convolution preserves infinite divisibility. -/
private lemma isInfinitelyDivisible_mul
    {μ ν : ProbabilityMeasure ℝ}
    (hμ : IsInfinitelyDivisible μ) (hν : IsInfinitelyDivisible ν) :
    IsInfinitelyDivisible (μ * ν) := by
  refine ⟨fun n ↦ ?_⟩
  rcases hμ.exists_root n with ⟨μroot, hμroot⟩
  rcases hν.exists_root n with ⟨νroot, hνroot⟩
  refine ⟨μroot * νroot, ?_⟩
  -- Proof comment: characteristic functions turn convolution into multiplication, so the
  -- convolution of the two roots is an `n`th root of `μ * ν`.
  apply ProbabilityMeasure.toMeasure_injective
  refine Measure.ext_of_charFun ?_
  funext t
  calc
    charFun (((μroot * νroot) ^ (n : ℕ) : ProbabilityMeasure ℝ) : Measure ℝ) t
        = charFun (μroot * νroot) t ^ (n : ℕ) := by
            simpa using
              congrArg (fun f : ℝ → ℂ ↦ f t) (ProbabilityMeasure.charFun_pow (μroot * νroot) (n : ℕ))
    _ = (charFun (μroot : Measure ℝ) t) ^ (n : ℕ) * (charFun (νroot : Measure ℝ) t) ^ (n : ℕ) := by
          rw [ProbabilityMeasure.toMeasure_mul, MeasureTheory.charFun_conv, mul_pow]
    _ = charFun (μ : Measure ℝ) t * charFun (ν : Measure ℝ) t := by
          rw [← hμroot, ← hνroot]
          simp only [ProbabilityMeasure.charFun_pow]
    _ = charFun (((μ * ν : ProbabilityMeasure ℝ) : Measure ℝ)) t := by
          rw [ProbabilityMeasure.toMeasure_mul, MeasureTheory.charFun_conv]

/-- Helper for Remark 16.18: along an additive orbit, repeated convolution with the root law
recovers the successive parameter multiples. -/
private theorem convolutionPower_succ_eq_of_additiveOrbit
    {E α : Type*} [AddMonoid E] [MeasurableSpace E] [MeasurableAdd₂ E] [AddMonoid α]
    (ν : α → ProbabilityMeasure E) (a : α)
    (hstep : ∀ k : ℕ,
      (((ν (((k + 1 : ℕ) • a)) : ProbabilityMeasure E) : Measure E) ∗ (ν a : Measure E) =
        (ν (((k + 2 : ℕ) • a)) : Measure E))) :
    ∀ k : ℕ, (ν a) ^ (k + 1) = ν (((k + 1 : ℕ) • a))
  | 0 => by
      -- Proof comment: the first convolution power is the root law itself.
      simp
  | k + 1 => by
      -- Proof comment: add one more convolution factor and use the additive-orbit recursion.
      rw [pow_succ, convolutionPower_succ_eq_of_additiveOrbit ν a hstep k]
      exact ProbabilityMeasure.toMeasure_injective (hstep k)

/-- Helper for Remark 16.18: every real Gaussian law is infinitely divisible. -/
private lemma gaussianReal_infinitelyDivisible (m : ℝ) (σ2 : NNReal) :
    IsInfinitelyDivisible
      (⟨gaussianReal m σ2, inferInstance⟩ : ProbabilityMeasure ℝ) := by
  refine ⟨fun n ↦ ?_⟩
  let gaussianLaw : ℝ × NNReal → ProbabilityMeasure ℝ :=
    fun p ↦ ⟨gaussianReal p.1 p.2, inferInstance⟩
  refine ⟨gaussianLaw (m / (n : ℝ), σ2 / (n : NNReal)), ?_⟩
  -- Route correction: rebuild the Gaussian root formula directly from the additive-orbit
  -- convolution identity, avoiding the brittle old chapter import route.
  change gaussianLaw (m / (n : ℝ), σ2 / (n : NNReal)) ^ (n : ℕ) = gaussianLaw (m, σ2)
  have hpow :=
    convolutionPower_succ_eq_of_additiveOrbit
      (ν := gaussianLaw) (a := (m / (n : ℝ), σ2 / (n : NNReal)))
      (hstep := by
        intro k
        -- Proof comment: Gaussian convolution adds the mean and variance parameters.
        simp [gaussianLaw]
        rw [ProbabilityTheory.gaussianReal_conv_gaussianReal]
        congr <;> ring)
      n.natPred
  have hnR : (n : ℝ) ≠ 0 := by
    exact_mod_cast n.ne_zero
  have hnNN : (n : NNReal) ≠ 0 := by
    exact_mod_cast n.ne_zero
  rw [n.natPred_add_one] at hpow
  calc
    gaussianLaw (m / (n : ℝ), σ2 / (n : NNReal)) ^ (n : ℕ)
        = gaussianLaw ((n : ℕ) • (m / (n : ℝ), σ2 / (n : NNReal))) := by
            simpa using hpow
    _ = gaussianLaw (m, σ2) := by
          congr 1
          ext
          · -- Proof comment: summing the root means recovers the original mean.
            simp [nsmul_eq_mul]
            field_simp [hnR]
          · -- Proof comment: summing the root variances recovers the original variance.
            simp [nsmul_eq_mul, div_eq_mul_inv, hnNN, mul_assoc, mul_left_comm, mul_comm]

/-- The explicit finite-jump law attached to a canonical Lévy--Khinchin triple. -/
def finiteCanonicalLaw (τ : LevyKhinchinTriple) [IsFiniteMeasure τ.ν] (hσ : 0 ≤ τ.sigma2) :
    ProbabilityMeasure ℝ :=
  let γ : ProbabilityMeasure ℝ :=
    ⟨gaussianReal
      (τ.b - ∫ x : ℝ, levyKhinchinCanonicalCentering x ∂τ.ν)
      ⟨τ.sigma2, hσ⟩, inferInstance⟩
  γ * compoundPoissonMeasure τ.ν

/-- The explicit finite-jump law realizes the given canonical triple in the Lévy--Khinchin
formula. -/
theorem finiteCanonicalLaw_hasLevyKhinchinRepresentation
    {τ : LevyKhinchinTriple} [IsFiniteMeasure τ.ν] (hτ : IsCanonicalTriple τ) :
    HasLevyKhinchinRepresentation (finiteCanonicalLaw τ hτ.sigma2_nonneg) τ := by
  let σ2NN : NNReal := ⟨τ.sigma2, hτ.sigma2_nonneg⟩
  let gaussianDrift : ℝ := τ.b - ∫ x : ℝ, levyKhinchinCanonicalCentering x ∂τ.ν
  let γ : ProbabilityMeasure ℝ := ⟨gaussianReal gaussianDrift σ2NN, inferInstance⟩
  let π : ProbabilityMeasure ℝ := compoundPoissonMeasure τ.ν
  have hγ :
      HasLevyKhinchinRepresentation γ
        { sigma2 := σ2NN, b := gaussianDrift, ν := 0 } := by
    -- Proof comment: the Gaussian factor carries the quadratic coefficient and the residual
    -- drift.
    simpa [γ] using gaussian_hasLevyKhinchinRepresentation gaussianDrift σ2NN
  have hπ :
      HasLevyKhinchinRepresentation π
        { sigma2 := 0
          b := ∫ x : ℝ, levyKhinchinCanonicalCentering x ∂τ.ν
          ν := τ.ν } := by
    -- Proof comment: the finite jump intensity is represented by the canonical compound-Poisson
    -- law.
    simpa [π] using
      compoundPoisson_hasLevyKhinchinRepresentation
        τ.ν hτ.isCanonicalMeasure.measure_singleton_zero
  constructor
  · exact hτ
  · intro t
    have hsumExp :
        levyKhinchinExponent { sigma2 := σ2NN, b := gaussianDrift, ν := 0 } t +
            levyKhinchinExponent
              { sigma2 := 0
                b := ∫ x : ℝ, levyKhinchinCanonicalCentering x ∂τ.ν
                ν := τ.ν } t =
          levyKhinchinExponent τ t := by
      -- Proof comment: the Gaussian and jump exponents add back to the target exponent of `τ`.
      simp [levyKhinchinExponent, levyKhinchinExponentWithCentering, σ2NN, gaussianDrift,
        sub_eq_add_neg, add_assoc, add_left_comm, add_comm, mul_assoc, mul_left_comm, mul_comm]
      ring
    -- Proof comment: convolution multiplies characteristic functions, so the exponents add.
    simpa [finiteCanonicalLaw, γ, π, ProbabilityMeasure.toMeasure_mul, MeasureTheory.charFun_conv]
      using
        (show charFun (γ * π) t = Complex.exp (levyKhinchinExponent τ t) by
          rw [ProbabilityMeasure.toMeasure_mul, MeasureTheory.charFun_conv, hγ.charFun_eq_exp,
            hπ.charFun_eq_exp, ← Complex.exp_add, hsumExp])

/-- Helper for Remark 16.18: the explicit finite-jump law is infinitely divisible because it is
the convolution of a Gaussian law and a compound-Poisson law. -/
private theorem finiteCanonicalLaw_isInfinitelyDivisible
    {τ : LevyKhinchinTriple} [IsFiniteMeasure τ.ν] (hτ : IsCanonicalTriple τ) :
    IsInfinitelyDivisible (finiteCanonicalLaw τ hτ.sigma2_nonneg) := by
  let σ2NN : NNReal := ⟨τ.sigma2, hτ.sigma2_nonneg⟩
  let gaussianDrift : ℝ := τ.b - ∫ x : ℝ, levyKhinchinCanonicalCentering x ∂τ.ν
  let γ : ProbabilityMeasure ℝ := ⟨gaussianReal gaussianDrift σ2NN, inferInstance⟩
  let π : ProbabilityMeasure ℝ := compoundPoissonMeasure τ.ν
  have hγInfDiv : IsInfinitelyDivisible γ := by
    -- Proof comment: Gaussian laws have explicit convolution roots.
    simpa [γ] using gaussianReal_infinitelyDivisible gaussianDrift σ2NN
  have hπInfDiv : IsInfinitelyDivisible π := by
    -- Proof comment: compound-Poisson laws are already known to be infinitely divisible.
    simpa [π] using compoundPoissonMeasure_infinitelyDivisible τ.ν
  -- Proof comment: the explicit finite law is the convolution of those two infinitely divisible
  -- factors.
  simpa [finiteCanonicalLaw, γ, π] using isInfinitelyDivisible_mul hγInfDiv hπInfDiv

/-- A Lévy--Khinchin representation with finite jump measure is automatically infinitely
divisible. -/
theorem isInfinitelyDivisible_of_hasLevyKhinchinRepresentation_of_isFiniteMeasure
    {μ : ProbabilityMeasure ℝ} {τ : LevyKhinchinTriple} [IsFiniteMeasure τ.ν]
    (hτ : HasLevyKhinchinRepresentation μ τ) :
    IsInfinitelyDivisible μ := by
  have hmodel :
      HasLevyKhinchinRepresentation
        (finiteCanonicalLaw τ hτ.isCanonicalTriple.sigma2_nonneg) τ :=
    finiteCanonicalLaw_hasLevyKhinchinRepresentation hτ.isCanonicalTriple
  have hmodelEq :
      finiteCanonicalLaw τ hτ.isCanonicalTriple.sigma2_nonneg = μ := by
    -- Proof comment: the explicit finite law and `μ` have the same characteristic function
    -- because they realize the same exponent.
    apply ProbabilityMeasure.toMeasure_injective
    refine Measure.ext_of_charFun ?_
    funext t
    rw [hmodel.charFun_eq_exp, hτ.charFun_eq_exp]
  have hmodelInfDiv :
      IsInfinitelyDivisible (finiteCanonicalLaw τ hτ.isCanonicalTriple.sigma2_nonneg) :=
    finiteCanonicalLaw_isInfinitelyDivisible hτ.isCanonicalTriple
  exact hmodelEq ▸ hmodelInfDiv

end MeasureTheory.ProbabilityMeasure
