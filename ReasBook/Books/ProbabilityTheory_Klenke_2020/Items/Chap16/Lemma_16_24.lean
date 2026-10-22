/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib
import Books.ProbabilityTheory_Klenke_2020.Items.Chap16.Definition_16_1
import Books.ProbabilityTheory_Klenke_2020.Items.Chap16.Definition_16_16
import Books.ProbabilityTheory_Klenke_2020.Items.Chap16.Definition_16_20

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory ProbabilityTheory
open scoped MeasureTheory

noncomputable section

namespace MeasureTheory.ProbabilityMeasure

/-- The canonical truncation function `x ↦ x 𝟙_{|x| < 1}` used in the real Lévy--Khinchin
formula. -/
def levyKhinchinCanonicalCentering (x : ℝ) : ℝ :=
  if |x| < 1 then x else 0

/-- Helper for Lemma 16.24: the canonical truncation function is measurable. -/
lemma measurable_levyKhinchinCanonicalCentering :
    Measurable levyKhinchinCanonicalCentering := by
  -- Proof comment: `levyKhinchinCanonicalCentering` is a piecewise combination of the identity
  -- and the zero function across the measurable set `{x | |x| < 1}`.
  classical
  simpa [levyKhinchinCanonicalCentering] using
    Measurable.piecewise
      (s := {x : ℝ | |x| < 1})
      (measurableSet_lt measurable_abs measurable_const)
      measurable_id
      measurable_const

/-- Helper for Lemma 16.24: the centered Lévy--Khinchin jump kernel at frequency `t`. -/
private def levyKhinchinCanonicalKernel (t : ℝ) : ℝ → ℂ :=
  fun x ↦
    Complex.exp (((t * x : ℝ) : ℂ) * Complex.I) - 1 -
      (((t * levyKhinchinCanonicalCentering x : ℝ) : ℂ) * Complex.I)

/-- Helper for Lemma 16.24: the canonical jump kernel is measurable. -/
private lemma measurable_levyKhinchinCanonicalKernel (t : ℝ) :
    Measurable (levyKhinchinCanonicalKernel t) := by
  -- Proof comment: once the centering cutoff is packaged as a measurable map, measurability of
  -- the oscillatory kernel is routine.
  have hExp :
      Measurable (fun x : ℝ ↦ Complex.exp (((t * x : ℝ) : ℂ) * Complex.I)) := by
    fun_prop
  have hCenter :
      Measurable
        (fun x : ℝ ↦ (((t * levyKhinchinCanonicalCentering x : ℝ) : ℂ) * Complex.I)) := by
    exact
      (Complex.measurable_ofReal.comp
        (measurable_const.mul measurable_levyKhinchinCanonicalCentering)).mul_const Complex.I
  exact (hExp.sub measurable_const).sub hCenter

/-- The Lévy--Khinchin exponent written with an arbitrary centering function `f`. -/
def levyKhinchinExponentWithCentering (σ2 b : ℝ) (ν : Measure ℝ) (f : ℝ → ℝ) : ℝ → ℂ :=
  fun t ↦
    (((-(σ2 / 2) * t ^ (2 : ℕ) : ℝ) : ℂ)) +
      (((b * t : ℝ) : ℂ) * Complex.I) +
      ∫ x : ℝ,
        (Complex.exp (((t * x : ℝ) : ℂ) * Complex.I) - 1 -
          (((t * f x : ℝ) : ℂ) * Complex.I)) ∂ν

/-- The Lévy--Khinchin exponent associated with a triple `(σ², b, ν)`. -/
def levyKhinchinExponent (τ : LevyKhinchinTriple) : ℝ → ℂ :=
  levyKhinchinExponentWithCentering τ.sigma2 τ.b τ.ν levyKhinchinCanonicalCentering

/-- A triple gives a Lévy--Khinchin representation of `μ` when it is canonical and the
characteristic function of `μ` is the exponential of its Lévy--Khinchin exponent. -/
def HasLevyKhinchinRepresentation
    (μ : ProbabilityMeasure ℝ) (τ : LevyKhinchinTriple) : Prop :=
  IsCanonicalTriple τ ∧
    ∀ t : ℝ, charFun μ t = Complex.exp (levyKhinchinExponent τ t)

namespace HasLevyKhinchinRepresentation

/-- A Lévy--Khinchin representation is, in particular, canonical. -/
theorem isCanonicalTriple
    {μ : ProbabilityMeasure ℝ} {τ : LevyKhinchinTriple}
    (hτ : HasLevyKhinchinRepresentation μ τ) :
    IsCanonicalTriple τ :=
  hτ.1

/-- A Lévy--Khinchin representation identifies the characteristic function with the exponential of
the associated exponent. -/
theorem charFun_eq_exp
    {μ : ProbabilityMeasure ℝ} {τ : LevyKhinchinTriple}
    (hτ : HasLevyKhinchinRepresentation μ τ) (t : ℝ) :
    charFun μ t = Complex.exp (levyKhinchinExponent τ t) :=
  hτ.2 t

end HasLevyKhinchinRepresentation

/-- Helper for Lemma 16.24: finite nat-scaling preserves canonicality of a Lévy measure on `ℝ`. -/
lemma isCanonicalMeasure_nsmul {ν : Measure ℝ} (n : ℕ) (hν : IsCanonicalMeasure ν) :
    IsCanonicalMeasure ((n : ℕ) • ν) := by
  have hmeasure : (n : ℕ) • ν = (n : ENNReal) • ν := by
    ext s hs
    simp [nsmul_eq_mul]
  refine ⟨?_, ?_⟩
  · -- Proof comment: scalar multiplication preserves the vanishing atom at the origin.
    simp [hν.measure_singleton_zero]
  · -- Proof comment: integrability of `min (x^2) 1` is stable under finite measure scaling.
    rw [hmeasure]
    simpa using hν.integrable_sq_min_one.smul_measure (c := (n : ENNReal)) (by simp)

/-- Helper for Lemma 16.24: scaling every component of a Lévy--Khinchin triple by `n` multiplies
the exponent by `(n : ℂ)`. -/
lemma levyKhinchinExponent_nsmul (τ : LevyKhinchinTriple) (n : ℕ) (t : ℝ) :
    levyKhinchinExponent
        { sigma2 := (n : ℝ) * τ.sigma2
          b := (n : ℝ) * τ.b
          ν := (n : ℕ) • τ.ν } t =
      (n : ℂ) * levyKhinchinExponent τ t := by
  -- Proof comment: every term in the exponent scales linearly with the Gaussian coefficient,
  -- the drift, and the jump measure.
  have hmeasure : (n : ℕ) • τ.ν = (n : ENNReal) • τ.ν := by
    ext s hs
    simp [nsmul_eq_mul]
  rw [levyKhinchinExponent, levyKhinchinExponentWithCentering, levyKhinchinExponent,
    levyKhinchinExponentWithCentering, hmeasure, MeasureTheory.integral_smul_measure]
  let J : ℂ :=
    ∫ x : ℝ,
      (Complex.exp (((t * x : ℝ) : ℂ) * Complex.I) - 1 -
        (((t * levyKhinchinCanonicalCentering x : ℝ) : ℂ) * Complex.I)) ∂τ.ν
  change
      (((-(((n : ℝ) * τ.sigma2) / 2) * t ^ (2 : ℕ) : ℝ) : ℂ)) +
          ((((n : ℝ) * τ.b * t : ℝ) : ℂ) * Complex.I) +
          ((n : ENNReal).toReal : ℝ) • J
        =
      (n : ℂ) *
        (((( -(τ.sigma2 / 2) * t ^ (2 : ℕ) : ℝ) : ℂ)) +
          (((τ.b * t : ℝ) : ℂ) * Complex.I) +
          J)
  have hsmul :
      ((n : ENNReal).toReal : ℝ) • J = (n : ℂ) * J := by
    simp [J, Algebra.smul_def]
  rw [hsmul]
  simp [mul_add, mul_assoc, mul_comm]
  ring

-- Proof sketch: the log-characteristic function of the `n`-fold convolution power is `n` times
-- the original exponent, so the Gaussian coefficient, the drift coefficient, and the Lévy
-- measure all scale by `n`.
/-- Part (1) of Lemma 16.24: if a probability law on `ℝ` has Lévy--Khinchin triple `(σ², b, ν)`,
then the law of the sum of `n` i.i.d. copies has Lévy--Khinchin triple
`((n : ℝ) σ², (n : ℝ) b, n ν)`, realized in Lean as the `n`th convolution power. -/
theorem pow_hasLevyKhinchinRepresentation
    (μ : ProbabilityMeasure ℝ) (τ : LevyKhinchinTriple) (n : ℕ+)
    (hτ : HasLevyKhinchinRepresentation μ τ) :
    HasLevyKhinchinRepresentation (μ ^ (n : ℕ))
      { sigma2 := (n : ℝ) * τ.sigma2
        b := (n : ℝ) * τ.b
        ν := (n : ℕ) • τ.ν } := by
  constructor
  · -- Proof comment: canonicality survives because both the Gaussian coefficient and the Lévy
    -- measure are scaled by a nonnegative factor.
    refine ⟨?_, isCanonicalMeasure_nsmul (n : ℕ) hτ.isCanonicalTriple.isCanonicalMeasure⟩
    exact mul_nonneg (by positivity) hτ.isCanonicalTriple.sigma2_nonneg
  · intro t
    -- Proof comment: the characteristic function of the convolution power is the pointwise
    -- `n`th power, and exponentials turn multiplication of exponents into powers.
    calc
      charFun (μ ^ (n : ℕ)) t = charFun μ t ^ (n : ℕ) := by
        simpa using
          congrArg (fun f : ℝ → ℂ ↦ f t) (ProbabilityMeasure.charFun_pow μ (n : ℕ))
      _ = Complex.exp (levyKhinchinExponent τ t) ^ (n : ℕ) := by
        rw [hτ.charFun_eq_exp]
      _ = Complex.exp (((n : ℕ) : ℂ) * levyKhinchinExponent τ t) := by
        rw [← Complex.exp_nat_mul]
      _ = Complex.exp
            (levyKhinchinExponent
              { sigma2 := (n : ℝ) * τ.sigma2
                b := (n : ℝ) * τ.b
                ν := (n : ℕ) • τ.ν } t) := by
        rw [levyKhinchinExponent_nsmul]

/-- Helper for Lemma 16.24: positive scaling rewrites the cutoff `|a * x| < 1` as
`|x| < 1 / a`. -/
lemma abs_mul_lt_one_iff {a x : ℝ} (ha : 0 < a) :
    |a * x| < 1 ↔ |x| < 1 / a := by
  rw [abs_mul, abs_of_pos ha, mul_comm, lt_div_iff₀ ha]

/-- Helper for Lemma 16.24: inside the unit ball the canonical truncated second moment is just
`x²`. -/
private lemma sqMinOne_eq_sq_of_abs_lt_one {x : ℝ} (hx : |x| < 1) :
    min (x ^ (2 : ℕ)) 1 = x ^ (2 : ℕ) := by
  -- Proof comment: inside the unit ball the truncation `min (x^2) 1` does not cut anything off.
  refine min_eq_left ?_
  exact le_of_lt ((sq_lt_one_iff_abs_lt_one x).2 hx)

/-- Helper for Lemma 16.24: outside the unit ball the canonical truncated second moment is `1`. -/
private lemma sqMinOne_eq_one_of_one_le_abs {x : ℝ} (hx : 1 ≤ |x|) :
    min (x ^ (2 : ℕ)) 1 = 1 := by
  -- Proof comment: once `|x| ≥ 1`, the truncation saturates at `1`.
  refine min_eq_right ?_
  have hxSq : 1 ≤ |x| * |x| := by
    nlinarith
  simpa [pow_two, sq_abs] using hxSq

/-- Helper for Lemma 16.24: the quadratic term `|t * x|²` factors as `|t|² x²`. -/
private lemma abs_mul_sq (t x : ℝ) :
    |t * x| ^ (2 : ℕ) = |t| ^ (2 : ℕ) * x ^ (2 : ℕ) := by
  -- Proof comment: take absolute values first, then expand the square of the product.
  rw [abs_mul, mul_pow, sq_abs, sq_abs]

/-- Helper for Lemma 16.24: when `|t * x| > 1`, the crude bound `2 + |t * x|` is still controlled
by `3 |t * x|²`. -/
private lemma two_add_abs_mul_le_three_abs_mul_sq {t x : ℝ} (hlarge : 1 < |t * x|) :
    2 + |t * x| ≤ 3 * |t * x| ^ (2 : ℕ) := by
  -- Proof comment: if `|t * x| > 1`, then both `2` and `|t * x|` are bounded by multiples of
  -- `|t * x|²`.
  nlinarith [le_of_lt hlarge, sq_nonneg (|t * x|)]

/-- Helper for Lemma 16.24: the oscillatory term `exp (i t x) - 1` is uniformly bounded by `2`. -/
private lemma norm_exp_sub_one_mul_I_le_two (t x : ℝ) :
    ‖Complex.exp (((t * x : ℝ) : ℂ) * Complex.I) - 1‖ ≤ 2 := by
  -- Proof comment: `exp (i y)` lies on the unit circle, so subtracting `1` has norm at most `2`.
  calc
    ‖Complex.exp (((t * x : ℝ) : ℂ) * Complex.I) - 1‖
        ≤ ‖Complex.exp (((t * x : ℝ) : ℂ) * Complex.I)‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
    _ = 1 + 1 := by
          rw [Complex.norm_exp_ofReal_mul_I]
          simp
    _ = 2 := by norm_num

/-- Helper for Lemma 16.24: the oscillatory remainder is bounded by `2 + |t * x|`. -/
private lemma norm_exp_sub_one_sub_id_mul_I_le_two_add_abs_mul (t x : ℝ) :
    ‖Complex.exp (((t * x : ℝ) : ℂ) * Complex.I) - 1 -
        (((t * x : ℝ) : ℂ) * Complex.I)‖ ≤
      2 + |t * x| := by
  -- Proof comment: use the triangle inequality and the basic bounds for `exp (i y) - 1` and
  -- `‖y I‖`.
  calc
    ‖Complex.exp (((t * x : ℝ) : ℂ) * Complex.I) - 1 -
        (((t * x : ℝ) : ℂ) * Complex.I)‖
        ≤ ‖Complex.exp (((t * x : ℝ) : ℂ) * Complex.I) - 1‖ +
            ‖(((t * x : ℝ) : ℂ) * Complex.I)‖ := norm_sub_le _ _
    _ ≤ 2 + |t * x| := by
      gcongr
      · exact norm_exp_sub_one_mul_I_le_two t x
      · simp [Complex.norm_I, Real.norm_eq_abs]

/-- Helper for Lemma 16.24: the two truncation functions occurring in the affine drift correction
are controlled by the canonical integrand `x ↦ min (x^2) 1`. -/
lemma abs_affineCenteringDifference_le {a : ℝ} (ha : 0 < a) (x : ℝ) :
    |(if |x| < 1 / a then x else 0) - (if |x| < 1 then x else 0)| ≤
      max a (1 / a) * min (x ^ (2 : ℕ)) 1 := by
  by_cases hxSmall : |x| < 1 / a
  · by_cases hxUnit : |x| < 1
    · -- Proof comment: both truncations agree on the common small-ball region.
      have hnonneg : 0 ≤ max a (1 / a) * min (x ^ (2 : ℕ)) 1 := by
        positivity
      have hsmall : |x| < a⁻¹ := by simpa [one_div] using hxSmall
      simpa [hsmall, hxUnit] using hnonneg
    · -- Proof comment: on `1 ≤ |x| < 1 / a`, only the scaled cutoff survives, so `min (x^2) 1`
      -- is `1`.
      have hxLarge : 1 ≤ |x| := le_of_not_gt hxUnit
      have hmax : 1 / a ≤ max a (1 / a) := le_max_right _ _
      calc
        |(if |x| < 1 / a then x else 0) - (if |x| < 1 then x else 0)|
            = |x| := by
                have hsmall : |x| < a⁻¹ := by simpa [one_div] using hxSmall
                simp [hsmall, hxUnit]
        _ ≤ 1 / a := le_of_lt hxSmall
        _ ≤ max a (1 / a) := hmax
        _ = max a (1 / a) * min (x ^ (2 : ℕ)) 1 := by
              rw [sqMinOne_eq_one_of_one_le_abs hxLarge, mul_one]
  · by_cases hxUnit : |x| < 1
    · -- Proof comment: on `1 / a ≤ |x| < 1`, only the canonical cutoff survives.
      have hxLower : 1 / a ≤ |x| := le_of_not_gt hxSmall
      have hmul : 1 ≤ a * |x| := by
        have := mul_le_mul_of_nonneg_left hxLower ha.le
        simpa [ha.ne', mul_comm, mul_left_comm, mul_assoc] using this
      have hxabs : |x| ≤ a * x ^ (2 : ℕ) := by
        have := mul_le_mul_of_nonneg_right hmul (abs_nonneg x)
        simpa [pow_two, sq_abs, mul_comm, mul_left_comm, mul_assoc] using this
      calc
        |(if |x| < 1 / a then x else 0) - (if |x| < 1 then x else 0)|
            = |x| := by
                have hsmall : ¬ |x| < a⁻¹ := by simpa [one_div] using hxSmall
                simp [hsmall, hxUnit]
        _ ≤ a * x ^ (2 : ℕ) := hxabs
        _ ≤ max a (1 / a) * x ^ (2 : ℕ) := by
              gcongr
              exact le_max_left _ _
        _ = max a (1 / a) * min (x ^ (2 : ℕ)) 1 := by
              rw [sqMinOne_eq_sq_of_abs_lt_one hxUnit]
    · -- Proof comment: outside both cutoffs the difference vanishes.
      have hnonneg : 0 ≤ max a (1 / a) * min (x ^ (2 : ℕ)) 1 := by
        positivity
      have hsmall : ¬ |x| < a⁻¹ := by simpa [one_div] using hxSmall
      simpa [hsmall, hxUnit] using hnonneg

/-- Helper for Lemma 16.24: the affine centering correction is integrable against a canonical
Lévy measure. -/
lemma integrable_affineCenteringDifference {ν : Measure ℝ} {a : ℝ}
    (ha : 0 < a) (hν : IsCanonicalMeasure ν) :
    Integrable
      (fun x : ℝ ↦ (if |x| < 1 / a then x else 0) - (if |x| < 1 then x else 0)) ν := by
  have hbound :
      Integrable (fun x : ℝ ↦ max a (1 / a) * min (x ^ (2 : ℕ)) 1) ν := by
    -- Proof comment: the canonical truncated second moment remains integrable after multiplying
    -- by the constant `max a (1 / a)`.
    simpa [mul_comm, mul_left_comm, mul_assoc] using
      hν.integrable_sq_min_one.const_mul (max a (1 / a))
  have hmeas :
      Measurable
        (fun x : ℝ ↦ (if |x| < 1 / a then x else 0) - (if |x| < 1 then x else 0)) := by
    -- Proof comment: both cutoff functions are measurable piecewise combinations of `id` and `0`.
    classical
    refine
      (Measurable.piecewise
        (s := {x : ℝ | |x| < 1 / a})
        (measurableSet_lt measurable_abs measurable_const)
        measurable_id
        measurable_const).sub ?_
    exact
      Measurable.piecewise
        (s := {x : ℝ | |x| < 1})
        (measurableSet_lt measurable_abs measurable_const)
        measurable_id
        measurable_const
  refine Integrable.mono' hbound hmeas.aestronglyMeasurable ?_
  exact Filter.Eventually.of_forall (fun x ↦ by
    simpa using abs_affineCenteringDifference_le ha x)

/-- Helper for Lemma 16.24: pushing a canonical Lévy measure forward by multiplication with a
positive scalar keeps it canonical. -/
lemma isCanonicalMeasure_map_mul {ν : Measure ℝ} {a : ℝ} (ha : 0 < a)
    (hν : IsCanonicalMeasure ν) :
    IsCanonicalMeasure (Measure.map (fun x : ℝ ↦ a * x) ν) := by
  let e : ℝ ≃ᵐ ℝ := (Homeomorph.mulLeft₀ a (ne_of_gt ha)).toMeasurableEquiv
  have hbound :
      Integrable (fun x : ℝ ↦ min (((a * x) ^ (2 : ℕ))) 1) ν := by
    have hmajor :
        ∀ x : ℝ,
          min ((a * x) ^ (2 : ℕ)) 1 ≤
            max (a ^ (2 : ℕ)) 1 * min (x ^ (2 : ℕ)) 1 := by
      intro x
      by_cases hx : |x| < 1
      · have hxSq : min (x ^ (2 : ℕ)) 1 = x ^ (2 : ℕ) :=
          sqMinOne_eq_sq_of_abs_lt_one hx
        calc
          min ((a * x) ^ (2 : ℕ)) 1 ≤ (a * x) ^ (2 : ℕ) := min_le_left _ _
          _ = a ^ (2 : ℕ) * x ^ (2 : ℕ) := by rw [mul_pow]
          _ ≤ max (a ^ (2 : ℕ)) 1 * x ^ (2 : ℕ) := by
                gcongr
                exact le_max_left _ _
          _ = max (a ^ (2 : ℕ)) 1 * min (x ^ (2 : ℕ)) 1 := by rw [hxSq]
      · have hxLarge : 1 ≤ |x| := le_of_not_gt hx
        calc
          min ((a * x) ^ (2 : ℕ)) 1 ≤ 1 := min_le_right _ _
          _ ≤ max (a ^ (2 : ℕ)) 1 := le_max_right _ _
          _ = max (a ^ (2 : ℕ)) 1 * min (x ^ (2 : ℕ)) 1 := by
                rw [sqMinOne_eq_one_of_one_le_abs hxLarge, mul_one]
    have hmeas : Measurable (fun x : ℝ ↦ min (((a * x) ^ (2 : ℕ))) 1) := by
      fun_prop
    have hdom :
        Integrable (fun x : ℝ ↦ max (a ^ (2 : ℕ)) 1 * min (x ^ (2 : ℕ)) 1) ν := by
      -- Proof comment: the scaled truncated second moment is dominated by a constant multiple of
      -- the canonical one.
      simpa [mul_comm, mul_left_comm, mul_assoc] using
        hν.integrable_sq_min_one.const_mul (max (a ^ (2 : ℕ)) 1)
    refine Integrable.mono' hdom hmeas.aestronglyMeasurable ?_
    · -- Proof comment: the scaled truncated second moment is dominated by a constant multiple of
      -- the canonical one.
      exact Filter.Eventually.of_forall (fun x ↦ by
        have hnonneg : 0 ≤ min ((a * x) ^ (2 : ℕ)) 1 := by
          positivity
        simpa [Real.norm_eq_abs, abs_of_nonneg hnonneg] using hmajor x)
  refine ⟨?_, ?_⟩
  · -- Proof comment: positive scaling fixes the origin and therefore preserves the missing atom
    -- at `{0}`.
    have hpre : (fun x : ℝ ↦ a * x) ⁻¹' ({0} : Set ℝ) = ({0} : Set ℝ) := by
      ext x
      simp [ha.ne']
    simpa [hpre, hν.measure_singleton_zero] using
      (Measure.map_apply
        (μ := ν)
        (f := fun x : ℝ ↦ a * x)
        (s := ({0} : Set ℝ))
        (measurable_const.mul measurable_id)
        (measurableSet_singleton (0 : ℝ)))
  · -- Proof comment: transport the canonical truncated second moment through the measurable
    -- equivalence `x ↦ a * x`.
    simpa [e, Function.comp_def] using
      (integrable_map_equiv e (fun x : ℝ ↦ min (x ^ (2 : ℕ)) 1)).2 hbound

/-- Helper for Lemma 16.24: the canonical Lévy--Khinchin kernel is pointwise dominated by the
canonical truncated second moment. -/
lemma norm_levyKhinchinCanonicalKernel_le (t x : ℝ) :
    ‖levyKhinchinCanonicalKernel t x‖ ≤
      max (3 * |t| ^ (2 : ℕ)) 2 * min (x ^ (2 : ℕ)) 1 := by
  by_cases hx : |x| < 1
  · by_cases htx : |t * x| ≤ 1
    · -- Proof comment: on the canonical small-jump region we use the quadratic remainder bound.
      have hquad :
          ‖Complex.exp (((t * x : ℝ) : ℂ) * Complex.I) - 1 -
              (((t * x : ℝ) : ℂ) * Complex.I)‖ ≤
            |t * x| ^ (2 : ℕ) := by
        simpa [Real.norm_eq_abs] using
          Complex.norm_exp_sub_one_sub_id_le (x := (((t * x : ℝ) : ℂ) * Complex.I)) (by
            simpa [Complex.norm_mul, Complex.norm_I, Real.norm_eq_abs] using htx)
      calc
        ‖levyKhinchinCanonicalKernel t x‖
            = ‖Complex.exp (((t * x : ℝ) : ℂ) * Complex.I) - 1 -
                (((t * x : ℝ) : ℂ) * Complex.I)‖ := by
                  simp [levyKhinchinCanonicalKernel, levyKhinchinCanonicalCentering, hx]
        _ ≤ |t * x| ^ (2 : ℕ) := hquad
        _ = |t| ^ (2 : ℕ) * x ^ (2 : ℕ) := abs_mul_sq t x
        _ ≤ 3 * |t| ^ (2 : ℕ) * x ^ (2 : ℕ) := by
              nlinarith [sq_nonneg (|t|), sq_nonneg x]
        _ ≤ max (3 * |t| ^ (2 : ℕ)) 2 * x ^ (2 : ℕ) := by
              gcongr
              exact le_max_left _ _
        _ = max (3 * |t| ^ (2 : ℕ)) 2 * min (x ^ (2 : ℕ)) 1 := by
              rw [sqMinOne_eq_sq_of_abs_lt_one hx]
    · -- Proof comment: if `|t * x| > 1`, the quadratic remainder still dominates after a crude
      -- bound.
      have hlarge : 1 < |t * x| := lt_of_not_ge htx
      calc
        ‖levyKhinchinCanonicalKernel t x‖
            = ‖Complex.exp (((t * x : ℝ) : ℂ) * Complex.I) - 1 -
                (((t * x : ℝ) : ℂ) * Complex.I)‖ := by
                  simp [levyKhinchinCanonicalKernel, levyKhinchinCanonicalCentering, hx]
        _ ≤ 2 + |t * x| := norm_exp_sub_one_sub_id_mul_I_le_two_add_abs_mul t x
        _ ≤ 3 * |t * x| ^ (2 : ℕ) := two_add_abs_mul_le_three_abs_mul_sq hlarge
        _ = 3 * (|t| ^ (2 : ℕ) * x ^ (2 : ℕ)) := by rw [abs_mul_sq]
        _ = 3 * |t| ^ (2 : ℕ) * x ^ (2 : ℕ) := by ring
        _ ≤ max (3 * |t| ^ (2 : ℕ)) 2 * x ^ (2 : ℕ) := by
              gcongr
              exact le_max_left _ _
        _ = max (3 * |t| ^ (2 : ℕ)) 2 * min (x ^ (2 : ℕ)) 1 := by
              rw [sqMinOne_eq_sq_of_abs_lt_one hx]
  · -- Proof comment: outside the unit ball the canonical centering vanishes, so the kernel is
    -- bounded by the universal `2` bound for `exp (i t x) - 1`.
    have hxLarge : 1 ≤ |x| := le_of_not_gt hx
    calc
      ‖levyKhinchinCanonicalKernel t x‖
          = ‖Complex.exp (((t * x : ℝ) : ℂ) * Complex.I) - 1‖ := by
              simp [levyKhinchinCanonicalKernel, levyKhinchinCanonicalCentering, hx]
      _ ≤ 2 := norm_exp_sub_one_mul_I_le_two t x
      _ ≤ max (3 * |t| ^ (2 : ℕ)) 2 := le_max_right _ _
      _ = max (3 * |t| ^ (2 : ℕ)) 2 * min (x ^ (2 : ℕ)) 1 := by
            rw [sqMinOne_eq_one_of_one_le_abs hxLarge, mul_one]

/-- Helper for Lemma 16.24: the canonical Lévy--Khinchin kernel is integrable against a canonical
Lévy measure. -/
lemma integrable_levyKhinchinCanonicalKernel {ν : Measure ℝ}
    (hν : IsCanonicalMeasure ν) (t : ℝ) :
    Integrable (levyKhinchinCanonicalKernel t) ν := by
  have hbound :
      Integrable (fun x : ℝ ↦ max (3 * |t| ^ (2 : ℕ)) 2 * min (x ^ (2 : ℕ)) 1) ν := by
    -- Proof comment: the dominating function is just a constant multiple of `min (x^2) 1`.
    simpa [mul_comm, mul_left_comm, mul_assoc] using
      hν.integrable_sq_min_one.const_mul (max (3 * |t| ^ (2 : ℕ)) 2)
  refine Integrable.mono' hbound (measurable_levyKhinchinCanonicalKernel t).aestronglyMeasurable ?_
  exact Filter.Eventually.of_forall (fun x ↦ norm_levyKhinchinCanonicalKernel_le t x)

/-- Helper for Lemma 16.24: the real-valued drift correction can be moved through the complex
Bochner integral as a scalar multiple of `Complex.I`. -/
private lemma integral_ofReal_mul_I {ν : Measure ℝ} (g : ℝ → ℝ) (t : ℝ) :
    ∫ x : ℝ, Complex.I * (((t * g x : ℝ) : ℂ)) ∂ν =
      Complex.I * (((t * ∫ x : ℝ, g x ∂ν : ℝ) : ℂ)) := by
  -- Proof comment: first pull the constant `I` through the integral, then reduce the complex
  -- integral to the real one.
  calc
    ∫ x : ℝ, Complex.I * (((t * g x : ℝ) : ℂ)) ∂ν
        = Complex.I * (∫ x : ℝ, ((t * g x : ℝ) : ℂ) ∂ν) := by
            simpa using
              (integral_const_mul (μ := ν) Complex.I
                (fun x : ℝ ↦ ((t * g x : ℝ) : ℂ)))
    _ = Complex.I * (((∫ x : ℝ, t * g x ∂ν : ℝ) : ℂ)) := by
          rw [integral_complex_ofReal]
    _ = Complex.I * (((t * ∫ x : ℝ, g x ∂ν : ℝ) : ℂ)) := by
          exact
            congrArg (fun r : ℝ ↦ Complex.I * (r : ℂ))
              (by simpa using (integral_const_mul (μ := ν) t g))

/-- Helper for Lemma 16.24: changing the centering function changes the Lévy--Khinchin kernel by
the corresponding linear drift term. -/
private lemma levyKhinchinKernel_sub_drift
    (t : ℝ) (f_new : ℝ → ℝ) (x : ℝ) :
    Complex.exp (((t * x : ℝ) : ℂ) * Complex.I) - 1 - (((t * f_new x : ℝ) : ℂ) * Complex.I) =
      levyKhinchinCanonicalKernel t x -
        Complex.I * (((t * (f_new x - levyKhinchinCanonicalCentering x) : ℝ) : ℂ)) := by
  -- Proof comment: separate the new centering term into the canonical cutoff plus the drift
  -- correction, then regroup linearly.
  simp [levyKhinchinCanonicalKernel, sub_eq_add_neg, mul_add, mul_comm]

/-- Helper for Lemma 16.24: changing from the scaled cutoff back to the canonical centering
shifts the drift by `∫ (f_new - levyKhinchinCanonicalCentering) dν`. -/
lemma levyKhinchinExponentWithCentering_changeCentering
    (σ2 b : ℝ) (ν : Measure ℝ) (hν : IsCanonicalMeasure ν) (f_new : ℝ → ℝ)
    (hfg : Integrable (fun x : ℝ ↦ f_new x - levyKhinchinCanonicalCentering x) ν) :
    levyKhinchinExponentWithCentering
        σ2 (b + ∫ x, (f_new x - levyKhinchinCanonicalCentering x) ∂ ν) ν f_new =
      levyKhinchinExponentWithCentering σ2 b ν levyKhinchinCanonicalCentering := by
  ext t
  let g : ℝ → ℝ := fun x ↦ f_new x - levyKhinchinCanonicalCentering x
  let kernel : ℝ → ℂ := levyKhinchinCanonicalKernel t
  let drift : ℝ → ℂ := fun x ↦ Complex.I * (((t * g x : ℝ) : ℂ))
  have hkernel : Integrable kernel ν := by
    -- Proof comment: the canonical kernel is integrable by the domination lemma proved above.
    simpa [kernel] using integrable_levyKhinchinCanonicalKernel hν t
  have hdrift : Integrable drift ν := by
    -- Proof comment: the centering correction stays integrable after multiplying by the fixed
    -- complex scalar `I`.
    simpa [drift, g] using ((hfg.const_mul t).ofReal.const_mul Complex.I)
  have hintegral :
      ∫ x : ℝ,
          (Complex.exp (((t * x : ℝ) : ℂ) * Complex.I) - 1 -
            (((t * f_new x : ℝ) : ℂ) * Complex.I)) ∂ν
        =
          ∫ x : ℝ, kernel x ∂ν - ∫ x : ℝ, drift x ∂ν := by
    calc
      ∫ x : ℝ,
          (Complex.exp (((t * x : ℝ) : ℂ) * Complex.I) - 1 -
            (((t * f_new x : ℝ) : ℂ) * Complex.I)) ∂ν
          =
            ∫ x : ℝ, (kernel x - drift x) ∂ν := by
              apply integral_congr_ae
              filter_upwards with x
              simpa [kernel, drift, g] using levyKhinchinKernel_sub_drift t f_new x
      _ = ∫ x : ℝ, kernel x ∂ν - ∫ x : ℝ, drift x ∂ν := by
            rw [integral_sub hkernel hdrift]
  -- Proof comment: evaluate pointwise in `t`, rewrite the integral difference, and then cancel
  -- the drift correction against the shifted `b` term.
  simp only [levyKhinchinExponentWithCentering]
  rw [hintegral, integral_ofReal_mul_I g t]
  let A : ℝ := ∫ x : ℝ, f_new x - levyKhinchinCanonicalCentering x ∂ν
  change
      (((-(σ2 / 2) * t ^ (2 : ℕ) : ℝ) : ℂ)) +
          ((((b + A) * t : ℝ) : ℂ) * Complex.I) +
          (∫ x : ℝ, kernel x ∂ν - Complex.I * (((t * A : ℝ) : ℂ)))
        =
      (((-(σ2 / 2) * t ^ (2 : ℕ) : ℝ) : ℂ)) +
          (((b * t : ℝ) : ℂ) * Complex.I) +
          ∫ x : ℝ, kernel x ∂ν
  have hcancel :
      ((((b + A) * t : ℝ) : ℂ) * Complex.I) - Complex.I * (((t * A : ℝ) : ℂ)) =
        (((b * t : ℝ) : ℂ) * Complex.I) := by
    have hreal : (b + A) * t - t * A = b * t := by
      ring
    calc
      ((((b + A) * t : ℝ) : ℂ) * Complex.I) - Complex.I * (((t * A : ℝ) : ℂ))
          = ((((b + A) * t : ℝ) : ℂ) * Complex.I) - (((t * A : ℝ) : ℂ) * Complex.I) := by
              congr 1
              rw [mul_comm]
      _ = (((((b + A) * t : ℝ) : ℂ) - (((t * A : ℝ) : ℂ))) * Complex.I) := by
            rw [← sub_mul]
      _ = (((((b + A) * t : ℝ) - t * A : ℝ) : ℂ)) * Complex.I := by
            norm_num
      _ = (((b * t : ℝ) : ℂ) * Complex.I) := by
            exact congrArg (fun r : ℝ ↦ (r : ℂ) * Complex.I) hreal
  calc
    (((-(σ2 / 2) * t ^ (2 : ℕ) : ℝ) : ℂ)) +
        ((((b + A) * t : ℝ) : ℂ) * Complex.I) +
        (∫ x : ℝ, kernel x ∂ν - Complex.I * (((t * A : ℝ) : ℂ)))
        =
      (((-(σ2 / 2) * t ^ (2 : ℕ) : ℝ) : ℂ)) +
        (((((b + A) * t : ℝ) : ℂ) * Complex.I) - Complex.I * (((t * A : ℝ) : ℂ))) +
        ∫ x : ℝ, kernel x ∂ν := by
          ring
    _ = (((-(σ2 / 2) * t ^ (2 : ℕ) : ℝ) : ℂ)) +
          (((b * t : ℝ) : ℂ) * Complex.I) +
          ∫ x : ℝ, kernel x ∂ν := by
            rw [hcancel]

/-- Helper for Lemma 16.24: after pushing a Lévy measure `ν` forward by `x ↦ a * x`, the
exponent rewrites back on `ν` with the cutoff `x ↦ x 𝟙_{|x| < 1 / a}` at frequency `a * t`. -/
lemma levyKhinchinExponent_map_mul_eq_withScaledCutoff
    (σ2 b : ℝ) (ν : Measure ℝ) {a : ℝ} (ha : 0 < a) (t : ℝ) :
    levyKhinchinExponent
        { sigma2 := a ^ (2 : ℕ) * σ2
          b := a * b
          ν := Measure.map (fun x : ℝ ↦ a * x) ν } t =
      levyKhinchinExponentWithCentering σ2 b ν
        (fun x : ℝ ↦ if |x| < 1 / a then x else 0) (a * t) := by
  let e : ℝ ≃ᵐ ℝ := (Homeomorph.mulLeft₀ a (ne_of_gt ha)).toMeasurableEquiv
  -- Proof comment: transport the pushforward integral through the measurable equivalence
  -- `x ↦ a * x`, then rewrite the cutoff as `|x| < 1 / a`.
  have hcutoff :
      ∀ x : ℝ,
        levyKhinchinCanonicalCentering (a * x) = if |x| < 1 / a then a * x else 0 := by
    intro x
    rw [levyKhinchinCanonicalCentering, abs_mul, abs_of_pos ha]
    have hcond : a * |x| < 1 ↔ |x| < 1 / a := by
      rw [lt_div_iff₀ ha, mul_comm]
    simp [hcond]
  have hIntegral :
      ∫ y : ℝ,
          (Complex.exp (((t * y : ℝ) : ℂ) * Complex.I) - 1 -
            (((t * levyKhinchinCanonicalCentering y : ℝ) : ℂ) * Complex.I)) ∂
              Measure.map (fun x : ℝ ↦ a * x) ν
        =
      ∫ x : ℝ,
          (Complex.exp (((t * (a * x) : ℝ) : ℂ) * Complex.I) - 1 -
            (((t * levyKhinchinCanonicalCentering (a * x) : ℝ) : ℂ) * Complex.I)) ∂ν := by
    simpa [e, Function.comp_def] using
      (integral_map_equiv
        (μ := ν)
        e
        (fun y : ℝ ↦
          Complex.exp (((t * y : ℝ) : ℂ) * Complex.I) - 1 -
            (((t * levyKhinchinCanonicalCentering y : ℝ) : ℂ) * Complex.I)))
  rw [levyKhinchinExponent, levyKhinchinExponentWithCentering, levyKhinchinExponentWithCentering,
    hIntegral]
  simp_rw [hcutoff]
  simp [mul_left_comm, mul_comm]
  ring

/-- Helper for Lemma 16.24: positive scaling preserves the Lévy--Khinchin exponent after the
canonical drift correction from formula (16.21) is added. -/
lemma levyKhinchinExponent_map_mul
    (τ : LevyKhinchinTriple) {a : ℝ} (ha : 0 < a) (hν : IsCanonicalMeasure τ.ν) (t : ℝ) :
    levyKhinchinExponent
        { sigma2 := a ^ (2 : ℕ) * τ.sigma2
          b := a * τ.b +
            a * ∫ x : ℝ,
              ((if |x| < 1 / a then x else 0) - (if |x| < 1 then x else 0)) ∂τ.ν
          ν := Measure.map (fun x : ℝ ↦ a * x) τ.ν } t =
      levyKhinchinExponent τ (a * t) := by
  let g : ℝ → ℝ := fun x : ℝ ↦ if |x| < 1 / a then x else 0
  let driftCorrection : ℝ := ∫ x : ℝ, (g x - (if |x| < 1 then x else 0)) ∂τ.ν
  have hg : Integrable (fun x : ℝ ↦ g x - levyKhinchinCanonicalCentering x) τ.ν := by
    -- Proof comment: this is exactly the affine-centering integrability statement already proved.
    simpa [g] using integrable_affineCenteringDifference ha hν
  calc
    levyKhinchinExponent
        { sigma2 := a ^ (2 : ℕ) * τ.sigma2
          b := a * τ.b +
            a * ∫ x : ℝ,
              ((if |x| < 1 / a then x else 0) - (if |x| < 1 then x else 0)) ∂τ.ν
          ν := Measure.map (fun x : ℝ ↦ a * x) τ.ν } t
        =
          levyKhinchinExponentWithCentering
            τ.sigma2
            (τ.b + driftCorrection)
            τ.ν g (a * t) := by
              -- Proof comment: reuse the scaled-cutoff normalization with the drift-corrected
              -- coefficient bundled into the `b` parameter.
              simpa [g, driftCorrection, levyKhinchinCanonicalCentering, add_mul, mul_add,
                add_assoc, add_left_comm, add_comm]
                using
                  levyKhinchinExponent_map_mul_eq_withScaledCutoff
                    τ.sigma2 (τ.b + driftCorrection) τ.ν ha t
    _ = levyKhinchinExponentWithCentering τ.sigma2 τ.b τ.ν levyKhinchinCanonicalCentering
          (a * t) := by
            simpa [g, driftCorrection, levyKhinchinCanonicalCentering] using
              congrArg (fun f : ℝ → ℂ ↦ f (a * t))
                (levyKhinchinExponentWithCentering_changeCentering
                  τ.sigma2 τ.b τ.ν hν g hg)
    _ = levyKhinchinExponent τ (a * t) := by
          rfl

/-- Helper for Lemma 16.24: increasing the drift parameter in
`levyKhinchinExponentWithCentering` by `d` adds the linear term `i d t`. -/
private lemma levyKhinchinExponentWithCentering_addDrift
    (σ2 b d : ℝ) (ν : Measure ℝ) (f : ℝ → ℝ) (t : ℝ) :
    levyKhinchinExponentWithCentering σ2 (b + d) ν f t =
      levyKhinchinExponentWithCentering σ2 b ν f t + (((d * t : ℝ) : ℂ) * Complex.I) := by
  simp [levyKhinchinExponentWithCentering, mul_add, add_assoc, add_left_comm, add_comm, mul_comm]

/-- Helper for Lemma 16.24: changing only the drift coefficient adds the linear term `i d t`
to the Lévy--Khinchin exponent. -/
lemma levyKhinchinExponent_addDrift
    (τ : LevyKhinchinTriple) (d t : ℝ) :
    levyKhinchinExponent { sigma2 := τ.sigma2, b := τ.b + d, ν := τ.ν } t =
      levyKhinchinExponent τ t + (((d * t : ℝ) : ℂ) * Complex.I) := by
  -- Proof comment: specialize the centering-level drift rewrite to the canonical centering
  -- function used by `levyKhinchinExponent`.
  simpa [levyKhinchinExponent] using
    levyKhinchinExponentWithCentering_addDrift
      τ.sigma2 τ.b d τ.ν levyKhinchinCanonicalCentering t

/-- Helper for Lemma 16.24: translating the law by `d` only changes the drift coefficient in the
Lévy--Khinchin triple. -/
lemma map_add_const_hasLevyKhinchinRepresentation
    (μ : ProbabilityMeasure ℝ) (τ : LevyKhinchinTriple)
    (hτ : HasLevyKhinchinRepresentation μ τ) (d : ℝ) :
    HasLevyKhinchinRepresentation
      (μ.map (measurable_affineMap 1 d).aemeasurable)
      { sigma2 := τ.sigma2, b := τ.b + d, ν := τ.ν } := by
  constructor
  · -- Proof comment: translation leaves the Gaussian coefficient and Lévy measure unchanged.
    refine ⟨hτ.isCanonicalTriple.sigma2_nonneg, ?_⟩
    simpa using hτ.isCanonicalTriple.isCanonicalMeasure
  · intro t
    -- Proof comment: rewrite the characteristic function of the translated law, then absorb the
    -- translation phase into the drift term of the exponent.
    calc
      charFun (μ.map (measurable_affineMap 1 d).aemeasurable) t
          = charFun (μ : Measure ℝ) t * Complex.exp (((inner ℝ d t : ℝ) : ℂ) * Complex.I) := by
              rw [ProbabilityMeasure.toMeasure_map]
              simpa [measurable_affineMap] using
                (MeasureTheory.charFun_map_add_const (μ := (μ : Measure ℝ)) d t)
      _ = charFun (μ : Measure ℝ) t * Complex.exp (((d * t : ℝ) : ℂ) * Complex.I) := by
            have hinner : inner ℝ d t = d * t := by
              change t * d = d * t
              ring
            rw [hinner]
      _ = Complex.exp (levyKhinchinExponent τ t) *
            Complex.exp (((d * t : ℝ) : ℂ) * Complex.I) := by
              rw [hτ.charFun_eq_exp]
      _ = Complex.exp (levyKhinchinExponent τ t + (((d * t : ℝ) : ℂ) * Complex.I)) := by
            rw [← Complex.exp_add]
      _ = Complex.exp
            (levyKhinchinExponent { sigma2 := τ.sigma2, b := τ.b + d, ν := τ.ν } t) := by
            rw [levyKhinchinExponent_addDrift]

/-- Helper for Lemma 16.24: positive scaling transports a Lévy--Khinchin representation to the
scaled law with the canonical drift correction from formula (16.21). -/
lemma map_mul_hasLevyKhinchinRepresentation
    (μ : ProbabilityMeasure ℝ) (τ : LevyKhinchinTriple)
    (hτ : HasLevyKhinchinRepresentation μ τ) {a : ℝ} (ha : 0 < a) :
    HasLevyKhinchinRepresentation
      (μ.map (measurable_affineMap a 0).aemeasurable)
      { sigma2 := a ^ (2 : ℕ) * τ.sigma2
        b := a * τ.b +
          a * ∫ x : ℝ, ((if |x| < 1 / a then x else 0) - (if |x| < 1 then x else 0)) ∂τ.ν
        ν := Measure.map (fun x : ℝ ↦ a * x) τ.ν } := by
  constructor
  · -- Proof comment: the Gaussian coefficient stays nonnegative and the pushed-forward Lévy
    -- measure remains canonical under positive scaling.
    refine ⟨?_, isCanonicalMeasure_map_mul ha hτ.isCanonicalTriple.isCanonicalMeasure⟩
    exact mul_nonneg (by positivity) hτ.isCanonicalTriple.sigma2_nonneg
  · intro t
    -- Proof comment: rewrite the scaled characteristic function and then use the exponent
    -- normalization already proved for positive scaling.
    calc
      charFun (μ.map (measurable_affineMap a 0).aemeasurable) t
          = charFun (μ : Measure ℝ) (a * t) := by
              rw [ProbabilityMeasure.toMeasure_map]
              simpa [measurable_affineMap, zero_add] using
                (MeasureTheory.charFun_map_mul (μ := (μ : Measure ℝ)) a t)
      _ = Complex.exp (levyKhinchinExponent τ (a * t)) := by
            rw [hτ.charFun_eq_exp]
      _ = Complex.exp
            (levyKhinchinExponent
              { sigma2 := a ^ (2 : ℕ) * τ.sigma2
                b := a * τ.b +
                  a * ∫ x : ℝ,
                    ((if |x| < 1 / a then x else 0) - (if |x| < 1 then x else 0)) ∂τ.ν
                ν := Measure.map (fun x : ℝ ↦ a * x) τ.ν } t) := by
            rw [levyKhinchinExponent_map_mul τ ha hτ.isCanonicalTriple.isCanonicalMeasure]

/-- Helper for Lemma 16.24: the affine pushforward is the composition of scaling by `a` and then
translating by `d`. -/
lemma map_affine_measure_eq_map_map (μ : Measure ℝ) {a d : ℝ} :
    ((μ.map (fun x : ℝ ↦ a * x)).map (fun x : ℝ ↦ x + d)) =
      μ.map (fun x : ℝ ↦ a * x + d) := by
  -- Proof comment: `x ↦ a * x + d` is literally the composition of `x ↦ a * x` with the
  -- translation `x ↦ x + d`.
  simpa [Function.comp_def] using
    (Measure.map_map
      (μ := μ)
      (g := fun x : ℝ ↦ x + d)
      (f := fun x : ℝ ↦ a * x)
      (by fun_prop)
      (by fun_prop))

-- Proof sketch: first prove the scale-only representation, then translate it, and finally
-- rewrite the composed pushforward to the single affine map.
/-- Lemma 16.24 (2): if a probability law on `ℝ` has Lévy--Khinchin triple `(σ², b, ν)`, then the
affine image law of `a X + d` for `a > 0` has Lévy--Khinchin triple
`(a² σ², a b + d + a ∫ ((1_{|x| < 1 / a} - 1_{|x| < 1}) x) dν, ν ∘ m_a⁻¹)`. -/
theorem map_affine_hasLevyKhinchinRepresentation
    (μ : ProbabilityMeasure ℝ) (τ : LevyKhinchinTriple)
    (hτ : HasLevyKhinchinRepresentation μ τ) {a d : ℝ} (ha : 0 < a) :
    HasLevyKhinchinRepresentation
      (μ.map (measurable_affineMap a d).aemeasurable)
      { sigma2 := a ^ (2 : ℕ) * τ.sigma2
        b := a * τ.b + d +
          a * ∫ x : ℝ, ((if |x| < 1 / a then x else 0) - (if |x| < 1 then x else 0)) ∂τ.ν
        ν := Measure.map (fun x : ℝ ↦ a * x) τ.ν } := by
  -- Route correction: package the scale and translation steps as separate representation lemmas,
  -- then rewrite the composed pushforward back to the target affine image.
  have hscale :
      HasLevyKhinchinRepresentation
        (μ.map (measurable_affineMap a 0).aemeasurable)
        { sigma2 := a ^ (2 : ℕ) * τ.sigma2
          b := a * τ.b +
            a * ∫ x : ℝ, ((if |x| < 1 / a then x else 0) - (if |x| < 1 then x else 0)) ∂τ.ν
          ν := Measure.map (fun x : ℝ ↦ a * x) τ.ν } :=
    map_mul_hasLevyKhinchinRepresentation μ τ hτ ha
  have htranslate :
      HasLevyKhinchinRepresentation
        ((μ.map (measurable_affineMap a 0).aemeasurable).map
          (measurable_affineMap 1 d).aemeasurable)
        { sigma2 := a ^ (2 : ℕ) * τ.sigma2
          b := (a * τ.b +
              a * ∫ x : ℝ, ((if |x| < 1 / a then x else 0) - (if |x| < 1 then x else 0)) ∂τ.ν) + d
          ν := Measure.map (fun x : ℝ ↦ a * x) τ.ν } :=
    map_add_const_hasLevyKhinchinRepresentation
      (μ := μ.map (measurable_affineMap a 0).aemeasurable)
      (τ := { sigma2 := a ^ (2 : ℕ) * τ.sigma2
              b := a * τ.b +
                a * ∫ x : ℝ,
                  ((if |x| < 1 / a then x else 0) - (if |x| < 1 then x else 0)) ∂τ.ν
              ν := Measure.map (fun x : ℝ ↦ a * x) τ.ν })
      hscale
      d
  have hmap :
      ((μ.map (measurable_affineMap a 0).aemeasurable).map
        (measurable_affineMap 1 d).aemeasurable) =
        μ.map (measurable_affineMap a d).aemeasurable := by
    -- Proof comment: identify the composed probability-measure pushforward with the single
    -- affine pushforward by comparing the underlying measures.
    apply ProbabilityMeasure.toMeasure_injective
    rw [ProbabilityMeasure.toMeasure_map, ProbabilityMeasure.toMeasure_map,
      ProbabilityMeasure.toMeasure_map]
    simp [map_affine_measure_eq_map_map]
  -- Proof comment: after rewriting the pushforward, only a harmless reordering of the drift term
  -- remains.
  rw [hmap] at htranslate
  simpa [add_assoc, add_left_comm, add_comm] using htranslate

end MeasureTheory.ProbabilityMeasure
