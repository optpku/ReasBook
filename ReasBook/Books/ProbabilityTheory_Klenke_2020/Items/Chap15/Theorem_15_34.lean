/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib.MeasureTheory.Measure.CharacteristicFunction.TaylorExpansion
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.Algebra.Group.ForwardDiff

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology fwdDiff

noncomputable section

/-- Helper for Theorem 15.34: `HasIteratedDerivNeighborhoodAt f n x` encodes the classical
one-variable meaning that `f` is `n`-times differentiable at `x`: the lower iterated derivatives
exist on an interval around `x`, and the top iterated derivative exists at `x`. -/
def HasIteratedDerivNeighborhoodAt (f : ℝ → ℂ) : ℕ → ℝ → Prop
  | 0, _ => True
  | n + 1, x =>
      ∃ ε > 0,
        (∀ k, k + 1 < n + 1 →
          DifferentiableOn ℝ (iteratedDeriv k f) (Set.Ioo (x - ε) (x + ε))) ∧
        DifferentiableAt ℝ (iteratedDeriv n f) x

-- Semantic recall note: `lean_leansearch` timed out on the Taylor-remainder query, so this file
-- keeps the verified local neighborhood differentiability predicate already used by the theorem.

/-- Helper for Theorem 15.34: the oscillatory phase `x ↦ exp(t * x * I)` is integrable against a
probability measure because it has constant norm `1`. -/
private lemma charFunPhaseIntegrable
    {μ : Measure ℝ} [IsProbabilityMeasure μ] (t : ℝ) :
    Integrable (fun x : ℝ ↦ Complex.exp (t * x * Complex.I)) μ := by
  -- Proof comment: dominate the complex exponential by the integrable constant-one function on the
  -- probability space.
  exact (integrable_const (1 : ℝ)).mono
    (by fun_prop)
    (Filter.Eventually.of_forall fun x ↦ by
      simpa [mul_assoc] using (Complex.norm_exp_ofReal_mul_I (t * x)).le)

/-- Helper for Theorem 15.34: the real part of the characteristic function is the cosine
transform of the law. -/
private lemma reCharFun_eq_integral_cos
    {μ : Measure ℝ} [IsProbabilityMeasure μ] (t : ℝ) :
    Complex.re (charFun μ t) = ∫ x, Real.cos (t * x) ∂μ := by
  -- Proof comment: rewrite `charFun` as the oscillatory integral and then pass the real part
  -- through the integral.
  rw [MeasureTheory.charFun_apply_real]
  calc
    Complex.re (∫ x : ℝ, Complex.exp (t * x * Complex.I) ∂μ)
      = ∫ x : ℝ, Complex.re (Complex.exp (t * x * Complex.I)) ∂μ := by
          simpa using
            (integral_re (charFunPhaseIntegrable t)).symm
    _ = ∫ x, Real.cos (t * x) ∂μ := by
          refine integral_congr_ae ?_
          filter_upwards with x
          simpa [mul_assoc] using Complex.exp_ofReal_mul_I_re (t * x)

/-- Helper for Theorem 15.34: `t ↦ Re (charFun μ t)` is an even function. -/
private lemma reCharFun_neg
    {μ : Measure ℝ} [IsProbabilityMeasure μ] (t : ℝ) :
    Complex.re (charFun μ (-t)) = Complex.re (charFun μ t) := by
  -- Proof comment: `charFun μ (-t)` is the complex conjugate of `charFun μ t`, and the real part
  -- is invariant under conjugation.
  rw [MeasureTheory.charFun_neg]
  simp

/-- Helper for Theorem 15.34: an even real-valued function has vanishing odd iterated derivatives
at `0`. -/
private lemma oddIteratedDeriv_zero_of_even
    {f : ℝ → ℝ} (hf : ∀ t : ℝ, f (-t) = f t) {m : ℕ} (hm : Odd m) :
    iteratedDeriv m f 0 = 0 := by
  obtain ⟨k, rfl⟩ := hm
  have hcomp := iteratedDeriv_comp_neg (2 * k + 1) f 0
  -- Proof comment: composing an even function with negation does not change the function, so the
  -- odd iterated derivative must equal its own negative.
  have heq :
      iteratedDeriv (2 * k + 1) f 0 = (-1 : ℝ) ^ (2 * k + 1) * iteratedDeriv (2 * k + 1) f 0 := by
    simpa [smul_eq_mul, hf] using hcomp
  have hsign : (-1 : ℝ) ^ (2 * k + 1) = -1 := by
    rw [pow_add, pow_mul]
    norm_num
  rw [hsign] at heq
  linarith

/-- Helper for Theorem 15.34: the normalized cosine remainder whose pointwise limit at `0`
produces the even moment kernel. -/
private def evenMomentKernel (n : ℕ) (x : ℝ) : ℝ :=
  if x = 0 then
    1
  else
    ((-1 : ℝ) ^ (n + 1) * ((2 * (n + 1)).factorial : ℝ) / x ^ (2 * (n + 1))) *
      (Real.cos x -
        Finset.sum (Finset.range (n + 1)) fun k ↦
          (-1 : ℝ) ^ k * x ^ (2 * k) / (((2 * k).factorial : ℕ) : ℝ))

/-- Helper for Theorem 15.34: the kernel is normalized to equal `1` at the origin. -/
private lemma evenMomentKernel_zero (n : ℕ) :
    evenMomentKernel n 0 = 1 := by
  -- Proof comment: this is the definition branch used to avoid the removable singularity at `0`.
  simp [evenMomentKernel]

/-- Helper for Theorem 15.34: away from `0`, the kernel is exactly the normalized cosine
remainder. -/
private lemma evenMomentKernel_eq_of_ne_zero
    (n : ℕ) {x : ℝ} (hx : x ≠ 0) :
    evenMomentKernel n x =
      ((-1 : ℝ) ^ (n + 1) * ((2 * (n + 1)).factorial : ℝ) / x ^ (2 * (n + 1))) *
        (Real.cos x -
          Finset.sum (Finset.range (n + 1)) fun k ↦
            (-1 : ℝ) ^ k * x ^ (2 * k) / (((2 * k).factorial : ℕ) : ℝ)) := by
  -- Proof comment: on the nonzero branch, the kernel is just its defining normalization formula.
  simp [evenMomentKernel, hx]

/-- Helper for Theorem 15.34: multiplying the kernel by the full scaled even power removes its
denominator and leaves the cosine remainder. -/
private lemma evenMomentKernel_mul_pow_eq_cosRemainder
    (n : ℕ) (t x : ℝ) :
    evenMomentKernel n (t * x) * (t * x) ^ (2 * (n + 1)) =
      ((-1 : ℝ) ^ (n + 1) * ((2 * (n + 1)).factorial : ℝ)) *
        (Real.cos (t * x) -
          Finset.sum (Finset.range (n + 1)) fun k ↦
            (-1 : ℝ) ^ k * (t * x) ^ (2 * k) / (((2 * k).factorial : ℕ) : ℝ)) := by
  by_cases htx : t * x = 0
  · -- Proof comment: at the origin branch the cosine remainder itself vanishes.
    rw [htx, evenMomentKernel_zero]
    have hsum :
        Finset.sum (Finset.range (n + 1)) (fun k ↦
            (-1 : ℝ) ^ k * (0 : ℝ) ^ (2 * k) / (((2 * k).factorial : ℕ) : ℝ)) = 1 := by
      rw [Finset.sum_eq_single 0]
      · simp
      · intro k hk hk0
        have hkne : 2 * k ≠ 0 := Nat.mul_ne_zero (by decide) hk0
        simp [hkne]
      · simp
    have hrem :
        Real.cos (0 : ℝ) -
            Finset.sum (Finset.range (n + 1)) (fun k ↦
              (-1 : ℝ) ^ k * (0 : ℝ) ^ (2 * k) / (((2 * k).factorial : ℕ) : ℝ)) = 0 := by
      simp [hsum]
    rw [hrem]
    simp
  · -- Proof comment: on the nonzero branch, one cancellation removes the denominator exactly.
    rw [evenMomentKernel_eq_of_ne_zero n htx]
    have hpow : (t * x) ^ (2 * (n + 1)) ≠ 0 := pow_ne_zero _ htx
    field_simp [hpow]

/-- Helper for Theorem 15.34: a finite even moment puts the identity random variable in the
matching `L^(2n+2)` space. -/
private lemma evenPower_memLp_of_integrable
    {μ : Measure ℝ} [IsProbabilityMeasure μ] (n : ℕ)
    (hInt : Integrable (fun x : ℝ ↦ x ^ (2 * (n + 1))) μ) :
    MemLp id (2 * (n + 1) : ℕ) μ := by
  -- Proof comment: replace the even power by the corresponding absolute power, then invoke the
  -- standard `Integrable ‖f‖^p ↔ MemLp f p` criterion on `id`.
  have hIntAbs : Integrable (fun x : ℝ ↦ |x| ^ (2 * (n + 1) : ℕ)) μ := by
    convert hInt using 1 with x
    simp [pow_mul]
  have hIntNorm :
      Integrable (fun x : ℝ ↦ ‖id x‖ ^ (((2 * (n + 1) : ℕ) : ENNReal).toReal)) μ := by
    convert hIntAbs using 1
    ext x
    rw [show ‖id x‖ = |x| by simp]
    rw [ENNReal.toReal_natCast, Real.rpow_natCast]
  have hMemLp :
      Integrable (fun x : ℝ ↦ ‖id x‖ ^ (((2 * (n + 1) : ℕ) : ENNReal).toReal)) μ ↔
        MemLp id (2 * (n + 1) : ℕ) μ :=
    MeasureTheory.integrable_norm_rpow_iff
      (by fun_prop) (by positivity) ENNReal.ofNat_ne_top
  exact hMemLp.1 hIntNorm

/-- Helper for Theorem 15.34: once the `2n+2`nd moment is integrable, mathlib's characteristic
function derivative formula gives the textbook identity. -/
private lemma evenMoment_formula_of_integrable
    {μ : Measure ℝ} [IsProbabilityMeasure μ] (n : ℕ)
    (hInt : Integrable (fun x : ℝ ↦ x ^ (2 * (n + 1))) μ) :
    ((∫ x, x ^ (2 * (n + 1)) ∂μ : ℝ) : ℂ) =
      (-1 : ℂ) ^ (n + 1) * iteratedDeriv (2 * (n + 1)) (charFun μ) 0 := by
  -- Proof comment: convert the moment bound to `MemLp`, rewrite the zero-derivative formula, and
  -- cancel the sign `(-1)^(n+1)` using that it squares to `1`.
  have hmem : MemLp id (2 * (n + 1) : ℕ) μ := evenPower_memLp_of_integrable n hInt
  have hderiv :
      iteratedDeriv (2 * (n + 1)) (charFun μ) 0 =
        Complex.I ^ (2 * (n + 1)) * ((∫ x, x ^ (2 * (n + 1)) ∂μ : ℝ) : ℂ) :=
    MeasureTheory.iteratedDeriv_charFun_zero hmem
  have hchar :
      iteratedDeriv (2 * (n + 1)) (charFun μ) 0 =
        (-1 : ℂ) ^ (n + 1) * ((∫ x, x ^ (2 * (n + 1)) ∂μ : ℝ) : ℂ) := by
    -- Proof comment: `I^(2m)` collapses to `(-1)^m`.
    calc
      iteratedDeriv (2 * (n + 1)) (charFun μ) 0
          = Complex.I ^ (2 * (n + 1)) * ((∫ x, x ^ (2 * (n + 1)) ∂μ : ℝ) : ℂ) := by
              simpa using hderiv
      _ = (-1 : ℂ) ^ (n + 1) * ((∫ x, x ^ (2 * (n + 1)) ∂μ : ℝ) : ℂ) := by
            rw [pow_mul]
            simp [Complex.I_sq]
  calc
    ((∫ x, x ^ (2 * (n + 1)) ∂μ : ℝ) : ℂ)
      = (-1 : ℂ) ^ (n + 1) * (((-1 : ℂ) ^ (n + 1)) * ((∫ x, x ^ (2 * (n + 1)) ∂μ : ℝ) : ℂ)) := by
          rw [← mul_assoc]
          have hsign : (-1 : ℂ) ^ (n + 1) * (-1 : ℂ) ^ (n + 1) = 1 := by
            calc
              (-1 : ℂ) ^ (n + 1) * (-1 : ℂ) ^ (n + 1) = (-1 : ℂ) ^ ((n + 1) + (n + 1)) := by
                rw [← pow_add]
              _ = (-1 : ℂ) ^ (2 * (n + 1)) := by ring_nf
              _ = 1 := by simp
          rw [hsign, one_mul]
    _ = (-1 : ℂ) ^ (n + 1) * iteratedDeriv (2 * (n + 1)) (charFun μ) 0 := by
          rw [hchar]

/-- Helper for Theorem 15.34: the finite-difference kernel used in the converse moment estimate. -/
private def scaledSinEven (m : ℕ) (t x : ℝ) : ℝ :=
  ((2 * Real.sin (t * x / 2)) / t) ^ (2 * m)

/-- Helper for Theorem 15.34: each finite-difference kernel value is nonnegative. -/
private lemma scaledSinEven_nonneg (m : ℕ) (t x : ℝ) :
    0 ≤ scaledSinEven m t x := by
  -- Proof comment: the kernel is an even natural power of a real scalar.
  let a : ℝ := (2 * Real.sin (t * x / 2)) / t
  have hsq : 0 ≤ (a ^ m) ^ 2 := sq_nonneg (a ^ m)
  simpa [scaledSinEven, a, two_mul, pow_add, pow_two, mul_assoc] using hsq

/-- Helper for Theorem 15.34: for nonzero mesh, the basic oscillatory quotient is `x * sinc`. -/
private lemma scaledSinBase_eq_mul_sinc {t x : ℝ} (ht : t ≠ 0) :
    (2 * Real.sin (t * x / 2)) / t = x * Real.sinc (t * x / 2) := by
  by_cases hx : x = 0
  · -- Proof comment: when `x = 0`, both sides vanish directly.
    subst hx
    simp [Real.sinc_zero]
  · -- Proof comment: away from `x = 0`, unfold `sinc` once and clear the denominator.
    have htx : t * x / 2 ≠ 0 := by
      refine div_ne_zero ?_ (by norm_num)
      exact mul_ne_zero ht hx
    rw [Real.sinc_of_ne_zero htx]
    field_simp [ht, hx]

/-- Helper for Theorem 15.34: every finite-difference kernel is integrable on a probability
space because it is bounded by a constant depending only on the mesh. -/
private lemma scaledSinEven_integrable
    {μ : Measure ℝ} [IsProbabilityMeasure μ] (m : ℕ) (t : ℝ) :
    Integrable (fun x : ℝ ↦ scaledSinEven m t x) μ := by
  refine Integrable.of_bound ?_ ((2 / |t|) ^ (2 * m)) ?_
  · -- Proof comment: the kernel is measurable because it is built from continuous real functions.
    simpa [scaledSinEven] using
      (by
        fun_prop :
          AEStronglyMeasurable (fun x : ℝ ↦ ((2 * Real.sin (t * x / 2)) / t) ^ (2 * m)) μ)
  filter_upwards with x
  by_cases ht : t = 0
  · -- Proof comment: the degenerate mesh `t = 0` gives the zero kernel everywhere.
    subst ht
    simp [scaledSinEven]
  · -- Proof comment: `|sin| ≤ 1` bounds the quotient by `2 / |t|`, and monotonicity of
    -- nonnegative powers transfers the bound to the kernel.
    have hsin :
        2 * |Real.sin (t * x / 2)| ≤ 2 := by
      nlinarith [Real.abs_sin_le_one (t * x / 2)]
    have habs :
        |(2 * Real.sin (t * x / 2)) / t| ≤ 2 / |t| := by
      calc
        |(2 * Real.sin (t * x / 2)) / t|
            = (2 * |Real.sin (t * x / 2)|) / |t| := by
                rw [abs_div, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
        _ ≤ 2 / |t| := by
              exact div_le_div_of_nonneg_right hsin (abs_pos.mpr ht).le
    calc
      ‖scaledSinEven m t x‖ = |((2 * Real.sin (t * x / 2)) / t) ^ (2 * m)| := by
        rw [Real.norm_eq_abs, scaledSinEven]
      _ = |(2 * Real.sin (t * x / 2)) / t| ^ (2 * m) := by
        rw [abs_pow]
      _ ≤ (2 / |t|) ^ (2 * m) := by
        exact pow_le_pow_left₀ (abs_nonneg _) habs (2 * m)

/-- Helper for Theorem 15.34: along the standard reciprocal mesh, the finite-difference kernel
converges pointwise to the even power. -/
private lemma scaledSinEven_pointwise_tendsto_evenPower (m : ℕ) (x : ℝ) :
    Tendsto (fun j : ℕ ↦ scaledSinEven m (((j + 1 : ℝ))⁻¹) x) atTop (𝓝 (x ^ (2 * m))) := by
  let tSeq : ℕ → ℝ := fun j ↦ ((j + 1 : ℝ))⁻¹
  have hseq_eq :
      (fun j : ℕ ↦ scaledSinEven m (tSeq j) x) =
        fun j : ℕ ↦ (x * Real.sinc (tSeq j * x / 2)) ^ (2 * m) := by
    funext j
    -- Proof comment: every reciprocal mesh point is nonzero, so the `sinc` normalization applies.
    have ht : tSeq j ≠ 0 := by
      dsimp [tSeq]
      positivity
    simpa [scaledSinEven] using
      congrArg (fun y : ℝ ↦ y ^ (2 * m)) (scaledSinBase_eq_mul_sinc ht)
  have htSeq_zero : Tendsto tSeq atTop (𝓝 0) := by
    -- Proof comment: the reciprocal mesh tends to the origin.
    simpa [tSeq, one_div] using
      (tendsto_one_div_add_atTop_nhds_zero_nat :
        Tendsto (fun n : ℕ ↦ 1 / ((n : ℝ) + 1)) atTop (𝓝 (0 : ℝ)))
  have hsinc :
      Tendsto (fun j : ℕ ↦ Real.sinc (tSeq j * x / 2)) atTop (𝓝 1) := by
    -- Proof comment: `sinc` is continuous at `0`, and the mesh-scaled argument tends to `0`.
    have harg : Tendsto (fun j : ℕ ↦ tSeq j * x / 2) atTop (𝓝 0) := by
      have hcont : Continuous fun t : ℝ ↦ t * x / 2 := by
        fun_prop
      have hcontAt : ContinuousAt (fun t : ℝ ↦ t * x / 2) 0 := hcont.continuousAt
      simpa using hcontAt.tendsto.comp htSeq_zero
    have hsincContAt : ContinuousAt Real.sinc 0 := Real.continuous_sinc.continuousAt
    simpa [Real.sinc_zero] using hsincContAt.tendsto.comp harg
  have hbase :
      Tendsto (fun j : ℕ ↦ x * Real.sinc (tSeq j * x / 2)) atTop (𝓝 x) := by
    -- Proof comment: the `sinc` factor tends to `1`, so the product tends to `x`.
    simpa using tendsto_const_nhds.mul hsinc
  have hpow :
      Tendsto (fun j : ℕ ↦ (x * Real.sinc (tSeq j * x / 2)) ^ (2 * m)) atTop
        (𝓝 (x ^ (2 * m))) := by
    -- Proof comment: taking a fixed natural power is continuous.
    have hcont : Continuous fun y : ℝ ↦ y ^ (2 * m) := by
      fun_prop
    have hcontAt : ContinuousAt (fun y : ℝ ↦ y ^ (2 * m)) x := hcont.continuousAt
    simpa using hcontAt.tendsto.comp hbase
  rw [hseq_eq]
  exact hpow

/-- Helper for Theorem 15.34: the centered exponential increment collapses to the sine factor
after multiplying by the half-phase. -/
private lemma exp_neg_half_mul_exp_sub_one_eq_two_sin_mul_I (a : ℝ) :
    Complex.exp (-(a / 2) * Complex.I) * (Complex.exp (a * Complex.I) - 1) =
      (((2 * Real.sin (a / 2) : ℝ) : ℂ) * Complex.I) := by
  -- Proof comment: rewrite the left-hand side as the classical difference
  -- `exp((a / 2) I) - exp(-(a / 2) I)` and then expand both exponentials trigonometrically.
  calc
    Complex.exp (-(a / 2) * Complex.I) * (Complex.exp (a * Complex.I) - 1)
        = Complex.exp ((a / 2) * Complex.I) - Complex.exp (-(a / 2) * Complex.I) := by
            rw [mul_sub]
            have hmul :
                Complex.exp (-(a / 2) * Complex.I) * Complex.exp (a * Complex.I) =
                  Complex.exp ((a / 2) * Complex.I) := by
              rw [← Complex.exp_add]
              ring_nf
            rw [hmul]
            simp
    _ = (Complex.cos (a / 2) + Complex.sin (a / 2) * Complex.I) -
          (Complex.cos (a / 2) - Complex.sin (a / 2) * Complex.I) := by
            rw [Complex.cos_add_sin_I, Complex.cos_sub_sin_I]
    _ = 2 * (Complex.sin (a / 2) * Complex.I) := by
          ring
    _ = 2 * (((Real.sin (a / 2) : ℝ) : ℂ) * Complex.I) := by
          norm_cast
    _ = (((2 * Real.sin (a / 2) : ℝ) : ℂ) * Complex.I) := by
          calc
            2 * (((Real.sin (a / 2) : ℝ) : ℂ) * Complex.I)
                = (((2 : ℂ) * (((Real.sin (a / 2) : ℝ) : ℂ))) * Complex.I) := by
                    ring
            _ = (((2 * Real.sin (a / 2) : ℝ) : ℂ) * Complex.I) := by
                  norm_num

/-- Helper for Theorem 15.34: the oscillatory phase `s ↦ exp (s x I)` is an additive character,
so forward differences reduce to powers of the basic increment. -/
private def expPhaseAddChar (x : ℝ) : AddChar ℝ ℂ where
  toFun := fun s ↦ Complex.exp (s * x * Complex.I)
  map_zero_eq_one' := by
    -- Proof comment: the phase at `0` is the unit of the multiplicative character.
    simp
  map_add_eq_mul' a b := by
    -- Proof comment: the exponent is additive in the shift variable, so `exp` turns it into a
    -- product.
    have h :
        ((a + b : ℝ) : ℂ) * (x : ℂ) * Complex.I =
          (a : ℂ) * (x : ℂ) * Complex.I + (b : ℂ) * (x : ℂ) * Complex.I := by
      norm_num [add_mul, mul_add, mul_assoc]
    rw [h, Complex.exp_add]

/-- Helper for Theorem 15.34: the complexified finite-difference kernel is a scaled forward
difference of the oscillatory phase `s ↦ exp (s x I)`. -/
private lemma scaledSinEven_complex_eq_shiftedFwdDiffPhase
    (m : ℕ) {t : ℝ} (ht : t ≠ 0) (x : ℝ) :
    (((scaledSinEven m t x : ℝ) : ℂ)) =
      ((-1 : ℂ) ^ m / (t : ℂ) ^ (2 * m)) *
        ((Nat.iterate (fwdDiff t) (2 * m)
            (fun s : ℝ ↦ Complex.exp (s * x * Complex.I))) (-(m : ℝ) * t)) := by
  -- Proof comment: first turn the centered forward difference into a power of the basic phase
  -- increment using the additive-character API.
  have hiter :
      ((Nat.iterate (fwdDiff t) (2 * m)
          (fun s : ℝ ↦ Complex.exp (s * x * Complex.I))) (-(m : ℝ) * t)) =
        (Complex.exp (t * x * Complex.I) - 1) ^ (2 * m) * Complex.exp (-(m : ℝ) * t * x * Complex.I) := by
    simpa [expPhaseAddChar] using
      (fwdDiff_addChar_eq (h := t) (φ := expPhaseAddChar x) (x := -(m : ℝ) * t) (n := 2 * m))
  let a : ℝ := t * x
  -- Proof comment: next absorb the centering phase into the even power using the half-phase sine
  -- identity.
  have hphase :
      Complex.exp (-(a / 2) * Complex.I) ^ (2 * m) * (Complex.exp (a * Complex.I) - 1) ^ (2 * m) =
        ((((2 * Real.sin (a / 2) : ℝ) : ℂ) * Complex.I) ^ (2 * m)) := by
    simpa [mul_pow] using congrArg (fun z : ℂ ↦ z ^ (2 * m))
      (exp_neg_half_mul_exp_sub_one_eq_two_sin_mul_I a)
  have hphasepow :
      (Complex.exp (a * Complex.I) - 1) ^ (2 * m) * Complex.exp (-(m : ℝ) * a * Complex.I) =
        ((((2 * Real.sin (a / 2) : ℝ) : ℂ) * Complex.I) ^ (2 * m)) := by
    have hexp :
        Complex.exp (-(a / 2) * Complex.I) ^ (2 * m) = Complex.exp (-(m : ℝ) * a * Complex.I) := by
      -- Proof comment: raising the half-phase to the even power reproduces the centered shift.
      calc
        Complex.exp (-(a / 2) * Complex.I) ^ (2 * m)
            = Complex.exp (((2 * m : ℕ) : ℂ) * (-(a / 2) * Complex.I)) := by
                rw [← Complex.exp_nat_mul]
        _ = Complex.exp (-(m : ℝ) * a * Complex.I) := by
              congr 1
              apply Complex.ext <;> simp [mul_assoc]
              ring
    rw [hexp, mul_comm] at hphase
    exact hphase
  have htC : (t : ℂ) ≠ 0 := by
    exact_mod_cast ht
  have htpow : (t : ℂ) ^ (2 * m) ≠ 0 := pow_ne_zero _ htC
  have hI : Complex.I ^ (2 * m) = (-1 : ℂ) ^ m := by
    rw [pow_mul]
    simp [Complex.I_sq]
  -- Proof comment: finally divide out the mesh power and use that the even power of `I`
  -- contributes exactly the sign `(-1)^m`.
  calc
    (((scaledSinEven m t x : ℝ) : ℂ))
      = (((((2 * Real.sin (a / 2)) / t) ^ (2 * m) : ℝ)) : ℂ) := by
          simp [scaledSinEven, a]
    _ = ((((2 * Real.sin (a / 2) : ℝ) : ℂ) / (t : ℂ)) ^ (2 * m)) := by
          simp [div_eq_mul_inv]
    _ = ((((2 * Real.sin (a / 2) : ℝ) : ℂ) ^ (2 * m)) / (t : ℂ) ^ (2 * m)) := by
          rw [div_pow]
    _ = ((-1 : ℂ) ^ m / (t : ℂ) ^ (2 * m)) *
          ((((2 * Real.sin (a / 2) : ℝ) : ℂ) * Complex.I) ^ (2 * m)) := by
          rw [mul_pow, hI]
          field_simp [htpow]
          ring_nf
          have hsign : (-1 : ℂ) ^ (m * 2) = 1 := by
            simp
          rw [hsign, mul_one]
    _ = ((-1 : ℂ) ^ m / (t : ℂ) ^ (2 * m)) *
          ((Complex.exp (a * Complex.I) - 1) ^ (2 * m) * Complex.exp (-(m : ℝ) * a * Complex.I)) := by
          rw [hphasepow]
    _ = ((-1 : ℂ) ^ m / (t : ℂ) ^ (2 * m)) *
          ((Nat.iterate (fwdDiff t) (2 * m)
            (fun s : ℝ ↦ Complex.exp (s * x * Complex.I))) (-(m : ℝ) * t)) := by
          rw [hiter]
          congr 1
          simp [a, mul_assoc]

/-- Helper for Theorem 15.34: the iterated forward difference of the characteristic function is
the integral of the iterated forward difference of the oscillatory phase. -/
private lemma fwdDiff_iter_charFun_eq_integral_phase
    {μ : Measure ℝ} [IsProbabilityMeasure μ] (n : ℕ) (t y : ℝ) :
    (Nat.iterate (fwdDiff t) n (charFun μ)) y =
      ∫ x : ℝ,
        (Nat.iterate (fwdDiff t) n
          (fun s : ℝ ↦ Complex.exp (s * x * Complex.I))) y ∂μ := by
  -- Proof comment: expand both forward differences into the same finite Gregory-Newton sum.
  rw [fwdDiff_iter_eq_sum_shift]
  simp_rw [fwdDiff_iter_eq_sum_shift]
  rw [MeasureTheory.integral_finset_sum]
  · congr 1 with k
    -- Proof comment: each summand is just the characteristic-function integral at the shifted
    -- mesh point, with the integer coefficient pulled through the integral.
    rw [MeasureTheory.charFun_apply_real]
    symm
    simpa [zsmul_eq_mul, mul_assoc] using
      (MeasureTheory.integral_const_mul ((((-1 : ℤ) ^ (n - k) * n.choose k : ℤ) : ℂ))
        (fun a : ℝ ↦ Complex.exp ((y + k • t) * a * Complex.I)) (μ := μ))
  · intro i hi
    -- Proof comment: each shifted phase remains integrable because it still has constant norm
    -- `1`.
    simpa [zsmul_eq_mul] using
      (charFunPhaseIntegrable (μ := μ) (y + i • t)).const_mul
        (((((-1 : ℤ) ^ (n - i) * n.choose i : ℤ) : ℂ)))

/-- Helper for Theorem 15.34: integrating the nonnegative kernel is the same as evaluating the
matching shifted forward difference of the characteristic function. -/
private lemma scaledSinEvenIntegral_eq_shiftedFwdDiff_charFun
    {μ : Measure ℝ} [IsProbabilityMeasure μ] (m : ℕ) {t : ℝ} (ht : t ≠ 0) :
    ((∫ x, scaledSinEven m t x ∂μ : ℝ) : ℂ) =
      ((-1 : ℂ) ^ m / (t : ℂ) ^ (2 * m)) *
        ((Nat.iterate (fwdDiff t) (2 * m) (charFun μ))
          (-(m : ℝ) * t)) := by
  -- Proof comment: rewrite the real integral as a complex integral, then substitute the pointwise
  -- phase identity from the previous lemma.
  calc
    ((∫ x, scaledSinEven m t x ∂μ : ℝ) : ℂ)
      = ∫ x, ((scaledSinEven m t x : ℝ) : ℂ) ∂μ := by
          simpa using (integral_ofReal (f := fun x : ℝ ↦ scaledSinEven m t x) (μ := μ)).symm
    _ = ∫ x,
          ((-1 : ℂ) ^ m / (t : ℂ) ^ (2 * m)) *
            ((Nat.iterate (fwdDiff t) (2 * m)
              (fun s : ℝ ↦ Complex.exp (s * x * Complex.I))) (-(m : ℝ) * t)) ∂μ := by
          refine integral_congr_ae ?_
          filter_upwards with x
          simpa using scaledSinEven_complex_eq_shiftedFwdDiffPhase m ht x
    _ = ((-1 : ℂ) ^ m / (t : ℂ) ^ (2 * m)) *
          ∫ x,
            ((Nat.iterate (fwdDiff t) (2 * m)
              (fun s : ℝ ↦ Complex.exp (s * x * Complex.I))) (-(m : ℝ) * t)) ∂μ := by
            simpa [mul_assoc] using
              (MeasureTheory.integral_const_mul
                (((-1 : ℂ) ^ m / (t : ℂ) ^ (2 * m)))
                (fun x : ℝ ↦
                  ((Nat.iterate (fwdDiff t) (2 * m)
                    (fun s : ℝ ↦ Complex.exp (s * x * Complex.I))) (-(m : ℝ) * t)))
                (μ := μ))
    _ = ((-1 : ℂ) ^ m / (t : ℂ) ^ (2 * m)) *
          ((Nat.iterate (fwdDiff t) (2 * m) (charFun μ))
            (-(m : ℝ) * t)) := by
            congr 1
            exact (fwdDiff_iter_charFun_eq_integral_phase (μ := μ) (2 * m) t (-(m : ℝ) * t)).symm

/-- Helper for Theorem 15.34: the real kernel integral is the real part of the corresponding
shifted forward-difference quotient for `charFun`. -/
private lemma scaledSinEvenIntegral_eq_re_shiftedFwdDiff_charFun
    {μ : Measure ℝ} [IsProbabilityMeasure μ] (m : ℕ) {t : ℝ} (ht : t ≠ 0) :
    ∫ x, scaledSinEven m t x ∂μ =
      Complex.re
        (((-1 : ℂ) ^ m / (t : ℂ) ^ (2 * m)) *
          ((Nat.iterate (fwdDiff t) (2 * m) (charFun μ))
            (-(m : ℝ) * t))) := by
  -- Proof comment: the previous complex identity has a real-valued left side, so projecting to
  -- the real part gives the claimed scalar bridge.
  have h :=
    congrArg Complex.re (scaledSinEvenIntegral_eq_shiftedFwdDiff_charFun (μ := μ) m ht)
  simpa using h

/-- Helper for Theorem 15.34: taking real parts commutes with iterated forward differences of a
complex-valued function. -/
private lemma re_fwdDiffIter
    (n : ℕ) (t y : ℝ) (f : ℝ → ℂ) :
    Complex.re ((Nat.iterate (fwdDiff t) n f) y) =
      (Nat.iterate (fwdDiff t) n (fun s : ℝ ↦ Complex.re (f s))) y := by
  induction n generalizing f y with
  | zero =>
      rfl
  | succ n ih =>
      -- Proof comment: apply the induction hypothesis to the one-step forward difference and then
      -- simplify the real-part projection through that outer difference.
      simpa [Function.iterate_succ_apply, fwdDiff] using ih y (fwdDiff t f)

/-- Helper for Theorem 15.34: rewrite the kernel integral as a purely real centered
forward-difference quotient of `t ↦ Re (charFun μ t)`. -/
private lemma scaledSinEvenIntegral_eq_shiftedFwdDiff_reCharFun
    {μ : Measure ℝ} [IsProbabilityMeasure μ] (m : ℕ) {t : ℝ} (ht : t ≠ 0) :
    ∫ x, scaledSinEven m t x ∂μ =
      ((-1 : ℝ) ^ m / t ^ (2 * m)) *
        ((Nat.iterate (fwdDiff t) (2 * m) (fun s : ℝ ↦ Complex.re (charFun μ s)))
          (-(m : ℝ) * t)) := by
  have hbase := scaledSinEvenIntegral_eq_re_shiftedFwdDiff_charFun (μ := μ) m ht
  have hfactor :
      ((-1 : ℂ) ^ m / (t : ℂ) ^ (2 * m)) =
        ((((-1 : ℝ) ^ m / t ^ (2 * m) : ℝ)) : ℂ) := by
    -- Proof comment: the prefactor is real because both the sign and the even mesh power are
    -- real scalars.
    simp [ht]
  calc
    ∫ x, scaledSinEven m t x ∂μ
      = Complex.re
          (((-1 : ℂ) ^ m / (t : ℂ) ^ (2 * m)) *
            ((Nat.iterate (fwdDiff t) (2 * m) (charFun μ))
              (-(m : ℝ) * t))) := hbase
    _ = ((-1 : ℝ) ^ m / t ^ (2 * m)) *
          Complex.re
            (((Nat.iterate (fwdDiff t) (2 * m) (charFun μ))
              (-(m : ℝ) * t))) := by
            rw [hfactor, Complex.re_ofReal_mul]
    _ = ((-1 : ℝ) ^ m / t ^ (2 * m)) *
          ((Nat.iterate (fwdDiff t) (2 * m) (fun s : ℝ ↦ Complex.re (charFun μ s)))
            (-(m : ℝ) * t)) := by
            rw [re_fwdDiffIter]

/-- Helper for Theorem 15.34: every reciprocal-mesh point used in the kernel approximation is
nonzero. -/
private lemma reciprocalMesh_ne_zero (j : ℕ) :
    (((j + 1 : ℝ))⁻¹) ≠ 0 := by
  -- Proof comment: the reciprocal mesh only samples positive real numbers.
  positivity

/-- Helper for Theorem 15.34: the shifted binomial coefficients annihilate lower-degree powers and
pick out the top-degree factorial coefficient. -/
private lemma shiftedBinomialPowSum (m r : ℕ) (hr : r ≤ 2 * m) :
    (∑ k ∈ Finset.range (2 * m + 1),
        ((((-1 : ℤ) ^ (2 * m - k) * (2 * m).choose k : ℤ) : ℂ) * ((k : ℂ) - m) ^ r)) =
      if r = 2 * m then (((2 * m).factorial : ℕ) : ℂ) else 0 := by
  have hsum :
      (∑ k ∈ Finset.range (2 * m + 1),
          ((((-1 : ℤ) ^ (2 * m - k) * (2 * m).choose k : ℤ) : ℂ) * ((k : ℂ) - m) ^ r)) =
        (Nat.iterate (fwdDiff (1 : ℂ)) (2 * m) (fun z : ℂ ↦ z ^ r)) (-(m : ℂ)) := by
    -- Proof comment: evaluate the `2m`-fold forward difference at the centered point `-m`.
    simpa [fwdDiff_iter_eq_sum_shift, sub_eq_add_neg, add_comm, add_left_comm, add_assoc,
      zsmul_eq_mul]
  rw [hsum]
  by_cases hEq : r = 2 * m
  · -- Proof comment: in the top-degree case, the iterated forward difference is the factorial.
    subst hEq
    simpa using congrFun (fwdDiff_iter_eq_factorial (R := ℂ) (n := 2 * m)) (-(m : ℂ))
  · -- Proof comment: lower-degree powers are killed by the `2m`-fold forward difference.
    have hlt : r < 2 * m := lt_of_le_of_ne hr hEq
    simpa [hEq] using
      congrFun (fwdDiff_iter_pow_eq_zero_of_lt (R := ℂ) (j := r) (n := 2 * m) hlt) (-(m : ℂ))

/-- Helper for Theorem 15.34: after centering at `-(m : ℝ) * t`, the `2m`-fold forward difference
of the monomial `s ↦ (s : ℂ)^r` factors out the full mesh power `t^r`. -/
private lemma centeredFwdDiff_pow_scaled (m r : ℕ) {t : ℝ} :
    ((Nat.iterate (fwdDiff t) (2 * m)
        (fun s : ℝ ↦ (s : ℂ) ^ r)) (-(m : ℝ) * t)) =
      (t : ℂ) ^ r *
        ((Nat.iterate (fwdDiff (1 : ℂ)) (2 * m)
          (fun z : ℂ ↦ z ^ r)) (-(m : ℂ))) := by
  calc
    ((Nat.iterate (fwdDiff t) (2 * m) (fun s : ℝ ↦ (s : ℂ) ^ r)) (-(m : ℝ) * t))
        =
          ∑ k ∈ Finset.range (2 * m + 1),
            ((((-1 : ℤ) ^ (2 * m - k) * (2 * m).choose k : ℤ) : ℂ) *
              (((( -(m : ℝ) * t) + k • t : ℝ) : ℂ) ^ r)) := by
              simpa [fwdDiff_iter_eq_sum_shift, zsmul_eq_mul]
    _ =
          ∑ k ∈ Finset.range (2 * m + 1),
            ((((-1 : ℤ) ^ (2 * m - k) * (2 * m).choose k : ℤ) : ℂ) *
              (((t : ℂ) * ((k : ℂ) - m)) ^ r)) := by
              refine Finset.sum_congr rfl ?_
              intro k hk
              congr 1
              congr 1
              norm_num [sub_eq_add_neg, zsmul_eq_mul, mul_add, add_mul, mul_assoc, mul_comm,
                mul_left_comm, add_comm, add_left_comm, add_assoc]
    _ =
          ∑ k ∈ Finset.range (2 * m + 1),
            ((((-1 : ℤ) ^ (2 * m - k) * (2 * m).choose k : ℤ) : ℂ) *
              ((t : ℂ) ^ r * ((k : ℂ) - m) ^ r)) := by
              refine Finset.sum_congr rfl ?_
              intro k hk
              rw [mul_pow]
    _ =
          (t : ℂ) ^ r *
            ∑ k ∈ Finset.range (2 * m + 1),
              ((((-1 : ℤ) ^ (2 * m - k) * (2 * m).choose k : ℤ) : ℂ) *
                ((k : ℂ) - m) ^ r) := by
              rw [Finset.mul_sum]
              refine Finset.sum_congr rfl ?_
              intro k hk
              ring
    _ =
          (t : ℂ) ^ r *
            ((Nat.iterate (fwdDiff (1 : ℂ)) (2 * m) (fun z : ℂ ↦ z ^ r))
              (-(m : ℂ))) := by
              congr 1
              symm
              simpa [fwdDiff_iter_eq_sum_shift, sub_eq_add_neg, add_comm, add_left_comm,
                add_assoc, zsmul_eq_mul]

/-- Helper for Theorem 15.34: every derivative order strictly below the top neighborhood order is
genuinely differentiable at the center point. -/
private lemma differentiableAt_iteratedDeriv_of_hasIteratedDerivNeighborhoodAt
    {f : ℝ → ℂ} {n k : ℕ} {x : ℝ}
    (h : HasIteratedDerivNeighborhoodAt f n x) (hk : k < n) :
    DifferentiableAt ℝ (iteratedDeriv k f) x := by
  cases n with
  | zero =>
      exact (Nat.not_lt_zero _ hk).elim
  | succ n =>
      rcases h with ⟨ε, hε, hDiff, hTop⟩
      by_cases hkn : k = n
      · -- Proof comment: at the top available order, differentiability at the center is part of
        -- the neighborhood hypothesis itself.
        simpa [hkn] using hTop
      · -- Proof comment: lower orders are differentiable on a whole interval around the center,
        -- so the pointwise differentiability follows by restricting that open neighborhood.
        have hkn_lt : k < n := lt_of_le_of_ne (Nat.le_of_lt_succ hk) hkn
        have hx :
            x ∈ Set.Ioo (x - ε) (x + ε) := by
          constructor <;> linarith
        exact (hDiff k (Nat.succ_lt_succ hkn_lt) x hx).differentiableAt
          (isOpen_Ioo.mem_nhds hx)

/-- Helper for Theorem 15.34: differentiating through `Complex.re` only changes the derivative by
taking real parts. -/
private lemma deriv_re_comp_eq {g : ℝ → ℂ} {x : ℝ} (hg : DifferentiableAt ℝ g x) :
    deriv (fun y => Complex.re (g y)) x = Complex.re (deriv g x) := by
  -- Proof comment: `Complex.re` is a bounded real-linear map, so the derivative is transported by
  -- composing the one-dimensional Fréchet derivative with that linear map.
  have hcompF :
      HasFDerivAt (fun y => Complex.re (g y))
        (Complex.reCLM.comp (ContinuousLinearMap.toSpanSingleton ℝ (deriv g x))) x := by
    apply HasFDerivAt.comp x
    · exact Complex.reCLM.isBoundedLinearMap.hasFDerivAt
    · simpa [hg.hasDerivAt.deriv] using hg.hasDerivAt.hasFDerivAt
  have hcompD := hcompF.hasDerivAt
  simpa using hcompD.deriv

/-- Helper for Theorem 15.34: on an open interval where the iterated derivatives of a
complex-valued function exist, iterated derivatives commute with taking real parts. -/
private lemma iteratedDeriv_re_eq_on_open {g : ℝ → ℂ} {s : Set ℝ} (hs : IsOpen s) :
    ∀ n, (∀ k < n, DifferentiableOn ℝ (iteratedDeriv k g) s) →
      ∀ x ∈ s,
        iteratedDeriv n (fun y => Complex.re (g y)) x = Complex.re (iteratedDeriv n g x)
  | 0, _hDiff, x, hx => by
      -- Proof comment: order zero is just evaluation of the original functions.
      simp
  | n + 1, hDiff, x, hx => by
      have ih :=
        iteratedDeriv_re_eq_on_open hs n
          (fun k hk => hDiff k (Nat.lt_trans hk (Nat.lt_succ_self _)))
      have hsMem : s ∈ 𝓝 x := hs.mem_nhds hx
      have hEq :
          (fun y => iteratedDeriv n (fun z => Complex.re (g z)) y) =ᶠ[𝓝 x]
            fun y => Complex.re (iteratedDeriv n g y) := by
        -- Proof comment: the induction hypothesis holds on the whole open interval, so it
        -- upgrades to neighborhood equality at the current interior point.
        filter_upwards [hsMem] with y hy
        exact ih y hy
      rw [iteratedDeriv_succ, hEq.deriv_eq]
      have hdiffx : DifferentiableAt ℝ (iteratedDeriv n g) x := by
        -- Proof comment: the neighborhood differentiability hypothesis on `g` supplies the
        -- derivative needed to pass `Complex.re` through the final derivation step.
        exact (hDiff n (Nat.lt_succ_self _) x hx).differentiableAt hsMem
      simpa [iteratedDeriv_succ] using deriv_re_comp_eq hdiffx

/-- Helper for Theorem 15.34: dropping the first derivative from the neighborhood package
preserves the same interval for the remaining derivative chain. -/
private lemma hasIteratedDerivNeighborhoodAt_tail
    {f : ℝ → ℂ} {n : ℕ} {x : ℝ}
    (h : HasIteratedDerivNeighborhoodAt f (n + 1) x) :
    HasIteratedDerivNeighborhoodAt (iteratedDeriv 1 f) n x := by
  cases n with
  | zero =>
      trivial
  | succ n =>
      rcases h with ⟨ε, hε, hDiff, hTop⟩
      refine ⟨ε, hε, ?_, ?_⟩
      · -- Proof comment: every lower derivative statement just shifts its index by one.
        intro k hk
        simpa [iteratedDeriv_one, iteratedDeriv_succ'] using
          hDiff (k + 1) (Nat.succ_lt_succ hk)
      · -- Proof comment: the new top differentiability statement is exactly the old one with one
        -- derivative peeled off.
        simpa [iteratedDeriv_one, iteratedDeriv_succ'] using hTop

/-- Helper for Theorem 15.34: the neighborhood differentiability package can be truncated to any
smaller derivative order. -/
private lemma hasIteratedDerivNeighborhoodAt_mono
    {f : ℝ → ℂ} {n k : ℕ} {x : ℝ}
    (h : HasIteratedDerivNeighborhoodAt f n x) (hk : k ≤ n) :
    HasIteratedDerivNeighborhoodAt f k x := by
  induction k generalizing n with
  | zero =>
      trivial
  | succ k ih =>
      cases n with
      | zero =>
          exact (Nat.not_succ_le_zero _ hk).elim
      | succ n =>
          rcases h with ⟨ε, hε, hDiff, hTop⟩
          refine ⟨ε, hε, ?_, ?_⟩
          · -- Proof comment: the lower-order interval differentiability statements are inherited
            -- directly from the longer derivative chain.
            intro j hj
            exact hDiff j (lt_of_lt_of_le hj hk)
          · -- Proof comment: the new top derivative lies strictly below the original top order,
            -- so the previous companion lemma upgrades it to pointwise differentiability.
            exact
              differentiableAt_iteratedDeriv_of_hasIteratedDerivNeighborhoodAt
                (n := n + 1) (k := k) ⟨ε, hε, hDiff, hTop⟩ (Nat.lt_of_succ_le hk)

/-- Helper for Theorem 15.34: the odd derivative quotient of `u(t) = Re (charFun μ t)` tends to
its next derivative at the origin once the neighborhood derivative chain is available. -/
private lemma oddReCharFunDeriv_div_tendsto_topDeriv
    {μ : Measure ℝ} [IsProbabilityMeasure μ] (m : ℕ) (hm : 0 < m)
    (hφ : HasIteratedDerivNeighborhoodAt (charFun μ) (2 * m) 0) :
    Tendsto
      (fun s : ℝ ↦ iteratedDeriv (2 * m - 1) (fun t ↦ Complex.re (charFun μ t)) s / s)
      (𝓝[≠] 0)
      (𝓝 (iteratedDeriv (2 * m) (fun t ↦ Complex.re (charFun μ t)) 0)) := by
  rcases Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hm) with ⟨k, rfl⟩
  let u : ℝ → ℝ := fun t ↦ Complex.re (charFun μ t)
  rcases hφ with ⟨ε, hε, hDiff, hTop⟩
  have hIoo : IsOpen (Set.Ioo (0 - ε) (0 + ε)) := isOpen_Ioo
  have hMem0 : 0 ∈ Set.Ioo (0 - ε) (0 + ε) := by
    constructor <;> linarith
  have hDiffLower :
      ∀ j < 2 * k + 1, DifferentiableOn ℝ (iteratedDeriv j (charFun μ)) (Set.Ioo (0 - ε) (0 + ε)) := by
    intro j hj
    exact hDiff j (by
      have hsucc : j + 1 < (2 * k + 1) + 1 := Nat.succ_lt_succ hj
      simpa [two_mul, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hsucc)
  have hEqNear :
      (fun s : ℝ ↦ iteratedDeriv (2 * k + 1) u s) =ᶠ[𝓝 0]
        fun s : ℝ ↦ Complex.re (iteratedDeriv (2 * k + 1) (charFun μ) s) := by
    -- Proof comment: on the open interval supplied by `hφ`, iterated derivatives commute with
    -- taking real parts.
    filter_upwards [hIoo.mem_nhds hMem0] with s hs
    simpa [u] using
      iteratedDeriv_re_eq_on_open hIoo (2 * k + 1) hDiffLower s hs
  have hDiffAt :
      DifferentiableAt ℝ (iteratedDeriv (2 * k + 1) (charFun μ)) 0 := by
    -- Proof comment: the neighborhood package makes the top odd iterated derivative genuinely
    -- differentiable at the center.
    exact
      differentiableAt_iteratedDeriv_of_hasIteratedDerivNeighborhoodAt
        (n := 2 * (k + 1)) (k := 2 * k + 1) ⟨ε, hε, hDiff, hTop⟩ (by omega)
  have hTopEq :
      iteratedDeriv (2 * (k + 1)) u 0 =
        Complex.re (iteratedDeriv (2 * (k + 1)) (charFun μ) 0) := by
    -- Proof comment: differentiate the neighborhood equality once more at `0`, then identify both
    -- derivatives via `iteratedDeriv_succ`.
    have hSuccU :
        iteratedDeriv (2 * (k + 1)) u = deriv (iteratedDeriv (2 * k + 1) u) := by
      simpa [two_mul, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
        (iteratedDeriv_succ (n := k + (k + 1)) (f := u))
    calc
      iteratedDeriv (2 * (k + 1)) u 0 = deriv (iteratedDeriv (2 * k + 1) u) 0 := by
        simpa using congrFun hSuccU 0
      _ = deriv (fun s ↦ Complex.re (iteratedDeriv (2 * k + 1) (charFun μ) s)) 0 := by
        exact hEqNear.deriv_eq
      _ = Complex.re (iteratedDeriv (2 * (k + 1)) (charFun μ) 0) := by
        rw [deriv_re_comp_eq hDiffAt]
        have hSuccChar :
            iteratedDeriv (2 * (k + 1)) (charFun μ) =
              deriv (iteratedDeriv (2 * k + 1) (charFun μ)) := by
          simpa [two_mul, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
            (iteratedDeriv_succ (n := k + (k + 1)) (f := charFun μ))
        simpa using (congrArg Complex.re (congrFun hSuccChar 0)).symm
  have hDerivRe :
      HasDerivAt (iteratedDeriv (2 * k + 1) u)
        (iteratedDeriv (2 * (k + 1)) u 0) 0 := by
    -- Proof comment: take real parts of the complex derivative and transfer it back to the real
    -- iterated-derivative surface using the neighborhood equality above.
    have hDerivReBase :
        HasDerivAt (fun s ↦ Complex.re (iteratedDeriv (2 * k + 1) (charFun μ) s))
          (Complex.re (iteratedDeriv (2 * (k + 1)) (charFun μ) 0)) 0 := by
      have hDiffReBase :
          DifferentiableAt ℝ (fun s ↦ Complex.re (iteratedDeriv (2 * k + 1) (charFun μ) s)) 0 := by
        exact Complex.reCLM.differentiableAt.comp 0 hDiffAt
      refine hDiffReBase.hasDerivAt.congr_deriv ?_
      rw [deriv_re_comp_eq hDiffAt]
      have hSuccChar :
          iteratedDeriv (2 * (k + 1)) (charFun μ) =
            deriv (iteratedDeriv (2 * k + 1) (charFun μ)) := by
        simpa [two_mul, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
          (iteratedDeriv_succ (n := k + (k + 1)) (f := charFun μ))
      simpa using (congrArg Complex.re (congrFun hSuccChar 0)).symm
    simpa [hTopEq] using hDerivReBase.congr_of_eventuallyEq hEqNear
  have hOddZero :
      iteratedDeriv (2 * k + 1) u 0 = 0 := by
    -- Proof comment: `u(t) = Re (charFun μ t)` is even, so every odd iterated derivative vanishes
    -- at the origin.
    refine oddIteratedDeriv_zero_of_even ?_ (by simp)
    intro t
    simpa [u] using reCharFun_neg (μ := μ) t
  have hOddZeroMul :
      iteratedDeriv (k * 2 + 1) u 0 = 0 := by
    simpa [Nat.mul_comm] using hOddZero
  have hSlopeEq :
      (fun t : ℝ ↦ t⁻¹ • (iteratedDeriv (2 * k + 1) u (0 + t) - iteratedDeriv (2 * k + 1) u 0)) =
        fun t : ℝ ↦ iteratedDeriv (2 * k + 1) u t / t := by
    ext t
    by_cases ht : t = 0
    · simp [ht]
    · rw [div_eq_mul_inv]
      simp [hOddZeroMul, ht, sub_eq_add_neg, mul_comm, mul_assoc]
  -- Proof comment: `HasDerivAt.tendsto_slope_zero` is exactly the desired quotient limit once the
  -- odd derivative value at `0` is rewritten to `0`.
  have hSlope := hDerivRe.tendsto_slope_zero
  rw [hSlopeEq] at hSlope
  simpa [u] using hSlope

/-- Helper for Theorem 15.34: the reciprocal mesh tends to `0` through nonzero real points. -/
private lemma reciprocalMesh_tendsto_punctured_zero :
    Tendsto (fun j : ℕ ↦ ((j + 1 : ℝ))⁻¹) atTop (𝓝[≠] (0 : ℝ)) := by
  -- Proof comment: the reciprocal mesh converges to `0`, and every mesh point is already
  -- nonzero.
  refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
      (fun j : ℕ ↦ ((j + 1 : ℝ))⁻¹) ?_ ?_
  · simpa [one_div] using
      (tendsto_one_div_add_atTop_nhds_zero_nat :
        Tendsto (fun n : ℕ ↦ 1 / ((n : ℝ) + 1)) atTop (𝓝 (0 : ℝ)))
  · exact Filter.Eventually.of_forall fun j ↦ by
      simpa using reciprocalMesh_ne_zero j

/-- Helper for Theorem 15.34: the odd-derivative quotient of `u(t) = Re (charFun μ t)` stays
uniformly bounded along the reciprocal mesh near `0`. -/
private lemma eventually_abs_oddReCharFunDeriv_div_lt_on_reciprocalMesh
    {μ : Measure ℝ} [IsProbabilityMeasure μ] (m : ℕ) (hm : 0 < m)
    (hφ : HasIteratedDerivNeighborhoodAt (charFun μ) (2 * m) 0) :
    ∀ᶠ j : ℕ in atTop,
      |iteratedDeriv (2 * m - 1) (fun t ↦ Complex.re (charFun μ t)) (((j + 1 : ℝ))⁻¹) /
          (((j + 1 : ℝ))⁻¹)| <
        |iteratedDeriv (2 * m) (fun t ↦ Complex.re (charFun μ t)) 0| + 1 := by
  -- Proof comment: compose the punctured-neighborhood limit with the reciprocal mesh and then
  -- shrink to the open bound `|L| + 1` around the finite limit `L`.
  have hTendstoQuot :
      Tendsto
        (fun j : ℕ ↦
          iteratedDeriv (2 * m - 1) (fun t ↦ Complex.re (charFun μ t)) (((j + 1 : ℝ))⁻¹) /
            (((j + 1 : ℝ))⁻¹))
        atTop
        (𝓝 (iteratedDeriv (2 * m) (fun t ↦ Complex.re (charFun μ t)) 0)) := by
    exact
      (oddReCharFunDeriv_div_tendsto_topDeriv (μ := μ) m hm hφ).comp
        reciprocalMesh_tendsto_punctured_zero
  have hTendstoAbs :
      Tendsto
        (fun j : ℕ ↦
          |iteratedDeriv (2 * m - 1) (fun t ↦ Complex.re (charFun μ t)) (((j + 1 : ℝ))⁻¹) /
              (((j + 1 : ℝ))⁻¹)|)
        atTop
        (𝓝 (|iteratedDeriv (2 * m) (fun t ↦ Complex.re (charFun μ t)) 0|)) := by
    have hAbsCont :
        ContinuousAt (fun x : ℝ ↦ |x|)
          (iteratedDeriv (2 * m) (fun t ↦ Complex.re (charFun μ t)) 0) :=
      continuous_abs.continuousAt
    exact hAbsCont.tendsto.comp hTendstoQuot
  exact hTendstoAbs.eventually (Iio_mem_nhds (lt_add_of_pos_right _ zero_lt_one))

/-- Helper for Theorem 15.34: on every short interval inside the neighborhood from `hφ`, the real
part of the characteristic function has the Taylor data needed for the Cauchy remainder formula. -/
private lemma reCharFunTaylorDataOnIcc
    {μ : Measure ℝ} [IsProbabilityMeasure μ] (m : ℕ) (hm : 0 < m)
    (huCont : ContDiff ℝ (2 * m - 2) (fun t ↦ Complex.re (charFun μ t)))
    (hφ : HasIteratedDerivNeighborhoodAt (charFun μ) (2 * m) 0) :
    ∃ ε > 0,
      ∀ {a : ℝ}, 0 < a → a < ε →
        ContDiffOn ℝ (2 * m - 2) (fun t ↦ Complex.re (charFun μ t)) (Set.Icc 0 a) ∧
        DifferentiableOn ℝ
          (iteratedDeriv (2 * m - 2) (fun t ↦ Complex.re (charFun μ t)))
          (Set.Ioo 0 a) ∧
        Set.EqOn
          (iteratedDerivWithin (2 * m - 2) (fun t ↦ Complex.re (charFun μ t)) (Set.Icc 0 a))
          (iteratedDeriv (2 * m - 2) (fun t ↦ Complex.re (charFun μ t))) (Set.Ioo 0 a) := by
  rcases Nat.exists_eq_succ_of_ne_zero
      (Nat.mul_ne_zero (by decide : 2 ≠ 0) (Nat.ne_of_gt hm)) with ⟨n, hn⟩
  rw [hn] at hφ
  rcases hφ with ⟨ε, hε, hDiff, _hTop⟩
  refine ⟨ε, hε, ?_⟩
  intro a ha ha_lt
  let s : Set ℝ := Set.Ioo (0 - ε) (0 + ε)
  have hOpen : IsOpen s := isOpen_Ioo
  have hDiffLower :
      ∀ k < 2 * m - 2,
        DifferentiableOn ℝ (iteratedDeriv k (charFun μ)) s := by
    intro k hk
    simpa [s] using hDiff k (by omega)
  refine ⟨huCont.contDiffOn, ?_, ?_⟩
  · intro x hx
    have hxOpen : x ∈ s := by
      constructor
      · linarith [hx.1]
      · linarith [hx.2, ha_lt]
    have hDiffAtChar :
        DifferentiableAt ℝ (iteratedDeriv (2 * m - 2) (charFun μ)) x := by
      exact (hDiff (2 * m - 2) (by omega) x hxOpen).differentiableAt (hOpen.mem_nhds hxOpen)
    have hDiffAtRe :
        DifferentiableAt ℝ
          (fun y ↦ Complex.re (iteratedDeriv (2 * m - 2) (charFun μ) y)) x := by
      exact Complex.reCLM.differentiableAt.comp x hDiffAtChar
    have hEqNear :
        (fun y ↦ iteratedDeriv (2 * m - 2) (fun t ↦ Complex.re (charFun μ t)) y) =ᶠ[𝓝 x]
          fun y ↦ Complex.re (iteratedDeriv (2 * m - 2) (charFun μ) y) := by
      -- Proof comment: on the open neighborhood from `hφ`, iterated derivatives commute with
      -- taking real parts.
      filter_upwards [hOpen.mem_nhds hxOpen] with y hy
      simpa using iteratedDeriv_re_eq_on_open hOpen (2 * m - 2) hDiffLower y hy
    exact (hDiffAtRe.congr_of_eventuallyEq hEqNear).differentiableWithinAt
  · intro x hx
    have hxIcc : x ∈ Set.Icc 0 a := ⟨le_of_lt hx.1, le_of_lt hx.2⟩
    -- Proof comment: on interior points of a closed interval, the within-iterated derivative is
    -- the ordinary iterated derivative.
    exact iteratedDerivWithin_eq_iteratedDeriv
      (uniqueDiffOn_Icc ha)
      (huCont.contDiffAt)
      hxIcc

/-- Helper for Theorem 15.34: every Taylor coefficient at the left endpoint of `Icc 0 a`
coincides with the ordinary iterated derivative as soon as the function is smooth enough. -/
private lemma iteratedDerivWithin_Icc_zero_eq_iteratedDeriv
    {u : ℝ → ℝ} {n : ℕ} {a : ℝ} (ha : 0 < a)
    (huCont : ContDiff ℝ n u) {k : ℕ} (hk : k ≤ n) :
    iteratedDerivWithin k u (Set.Icc 0 a) 0 = iteratedDeriv k u 0 := by
  -- Proof comment: the endpoint `0` still sees the ordinary iterated derivative because the
  -- function is `C^k` there and `Icc 0 a` has unique derivatives.
  simpa using
    iteratedDerivWithin_eq_iteratedDeriv
      (uniqueDiffOn_Icc ha)
      ((huCont.of_le (by exact_mod_cast hk)).contDiffAt)
      (by exact ⟨le_rfl, ha.le⟩)

/-- Helper for Theorem 15.34: if the top within-derivative already agrees with the ordinary
iterated derivative on `Ioo 0 a`, then its differentiability transports to the within surface. -/
private lemma differentiableOn_iteratedDerivWithin_of_eqOn_Ioo
    {u : ℝ → ℝ} {n : ℕ} {a : ℝ}
    (hDiff : DifferentiableOn ℝ (iteratedDeriv n u) (Set.Ioo 0 a))
    (hEqOn : Set.EqOn (iteratedDerivWithin n u (Set.Icc 0 a)) (iteratedDeriv n u) (Set.Ioo 0 a)) :
    DifferentiableOn ℝ (iteratedDerivWithin n u (Set.Icc 0 a)) (Set.Ioo 0 a) := by
  intro x hx
  have hEqNear :
      (fun y ↦ iteratedDerivWithin n u (Set.Icc 0 a) y) =ᶠ[𝓝[Set.Ioo 0 a] x]
        fun y ↦ iteratedDeriv n u y := by
    -- Proof comment: the two derivative surfaces agree on the whole open interval, hence also in
    -- the corresponding neighborhood-within filter at every interior point.
    filter_upwards [self_mem_nhdsWithin] with y hy
    exact hEqOn hy
  -- Proof comment: differentiability is stable under eventual equality on the neighborhood-within
  -- filter.
  exact (hDiff x hx).congr_of_eventuallyEq hEqNear (hEqOn hx)

/-- Helper for Theorem 15.34: on the interior of `Icc 0 a`, the next within-iterated derivative
agrees with the ordinary iterated derivative once the previous stage already agrees there. -/
private lemma iteratedDerivWithinIccSucc_eq_iteratedDerivOnIoo
    {u : ℝ → ℝ} {n : ℕ} {a x : ℝ} (hx : x ∈ Set.Ioo 0 a)
    (_hDiff : DifferentiableOn ℝ (iteratedDeriv n u) (Set.Ioo 0 a))
    (hEqOn : Set.EqOn (iteratedDerivWithin n u (Set.Icc 0 a)) (iteratedDeriv n u) (Set.Ioo 0 a)) :
    iteratedDerivWithin (n + 1) u (Set.Icc 0 a) x = iteratedDeriv (n + 1) u x := by
  have hIccNhds : Set.Icc 0 a ∈ 𝓝 x := by
    -- Proof comment: interior points of `Icc 0 a` see the whole closed interval as a neighborhood.
    refine Filter.mem_of_superset (Ioo_mem_nhds hx.1 hx.2) ?_
    intro y hy
    exact ⟨le_of_lt hy.1, le_of_lt hy.2⟩
  have hEqNear :
      (fun y ↦ iteratedDerivWithin n u (Set.Icc 0 a) y) =ᶠ[𝓝 x]
        fun y ↦ iteratedDeriv n u y := by
    -- Proof comment: the previous-stage identification holds on the whole open interval, hence
    -- in an ordinary neighborhood of each interior point.
    filter_upwards [Ioo_mem_nhds hx.1 hx.2] with y hy
    exact hEqOn hy
  calc
    iteratedDerivWithin (n + 1) u (Set.Icc 0 a) x
        = derivWithin (iteratedDerivWithin n u (Set.Icc 0 a)) (Set.Icc 0 a) x := by
            rw [iteratedDerivWithin_succ]
    _ = deriv (iteratedDerivWithin n u (Set.Icc 0 a)) x := by
          rw [derivWithin_of_mem_nhds hIccNhds]
    _ = deriv (iteratedDeriv n u) x := by
          rw [hEqNear.deriv_eq]
    _ = iteratedDeriv (n + 1) u x := by
          rw [iteratedDeriv_succ]

/-- Helper for Theorem 15.34: the Taylor polynomial on `Icc 0 a` at the left endpoint `0`
already has the explicit ordinary-derivative form used in the textbook proof. -/
private lemma taylorWithinEvalIccZero_eq_explicitIteratedDerivSum
    {u : ℝ → ℝ} {n : ℕ} {a x : ℝ} (ha : 0 < a) (huCont : ContDiff ℝ n u) :
    taylorWithinEval u n (Set.Icc 0 a) 0 x =
      ∑ r ∈ Finset.range (n + 1), ((r.factorial : ℝ)⁻¹ * x ^ r) * iteratedDeriv r u 0 := by
  -- Proof comment: `taylor_within_apply` expands the polynomial, and every endpoint within-
  -- derivative is already the ordinary derivative at `0`.
  rw [taylor_within_apply]
  refine Finset.sum_congr rfl ?_
  intro r hr
  have hrle : r ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hr)
  simp [sub_zero, smul_eq_mul,
    iteratedDerivWithin_Icc_zero_eq_iteratedDeriv ha huCont hrle]

/-- Helper for Theorem 15.34: evaluating the centered `2m`-fold forward difference at `-(m : ℝ) * t`
is the same as summing over the centered mesh nodes `((k : ℝ) - m) * t`. -/
private lemma centeredShiftedFwdDiff_eq_meshSum
    (m : ℕ) (t : ℝ) (f : ℝ → ℝ) :
    ((Nat.iterate (fwdDiff t) (2 * m) f) (-(m : ℝ) * t)) =
      ∑ k ∈ Finset.range (2 * m + 1),
        ((((-1 : ℤ) ^ (2 * m - k) * (2 * m).choose k : ℤ) : ℝ) *
          f (((k : ℝ) - m) * t)) := by
  -- Proof comment: specialize the Gregory-Newton forward-difference formula at the centered base
  -- point `-(m : ℝ) * t` and normalize the shifted nodes once.
  simpa [fwdDiff_iter_eq_sum_shift, sub_eq_add_neg, add_comm, add_left_comm, add_assoc,
    zsmul_eq_mul, mul_add, add_mul, mul_assoc, mul_comm, mul_left_comm] using
    (fwdDiff_iter_eq_sum_shift (h := t) (f := f) (n := 2 * m) (y := -(m : ℝ) * t))

/-- Helper for Theorem 15.34: the centered forward difference of the monomial `s ↦ s^r` factors
out the full mesh power `t^r` on the real side as well. -/
private lemma centeredFwdDiff_pow_scaled_real (m r : ℕ) {t : ℝ} :
    ((Nat.iterate (fwdDiff t) (2 * m) (fun s : ℝ ↦ s ^ r)) (-(m : ℝ) * t)) =
      t ^ r *
        ((Nat.iterate (fwdDiff (1 : ℝ)) (2 * m) (fun z : ℝ ↦ z ^ r)) (-(m : ℝ))) := by
  -- Proof comment: expand the centered forward difference into the explicit mesh sum and factor
  -- out the common power `t^r`.
  calc
    ((Nat.iterate (fwdDiff t) (2 * m) (fun s : ℝ ↦ s ^ r)) (-(m : ℝ) * t))
        =
          ∑ k ∈ Finset.range (2 * m + 1),
            ((((-1 : ℤ) ^ (2 * m - k) * (2 * m).choose k : ℤ) : ℝ) *
              (((-(m : ℝ) * t) + k • t) ^ r)) := by
              simpa [fwdDiff_iter_eq_sum_shift, zsmul_eq_mul]
    _ =
          ∑ k ∈ Finset.range (2 * m + 1),
            ((((-1 : ℤ) ^ (2 * m - k) * (2 * m).choose k : ℤ) : ℝ) *
              ((t * ((k : ℝ) - m)) ^ r)) := by
              refine Finset.sum_congr rfl ?_
              intro k hk
              congr 1
              norm_num [sub_eq_add_neg, zsmul_eq_mul, mul_add, add_mul, mul_assoc, mul_comm,
                mul_left_comm, add_comm, add_left_comm, add_assoc]
    _ =
          ∑ k ∈ Finset.range (2 * m + 1),
            ((((-1 : ℤ) ^ (2 * m - k) * (2 * m).choose k : ℤ) : ℝ) *
              (t ^ r * ((k : ℝ) - m) ^ r)) := by
              refine Finset.sum_congr rfl ?_
              intro k hk
              rw [mul_pow]
    _ =
          t ^ r *
            ∑ k ∈ Finset.range (2 * m + 1),
              ((((-1 : ℤ) ^ (2 * m - k) * (2 * m).choose k : ℤ) : ℝ) *
                ((k : ℝ) - m) ^ r) := by
              rw [Finset.mul_sum]
              refine Finset.sum_congr rfl ?_
              intro k hk
              ring
    _ =
          t ^ r *
            ((Nat.iterate (fwdDiff (1 : ℝ)) (2 * m) (fun z : ℝ ↦ z ^ r)) (-(m : ℝ))) := by
              congr 1
              symm
              simpa [fwdDiff_iter_eq_sum_shift, sub_eq_add_neg, add_comm, add_left_comm,
                add_assoc, zsmul_eq_mul]

/-- Helper for Theorem 15.34: every centered mesh sum of a monomial of degree `< 2m` vanishes. -/
private lemma centeredMeshPowerSum_eq_zero (m r : ℕ) (hr : r < 2 * m) {t : ℝ} :
    ∑ k ∈ Finset.range (2 * m + 1),
      ((((-1 : ℤ) ^ (2 * m - k) * (2 * m).choose k : ℤ) : ℝ) *
        ((((k : ℝ) - m) * t) ^ r)) = 0 := by
  have hzero :
      ((Nat.iterate (fwdDiff t) (2 * m) (fun s : ℝ ↦ s ^ r)) (-(m : ℝ) * t)) = 0 := by
    calc
      ((Nat.iterate (fwdDiff t) (2 * m) (fun s : ℝ ↦ s ^ r)) (-(m : ℝ) * t))
          = t ^ r *
              ((Nat.iterate (fwdDiff (1 : ℝ)) (2 * m) (fun z : ℝ ↦ z ^ r)) (-(m : ℝ))) := by
                simpa using centeredFwdDiff_pow_scaled_real (m := m) (r := r) (t := t)
      _ = t ^ r * 0 := by
            congr 1
            exact congrFun
              (fwdDiff_iter_pow_eq_zero_of_lt (R := ℝ) (j := r) (n := 2 * m) hr) (-(m : ℝ))
      _ = 0 := by simp
  rw [centeredShiftedFwdDiff_eq_meshSum (m := m) (t := t) (f := fun s : ℝ ↦ s ^ r)] at hzero
  exact hzero

/-- Helper for Theorem 15.34: the centered `2m`-mesh annihilates the explicit Taylor polynomial
of `u(t) = Re (charFun μ t)` truncated at degree `2m - 2`. -/
private lemma centeredExplicitTaylorMeshSum_eq_zero
    {μ : Measure ℝ} [IsProbabilityMeasure μ] (m : ℕ) (t : ℝ) :
    let u : ℝ → ℝ := fun s ↦ Complex.re (charFun μ s)
    let P : ℝ → ℝ := fun s ↦
      ∑ r ∈ Finset.range (2 * m - 1),
        ((r.factorial : ℝ)⁻¹ * s ^ r) * iteratedDeriv r u 0
    ∑ k ∈ Finset.range (2 * m + 1),
      ((((-1 : ℤ) ^ (2 * m - k) * (2 * m).choose k : ℤ) : ℝ) * P (((k : ℝ) - m) * t)) = 0 := by
  let u : ℝ → ℝ := fun s ↦ Complex.re (charFun μ s)
  let P : ℝ → ℝ := fun s ↦
    ∑ r ∈ Finset.range (2 * m - 1),
      ((r.factorial : ℝ)⁻¹ * s ^ r) * iteratedDeriv r u 0
  -- Proof comment: swap the centered node sum with the Taylor sum and kill each monomial by the
  -- `2m`-fold forward-difference cancellation for degrees `< 2m`.
  dsimp [P]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_eq_zero ?_
  intro r hr
  have hrlt : r < 2 * m := by
    have hrr : r < 2 * m - 1 := Finset.mem_range.mp hr
    omega
  have hfactor :
      ∑ k ∈ Finset.range (2 * m + 1),
        ((((-1 : ℤ) ^ (2 * m - k) * (2 * m).choose k : ℤ) : ℝ) *
          (((r.factorial : ℝ)⁻¹ * ((((k : ℝ) - m) * t) ^ r)) * iteratedDeriv r u 0)) =
        (((r.factorial : ℝ)⁻¹ * iteratedDeriv r u 0) *
          ∑ k ∈ Finset.range (2 * m + 1),
            ((((-1 : ℤ) ^ (2 * m - k) * (2 * m).choose k : ℤ) : ℝ) *
              ((((k : ℝ) - m) * t) ^ r))) := by
    calc
      ∑ k ∈ Finset.range (2 * m + 1),
          ((((-1 : ℤ) ^ (2 * m - k) * (2 * m).choose k : ℤ) : ℝ) *
            (((r.factorial : ℝ)⁻¹ * ((((k : ℝ) - m) * t) ^ r)) * iteratedDeriv r u 0))
          =
            ∑ k ∈ Finset.range (2 * m + 1),
              ((((r.factorial : ℝ)⁻¹ * iteratedDeriv r u 0) *
                ((((-1 : ℤ) ^ (2 * m - k) * (2 * m).choose k : ℤ) : ℝ) *
                  ((((k : ℝ) - m) * t) ^ r)))) := by
                refine Finset.sum_congr rfl ?_
                intro k hk
                ring
      _ =
          (((r.factorial : ℝ)⁻¹ * iteratedDeriv r u 0) *
            ∑ k ∈ Finset.range (2 * m + 1),
              ((((-1 : ℤ) ^ (2 * m - k) * (2 * m).choose k : ℤ) : ℝ) *
                ((((k : ℝ) - m) * t) ^ r))) := by
                rw [Finset.mul_sum]
  rw [hfactor, centeredMeshPowerSum_eq_zero (m := m) (r := r) hrlt (t := t), mul_zero]

/-- Helper for Theorem 15.34: a Cauchy-remainder witness with quotient bound
`|D / x| ≤ B` yields the expected `a^(n+2)` Taylor remainder estimate. -/
private lemma cauchyRemainderAbs_le_of_quotientBound
    {n : ℕ} {a x D B : ℝ} (hx : x ∈ Set.Ioo 0 a) (hB : 0 ≤ B)
    (hQuot : |D / x| ≤ B) :
    |D * (a - x) ^ n / (n.factorial : ℝ) * a| ≤ B * a ^ (n + 2) / (n.factorial : ℝ) := by
  have hx_pos : 0 < x := hx.1
  have hx_lt : x < a := hx.2
  have ha_pos : 0 < a := lt_trans hx_pos hx_lt
  have ha_nonneg : 0 ≤ a := ha_pos.le
  have hx_le : x ≤ a := hx_lt.le
  have hsub_nonneg : 0 ≤ a - x := sub_nonneg.mpr hx_le
  have hfac_nonneg : (0 : ℝ) ≤ (n.factorial : ℝ) := by positivity
  have hfac_pos : (0 : ℝ) < (n.factorial : ℝ) := by positivity
  have hDx : |D| ≤ B * x := by
    have hQuot' : |D| / x ≤ B := by
      simpa [abs_div, abs_of_pos hx_pos] using hQuot
    exact (div_le_iff₀ hx_pos).mp hQuot'
  have hpow : (a - x) ^ n ≤ a ^ n := by
    refine pow_le_pow_left₀ hsub_nonneg ?_ n
    exact sub_le_self a hx_pos.le
  have hxa : x * (a - x) ^ n * a ≤ a ^ (n + 2) := by
    calc
      x * (a - x) ^ n * a ≤ a * a ^ n * a := by
        gcongr
      _ = a ^ (n + 2) := by
        rw [show n + 2 = (n + 1) + 1 by omega, pow_succ, pow_succ']
  have hnum : |D| * (a - x) ^ n * a ≤ B * a ^ (n + 2) := by
    calc
      |D| * (a - x) ^ n * a ≤ (B * x) * (a - x) ^ n * a := by
        gcongr
      _ = B * (x * (a - x) ^ n * a) := by ring
      _ ≤ B * a ^ (n + 2) := by
        gcongr
  have habs :
      |D * (a - x) ^ n / (n.factorial : ℝ) * a| =
        |D| * (a - x) ^ n * a / (n.factorial : ℝ) := by
    rw [show D * (a - x) ^ n / (n.factorial : ℝ) * a =
        (D * (a - x) ^ n * a) / (n.factorial : ℝ) by ring]
    rw [abs_div, abs_mul, abs_mul, abs_pow, abs_of_nonneg hsub_nonneg, abs_of_nonneg ha_nonneg,
      abs_of_nonneg hfac_nonneg]
  rw [habs]
  exact div_le_div_of_nonneg_right hnum hfac_nonneg

/-- Helper for Theorem 15.34: the explicit Taylor polynomial of
`u(t) = Re (charFun μ t)` only contains even powers, hence is unchanged by `t ↦ -t`. -/
private lemma reCharFunTaylorPolynomial_even
    {μ : Measure ℝ} [IsProbabilityMeasure μ] (m : ℕ) (z : ℝ) :
    let u : ℝ → ℝ := fun t ↦ Complex.re (charFun μ t)
    let P : ℝ → ℝ := fun t ↦
      ∑ r ∈ Finset.range (2 * m - 1),
        ((r.factorial : ℝ)⁻¹ * t ^ r) * iteratedDeriv r u 0
    P (-z) = P z := by
  -- Proof comment: odd coefficients vanish because `u` is even, while even powers are unchanged
  -- under negation.
  dsimp
  refine Finset.sum_congr rfl ?_
  intro r hr
  rcases Nat.even_or_odd r with (hrEven | hrOdd)
  · obtain ⟨k, hk⟩ := hrEven
    subst hk
    simp [pow_mul]
  · have hOddZero :
        iteratedDeriv r (fun t ↦ Complex.re (charFun μ t)) 0 = 0 := by
        refine oddIteratedDeriv_zero_of_even ?_ hrOdd
        intro t
        simpa using reCharFun_neg (μ := μ) t
    simp [hOddZero]

/-- Helper for Theorem 15.34: the short-interval Taylor remainder of
`u(t) = Re (charFun μ t)` is controlled by the local odd-derivative quotient bound. -/
private lemma reCharFunTaylorRemainderBound
    {μ : Measure ℝ} [IsProbabilityMeasure μ] (m : ℕ) (hm : 0 < m)
    {ε B a : ℝ} (hB : 0 ≤ B)
    (huCont : ContDiff ℝ (2 * m - 2) (fun t ↦ Complex.re (charFun μ t)))
    (hData :
      ∀ {b : ℝ}, 0 < b → b < ε →
        ContDiffOn ℝ (2 * m - 2) (fun t ↦ Complex.re (charFun μ t)) (Set.Icc 0 b) ∧
        DifferentiableOn ℝ
          (iteratedDeriv (2 * m - 2) (fun t ↦ Complex.re (charFun μ t))) (Set.Ioo 0 b) ∧
        Set.EqOn
          (iteratedDerivWithin (2 * m - 2) (fun t ↦ Complex.re (charFun μ t)) (Set.Icc 0 b))
          (iteratedDeriv (2 * m - 2) (fun t ↦ Complex.re (charFun μ t))) (Set.Ioo 0 b))
    (ha : 0 ≤ a) (ha_lt : a < ε)
    (hQuot : ∀ s : ℝ, s ≠ 0 → |s| < ε →
      |iteratedDeriv (2 * m - 1) (fun t ↦ Complex.re (charFun μ t)) s / s| < B) :
    let u : ℝ → ℝ := fun t ↦ Complex.re (charFun μ t)
    let P : ℝ → ℝ := fun t ↦
      ∑ r ∈ Finset.range (2 * m - 1),
        ((r.factorial : ℝ)⁻¹ * t ^ r) * iteratedDeriv r u 0
    |u a - P a| ≤ B * a ^ (2 * m) / (2 * m - 2).factorial := by
  let u : ℝ → ℝ := fun t ↦ Complex.re (charFun μ t)
  let P : ℝ → ℝ := fun t ↦
    ∑ r ∈ Finset.range (2 * m - 1),
      ((r.factorial : ℝ)⁻¹ * t ^ r) * iteratedDeriv r u 0
  by_cases h0 : a = 0
  · subst h0
    -- Proof comment: the remainder vanishes at the base point because the Taylor polynomial is
    -- normalized there.
    have hP0 : P 0 = 1 := by
      dsimp [P]
      rw [Finset.sum_eq_single 0]
      · simp [u, MeasureTheory.charFun_zero]
      · intro r hr hr0
        simp [hr0]
      · intro hbad
        exact (hbad (Finset.mem_range.mpr (by omega))).elim
    have hu0 : u 0 = 1 := by
      simp [u, MeasureTheory.charFun_zero]
    have hpow0 : (0 : ℝ) ^ (2 * m) = 0 := by
      exact zero_pow (Nat.mul_ne_zero (by decide : 2 ≠ 0) hm.ne')
    simpa [u, P, hP0, hu0, hpow0]
  · have ha_pos : 0 < a := lt_of_le_of_ne ha (Ne.symm h0)
    rcases hData ha_pos ha_lt with ⟨hContOn, hDiffOn, hEqOn⟩
    have hTaylorDiff :
        DifferentiableOn ℝ
          (iteratedDerivWithin (2 * m - 2) u (Set.Icc 0 a))
          (Set.Ioo 0 a) :=
      differentiableOn_iteratedDerivWithin_of_eqOn_Ioo hDiffOn hEqOn
    rcases taylor_mean_remainder_cauchy (x₀ := 0) (x := a) (n := 2 * m - 2)
        ha_pos hContOn hTaylorDiff with ⟨x', hx', hRem⟩
    have hTaylorEval :
        taylorWithinEval u (2 * m - 2) (Set.Icc 0 a) 0 a = P a := by
      -- Proof comment: this is the single normal-form rewrite that replaces the Taylor object by
      -- the explicit polynomial used in the mesh argument.
      simpa [P, show 2 * m - 2 + 1 = 2 * m - 1 by omega] using
        taylorWithinEvalIccZero_eq_explicitIteratedDerivSum
          (u := u) (n := 2 * m - 2) (a := a) (x := a) ha_pos huCont
    have hWithinEq :
        iteratedDerivWithin (2 * m - 1) u (Set.Icc 0 a) x' = iteratedDeriv (2 * m - 1) u x' := by
      -- Proof comment: the Cauchy witness lies in the open interval, so the within-derivative is
      -- already the ordinary one there.
      simpa [u, show 2 * m - 2 + 1 = 2 * m - 1 by omega] using
        iteratedDerivWithinIccSucc_eq_iteratedDerivOnIoo hx' hDiffOn hEqOn
    have hRem' :
        u a - taylorWithinEval u (2 * m - 2) (Set.Icc 0 a) 0 a =
          iteratedDerivWithin (2 * m - 1) u (Set.Icc 0 a) x' * (a - x') ^ (2 * m - 2) /
            (2 * m - 2).factorial * a := by
      simpa [u, sub_zero, show 2 * m - 2 + 1 = 2 * m - 1 by omega] using hRem
    have hx'_ne : x' ≠ 0 := ne_of_gt hx'.1
    have hx'_abs : |x'| < ε := by
      have hx'_lt_eps : x' < ε := lt_trans hx'.2 ha_lt
      simpa [abs_of_pos hx'.1] using hx'_lt_eps
    have hQuot' :
        |iteratedDeriv (2 * m - 1) u x' / x'| ≤ B := by
      exact le_of_lt (by simpa [u] using hQuot x' hx'_ne hx'_abs)
    have hAbs :
        |u a - P a| ≤ B * a ^ (2 * m) / (2 * m - 2).factorial := by
      rw [← hTaylorEval]
      rw [hRem', hWithinEq]
      simpa [show (2 * m - 2) + 2 = 2 * m by omega] using
        cauchyRemainderAbs_le_of_quotientBound
          (n := 2 * m - 2) (a := a) (x := x')
          (D := iteratedDeriv (2 * m - 1) u x') (B := B) hx' hB hQuot'
    exact hAbs

/-- Helper for Theorem 15.34: every lower even derivative of `u(t) = Re (charFun μ t)` at `0`
is the corresponding signed even moment already known from the induction hypothesis. -/
private lemma reCharFun_evenIteratedDeriv_zero_eq_lowerMoment
    {μ : Measure ℝ} [IsProbabilityMeasure μ] {m k : ℕ}
    (hφ : HasIteratedDerivNeighborhoodAt (charFun μ) (2 * m) 0) (hk : k < m)
    (hLower : ∀ j < m,
      Integrable (fun x : ℝ ↦ x ^ (2 * j)) μ ∧
        ((∫ x, x ^ (2 * j) ∂μ : ℝ) : ℂ) =
          (-1 : ℂ) ^ j * iteratedDeriv (2 * j) (charFun μ) 0) :
    iteratedDeriv (2 * k) (fun t ↦ Complex.re (charFun μ t)) 0 =
      (-1 : ℝ) ^ k * ∫ x, x ^ (2 * k) ∂μ := by
  cases m with
  | zero =>
      exact (Nat.not_lt_zero _ hk).elim
  | succ m =>
      rcases hφ with ⟨ε, hε, hDiff, _hTop⟩
      have hIoo : IsOpen (Set.Ioo (-ε) ε) := isOpen_Ioo
      have hMem0 : 0 ∈ Set.Ioo (-ε) ε := by
        constructor <;> linarith
      have hDiffLower :
          ∀ j < 2 * k, DifferentiableOn ℝ (iteratedDeriv j (charFun μ)) (Set.Ioo (-ε) ε) := by
        intro j hj
        have hj_succ : j + 1 ≤ 2 * k := Nat.succ_le_of_lt hj
        have hk_mul : 2 * k < 2 * (m + 1) := by
          simpa [two_mul] using Nat.mul_lt_mul_of_pos_left hk (by decide : 0 < 2)
        simpa using hDiff j (lt_of_le_of_lt hj_succ hk_mul)
      have hReEq :
          iteratedDeriv (2 * k) (fun t ↦ Complex.re (charFun μ t)) 0 =
            Complex.re (iteratedDeriv (2 * k) (charFun μ) 0) := by
        -- Proof comment: the lower derivative chain on the open interval lets real parts commute
        -- with iterated derivatives at the center point.
        simpa using iteratedDeriv_re_eq_on_open hIoo (2 * k) hDiffLower 0 hMem0
      have hMomentComplex :=
        (hLower k (by simpa using hk)).2
      have hMomentReal :
          ∫ x, x ^ (2 * k) ∂μ =
            (-1 : ℝ) ^ k * iteratedDeriv (2 * k) (fun t ↦ Complex.re (charFun μ t)) 0 := by
        -- Proof comment: take real parts of the complex induction identity; the even moment is
        -- already real-valued, and the sign factor is a real scalar.
        calc
          ∫ x, x ^ (2 * k) ∂μ
              = Complex.re ((-1 : ℂ) ^ k * iteratedDeriv (2 * k) (charFun μ) 0) := by
                  simpa using congrArg Complex.re hMomentComplex
          _ = (-1 : ℝ) ^ k * Complex.re (iteratedDeriv (2 * k) (charFun μ) 0) := by
                have hsignRe : Complex.re ((-1 : ℂ) ^ k) = (-1 : ℝ) ^ k := by
                  rcases Nat.even_or_odd k with (⟨r, rfl⟩ | ⟨r, rfl⟩)
                  · simp [pow_mul]
                  · simp [pow_add, pow_mul]
                have hsignIm : Complex.im ((-1 : ℂ) ^ k) = 0 := by
                  rcases Nat.even_or_odd k with (⟨r, rfl⟩ | ⟨r, rfl⟩)
                  · simp [pow_mul]
                  · simp [pow_add, pow_mul]
                rw [Complex.mul_re, hsignRe, hsignIm]
                ring
          _ = (-1 : ℝ) ^ k * iteratedDeriv (2 * k) (fun t ↦ Complex.re (charFun μ t)) 0 := by
                rw [hReEq]
      have hsign : (-1 : ℝ) ^ k * (-1 : ℝ) ^ k = 1 := by
        calc
          (-1 : ℝ) ^ k * (-1 : ℝ) ^ k = (-1 : ℝ) ^ (k + k) := by
            rw [← pow_add]
          _ = (-1 : ℝ) ^ (2 * k) := by
            ring_nf
          _ = ((-1 : ℝ) ^ 2) ^ k := by
            rw [pow_mul]
          _ = 1 := by simp
      calc
        iteratedDeriv (2 * k) (fun t ↦ Complex.re (charFun μ t)) 0
            = 1 * iteratedDeriv (2 * k) (fun t ↦ Complex.re (charFun μ t)) 0 := by
                simp
        _ = ((-1 : ℝ) ^ k * (-1 : ℝ) ^ k) *
              iteratedDeriv (2 * k) (fun t ↦ Complex.re (charFun μ t)) 0 := by
                rw [hsign]
        _ = (-1 : ℝ) ^ k *
              (((-1 : ℝ) ^ k) * iteratedDeriv (2 * k) (fun t ↦ Complex.re (charFun μ t)) 0) := by
                ring
        _ = (-1 : ℝ) ^ k * ∫ x, x ^ (2 * k) ∂μ := by
              rw [← hMomentReal]

/-- Helper for Theorem 15.34: the source-style induction step only needs the lower even moments
plus the derivative chain at `0`; the remaining blocker is precisely this local analytic bridge. -/
-- Route correction: the previous `ContDiffAt`/`Real.taylor_tendsto` pivot is not available from
-- `HasIteratedDerivNeighborhoodAt`; this local predicate controls lower derivatives on an interval
-- and the top derivative only at the center. The remaining proof must therefore stay on the
-- interval/Cauchy-remainder surface and then connect that bound back to the reciprocal-mesh kernel.
private lemma integrableEvenPower_of_derivativeChain_of_lowerMoments
    {μ : Measure ℝ} [IsProbabilityMeasure μ] (m : ℕ) (hm : 0 < m)
    (hφ : HasIteratedDerivNeighborhoodAt (charFun μ) (2 * m) 0)
    (hLower : ∀ k < m,
      Integrable (fun x : ℝ ↦ x ^ (2 * k)) μ ∧
        ((∫ x, x ^ (2 * k) ∂μ : ℝ) : ℂ) =
          (-1 : ℂ) ^ k * iteratedDeriv (2 * k) (charFun μ) 0) :
    Integrable (fun x : ℝ ↦ x ^ (2 * m)) μ := by
  let u : ℝ → ℝ := fun t ↦ Complex.re (charFun μ t)
  let P : ℝ → ℝ := fun t ↦
    ∑ r ∈ Finset.range (2 * m - 1),
      ((r.factorial : ℝ)⁻¹ * t ^ r) * iteratedDeriv r u 0
  let coeff : ℕ → ℝ := fun k ↦
    ((((-1 : ℤ) ^ (2 * m - k) * (2 * m).choose k : ℤ) : ℝ))
  have hQuotEvent :
      ∀ᶠ s : ℝ in 𝓝[≠] (0 : ℝ),
        |iteratedDeriv (2 * m - 1) u s / s| < |iteratedDeriv (2 * m) u 0| + 1 := by
    -- Proof comment: the quotient limit from the already established odd-derivative bridge gives
    -- the punctured-neighborhood control that the final Taylor/Fatou step must consume.
    have hTendsto :
        Tendsto
          (fun s : ℝ ↦ iteratedDeriv (2 * m - 1) u s / s)
          (𝓝[≠] (0 : ℝ))
          (𝓝 (iteratedDeriv (2 * m) u 0)) := by
      simpa [u] using oddReCharFunDeriv_div_tendsto_topDeriv (μ := μ) m hm hφ
    have hAbsTendsto :
        Tendsto
          (fun s : ℝ ↦ |iteratedDeriv (2 * m - 1) u s / s|)
          (𝓝[≠] (0 : ℝ))
          (𝓝 (|iteratedDeriv (2 * m) u 0|)) := by
      exact continuous_abs.continuousAt.tendsto.comp hTendsto
    exact hAbsTendsto.eventually (Iio_mem_nhds (lt_add_of_pos_right _ zero_lt_one))
  have hQuotBall :
      ∃ δ > 0, ∀ s : ℝ, s ≠ 0 → |s| < δ →
        |iteratedDeriv (2 * m - 1) u s / s| < |iteratedDeriv (2 * m) u 0| + 1 := by
    rw [eventually_nhdsWithin_iff] at hQuotEvent
    rcases Metric.mem_nhds_iff.mp hQuotEvent with ⟨δ, hδ, hδmem⟩
    refine ⟨δ, hδ, ?_⟩
    intro s hs hsd
    exact hδmem (by simpa [Real.dist_eq, abs_sub_comm] using hsd) hs
  have hPrevInt :
      Integrable (fun x : ℝ ↦ x ^ (2 * (m - 1))) μ := by
    have hm1 : m - 1 < m := by omega
    simpa using (hLower (m - 1) hm1).1
  have huCont :
      ContDiff ℝ (2 * m - 2) u := by
    -- Proof comment: the highest already-known even moment gives global `C^(2m-2)` regularity of
    -- the characteristic function, and real parts preserve that smoothness.
    have hMem : MemLp id (2 * (m - 1) : ℕ) μ := by
      cases m with
      | zero =>
          cases hm
      | succ m =>
          cases m with
          | zero =>
              simpa using
                (memLp_zero_iff_aestronglyMeasurable.mpr
                  (aestronglyMeasurable_id : AEStronglyMeasurable (id : ℝ → ℝ) μ))
          | succ m =>
              simpa using evenPower_memLp_of_integrable (μ := μ) m hPrevInt
    simpa [u, Nat.mul_sub_left_distrib, hm.ne'] using
      Complex.reCLM.contDiff.comp (MeasureTheory.contDiff_charFun (μ := μ) hMem)
  have hTaylorData := reCharFunTaylorDataOnIcc (μ := μ) m hm huCont hφ
  rcases hQuotBall with ⟨δ, hδ, hQuotδ⟩
  rcases hTaylorData with ⟨ε₀, hε₀, hTaylorData₀⟩
  let ε : ℝ := min ε₀ δ
  have hε : 0 < ε := by
    exact lt_min hε₀ hδ
  have hB : 0 ≤ |iteratedDeriv (2 * m) u 0| + 1 := by positivity
  have hTaylorData' :
      ∀ {b : ℝ}, 0 < b → b < ε →
        ContDiffOn ℝ (2 * m - 2) u (Set.Icc 0 b) ∧
        DifferentiableOn ℝ (iteratedDeriv (2 * m - 2) u) (Set.Ioo 0 b) ∧
        Set.EqOn (iteratedDerivWithin (2 * m - 2) u (Set.Icc 0 b))
          (iteratedDeriv (2 * m - 2) u) (Set.Ioo 0 b) := by
    intro b hb hbε
    exact hTaylorData₀ hb (lt_of_lt_of_le hbε (min_le_left _ _))
  have hQuot' :
      ∀ s : ℝ, s ≠ 0 → |s| < ε →
        |iteratedDeriv (2 * m - 1) u s / s| < |iteratedDeriv (2 * m) u 0| + 1 := by
    intro s hs hsε
    exact hQuotδ s hs (lt_of_lt_of_le hsε (min_le_right _ _))
  let C : ℝ :=
    ((|iteratedDeriv (2 * m) u 0| + 1) / (((2 * m - 2).factorial : ℕ) : ℝ)) *
      ∑ k ∈ Finset.range (2 * m + 1),
        |coeff k| * |(k : ℝ) - m| ^ (2 * m)
  have hKernelBound :
      ∀ {t : ℝ}, 0 < t → (m : ℝ) * t < ε →
        ∫ x, scaledSinEven m t x ∂μ ≤ C := by
    intro t ht htSmall
    have ht_ne : t ≠ 0 := ht.ne'
    have hnonnegInt :
        0 ≤ ∫ x, scaledSinEven m t x ∂μ := by
      exact integral_nonneg_of_ae (ae_of_all _ fun x ↦ scaledSinEven_nonneg m t x)
    have hPolyZero :
        ∑ k ∈ Finset.range (2 * m + 1), coeff k * P (((k : ℝ) - m) * t) = 0 := by
      simpa [u, P, coeff] using centeredExplicitTaylorMeshSum_eq_zero (μ := μ) m t
    have hDiffDecomp :
        ∫ x, scaledSinEven m t x ∂μ =
          ((-1 : ℝ) ^ m / t ^ (2 * m)) *
            (∑ k ∈ Finset.range (2 * m + 1),
              coeff k * (u (((k : ℝ) - m) * t) - P (((k : ℝ) - m) * t))) := by
      -- Proof comment: subtract the explicit Taylor polynomial before expanding the centered mesh;
      -- the polynomial part vanishes under the `2m`-fold forward difference.
      rw [scaledSinEvenIntegral_eq_shiftedFwdDiff_reCharFun (μ := μ) m ht_ne]
      have hForward :
          ((Nat.iterate (fwdDiff t) (2 * m) u) (-(m : ℝ) * t)) =
            ∑ k ∈ Finset.range (2 * m + 1),
              coeff k * (u (((k : ℝ) - m) * t) - P (((k : ℝ) - m) * t)) := by
        have huStep : (fun s ↦ u s) = (fun s ↦ u s - P s) + P := by
          funext s
          simp [sub_eq_add_neg]
        have hIter :
            (Nat.iterate (fwdDiff t) (2 * m) (fun s ↦ u s)) =
              Nat.iterate (fwdDiff t) (2 * m) ((fun s ↦ u s - P s) + P) := by
          rw [huStep]
        calc
          ((Nat.iterate (fwdDiff t) (2 * m) u) (-(m : ℝ) * t))
              = ((Nat.iterate (fwdDiff t) (2 * m) ((fun s ↦ u s - P s) + P)) (-(m : ℝ) * t)) := by
                  simpa using congrFun hIter (-(m : ℝ) * t)
          _ =
              (((Nat.iterate (fwdDiff t) (2 * m) (fun s ↦ u s - P s)) +
                (Nat.iterate (fwdDiff t) (2 * m) P)) (-(m : ℝ) * t)) := by
                  rw [fwdDiff_iter_add]
          _ = ((Nat.iterate (fwdDiff t) (2 * m) (fun s ↦ u s - P s)) (-(m : ℝ) * t)) +
                ((Nat.iterate (fwdDiff t) (2 * m) P) (-(m : ℝ) * t)) := by
                  simp
          _ = ∑ k ∈ Finset.range (2 * m + 1),
                coeff k * (u (((k : ℝ) - m) * t) - P (((k : ℝ) - m) * t)) +
              ∑ k ∈ Finset.range (2 * m + 1), coeff k * P (((k : ℝ) - m) * t) := by
                  rw [centeredShiftedFwdDiff_eq_meshSum (m := m) (t := t) (f := fun s ↦ u s - P s),
                    centeredShiftedFwdDiff_eq_meshSum (m := m) (t := t) (f := P)]
          _ = ∑ k ∈ Finset.range (2 * m + 1),
                coeff k * (u (((k : ℝ) - m) * t) - P (((k : ℝ) - m) * t)) := by
                  rw [hPolyZero, add_zero]
      exact congrArg (fun z : ℝ ↦ ((-1 : ℝ) ^ m / t ^ (2 * m)) * z) hForward
    have hNodeBound :
        ∀ k ∈ Finset.range (2 * m + 1),
          |u (((k : ℝ) - m) * t) - P (((k : ℝ) - m) * t)| ≤
            (|iteratedDeriv (2 * m) u 0| + 1) *
              |((k : ℝ) - m) * t| ^ (2 * m) / (((2 * m - 2).factorial : ℕ) : ℝ) := by
      intro k hk
      have hk_le : k ≤ 2 * m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
      have hk_cast_le : (k : ℝ) ≤ 2 * m := by exact_mod_cast hk_le
      have hcenter_le : |(k : ℝ) - m| ≤ m := by
        rw [abs_le]
        constructor <;> nlinarith
      have hnode_lt :
          |((k : ℝ) - m) * t| < ε := by
        have habs_mul :
            |((k : ℝ) - m) * t| ≤ (m : ℝ) * t := by
          rw [abs_mul, abs_of_nonneg ht.le]
          exact mul_le_mul_of_nonneg_right hcenter_le ht.le
        exact lt_of_le_of_lt habs_mul htSmall
      have hSigned :
          |u (((k : ℝ) - m) * t) - P (((k : ℝ) - m) * t)| =
            |u (|((k : ℝ) - m) * t|) - P (|((k : ℝ) - m) * t|)| := by
        by_cases hnode_nonneg : 0 ≤ ((k : ℝ) - m) * t
        · rw [abs_of_nonneg hnode_nonneg]
        · have hnode_neg : ((k : ℝ) - m) * t < 0 := lt_of_not_ge hnode_nonneg
          rw [abs_of_neg hnode_neg]
          have huEven :
              u (-(((k : ℝ) - m) * t)) = u (((k : ℝ) - m) * t) := by
            simpa [u] using reCharFun_neg (μ := μ) (((k : ℝ) - m) * t)
          have hPEven :
              P (-(((k : ℝ) - m) * t)) = P (((k : ℝ) - m) * t) := by
            simpa [u, P] using reCharFunTaylorPolynomial_even (μ := μ) m (((k : ℝ) - m) * t)
          rw [huEven, hPEven]
      have hRemainder :
          |u (|((k : ℝ) - m) * t|) - P (|((k : ℝ) - m) * t|)| ≤
            (|iteratedDeriv (2 * m) u 0| + 1) *
              |((k : ℝ) - m) * t| ^ (2 * m) / (((2 * m - 2).factorial : ℕ) : ℝ) := by
        simpa [u, P] using
          reCharFunTaylorRemainderBound (μ := μ) (m := m) hm
            (B := |iteratedDeriv (2 * m) u 0| + 1) hB huCont hTaylorData'
            (a := |((k : ℝ) - m) * t|) (abs_nonneg _) hnode_lt hQuot'
      rw [hSigned]
      exact hRemainder
    have hpref :
        |(-1 : ℝ) ^ m / t ^ (2 * m)| = 1 / t ^ (2 * m) := by
      rw [abs_div, abs_of_nonneg (pow_nonneg ht.le _)]
      simp
    calc
      ∫ x, scaledSinEven m t x ∂μ
          ≤ |∫ x, scaledSinEven m t x ∂μ| := le_abs_self _
      _ = |(((-1 : ℝ) ^ m / t ^ (2 * m)) *
            (∑ k ∈ Finset.range (2 * m + 1),
              coeff k * (u (((k : ℝ) - m) * t) - P (((k : ℝ) - m) * t))))| := by
            rw [hDiffDecomp]
      _ ≤ |(-1 : ℝ) ^ m / t ^ (2 * m)| *
            |∑ k ∈ Finset.range (2 * m + 1),
              coeff k * (u (((k : ℝ) - m) * t) - P (((k : ℝ) - m) * t))| := by
            simpa [abs_mul] using
              abs_mul ((-1 : ℝ) ^ m / t ^ (2 * m))
                (∑ k ∈ Finset.range (2 * m + 1),
                  coeff k * (u (((k : ℝ) - m) * t) - P (((k : ℝ) - m) * t)))
      _ ≤ |(-1 : ℝ) ^ m / t ^ (2 * m)| *
            ∑ k ∈ Finset.range (2 * m + 1),
              |coeff k * (u (((k : ℝ) - m) * t) - P (((k : ℝ) - m) * t))| := by
            exact mul_le_mul_of_nonneg_left
              (Finset.abs_sum_le_sum_abs
                (f := fun k ↦ coeff k * (u (((k : ℝ) - m) * t) - P (((k : ℝ) - m) * t)))
                (s := Finset.range (2 * m + 1)))
              (abs_nonneg _)
      _ ≤ (1 / t ^ (2 * m)) *
            ∑ k ∈ Finset.range (2 * m + 1),
              |coeff k| *
                ((|iteratedDeriv (2 * m) u 0| + 1) *
                  |((k : ℝ) - m) * t| ^ (2 * m) / (((2 * m - 2).factorial : ℕ) : ℝ)) := by
            rw [hpref]
            refine mul_le_mul_of_nonneg_left ?_ (by positivity)
            refine Finset.sum_le_sum ?_
            intro k hk
            calc
              |coeff k * (u (((k : ℝ) - m) * t) - P (((k : ℝ) - m) * t))|
                  = |coeff k| * |u (((k : ℝ) - m) * t) - P (((k : ℝ) - m) * t)| := by
                      rw [abs_mul]
              _ ≤ |coeff k| *
                    ((|iteratedDeriv (2 * m) u 0| + 1) *
                      |((k : ℝ) - m) * t| ^ (2 * m) / (((2 * m - 2).factorial : ℕ) : ℝ)) := by
                    gcongr
                    exact hNodeBound k hk
      _ = ∑ k ∈ Finset.range (2 * m + 1),
            (1 / t ^ (2 * m)) *
              (|coeff k| *
                ((|iteratedDeriv (2 * m) u 0| + 1) *
                  |((k : ℝ) - m) * t| ^ (2 * m) / (((2 * m - 2).factorial : ℕ) : ℝ))) := by
            rw [Finset.mul_sum]
      _ = ∑ k ∈ Finset.range (2 * m + 1),
            ((|iteratedDeriv (2 * m) u 0| + 1) / (((2 * m - 2).factorial : ℕ) : ℝ)) *
              |coeff k| * |(k : ℝ) - m| ^ (2 * m) := by
            refine Finset.sum_congr rfl ?_
            intro k hk
            have htpow_ne : t ^ (2 * m) ≠ 0 := pow_ne_zero _ ht_ne
            have hfac_ne : ((((2 * m - 2).factorial : ℕ) : ℝ)) ≠ 0 := by positivity
            rw [abs_mul, abs_of_nonneg ht.le, mul_pow]
            field_simp [htpow_ne, hfac_ne]
      _ = ((|iteratedDeriv (2 * m) u 0| + 1) / (((2 * m - 2).factorial : ℕ) : ℝ)) *
            ∑ k ∈ Finset.range (2 * m + 1),
              |coeff k| * |(k : ℝ) - m| ^ (2 * m) := by
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl ?_
            intro k hk
            ring
      _ = C := rfl
  have hMeshEventually :
      ∀ᶠ j : ℕ in atTop, (m : ℝ) * (((j + 1 : ℝ))⁻¹) < ε := by
    have hm_real_pos : 0 < (m : ℝ) := by exact_mod_cast hm
    have hrecip_zero :
        Tendsto (fun j : ℕ ↦ ((j + 1 : ℝ))⁻¹) atTop (𝓝 (0 : ℝ)) := by
      simpa [one_div] using
        (tendsto_one_div_add_atTop_nhds_zero_nat :
          Tendsto (fun n : ℕ ↦ 1 / ((n : ℝ) + 1)) atTop (𝓝 (0 : ℝ)))
    have hEventuallyRecip :
        ∀ᶠ j : ℕ in atTop, ((j + 1 : ℝ))⁻¹ < ε / m := by
      exact hrecip_zero.eventually (Iio_mem_nhds (by positivity : 0 < ε / m))
    filter_upwards [hEventuallyRecip] with j hj
    have hmul := mul_lt_mul_of_pos_left hj hm_real_pos
    simpa [div_eq_mul_inv, hm_real_pos.ne', mul_assoc, mul_comm, mul_left_comm] using hmul
  have hFatou :
      ∫⁻ x, ENNReal.ofReal (x ^ (2 * m)) ∂μ ≤
        liminf
          (fun j : ℕ ↦
            ∫⁻ x, ENNReal.ofReal (scaledSinEven m (((j + 1 : ℝ))⁻¹) x) ∂μ)
          atTop := by
    calc
      ∫⁻ x, ENNReal.ofReal (x ^ (2 * m)) ∂μ =
          ∫⁻ x,
            liminf
              (fun j : ℕ ↦ ENNReal.ofReal (scaledSinEven m (((j + 1 : ℝ))⁻¹) x))
              atTop ∂μ := by
            refine lintegral_congr_ae ?_
            filter_upwards with x
            exact ((ENNReal.continuous_ofReal.tendsto (x ^ (2 * m))).comp
              (scaledSinEven_pointwise_tendsto_evenPower m x)).liminf_eq.symm
      _ ≤ liminf
            (fun j : ℕ ↦
              ∫⁻ x, ENNReal.ofReal (scaledSinEven m (((j + 1 : ℝ))⁻¹) x) ∂μ)
            atTop := by
            refine MeasureTheory.lintegral_liminf_le' ?_
            intro j
            have hMeas :
                AEMeasurable
                  (fun x : ℝ ↦ ENNReal.ofReal (scaledSinEven m (((j + 1 : ℝ))⁻¹) x)) μ := by
              have hMeasBase :
                  AEStronglyMeasurable
                    (fun x : ℝ ↦ scaledSinEven m (((j + 1 : ℝ))⁻¹) x) μ :=
                (scaledSinEven_integrable (μ := μ) m (((j + 1 : ℝ))⁻¹)).aestronglyMeasurable
              exact hMeasBase.aemeasurable.ennreal_ofReal
            exact hMeas
  have hEventuallyBoundLIntegral :
      ∀ᶠ j : ℕ in atTop,
        ∫⁻ x, ENNReal.ofReal (scaledSinEven m (((j + 1 : ℝ))⁻¹) x) ∂μ ≤ ENNReal.ofReal C := by
    filter_upwards [hMeshEventually] with j hj
    have ht_pos : 0 < ((j + 1 : ℝ))⁻¹ := by positivity
    have hrealBound :
        ∫ x, scaledSinEven m (((j + 1 : ℝ))⁻¹) x ∂μ ≤ C := by
      exact hKernelBound ht_pos hj
    rw [← ofReal_integral_eq_lintegral_ofReal
      (scaledSinEven_integrable (μ := μ) m (((j + 1 : ℝ))⁻¹))
      (ae_of_all _ fun x ↦ scaledSinEven_nonneg m (((j + 1 : ℝ))⁻¹) x)]
    exact ENNReal.ofReal_le_ofReal hrealBound
  have hLiminf_ne_top :
      liminf
        (fun j : ℕ ↦
          ∫⁻ x, ENNReal.ofReal (scaledSinEven m (((j + 1 : ℝ))⁻¹) x) ∂μ)
        atTop ≠ ⊤ := by
    have hLiminf_le :
      liminf
          (fun j : ℕ ↦
            ∫⁻ x, ENNReal.ofReal (scaledSinEven m (((j + 1 : ℝ))⁻¹) x) ∂μ)
          atTop ≤ ENNReal.ofReal C :=
      Filter.liminf_le_of_frequently_le' hEventuallyBoundLIntegral.frequently
    exact ne_top_of_le_ne_top (b := ENNReal.ofReal C) ENNReal.ofReal_ne_top hLiminf_le
  have hMomentLIntegral_ne_top :
      ∫⁻ x, ENNReal.ofReal (x ^ (2 * m)) ∂μ ≠ ⊤ := by
    exact ne_top_of_le_ne_top hLiminf_ne_top hFatou
  have hPowMeas : AEStronglyMeasurable (fun x : ℝ ↦ x ^ (2 * m)) μ := by
    fun_prop
  have hPowNonneg : 0 ≤ᵐ[μ] fun x : ℝ ↦ x ^ (2 * m) := by
    exact ae_of_all _ fun x ↦ by
      simpa [pow_mul, Nat.mul_comm] using sq_nonneg (x ^ m)
  exact
    (MeasureTheory.lintegral_ofReal_ne_top_iff_integrable hPowMeas hPowNonneg).mp
      hMomentLIntegral_ne_top

/-- Theorem 15.34: if the characteristic function of a real probability law is `2n`-times
differentiable at `0` in the classical neighborhood sense, then the `2n`th moment is finite and
equals `(-1)^n` times the `2n`th derivative at `0`. -/
theorem evenMoment_eq_negOnePow_mul_iteratedDeriv_charFun_zero
    {μ : Measure ℝ} [IsProbabilityMeasure μ] (n : ℕ)
    (hφ : HasIteratedDerivNeighborhoodAt (charFun μ) (2 * n) 0) :
    Integrable (fun x : ℝ ↦ x ^ (2 * n)) μ ∧
      ((∫ x, x ^ (2 * n) ∂μ : ℝ) : ℂ) =
        (-1 : ℂ) ^ n * iteratedDeriv (2 * n) (charFun μ) 0 := by
  revert hφ
  refine Nat.strong_induction_on n ?_
  intro n ih hφ
  cases n with
  | zero =>
      constructor
      · -- Proof comment: the zeroth moment is the constant-one function on a probability space.
        simpa using (integrable_const (1 : ℝ))
      · -- Proof comment: `iteratedDeriv 0` is the function itself, and `charFun μ 0 = 1`.
        simp [MeasureTheory.charFun_zero]
  | succ n =>
      have hLower :
          ∀ k < n + 1,
            Integrable (fun x : ℝ ↦ x ^ (2 * k)) μ ∧
              ((∫ x, x ^ (2 * k) ∂μ : ℝ) : ℂ) =
                (-1 : ℂ) ^ k * iteratedDeriv (2 * k) (charFun μ) 0 := by
        intro k hk
        -- Proof comment: strong induction reuses the theorem at every lower even order after
        -- truncating the derivative-chain hypothesis.
        have hkφ : HasIteratedDerivNeighborhoodAt (charFun μ) (2 * k) 0 :=
          hasIteratedDerivNeighborhoodAt_mono hφ
            (Nat.mul_le_mul_left 2 (Nat.le_of_lt hk))
        exact ih k hk hkφ
      have hInt : Integrable (fun x : ℝ ↦ x ^ (2 * (n + 1))) μ :=
        integrableEvenPower_of_derivativeChain_of_lowerMoments
          (μ := μ) (m := n + 1) (Nat.succ_pos _) hφ hLower
      constructor
      · -- Proof comment: the induction step first recovers the finite `2(n+1)`th moment.
        simpa using hInt
      · -- Proof comment: once the moment is integrable, the derivative identity is the stable
        -- forward implication already proved above.
        exact evenMoment_formula_of_integrable (μ := μ) n hInt
