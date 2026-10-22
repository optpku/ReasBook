/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

open Filter MeasureTheory

universe u

namespace ProbabilityTheory

variable {Ω : Type u} [MeasurableSpace Ω]

namespace HasLaw

/-- Helper for Lemma 22.2: the standard Gaussian right tail is the integral of its density over
`Set.Ioi x`. -/
private lemma gaussianRealRealIci_eq_tailIntegral (x : ℝ) :
    (gaussianReal 0 1).real (Set.Ici x) = ∫ t in Set.Ioi x, gaussianPDFReal 0 1 t := by
  rw [measureReal_def, gaussianReal_apply_eq_integral 0 one_ne_zero]
  rw [ENNReal.toReal_ofReal (integral_nonneg fun t ↦ gaussianPDFReal_nonneg 0 1 t)]
  simpa using
    (integral_Ici_eq_integral_Ioi (μ := volume) (f := gaussianPDFReal 0 1) (x := x))

/-- Helper for Lemma 22.2: the reciprocal map has derivative `-(1 / t ^ 2)` on `(0, ∞)`. -/
private lemma hasDerivAt_one_div (t : ℝ) (ht : 0 < t) :
    HasDerivAt (fun y : ℝ ↦ 1 / y) (-(1 / t ^ 2)) t := by
  simpa [one_div, div_eq_mul_inv, pow_two, mul_comm, mul_left_comm, mul_assoc] using
    (hasDerivAt_id t).inv ht.ne'

/-- Helper for Lemma 22.2: the derivative of `-gaussianPDFReal 0 1` is
`t * gaussianPDFReal 0 1 t`. -/
private lemma hasDerivAt_negStandardGaussianPDF (t : ℝ) :
    HasDerivAt (fun y : ℝ ↦ -gaussianPDFReal 0 1 y) (t * gaussianPDFReal 0 1 t) t := by
  have hpow : HasDerivAt (fun y : ℝ ↦ y ^ 2) (2 * t) t := by
    simpa [two_mul] using (hasDerivAt_id t).pow 2
  have harg : HasDerivAt (fun y : ℝ ↦ -(y ^ 2) / 2) (-t) t := by
    simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using
      hpow.neg.const_mul (1 / 2 : ℝ)
  have hexp :
      HasDerivAt (fun y : ℝ ↦ Real.exp (-(y ^ 2) / 2))
        (-(t * Real.exp (-(t ^ 2) / 2))) t := by
    simpa [mul_comm] using harg.exp
  simpa [gaussianPDFReal_def, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using
    hexp.const_mul (-((Real.sqrt (2 * Real.pi))⁻¹))

/-- Helper for Lemma 22.2: the antiderivative `t ↦ -gaussianPDFReal 0 1 t / t` differentiates to
`gaussianPDFReal 0 1 t + gaussianPDFReal 0 1 t / t ^ 2` on `(0, ∞)`. -/
private lemma hasDerivAt_negStandardGaussianPDFDiv {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun y : ℝ ↦ -gaussianPDFReal 0 1 y / y)
      (gaussianPDFReal 0 1 t + gaussianPDFReal 0 1 t / t ^ 2) t := by
  have hmul :
      HasDerivAt
        (fun y : ℝ ↦ (1 / y) * (-gaussianPDFReal 0 1 y))
        ((-(1 / t ^ 2)) * (-gaussianPDFReal 0 1 t) + (1 / t) * (t * gaussianPDFReal 0 1 t)) t :=
    (hasDerivAt_one_div t ht).mul (hasDerivAt_negStandardGaussianPDF t)
  convert hmul using 1
  · funext y
    ring
  · field_simp [ht.ne']
    ring

/-- Helper for Lemma 22.2: `-gaussianPDFReal 0 1 t / t` is a constant multiple of
`Real.exp (-(t ^ 2) / 2) * t⁻¹`. -/
private lemma negStandardGaussianPDFDiv_eq_const_mul_exp_mul_inv (t : ℝ) :
    -gaussianPDFReal 0 1 t / t =
      (-((Real.sqrt (2 * Real.pi))⁻¹)) * (Real.exp (-(t ^ 2) / 2) * t⁻¹) := by
  simp [gaussianPDFReal_def, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm]

/-- Helper for Lemma 22.2: the product `Real.exp (-(t ^ 2) / 2) * t⁻¹` tends to `0` at `+∞`. -/
private lemma tendsto_standardGaussianExpMulInvAtTop :
    Tendsto (fun t : ℝ ↦ Real.exp (-(t ^ 2) / 2) * t⁻¹) atTop (nhds 0) := by
  have hquad : Tendsto (fun t : ℝ ↦ -(t ^ 2) / 2) atTop atBot := by
    simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using
      (Filter.tendsto_pow_atTop two_ne_zero).const_mul_atTop_of_neg
        (by norm_num : -(1 / 2 : ℝ) < 0)
  have hexp :
      Tendsto (fun t : ℝ ↦ Real.exp (-(t ^ 2) / 2)) atTop (nhds 0) := by
    exact Real.tendsto_exp_atBot.comp hquad
  have hinv : Tendsto (fun t : ℝ ↦ t⁻¹) atTop (nhds 0) := tendsto_inv_atTop_zero
  simpa using hexp.mul hinv

/-- Helper for Lemma 22.2: `-gaussianPDFReal 0 1 t / t` tends to `0` at `+∞`. -/
private lemma tendsto_negStandardGaussianPDFDivAtTop :
    Tendsto (fun t : ℝ ↦ -gaussianPDFReal 0 1 t / t) atTop (nhds 0) := by
  have hmul :=
    (tendsto_standardGaussianExpMulInvAtTop).const_mul (-((Real.sqrt (2 * Real.pi))⁻¹))
  simpa [negStandardGaussianPDFDiv_eq_const_mul_exp_mul_inv] using hmul

/-- Helper for Lemma 22.2: on `Set.Ici x`, the antiderivative
`t ↦ -gaussianPDFReal 0 1 t / t` has the expected derivative. -/
private lemma hasDerivAt_negStandardGaussianPDFDiv_of_memIci
    {x t : ℝ} (hx : 0 < x) (ht : t ∈ Set.Ici x) :
    HasDerivAt
      (fun y : ℝ ↦ -gaussianPDFReal 0 1 y / y)
      (gaussianPDFReal 0 1 t + gaussianPDFReal 0 1 t / t ^ 2) t := by
  exact hasDerivAt_negStandardGaussianPDFDiv (lt_of_lt_of_le hx ht)

/-- Helper for Lemma 22.2: the integrand arising from differentiating
`t ↦ -gaussianPDFReal 0 1 t / t` is nonnegative on `(x, ∞)`. -/
private lemma standardGaussianTailDerivativeIntegrandNonneg
    (t : ℝ) :
    0 ≤ gaussianPDFReal 0 1 t + gaussianPDFReal 0 1 t / t ^ 2 := by
  have hφ : 0 ≤ gaussianPDFReal 0 1 t := gaussianPDFReal_nonneg 0 1 t
  exact add_nonneg hφ (div_nonneg hφ (sq_nonneg _))

/-- Helper for Lemma 22.2: the derivative integrand is integrable on `(x, ∞)`. -/
private lemma standardGaussianTailDerivativeIntegrandIntegrable
    {x : ℝ} (hx : 0 < x) :
    IntegrableOn
      (fun t : ℝ ↦ gaussianPDFReal 0 1 t + gaussianPDFReal 0 1 t / t ^ 2)
      (Set.Ioi x) := by
  exact
    integrableOn_Ioi_deriv_of_nonneg'
      (fun t ht ↦ hasDerivAt_negStandardGaussianPDFDiv (lt_of_lt_of_le hx ht))
      (fun t _ ↦ standardGaussianTailDerivativeIntegrandNonneg t)
      tendsto_negStandardGaussianPDFDivAtTop

/-- Helper for Lemma 22.2: integrating the derivative of
`t ↦ -gaussianPDFReal 0 1 t / t` over `(x, ∞)` gives `gaussianPDFReal 0 1 x / x`. -/
private lemma standardGaussianTailDerivativeIntegral_eq
    {x : ℝ} (hx : 0 < x) :
    ∫ t in Set.Ioi x, (gaussianPDFReal 0 1 t + gaussianPDFReal 0 1 t / t ^ 2) =
      gaussianPDFReal 0 1 x / x := by
  simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using
    integral_Ioi_of_hasDerivAt_of_nonneg'
      (fun t ht ↦ hasDerivAt_negStandardGaussianPDFDiv (lt_of_lt_of_le hx ht))
      (fun t _ ↦ standardGaussianTailDerivativeIntegrandNonneg t)
      tendsto_negStandardGaussianPDFDivAtTop

/-- Helper for Lemma 22.2: the Gaussian tail integral is dominated by the derivative integral,
since the remainder term `gaussianPDFReal 0 1 t / t ^ 2` is nonnegative. -/
private lemma standardGaussianTail_leDerivativeIntegral
    {x : ℝ} (hx : 0 < x) :
    (∫ t in Set.Ioi x, gaussianPDFReal 0 1 t) ≤
      ∫ t in Set.Ioi x, (gaussianPDFReal 0 1 t + gaussianPDFReal 0 1 t / t ^ 2) := by
  have hφInt : IntegrableOn (gaussianPDFReal 0 1) (Set.Ioi x) :=
    (integrable_gaussianPDFReal 0 1).integrableOn
  have hderivInt :
      IntegrableOn
        (fun t : ℝ ↦ gaussianPDFReal 0 1 t + gaussianPDFReal 0 1 t / t ^ 2)
        (Set.Ioi x) :=
    standardGaussianTailDerivativeIntegrandIntegrable hx
  refine setIntegral_mono_on hφInt hderivInt measurableSet_Ioi ?_
  intro t ht
  have hrem : 0 ≤ gaussianPDFReal 0 1 t / t ^ 2 := by
    exact div_nonneg (gaussianPDFReal_nonneg 0 1 t) (sq_nonneg _)
  linarith

/-- Helper for Lemma 22.2: the derivative integrand is bounded by
`(1 + 1 / x ^ 2) * gaussianPDFReal 0 1 t` on `(x, ∞)`. -/
private lemma standardGaussianTailDerivativeIntegral_le_scaledTail
    {x : ℝ} (hx : 0 < x) :
    (∫ t in Set.Ioi x, (gaussianPDFReal 0 1 t + gaussianPDFReal 0 1 t / t ^ 2)) ≤
      (1 + 1 / x ^ 2) * ∫ t in Set.Ioi x, gaussianPDFReal 0 1 t := by
  have hφInt : IntegrableOn (gaussianPDFReal 0 1) (Set.Ioi x) :=
    (integrable_gaussianPDFReal 0 1).integrableOn
  have hderivInt :
      IntegrableOn
        (fun t : ℝ ↦ gaussianPDFReal 0 1 t + gaussianPDFReal 0 1 t / t ^ 2)
        (Set.Ioi x) :=
    standardGaussianTailDerivativeIntegrandIntegrable hx
  have hscaledInt :
      IntegrableOn (fun t : ℝ ↦ (1 + 1 / x ^ 2) * gaussianPDFReal 0 1 t) (Set.Ioi x) :=
    hφInt.const_mul _
  calc
    ∫ t in Set.Ioi x, (gaussianPDFReal 0 1 t + gaussianPDFReal 0 1 t / t ^ 2)
        ≤ ∫ t in Set.Ioi x, (1 + 1 / x ^ 2) * gaussianPDFReal 0 1 t := by
          refine setIntegral_mono_on hderivInt hscaledInt measurableSet_Ioi ?_
          intro t ht
          have hxt : x < t := ht
          have hsq : x ^ 2 ≤ t ^ 2 := by
            nlinarith [hx, hxt]
          have hle : 1 / t ^ 2 ≤ 1 / x ^ 2 := one_div_le_one_div_of_le (by positivity) hsq
          have hφ : 0 ≤ gaussianPDFReal 0 1 t := gaussianPDFReal_nonneg 0 1 t
          have hrem :
              gaussianPDFReal 0 1 t / t ^ 2 ≤ (1 / x ^ 2) * gaussianPDFReal 0 1 t := by
            simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using
              mul_le_mul_of_nonneg_right hle hφ
          calc
            gaussianPDFReal 0 1 t + gaussianPDFReal 0 1 t / t ^ 2
                ≤ gaussianPDFReal 0 1 t + (1 / x ^ 2) * gaussianPDFReal 0 1 t := by
                  simpa [add_comm, add_left_comm, add_assoc] using
                    add_le_add_left hrem (gaussianPDFReal 0 1 t)
            _ = (1 + 1 / x ^ 2) * gaussianPDFReal 0 1 t := by
              ring
    _ = (1 + 1 / x ^ 2) * ∫ t in Set.Ioi x, gaussianPDFReal 0 1 t := by
      simp [integral_const_mul]

/-- Helper for Lemma 22.2: the standard Gaussian upper tail over `Set.Ici x` satisfies the
textbook Mills upper bound. -/
private lemma standardGaussianRealTailUpperBound
    {x : ℝ} (hx : 0 < x) :
    (gaussianReal 0 1).real (Set.Ici x) ≤ gaussianPDFReal 0 1 x / x := by
  -- Proof comment: rewrite the tail as the density integral and compare it with the derivative
  -- integral, whose value is exact by the fundamental theorem of calculus.
  rw [gaussianRealRealIci_eq_tailIntegral x]
  calc
    ∫ t in Set.Ioi x, gaussianPDFReal 0 1 t
        ≤ ∫ t in Set.Ioi x, (gaussianPDFReal 0 1 t + gaussianPDFReal 0 1 t / t ^ 2) :=
          standardGaussianTail_leDerivativeIntegral hx
    _ = gaussianPDFReal 0 1 x / x := standardGaussianTailDerivativeIntegral_eq hx

/-- Helper for Lemma 22.2: the standard Gaussian upper-tail estimate implies the textbook lower
Mills bound over `Set.Ici x`. -/
private lemma standardGaussianRealTailLowerBound
    {x : ℝ} (hx : 0 < x) :
    gaussianPDFReal 0 1 x / (x + 1 / x) ≤ (gaussianReal 0 1).real (Set.Ici x) := by
  -- Proof comment: bound the derivative integral by `(1 + x⁻²)` times the tail, then solve for
  -- the tail integral.
  rw [gaussianRealRealIci_eq_tailIntegral x]
  have hxsum : 0 < x + 1 / x := by
    positivity
  have hstep :
      gaussianPDFReal 0 1 x / x ≤
        (1 + 1 / x ^ 2) * ∫ t in Set.Ioi x, gaussianPDFReal 0 1 t := by
    simpa [standardGaussianTailDerivativeIntegral_eq hx] using
      standardGaussianTailDerivativeIntegral_le_scaledTail hx
  have hxcoeff : x * (1 + 1 / x ^ 2) = x + 1 / x := by
    field_simp [hx.ne']
  have hmain :
      gaussianPDFReal 0 1 x ≤ (x + 1 / x) * ∫ t in Set.Ioi x, gaussianPDFReal 0 1 t := by
    calc
      gaussianPDFReal 0 1 x = x * (gaussianPDFReal 0 1 x / x) := by
        field_simp [hx.ne']
      _ ≤ x * ((1 + 1 / x ^ 2) * ∫ t in Set.Ioi x, gaussianPDFReal 0 1 t) := by
        exact mul_le_mul_of_nonneg_left hstep hx.le
      _ = (x + 1 / x) * ∫ t in Set.Ioi x, gaussianPDFReal 0 1 t := by
        rw [← mul_assoc, hxcoeff]
  exact (div_le_iff₀ hxsum).2 (by simpa [mul_comm, mul_left_comm, mul_assoc] using hmain)

/-- Helper for Lemma 22.2: the canonical owner theorem yields the lower Gaussian tail bound
directly. -/
private lemma standardNormalTailLowerBound
    {P : Measure Ω} {X : Ω → ℝ} (hX : HasLaw X (gaussianReal 0 1) P) {x : ℝ} (hx : 0 < x) :
    gaussianPDFReal 0 1 x / (x + 1 / x) ≤ P.real (X ⁻¹' Set.Ici x) := by
  -- Proof comment: transfer the standard-Gaussian bound through the law of `X`.
  have hIci : P (X ⁻¹' Set.Ici x) = (gaussianReal 0 1) (Set.Ici x) :=
    (hX.identDistrib HasLaw.id).measure_mem_eq measurableSet_Ici
  have hpreimage : P.real (X ⁻¹' Set.Ici x) = (gaussianReal 0 1).real (Set.Ici x) := by
    simpa [measureReal_def] using congrArg ENNReal.toReal hIci
  rw [hpreimage]
  exact standardGaussianRealTailLowerBound hx

/-- Helper for Lemma 22.2: the canonical owner theorem yields the upper Gaussian tail bound
directly. -/
private lemma standardNormalTailUpperBound
    {P : Measure Ω} {X : Ω → ℝ} (hX : HasLaw X (gaussianReal 0 1) P) {x : ℝ} (hx : 0 < x) :
    P.real (X ⁻¹' Set.Ici x) ≤ gaussianPDFReal 0 1 x / x := by
  -- Proof comment: transfer the standard-Gaussian upper-tail bound through the law of `X`.
  have hIci : P (X ⁻¹' Set.Ici x) = (gaussianReal 0 1) (Set.Ici x) :=
    (hX.identDistrib HasLaw.id).measure_mem_eq measurableSet_Ici
  have hpreimage : P.real (X ⁻¹' Set.Ici x) = (gaussianReal 0 1).real (Set.Ici x) := by
    simpa [measureReal_def] using congrArg ENNReal.toReal hIci
  rw [hpreimage]
  exact standardGaussianRealTailUpperBound hx

/-- Lemma 22.2: if `X` has law `gaussianReal 0 1` under `P`, then for every `x > 0` the right
tail probability `P[X ≥ x]` is bounded between the standard Gaussian Mills lower and upper
bounds. -/
theorem standardNormal_tail_bounds
    {P : Measure Ω} {X : Ω → ℝ} (hX : HasLaw X (gaussianReal 0 1) P) {x : ℝ} (hx : 0 < x) :
    gaussianPDFReal 0 1 x / (x + 1 / x) ≤ P.real (X ⁻¹' Set.Ici x) ∧
      P.real (X ⁻¹' Set.Ici x) ≤ gaussianPDFReal 0 1 x / x := by
  -- Proof comment: combine the already established lower and upper tail estimates.
  constructor
  · exact standardNormalTailLowerBound hX hx
  · exact standardNormalTailUpperBound hX hx

end HasLaw

end ProbabilityTheory
