/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import ComputationalMethodsInverseProblems_Vogel_2002.Chap07.Prop_7_19.KernelMoment
public import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.Probability.Distributions.Beta

public section

open scoped KernelMoment.Notation

namespace KernelMoment

section

variable {p s : ℝ} {j : ℕ}

/-- Helper for Proposition 7.20: the normalized beta parameters are positive and sum to `j`. -/
lemma kernelMomentParametersPos
    (hs : 0 < s + 1) (hDecay : 0 < (j : ℝ) * p - s - 1) :
    0 < (j : ℝ) ∧
      0 < p ∧
      0 < (((j : ℝ) * p - s - 1) / p) ∧
      0 < ((s + 1) / p) ∧
      (((j : ℝ) * p - s - 1) / p) + ((s + 1) / p) = (j : ℝ) := by
  -- First exclude the degenerate case `j = 0`, which would contradict the two source inequalities.
  have hj_nat_ne : j ≠ 0 := by
    intro hj
    subst hj
    norm_num at hDecay
    linarith
  have hj_pos : 0 < (j : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero hj_nat_ne
  -- The two source inequalities imply `(j : ℝ) * p > 0`, hence `p > 0`.
  have hjp_pos : 0 < (j : ℝ) * p := by
    linarith
  have hp : 0 < p := by
    have : 0 < ((j : ℝ) * p) / (j : ℝ) := div_pos hjp_pos hj_pos
    simpa [hj_pos.ne'] using this
  have ha : 0 < (((j : ℝ) * p - s - 1) / p) := div_pos hDecay hp
  have hb : 0 < ((s + 1) / p) := div_pos hs hp
  -- The two normalized parameters telescope back to `j`.
  have hsum : (((j : ℝ) * p - s - 1) / p) + ((s + 1) / p) = (j : ℝ) := by
    calc
      (((j : ℝ) * p - s - 1) / p) + ((s + 1) / p)
          = (((j : ℝ) * p - s - 1) + (s + 1)) / p := by
              rw [← add_div]
      _ = ((j : ℝ) * p) / p := by ring
      _ = (j : ℝ) := by rw [mul_div_cancel_right₀ _ hp.ne']
  exact ⟨hj_pos, hp, ha, hb, hsum⟩

/-- Helper for Proposition 7.20: the `u ↦ u ^ p` substitution rewrites the kernel moment
integrand into the beta-prime integrand. -/
lemma kernelMomentRpowSubstitutionIntegrand
    (hp : 0 < p) {u : ℝ} (hu : 0 < u) :
    p * u ^ (p - 1) *
        ((1 / p) * ((u ^ p) ^ (((s + 1) / p) - 1) / (1 + u ^ p) ^ j)) =
      u ^ s / (1 + u ^ p) ^ j := by
  have hpow : (u ^ p) ^ (((s + 1) / p) - 1) = u ^ (s + 1 - p) := by
    calc
      (u ^ p) ^ (((s + 1) / p) - 1) = u ^ (p * (((s + 1) / p) - 1)) := by
        rw [← Real.rpow_mul hu.le]
      _ = u ^ (s + 1 - p) := by
        congr 1
        field_simp [hp.ne']
  have hcancel : p * (1 / p) = 1 := by
    field_simp [hp.ne']
  have hexp : u ^ (p - 1) * u ^ (s + 1 - p) = u ^ s := by
    rw [← Real.rpow_add hu]
    ring_nf
  -- After canceling the Jacobian factor, the exponents add up to the original power `s`.
  calc
    p * u ^ (p - 1) *
        ((1 / p) * ((u ^ p) ^ (((s + 1) / p) - 1) / (1 + u ^ p) ^ j))
        = p * u ^ (p - 1) * ((1 / p) * (u ^ (s + 1 - p) / (1 + u ^ p) ^ j)) := by
            rw [hpow]
    _ = (p * (1 / p)) * (u ^ (p - 1) * (u ^ (s + 1 - p) / (1 + u ^ p) ^ j)) := by ring
    _ = u ^ (p - 1) * (u ^ (s + 1 - p) / (1 + u ^ p) ^ j) := by rw [hcancel, one_mul]
    _ = (u ^ (p - 1) * u ^ (s + 1 - p)) / (1 + u ^ p) ^ j := by rw [mul_div_assoc]
    _ = u ^ s / (1 + u ^ p) ^ j := by rw [hexp]

/-- Helper for Proposition 7.20: the substitution `y ↦ y / (1 + y)` carries
`(0, ∞)` onto `(0, 1)`. -/
lemma betaPrimeSubstitutionImage :
    (fun y : ℝ ↦ y / (1 + y)) '' Set.Ioi (0 : ℝ) = Set.Ioo (0 : ℝ) 1 := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    have hy0 : 0 < y := hy
    have hy1 : 0 < 1 + y := by nlinarith
    constructor
    · exact div_pos hy0 hy1
    · exact (div_lt_one hy1).2 (by nlinarith)
  · intro hx
    have hx1 : 0 < 1 - x := sub_pos.mpr hx.2
    refine ⟨x / (1 - x), div_pos hx.1 hx1, ?_⟩
    have hx1_ne : 1 - x ≠ 0 := sub_ne_zero.mpr (ne_comm.mp hx.2.ne)
    field_simp [hx1_ne]
    ring

/-- Helper for Proposition 7.20: the `y ↦ y / (1 + y)` substitution rewrites the beta-prime
integrand into the beta integrand. -/
lemma betaPrimeSubstitutionIntegrand {a b y : ℝ} (hy : 0 < y) :
    (1 / (1 + y) ^ (2 : ℕ)) *
        ((y / (1 + y)) ^ (b - 1) * (1 - y / (1 + y)) ^ (a - 1)) =
      y ^ (b - 1) / (1 + y) ^ (a + b) := by
  have hy1 : 0 < 1 + y := by linarith
  have hone : 1 - y / (1 + y) = 1 / (1 + y) := by
    field_simp [hy1.ne']
    ring
  have hpow2 : 1 / (1 + y) ^ (2 : ℕ) = (1 + y) ^ (-2 : ℝ) := by
    rw [one_div, ← Real.rpow_natCast]
    simpa using (Real.rpow_neg hy1.le (2 : ℝ)).symm
  have hpowb : 1 / (1 + y) ^ (b - 1) = (1 + y) ^ (-(b - 1)) := by
    rw [one_div]
    simpa using (Real.rpow_neg hy1.le (b - 1)).symm
  have hpowa : 1 / (1 + y) ^ (a - 1) = (1 + y) ^ (-(a - 1)) := by
    rw [one_div]
    simpa using (Real.rpow_neg hy1.le (a - 1)).symm
  have hpowb' : ((1 + y) ^ (b - 1))⁻¹ = (1 + y) ^ (-(b - 1)) := by
    simpa [one_div] using hpowb
  have hpowa' : ((1 + y) ^ (a - 1))⁻¹ = (1 + y) ^ (-(a - 1)) := by
    simpa [one_div] using hpowa
  have honepow : (1 - y / (1 + y)) ^ (a - 1) = 1 / (1 + y) ^ (a - 1) := by
    rw [hone]
    simpa using (Real.div_rpow (show 0 ≤ (1 : ℝ) by positivity) hy1.le (a - 1))
  -- The Jacobian contributes `(1 + y)⁻²`, and the remaining powers collapse to `a + b`.
  calc
    (1 / (1 + y) ^ (2 : ℕ)) *
        ((y / (1 + y)) ^ (b - 1) * (1 - y / (1 + y)) ^ (a - 1))
        = (1 / (1 + y) ^ (2 : ℕ)) *
            ((y ^ (b - 1) / (1 + y) ^ (b - 1)) * (1 / (1 + y) ^ (a - 1))) := by
              rw [Real.div_rpow hy.le hy1.le, honepow]
    _ = (1 + y) ^ (-2 : ℝ) *
          (y ^ (b - 1) * ((1 + y) ^ (-(b - 1)) * (1 + y) ^ (-(a - 1)))) := by
            rw [hpow2, div_eq_mul_inv, hpowb', hpowa]
            ring
    _ = y ^ (b - 1) *
          ((1 + y) ^ (-2 : ℝ) * ((1 + y) ^ (-(b - 1)) * (1 + y) ^ (-(a - 1)))) := by
            ring
    _ = y ^ (b - 1) * (1 + y) ^ (-(a + b)) := by
          rw [← Real.rpow_add hy1, ← Real.rpow_add hy1]
          congr 1
          ring
    _ = y ^ (b - 1) / (1 + y) ^ (a + b) := by
          rw [div_eq_mul_inv, ← Real.rpow_neg hy1.le (a + b)]

/-- Helper for Proposition 7.20: the normalized beta-prime integral is the real part of the beta
integral. -/
lemma betaPrimeIntegral_eq_betaIntegralRe {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    (∫ y in Set.Ioi (0 : ℝ), y ^ (b - 1) / (1 + y) ^ (a + b)) =
      ((Complex.betaIntegral (a : ℂ) (b : ℂ)).re) := by
  have hf' :
      ∀ y ∈ Set.Ioi (0 : ℝ),
        HasDerivWithinAt (fun y : ℝ ↦ y / (1 + y)) (1 / (1 + y) ^ (2 : ℕ)) (Set.Ioi 0) y := by
    intro y hy
    have hy1_pos : 0 < 1 + y := by nlinarith [show 0 < y from hy]
    have hy1 : 1 + y ≠ 0 := hy1_pos.ne'
    -- Differentiate the rational substitution before simplifying its derivative.
    change HasDerivWithinAt (id / fun x : ℝ => 1 + x) (1 / (1 + y) ^ (2 : ℕ)) (Set.Ioi 0) y
    simpa [pow_two, hy1] using
      ((hasDerivAt_id y).div ((hasDerivAt_id y).const_add 1) hy1).hasDerivWithinAt
  have hmono : MonotoneOn (fun y : ℝ ↦ y / (1 + y)) (Set.Ioi (0 : ℝ)) := by
    intro x hx y hy hxy
    have hx1 : 0 < 1 + x := by nlinarith [show 0 < x from hx]
    have hy1 : 0 < 1 + y := by nlinarith [show 0 < y from hy]
    refine (div_le_div_iff₀ hx1 hy1).2 ?_
    nlinarith
  have hchange :=
    MeasureTheory.integral_image_eq_integral_deriv_smul_of_monotoneOn
      measurableSet_Ioi hf' hmono (fun x : ℝ ↦ x ^ (b - 1) * (1 - x) ^ (a - 1))
  -- Push the integral from `(0, ∞)` to `(0, 1)` using the explicit rational substitution.
  have hBetaDomain :
      (∫ y in Set.Ioi (0 : ℝ), y ^ (b - 1) / (1 + y) ^ (a + b)) =
        ∫ x in Set.Ioo (0 : ℝ) 1, x ^ (b - 1) * (1 - x) ^ (a - 1) := by
    calc
      (∫ y in Set.Ioi (0 : ℝ), y ^ (b - 1) / (1 + y) ^ (a + b))
          = ∫ y in Set.Ioi (0 : ℝ),
              (1 / (1 + y) ^ (2 : ℕ)) *
                ((y / (1 + y)) ^ (b - 1) * (1 - y / (1 + y)) ^ (a - 1)) := by
              refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi ?_
              intro y hy
              simpa [one_div] using
                (betaPrimeSubstitutionIntegrand (a := a) (b := b) (y := y) hy).symm
      _ = ∫ x in (fun y : ℝ ↦ y / (1 + y)) '' Set.Ioi (0 : ℝ),
            x ^ (b - 1) * (1 - x) ^ (a - 1) := by
            simpa [smul_eq_mul] using hchange.symm
      _ = ∫ x in Set.Ioo (0 : ℝ) 1, x ^ (b - 1) * (1 - x) ^ (a - 1) := by
            rw [betaPrimeSubstitutionImage]
  -- Finally compare the real beta integral to mathlib's canonical complex beta integral.
  calc
    (∫ y in Set.Ioi (0 : ℝ), y ^ (b - 1) / (1 + y) ^ (a + b))
        = ∫ x in Set.Ioo (0 : ℝ) 1, x ^ (b - 1) * (1 - x) ^ (a - 1) := hBetaDomain
    _ = ((Complex.betaIntegral (b : ℂ) (a : ℂ)).re) := by
          rw [Complex.betaIntegral, intervalIntegral.integral_of_le (by norm_num),
            ← MeasureTheory.integral_Ioc_eq_integral_Ioo, ← RCLike.re_to_complex, ← integral_re]
          · refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioc fun x hx ↦ ?_
            norm_cast
            rw [← Complex.ofReal_cpow, ← Complex.ofReal_cpow, RCLike.re_to_complex,
              Complex.re_mul_ofReal, Complex.ofReal_re]
            · have hx1 : 0 ≤ 1 - x := by nlinarith [hx.2]
              exact hx1
            · exact hx.1.le
          · convert Complex.betaIntegral_convergent (u := (b : ℂ)) (v := (a : ℂ))
              (by simpa) (by simpa)
            rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (by simp), MeasureTheory.IntegrableOn]
    _ = ((Complex.betaIntegral (a : ℂ) (b : ℂ)).re) := by
          rw [Complex.betaIntegral_symm]

/-- Helper for Proposition 7.20: the real part of the beta integral is the usual gamma ratio. -/
lemma betaIntegralRe_eq_realGammaRatio {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    ((Complex.betaIntegral (a : ℂ) (b : ℂ)).re) =
      (Real.Gamma a * Real.Gamma b) / Real.Gamma (a + b) := by
  -- Use the real-valued beta API, which already packages the complex-to-real rewrite.
  simpa [ProbabilityTheory.beta] using
    (ProbabilityTheory.beta_eq_betaIntegralReal a b ha hb).symm

/-- Helper for Proposition 7.20: `Γ(j)` agrees with `(j - 1)!` for positive integers `j`. -/
lemma realGammaNatCast_eq_factorialPred (hj : 0 < (j : ℝ)) :
    Real.Gamma (j : ℝ) = (Nat.factorial (j - 1) : ℝ) := by
  have hj_nat : 0 < j := by
    exact_mod_cast hj
  -- Rewrite `j` as `(j - 1) + 1` before applying the standard gamma identity.
  have hcast : (((Nat.pred j) + 1 : ℕ) : ℝ) = (j : ℝ) := by
    exact_mod_cast (Nat.succ_pred_eq_of_pos hj_nat)
  calc
    Real.Gamma (j : ℝ) = Real.Gamma (((Nat.pred j) + 1 : ℕ) : ℝ) := by rw [← hcast]
    _ = (Nat.factorial (Nat.pred j) : ℝ) := by
      simpa using Real.Gamma_nat_eq_factorial (Nat.pred j)
    _ = (Nat.factorial (j - 1) : ℝ) := by
      rw [Nat.pred_eq_sub_one]

/-- Proposition 7.20 (1). If `0 < s + 1` and `0 < (j : ℝ) * p - s - 1`, then
`I_{p,j}^s = (1 / p) * B(((j * p - s - 1) / p), ((s + 1) / p))`, written using
the canonical complex beta integral specialized at real arguments. -/
theorem integral_eq_betaIntegral
    (hs : 0 < s + 1) (hDecay : 0 < (j : ℝ) * p - s - 1) :
    I_{p, j}^{s} =
      (1 / p) *
        (Complex.betaIntegral
          ((((j : ℝ) * p - s - 1) / p : ℝ) : ℂ)
          (((s + 1) / p : ℝ) : ℂ)).re := by
  set a : ℝ := (((j : ℝ) * p - s - 1) / p)
  set b : ℝ := ((s + 1) / p)
  rcases kernelMomentParametersPos (p := p) (s := s) (j := j) hs hDecay with
    ⟨hj_pos, hp, ha_raw, hb_raw, hsum_raw⟩
  have ha : 0 < a := by simpa [a] using ha_raw
  have hb : 0 < b := by simpa [b] using hb_raw
  have hsum : a + b = (j : ℝ) := by simpa [a, b] using hsum_raw
  -- First normalize the improper integral with `y = u ^ p`.
  calc
    I_{p, j}^{s}
        = (1 / p) * ∫ y in Set.Ioi (0 : ℝ), y ^ (b - 1) / (1 + y) ^ j := by
            rw [KernelMoment.integral_def]
            have hrewrite :
                (∫ x in Set.Ioi (0 : ℝ), KernelMoment.integrand p j s x) =
                  ∫ x in Set.Ioi (0 : ℝ),
                    p * x ^ (p - 1) * ((1 / p) * ((x ^ p) ^ (b - 1) / (1 + x ^ p) ^ j)) := by
                  refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi ?_
                  intro x hx
                  rw [KernelMoment.integrand_def]
                  simpa [b, mul_assoc] using
                    (kernelMomentRpowSubstitutionIntegrand (p := p) (s := s) (j := j) hp hx).symm
            rw [hrewrite]
            have hcomp :
                ∫ x in Set.Ioi (0 : ℝ),
                    p * x ^ (p - 1) * ((1 / p) * ((x ^ p) ^ (b - 1) / (1 + x ^ p) ^ j)) =
                  ∫ y in Set.Ioi (0 : ℝ), (1 / p) * (y ^ (b - 1) / (1 + y) ^ j) := by
                    simpa [smul_eq_mul, mul_assoc] using
                      (MeasureTheory.integral_comp_rpow_Ioi_of_pos (p := p)
                        (g := fun y ↦ (1 / p) * (y ^ (b - 1) / (1 + y) ^ j)) hp)
            rw [hcomp, MeasureTheory.integral_const_mul]
    -- Then rewrite the normalized beta-prime integral using the beta substitution.
    _ = (1 / p) * ∫ y in Set.Ioi (0 : ℝ), y ^ (b - 1) / (1 + y) ^ (a + b) := by
          congr 1
          refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi ?_
          intro y hy
          change y ^ (b - 1) / ((1 + y) ^ j : ℝ) = y ^ (b - 1) / (1 + y) ^ (a + b)
          have hpow : ((1 + y) ^ j : ℝ) = (1 + y) ^ (a + b) := by
            rw [← Real.rpow_natCast (1 + y) j, ← hsum]
          rw [hpow]
    _ = (1 / p) * (Complex.betaIntegral (a : ℂ) (b : ℂ)).re := by
          rw [betaPrimeIntegral_eq_betaIntegralRe ha hb]
    _ = (1 / p) *
          (Complex.betaIntegral
            ((((j : ℝ) * p - s - 1) / p : ℝ) : ℂ)
            (((s + 1) / p : ℝ) : ℂ)).re := by
          simp [a, b]

/-- The gamma-ratio form of Proposition 7.20, matching mathlib's canonical
`Complex.betaIntegral_eq_Gamma_mul_div` API after specializing to the kernel
moment parameters under the same positivity hypotheses. -/
theorem integral_eq_gamma_mul_gamma_div_gamma
    (hs : 0 < s + 1) (hDecay : 0 < (j : ℝ) * p - s - 1) :
    I_{p, j}^{s} =
      (Real.Gamma (((j : ℝ) * p - s - 1) / p) * Real.Gamma ((s + 1) / p)) /
        (p * Real.Gamma (j : ℝ)) := by
  set a : ℝ := (((j : ℝ) * p - s - 1) / p)
  set b : ℝ := ((s + 1) / p)
  rcases kernelMomentParametersPos (p := p) (s := s) (j := j) hs hDecay with
    ⟨hj_pos, hp, ha_raw, hb_raw, hsum_raw⟩
  have ha : 0 < a := by simpa [a] using ha_raw
  have hb : 0 < b := by simpa [b] using hb_raw
  have hsum : a + b = (j : ℝ) := by simpa [a, b] using hsum_raw
  have hGamma_ne : Real.Gamma (a + b) ≠ 0 := by
    exact (Real.Gamma_pos_of_pos (hsum ▸ hj_pos)).ne'
  -- Reuse the beta-integral form, then simplify the beta factor with the gamma identity.
  calc
    I_{p, j}^{s} = (1 / p) * (Complex.betaIntegral (a : ℂ) (b : ℂ)).re := by
      simpa [a, b] using integral_eq_betaIntegral (p := p) (s := s) (j := j) hs hDecay
    _ = (1 / p) * ((Real.Gamma a * Real.Gamma b) / Real.Gamma (a + b)) := by
      rw [betaIntegralRe_eq_realGammaRatio ha hb]
    _ = (Real.Gamma a * Real.Gamma b) / (p * Real.Gamma (a + b)) := by
      field_simp [hp.ne', hGamma_ne]
    _ = (Real.Gamma (((j : ℝ) * p - s - 1) / p) * Real.Gamma ((s + 1) / p)) /
          (p * Real.Gamma (j : ℝ)) := by
      simp [a, b, hsum]

/-- Proposition 7.20 (2). Rewriting the gamma-ratio form with
`Real.Gamma (j : ℝ) = (Nat.factorial (j - 1) : ℝ)` gives the source-facing
factorial denominator. -/
theorem integral_eq_gamma_mul_gamma_div_factorial
    (hs : 0 < s + 1) (hDecay : 0 < (j : ℝ) * p - s - 1) :
    I_{p, j}^{s} =
      (Real.Gamma (((j : ℝ) * p - s - 1) / p) * Real.Gamma ((s + 1) / p)) /
        (p * (Nat.factorial (j - 1) : ℝ)) := by
  rcases kernelMomentParametersPos (p := p) (s := s) (j := j) hs hDecay with
    ⟨hj_pos, hp, ha, hb, hsum⟩
  -- Only the denominator changes: replace `Γ(j)` by the factorial formula.
  calc
    I_{p, j}^{s}
        = (Real.Gamma (((j : ℝ) * p - s - 1) / p) * Real.Gamma ((s + 1) / p)) /
            (p * Real.Gamma (j : ℝ)) := by
              exact integral_eq_gamma_mul_gamma_div_gamma (p := p) (s := s) (j := j) hs hDecay
    _ = (Real.Gamma (((j : ℝ) * p - s - 1) / p) * Real.Gamma ((s + 1) / p)) /
          (p * (Nat.factorial (j - 1) : ℝ)) := by
            rw [realGammaNatCast_eq_factorialPred (j := j) hj_pos]

end

end KernelMoment

end
