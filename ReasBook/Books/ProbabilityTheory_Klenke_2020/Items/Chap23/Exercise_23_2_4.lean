/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib
import Books.ProbabilityTheory_Klenke_2020.Items.Chap23.Exercise_23_1_1

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory Topology

noncomputable section

universe u

namespace ProbabilityTheory

variable {Ω : Type u} [MeasurableSpace Ω]

/-- Helper for Exercise 23.2.4: the Legendre-Fenchel transform of the source-facing extended
logarithmic moment-generating function `Λ`. -/
noncomputable def legendreFenchelRateFunction (Λ : ℝ → EReal) (x : ℝ) : EReal :=
  sSup (Set.range fun t : ℝ ↦ ((t * x : ℝ) : EReal) - Λ t)

/-- Helper for Exercise 23.2.4: integrate against `expMeasure θ` by rewriting the measure through
its explicit real density. -/
private theorem integralExpMeasure_eq_integral_density {θ : ℝ} (hθ : 0 < θ) {f : ℝ → ℝ} :
    ∫ x, f x ∂expMeasure θ = ∫ x, exponentialPDFReal θ x * f x := by
  rw [expMeasure, gammaMeasure,
    integral_withDensity_eq_integral_toReal_smul (μ := volume) (f := gammaPDF 1 θ)
      (measurable_gammaPDFReal 1 θ).ennreal_ofReal
      (ae_of_all _ fun _ ↦ ENNReal.ofReal_lt_top)]
  refine integral_congr_ae ?_
  filter_upwards with x
  simp [gammaPDF, exponentialPDFReal, gammaPDFReal_nonneg zero_lt_one hθ x, smul_eq_mul]

/-- Helper for Exercise 23.2.4: the exponential-law moment-generating function equals
`θ / (θ - t)` on the half-line `t < θ`. -/
private theorem expMeasure_mgf_eq (θ : ℝ) (hθ : 0 < θ) {t : ℝ} (ht : t < θ) :
    mgf id (expMeasure θ) t = θ / (θ - t) := by
  have hneg : t - θ < 0 := sub_lt_zero.mpr ht
  rw [mgf, integralExpMeasure_eq_integral_density hθ]
  calc
    ∫ x, exponentialPDFReal θ x * Real.exp (t * x)
        = ∫ x, Set.indicator (Set.Ici (0 : ℝ))
            (fun y : ℝ ↦ θ * Real.exp ((t - θ) * y)) x := by
            refine integral_congr_ae ?_
            filter_upwards with x
            by_cases hx : 0 ≤ x
            · calc
                exponentialPDFReal θ x * Real.exp (t * x)
                    = (θ * Real.exp (-(θ * x))) * Real.exp (t * x) := by
                        simp [exponentialPDFReal, gammaPDFReal, hx]
                _ = θ * Real.exp ((t - θ) * x) := by
                        rw [mul_assoc, ← Real.exp_add]
                        congr 1
                        ring
                _ = Set.indicator (Set.Ici (0 : ℝ))
                      (fun y : ℝ ↦ θ * Real.exp ((t - θ) * y)) x := by
                        simp [hx]
            · simp [exponentialPDFReal, gammaPDFReal, hx]
    _ = ∫ x in Set.Ici (0 : ℝ), θ * Real.exp ((t - θ) * x) := by
          rw [integral_indicator measurableSet_Ici]
    _ = ∫ x in Set.Ioi (0 : ℝ), θ * Real.exp ((t - θ) * x) := by
          rw [integral_Ici_eq_integral_Ioi]
    _ = θ * ∫ x in Set.Ioi (0 : ℝ), Real.exp ((t - θ) * x) := by
          rw [integral_const_mul]
    _ = θ * (-(Real.exp ((t - θ) * 0)) / (t - θ)) := by
          rw [integral_exp_mul_Ioi hneg 0]
    _ = θ / (θ - t) := by
          have htne : t - θ ≠ 0 := by linarith
          have hdiv : -(Real.exp ((t - θ) * 0)) / (t - θ) = 1 / (θ - t) := by
            rw [mul_zero, Real.exp_zero]
            rw [show θ - t = -(t - θ) by ring]
            have hnegne : -(t - θ) ≠ 0 := by linarith
            field_simp [htne, hnegne]
          rw [hdiv, mul_one_div]

/-- Helper for Exercise 23.2.4: the boundary tilt `θ` is not exponentially integrable under
`expMeasure θ`. -/
private theorem expMeasure_boundary_not_mem_integrableExpSet (θ : ℝ) (hθ : 0 < θ) :
    θ ∉ integrableExpSet id (expMeasure θ) := by
  intro hθ_mem
  have hDensityInt :
      Integrable (fun x : ℝ ↦ Real.exp (θ * x) * (gammaPDF 1 θ x).toReal) volume := by
    rw [expMeasure, gammaMeasure] at hθ_mem
    exact
      (integrable_withDensity_iff (μ := volume)
        (f := gammaPDF 1 θ)
        (hf := (measurable_gammaPDFReal 1 θ).ennreal_ofReal)
        (hflt := ae_of_all _ fun _ ↦ ENNReal.ofReal_lt_top)).1 hθ_mem
  have hIndicatorInt : Integrable (Set.indicator (Set.Ici (0 : ℝ)) (fun _ : ℝ ↦ θ)) volume := by
    refine hDensityInt.congr ?_
    filter_upwards with x
    by_cases hx : 0 ≤ x
    · have hpdf : (gammaPDF 1 θ x).toReal = θ * Real.exp (-(θ * x)) := by
        have hgamma_nonneg :
            0 ≤ θ ^ (1 : ℝ) / Real.Gamma 1 * x ^ (1 - 1) * Real.exp (-(θ * x)) := by
          positivity
        simpa [gammaPDF, gammaPDFReal, hx, Real.Gamma_one] using
          (ENNReal.toReal_ofReal hgamma_nonneg)
      rw [hpdf]
      calc
        Real.exp (θ * x) * (θ * Real.exp (-(θ * x)))
            = θ * (Real.exp (θ * x) * Real.exp (-(θ * x))) := by ring
        _ = θ * Real.exp 0 := by
              rw [← Real.exp_add]
              congr 1
              ring
        _ = Set.indicator (Set.Ici (0 : ℝ)) (fun _ : ℝ ↦ θ) x := by
              simp [hx]
    · simp [gammaPDF, gammaPDFReal, hx]
  have hConstInt : IntegrableOn (fun _ : ℝ ↦ θ) (Set.Ici (0 : ℝ)) volume := by
    simpa [integrable_indicator_iff measurableSet_Ici] using hIndicatorInt
  have hFinite : volume (Set.Ici (0 : ℝ)) < ∞ := by
    have hConstIff :=
      (integrableOn_const_iff (show ‖θ‖ₑ ≠ ∞ by finiteness)
        (μ := volume) (s := Set.Ici (0 : ℝ)) (C := θ)).1 hConstInt
    rcases hConstIff with hzero | hfinite
    · exact (hθ.ne' <| by simpa using hzero).elim
    · exact hfinite
  simp [Real.volume_Ici] at hFinite

/-- Helper for Exercise 23.2.4: every tilt `t ≥ θ` lies outside
`integrableExpSet id (expMeasure θ)`. -/
private theorem expMeasure_not_mem_integrableExpSet_of_ge
    (θ : ℝ) (hθ : 0 < θ) {t : ℝ} (ht : θ ≤ t) :
    t ∉ integrableExpSet id (expMeasure θ) := by
  by_cases hteq : t = θ
  · simpa [hteq] using expMeasure_boundary_not_mem_integrableExpSet θ hθ
  intro ht_mem
  letI : IsProbabilityMeasure (expMeasure θ) := isProbabilityMeasure_expMeasure hθ
  have hzero_mem : (0 : ℝ) ∈ integrableExpSet id (expMeasure θ) := by
    simp [integrableExpSet]
  have hconv : Convex ℝ (integrableExpSet id (expMeasure θ)) := convex_integrableExpSet
  have ht_pos : 0 < t := lt_of_lt_of_le hθ ht
  have hratio_nonneg : 0 ≤ θ / t := by positivity
  have hratio_sub_nonneg : 0 ≤ 1 - θ / t := by
    have hratio_le_one : θ / t ≤ 1 := (div_le_iff₀ ht_pos).2 (by simpa using ht)
    linarith
  have htheta_mem' :
      (θ / t) • t + (1 - θ / t) • (0 : ℝ) ∈ integrableExpSet id (expMeasure θ) :=
    hconv ht_mem hzero_mem hratio_nonneg hratio_sub_nonneg (by ring)
  have hrepr : (θ / t) • t + (1 - θ / t) • (0 : ℝ) = θ := by
    have hmul : (θ / t) * t = θ := by
      field_simp [ht_pos.ne']
    calc
      (θ / t) • t + (1 - θ / t) • (0 : ℝ) = (θ / t) * t + (1 - θ / t) * 0 := by
        simp [smul_eq_mul]
      _ = θ := by simp [hmul]
  have htheta_mem : θ ∈ integrableExpSet id (expMeasure θ) := by
    rwa [hrepr] at htheta_mem'
  exact expMeasure_boundary_not_mem_integrableExpSet θ hθ htheta_mem

-- Helper for the source-facing rate formula below: evaluate the exponential moment of
-- `expMeasure θ` by the standard density integral on `(0, ∞)`, obtaining `θ / (θ - t)`, and then
-- pass to the chapter owner `extendedLogMomentGeneratingFunction`.
private theorem extendedLogMomentGeneratingFunction_id_expMeasure_of_lt
    {θ t : ℝ} (hθ : 0 < θ) (ht : t < θ) :
    Λ(id; expMeasure θ) t = Real.log (θ / (θ - t)) := by
  letI : IsProbabilityMeasure (expMeasure θ) := isProbabilityMeasure_expMeasure hθ
  have hmgf : mgf id (expMeasure θ) t = θ / (θ - t) :=
    expMeasure_mgf_eq θ hθ ht
  have hmgf_pos : 0 < mgf id (expMeasure θ) t := by
    rw [hmgf]
    exact div_pos hθ (sub_pos.mpr ht)
  have ht_mem : t ∈ integrableExpSet id (expMeasure θ) :=
    (mgf_pos_iff).1 hmgf_pos
  calc
    Λ(id; expMeasure θ) t = (cgf id (expMeasure θ) t : EReal) := by
      simpa using
        extendedLogMomentGeneratingFunction_eq_cgf_of_mem_integrableExpSet
          id (expMeasure θ) ht_mem
    _ = Real.log (θ / (θ - t)) := by
      rw [cgf, hmgf]

-- Helper for the source-facing rate formula below: when `t ≥ θ`, the exponential moment
-- diverges, so the chapter owner `extendedLogMomentGeneratingFunction` takes the value `∞`.
private theorem extendedLogMomentGeneratingFunction_id_expMeasure_of_ge
    {θ t : ℝ} (hθ : 0 < θ) (ht : θ ≤ t) :
    Λ(id; expMeasure θ) t = ⊤ := by
  simpa using
    extendedLogMomentGeneratingFunction_eq_top_of_not_mem_integrableExpSet
      id (expMeasure θ) (expMeasure_not_mem_integrableExpSet_of_ge θ hθ ht)

/-- Helper for Exercise 23.2.4: every admissible affine summand of the exponential-law Legendre
transform is bounded above by the textbook closed form on the positive branch. -/
private theorem expMeasureAffineSummand_le_closedForm
    {θ x t : ℝ} (hθ : 0 < θ) (hx : 0 < x) (ht : t < θ) :
    (((t * x : ℝ) : EReal) - Λ(id; expMeasure θ) t) ≤
      ((θ * x - Real.log (θ * x) - 1 : ℝ) : EReal) := by
  -- Proof comment: rewrite the summand with `y = x * (θ - t)`; then the claim is exactly
  -- `log y ≤ y - 1` for the positive quantity `y`.
  rw [extendedLogMomentGeneratingFunction_id_expMeasure_of_lt hθ ht]
  have hsub_pos : 0 < θ - t := sub_pos.mpr ht
  have hy : 0 < x * (θ - t) := mul_pos hx hsub_pos
  have hlog_mul : Real.log (x * (θ - t)) = Real.log x + Real.log (θ - t) := by
    rw [Real.log_mul hx.ne' hsub_pos.ne']
  have hlog_theta_x : Real.log (θ * x) = Real.log θ + Real.log x := by
    rw [Real.log_mul hθ.ne' hx.ne']
  have hdecomp :
      t * x - Real.log (θ / (θ - t)) =
        θ * x - Real.log (θ * x) + (Real.log (x * (θ - t)) - x * (θ - t)) := by
    rw [Real.log_div hθ.ne' hsub_pos.ne', hlog_mul, hlog_theta_x]
    ring
  have haux : Real.log (x * (θ - t)) - x * (θ - t) ≤ -1 := by
    linarith [Real.log_le_sub_one_of_pos hy]
  have hreal :
      t * x - Real.log (θ / (θ - t)) ≤ θ * x - Real.log (θ * x) - 1 := by
    linarith [hdecomp, haux]
  simpa using
    (show (((t * x - Real.log (θ / (θ - t)) : ℝ) : EReal)) ≤
        ((θ * x - Real.log (θ * x) - 1 : ℝ) : EReal) by
      exact_mod_cast hreal)

/-- Helper for Exercise 23.2.4: on `(-∞, 0]`, the exponential-law Legendre transform is `⊤`. -/
private theorem legendreFenchelRateFunction_id_expMeasure_eq_top_of_nonpos
    {θ x : ℝ} (hθ : 0 < θ) (hx : x ≤ 0) :
    legendreFenchelRateFunction (Λ(id; expMeasure θ)) x = ⊤ := by
  apply (EReal.eq_top_iff_forall_lt _).2
  intro y
  rw [legendreFenchelRateFunction]
  by_cases hx0 : x = 0
  · let t0 : ℝ := θ - θ * Real.exp (y + 1)
    have ht0 : t0 < θ := by
      -- Proof comment: the witness tilt stays in the admissible region because `exp (y + 1) > 0`.
      dsimp [t0]
      nlinarith [hθ, Real.exp_pos (y + 1)]
    have hmem :
        ((((t0 * x : ℝ) : EReal) - Λ(id; expMeasure θ) t0)) ∈
          Set.range (fun t : ℝ ↦ ((t * x : ℝ) : EReal) - Λ(id; expMeasure θ) t) :=
      ⟨t0, rfl⟩
    have hwitness :
        (y : EReal) < (((t0 * x : ℝ) : EReal) - Λ(id; expMeasure θ) t0) := by
      subst hx0
      rw [extendedLogMomentGeneratingFunction_id_expMeasure_of_lt hθ ht0]
      have hratio :
          θ / (θ - t0) = Real.exp (-(y + 1)) := by
        have hden : θ - t0 = θ * Real.exp (y + 1) := by
          dsimp [t0]
          ring
        rw [hden, Real.exp_neg]
        field_simp [hθ.ne', (Real.exp_pos (y + 1)).ne']
      have hreal : -Real.log (θ / (θ - t0)) = y + 1 := by
        rw [hratio, Real.log_exp]
        ring
      have hy_lt : (y : EReal) < ((y + 1 : ℝ) : EReal) := by
        exact_mod_cast (show y < y + 1 by linarith)
      have hrealE :
          (((-Real.log (θ / (θ - t0)) : ℝ) : EReal)) = ((y + 1 : ℝ) : EReal) :=
        congrArg (fun z : ℝ ↦ (z : EReal)) hreal
      simpa using
        (show (y : EReal) < (((-Real.log (θ / (θ - t0)) : ℝ) : EReal)) by
          rw [hrealE]
          exact hy_lt)
    exact lt_of_lt_of_le hwitness (le_sSup hmem)
  · have hxneg : x < 0 := lt_of_le_of_ne hx hx0
    obtain ⟨n, hn⟩ := exists_nat_gt (y / (-x))
    let t0 : ℝ := -(n : ℝ)
    have ht0 : t0 < θ := by
      -- Proof comment: every nonpositive tilt lies strictly below the positive rate parameter.
      dsimp [t0]
      linarith
    have hmem :
        ((((t0 * x : ℝ) : EReal) - Λ(id; expMeasure θ) t0)) ∈
          Set.range (fun t : ℝ ↦ ((t * x : ℝ) : EReal) - Λ(id; expMeasure θ) t) :=
      ⟨t0, rfl⟩
    have hwitness :
        (y : EReal) < (((t0 * x : ℝ) : EReal) - Λ(id; expMeasure θ) t0) := by
      rw [extendedLogMomentGeneratingFunction_id_expMeasure_of_lt hθ ht0]
      have hxpos : 0 < -x := by linarith
      have hlinear : y < (n : ℝ) * (-x) := by
        have hn' : y / (-x) < (n : ℝ) := by
          exact_mod_cast hn
        exact (div_lt_iff₀ hxpos).mp hn'
      have hratio_nonneg : 0 ≤ θ / (θ + n) := by positivity
      have hratio_le_one : θ / (θ + n) ≤ 1 := by
        have hden_pos : 0 < θ + n := by positivity
        exact (div_le_iff₀ hden_pos).2 (by nlinarith)
      have hlog_nonpos : Real.log (θ / (θ + n)) ≤ 0 :=
        Real.log_nonpos hratio_nonneg hratio_le_one
      have hsummand :
          y < (-(n : ℝ)) * x - Real.log (θ / (θ + n)) := by
        have hlinear' : y < (-(n : ℝ)) * x := by
          nlinarith
        linarith
      have hsummand' :
          y < t0 * x - Real.log (θ / (θ - t0)) := by
        simpa [t0] using hsummand
      exact_mod_cast hsummand'
    exact lt_of_lt_of_le hwitness (le_sSup hmem)

-- Proof sketch: split on `0 < x`; on the positive branch, substitute the explicit optimizer
-- `t = θ - 1 / x` into the Legendre transform of `Λ`, and on the nonpositive branch use that the
-- supremum diverges to `∞`.
/-- Exercise 23.2.4: for the exponential law with rate `θ`, the Legendre transform `Λ*` is
`x ↦ θ x - log (θ x) - 1` on `(0, ∞)` and `∞` on `(-∞, 0]`. -/
theorem legendreFenchelRateFunction_id_expMeasure_eq
    {θ x : ℝ} (hθ : 0 < θ) :
    legendreFenchelRateFunction (Λ(id; expMeasure θ)) x =
      if 0 < x then ((θ * x - Real.log (θ * x) - 1 : ℝ) : EReal) else ⊤ := by
  by_cases hx : 0 < x
  · rw [if_pos hx]
    apply le_antisymm
    · rw [legendreFenchelRateFunction]
      refine sSup_le ?_
      rintro _ ⟨t, rfl⟩
      by_cases ht : t < θ
      · exact expMeasureAffineSummand_le_closedForm hθ hx ht
      · -- Proof comment: once the tilt crosses `θ`, the exponential moment diverges and the
        -- corresponding affine summand drops to `⊥`.
        simp [extendedLogMomentGeneratingFunction_id_expMeasure_of_ge hθ (le_of_not_gt ht)]
    · rw [legendreFenchelRateFunction]
      let t0 : ℝ := θ - 1 / x
      have ht0 : t0 < θ := by
        -- Proof comment: the optimizer `θ - 1 / x` lies inside the admissible strip because
        -- `1 / x > 0`.
        dsimp [t0]
        have hxinv : 0 < 1 / x := one_div_pos.mpr hx
        linarith
      have hmem :
          ((((t0 * x : ℝ) : EReal) - Λ(id; expMeasure θ) t0)) ∈
            Set.range (fun t : ℝ ↦ ((t * x : ℝ) : EReal) - Λ(id; expMeasure θ) t) :=
        ⟨t0, rfl⟩
      have hEval :
          (((t0 * x : ℝ) : EReal) - Λ(id; expMeasure θ) t0) =
            ((θ * x - Real.log (θ * x) - 1 : ℝ) : EReal) := by
        rw [extendedLogMomentGeneratingFunction_id_expMeasure_of_lt hθ ht0]
        have hreal :
            t0 * x - Real.log (θ / (θ - t0)) = θ * x - Real.log (θ * x) - 1 := by
          dsimp [t0]
          rw [show θ - (θ - 1 / x) = 1 / x by ring]
          have hdiv : θ / (1 / x) = θ * x := by
            field_simp [hx.ne']
          rw [hdiv]
          have hlin : (θ - 1 / x) * x = θ * x - 1 := by
            field_simp [hx.ne']
          linarith
        simpa using congrArg (fun z : ℝ ↦ (z : EReal)) hreal
      have hsSup :
          (((t0 * x : ℝ) : EReal) - Λ(id; expMeasure θ) t0) ≤
            sSup (Set.range fun t : ℝ ↦ ((t * x : ℝ) : EReal) - Λ(id; expMeasure θ) t) :=
        le_sSup hmem
      rw [hEval] at hsSup
      exact hsSup
  · rw [if_neg hx]
    exact legendreFenchelRateFunction_id_expMeasure_eq_top_of_nonpos hθ (le_of_not_gt hx)

-- Proof sketch: on `(0, ∞)`, differentiate `x ↦ θ x - log (θ x) - 1` and solve
-- `θ - 1 / x = 0`, obtaining `x = 1 / θ`; strict convexity then shows this is the unique zero.
/-- The exponential-law Legendre transform has its unique zero at the mean `1 / θ` of `Exp(θ)`. -/
theorem legendreFenchelRateFunction_id_expMeasure_eq_zero_iff {θ x : ℝ} (hθ : 0 < θ) :
    legendreFenchelRateFunction (Λ(id; expMeasure θ)) x = 0 ↔ x = 1 / θ := by
  rw [legendreFenchelRateFunction_id_expMeasure_eq hθ]
  by_cases hx : 0 < x
  · rw [if_pos hx]
    constructor
    · intro hRate
      have hθx_pos : 0 < θ * x := mul_pos hθ hx
      by_cases hmul : θ * x = 1
      · have hdiv := congrArg (fun z : ℝ ↦ z / θ) hmul
        simpa [hθ.ne', mul_comm, mul_left_comm, mul_assoc] using hdiv
      · -- Proof comment: off the minimizer `θ x = 1`, the strict logarithmic inequality forces
        -- the explicit rate to be strictly positive, contradicting `Λ*(x) = 0`.
        have hstrict : Real.log (θ * x) < θ * x - 1 :=
          Real.log_lt_sub_one_of_pos hθx_pos hmul
        have hpos : 0 < θ * x - Real.log (θ * x) - 1 := by
          linarith
        have hposE : (0 : EReal) < ((θ * x - Real.log (θ * x) - 1 : ℝ) : EReal) := by
          exact_mod_cast hpos
        exfalso
        have : (0 : EReal) < 0 := by
          have hposE' := hposE
          simp [hRate] at hposE'
        exact (lt_irrefl (0 : EReal)) this
    · intro hx_mean
      rw [hx_mean]
      have hmul : θ * (1 / θ) = 1 := by
        field_simp [hθ.ne']
      rw [hmul]
      norm_num
  · rw [if_neg hx]
    constructor
    · intro hTop
      exfalso
      have htop : (⊤ : EReal) ≠ 0 := by simp
      exact htop hTop
    · intro hx_mean
      have hx_mean_pos : 0 < x := by
        rw [hx_mean]
        exact one_div_pos.mpr hθ
      exact (hx hx_mean_pos).elim

end ProbabilityTheory
