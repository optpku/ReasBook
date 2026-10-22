/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open Filter MeasureTheory ProbabilityTheory Set
open scoped ProbabilityTheory ENNReal Topology

noncomputable section

namespace ProbabilityTheory

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The integrability domain `integrableExpSet X P` has a local classical decider for the `if`
expressions used in the source-facing `Λ` definition. -/
local instance integrableExpSetMemDecidable
    (X : Ω → ℝ) (P : Measure Ω) (t : ℝ) :
    Decidable (t ∈ integrableExpSet X P) :=
  Classical.decPred _ t

/-- The extended logarithmic moment-generating function `Λ(X; P)`, equal to `cgf X P` on the
exponential-integrability domain and `⊤` outside it. -/
noncomputable def extendedLogMomentGeneratingFunction
    (X : Ω → ℝ) (P : Measure Ω) (t : ℝ) : EReal :=
  if t ∈ integrableExpSet X P then
    (cgf X P t : EReal)
  else
    ⊤

scoped[ProbabilityTheory] notation "Λ(" X "; " P ")" => extendedLogMomentGeneratingFunction X P

/-- On the effective domain, `Λ(X; P)` agrees with the ordinary cumulant-generating function. -/
theorem extendedLogMomentGeneratingFunction_eq_cgf_of_mem_integrableExpSet
    (X : Ω → ℝ) (P : Measure Ω) {t : ℝ} (ht : t ∈ integrableExpSet X P) :
    Λ(X; P) t = (cgf X P t : EReal) := by
  -- Proof comment: unfold the definition and simplify the `if` with the domain membership.
  simp [extendedLogMomentGeneratingFunction, ht]

/-- Outside the effective domain, `Λ(X; P)` takes the value `⊤`. -/
theorem extendedLogMomentGeneratingFunction_eq_top_of_not_mem_integrableExpSet
    (X : Ω → ℝ) (P : Measure Ω) {t : ℝ} (ht : t ∉ integrableExpSet X P) :
    Λ(X; P) t = ⊤ := by
  -- Proof comment: unfold the definition and simplify the `if` with the excluded parameter.
  simp [extendedLogMomentGeneratingFunction, ht]

end ProbabilityTheory

/-- The normalizing constant
`c = ∫ exp (-|x|) / (1 + |x|^3) dx`
appearing in Exercise 23.1.1. -/
noncomputable def exercise2311NormalizationConstant : ℝ :=
  ∫ x : ℝ, Real.exp (-|x|) / (1 + |x| ^ (3 : ℕ)) ∂volume

/-- The textbook density
`x ↦ c⁻¹ exp (-|x|) / (1 + |x|^3)`
from Exercise 23.1.1. -/
noncomputable def exercise2311Density (x : ℝ) : ℝ :=
  exercise2311NormalizationConstant⁻¹ * Real.exp (-|x|) / (1 + |x| ^ (3 : ℕ))

/-- The probability law on `ℝ` whose density is
`x ↦ c⁻¹ exp (-|x|) / (1 + |x|^3)` with respect to Lebesgue measure. -/
noncomputable def exercise2311Measure : Measure ℝ :=
  volume.withDensity (fun x ↦ ENNReal.ofReal (exercise2311Density x))

/-- Helper for Exercise 23.1.1: the unnormalized Lebesgue-density profile
`x ↦ exp (-|x|) / (1 + |x|^3)`. -/
noncomputable def exercise2311BaseIntegrand (x : ℝ) : ℝ :=
  Real.exp (-|x|) / (1 + |x| ^ (3 : ℕ))

/-- Helper for Exercise 23.1.1: the base integrand is continuous on `ℝ`. -/
lemma exercise2311BaseIntegrand_continuous : Continuous exercise2311BaseIntegrand := by
  -- Proof comment: both numerator and denominator are continuous, and the denominator never
  -- vanishes because it is at least `1`.
  unfold exercise2311BaseIntegrand
  refine Continuous.div ?_ ?_ ?_
  · fun_prop
  · fun_prop
  · intro x
    positivity

/-- Helper for Exercise 23.1.1: the base integrand is integrable on `ℝ`. -/
lemma exercise2311BaseIntegrand_integrable : Integrable exercise2311BaseIntegrand := by
  -- Proof comment: split at the origin and compare each side with a pure exponential tail.
  rw [← integrableOn_univ, ← Iic_union_Ioi, integrableOn_union]
  constructor
  · refine Integrable.mono' (integrableOn_exp_mul_Iic (a := 1) zero_lt_one 0) ?_ ?_
    · exact exercise2311BaseIntegrand_continuous.stronglyMeasurable.aestronglyMeasurable
    · filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Iic] with x hx
      have hx_le : x ≤ 0 := hx
      have hdenom_pos : 0 < 1 + |x| ^ (3 : ℕ) := by positivity
      have hdenom_ge : (1 : ℝ) ≤ 1 + |x| ^ (3 : ℕ) := by
        nlinarith [pow_nonneg (abs_nonneg x) (3 : ℕ)]
      have hexp_nonneg : 0 ≤ Real.exp x := by positivity
      have hdiv :
          Real.exp x / (1 + |x| ^ (3 : ℕ)) ≤ Real.exp x := by
        refine (div_le_iff₀ hdenom_pos).2 ?_
        nlinarith
      have hnonneg : 0 ≤ exercise2311BaseIntegrand x := by
        exact div_nonneg (by positivity) (by positivity)
      calc
        |exercise2311BaseIntegrand x| = exercise2311BaseIntegrand x := abs_of_nonneg hnonneg
        _ = Real.exp x / (1 + |x| ^ (3 : ℕ)) := by
              simp [exercise2311BaseIntegrand, abs_of_nonpos hx_le]
        _ ≤ Real.exp x := hdiv
        _ = Real.exp (1 * x) := by simp
  · refine Integrable.mono' (integrableOn_exp_mul_Ioi (a := -1) (by norm_num) 0) ?_ ?_
    · exact exercise2311BaseIntegrand_continuous.stronglyMeasurable.aestronglyMeasurable
    · filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Ioi] with x hx
      have hx_pos : 0 < x := hx
      have hdenom_pos : 0 < 1 + |x| ^ (3 : ℕ) := by positivity
      have hdenom_ge : (1 : ℝ) ≤ 1 + |x| ^ (3 : ℕ) := by
        nlinarith [pow_nonneg (abs_nonneg x) (3 : ℕ)]
      have hexp_nonneg : 0 ≤ Real.exp (-x) := by positivity
      have hdiv :
          Real.exp (-x) / (1 + |x| ^ (3 : ℕ)) ≤ Real.exp (-x) := by
        refine (div_le_iff₀ hdenom_pos).2 ?_
        nlinarith
      have hnonneg : 0 ≤ exercise2311BaseIntegrand x := by
        exact div_nonneg (by positivity) (by positivity)
      calc
        |exercise2311BaseIntegrand x| = exercise2311BaseIntegrand x := abs_of_nonneg hnonneg
        _ = Real.exp (-x) / (1 + |x| ^ (3 : ℕ)) := by
              simp [exercise2311BaseIntegrand, abs_of_pos hx_pos]
        _ ≤ Real.exp (-x) := hdiv
        _ = Real.exp (-1 * x) := by ring_nf

/-- Helper for Exercise 23.1.1: the normalizing constant `c` is strictly positive. -/
lemma exercise2311NormalizationConstant_pos : 0 < exercise2311NormalizationConstant := by
  -- Proof comment: the base integrand is everywhere positive, hence its integral over Lebesgue
  -- measure is strictly positive.
  change 0 < ∫ x, exercise2311BaseIntegrand x ∂volume
  have hnonneg : ∀ x : ℝ, 0 ≤ exercise2311BaseIntegrand x := by
    intro x
    exact div_nonneg (by positivity) (by positivity)
  have hsupport : Function.support exercise2311BaseIntegrand = Set.univ := by
    ext x
    simp [exercise2311BaseIntegrand, Function.mem_support,
      show Real.exp (-|x|) ≠ 0 by positivity,
      show (1 + |x| ^ (3 : ℕ)) ≠ 0 by positivity]
  rw [MeasureTheory.integral_pos_iff_support_of_nonneg hnonneg
    exercise2311BaseIntegrand_integrable, hsupport]
  simp

/-- Helper for Exercise 23.1.1: the normalized density is pointwise nonnegative. -/
lemma exercise2311Density_nonneg (x : ℝ) : 0 ≤ exercise2311Density x := by
  -- Proof comment: all three factors in the density are nonnegative, and the normalization
  -- constant is strictly positive.
  unfold exercise2311Density
  exact div_nonneg
    (mul_nonneg (inv_nonneg.mpr exercise2311NormalizationConstant_pos.le) (by positivity))
    (by positivity)

/-- Helper for Exercise 23.1.1: the normalized density is integrable on `ℝ`. -/
lemma exercise2311Density_integrable : Integrable exercise2311Density := by
  -- Proof comment: the density is a constant multiple of the already integrable base integrand.
  convert
      (exercise2311BaseIntegrand_integrable.const_mul exercise2311NormalizationConstant⁻¹) using 1
  ext x
  rw [exercise2311Density, exercise2311BaseIntegrand, mul_div_assoc]

/-- Helper for Exercise 23.1.1: the normalized density is continuous on `ℝ`. -/
lemma exercise2311Density_continuous : Continuous exercise2311Density := by
  -- Proof comment: `exercise2311Density` is the fixed normalization constant times the continuous
  -- base profile.
  have hdensity :
      exercise2311Density = fun x ↦
        exercise2311NormalizationConstant⁻¹ * exercise2311BaseIntegrand x := by
    funext x
    rw [exercise2311Density, exercise2311BaseIntegrand, mul_div_assoc]
  rw [hdensity]
  exact exercise2311BaseIntegrand_continuous.const_mul exercise2311NormalizationConstant⁻¹

/-- Helper for Exercise 23.1.1: the normalized density is measurable as a real-valued function. -/
lemma exercise2311Density_measurable : Measurable exercise2311Density :=
  exercise2311Density_continuous.measurable

/-- Helper for Exercise 23.1.1: the normalized density is the normalization constant times the
unnormalized base profile. -/
lemma exercise2311Density_eq_const_mul_base (x : ℝ) :
    exercise2311Density x =
      exercise2311NormalizationConstant⁻¹ * exercise2311BaseIntegrand x := by
  -- Proof comment: isolate the fixed scalar normalization from the explicit base profile.
  rw [exercise2311Density, exercise2311BaseIntegrand, mul_div_assoc]

/-- Helper for Exercise 23.1.1: the density is even. -/
lemma exercise2311Density_neg_eq (x : ℝ) :
    exercise2311Density (-x) = exercise2311Density x := by
  -- Proof comment: the only `x`-dependence is through `|x|`.
  simp [exercise2311Density, abs_neg]

-- Proof sketch: the density is nonnegative and integrates to `1` by the choice of the
-- normalizing constant `exercise2311NormalizationConstant`, so the weighted Lebesgue measure is a
-- probability measure.
/-- The law defined by `exercise2311Measure` is a probability measure. -/
theorem exercise2311Measure_isProbabilityMeasure :
    IsProbabilityMeasure exercise2311Measure := by
  refine ⟨?_⟩
  -- Proof comment: rewrite the total mass as the integral of the density and evaluate the
  -- normalization factor explicitly.
  rw [exercise2311Measure, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
  have hnonneg : 0 ≤ᵐ[volume] exercise2311Density :=
    Filter.Eventually.of_forall exercise2311Density_nonneg
  rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal exercise2311Density_integrable hnonneg]
  have hnorm_ne : exercise2311NormalizationConstant ≠ 0 :=
    exercise2311NormalizationConstant_pos.ne'
  have hmass : ∫ x, exercise2311Density x ∂volume = 1 := by
    -- Proof comment: `exercise2311Density = c⁻¹ • exercise2311BaseIntegrand`, so the integral is
    -- `c⁻¹ * c`.
    have hdensity :
        exercise2311Density = fun x ↦
          exercise2311NormalizationConstant⁻¹ * exercise2311BaseIntegrand x := by
      funext x
      rw [exercise2311Density, exercise2311BaseIntegrand, mul_div_assoc]
    calc
      ∫ x, exercise2311Density x ∂volume
          = exercise2311NormalizationConstant⁻¹ * ∫ x, exercise2311BaseIntegrand x ∂volume := by
              rw [hdensity, integral_const_mul]
      _ = exercise2311NormalizationConstant⁻¹ * exercise2311NormalizationConstant := by
              simp [exercise2311NormalizationConstant, exercise2311BaseIntegrand]
      _ = 1 := by
              field_simp [hnorm_ne]
  simp [hmass]

/-- `exercise2311Measure` carries its canonical probability-measure instance. -/
instance : IsProbabilityMeasure exercise2311Measure :=
  exercise2311Measure_isProbabilityMeasure

/-- Helper for Exercise 23.1.1: reflecting the law across `x ↦ -x` leaves it unchanged. -/
lemma exercise2311Measure_map_neg :
    exercise2311Measure.map (fun x : ℝ ↦ -x) = exercise2311Measure := by
  -- Proof comment: rewrite both measures through `withDensity`, then use the evenness of the
  -- density together with the invariance of Lebesgue measure under reflection.
  let hpres : MeasurePreserving (fun x : ℝ ↦ -x) volume volume :=
    Measure.measurePreserving_neg (volume : Measure ℝ)
  ext s hs
  rw [exercise2311Measure, Measure.map_apply measurable_neg hs, withDensity_apply _ hs,
    withDensity_apply _ ((by fun_prop : Measurable (fun x : ℝ ↦ -x)) hs)]
  calc
    ∫⁻ x in (fun x : ℝ ↦ -x) ⁻¹' s, ENNReal.ofReal (exercise2311Density x) ∂volume
        =
          ∫⁻ x in (fun x : ℝ ↦ -x) ⁻¹' s, ENNReal.ofReal (exercise2311Density (-x)) ∂volume := by
            refine lintegral_congr_ae ?_
            filter_upwards with x
            exact congrArg ENNReal.ofReal (exercise2311Density_neg_eq x).symm
    _ = ∫⁻ x in s, ENNReal.ofReal (exercise2311Density x) ∂volume := by
          simpa using
            hpres.setLIntegral_comp_preimage hs exercise2311Density_measurable.ennreal_ofReal

/-- Helper for Exercise 23.1.1: integrability under `exercise2311Measure` is equivalent to
Lebesgue integrability against the explicit base density. -/
lemma exercise2311_integrableExp_transport {t : ℝ} :
    t ∈ integrableExpSet id exercise2311Measure ↔
      Integrable (fun x : ℝ ↦ Real.exp (t * x) * exercise2311BaseIntegrand x) volume := by
  -- Proof comment: first transport integrability through `withDensity`, then remove the fixed
  -- normalization constant using the explicit density/base-profile rewrite.
  change Integrable (fun x : ℝ ↦ Real.exp (t * x)) exercise2311Measure ↔ _
  rw [exercise2311Measure]
  have hdensity_lt_top :
      ∀ᵐ x ∂volume, ENNReal.ofReal (exercise2311Density x) < ∞ := by
    filter_upwards with x
    simp
  have htransport :
      Integrable (fun x : ℝ ↦ Real.exp (t * x))
          (volume.withDensity fun x ↦ ENNReal.ofReal (exercise2311Density x)) ↔
        Integrable (fun x : ℝ ↦ Real.exp (t * x) * exercise2311Density x) volume := by
    simpa [exercise2311Density_nonneg, mul_comm, mul_left_comm, mul_assoc] using
      (MeasureTheory.integrable_withDensity_iff
        (μ := volume)
        (f := fun x ↦ ENNReal.ofReal (exercise2311Density x))
        exercise2311Density_measurable.ennreal_ofReal
        hdensity_lt_top
        (g := fun x : ℝ ↦ Real.exp (t * x)))
  rw [htransport]
  have hconst_unit : IsUnit exercise2311NormalizationConstant⁻¹ :=
    IsUnit.mk0 _ (inv_ne_zero exercise2311NormalizationConstant_pos.ne')
  have hrewrite :
      (fun x : ℝ ↦ Real.exp (t * x) * exercise2311Density x) =
        fun x : ℝ ↦
          exercise2311NormalizationConstant⁻¹ *
            (Real.exp (t * x) * exercise2311BaseIntegrand x) := by
    funext x
    rw [exercise2311Density_eq_const_mul_base]
    ring
  rw [hrewrite]
  simpa using
    (integrable_const_mul_iff hconst_unit
      (fun x : ℝ ↦ Real.exp (t * x) * exercise2311BaseIntegrand x) (μ := volume))

/-- Helper for Exercise 23.1.1: the positive-half-line envelope `x ↦ (1 + x^3)⁻¹` is integrable
on `Set.Ioi 0`. -/
lemma exercise2311InvCubicEnvelope_integrableOn_pos :
    IntegrableOn (fun x : ℝ ↦ 1 / (1 + x ^ (3 : ℕ))) (Set.Ioi 0) := by
  -- Proof comment: split the half-line into the compact core `(0, 1]` and the tail `(1, ∞)`.
  have hcore : IntegrableOn (fun x : ℝ ↦ 1 / (1 + x ^ (3 : ℕ))) (Set.Icc (0 : ℝ) 1) := by
    -- Proof comment: on the compact interval, continuity is enough.
    have hcont :
        ContinuousOn (fun x : ℝ ↦ 1 / (1 + x ^ (3 : ℕ))) (Set.Icc (0 : ℝ) 1) := by
      refine ContinuousOn.div continuousOn_const ?_ ?_
      · fun_prop
      · intro x
        intro hx
        have hx_nonneg : 0 ≤ x := hx.1
        positivity
    exact hcont.integrableOn_compact isCompact_Icc
  have hcore' : IntegrableOn (fun x : ℝ ↦ 1 / (1 + x ^ (3 : ℕ))) (Set.Ioc (0 : ℝ) 1) := by
    -- Proof comment: removing the left endpoint does not change integrability for Lebesgue
    -- measure.
    exact (integrableOn_Icc_iff_integrableOn_Ioc : _).1 hcore
  have htailModel : IntegrableOn (fun x : ℝ ↦ 1 / x ^ (3 : ℕ)) (Set.Ioi (1 : ℝ)) := by
    -- Proof comment: the tail is dominated by the integrable power `x ↦ x⁻³`.
    have hrpow : IntegrableOn (fun x : ℝ ↦ x ^ (-(3 : ℝ))) (Set.Ioi (1 : ℝ)) := by
      simpa using
        integrableOn_Ioi_rpow_of_lt (a := -(3 : ℝ)) (c := (1 : ℝ)) (by norm_num) zero_lt_one
    refine hrpow.congr_fun ?_ measurableSet_Ioi
    intro x hx
    have hx_pos : 0 < x := lt_trans zero_lt_one hx
    simpa [one_div, Real.rpow_natCast] using
      (Real.rpow_neg (le_of_lt hx_pos) (3 : ℝ))
  have htail : IntegrableOn (fun x : ℝ ↦ 1 / (1 + x ^ (3 : ℕ))) (Set.Ioi (1 : ℝ)) := by
    -- Proof comment: compare `(1 + x^3)⁻¹` with `x⁻³` on `x > 1`.
    change Integrable (fun x : ℝ ↦ 1 / (1 + x ^ (3 : ℕ))) (volume.restrict (Set.Ioi (1 : ℝ)))
    refine Integrable.mono' htailModel ?_ ?_
    · have hcont :
          ContinuousOn (fun x : ℝ ↦ 1 / (1 + x ^ (3 : ℕ))) (Set.Ioi (1 : ℝ)) := by
        refine ContinuousOn.div continuousOn_const ?_ ?_
        · fun_prop
        · intro x hx
          have hx_pos : 0 < x := lt_trans zero_lt_one hx
          have hpow_nonneg : 0 ≤ x ^ (3 : ℕ) := by
            exact pow_nonneg hx_pos.le _
          have hden_pos : 0 < 1 + x ^ (3 : ℕ) := by
            nlinarith
          exact hden_pos.ne'
      exact hcont.aestronglyMeasurable measurableSet_Ioi
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
      have hx_gt_one : 1 < x := hx
      have hx_pos : 0 < x := lt_trans zero_lt_one hx_gt_one
      have hpow_pos : 0 < x ^ (3 : ℕ) := by positivity
      have hden_ge : x ^ (3 : ℕ) ≤ 1 + x ^ (3 : ℕ) := by linarith
      have hle : 1 / (1 + x ^ (3 : ℕ)) ≤ 1 / x ^ (3 : ℕ) := by
        exact one_div_le_one_div_of_le hpow_pos hden_ge
      have hden_pos : 0 < 1 + x ^ (3 : ℕ) := by
        have hpow_nonneg : 0 ≤ x ^ (3 : ℕ) := by positivity
        nlinarith
      have hleft_nonneg : 0 ≤ 1 / (1 + x ^ (3 : ℕ)) := by
        exact one_div_nonneg.mpr hden_pos.le
      have hright_nonneg : 0 ≤ 1 / x ^ (3 : ℕ) := by positivity
      simpa [Real.norm_eq_abs, abs_of_nonneg hleft_nonneg, abs_of_nonneg hright_nonneg,
        abs_of_nonneg hden_pos.le] using hle
  have hsplit :
      Set.Ioi (0 : ℝ) = Set.Ioc (0 : ℝ) 1 ∪ Set.Ioi (1 : ℝ) := by
    ext x
    constructor
    · intro hx
      by_cases hx1 : x ≤ 1
      · exact Or.inl ⟨hx, hx1⟩
      · exact Or.inr (lt_of_not_ge hx1)
    · intro hx
      rcases hx with hx | hx
      · exact hx.1
      · have hx_one : 1 < x := hx
        exact lt_trans zero_lt_one hx_one
  rw [hsplit]
  exact IntegrableOn.union hcore' htail

/-- Helper for Exercise 23.1.1: the polynomial envelope `(1 + |x|^3)⁻¹` is integrable on `ℝ`. -/
lemma exercise2311InvCubicEnvelope_integrable :
    Integrable (fun x : ℝ ↦ 1 / (1 + |x| ^ (3 : ℕ))) := by
  -- Proof comment: first upgrade the positive-half-line estimate to `Ici 0`, then transport it
  -- across `x ↦ -x` using the invariance of Lebesgue measure under reflection.
  have hposIci :
      IntegrableOn (fun x : ℝ ↦ 1 / (1 + |x| ^ (3 : ℕ))) (Set.Ici (0 : ℝ)) := by
    -- Proof comment: adding the single endpoint `0` does not change integrability.
    rw [integrableOn_Ici_iff_integrableOn_Ioi
      (f := fun x : ℝ ↦ 1 / (1 + |x| ^ (3 : ℕ))) (b := (0 : ℝ)) (by simp)]
    refine exercise2311InvCubicEnvelope_integrableOn_pos.congr_fun ?_ measurableSet_Ioi
    intro x hx
    have hx_pos : 0 < x := hx
    simp [abs_of_pos hx_pos]
  rw [← integrableOn_univ, ← Iic_union_Ioi, integrableOn_union]
  constructor
  · -- Proof comment: reflect the positive-side `Ici 0` result to the negative side.
    have hnegIic :
        IntegrableOn (fun x : ℝ ↦ 1 / (1 + |x| ^ (3 : ℕ))) (Set.Iic (0 : ℝ)) := by
      rw [← Measure.map_neg_eq_self (volume : Measure ℝ)]
      let m : MeasurableEmbedding (fun x : ℝ ↦ -x) := (Homeomorph.neg ℝ).measurableEmbedding
      rw [m.integrableOn_map_iff]
      have hpreimage :
          (fun x : ℝ ↦ -x) ⁻¹' Set.Iic (0 : ℝ) = Set.Ici (0 : ℝ) := by
        ext x
        simp
      rw [hpreimage]
      simpa only [Function.comp_def, abs_neg] using hposIci
    exact hnegIic
  · -- Proof comment: on the positive side, `|x| = x`.
    refine exercise2311InvCubicEnvelope_integrableOn_pos.congr_fun ?_ measurableSet_Ioi
    intro x hx
    have hx_pos : 0 < x := hx
    simp [abs_of_pos hx_pos]

/-- Helper for Exercise 23.1.1: every parameter with `|t| ≤ 1` belongs to the exponential
integrability domain. -/
lemma exercise2311_mem_integrableExpSet_of_abs_le_one {t : ℝ} (ht : |t| ≤ 1) :
    t ∈ integrableExpSet id exercise2311Measure := by
  -- Proof comment: after transporting back to Lebesgue measure, `|t| ≤ 1` gives
  -- `exp (t x) exp (-|x|) ≤ 1`, so the exponential integrand is dominated by the fixed inverse
  -- cubic envelope.
  refine (exercise2311_integrableExp_transport).2 ?_
  refine Integrable.mono' exercise2311InvCubicEnvelope_integrable ?_ ?_
  · exact
      ((((continuous_const.mul continuous_id).rexp).mul
        exercise2311BaseIntegrand_continuous)).aestronglyMeasurable
  · filter_upwards with x
    have htx_le_abs : t * x ≤ |x| := by
      calc
        t * x ≤ |t * x| := le_abs_self _
        _ = |t| * |x| := by rw [abs_mul]
        _ ≤ 1 * |x| := by gcongr
        _ = |x| := by ring
    have hExpBound :
        Real.exp (t * x) * Real.exp (-|x|) ≤ 1 := by
      have hExpLe : Real.exp (t * x) ≤ Real.exp |x| := Real.exp_le_exp.mpr htx_le_abs
      calc
        Real.exp (t * x) * Real.exp (-|x|)
            ≤ Real.exp |x| * Real.exp (-|x|) := by
              gcongr
        _ = 1 := by
              rw [← Real.exp_add]
              ring_nf
              simp
    have hdenom_nonneg : 0 ≤ ((1 + |x| ^ (3 : ℕ))⁻¹ : ℝ) := by positivity
    have hnonneg :
        0 ≤ Real.exp (t * x) * exercise2311BaseIntegrand x := by
      exact mul_nonneg (by positivity) (div_nonneg (by positivity) (by positivity))
    calc
      |Real.exp (t * x) * exercise2311BaseIntegrand x|
          = Real.exp (t * x) * exercise2311BaseIntegrand x := abs_of_nonneg hnonneg
      _ = (Real.exp (t * x) * Real.exp (-|x|)) * (1 + |x| ^ (3 : ℕ))⁻¹ := by
            rw [exercise2311BaseIntegrand, div_eq_mul_inv]
            ring
      _ ≤ 1 * (1 + |x| ^ (3 : ℕ))⁻¹ := by
            exact mul_le_mul_of_nonneg_right hExpBound hdenom_nonneg
      _ = 1 / (1 + |x| ^ (3 : ℕ)) := by
            rw [one_mul, one_div]

/-- Helper for Exercise 23.1.1: the exponential-integrability domain is symmetric under
`t ↦ -t`. -/
lemma exercise2311_mem_integrableExpSet_neg_iff (t : ℝ) :
    (-t) ∈ integrableExpSet id exercise2311Measure ↔
      t ∈ integrableExpSet id exercise2311Measure := by
  -- Proof comment: transport the integrability statement through the reflected measure, then use
  -- the invariance of `exercise2311Measure`.
  change Integrable (fun x : ℝ ↦ Real.exp ((-t) * x)) exercise2311Measure ↔
    Integrable (fun x : ℝ ↦ Real.exp (t * x)) exercise2311Measure
  constructor
  · intro ht
    have hmap :
        Integrable (fun x : ℝ ↦ Real.exp ((-t) * x))
          (exercise2311Measure.map (fun x : ℝ ↦ -x)) := by
      simpa [exercise2311Measure_map_neg] using ht
    have hcomp :
        Integrable (fun x : ℝ ↦ Real.exp ((-t) * (-x))) exercise2311Measure :=
      (integrable_map_equiv (μ := exercise2311Measure) (MeasurableEquiv.neg ℝ)
        (fun x : ℝ ↦ Real.exp ((-t) * x))).1 hmap
    simpa [neg_mul, mul_comm, mul_left_comm, mul_assoc] using hcomp
  · intro ht
    have hmap :
        Integrable (fun x : ℝ ↦ Real.exp (t * x))
          (exercise2311Measure.map (fun x : ℝ ↦ -x)) := by
      simpa [exercise2311Measure_map_neg] using ht
    have hcomp :
        Integrable (fun x : ℝ ↦ Real.exp (t * (-x))) exercise2311Measure :=
      (integrable_map_equiv (μ := exercise2311Measure) (MeasurableEquiv.neg ℝ)
        (fun x : ℝ ↦ Real.exp (t * x))).1 hmap
    simpa [neg_mul, mul_comm, mul_left_comm, mul_assoc] using hcomp

/-- Helper for Exercise 23.1.1: when `t > 1`, the exponential factor
`exp ((t - 1) x) / x^2` is eventually at least `2` along the positive tail. -/
lemma exercise2311_expSubOneMul_divSq_eventually_ge_two {t : ℝ} (ht : 1 < t) :
    ∀ᶠ x in Filter.atTop, 2 ≤ Real.exp ((t - 1) * x) / x ^ (2 : ℝ) := by
  -- Proof comment: the standard exponential-vs-polynomial asymptotic tends to `+∞`, so any
  -- fixed lower bound such as `2` eventually holds.
  exact
    (tendsto_exp_mul_div_rpow_atTop 2 (t - 1) (sub_pos.mpr ht)).eventually_ge_atTop 2

/-- Helper for Exercise 23.1.1: on a sufficiently far positive tail, the explicit transported
integrand dominates `x ↦ x⁻¹` whenever `t > 1`. -/
lemma exercise2311_tailLowerBoundOnIoi {t : ℝ} (ht : 1 < t) :
    ∃ R : ℝ, 1 ≤ R ∧ ∀ ⦃x : ℝ⦄, x ∈ Set.Ioi R →
      x⁻¹ ≤ Real.exp (t * x) * exercise2311BaseIntegrand x := by
  -- Proof comment: combine the eventual exponential lower bound with `1 + x^3 ≤ 2x^3`.
  rcases (eventually_atTop.1 (exercise2311_expSubOneMul_divSq_eventually_ge_two ht)) with
    ⟨R, hR⟩
  refine ⟨max R 1, le_max_right _ _, ?_⟩
  intro x hx
  have hxR : R ≤ x := le_trans (le_max_left _ _) hx.le
  have hx1 : 1 ≤ x := le_trans (le_max_right _ _) hx.le
  have hx_pos : 0 < x := lt_of_lt_of_le zero_lt_one hx1
  have hEvent : 2 ≤ Real.exp ((t - 1) * x) / (x ^ (2 : ℕ) : ℝ) := by
    simpa [Real.rpow_natCast] using hR x hxR
  have hExpLower : (2 : ℝ) * x ^ (2 : ℕ) ≤ Real.exp ((t - 1) * x) := by
    exact (le_div_iff₀ (by positivity : 0 < (x ^ (2 : ℕ) : ℝ))).1 hEvent
  have hx3_ge_one : (1 : ℝ) ≤ x ^ (3 : ℕ) := by
    exact one_le_pow₀ hx1
  have hDenUpper : 1 + x ^ (3 : ℕ) ≤ 2 * x ^ (3 : ℕ) := by
    nlinarith
  have hMulBound : (1 + x ^ (3 : ℕ)) * x⁻¹ ≤ Real.exp ((t - 1) * x) := by
    have hCore : (1 + x ^ (3 : ℕ)) * x⁻¹ ≤ 2 * x ^ (2 : ℕ) := by
      field_simp [ne_of_gt hx_pos]
      nlinarith
    exact le_trans hCore hExpLower
  have hQuot :
      x⁻¹ ≤ Real.exp ((t - 1) * x) / (1 + x ^ (3 : ℕ)) := by
    refine (le_div_iff₀ (by positivity : 0 < 1 + x ^ (3 : ℕ))).2 ?_
    simpa [mul_comm, mul_left_comm, mul_assoc] using hMulBound
  have hrewrite :
      Real.exp (t * x) * exercise2311BaseIntegrand x =
        Real.exp ((t - 1) * x) / (1 + x ^ (3 : ℕ)) := by
    calc
      Real.exp (t * x) * exercise2311BaseIntegrand x
          = (Real.exp (t * x) * Real.exp (-x)) / (1 + x ^ (3 : ℕ)) := by
              simp [exercise2311BaseIntegrand, abs_of_pos hx_pos, div_eq_mul_inv, mul_assoc]
      _ = Real.exp ((t - 1) * x) / (1 + x ^ (3 : ℕ)) := by
            congr 1
            rw [← Real.exp_add]
            congr 1
            ring
  simpa [hrewrite] using hQuot

/-- Helper for Exercise 23.1.1: no parameter `t > 1` belongs to the exponential-integrability
domain. -/
lemma exercise2311_not_mem_integrableExpSet_of_one_lt {t : ℝ} (ht : 1 < t) :
    t ∉ integrableExpSet id exercise2311Measure := by
  -- Proof comment: after transport to Lebesgue measure, the positive tail dominates `x ↦ x⁻¹`,
  -- whose integral over `Ioi R` diverges.
  intro ht_mem
  have hInt :
      Integrable (fun x : ℝ ↦ Real.exp (t * x) * exercise2311BaseIntegrand x) volume :=
    (exercise2311_integrableExp_transport).1 ht_mem
  rcases exercise2311_tailLowerBoundOnIoi ht with ⟨R, hR_le, hR⟩
  have hInv : IntegrableOn (fun x : ℝ ↦ x⁻¹) (Set.Ioi R) := by
    -- Proof comment: the tail lower bound upgrades integrability of the explicit density to
    -- integrability of the non-integrable comparison function.
    change Integrable (fun x : ℝ ↦ x⁻¹) (volume.restrict (Set.Ioi R))
    refine Integrable.mono' (hInt.restrict) measurable_inv.aestronglyMeasurable ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    have hbound : x⁻¹ ≤ Real.exp (t * x) * exercise2311BaseIntegrand x := hR hx
    have hx_nonneg : 0 ≤ x := by
      exact le_trans (by norm_num : (0 : ℝ) ≤ 1) (hR_le.trans hx.le)
    have hleft_nonneg : 0 ≤ x⁻¹ := inv_nonneg.mpr hx_nonneg
    have hright_nonneg : 0 ≤ Real.exp (t * x) * exercise2311BaseIntegrand x := by
      exact mul_nonneg (by positivity) (div_nonneg (by positivity) (by positivity))
    simpa [Real.norm_eq_abs, abs_inv, abs_of_nonneg hx_nonneg,
      abs_of_nonneg hright_nonneg] using hbound
  exact not_integrableOn_Ioi_inv hInv

-- Proof sketch: for this density, the positive tail of `exp (t x)` is controlled by
-- `exp ((t - 1) x) / x^3` and the negative tail by `exp (-(t + 1) x) / x^3`; both are integrable
-- exactly for `t ∈ [-1, 1]`, and the boundary values `t = ±1` remain integrable because
-- `x ↦ x⁻³` is integrable at infinity.
-- Route correction: the inner inclusion now comes from the global dominator
-- `x ↦ (1 + |x|^3)⁻¹`, so only the outer tail obstruction `|t| > 1` remains.
-- TODO: use `exercise2311_integrableExp_transport` and an eventual lower bound against `x ↦ 1 / x`
-- on a far tail to show that no `|t| > 1` can belong to the domain.
/-- The exponential-integrability domain for the law of Exercise 23.1.1 is exactly `[-1, 1]`. -/
theorem exercise2311_integrableExpSet :
    integrableExpSet id exercise2311Measure = Icc (-1 : ℝ) 1 := by
  ext t
  constructor
  · intro ht
    -- Proof comment: the inner inclusion is already known, so only the tail obstructions
    -- `t > 1` and `t < -1` need to be excluded.
    have ht_upper : t ≤ 1 := by
      by_contra hcontra
      exact exercise2311_not_mem_integrableExpSet_of_one_lt (lt_of_not_ge hcontra) ht
    have ht_lower : -1 ≤ t := by
      by_contra hcontra
      have hneg_mem : -t ∈ integrableExpSet id exercise2311Measure :=
        (exercise2311_mem_integrableExpSet_neg_iff t).2 ht
      have hneg_gt : 1 < -t := by linarith
      exact exercise2311_not_mem_integrableExpSet_of_one_lt hneg_gt hneg_mem
    simpa [Set.mem_Icc] using And.intro ht_lower ht_upper
  · intro ht
    -- Proof comment: the polynomial envelope lemma gives the whole inner inclusion at once.
    have ht_abs : |t| ≤ 1 := by
      simpa [abs_le, Set.mem_Icc] using ht
    exact exercise2311_mem_integrableExpSet_of_abs_le_one ht_abs

-- Proof sketch: specialize the chapter owner theorem
-- `extendedLogMomentGeneratingFunction_eq_cgf_of_mem_integrableExpSet` to `id` and
-- `exercise2311Measure`.
/-- On its effective domain, the extended logarithmic moment-generating function of
Exercise 23.1.1 agrees with the ordinary cumulant-generating function `cgf`. -/
theorem exercise2311LogMomentGeneratingFunction_eq_cgf_of_mem_integrableExpSet {t : ℝ}
    (ht : t ∈ integrableExpSet id exercise2311Measure) :
    Λ(id; exercise2311Measure) t = (cgf id exercise2311Measure t : EReal) := by
  simpa using
    extendedLogMomentGeneratingFunction_eq_cgf_of_mem_integrableExpSet
      id exercise2311Measure ht

-- Proof sketch: specialize the chapter owner theorem
-- `extendedLogMomentGeneratingFunction_eq_top_of_not_mem_integrableExpSet` to `id` and
-- `exercise2311Measure`.
/-- Outside its effective domain, the extended logarithmic moment-generating function of
Exercise 23.1.1 is `⊤`. -/
theorem exercise2311LogMomentGeneratingFunction_eq_top_of_not_mem_integrableExpSet {t : ℝ}
    (ht : t ∉ integrableExpSet id exercise2311Measure) :
    Λ(id; exercise2311Measure) t = ⊤ := by
  simpa using
    extendedLogMomentGeneratingFunction_eq_top_of_not_mem_integrableExpSet
      id exercise2311Measure ht

-- Proof sketch: the density is even, so replacing `x` by `-x` leaves the law invariant and turns
-- the exponential moment at `t` into the exponential moment at `-t`. Taking logarithms preserves
-- the resulting symmetry.
/-- The logarithmic moment-generating function of Exercise 23.1.1 is even. -/
theorem exercise2311LogMomentGeneratingFunction_neg_eq (t : ℝ) :
    Λ(id; exercise2311Measure) (-t) = Λ(id; exercise2311Measure) t := by
  by_cases ht : t ∈ integrableExpSet id exercise2311Measure
  · have hneg : (-t) ∈ integrableExpSet id exercise2311Measure :=
      (exercise2311_mem_integrableExpSet_neg_iff t).2 ht
    have hmgf :
        mgf id exercise2311Measure (-t) = mgf id exercise2311Measure t := by
      calc
        mgf id exercise2311Measure (-t)
            = mgf id (exercise2311Measure.map (fun x : ℝ ↦ -x)) (-t) := by
                rw [exercise2311Measure_map_neg]
        _ = mgf (fun x : ℝ ↦ -x) exercise2311Measure (-t) := by
              simpa using congrFun
                (ProbabilityTheory.mgf_id_map
                  (μ := exercise2311Measure)
                  (X := fun x : ℝ ↦ -x)
                  ((by fun_prop : AEMeasurable (fun x : ℝ ↦ -x) exercise2311Measure))) (-t)
        _ = mgf id exercise2311Measure t := by
              simpa using
                (ProbabilityTheory.mgf_neg
                  (X := (id : ℝ → ℝ))
                  (μ := exercise2311Measure)
                  (t := -t))
    rw [exercise2311LogMomentGeneratingFunction_eq_cgf_of_mem_integrableExpSet hneg,
      exercise2311LogMomentGeneratingFunction_eq_cgf_of_mem_integrableExpSet ht]
    simp [ProbabilityTheory.cgf, hmgf]
  · have hneg : (-t) ∉ integrableExpSet id exercise2311Measure := by
      intro hneg
      exact ht ((exercise2311_mem_integrableExpSet_neg_iff t).1 hneg)
    rw [exercise2311LogMomentGeneratingFunction_eq_top_of_not_mem_integrableExpSet hneg,
      exercise2311LogMomentGeneratingFunction_eq_top_of_not_mem_integrableExpSet ht]

-- Proof sketch: because `exercise2311Measure` is a probability measure, the moment-generating
-- function at `t = 0` is `1`; hence its logarithm is `0`.
/-- At the origin, the logarithmic moment-generating function of Exercise 23.1.1 equals `0`. -/
theorem exercise2311LogMomentGeneratingFunction_zero :
    Λ(id; exercise2311Measure) 0 = 0 := by
  have hzero_mem : (0 : ℝ) ∈ integrableExpSet id exercise2311Measure := by
    -- Proof comment: at `t = 0`, the exponential integrand is the constant function `1`.
    simp [integrableExpSet]
  -- Proof comment: on the effective domain, `Λ` agrees with `cgf`, and `cgf` vanishes at the
  -- origin for every probability measure.
  rw [exercise2311LogMomentGeneratingFunction_eq_cgf_of_mem_integrableExpSet hzero_mem]
  simp

/-- Helper for Exercise 23.1.1: the two endpoint exponential moments provide an integrable
dominator for parameters in `[-1, 1]`. -/
lemma exercise2311_endpointDominator_integrable :
    Integrable (fun x : ℝ ↦ Real.exp x + Real.exp (-x)) exercise2311Measure := by
  -- Proof comment: the endpoint parameters `t = ±1` are already known to lie in the effective
  -- domain, so their integrands add to the desired dominator.
  have hpos : (1 : ℝ) ∈ integrableExpSet id exercise2311Measure :=
    exercise2311_mem_integrableExpSet_of_abs_le_one (by simp)
  have hneg : (-1 : ℝ) ∈ integrableExpSet id exercise2311Measure :=
    exercise2311_mem_integrableExpSet_of_abs_le_one (by simp)
  have hExpPos : Integrable (fun x : ℝ ↦ Real.exp x) exercise2311Measure := by
    simpa [integrableExpSet] using hpos
  have hExpNeg : Integrable (fun x : ℝ ↦ Real.exp (-x)) exercise2311Measure := by
    simpa [integrableExpSet] using hneg
  exact hExpPos.add hExpNeg

/-- Helper for Exercise 23.1.1: the moment-generating function tends to its endpoint values along
the one-sided filters `𝓝[≤] 1` and `𝓝[≥] (-1)`. -/
lemma exercise2311Tendsto_mgf_endpoints :
    Tendsto (fun t : ℝ ↦ mgf id exercise2311Measure t) (𝓝[≤] (1 : ℝ))
      (𝓝 (mgf id exercise2311Measure 1)) ∧
    Tendsto (fun t : ℝ ↦ mgf id exercise2311Measure t) (𝓝[≥] (-1 : ℝ))
      (𝓝 (mgf id exercise2311Measure (-1))) := by
  -- Proof comment: dominated convergence applies on both one-sided endpoint filters with the
  -- common majorant `exp x + exp (-x)`.
  have hPointwiseBound {t x : ℝ} (ht : |t| ≤ 1) :
      ‖Real.exp (t * x)‖ ≤ Real.exp x + Real.exp (-x) := by
    have htx_le_abs : t * x ≤ |x| := by
      calc
        t * x ≤ |t * x| := le_abs_self _
        _ = |t| * |x| := by rw [abs_mul]
        _ ≤ 1 * |x| := by gcongr
        _ = |x| := by ring
    have hExpLe : Real.exp (t * x) ≤ Real.exp |x| := Real.exp_le_exp.mpr htx_le_abs
    cases le_or_gt 0 x with
    | inl hx_nonneg =>
        calc
          ‖Real.exp (t * x)‖ = Real.exp (t * x) := by
              rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
          _ ≤ Real.exp |x| := hExpLe
          _ = Real.exp x := by simp [abs_of_nonneg hx_nonneg]
          _ ≤ Real.exp x + Real.exp (-x) := by
              exact le_add_of_nonneg_right (by positivity)
    | inr hx_neg =>
        calc
          ‖Real.exp (t * x)‖ = Real.exp (t * x) := by
              rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
          _ ≤ Real.exp |x| := hExpLe
          _ = Real.exp (-x) := by simp [abs_of_nonpos hx_neg.le]
          _ ≤ Real.exp x + Real.exp (-x) := by
              exact le_add_of_nonneg_left (by positivity)
  constructor
  · -- Proof comment: near `1` inside `Iic 1`, the parameter stays in `[-1,1]`.
    have hMeas :
        ∀ᶠ t in 𝓝[≤] (1 : ℝ),
          AEStronglyMeasurable (fun x : ℝ ↦ Real.exp (t * x)) exercise2311Measure := by
      exact Eventually.of_forall fun t =>
        ((((continuous_const.mul continuous_id).rexp) :
          Continuous (fun x : ℝ ↦ Real.exp (t * x))).aestronglyMeasurable)
    have hBound :
        ∀ᶠ t in 𝓝[≤] (1 : ℝ),
          ∀ᵐ x ∂exercise2311Measure, ‖Real.exp (t * x)‖ ≤ Real.exp x + Real.exp (-x) := by
      have hIcc :
          ∀ᶠ t in 𝓝[≤] (1 : ℝ), t ∈ Set.Icc (-1 : ℝ) 1 := by
        exact Icc_mem_nhdsLE (a := (-1 : ℝ)) (b := (1 : ℝ)) (by norm_num)
      filter_upwards [hIcc] with t htIcc
      have ht_abs : |t| ≤ 1 := by
        simpa [abs_le, Set.mem_Icc] using htIcc
      filter_upwards with x
      exact hPointwiseBound ht_abs
    have hLim :
        ∀ᵐ x ∂exercise2311Measure,
          Tendsto (fun t : ℝ ↦ Real.exp (t * x)) (𝓝[≤] (1 : ℝ)) (𝓝 (Real.exp (1 * x))) := by
      filter_upwards with x
      have hCont : Continuous (fun t : ℝ ↦ Real.exp (t * x)) := by
        fun_prop
      exact (hCont.continuousAt.tendsto).mono_left inf_le_left
    simpa [ProbabilityTheory.mgf, one_mul] using
      (MeasureTheory.tendsto_integral_filter_of_dominated_convergence
        (μ := exercise2311Measure)
        (bound := fun x : ℝ ↦ Real.exp x + Real.exp (-x))
        hMeas hBound exercise2311_endpointDominator_integrable hLim)
  · -- Proof comment: the left endpoint is the mirrored dominated-convergence argument.
    have hMeas :
        ∀ᶠ t in 𝓝[≥] (-1 : ℝ),
          AEStronglyMeasurable (fun x : ℝ ↦ Real.exp (t * x)) exercise2311Measure := by
      exact Eventually.of_forall fun t =>
        ((((continuous_const.mul continuous_id).rexp) :
          Continuous (fun x : ℝ ↦ Real.exp (t * x))).aestronglyMeasurable)
    have hBound :
        ∀ᶠ t in 𝓝[≥] (-1 : ℝ),
          ∀ᵐ x ∂exercise2311Measure, ‖Real.exp (t * x)‖ ≤ Real.exp x + Real.exp (-x) := by
      have hIcc :
          ∀ᶠ t in 𝓝[≥] (-1 : ℝ), t ∈ Set.Icc (-1 : ℝ) 1 := by
        exact Icc_mem_nhdsGE (a := (-1 : ℝ)) (b := (1 : ℝ)) (by norm_num)
      filter_upwards [hIcc] with t htIcc
      have ht_abs : |t| ≤ 1 := by
        simpa [abs_le, Set.mem_Icc] using htIcc
      filter_upwards with x
      exact hPointwiseBound ht_abs
    have hLim :
        ∀ᵐ x ∂exercise2311Measure,
          Tendsto (fun t : ℝ ↦ Real.exp (t * x)) (𝓝[≥] (-1 : ℝ)) (𝓝 (Real.exp ((-1) * x))) := by
      filter_upwards with x
      have hCont : Continuous (fun t : ℝ ↦ Real.exp (t * x)) := by
        fun_prop
      exact (hCont.continuousAt.tendsto).mono_left inf_le_left
    simpa [ProbabilityTheory.mgf] using
      (MeasureTheory.tendsto_integral_filter_of_dominated_convergence
        (μ := exercise2311Measure)
        (bound := fun x : ℝ ↦ Real.exp x + Real.exp (-x))
        hMeas hBound exercise2311_endpointDominator_integrable hLim)

/-- Helper for Exercise 23.1.1: the moment-generating function is left-continuous at the right
endpoint `t = 1`. -/
lemma exercise2311ContinuousWithinAt_mgf_rightEndpoint :
    ContinuousWithinAt (fun t : ℝ ↦ mgf id exercise2311Measure t) (Set.Iic (1 : ℝ)) 1 := by
  -- Proof comment: `ContinuousWithinAt` is exactly the one-sided `Tendsto` statement.
  simpa using exercise2311Tendsto_mgf_endpoints.1

/-- Helper for Exercise 23.1.1: the moment-generating function is right-continuous at the left
endpoint `t = -1`. -/
lemma exercise2311ContinuousWithinAt_mgf_leftEndpoint :
    ContinuousWithinAt (fun t : ℝ ↦ mgf id exercise2311Measure t) (Set.Ici (-1 : ℝ)) (-1) := by
  -- Proof comment: this is the second component of the one-sided endpoint `Tendsto` lemma.
  simpa using exercise2311Tendsto_mgf_endpoints.2

-- Proof sketch: on `[-1, 1]`, identify `Λ` with `cgf id exercise2311Measure` and use the tail
-- bounds above plus dominated convergence to obtain continuity up to the endpoints. Global
-- continuity fails because `Λ (±1)` is finite while `Λ t = ⊤` immediately outside the interval.
-- TODO: combine the exact domain theorem with the evenness theorem; use `analyticOn_cgf` on
-- `Ioo (-1) 1`, prove one-sided continuity at `±1`, then separate the finite endpoint values from
-- the `⊤` values on every neighborhood crossing outside `[-1, 1]`.
/-- Exercise 23.1.1: the logarithmic moment-generating function for the density
`x ↦ c⁻¹ exp (-|x|) / (1 + |x|^3)` is continuous on its effective domain `[-1, 1]`, but it is not
continuous on all of `ℝ` because it jumps to `⊤` outside that interval. -/
theorem exercise2311LogMomentGeneratingFunction_continuity_answer :
    ContinuousOn (Λ(id; exercise2311Measure)) (integrableExpSet id exercise2311Measure) ∧
      ¬ Continuous (Λ(id; exercise2311Measure)) := by
  constructor
  · -- Proof comment: after identifying the effective domain with `[-1,1]`, treat interior points
    -- analytically and the endpoints by one-sided continuity of `mgf` and `log`.
    rw [exercise2311_integrableExpSet]
    intro t ht
    have hEqOn :
        ∀ y ∈ Set.Icc (-1 : ℝ) 1,
          Λ(id; exercise2311Measure) y = (cgf id exercise2311Measure y : EReal) := by
      intro y hy
      exact exercise2311LogMomentGeneratingFunction_eq_cgf_of_mem_integrableExpSet
        (by simpa [exercise2311_integrableExpSet] using hy)
    by_cases hRight : t = 1
    · subst hRight
      have hMem : (1 : ℝ) ∈ integrableExpSet id exercise2311Measure := by
        simpa [exercise2311_integrableExpSet]
      have hInt :
          Integrable (fun x : ℝ ↦ Real.exp (1 * x)) exercise2311Measure := by
        simpa [integrableExpSet] using hMem
      have hMgf :
          ContinuousWithinAt (fun t : ℝ ↦ mgf id exercise2311Measure t)
            (Set.Icc (-1 : ℝ) 1) 1 := by
        simpa [ContinuousWithinAt, nhdsWithin_Icc_eq_nhdsLE
          (a := (-1 : ℝ)) (b := (1 : ℝ)) (by norm_num)] using
          exercise2311ContinuousWithinAt_mgf_rightEndpoint
      have hCgf :
          ContinuousWithinAt (fun t : ℝ ↦ cgf id exercise2311Measure t)
            (Set.Icc (-1 : ℝ) 1) 1 := by
        -- Proof comment: `cgf = log ∘ mgf`, and `mgf` stays positive at the endpoint.
        simpa [ProbabilityTheory.cgf] using hMgf.log (ProbabilityTheory.mgf_pos hInt).ne'
      have hEReal :
          ContinuousWithinAt (fun t : ℝ ↦ (cgf id exercise2311Measure t : EReal))
            (Set.Icc (-1 : ℝ) 1) 1 := by
        exact continuous_coe_real_ereal.continuousAt.comp_continuousWithinAt hCgf
      exact (continuousWithinAt_congr_of_mem hEqOn ht).2 hEReal
    · by_cases hLeft : t = -1
      · subst hLeft
        have hMem : (-1 : ℝ) ∈ integrableExpSet id exercise2311Measure := by
          simpa [exercise2311_integrableExpSet]
        have hInt :
            Integrable (fun x : ℝ ↦ Real.exp ((-1) * x)) exercise2311Measure := by
          simpa [integrableExpSet] using hMem
        have hMgf :
            ContinuousWithinAt (fun t : ℝ ↦ mgf id exercise2311Measure t)
              (Set.Icc (-1 : ℝ) 1) (-1) := by
          simpa [ContinuousWithinAt, nhdsWithin_Icc_eq_nhdsGE
            (a := (-1 : ℝ)) (b := (1 : ℝ)) (by norm_num)] using
            exercise2311ContinuousWithinAt_mgf_leftEndpoint
        have hCgf :
            ContinuousWithinAt (fun t : ℝ ↦ cgf id exercise2311Measure t)
              (Set.Icc (-1 : ℝ) 1) (-1) := by
          -- Proof comment: apply the same `log ∘ mgf` argument at the left endpoint.
          simpa [ProbabilityTheory.cgf] using hMgf.log (ProbabilityTheory.mgf_pos hInt).ne'
        have hEReal :
            ContinuousWithinAt (fun t : ℝ ↦ (cgf id exercise2311Measure t : EReal))
              (Set.Icc (-1 : ℝ) 1) (-1) := by
          exact continuous_coe_real_ereal.continuousAt.comp_continuousWithinAt hCgf
        exact (continuousWithinAt_congr_of_mem hEqOn ht).2 hEReal
      · have hInterior : t ∈ Set.Ioo (-1 : ℝ) 1 := by
          constructor
          · exact lt_of_le_of_ne ht.1 (Ne.symm hLeft)
          · exact lt_of_le_of_ne ht.2 hRight
        have hAnalytic :
            AnalyticAt ℝ (cgf id exercise2311Measure) t := by
          have hInteriorMem : t ∈ interior (integrableExpSet id exercise2311Measure) := by
            rw [exercise2311_integrableExpSet, interior_Icc]
            exact hInterior
          exact ProbabilityTheory.analyticAt_cgf (X := id) (μ := exercise2311Measure) hInteriorMem
        have hEReal :
            ContinuousWithinAt (fun t : ℝ ↦ (cgf id exercise2311Measure t : EReal))
              (Set.Icc (-1 : ℝ) 1) t := by
          have hReal : ContinuousAt (cgf id exercise2311Measure) t := hAnalytic.continuousAt
          exact continuous_coe_real_ereal.continuousAt.comp_continuousWithinAt
            hReal.continuousWithinAt
        exact (continuousWithinAt_congr_of_mem hEqOn ht).2 hEReal
  · -- Proof comment: approaching `1` from the right forces `Λ` to stay equal to `⊤`, so global
    -- continuity would contradict the finite value at the endpoint.
    intro hcont
    let u : ℕ → ℝ := fun n ↦ 1 + ((n : ℝ) + 1)⁻¹
    have hu_tendsto : Tendsto u atTop (𝓝 (1 : ℝ)) := by
      have hNat : Tendsto (fun n : ℕ ↦ (n : ℝ) + 1) atTop atTop := by
        exact tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds
      have hInv : Tendsto (fun n : ℕ ↦ ((n : ℝ) + 1)⁻¹) atTop (𝓝 (0 : ℝ)) :=
        tendsto_inv_atTop_zero.comp hNat
      simpa [u] using tendsto_const_nhds.add hInv
    have hSeqTop :
        (fun n : ℕ ↦ Λ(id; exercise2311Measure) (u n)) = fun _ : ℕ ↦ (⊤ : EReal) := by
      funext n
      apply exercise2311LogMomentGeneratingFunction_eq_top_of_not_mem_integrableExpSet
      apply exercise2311_not_mem_integrableExpSet_of_one_lt
      have hInvPos : 0 < ((n : ℝ) + 1)⁻¹ := by
        positivity
      linarith
    have hTendstoTop :
        Tendsto (fun n : ℕ ↦ Λ(id; exercise2311Measure) (u n)) atTop (𝓝 (⊤ : EReal)) := by
      rw [hSeqTop]
      exact tendsto_const_nhds
    have hTendstoAtOne :
        Tendsto (fun n : ℕ ↦ Λ(id; exercise2311Measure) (u n)) atTop
          (𝓝 (Λ(id; exercise2311Measure) 1)) :=
      hcont.continuousAt.tendsto.comp hu_tendsto
    have hMem : (1 : ℝ) ∈ integrableExpSet id exercise2311Measure := by
      simpa [exercise2311_integrableExpSet]
    have hFinite : Λ(id; exercise2311Measure) 1 ≠ (⊤ : EReal) := by
      rw [exercise2311LogMomentGeneratingFunction_eq_cgf_of_mem_integrableExpSet hMem]
      simp
    exact hFinite (tendsto_nhds_unique hTendstoAtOne hTendstoTop)
