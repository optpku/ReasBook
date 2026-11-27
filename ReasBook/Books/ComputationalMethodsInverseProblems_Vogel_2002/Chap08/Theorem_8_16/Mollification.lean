/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ComputationalMethodsInverseProblems_Vogel_2002.Chap08.Theorem_8_16.DomainRegularity
public import ComputationalMethodsInverseProblems_Vogel_2002.Chap08.Theorem_8_16.SmoothVariation
public import ComputationalMethodsInverseProblems_Vogel_2002.Chap08.Theorem_8_16.SmoothTranslation
public import Mathlib.Analysis.Calculus.BumpFunction.Convolution
public import Mathlib.Analysis.Calculus.ContDiff.Convolution
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.DistLEIntegral
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.Analysis.SpecificLimits.Basic

public section
noncomputable section

open MeasureTheory Set Filter
open scoped Convolution Topology BigOperators

namespace VariationalRegularization

@[simp] lemma domainMeasure_top_eq_volume {d : ℕ} :
    domainMeasure (⊤ : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin d))) = volume := by
  simp [domainMeasure_def, EuclideanSpace.euclideanHausdorffMeasure_eq_volume]

namespace BVCompactness
namespace Mollification

variable {d : ℕ}
abbrev Space (d : ℕ) := EuclideanSpace ℝ (Fin d)
abbrev Ambient (d : ℕ) : TopologicalSpace.Opens (Space d) := ⊤

/-- Translation preserves the admissible test-field class in the whole space. -/
@[expose] def shiftField (v : AdmissibleTestField (Ambient d)) (a : Space d) :
    AdmissibleTestField (Ambient d) where
  toTestFunction := TestFunction.mk (fun x ↦ v.toTestFunction (x + a))
    (v.toTestFunction.contDiff.comp (contDiff_id.add contDiff_const))
    (v.toTestFunction.hasCompactSupport.comp_homeomorph (Homeomorph.addRight a))
    (subset_univ _)
  norm_le_one x _ := v.norm_le_one (x + a) (mem_univ _)

@[simp] lemma shiftField_apply (v : AdmissibleTestField (Ambient d)) (a x : Space d) :
    (shiftField v a).toTestFunction x = v.toTestFunction (x + a) := rfl

lemma divergence_shiftField (v : AdmissibleTestField (Ambient d)) (a x : Space d) :
    admissibleDivergence (shiftField v a) x = admissibleDivergence v (x + a) := by
  have hder := (v.toTestFunction.contDiff.differentiable one_ne_zero (x + a)).hasFDerivAt.comp x
    ((hasFDerivAt_id x).add_const a)
  have heq : fderiv ℝ (shiftField v a).toTestFunction x =
      fderiv ℝ v.toTestFunction (x + a) := by
    rw [show (⇑(shiftField v a).toTestFunction) = (fun x ↦ v.toTestFunction (x + a)) from
      funext (shiftField_apply v a)]
    simpa only [Function.comp_def, id_eq, ContinuousLinearMap.comp_id] using hder.fderiv
  simp only [admissibleDivergence_def, heq]

/-- Fubini and translation of volume move a convolution onto a test function. -/
lemma integral_convolution_mul {f ρ h : Space d → ℝ}
    (hf : Integrable f) (hρ : Integrable ρ) (hh : Continuous h)
    (hc : HasCompactSupport h) :
    (∫ x, (ρ ⋆ f) x * h x) = ∫ z, ρ z * ∫ y, f y * h (y + z) := by
  obtain ⟨C, hC⟩ := hh.norm.bddAbove_range_of_hasCompactSupport hc.norm
  have hF : Integrable (fun p : Space d × Space d ↦
      (ρ p.2 * f (p.1 - p.2)) * h p.1) (volume.prod volume) :=
    (hρ.convolution_integrand (ContinuousLinearMap.mul ℝ ℝ) hf).mul_bdd
      (hh.comp continuous_fst).aestronglyMeasurable (.of_forall fun p ↦ hC ⟨p.1, rfl⟩)
  have hswap := integral_integral_swap
    (f := fun x z : Space d ↦ (ρ z * f (x - z)) * h x) hF
  calc
    _ = ∫ x, ∫ z, (ρ z * f (x - z)) * h x := by
      simp only [convolution_def, ContinuousLinearMap.lsmul_apply, smul_eq_mul,
        integral_mul_const]
    _ = ∫ z, ∫ x, (ρ z * f (x - z)) * h x := hswap
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [] with z
      rw [← integral_add_right_eq_self (fun x ↦ (ρ z * f (x - z)) * h x) z]
      simp only [add_sub_cancel_right, mul_assoc, integral_const_mul]

/-- The same Fubini calculation supplies integrability of the transposed pairing. -/
lemma integrable_convolution_test {f ρ h : Space d → ℝ}
    (hf : Integrable f) (hρ : Integrable ρ) (hh : Continuous h)
    (hc : HasCompactSupport h) :
    Integrable (fun z ↦ ρ z * ∫ y, f y * h (y + z)) := by
  obtain ⟨C, hC⟩ := hh.norm.bddAbove_range_of_hasCompactSupport hc.norm
  have hF : Integrable (fun p : Space d × Space d ↦
      (ρ p.1 * f p.2) * h (p.2 + p.1)) (volume.prod volume) :=
    (hρ.mul_prod hf).mul_bdd ((hh.comp (continuous_snd.add continuous_fst)).aestronglyMeasurable)
      (.of_forall fun p ↦ hC ⟨p.2 + p.1, rfl⟩)
  simpa only [mul_assoc, integral_const_mul] using hF.integral_prod_left

@[expose] def ambientLp (f : Space d → ℝ) (hf : Integrable f) :
    Lp ℝ 1 (domainMeasure (Ambient d)) :=
  (memLp_one_iff_integrable.2 (show Integrable f (domainMeasure (Ambient d)) by
    simpa using hf)).toLp f

lemma ambientLp_ae (f : Space d → ℝ) (hf : Integrable f) : ambientLp f hf =ᵐ[volume] f := by
  simpa only [ambientLp, domainMeasure_top_eq_volume] using
    (memLp_one_iff_integrable.2 (show Integrable f (domainMeasure (Ambient d)) by
    simpa using hf)).coeFn_toLp

lemma ambient_integrable (u : BV (Ambient d)) : Integrable (u.toL1 : Space d → ℝ) := by
  simpa using (memLp_one_iff_integrable.1 (Lp.memLp u.toL1))

/-- Positive normalized smoothing cannot increase the BV norm's variation bound. -/
lemma totalVariation_convolution_le (u : BV (Ambient d)) {ρ : Space d → ℝ}
    (hρ : Integrable ρ) (hρ0 : ∀ x, 0 ≤ ρ x) (hρ1 : ∫ x, ρ x = 1) :
    totalVariation (ambientLp (ρ ⋆ (u.toL1 : Space d → ℝ))
      (hρ.integrable_convolution (ContinuousLinearMap.lsmul ℝ ℝ) (ambient_integrable u))) ≤
      (‖u‖ : EReal) := by
  let f : Space d → ℝ := u.toL1
  have hf : Integrable f := by simpa [f] using (memLp_one_iff_integrable.1 (Lp.memLp u.toL1))
  apply totalVariation_le_of_forall_admissibleDivergencePairing_le
  intro v
  have hpoint (z : Space d) : (∫ y, f y * admissibleDivergence v (y + z)) ≤ ‖u‖ := by
    have hp : ((admissibleDivergencePairing u.toL1 (shiftField v z) : ℝ) : EReal) ≤
        totalVariation u.toL1 := by
      rw [totalVariation_def]
      exact le_sSup ⟨shiftField v z, rfl⟩
    have hbound := hp.trans (BV.lpTotalVariation_le_coe_norm u)
    have hb : admissibleDivergencePairing u.toL1 (shiftField v z) ≤ ‖u‖ := by exact_mod_cast hbound
    simpa only [admissibleDivergencePairing_def, domainMeasure_top_eq_volume,
      divergence_shiftField] using hb
  have hconv : Integrable (ρ ⋆ f) := hρ.integrable_convolution (ContinuousLinearMap.lsmul ℝ ℝ) hf
  have hcoe := ambientLp_ae (ρ ⋆ f) hconv
  have hpair : admissibleDivergencePairing (ambientLp (ρ ⋆ f) hconv) v =
      ∫ x, (ρ ⋆ f) x * admissibleDivergence v x := by
    let gfun : Space d → ℝ := ambientLp (ρ ⋆ f) hconv
    change (∫ x, gfun x * admissibleDivergence v x ∂domainMeasure (Ambient d)) = _
    rw [domainMeasure_top_eq_volume]
    exact integral_congr_ae (hcoe.fun_mul EventuallyEq.rfl)
  rw [hpair, integral_convolution_mul hf hρ (admissibleDivergenceContinuous v)
    (admissibleDivergenceHasCompactSupport v)]
  have hbound := integral_mono
    (integrable_convolution_test hf hρ (admissibleDivergenceContinuous v)
      (admissibleDivergenceHasCompactSupport v)) (hρ.mul_const ‖u‖)
    (fun z ↦ mul_le_mul_of_nonneg_left (hpoint z) (hρ0 z))
  simp only [integral_mul_const, hρ1, one_mul] at hbound
  exact_mod_cast hbound

lemma convolution_hasCompactSupport {f ρ : Space d → ℝ} {K : Set (Space d)}
    (hc : HasCompactSupport ρ) (hK : IsCompact K)
    (hs : ∀ᵐ x ∂volume, x ∉ K → f x = 0) : HasCompactSupport (ρ ⋆ f) := by
  let fK := K.indicator f
  have hfK : HasCompactSupport fK := by
    apply HasCompactSupport.of_support_subset_isCompact hK
    intro x hx
    by_contra hxK
    exact hx (by simp [fK, hxK])
  have hae : f =ᵐ[volume] fK := by
    filter_upwards [hs] with x hx
    by_cases hxK : x ∈ K
    · simp [fK, hxK]
    · simp [fK, hxK, hx hxK]
  rw [convolution_congr (ContinuousLinearMap.lsmul ℝ ℝ) EventuallyEq.rfl hae]
  exact hc.convolution (ContinuousLinearMap.lsmul ℝ ℝ) hfK

/-- The smooth convolution's gradient integral is bounded by the original BV norm. -/
lemma convolution_integral_norm_fderiv_le (u : BV (Ambient d)) {ρ : Space d → ℝ}
    (hc : HasCompactSupport ρ) (hρ : ContDiff ℝ 1 ρ)
    (hρ0 : ∀ x, 0 ≤ ρ x) (hρ1 : ∫ x, ρ x = 1)
    (hg : HasCompactSupport (ρ ⋆ (u.toL1 : Space d → ℝ))) :
    (∫ x, ‖fderiv ℝ (ρ ⋆ (u.toL1 : Space d → ℝ)) x‖) ≤ ‖u‖ := by
  have hρi : Integrable ρ := hρ.continuous.integrable_of_hasCompactSupport hc
  have hgi := hρi.integrable_convolution (ContinuousLinearMap.lsmul ℝ ℝ) (ambient_integrable u)
  have hgs : ContDiff ℝ 1 (ρ ⋆ (u.toL1 : Space d → ℝ)) :=
    hc.contDiff_convolution_left (ContinuousLinearMap.lsmul ℝ ℝ) hρ (ambient_integrable u).locallyIntegrable
  have heq := smoothCompactSupport_totalVariationToReal_eq_integral_norm_fderiv
    (Ω := Ambient d) hgs hg (subset_univ _)
  have htv := totalVariation_convolution_le u hρi hρ0 hρ1
  have hbot : totalVariation (ambientLp (ρ ⋆ (u.toL1 : Space d → ℝ)) hgi) ≠ ⊥ :=
    ne_bot_of_gt (lt_of_lt_of_le (EReal.bot_lt_coe 0) (lpTotalVariationNonneg _))
  have hb := EReal.toReal_le_toReal htv hbot (EReal.coe_ne_top ‖u‖)
  have heq' : (totalVariation (ambientLp (ρ ⋆ (u.toL1 : Space d → ℝ)) hgi)).toReal =
      ∫ x, ‖fderiv ℝ (ρ ⋆ (u.toL1 : Space d → ℝ)) x‖ := by
    simpa only [ambientLp, domainMeasure_top_eq_volume] using heq
  simpa only [heq', EReal.toReal_coe] using hb

/-- The BV translation estimate on the ambient space. It is obtained from
smooth convolution, the classical FTC estimate, and Fatou's lemma. -/
lemma integral_norm_translate_sub_le (u : BV (Ambient d))
    {K : Set (Space d)} (hK : IsCompact K)
    (hs : ∀ᵐ x ∂volume, x ∉ K → u.toL1 x = 0) (a : Space d) :
    (∫ x, ‖u.toL1 (x + a) - u.toL1 x‖) ≤ ‖u‖ * ‖a‖ := by
  let φ : ℕ → ContDiffBump (0 : Space d) := fun n ↦
    ⟨(1 / ((n : ℝ) + 1)) / 2, 1 / ((n : ℝ) + 1), by positivity,
      by
        have hn : 0 < 1 / ((n : ℝ) + 1) := by positivity
        linarith⟩
  let g : ℕ → Space d → ℝ := fun n ↦ (φ n).normed volume ⋆ (u.toL1 : Space d → ℝ)
  have hf := ambient_integrable u
  have hgs (n : ℕ) : ContDiff ℝ 1 (g n) :=
    (φ n).hasCompactSupport_normed.contDiff_convolution_left (ContinuousLinearMap.lsmul ℝ ℝ)
      (φ n).contDiff_normed hf.locallyIntegrable
  have hgc (n : ℕ) : HasCompactSupport (g n) :=
    convolution_hasCompactSupport (φ n).hasCompactSupport_normed hK hs
  have hgi (n : ℕ) : Integrable (g n) :=
    (φ n).integrable_normed.integrable_convolution (ContinuousLinearMap.lsmul ℝ ℝ) hf
  have hbound (n : ℕ) : eLpNorm (fun x ↦ g n (x + a) - g n x) 1 volume ≤
      ENNReal.ofReal (‖u‖ * ‖a‖) := by
    have hFTC := smooth_integral_norm_translate_sub_le (hgs n) (hgc n) a
    have hgrad := convolution_integral_norm_fderiv_le u (φ n).hasCompactSupport_normed
      (φ n).contDiff_normed (φ n).nonneg_normed (φ n).integral_normed (hgc n)
    have hi : Integrable (fun x ↦ g n (x + a) - g n x) := (hgi n |>.comp_add_right a).sub (hgi n)
    rw [eLpNorm_one_eq_lintegral_enorm, ← ofReal_integral_norm_eq_lintegral_enorm hi]
    exact ENNReal.ofReal_le_ofReal (hFTC.trans (mul_le_mul_of_nonneg_right hgrad (norm_nonneg a)))
  have hlim : ∀ᵐ x ∂volume, Tendsto (fun n ↦ g n x) atTop (nhds (u.toL1 x)) := by
    apply ContDiffBump.ae_convolution_tendsto_right_of_locallyIntegrable
      (φ := φ) (K := 2) (by simpa [φ] using (tendsto_one_div_add_atTop_nhds_zero_nat :
        Tendsto (fun n : ℕ ↦ 1 / ((n : ℝ) + 1)) atTop (nhds 0)))
      (.of_forall fun n ↦ by dsimp [φ]; linarith) hf.locallyIntegrable
  have hlimShift :=
    (measurePreserving_add_right (volume : Measure (Space d)) a).quasiMeasurePreserving.tendsto_ae.eventually hlim
  have hlimSub : ∀ᵐ x ∂volume,
      Tendsto (fun n ↦ g n (x + a) - g n x) atTop (nhds (u.toL1 (x + a) - u.toL1 x)) := by
    filter_upwards [hlim, hlimShift] with x hx hxa
    exact hxa.sub hx
  have hb := Lp.eLpNorm_le_of_ae_tendsto (p := (1 : ENNReal))
    (.of_forall hbound)
    (fun n ↦ ((hgs n).continuous.comp (continuous_id.add continuous_const)).aestronglyMeasurable.sub
      (hgs n).continuous.aestronglyMeasurable) hlimSub
  have hi : Integrable (fun x ↦ u.toL1 (x + a) - u.toL1 x) := (hf.comp_add_right a).sub hf
  rw [eLpNorm_one_eq_lintegral_enorm, ← ofReal_integral_norm_eq_lintegral_enorm hi] at hb
  exact (ENNReal.ofReal_le_ofReal_iff (mul_nonneg (norm_nonneg u) (norm_nonneg a))).1 hb

/-- A positive normalized kernel supported in a radius-`r` ball approximates
an ambient BV function in `L¹` with error at most `r * ‖u‖BV`. -/
lemma integral_norm_sub_convolution_le (u : BV (Ambient d))
    {K : Set (Space d)} (hK : IsCompact K)
    (hs : ∀ᵐ x ∂volume, x ∉ K → u.toL1 x = 0)
    {ρ : Space d → ℝ} (hc : HasCompactSupport ρ) (hρ : ContDiff ℝ 1 ρ)
    (hρ0 : ∀ x, 0 ≤ ρ x) (hρ1 : ∫ x, ρ x = 1)
    {r : ℝ} (hr : Function.support ρ ⊆ Metric.closedBall 0 r) :
    (∫ x, ‖u.toL1 x - (ρ ⋆ (u.toL1 : Space d → ℝ)) x‖) ≤ r * ‖u‖ := by
  let f : Space d → ℝ := u.toL1
  have hf := ambient_integrable u
  have hρi : Integrable ρ := hρ.continuous.integrable_of_hasCompactSupport hc
  have hgi : Integrable (ρ ⋆ f) := hρi.integrable_convolution (ContinuousLinearMap.lsmul ℝ ℝ) hf
  let F : Space d × Space d → ℝ := fun p ↦ ρ p.2 * (f p.1 - f (p.1 - p.2))
  have hFi : Integrable F (volume.prod volume) := by
    apply ((hf.mul_prod hρi).sub
      (hρi.convolution_integrand (ContinuousLinearMap.mul ℝ ℝ) hf)).congr
    exact .of_forall fun p ↦ by dsimp [F]; ring
  have heq (x : Space d) : f x - (ρ ⋆ f) x = ∫ z, F (x, z) := by
    have hx : Integrable (fun z ↦ ρ z * f (x - z)) :=
      hc.convolutionExists_left (ContinuousLinearMap.lsmul ℝ ℝ) hρ.continuous hf.locallyIntegrable x
    simp only [F, mul_sub, integral_sub (hρi.mul_const (f x)) hx, integral_mul_const,
      hρ1, one_mul, convolution_def, ContinuousLinearMap.lsmul_apply, smul_eq_mul]
  have hmono : (∫ x, ‖f x - (ρ ⋆ f) x‖) ≤ ∫ x, ∫ z, ‖F (x, z)‖ := by
    apply integral_mono (hf.sub hgi).norm hFi.integral_norm_prod_left
    intro x
    change ‖f x - (ρ ⋆ f) x‖ ≤ ∫ z, ‖F (x, z)‖
    rw [heq]
    exact norm_integral_le_integral_norm _
  refine hmono.trans ?_
  rw [integral_integral_swap (f := fun x z ↦ ‖F (x, z)‖) hFi.norm]
  have hinner (z : Space d) : (∫ x, ‖F (x, z)‖) ≤ ρ z * (r * ‖u‖) := by
    have he : (∫ x, ‖F (x, z)‖) = ρ z * ∫ x, ‖f (x - z) - f x‖ := by
      simp only [F, norm_mul, Real.norm_eq_abs, abs_of_nonneg (hρ0 z), norm_sub_rev,
        integral_const_mul]
    rw [he]
    by_cases hz : ρ z = 0
    · simp [hz]
    have hzr : ‖z‖ ≤ r := by simpa [Metric.mem_closedBall] using hr hz
    have hb := integral_norm_translate_sub_le u hK hs (-z)
    simp only [← sub_eq_add_neg, norm_neg] at hb
    apply mul_le_mul_of_nonneg_left _ (hρ0 z)
    exact hb.trans (by nlinarith [norm_nonneg u])
  have hb := integral_mono hFi.integral_norm_prod_right (hρi.mul_const (r * ‖u‖)) hinner
  simpa only [integral_mul_const, hρ1, one_mul] using hb

end Mollification
end BVCompactness
end VariationalRegularization
