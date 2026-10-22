/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib.Tactic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Measure.GiryMonad
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.Probability.Kernel.Composition.IntegralCompProd

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory
open scoped ProbabilityTheory

noncomputable section

namespace ProbabilityTheory

/-- The explicit measure underlying the centered two-point law at support pair `(u,v)` with
`u < 0 ≤ v`. -/
private def negativeNonnegativeTwoPointMeasure
    (z : Set.Iio (0 : ℝ) × Set.Ici (0 : ℝ)) : Measure ℝ :=
  let u : ℝ := z.1
  let v : ℝ := z.2
  ENNReal.ofReal (v / (v - u)) • Measure.dirac u +
    ENNReal.ofReal (-u / (v - u)) • Measure.dirac v

/-- Helper for Lemma 22.8: evaluating the explicit two-point fiber on a measurable set depends
measurably on the support pair. -/
private lemma measurable_negativeNonnegativeTwoPointMeasure_apply
    {s : Set ℝ} (hs : MeasurableSet s) :
    Measurable
      (fun z : Set.Iio (0 : ℝ) × Set.Ici (0 : ℝ) ↦ negativeNonnegativeTwoPointMeasure z s) := by
  -- Proof comment: rewrite each Dirac evaluation as the indicator of membership in `s`, so the
  -- fiber mass is built from measurable coordinate maps by arithmetic operations.
  classical
  have hfst : Measurable (fun z : Set.Iio (0 : ℝ) × Set.Ici (0 : ℝ) ↦ (z.1 : ℝ)) := by
    fun_prop
  have hsnd : Measurable (fun z : Set.Iio (0 : ℝ) × Set.Ici (0 : ℝ) ↦ (z.2 : ℝ)) := by
    fun_prop
  have hdiracFst :
      Measurable
        (fun z : Set.Iio (0 : ℝ) × Set.Ici (0 : ℝ) ↦ Measure.dirac (z.1 : ℝ) s) := by
    simpa [Measure.dirac_apply] using
      ((Measurable.indicator measurable_const hs).comp hfst)
  have hdiracSnd :
      Measurable
        (fun z : Set.Iio (0 : ℝ) × Set.Ici (0 : ℝ) ↦ Measure.dirac (z.2 : ℝ) s) := by
    simpa [Measure.dirac_apply] using
      ((Measurable.indicator measurable_const hs).comp hsnd)
  have hweightFst :
      Measurable
        (fun z : Set.Iio (0 : ℝ) × Set.Ici (0 : ℝ) ↦
          ENNReal.ofReal ((z.2 : ℝ) / ((z.2 : ℝ) - (z.1 : ℝ)))) := by
    exact Measurable.ennreal_ofReal (by fun_prop)
  have hweightSnd :
      Measurable
        (fun z : Set.Iio (0 : ℝ) × Set.Ici (0 : ℝ) ↦
          ENNReal.ofReal (-(z.1 : ℝ) / ((z.2 : ℝ) - (z.1 : ℝ)))) := by
    exact Measurable.ennreal_ofReal (by fun_prop)
  simpa [negativeNonnegativeTwoPointMeasure, smul_eq_mul] using
    (hweightFst.mul hdiracFst).add (hweightSnd.mul hdiracSnd)

/-- Helper for Lemma 22.8: each centered two-point fiber has total mass `1`. -/
private lemma negativeNonnegativeTwoPointMeasure_univ
    (z : Set.Iio (0 : ℝ) × Set.Ici (0 : ℝ)) :
    negativeNonnegativeTwoPointMeasure z Set.univ = 1 := by
  -- Proof comment: both Dirac masses contribute total mass `1`, and the two zero-mean weights
  -- add up to `1` because `u < 0 ≤ v`.
  rcases z with ⟨u, v⟩
  have huv : (u : ℝ) < v := lt_of_lt_of_le u.2 v.2
  have hdenom : 0 < (v : ℝ) - (u : ℝ) := sub_pos.mpr huv
  have hweightFst_nonneg : 0 ≤ (v : ℝ) / ((v : ℝ) - (u : ℝ)) := by
    exact div_nonneg v.2 hdenom.le
  have hweightSnd_nonneg : 0 ≤ (-(u : ℝ)) / ((v : ℝ) - (u : ℝ)) := by
    exact div_nonneg (neg_nonneg.mpr u.2.le) hdenom.le
  have hsum :
      (v : ℝ) / ((v : ℝ) - (u : ℝ)) + (-(u : ℝ)) / ((v : ℝ) - (u : ℝ)) = 1 := by
    field_simp [hdenom.ne']
    ring
  rw [negativeNonnegativeTwoPointMeasure]
  rw [Measure.add_apply]
  simp only [Measure.coe_smul, Pi.smul_apply, Measure.dirac_apply_of_mem (Set.mem_univ _),
    smul_eq_mul]
  have hsumENN :
      ENNReal.ofReal ((v : ℝ) / ((v : ℝ) - (u : ℝ))) +
        ENNReal.ofReal (-(u : ℝ) / ((v : ℝ) - (u : ℝ))) = 1 := by
    rw [← ENNReal.ofReal_add hweightFst_nonneg hweightSnd_nonneg, hsum, ENNReal.ofReal_one]
  simpa using hsumENN

/-- The kernel sending `(u,v)` to the centered two-point law supported on `{u,v}`. -/
def negativeNonnegativeTwoPointKernel :
    Kernel (Set.Iio (0 : ℝ) × Set.Ici (0 : ℝ)) ℝ where
  toFun := negativeNonnegativeTwoPointMeasure
  measurable' := by
    -- Proof comment: kernel measurability is exactly the measurable set-evaluation map proved
    -- for the explicit fiber formula above.
    exact Measure.measurable_of_measurable_coe _ fun s hs ↦
      measurable_negativeNonnegativeTwoPointMeasure_apply (s := s) hs

/-- At `z = (u,v)`, the kernel fiber is the explicit convex combination of the two Dirac masses
at `u` and `v` with zero-mean weights. -/
@[simp] theorem negativeNonnegativeTwoPointKernel_apply
    (u : Set.Iio (0 : ℝ)) (v : Set.Ici (0 : ℝ)) :
    negativeNonnegativeTwoPointKernel (u, v) =
      ENNReal.ofReal ((v : ℝ) / ((v : ℝ) - (u : ℝ))) • Measure.dirac (u : ℝ) +
        ENNReal.ofReal (-(u : ℝ) / ((v : ℝ) - (u : ℝ))) • Measure.dirac (v : ℝ) :=
  rfl

/-- The centered two-point family is a Markov kernel. -/
theorem negativeNonnegativeTwoPointKernel_isMarkovKernel :
    IsMarkovKernel negativeNonnegativeTwoPointKernel := by
  -- Proof comment: each fiber is a probability measure because its total mass is exactly `1`.
  refine ⟨fun z ↦ ?_⟩
  change IsProbabilityMeasure (negativeNonnegativeTwoPointMeasure z)
  exact ⟨negativeNonnegativeTwoPointMeasure_univ z⟩

instance : IsMarkovKernel negativeNonnegativeTwoPointKernel :=
  negativeNonnegativeTwoPointKernel_isMarkovKernel

/-- Helper for Lemma 22.8: the second moment of each centered two-point fiber is `-u v`. -/
private lemma negativeNonnegativeTwoPointKernel_secondMoment
    (z : Set.Iio (0 : ℝ) × Set.Ici (0 : ℝ)) :
    ∫ x, x ^ 2 ∂negativeNonnegativeTwoPointKernel z = -((z.1 : ℝ) * z.2) := by
  -- Proof comment: evaluate the integral against the two Dirac masses and simplify the resulting
  -- rational identity using `u < 0 ≤ v`.
  rcases z with ⟨u, v⟩
  have huv : (u : ℝ) < v := lt_of_lt_of_le u.2 v.2
  have hdenom : 0 < (v : ℝ) - (u : ℝ) := sub_pos.mpr huv
  have hweightFst_nonneg : 0 ≤ (v : ℝ) / ((v : ℝ) - (u : ℝ)) := by
    exact div_nonneg v.2 hdenom.le
  have hweightSnd_nonneg : 0 ≤ (-(u : ℝ)) / ((v : ℝ) - (u : ℝ)) := by
    exact div_nonneg (neg_nonneg.mpr u.2.le) hdenom.le
  have huInt : Integrable (fun x : ℝ ↦ x ^ 2) (Measure.dirac (u : ℝ)) := by
    exact integrable_dirac (by simp)
  have hvInt : Integrable (fun x : ℝ ↦ x ^ 2) (Measure.dirac (v : ℝ)) := by
    exact integrable_dirac (by simp)
  have huSmul :
      Integrable (fun x : ℝ ↦ x ^ 2)
        (ENNReal.ofReal ((v : ℝ) / ((v : ℝ) - (u : ℝ))) • Measure.dirac (u : ℝ)) := by
    exact huInt.smul_measure (by simp)
  have hvSmul :
      Integrable (fun x : ℝ ↦ x ^ 2)
        (ENNReal.ofReal (-(u : ℝ) / ((v : ℝ) - (u : ℝ))) • Measure.dirac (v : ℝ)) := by
    exact hvInt.smul_measure (by simp)
  rw [negativeNonnegativeTwoPointKernel_apply, integral_add_measure huSmul hvSmul,
    integral_smul_measure, integral_smul_measure, integral_dirac, integral_dirac]
  rw [ENNReal.toReal_ofReal hweightFst_nonneg, ENNReal.toReal_ofReal hweightSnd_nonneg]
  simp only [smul_eq_mul]
  field_simp [hdenom.ne']
  ring

/-- Helper for Lemma 22.8: a finite real law with integrable square also has integrable first
moment. -/
private lemma integrable_id_of_integrable_sq
    {μ : Measure ℝ} [IsFiniteMeasure μ]
    (h_sq : Integrable (fun x : ℝ ↦ x ^ 2) μ) :
    Integrable (fun x : ℝ ↦ x) μ := by
  -- Proof comment: dominate `|x|` by the integrable envelope `x ^ 2 + 1`.
  have h_aux : Integrable (fun x : ℝ ↦ x ^ 2 + 1) μ := by
    exact h_sq.add (integrable_const 1)
  refine h_aux.mono' (by fun_prop) ?_
  filter_upwards with x
  have hbound : |x| ≤ x ^ 2 + 1 := by
    have hbound' : |x| ≤ |x| ^ 2 + 1 := by
      nlinarith [sq_nonneg (|x| - 1)]
    simpa [sq_abs] using hbound'
  simpa [Real.norm_eq_abs] using hbound

/-- Helper for Lemma 22.8: the positive and negative first moments agree for a centered
integrable law on `ℝ`. -/
private lemma positiveNegativeFirstMoment_eq
    {μ : Measure ℝ}
    (hint : Integrable (fun x : ℝ ↦ x) μ)
    (hmean : ∫ x, x ∂μ = 0) :
    ∫ x in Set.Ici (0 : ℝ), x ∂μ = ∫ x in Set.Iio (0 : ℝ), -x ∂μ := by
  -- Proof comment: split the centered integral over `(-∞,0)` and `[0,∞)`, then move the
  -- negative contribution to the right-hand side.
  have hsplit :
      (∫ x in Set.Iio (0 : ℝ), x ∂μ) + ∫ x in Set.Ici (0 : ℝ), x ∂μ = ∫ x, x ∂μ := by
    exact intervalIntegral.integral_Iio_add_Ici (b := (0 : ℝ)) hint.integrableOn hint.integrableOn
  have hneg :
      ∫ x in Set.Iio (0 : ℝ), -x ∂μ = -∫ x in Set.Iio (0 : ℝ), x ∂μ := by
    rw [integral_neg]
  have hsum :
      (∫ x in Set.Iio (0 : ℝ), x ∂μ) + ∫ x in Set.Ici (0 : ℝ), x ∂μ = 0 := by
    simpa [hmean] using hsplit
  have htarget : ∫ x in Set.Ici (0 : ℝ), x ∂μ = -∫ x in Set.Iio (0 : ℝ), x ∂μ := by
    linarith
  rw [hneg]
  exact htarget

/-- Helper for Lemma 22.8: if the positive first moment of a centered law vanishes, then the law
is concentrated at `0`. -/
private lemma eq_dirac_zero_of_positivePartMeanZero
    (μ : ProbabilityMeasure ℝ)
    (hint : Integrable (fun x : ℝ ↦ x) (μ : Measure ℝ))
    (hmean : ∫ x, x ∂(μ : Measure ℝ) = 0)
    (hm0 : ∫ x in Set.Ici (0 : ℝ), x ∂(μ : Measure ℝ) = 0) :
    (μ : Measure ℝ) = Measure.dirac 0 := by
  -- Proof comment: the positive and negative first moments both vanish, so the strict positive
  -- and strict negative half-lines have measure zero. Then the probability law is concentrated
  -- at `0`, and `Measure.ext_of_Iic` identifies it with `dirac 0`.
  have hneg0 : ∫ x in Set.Iio (0 : ℝ), -x ∂(μ : Measure ℝ) = 0 := by
    rw [← positiveNegativeFirstMoment_eq hint hmean, hm0]
  have hnonnegIci :
      0 ≤ᵐ[(μ : Measure ℝ).restrict (Set.Ici (0 : ℝ))] fun x : ℝ ↦ x := by
    refine (ae_restrict_iff' measurableSet_Ici).2 ?_
    exact ae_of_all _ fun x hx ↦ hx
  have hnonnegIio :
      0 ≤ᵐ[(μ : Measure ℝ).restrict (Set.Iio (0 : ℝ))] fun x : ℝ ↦ -x := by
    refine (ae_restrict_iff' measurableSet_Iio).2 ?_
    exact ae_of_all _ fun x hx ↦ neg_nonneg.mpr (le_of_lt hx)
  have hIoi_support :
      Function.support (fun x : ℝ ↦ x) ∩ Set.Ici (0 : ℝ) = Set.Ioi (0 : ℝ) := by
    ext x
    constructor
    · rintro ⟨hx, hx0⟩
      rw [Function.mem_support] at hx
      have hx0' : 0 ≤ x := hx0
      exact lt_of_le_of_ne hx0' (by simpa [eq_comm] using hx)
    · intro hx
      have hx' : 0 < x := hx
      have hxIci : x ∈ Set.Ici (0 : ℝ) := by
        exact le_of_lt hx'
      refine ⟨?_, hxIci⟩
      rw [Function.mem_support]
      exact hx'.ne'
  have hIio_support :
      Function.support (fun x : ℝ ↦ -x) ∩ Set.Iio (0 : ℝ) = Set.Iio (0 : ℝ) := by
    ext x
    constructor
    · intro hx
      exact hx.2
    · intro hx
      refine ⟨?_, hx⟩
      rw [Function.mem_support]
      exact neg_ne_zero.mpr hx.ne
  have hμIoi : (μ : Measure ℝ) (Set.Ioi (0 : ℝ)) = 0 := by
    have hsupp :
        ¬0 < (μ : Measure ℝ) (Function.support (fun x : ℝ ↦ x) ∩ Set.Ici (0 : ℝ)) := by
      intro hpos
      have hposInt :
          0 < ∫ x in Set.Ici (0 : ℝ), x ∂(μ : Measure ℝ) := by
        exact (MeasureTheory.setIntegral_pos_iff_support_of_nonneg_ae hnonnegIci
          hint.integrableOn).2 hpos
      simp [hm0] at hposInt
    exact le_antisymm (not_lt.mp <| by simpa [hIoi_support] using hsupp) bot_le
  have hμIio : (μ : Measure ℝ) (Set.Iio (0 : ℝ)) = 0 := by
    have hsupp :
        ¬0 < (μ : Measure ℝ) (Function.support (fun x : ℝ ↦ -x) ∩ Set.Iio (0 : ℝ)) := by
      intro hpos
      have hposInt :
          0 < ∫ x in Set.Iio (0 : ℝ), -x ∂(μ : Measure ℝ) := by
        exact (MeasureTheory.setIntegral_pos_iff_support_of_nonneg_ae hnonnegIio
          hint.integrableOn.neg).2 hpos
      simp [hneg0] at hposInt
    exact le_antisymm (not_lt.mp <| by simpa [hIio_support] using hsupp) bot_le
  refine Measure.ext_of_Iic (μ := (μ : Measure ℝ)) (ν := Measure.dirac 0) fun a ↦ ?_
  by_cases ha : a < 0
  · have hsubset : Set.Iic a ⊆ Set.Iio (0 : ℝ) := fun x hx ↦ lt_of_le_of_lt hx ha
    have hμzero : (μ : Measure ℝ) (Set.Iic a) = 0 := by
      exact le_antisymm (le_trans (measure_mono hsubset) <| by simp [hμIio]) bot_le
    simp [ha, hμzero]
  · have ha0 : 0 ≤ a := le_of_not_gt ha
    have hsubset : Set.Ioi a ⊆ Set.Ioi (0 : ℝ) := fun x hx ↦ lt_of_le_of_lt ha0 hx
    have hμIoi_a : (μ : Measure ℝ) (Set.Ioi a) = 0 := by
      exact le_antisymm (le_trans (measure_mono hsubset) <| by simp [hμIoi]) bot_le
    have hprob :
        (μ : Measure ℝ) (Set.Iic a) + (μ : Measure ℝ) (Set.Ioi a) = 1 := by
      simpa [Set.compl_Iic] using
        (MeasureTheory.prob_add_prob_compl (μ := (μ : Measure ℝ)) measurableSet_Iic)
    simpa [ha0, hμIoi_a] using hprob

/-- Helper for Lemma 22.8: the base product law on `(-∞,0) × [0,∞)` used for the two-point
mixing construction. -/
private def twoPointMixingBaseMeasure
    (μ : ProbabilityMeasure ℝ) :
    Measure (Set.Iio (0 : ℝ) × Set.Ici (0 : ℝ)) :=
  (Measure.comap Subtype.val (μ : Measure ℝ)).prod
    (Measure.comap Subtype.val (μ : Measure ℝ))

/-- Helper for Lemma 22.8: the textbook `withDensity` law on `(-∞,0) × [0,∞)` whose density is
proportional to `v - u`. -/
private def twoPointMixingMeasure
    (μ : ProbabilityMeasure ℝ) (m : ℝ) :
    Measure (Set.Iio (0 : ℝ) × Set.Ici (0 : ℝ)) :=
  (twoPointMixingBaseMeasure μ).withDensity
    (fun z ↦ ENNReal.ofReal (((z.2 : ℝ) - z.1) / m))

/-- Helper for Lemma 22.8: the positive-part density factor integrates to `1` once normalized by
its first moment. -/
private lemma positivePartScaledLIntegral_eq_one
    (μ : ProbabilityMeasure ℝ)
    (hint : Integrable (fun x : ℝ ↦ x) (μ : Measure ℝ))
    {m : ℝ} (hm : 0 < m)
    (hmdef : ∫ x in Set.Ici (0 : ℝ), x ∂(μ : Measure ℝ) = m) :
    ∫⁻ v : Set.Ici (0 : ℝ), ENNReal.ofReal ((v : ℝ) / m)
      ∂Measure.comap Subtype.val (μ : Measure ℝ) = 1 := by
  -- Proof comment: pass from the subtype `lintegral` to the set integral on `[0,∞)`, then the
  -- normalization is exactly the definition of `m`.
  have hnonneg :
      0 ≤ᵐ[Measure.comap Subtype.val (μ : Measure ℝ)] fun v : Set.Ici (0 : ℝ) ↦ (v : ℝ) / m := by
    exact ae_of_all _ fun v ↦ div_nonneg v.2 hm.le
  have hintSubtype :
      Integrable (fun v : Set.Ici (0 : ℝ) ↦ (v : ℝ) / m)
        (Measure.comap Subtype.val (μ : Measure ℝ)) := by
    simpa [Function.comp_def] using
      (integrableOn_iff_comap_subtypeVal (f := fun x : ℝ ↦ x / m)
        (μ := (μ : Measure ℝ)) (s := Set.Ici (0 : ℝ)) measurableSet_Ici).mp
        (hint.integrableOn.div_const m)
  have hIntegral :
      ∫ v : Set.Ici (0 : ℝ), (v : ℝ) / m ∂Measure.comap Subtype.val (μ : Measure ℝ) = 1 := by
    calc
      ∫ v : Set.Ici (0 : ℝ), (v : ℝ) / m ∂Measure.comap Subtype.val (μ : Measure ℝ)
          = ∫ x in Set.Ici (0 : ℝ), x / m ∂(μ : Measure ℝ) := by
              simpa using
                (integral_subtype_comap (μ := (μ : Measure ℝ)) measurableSet_Ici
                  (fun x : ℝ ↦ x / m))
      _ = (∫ x in Set.Ici (0 : ℝ), x ∂(μ : Measure ℝ)) / m := by
            rw [integral_div]
      _ = m / m := by rw [hmdef]
      _ = 1 := by field_simp [hm.ne']
  have hOfReal :
      ENNReal.ofReal
          (∫ v : Set.Ici (0 : ℝ), (v : ℝ) / m
            ∂Measure.comap Subtype.val (μ : Measure ℝ)) =
        ∫⁻ v : Set.Ici (0 : ℝ), ENNReal.ofReal ((v : ℝ) / m)
          ∂Measure.comap Subtype.val (μ : Measure ℝ) := by
    exact MeasureTheory.ofReal_integral_eq_lintegral_ofReal hintSubtype hnonneg
  rw [hIntegral, ENNReal.ofReal_one] at hOfReal
  simpa using hOfReal.symm

/-- Helper for Lemma 22.8: the negative-part density factor integrates to `1` once normalized by
the common first moment. -/
private lemma negativePartScaledLIntegral_eq_one
    (μ : ProbabilityMeasure ℝ)
    (hint : Integrable (fun x : ℝ ↦ x) (μ : Measure ℝ))
    {m : ℝ} (hm : 0 < m)
    (hmdef : ∫ x in Set.Iio (0 : ℝ), -x ∂(μ : Measure ℝ) = m) :
    ∫⁻ u : Set.Iio (0 : ℝ), ENNReal.ofReal (-(u : ℝ) / m)
      ∂Measure.comap Subtype.val (μ : Measure ℝ) = 1 := by
  -- Proof comment: this is the same normalization argument on the negative half-line, applied to
  -- the nonnegative function `x ↦ -x`.
  have hnonneg :
      0 ≤ᵐ[Measure.comap Subtype.val (μ : Measure ℝ)] fun u : Set.Iio (0 : ℝ) ↦ -(u : ℝ) / m := by
    exact ae_of_all _ fun u ↦ div_nonneg (neg_nonneg.mpr u.2.le) hm.le
  have hintSubtype :
      Integrable (fun u : Set.Iio (0 : ℝ) ↦ -(u : ℝ) / m)
        (Measure.comap Subtype.val (μ : Measure ℝ)) := by
    simpa [Function.comp_def] using
      (integrableOn_iff_comap_subtypeVal (f := fun x : ℝ ↦ -x / m)
        (μ := (μ : Measure ℝ)) (s := Set.Iio (0 : ℝ)) measurableSet_Iio).mp
        (hint.neg.integrableOn.div_const m)
  have hIntegral :
      ∫ u : Set.Iio (0 : ℝ), -(u : ℝ) / m ∂Measure.comap Subtype.val (μ : Measure ℝ) = 1 := by
    calc
      ∫ u : Set.Iio (0 : ℝ), -(u : ℝ) / m ∂Measure.comap Subtype.val (μ : Measure ℝ)
          = ∫ x in Set.Iio (0 : ℝ), -x / m ∂(μ : Measure ℝ) := by
              simpa using
                (integral_subtype_comap (μ := (μ : Measure ℝ)) measurableSet_Iio
                  (fun x : ℝ ↦ -x / m))
      _ = (∫ x in Set.Iio (0 : ℝ), -x ∂(μ : Measure ℝ)) / m := by
            rw [integral_div]
      _ = m / m := by rw [hmdef]
      _ = 1 := by field_simp [hm.ne']
  have hOfReal :
      ENNReal.ofReal
          (∫ u : Set.Iio (0 : ℝ), -(u : ℝ) / m
            ∂Measure.comap Subtype.val (μ : Measure ℝ)) =
        ∫⁻ u : Set.Iio (0 : ℝ), ENNReal.ofReal (-(u : ℝ) / m)
          ∂Measure.comap Subtype.val (μ : Measure ℝ) := by
    exact MeasureTheory.ofReal_integral_eq_lintegral_ofReal hintSubtype hnonneg
  rw [hIntegral, ENNReal.ofReal_one] at hOfReal
  simpa using hOfReal.symm

/-- Helper for Lemma 22.8: on the negative half-line, the `withDensity` mixing law reproduces the
negative part of `μ`. -/
private lemma twoPointMixingMeasure_apply_Iio
    (μ : ProbabilityMeasure ℝ)
    (hint : Integrable (fun x : ℝ ↦ x) (μ : Measure ℝ))
    {m : ℝ} (hm : 0 < m) {s : Set ℝ} (hs : MeasurableSet s)
    (hmdef : ∫ x in Set.Ici (0 : ℝ), x ∂(μ : Measure ℝ) = m) :
    (negativeNonnegativeTwoPointKernel ∘ₘ twoPointMixingMeasure μ m)
        (s ∩ Set.Iio (0 : ℝ)) =
      (μ : Measure ℝ) (s ∩ Set.Iio (0 : ℝ)) := by
  -- Proof comment: on the negative half-line the fiber kernel only keeps the Dirac mass at `u`,
  -- so after multiplying by the density `((v - u) / m)` the integrand factors as the indicator of
  -- the negative-side event times the normalized positive coordinate `v / m`.
  classical
  let density := fun z : Set.Iio (0 : ℝ) × Set.Ici (0 : ℝ) ↦
    ENNReal.ofReal (((z.2 : ℝ) - z.1) / m)
  have hdensity :
      AEMeasurable density (twoPointMixingBaseMeasure μ) := by
    exact (Measurable.ennreal_ofReal (by fun_prop)).aemeasurable
  rw [Measure.bind_apply (hs.inter measurableSet_Iio) (Kernel.aemeasurable _),
    twoPointMixingMeasure, lintegral_withDensity_eq_lintegral_mul₀ hdensity
      ((Kernel.measurable_coe _ (hs.inter measurableSet_Iio)).aemeasurable)]
  let negFirst := fun u : {x : ℝ // x < 0} ↦
    if (u : ℝ) ∈ s then (1 : ENNReal) else (0 : ENNReal)
  have hfactor :
      (fun z : Set.Iio (0 : ℝ) × Set.Ici (0 : ℝ) ↦
          density z * negativeNonnegativeTwoPointKernel z (s ∩ Set.Iio (0 : ℝ))) =
        fun z ↦
          negFirst z.1 *
            ENNReal.ofReal ((z.2 : ℝ) / m) := by
    funext z
    rcases z with ⟨u, v⟩
    have huv : (u : ℝ) < v := lt_of_lt_of_le u.2 v.2
    have hdenom : 0 < (v : ℝ) - (u : ℝ) := sub_pos.mpr huv
    have hdensity_nonneg : 0 ≤ (((v : ℝ) - (u : ℝ)) / m) := by
      exact div_nonneg hdenom.le hm.le
    have hkernel_nonneg : 0 ≤ (v : ℝ) / ((v : ℝ) - (u : ℝ)) := by
      exact div_nonneg v.2 hdenom.le
    have hcancel :
        ENNReal.ofReal (((v : ℝ) - (u : ℝ)) / m) *
            ENNReal.ofReal ((v : ℝ) / ((v : ℝ) - (u : ℝ))) =
          ENNReal.ofReal ((v : ℝ) / m) := by
      rw [← ENNReal.ofReal_mul hdensity_nonneg]
      have hreal :
          (((v : ℝ) - (u : ℝ)) / m) * ((v : ℝ) / ((v : ℝ) - (u : ℝ))) =
            (v : ℝ) / m := by
        field_simp [hm.ne', hdenom.ne']
      rw [hreal]
    by_cases hu : (u : ℝ) ∈ s
    · have hkernel :
          negativeNonnegativeTwoPointKernel (u, v) (s ∩ Set.Iio (0 : ℝ)) =
            ENNReal.ofReal ((v : ℝ) / ((v : ℝ) - (u : ℝ))) := by
        have huNeg : (u : ℝ) < 0 := u.2
        have hvNonneg : 0 ≤ (v : ℝ) := v.2
        have huMem : (u : ℝ) ∈ s ∩ Set.Iio (0 : ℝ) := by
          exact ⟨hu, huNeg⟩
        have hvNotMem : (v : ℝ) ∉ s ∩ Set.Iio (0 : ℝ) := by
          rintro ⟨_, hvIio⟩
          exact not_lt_of_ge hvNonneg hvIio
        rw [negativeNonnegativeTwoPointKernel_apply, Measure.add_apply]
        simp [hs.inter measurableSet_Iio, huMem, smul_eq_mul]
      calc
        density (u, v) * negativeNonnegativeTwoPointKernel (u, v) (s ∩ Set.Iio (0 : ℝ))
            = density (u, v) * ENNReal.ofReal ((v : ℝ) / ((v : ℝ) - (u : ℝ))) := by
                  rw [hkernel]
        _ = ENNReal.ofReal (((v : ℝ) - (u : ℝ)) / m) *
              ENNReal.ofReal ((v : ℝ) / ((v : ℝ) - (u : ℝ))) := by
                simp [density]
        _ = ENNReal.ofReal ((v : ℝ) / m) := hcancel
        _ = negFirst u * ENNReal.ofReal ((v : ℝ) / m) := by
              simp [negFirst, hu]
    · have hkernel :
          negativeNonnegativeTwoPointKernel (u, v) (s ∩ Set.Iio (0 : ℝ)) = 0 := by
        have hvNonneg : 0 ≤ (v : ℝ) := v.2
        have huNotMem : (u : ℝ) ∉ s ∩ Set.Iio (0 : ℝ) := by
          rintro ⟨huMem, _⟩
          exact hu huMem
        have hvNotMem : (v : ℝ) ∉ s ∩ Set.Iio (0 : ℝ) := by
          rintro ⟨_, hvIio⟩
          exact not_lt_of_ge hvNonneg hvIio
        rw [negativeNonnegativeTwoPointKernel_apply, Measure.add_apply]
        simp [hs.inter measurableSet_Iio, huNotMem, smul_eq_mul]
      calc
        density (u, v) * negativeNonnegativeTwoPointKernel (u, v) (s ∩ Set.Iio (0 : ℝ))
            = density (u, v) * 0 := by rw [hkernel]
        _ = negFirst u * ENNReal.ofReal ((v : ℝ) / m) := by
              simp [density, negFirst, hu]
  change
    ∫⁻ a : Set.Iio (0 : ℝ) × Set.Ici (0 : ℝ),
        density a * negativeNonnegativeTwoPointKernel a (s ∩ Set.Iio (0 : ℝ))
        ∂twoPointMixingBaseMeasure μ =
      (μ : Measure ℝ) (s ∩ Set.Iio (0 : ℝ))
  rw [hfactor, twoPointMixingBaseMeasure]
  have hfst :
      ∫⁻ u : Set.Iio (0 : ℝ), negFirst u
          ∂Measure.comap Subtype.val (μ : Measure ℝ) =
        (μ : Measure ℝ) (s ∩ Set.Iio (0 : ℝ)) := by
    calc
      ∫⁻ u : Set.Iio (0 : ℝ), negFirst u ∂Measure.comap Subtype.val (μ : Measure ℝ) =
          ∫⁻ x in Set.Iio (0 : ℝ), (if x ∈ s then (1 : ENNReal) else 0) ∂(μ : Measure ℝ) := by
            simpa [negFirst] using
              (lintegral_subtype_comap (μ := (μ : Measure ℝ)) measurableSet_Iio
                (fun x : ℝ ↦ if x ∈ s then (1 : ENNReal) else 0))
      _ = (μ : Measure ℝ) (s ∩ Set.Iio (0 : ℝ)) := by
            simpa [Set.inter_comm, Set.indicator] using
              (lintegral_indicator_one (μ := (μ : Measure ℝ).restrict (Set.Iio (0 : ℝ))) hs)
  have hnegFirstAEMeasurable :
      AEMeasurable negFirst (Measure.comap Subtype.val (μ : Measure ℝ)) := by
    have hnegFirstMeasurable : Measurable negFirst := by
      simpa [negFirst, Set.indicator] using
        ((Measurable.indicator measurable_const hs).comp measurable_subtype_coe)
    exact hnegFirstMeasurable.aemeasurable
  calc
    ∫⁻ z : Set.Iio (0 : ℝ) × Set.Ici (0 : ℝ),
        negFirst z.1 * ENNReal.ofReal ((z.2 : ℝ) / m) ∂
          (Measure.comap Subtype.val (μ : Measure ℝ)).prod
            (Measure.comap Subtype.val (μ : Measure ℝ)) =
      (∫⁻ u : Set.Iio (0 : ℝ), negFirst u ∂Measure.comap Subtype.val (μ : Measure ℝ)) *
        ∫⁻ v : Set.Ici (0 : ℝ), ENNReal.ofReal ((v : ℝ) / m)
          ∂Measure.comap Subtype.val (μ : Measure ℝ) := by
          simpa using
            (lintegral_prod_mul
              (μ := Measure.comap Subtype.val (μ : Measure ℝ))
              (ν := Measure.comap Subtype.val (μ : Measure ℝ))
              (f := negFirst)
              (g := fun v : Set.Ici (0 : ℝ) ↦ ENNReal.ofReal ((v : ℝ) / m))
              hnegFirstAEMeasurable
              ((Measurable.ennreal_ofReal (by fun_prop)).aemeasurable))
    _ = (μ : Measure ℝ) (s ∩ Set.Iio (0 : ℝ)) := by
          rw [hfst, positivePartScaledLIntegral_eq_one μ hint hm hmdef, mul_one]

/-- Helper for Lemma 22.8: on the nonnegative half-line, the `withDensity` mixing law reproduces
the nonnegative part of `μ`. -/
private lemma twoPointMixingMeasure_apply_Ici
    (μ : ProbabilityMeasure ℝ)
    (hint : Integrable (fun x : ℝ ↦ x) (μ : Measure ℝ))
    {m : ℝ} (hm : 0 < m) {s : Set ℝ} (hs : MeasurableSet s)
    (hmdef : ∫ x in Set.Iio (0 : ℝ), -x ∂(μ : Measure ℝ) = m) :
    (negativeNonnegativeTwoPointKernel ∘ₘ twoPointMixingMeasure μ m)
        (s ∩ Set.Ici (0 : ℝ)) =
      (μ : Measure ℝ) (s ∩ Set.Ici (0 : ℝ)) := by
  -- Proof comment: on `[0,∞)` only the Dirac mass at `v` survives, so the same factorization
  -- argument now leaves the normalized negative coordinate `(-u) / m`.
  classical
  let density := fun z : Set.Iio (0 : ℝ) × Set.Ici (0 : ℝ) ↦
    ENNReal.ofReal (((z.2 : ℝ) - z.1) / m)
  have hdensity :
      AEMeasurable density (twoPointMixingBaseMeasure μ) := by
    exact (Measurable.ennreal_ofReal (by fun_prop)).aemeasurable
  rw [Measure.bind_apply (hs.inter measurableSet_Ici) (Kernel.aemeasurable _),
    twoPointMixingMeasure, lintegral_withDensity_eq_lintegral_mul₀ hdensity
      ((Kernel.measurable_coe _ (hs.inter measurableSet_Ici)).aemeasurable)]
  let posSecond := fun v : {x : ℝ // 0 ≤ x} ↦
    if (v : ℝ) ∈ s then (1 : ENNReal) else (0 : ENNReal)
  have hfactor :
      (fun z : Set.Iio (0 : ℝ) × Set.Ici (0 : ℝ) ↦
          density z * negativeNonnegativeTwoPointKernel z (s ∩ Set.Ici (0 : ℝ))) =
        fun z ↦
          ENNReal.ofReal (-(z.1 : ℝ) / m) *
            posSecond z.2 := by
    funext z
    rcases z with ⟨u, v⟩
    have huv : (u : ℝ) < v := lt_of_lt_of_le u.2 v.2
    have hdenom : 0 < (v : ℝ) - (u : ℝ) := sub_pos.mpr huv
    have hdensity_nonneg : 0 ≤ (((v : ℝ) - (u : ℝ)) / m) := by
      exact div_nonneg hdenom.le hm.le
    have hkernel_nonneg : 0 ≤ (-(u : ℝ)) / ((v : ℝ) - (u : ℝ)) := by
      exact div_nonneg (neg_nonneg.mpr u.2.le) hdenom.le
    have hcancel :
        ENNReal.ofReal (((v : ℝ) - (u : ℝ)) / m) *
            ENNReal.ofReal (-(u : ℝ) / ((v : ℝ) - (u : ℝ))) =
          ENNReal.ofReal (-(u : ℝ) / m) := by
      rw [← ENNReal.ofReal_mul hdensity_nonneg]
      have hreal :
          (((v : ℝ) - (u : ℝ)) / m) * (-(u : ℝ) / ((v : ℝ) - (u : ℝ))) =
            -(u : ℝ) / m := by
        field_simp [hm.ne', hdenom.ne']
      rw [hreal]
    by_cases hv : (v : ℝ) ∈ s
    · have hkernel :
          negativeNonnegativeTwoPointKernel (u, v) (s ∩ Set.Ici (0 : ℝ)) =
            ENNReal.ofReal (-(u : ℝ) / ((v : ℝ) - (u : ℝ))) := by
        have huNeg : (u : ℝ) < 0 := u.2
        have hvNonneg : 0 ≤ (v : ℝ) := v.2
        have huNotMem : (u : ℝ) ∉ s ∩ Set.Ici (0 : ℝ) := by
          rintro ⟨_, huIci⟩
          exact not_le.mpr huNeg huIci
        have hvMem : (v : ℝ) ∈ s ∩ Set.Ici (0 : ℝ) := by
          exact ⟨hv, hvNonneg⟩
        rw [negativeNonnegativeTwoPointKernel_apply, Measure.add_apply]
        simp only [Measure.coe_smul, Pi.smul_apply, smul_eq_mul]
        rw [Measure.dirac_apply, Measure.dirac_apply]
        rw [Set.indicator_of_notMem huNotMem, Set.indicator_of_mem hvMem]
        simp
      calc
        density (u, v) * negativeNonnegativeTwoPointKernel (u, v) (s ∩ Set.Ici (0 : ℝ))
            = density (u, v) * ENNReal.ofReal (-(u : ℝ) / ((v : ℝ) - (u : ℝ))) := by
                  rw [hkernel]
        _ = ENNReal.ofReal (((v : ℝ) - (u : ℝ)) / m) *
              ENNReal.ofReal (-(u : ℝ) / ((v : ℝ) - (u : ℝ))) := by
                simp [density]
        _ = ENNReal.ofReal (-(u : ℝ) / m) := hcancel
        _ = ENNReal.ofReal (-(u : ℝ) / m) * posSecond v := by
              have hposSecond : posSecond v = 1 := by
                simpa [posSecond] using
                  (if_pos hv : (if (v : ℝ) ∈ s then (1 : ENNReal) else 0) = 1)
              rw [hposSecond, mul_one]
    · have hkernel :
          negativeNonnegativeTwoPointKernel (u, v) (s ∩ Set.Ici (0 : ℝ)) = 0 := by
        have huNeg : (u : ℝ) < 0 := u.2
        have huNotMem : (u : ℝ) ∉ s ∩ Set.Ici (0 : ℝ) := by
          rintro ⟨_, huIci⟩
          exact not_le.mpr huNeg huIci
        have hvNotMem : (v : ℝ) ∉ s ∩ Set.Ici (0 : ℝ) := by
          rintro ⟨hvMem, _⟩
          exact hv hvMem
        rw [negativeNonnegativeTwoPointKernel_apply, Measure.add_apply]
        simp only [Measure.coe_smul, Pi.smul_apply, smul_eq_mul]
        rw [Measure.dirac_apply, Measure.dirac_apply]
        rw [Set.indicator_of_notMem huNotMem, Set.indicator_of_notMem hvNotMem]
        simp
      calc
        density (u, v) * negativeNonnegativeTwoPointKernel (u, v) (s ∩ Set.Ici (0 : ℝ))
            = density (u, v) * 0 := by rw [hkernel]
        _ = ENNReal.ofReal (-(u : ℝ) / m) * posSecond v := by
              have hposSecond : posSecond v = 0 := by
                simpa [posSecond] using
                  (if_neg hv : (if (v : ℝ) ∈ s then (1 : ENNReal) else 0) = 0)
              rw [hposSecond]
              simp [density]
  change
    ∫⁻ a : Set.Iio (0 : ℝ) × Set.Ici (0 : ℝ),
        density a * negativeNonnegativeTwoPointKernel a (s ∩ Set.Ici (0 : ℝ))
        ∂twoPointMixingBaseMeasure μ =
      (μ : Measure ℝ) (s ∩ Set.Ici (0 : ℝ))
  rw [hfactor, twoPointMixingBaseMeasure]
  have hsnd :
      ∫⁻ v : Set.Ici (0 : ℝ), posSecond v
          ∂Measure.comap Subtype.val (μ : Measure ℝ) =
        (μ : Measure ℝ) (s ∩ Set.Ici (0 : ℝ)) := by
    calc
      ∫⁻ v : Set.Ici (0 : ℝ), posSecond v ∂Measure.comap Subtype.val (μ : Measure ℝ) =
          ∫⁻ x in Set.Ici (0 : ℝ), (if x ∈ s then (1 : ENNReal) else 0) ∂(μ : Measure ℝ) := by
            simpa [posSecond] using
              (lintegral_subtype_comap (μ := (μ : Measure ℝ)) measurableSet_Ici
                (fun x : ℝ ↦ if x ∈ s then (1 : ENNReal) else 0))
      _ = (μ : Measure ℝ) (s ∩ Set.Ici (0 : ℝ)) := by
            simpa [Set.inter_comm, Set.indicator] using
              (lintegral_indicator_one (μ := (μ : Measure ℝ).restrict (Set.Ici (0 : ℝ))) hs)
  have hposSecondAEMeasurable :
      AEMeasurable posSecond (Measure.comap Subtype.val (μ : Measure ℝ)) := by
    have hposSecondMeasurable : Measurable posSecond := by
      simpa [posSecond, Set.indicator] using
        ((Measurable.indicator measurable_const hs).comp measurable_subtype_coe)
    exact hposSecondMeasurable.aemeasurable
  calc
    ∫⁻ z : Set.Iio (0 : ℝ) × Set.Ici (0 : ℝ),
        ENNReal.ofReal (-(z.1 : ℝ) / m) * posSecond z.2 ∂
          (Measure.comap Subtype.val (μ : Measure ℝ)).prod
            (Measure.comap Subtype.val (μ : Measure ℝ)) =
      (∫⁻ u : Set.Iio (0 : ℝ), ENNReal.ofReal (-(u : ℝ) / m)
          ∂Measure.comap Subtype.val (μ : Measure ℝ)) *
        ∫⁻ v : Set.Ici (0 : ℝ), posSecond v ∂Measure.comap Subtype.val (μ : Measure ℝ) := by
          simpa using
            (lintegral_prod_mul
              (μ := Measure.comap Subtype.val (μ : Measure ℝ))
              (ν := Measure.comap Subtype.val (μ : Measure ℝ))
              (f := fun u : Set.Iio (0 : ℝ) ↦ ENNReal.ofReal (-(u : ℝ) / m))
              (g := posSecond)
              ((Measurable.ennreal_ofReal (by fun_prop)).aemeasurable)
              hposSecondAEMeasurable)
    _ = (μ : Measure ℝ) (s ∩ Set.Ici (0 : ℝ)) := by
          rw [negativePartScaledLIntegral_eq_one μ hint hm hmdef, hsnd, one_mul]

/-- Helper for Lemma 22.8: the second moment of a mixture of centered two-point fibers is the
average of the fiber second moments. -/
private lemma secondMoment_comp_negativeNonnegativeTwoPointKernel
    (θ : ProbabilityMeasure (Set.Iio (0 : ℝ) × Set.Ici (0 : ℝ)))
    (hint :
      Integrable (fun x : ℝ ↦ x ^ 2)
        (negativeNonnegativeTwoPointKernel ∘ₘ
          (θ : Measure (Set.Iio (0 : ℝ) × Set.Ici (0 : ℝ))))) :
    ∫ x, x ^ 2
        ∂(negativeNonnegativeTwoPointKernel ∘ₘ
          (θ : Measure (Set.Iio (0 : ℝ) × Set.Ici (0 : ℝ)))) =
      ∫ z, -((z.1 : ℝ) * z.2)
        ∂(θ : Measure (Set.Iio (0 : ℝ) × Set.Ici (0 : ℝ))) := by
  -- Proof comment: rewrite the measure composition as a kernel composition with a constant
  -- source kernel, apply the standard integral formula for `∘ₖ`, and then insert the explicit
  -- second moment of each fiber.
  let κ : Kernel Unit (Set.Iio (0 : ℝ) × Set.Ici (0 : ℝ)) :=
    Kernel.const Unit (θ : Measure (Set.Iio (0 : ℝ) × Set.Ici (0 : ℝ)))
  have hcomp :
      negativeNonnegativeTwoPointKernel ∘ₘ
          (θ : Measure (Set.Iio (0 : ℝ) × Set.Ici (0 : ℝ))) =
        (negativeNonnegativeTwoPointKernel ∘ₖ κ) () := by
    change negativeNonnegativeTwoPointKernel ∘ₘ
        (θ : Measure (Set.Iio (0 : ℝ) × Set.Ici (0 : ℝ))) =
      (negativeNonnegativeTwoPointKernel ∘ₖ
        Kernel.const Unit (θ : Measure (Set.Iio (0 : ℝ) × Set.Ici (0 : ℝ)))) ()
    exact MeasureTheory.Measure.comp_eq_comp_const_apply
      (κ := negativeNonnegativeTwoPointKernel)
      (μ := (θ : Measure (Set.Iio (0 : ℝ) × Set.Ici (0 : ℝ))))
  have hIntComp :
      Integrable (fun x : ℝ ↦ x ^ 2) ((negativeNonnegativeTwoPointKernel ∘ₖ κ) ()) := by
    simpa [hcomp] using hint
  calc
    ∫ x, x ^ 2
        ∂(negativeNonnegativeTwoPointKernel ∘ₘ
          (θ : Measure (Set.Iio (0 : ℝ) × Set.Ici (0 : ℝ))))
        = ∫ x, x ^ 2 ∂((negativeNonnegativeTwoPointKernel ∘ₖ κ) ()) := by
            rw [hcomp]
    _ = ∫ z, ∫ x, x ^ 2 ∂negativeNonnegativeTwoPointKernel z
          ∂(θ : Measure (Set.Iio (0 : ℝ) × Set.Ici (0 : ℝ))) := by
            simpa [κ] using
              (ProbabilityTheory.Kernel.integral_comp
                (a := ())
                (κ := κ)
                (η := negativeNonnegativeTwoPointKernel)
                (f := fun x : ℝ ↦ x ^ 2)
                hIntComp)
    _ = ∫ z, -((z.1 : ℝ) * z.2)
          ∂(θ : Measure (Set.Iio (0 : ℝ) × Set.Ici (0 : ℝ))) := by
            refine integral_congr_ae ?_
            exact ae_of_all _ negativeNonnegativeTwoPointKernel_secondMoment

-- Proof sketch: split `μ` into its negative and nonnegative parts, use the textbook construction
-- of the mixing law `θ` on `(-∞,0) × [0,∞)`, identify `μ` with the resulting kernel mixture
-- mixture of the centered two-point laws, and then compute the second moment by integrating the
-- explicit second moment of each two-point law.
/-- Lemma 22.8: every centered probability measure on `ℝ` with finite second moment is a mixture
of centered two-point laws supported on one negative and one nonnegative point, and its second
moment is the negative `uv`-moment of the mixing measure. -/
theorem exists_centered_two_point_mixture
    (μ : ProbabilityMeasure ℝ)
    (h_mean : ∫ x, x ∂(μ : Measure ℝ) = 0)
    (h_sq : Integrable (fun x : ℝ ↦ x ^ 2) (μ : Measure ℝ)) :
    ∃ θ : ProbabilityMeasure (Set.Iio (0 : ℝ) × Set.Ici (0 : ℝ)),
      (μ : Measure ℝ) =
        negativeNonnegativeTwoPointKernel ∘ₘ
          (θ : Measure (Set.Iio (0 : ℝ) × Set.Ici (0 : ℝ))) ∧
      ∫ x, x ^ 2 ∂(μ : Measure ℝ) =
        ∫ z, -((z.1 : ℝ) * z.2) ∂(θ : Measure (Set.Iio (0 : ℝ) × Set.Ici (0 : ℝ))) :=
  by
  -- Proof comment: split on the positive first moment. The degenerate branch gives `μ = dirac 0`,
  -- while the nondegenerate branch uses the textbook `withDensity` construction and glues its two
  -- half-line restrictions into the full mixture identity.
  let m : ℝ := ∫ x in Set.Ici (0 : ℝ), x ∂(μ : Measure ℝ)
  have hint : Integrable (fun x : ℝ ↦ x) (μ : Measure ℝ) := integrable_id_of_integrable_sq h_sq
  have hpm : m = ∫ x in Set.Iio (0 : ℝ), -x ∂(μ : Measure ℝ) := by
    simpa [m] using positiveNegativeFirstMoment_eq hint h_mean
  by_cases hm0 : m = 0
  · let u0 : Set.Iio (0 : ℝ) := ⟨-1, by norm_num⟩
    let v0 : Set.Ici (0 : ℝ) := ⟨0, by simp⟩
    let θ : ProbabilityMeasure (Set.Iio (0 : ℝ) × Set.Ici (0 : ℝ)) :=
      ⟨Measure.dirac (u0, v0), Measure.dirac.isProbabilityMeasure⟩
    have hμdirac : (μ : Measure ℝ) = Measure.dirac 0 := by
      exact eq_dirac_zero_of_positivePartMeanZero μ hint h_mean hm0
    have hmix :
        (μ : Measure ℝ) =
          negativeNonnegativeTwoPointKernel ∘ₘ
            (θ : Measure (Set.Iio (0 : ℝ) × Set.Ici (0 : ℝ))) := by
      rw [hμdirac]
      ext s hs
      rw [Measure.bind_apply hs (Kernel.aemeasurable _)]
      simp [θ, u0, v0, negativeNonnegativeTwoPointKernel_apply, hs]
    refine ⟨θ, hmix, ?_⟩
    rw [hμdirac]
    calc
      ∫ x, x ^ 2 ∂(Measure.dirac (0 : ℝ)) = 0 := by simp
      _ = -((u0 : ℝ) * v0) := by
            norm_num [u0, v0]
      _ = ∫ z, -((z.1 : ℝ) * z.2) ∂(θ : Measure (Set.Iio (0 : ℝ) × Set.Ici (0 : ℝ))) := by
            simp [θ]
  · have hm_nonneg : 0 ≤ m := by
      exact MeasureTheory.setIntegral_nonneg_ae measurableSet_Ici
        (ae_of_all _ fun x hx ↦ hx)
    have hm : 0 < m := lt_of_le_of_ne hm_nonneg (by simpa [eq_comm] using hm0)
    let θm : Measure (Set.Iio (0 : ℝ) × Set.Ici (0 : ℝ)) := twoPointMixingMeasure μ m
    have hmix :
        (μ : Measure ℝ) = negativeNonnegativeTwoPointKernel ∘ₘ θm := by
      ext s hs
      have hpart :
          s = (s ∩ Set.Iio (0 : ℝ)) ∪ (s ∩ Set.Ici (0 : ℝ)) := by
        ext x
        by_cases hx : x < 0
        · have hx0 : ¬0 ≤ x := not_le.mpr hx
          simp [hx, hx0]
        · have hx0 : 0 ≤ x := le_of_not_gt hx
          simp [hx, hx0]
      have hdisj :
          Disjoint (s ∩ Set.Iio (0 : ℝ)) (s ∩ Set.Ici (0 : ℝ)) := by
        refine Set.disjoint_left.2 ?_
        intro x hxIio hxIci
        have hxNotLt : ¬ x < 0 := not_lt_of_ge hxIci.2
        exact hxNotLt hxIio.2
      have hIio :
          (negativeNonnegativeTwoPointKernel ∘ₘ θm) (s ∩ Set.Iio (0 : ℝ)) =
            (μ : Measure ℝ) (s ∩ Set.Iio (0 : ℝ)) := by
        simpa [θm] using
          twoPointMixingMeasure_apply_Iio μ hint hm hs (by simp [m])
      have hIci :
          (negativeNonnegativeTwoPointKernel ∘ₘ θm) (s ∩ Set.Ici (0 : ℝ)) =
            (μ : Measure ℝ) (s ∩ Set.Ici (0 : ℝ)) := by
        simpa [θm] using
          twoPointMixingMeasure_apply_Ici μ hint hm hs (by simpa [m] using hpm.symm)
      have hpart' : (s ∩ Set.Iio (0 : ℝ)) ∪ (s ∩ Set.Ici (0 : ℝ)) = s := by
        simpa using hpart.symm
      calc
        (μ : Measure ℝ) s
            = (μ : Measure ℝ) ((s ∩ Set.Iio (0 : ℝ)) ∪ (s ∩ Set.Ici (0 : ℝ))) := by
                rw [hpart']
        _ = (μ : Measure ℝ) (s ∩ Set.Iio (0 : ℝ)) + (μ : Measure ℝ) (s ∩ Set.Ici (0 : ℝ)) := by
              exact measure_union hdisj (hs.inter measurableSet_Ici)
        _ = (negativeNonnegativeTwoPointKernel ∘ₘ θm) (s ∩ Set.Iio (0 : ℝ)) +
              (negativeNonnegativeTwoPointKernel ∘ₘ θm) (s ∩ Set.Ici (0 : ℝ)) := by
                rw [hIio, hIci]
        _ = (negativeNonnegativeTwoPointKernel ∘ₘ θm)
              ((s ∩ Set.Iio (0 : ℝ)) ∪ (s ∩ Set.Ici (0 : ℝ))) := by
                exact (measure_union hdisj (hs.inter measurableSet_Ici)).symm
        _ = (negativeNonnegativeTwoPointKernel ∘ₘ θm) s := by
              rw [hpart']
    have hθm_univ : θm Set.univ = 1 := by
      have hcompUniv :
          (negativeNonnegativeTwoPointKernel ∘ₘ θm) Set.univ = θm Set.univ := by
        simp
      calc
        θm Set.univ = (negativeNonnegativeTwoPointKernel ∘ₘ θm) Set.univ := by
          exact hcompUniv.symm
        _ = (μ : Measure ℝ) Set.univ := by rw [hmix]
        _ = 1 := by simp
    let θ : ProbabilityMeasure (Set.Iio (0 : ℝ) × Set.Ici (0 : ℝ)) := ⟨θm, ⟨hθm_univ⟩⟩
    refine ⟨θ, ?_, ?_⟩
    · simpa [θ] using hmix
    · have hInt :
          Integrable (fun x : ℝ ↦ x ^ 2)
            (negativeNonnegativeTwoPointKernel ∘ₘ
              (θ : Measure (Set.Iio (0 : ℝ) × Set.Ici (0 : ℝ)))) := by
        simpa [θ, hmix] using h_sq
      simpa [θ, hmix] using secondMoment_comp_negativeNonnegativeTwoPointKernel θ hInt

end ProbabilityTheory
