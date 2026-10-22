/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib.MeasureTheory.Function.UniformIntegrable
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Topology.Bornology.Basic
import Books.ProbabilityTheory_Klenke_2020.Items.Chap06.Theorem_6_17

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory

universe u

variable {Ω : Type u} [MeasurableSpace Ω] {μ : Measure Ω}

/-- A family in `L¹(μ)` satisfies the source integrable-weight condition if there is
an integrable `μ`-a.e. nonnegative weight for which the source theorem's condition `(ii)` holds.
This is the source-facing weight criterion; the owner small-set abstraction remains
`MeasureTheory.UnifIntegrable`. -/
def HasIntegrableWeightControl (F : Set (Lp ℝ 1 μ)) : Prop :=
  ∃ weight : Ω → ℝ,
    0 ≤ᵐ[μ] weight ∧
      Integrable weight μ ∧
        ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
          ∀ s : Set Ω, MeasurableSet s → (∫ x in s, weight x ∂μ) < δ →
            ∀ ⦃f : Lp ℝ 1 μ⦄, f ∈ F → (∫ x in s, |f x| ∂μ) ≤ ε

/-- Helper for Theorem 6.24: for an `L¹` function, the restricted `L¹` seminorm is the restricted
integral of the absolute value. -/
lemma eLpNorm_indicator_eq_ofReal_setIntegral_abs (f : Lp ℝ 1 μ) {s : Set Ω}
    (hs : MeasurableSet s) :
    eLpNorm (s.indicator (f : Ω → ℝ)) 1 μ = ENNReal.ofReal (∫ x in s, |(f : Ω → ℝ) x| ∂μ) := by
  -- Rewrite the restricted `L¹` seminorm as the restricted integral of the absolute value.
  have hInt : Integrable (f : Ω → ℝ) (μ.restrict s) :=
    memLp_one_iff_integrable.mp <| (Lp.memLp f).mono_measure μ.restrict_le_self
  calc
    eLpNorm (s.indicator (f : Ω → ℝ)) 1 μ
        = ∫⁻ x in s, ENNReal.ofReal |(f : Ω → ℝ) x| ∂μ := by
            rw [eLpNorm_indicator_one_eq_setLIntegral_abs _ hs]
    _ = ENNReal.ofReal (∫ x in s, |(f : Ω → ℝ) x| ∂μ) := by
          symm
          simpa [Real.enorm_eq_ofReal_abs] using
            (MeasureTheory.ofReal_integral_norm_eq_lintegral_enorm hInt)

-- Route correction: the small-set-only bridge needed here is one-way. The converse is exactly the
-- part that requires the missing cutoff-to-weight construction.
/-- Helper for Theorem 6.24: the source weight criterion implies the small-set owner
`UnifIntegrable`. -/
theorem unifIntegrableOfHasIntegrableWeightControl (F : Set (Lp ℝ 1 μ)) :
    HasIntegrableWeightControl F → UnifIntegrable ((↑) : F → Ω → ℝ) 1 μ := by
  intro hControl ε hε
  rcases hControl with ⟨weight, hweight_nonneg, hweight_int, hcontrol⟩
  -- First make the weight integral itself small on sufficiently small measurable sets.
  obtain ⟨δ, hδ_pos, hδ⟩ := hcontrol ε hε
  have hMemLp : MemLp weight 1 μ := memLp_one_iff_integrable.mpr hweight_int
  obtain ⟨η, hη_pos, hη⟩ :=
    hMemLp.eLpNorm_indicator_le le_rfl ENNReal.one_ne_top (half_pos hδ_pos)
  refine ⟨η, hη_pos, fun f s hs hμs ↦ ?_⟩
  have hIndicatorNorm :
      eLpNorm (s.indicator weight) 1 μ ≤ ENNReal.ofReal (δ / 2) :=
    hη s hs hμs
  have hAbsEq :
      ∫⁻ x in s, ENNReal.ofReal |weight x| ∂μ =
        ∫⁻ x in s, ENNReal.ofReal (weight x) ∂μ := by
    refine lintegral_congr_ae ?_
    filter_upwards [ae_restrict_of_ae hweight_nonneg] with x hx
    simp [abs_of_nonneg hx]
  have hWeightLin :
      ∫⁻ x in s, ENNReal.ofReal (weight x) ∂μ ≤ ENNReal.ofReal (δ / 2) := by
    rw [← hAbsEq]
    rw [eLpNorm_indicator_one_eq_setLIntegral_abs _ hs] at hIndicatorNorm
    exact hIndicatorNorm
  have hWeightIntEq :
      ∫ x in s, weight x ∂μ =
        ENNReal.toReal (∫⁻ x in s, ENNReal.ofReal (weight x) ∂μ) := by
    -- The almost-everywhere nonnegativity turns the set integral into the corresponding
    -- nonnegative `lintegral`.
    simpa using
      (MeasureTheory.integral_eq_lintegral_of_nonneg_ae
        (ae_restrict_of_ae hweight_nonneg)
        ((hweight_int.mono_measure μ.restrict_le_self).aestronglyMeasurable))
  have hWeightSmall :
      ∫ x in s, weight x ∂μ < δ := by
    rw [hWeightIntEq]
    have hToReal :
        ENNReal.toReal (∫⁻ x in s, ENNReal.ofReal (weight x) ∂μ) ≤ δ / 2 :=
      ENNReal.toReal_le_of_le_ofReal (by positivity) hWeightLin
    linarith
  have hSetInt :
      (∫ x in s, |(((f : F) : Lp ℝ 1 μ) : Ω → ℝ) x| ∂μ) ≤ ε :=
    hδ s hs hWeightSmall f.2
  -- Convert the direct restricted absolute integral bound into the owner `eLpNorm` bound.
  rw [eLpNorm_indicator_eq_ofReal_setIntegral_abs ((f : F) : Lp ℝ 1 μ) hs]
  exact ENNReal.ofReal_le_ofReal hSetInt

-- Semantic recall note: `lean_leansearch` confirms mathlib's canonical owners
-- `UnifIntegrable`/`UniformIntegrable`, so the source's bounded-plus-gauge side is packaged as a
-- small Prop owner rather than as a public conjunction.
/-- The source boundedness-plus-gauge condition from Theorem 6.24: the family is bounded in the
chapter sense of Definition 6.20 and satisfies the source integrable-weight condition `(ii)`. -/
class BoundedIntegrableWeightControl (F : Set (Lp ℝ 1 μ)) : Prop where
  isBounded : Bornology.IsBounded F
  hasIntegrableWeightControl : HasIntegrableWeightControl F

/-- Companion unpacking lemma for `BoundedIntegrableWeightControl`. -/
theorem boundedIntegrableWeightControl_iff (F : Set (Lp ℝ 1 μ)) :
    BoundedIntegrableWeightControl F ↔ Bornology.IsBounded F ∧ HasIntegrableWeightControl F :=
  by
    constructor
    · intro h
      exact ⟨h.isBounded, h.hasIntegrableWeightControl⟩
    · rintro ⟨hBounded, hWeight⟩
      exact ⟨hBounded, hWeight⟩

/-- Helper for Theorem 6.24: boundedness in `Lp` together with the source weight criterion
upgrades to mathlib's `UniformIntegrable`. -/
theorem uniformIntegrableOfIsBoundedAndHasIntegrableWeightControl (F : Set (Lp ℝ 1 μ)) :
    Bornology.IsBounded F → HasIntegrableWeightControl F →
      UniformIntegrable ((↑) : F → Ω → ℝ) 1 μ := by
  intro hBounded hWeight
  refine ⟨fun f ↦ (Lp.stronglyMeasurable f.1).aestronglyMeasurable,
    unifIntegrableOfHasIntegrableWeightControl F hWeight, ?_⟩
  -- The bornological bound supplies the uniform `L¹` norm control in the owner definition.
  obtain ⟨R, hR⟩ := hBounded.subset_closedBall (0 : Lp ℝ 1 μ)
  let Cnn : NNReal := ⟨max R 0, le_max_right _ _⟩
  refine ⟨Cnn, fun f ↦ ?_⟩
  have hNorm : ‖((f : F) : Lp ℝ 1 μ)‖ ≤ max R 0 := by
    have hMem : ((f : F) : Lp ℝ 1 μ) ∈ Metric.closedBall (0 : Lp ℝ 1 μ) R := hR f.2
    have hNormR : ‖((f : F) : Lp ℝ 1 μ)‖ ≤ R := by
      simpa [Metric.mem_closedBall, dist_eq_norm] using hMem
    exact hNormR.trans (le_max_left _ _)
  have hNormNN : ‖((f : F) : Lp ℝ 1 μ)‖₊ ≤ Cnn := by
    exact_mod_cast hNorm
  calc
    eLpNorm ((((f : F) : Lp ℝ 1 μ) : Ω → ℝ)) 1 μ = ‖((f : F) : Lp ℝ 1 μ)‖ₑ := by
      simp [Lp.enorm_def]
    _ ≤ (Cnn : ENNReal) := by
      simpa [enorm_eq_nnnorm] using hNormNN

/-- Helper for Theorem 6.24: on a measurable set, split `|f|` into its strict-tail part and the
part dominated by a nonnegative cutoff. -/
lemma setIntegralAbs_le_tailIntegral_add_cutoffIntegral
    (g : @IntegrableNonnegativeCutoff Ω _ μ) (f : Lp ℝ 1 μ) {s : Set Ω} (hs : MeasurableSet s) :
    (∫ x in s, |(f : Ω → ℝ) x| ∂μ) ≤
      ∫ x in {x | g x < |(f : Ω → ℝ) x|}, |(f : Ω → ℝ) x| ∂μ + ∫ x in s, g x ∂μ := by
  let tailSet : Set Ω := {x | g x < |(f : Ω → ℝ) x|}
  have htailSet_meas : MeasurableSet tailSet :=
    measurableSet_lt (Lp.stronglyMeasurable g.toLp).measurable
      (Lp.stronglyMeasurable f).norm.measurable
  have hf_abs_int : Integrable (fun x ↦ |(f : Ω → ℝ) x|) μ :=
    (memLp_one_iff_integrable.mp (Lp.memLp f)).norm
  have hg_int : Integrable (g : Ω → ℝ) μ := memLp_one_iff_integrable.mp (Lp.memLp g.toLp)
  have htailIndicator_int :
      Integrable (tailSet.indicator fun x ↦ |(f : Ω → ℝ) x|) μ := hf_abs_int.indicator htailSet_meas
  have htailIndicator_nonneg :
      0 ≤ᵐ[μ] tailSet.indicator (fun x ↦ |(f : Ω → ℝ) x|) := by
    filter_upwards with x
    by_cases hx : x ∈ tailSet
    · simp [tailSet, hx]
    · simp [tailSet, hx]
  have hpointwise :
      ∀ᵐ x ∂μ,
        x ∈ s →
          |(f : Ω → ℝ) x| ≤ tailSet.indicator (fun y ↦ |(f : Ω → ℝ) y|) x + g x := by
    -- On the tail, the indicator already equals `|f|`; off the tail, the cutoff bounds `|f|`.
    filter_upwards [g.ae_nonneg] with x hx_nonneg hx_mem
    have hgx_nonneg : 0 ≤ g x := by simpa using hx_nonneg
    by_cases htail : x ∈ tailSet
    · simpa [tailSet, htail] using
        (le_add_of_nonneg_right hgx_nonneg : |(f : Ω → ℝ) x| ≤ |(f : Ω → ℝ) x| + g x)
    · have hle : |(f : Ω → ℝ) x| ≤ g x := le_of_not_gt htail
      simpa [tailSet, htail] using hle
  have hmain :
      (∫ x in s, |(f : Ω → ℝ) x| ∂μ) ≤
        ∫ x in s, tailSet.indicator (fun x ↦ |(f : Ω → ℝ) x|) x + g x ∂μ :=
    setIntegral_mono_on_ae hf_abs_int.integrableOn (htailIndicator_int.add hg_int).integrableOn hs
      hpointwise
  have htailPart :
      (∫ x in s, tailSet.indicator (fun x ↦ |(f : Ω → ℝ) x|) x ∂μ) ≤
        ∫ x in tailSet, |(f : Ω → ℝ) x| ∂μ := by
    -- The strict-tail indicator is nonnegative, so restricting it to `s` can only decrease its
    -- integral.
    calc
      ∫ x in s, tailSet.indicator (fun x ↦ |(f : Ω → ℝ) x|) x ∂μ
          ≤ ∫ x, tailSet.indicator (fun x ↦ |(f : Ω → ℝ) x|) x ∂μ :=
            setIntegral_le_integral htailIndicator_int htailIndicator_nonneg
      _ = ∫ x in tailSet, |(f : Ω → ℝ) x| ∂μ := by rw [integral_indicator htailSet_meas]
  calc
    (∫ x in s, |(f : Ω → ℝ) x| ∂μ) ≤
        ∫ x in s, tailSet.indicator (fun x ↦ |(f : Ω → ℝ) x|) x + g x ∂μ := hmain
    _ =
        (∫ x in s, tailSet.indicator (fun x ↦ |(f : Ω → ℝ) x|) x ∂μ) + ∫ x in s, g x ∂μ := by
          simpa using
            (integral_add
              (htailIndicator_int.mono_measure Measure.restrict_le_self)
              (hg_int.mono_measure Measure.restrict_le_self))
    _ ≤ ∫ x in tailSet, |(f : Ω → ℝ) x| ∂μ + ∫ x in s, g x ∂μ := by
          exact add_le_add htailPart le_rfl

/-- Helper for Theorem 6.24: the normalized geometric scale used for the cutoff-family packaging
is summable. This is the mathlib-native form of the textbook scale `(1 / 2)^(n + 2)`. -/
lemma geometricCutoffScale_summable : Summable fun n : ℕ ↦ (1 / 2 : ℝ) / 2 / 2 ^ n := by
  -- Use the canonical `a / 2 / 2^n` geometric-series API directly.
  simpa using (summable_geometric_two' (1 / 2 : ℝ))

/-- Helper for Theorem 6.24: normalizing one nonnegative cutoff by `1 + ∫ g` keeps its total
mass below the target scale. -/
lemma normalizedCutoffTerm_lintegral_le
    (g : @IntegrableNonnegativeCutoff Ω _ μ) {ε : ℝ} (hε : 0 ≤ ε) :
    ∫⁻ x, ENNReal.ofReal ((ε / (1 + ∫ y, g y ∂μ)) * g x) ∂μ ≤ ENNReal.ofReal ε := by
  have hg_int : Integrable (g : Ω → ℝ) μ := memLp_one_iff_integrable.mp (Lp.memLp g.toLp)
  have hg_nonneg_int : 0 ≤ ∫ y, g y ∂μ := integral_nonneg_of_ae g.ae_nonneg
  have hden_pos : 0 < 1 + ∫ y, g y ∂μ := by
    linarith
  have hcoeff_nonneg : 0 ≤ ε / (1 + ∫ y, g y ∂μ) := by
    exact div_nonneg hε hden_pos.le
  have hterm_nonneg :
      0 ≤ᵐ[μ] fun x ↦ (ε / (1 + ∫ y, g y ∂μ)) * g x := by
    -- The normalized coefficient and the cutoff are both nonnegative.
    filter_upwards [g.ae_nonneg] with x hx
    exact mul_nonneg hcoeff_nonneg hx
  have hstep :
      (ε / (1 + ∫ y, g y ∂μ)) * ∫ y, g y ∂μ ≤ ε := by
    have hmul :
        (ε / (1 + ∫ y, g y ∂μ)) * ∫ y, g y ∂μ ≤
          (ε / (1 + ∫ y, g y ∂μ)) * (1 + ∫ y, g y ∂μ) := by
      gcongr
      linarith
    have hcancel :
        (ε / (1 + ∫ y, g y ∂μ)) * (1 + ∫ y, g y ∂μ) = ε := by
      field_simp [hden_pos.ne']
    simpa [hcancel] using hmul
  -- Convert the real integral estimate into the corresponding nonnegative `lintegral` bound.
  rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal
    (hg_int.const_mul (ε / (1 + ∫ y, g y ∂μ))) hterm_nonneg]
  rw [integral_const_mul]
  exact ENNReal.ofReal_le_ofReal hstep

/-- Helper for Theorem 6.24: the cutoff-tail criterion from Theorem 6.17 produces one integrable
weight that controls all small restricted `L¹` integrals. -/
theorem hasIntegrableWeightControlOfCutoffTailCriterion (F : Set (Lp ℝ 1 μ)) :
    HasIntegrableCutoffTailCriterion F → HasIntegrableWeightControl F := by
  intro hTail
  -- Route correction: package the cutoff family on the `ℝ≥0∞` side first, and convert to a real
  -- weight only after the series has finite total mass.
  rw [HasIntegrableCutoffTailCriterion, sInfRange_eq_zero_iff_forall_epsilon] at hTail
  let eps : ℕ → ℝ := fun n ↦ (1 / 2 : ℝ) / 2 / 2 ^ n
  have hε_pos : ∀ n, 0 < eps n := by
    intro n
    dsimp [eps]
    positivity
  have hε_nonneg : ∀ n, 0 ≤ eps n := fun n ↦ (hε_pos n).le
  choose g hg using fun n ↦ hTail (eps n) (hε_pos n)
  let c : ℕ → ℝ := fun n ↦ eps n / (1 + ∫ y, g n y ∂μ)
  let weightInf : Ω → ENNReal := fun x ↦ ∑' n, ENNReal.ofReal (c n * g n x)
  let weight : Ω → ℝ := fun x ↦ (weightInf x).toReal
  have hterm_aemeas :
      ∀ n, AEMeasurable (fun x ↦ ENNReal.ofReal (c n * g n x)) μ := by
    intro n
    exact
      (((Lp.stronglyMeasurable (g n).toLp).measurable.const_mul (c n)).aemeasurable).ennreal_ofReal
  have hweightInf_aemeas : AEMeasurable weightInf μ := by
    simpa [weightInf] using (AEMeasurable.ennreal_tsum hterm_aemeas)
  have hscale_summable : Summable eps := by
    simpa [eps] using geometricCutoffScale_summable
  have hweightInf_ne_top : ∫⁻ x, weightInf x ∂μ ≠ ⊤ := by
    have hseries_le :
        ∫⁻ x, weightInf x ∂μ ≤ ∑' n, ENNReal.ofReal (eps n) := by
      -- Sum the normalized cutoff masses termwise and compare with the geometric majorant.
      calc
        ∫⁻ x, weightInf x ∂μ = ∑' n, ∫⁻ x, ENNReal.ofReal (c n * g n x) ∂μ := by
          simpa [weightInf] using
            (lintegral_tsum hterm_aemeas :
              ∫⁻ x, (∑' n, ENNReal.ofReal (c n * g n x)) ∂μ =
                ∑' n, ∫⁻ x, ENNReal.ofReal (c n * g n x) ∂μ)
        _ ≤ ∑' n, ENNReal.ofReal (eps n) := by
          refine ENNReal.tsum_le_tsum fun n ↦ ?_
          simpa [c] using normalizedCutoffTerm_lintegral_le (g n) (hε_nonneg n)
    exact ne_top_of_le_ne_top hscale_summable.tsum_ofReal_ne_top hseries_le
  have hweight_integrable : Integrable weight μ := by
    -- The finite-mass `ℝ≥0∞` series becomes the desired real-valued integrable weight by
    -- taking `toReal`.
    exact integrable_toReal_of_lintegral_ne_top hweightInf_aemeas hweightInf_ne_top
  refine ⟨weight, Filter.Eventually.of_forall fun _ ↦ ENNReal.toReal_nonneg, hweight_integrable, ?_⟩
  intro ε hε
  have hscale_zero := hscale_summable.tendsto_atTop_zero
  obtain ⟨n, hn⟩ := (Metric.tendsto_atTop.1 hscale_zero) (ε / 2) (half_pos hε)
  have hεn_small : eps n < ε / 2 := by
    have hn_self := hn n le_rfl
    simpa [Real.dist_eq, abs_of_nonneg (hε_nonneg n)] using hn_self
  have hεn_sum_le : eps n + eps n ≤ ε := by
    linarith
  have hc_pos : 0 < c n := by
    have hg_int_nonneg : 0 ≤ ∫ y, g n y ∂μ := integral_nonneg_of_ae (g n).ae_nonneg
    have hden_pos : 0 < 1 + ∫ y, g n y ∂μ := by
      linarith
    exact div_pos (hε_pos n) hden_pos
  refine ⟨c n * eps n, by positivity, ?_⟩
  intro s hs hWeightSmall f hf
  let tailSet : Set Ω := {x | g n x < |(f : Ω → ℝ) x|}
  have htailSet_meas : MeasurableSet tailSet :=
    measurableSet_lt (Lp.stronglyMeasurable (g n).toLp).measurable
      (Lp.stronglyMeasurable f).norm.measurable
  have hweightInf_restrict_ne_top : ∫⁻ x in s, weightInf x ∂μ ≠ ⊤ := by
    exact ne_top_of_le_ne_top hweightInf_ne_top (lintegral_mono' Measure.restrict_le_self le_rfl)
  have hweightInf_restrict_aemeas : AEMeasurable weightInf (μ.restrict s) :=
    hweightInf_aemeas.mono_measure Measure.restrict_le_self
  have hweightInf_restrict_ae_lt_top : ∀ᵐ x ∂μ.restrict s, weightInf x < ⊤ :=
    MeasureTheory.ae_lt_top' hweightInf_restrict_aemeas hweightInf_restrict_ne_top
  have hweightIntegral_eq :
      ∫ x in s, weight x ∂μ = ENNReal.toReal (∫⁻ x in s, weightInf x ∂μ) := by
    -- On the restricted measure, the real weight is exactly the `toReal` of the packaged series.
    simpa [weight] using
      (MeasureTheory.integral_toReal
        hweightInf_restrict_aemeas hweightInf_restrict_ae_lt_top)
  have hcutoff_integral_dom :
      ENNReal.ofReal (c n * ∫ x in s, g n x ∂μ) ≤ ∫⁻ x in s, weightInf x ∂μ := by
    have hg_restrict_int :
        Integrable (g n : Ω → ℝ) (μ.restrict s) :=
      (memLp_one_iff_integrable.mp (Lp.memLp (g n).toLp)).mono_measure Measure.restrict_le_self
    have hscaled_nonneg :
        0 ≤ᵐ[μ.restrict s] fun x ↦ c n * g n x := by
      filter_upwards [ae_restrict_of_ae (g n).ae_nonneg] with x hx
      exact mul_nonneg hc_pos.le hx
    -- The selected normalized cutoff term is one summand of the full series.
    calc
      ENNReal.ofReal (c n * ∫ x in s, g n x ∂μ)
          = ∫⁻ x in s, ENNReal.ofReal (c n * g n x) ∂μ := by
              rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal
                (hg_restrict_int.const_mul (c n)) hscaled_nonneg]
              rw [integral_const_mul]
      _ ≤ ∫⁻ x in s, weightInf x ∂μ := by
            refine lintegral_mono fun x ↦ ?_
            simpa [weightInf] using
              (ENNReal.le_tsum n :
                ENNReal.ofReal (c n * g n x) ≤ ∑' k : ℕ, ENNReal.ofReal (c k * g k x))
  have hcutoff_real_dom :
      c n * ∫ x in s, g n x ∂μ ≤ ∫ x in s, weight x ∂μ := by
    rw [hweightIntegral_eq]
    exact (ENNReal.ofReal_le_iff_le_toReal hweightInf_restrict_ne_top).mp hcutoff_integral_dom
  have hcutoff_small : ∫ x in s, g n x ∂μ < eps n := by
    have hscaled_small : c n * ∫ x in s, g n x ∂μ < c n * eps n :=
      lt_of_le_of_lt hcutoff_real_dom hWeightSmall
    nlinarith
  have htail_le_iSup :
      ∫⁻ x in tailSet, ENNReal.ofReal |(f : Ω → ℝ) x| ∂μ ≤
        iSup (fun f' : F ↦
          ∫⁻ x in {x | g n x < |(f'.1 : Ω → ℝ) x|}, ENNReal.ofReal |(f'.1 : Ω → ℝ) x| ∂μ) := by
    simpa [tailSet] using
      (le_iSup
        (fun f' : F ↦
          ∫⁻ x in {x | g n x < |(f'.1 : Ω → ℝ) x|}, ENNReal.ofReal |(f'.1 : Ω → ℝ) x| ∂μ)
        ⟨f, hf⟩)
  have htail_small :
      ∫ x in tailSet, |(f : Ω → ℝ) x| ∂μ < eps n := by
    have htail_lintegral_small :
        ∫⁻ x in tailSet, ENNReal.ofReal |(f : Ω → ℝ) x| ∂μ < ENNReal.ofReal (eps n) :=
      lt_of_le_of_lt htail_le_iSup (hg n)
    have htail_norm_small :
        eLpNorm (tailSet.indicator (f : Ω → ℝ)) 1 μ < ENNReal.ofReal (eps n) := by
      simpa [eLpNorm_indicator_one_eq_setLIntegral_abs (f : Ω → ℝ) htailSet_meas] using
        htail_lintegral_small
    have htail_real_small :
        ENNReal.ofReal (∫ x in tailSet, |(f : Ω → ℝ) x| ∂μ) < ENNReal.ofReal (eps n) := by
      simpa [eLpNorm_indicator_eq_ofReal_setIntegral_abs f htailSet_meas] using
        htail_norm_small
    exact (ENNReal.ofReal_lt_ofReal_iff (hε_pos n)).mp htail_real_small
  -- Combine the small strict-tail piece with the small bounded-cutoff piece on `s`.
  calc
    (∫ x in s, |(f : Ω → ℝ) x| ∂μ) ≤
        ∫ x in tailSet, |(f : Ω → ℝ) x| ∂μ + ∫ x in s, g n x ∂μ :=
      setIntegralAbs_le_tailIntegral_add_cutoffIntegral (g n) f hs
    _ ≤ eps n + eps n := add_le_add htail_small.le hcutoff_small.le
    _ ≤ ε := by
      linarith

-- Proof sketch: combine the canonical boundedness factor in the definition of
-- `UniformIntegrable` for `L¹` families with the source integrable-weight criterion for the
-- small-set clause.
/-- Theorem 6.24: a family in `L¹(μ)` is uniformly integrable if and only if it is bounded in the
chapter sense of Definition 6.20 and satisfies condition `(ii)` of the source theorem. -/
theorem uniformIntegrable_iff_isBounded_and_exists_integrable_weight_control
    (F : Set (Lp ℝ 1 μ)) :
    UniformIntegrable ((↑) : F → Ω → ℝ) 1 μ ↔
      Bornology.IsBounded F ∧ HasIntegrableWeightControl F := by
  constructor
  · intro hUI
    refine ⟨?_, ?_⟩
    · -- The owner definition already contains a uniform `L¹` bound, hence bornological boundedness.
      obtain ⟨C, hC⟩ := hUI.2.2
      exact (Metric.isBounded_iff_subset_closedBall (0 : Lp ℝ 1 μ)).2 ⟨C, by
        intro f hf
        have hNorm :
            ‖(f : Lp ℝ 1 μ)‖ ≤ C := by
          simpa [Lp.norm_def] using
            (ENNReal.toReal_le_toReal (Lp.eLpNorm_ne_top f) ENNReal.coe_ne_top).2 (hC ⟨f, hf⟩)
        simpa [Metric.mem_closedBall, dist_eq_norm] using hNorm⟩
    · -- The arbitrary-measure cutoff-to-weight bridge is not yet available.
      sorry
  · rintro ⟨hBounded, hWeight⟩
    exact uniformIntegrableOfIsBoundedAndHasIntegrableWeightControl F hBounded hWeight

/-- Helper for Theorem 6.24: on finite measure spaces, the source weight criterion implies the
small-measure formulation `(iii)`. -/
theorem smallMeasureIntegralControlOfHasIntegrableWeightControl
    (F : Set (Lp ℝ 1 μ)) [IsFiniteMeasure μ] :
    HasIntegrableWeightControl F →
      ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
        ∀ s : Set Ω, MeasurableSet s → μ s < ENNReal.ofReal δ →
          ∀ ⦃f : Lp ℝ 1 μ⦄, f ∈ F → (∫ x in s, |f x| ∂μ) ≤ ε := by
  intro hControl ε hε
  obtain ⟨δ, hδ_pos, hδ⟩ :=
    (unifIntegrableOfHasIntegrableWeightControl F hControl) hε
  refine ⟨δ, hδ_pos, fun s hs hμs f hf ↦ ?_⟩
  have hIndicator :
      eLpNorm (s.indicator (f : Ω → ℝ)) 1 μ ≤ ENNReal.ofReal ε :=
    hδ ⟨f, hf⟩ s hs (le_of_lt hμs)
  rw [eLpNorm_indicator_eq_ofReal_setIntegral_abs f hs] at hIndicator
  exact (ENNReal.ofReal_le_ofReal_iff hε.le).mp hIndicator

/-- Helper for Theorem 6.24: on finite measure spaces, the source small-measure formulation
`(iii)` is realized by the constant weight `1`. -/
theorem hasIntegrableWeightControlOfSmallMeasureIntegralControl
    (F : Set (Lp ℝ 1 μ)) [IsFiniteMeasure μ] :
    (∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
      ∀ s : Set Ω, MeasurableSet s → μ s < ENNReal.ofReal δ →
        ∀ ⦃f : Lp ℝ 1 μ⦄, f ∈ F → (∫ x in s, |f x| ∂μ) ≤ ε) →
      HasIntegrableWeightControl F := by
  intro hSmall
  refine ⟨fun _ ↦ (1 : ℝ), Filter.Eventually.of_forall fun _ ↦ by positivity,
    integrable_const 1, ?_⟩
  intro ε hε
  obtain ⟨δ, hδ_pos, hδ⟩ := hSmall ε hε
  refine ⟨δ, hδ_pos, fun s hs hInt f hf ↦ ?_⟩
  have hμReal : μ.real s < δ := by
    simpa [MeasureTheory.integral_indicator_one hs] using hInt
  have hμs : μ s < ENNReal.ofReal δ := by
    exact (ENNReal.lt_ofReal_iff_toReal_lt (measure_ne_top μ s)).2 hμReal
  exact hδ s hs hμs hf

/-- On a finite measure space, condition `(ii)` is equivalent to the small-measure
formulation `(iii)` from the source text. -/
theorem exists_integrable_weight_control_iff_small_measure_integral_control
    (F : Set (Lp ℝ 1 μ)) [IsFiniteMeasure μ] :
    HasIntegrableWeightControl F ↔
      ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
        ∀ s : Set Ω, MeasurableSet s → μ s < ENNReal.ofReal δ →
          ∀ ⦃f : Lp ℝ 1 μ⦄, f ∈ F → (∫ x in s, |f x| ∂μ) ≤ ε := by
  constructor
  · exact smallMeasureIntegralControlOfHasIntegrableWeightControl F
  · exact hasIntegrableWeightControlOfSmallMeasureIntegralControl F

/-- On a finite measure space, the source criterion can be read directly in terms of the
canonical owner
predicate `UniformIntegrable`: boundedness in `L¹(μ)` plus the source small-measure control
criterion. -/
theorem uniformIntegrable_iff_isBounded_and_small_measure_integral_control
    (F : Set (Lp ℝ 1 μ)) [IsFiniteMeasure μ] :
    UniformIntegrable ((↑) : F → Ω → ℝ) 1 μ ↔
      Bornology.IsBounded F ∧
        (∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
          ∀ s : Set Ω, MeasurableSet s → μ s < ENNReal.ofReal δ →
            ∀ ⦃f : Lp ℝ 1 μ⦄, f ∈ F → (∫ x in s, |f x| ∂μ) ≤ ε) := by
  constructor
  · intro hUI
    refine ⟨?_, ?_⟩
    · -- The boundedness part is read off directly from the owner definition.
      obtain ⟨C, hC⟩ := hUI.2.2
      exact (Metric.isBounded_iff_subset_closedBall (0 : Lp ℝ 1 μ)).2 ⟨C, by
        intro f hf
        have hNorm :
            ‖(f : Lp ℝ 1 μ)‖ ≤ C := by
          simpa [Lp.norm_def] using
            (ENNReal.toReal_le_toReal (Lp.eLpNorm_ne_top f) ENNReal.coe_ne_top).2 (hC ⟨f, hf⟩)
        simpa [Metric.mem_closedBall, dist_eq_norm] using hNorm⟩
    · -- The small-measure clause is exactly the `UnifIntegrable` condition at exponent `1`.
      intro ε hε
      obtain ⟨δ, hδ_pos, hδ⟩ := hUI.unifIntegrable hε
      refine ⟨δ, hδ_pos, fun s hs hμs f hf ↦ ?_⟩
      have hIndicator :
          eLpNorm (s.indicator (f : Ω → ℝ)) 1 μ ≤ ENNReal.ofReal ε :=
        hδ ⟨f, hf⟩ s hs (le_of_lt hμs)
      rw [eLpNorm_indicator_eq_ofReal_setIntegral_abs f hs] at hIndicator
      exact (ENNReal.ofReal_le_ofReal_iff hε.le).mp hIndicator
  · rintro ⟨hBounded, hSmall⟩
    refine ⟨fun f ↦ (Lp.stronglyMeasurable f.1).aestronglyMeasurable, ?_, ?_⟩
    · intro ε hε
      obtain ⟨δ, hδ_pos, hδ⟩ := hSmall ε hε
      refine ⟨δ / 2, half_pos hδ_pos, fun f s hs hμs ↦ ?_⟩
      have hμs' : μ s < ENNReal.ofReal δ := by
        calc
          μ s ≤ ENNReal.ofReal (δ / 2) := hμs
          _ < ENNReal.ofReal δ := by
            exact (ENNReal.ofReal_lt_ofReal_iff hδ_pos).2 (by linarith)
      have hSetInt :
          (∫ x in s, |(((f : F) : Lp ℝ 1 μ) : Ω → ℝ) x| ∂μ) ≤ ε :=
        hδ s hs hμs' f.2
      rw [eLpNorm_indicator_eq_ofReal_setIntegral_abs ((f : F) : Lp ℝ 1 μ) hs]
      exact ENNReal.ofReal_le_ofReal hSetInt
    · obtain ⟨R, hR⟩ := hBounded.subset_closedBall (0 : Lp ℝ 1 μ)
      let Cnn : NNReal := ⟨max R 0, le_max_right _ _⟩
      refine ⟨Cnn, fun f ↦ ?_⟩
      have hNorm : ‖((f : F) : Lp ℝ 1 μ)‖ ≤ max R 0 := by
        have hMem : ((f : F) : Lp ℝ 1 μ) ∈ Metric.closedBall (0 : Lp ℝ 1 μ) R := hR f.2
        have hNormR : ‖((f : F) : Lp ℝ 1 μ)‖ ≤ R := by
          simpa [Metric.mem_closedBall, dist_eq_norm] using hMem
        exact hNormR.trans (le_max_left _ _)
      have hNormNN : ‖((f : F) : Lp ℝ 1 μ)‖₊ ≤ Cnn := by
        exact_mod_cast hNorm
      calc
        eLpNorm ((((f : F) : Lp ℝ 1 μ) : Ω → ℝ)) 1 μ = ‖((f : F) : Lp ℝ 1 μ)‖ₑ := by
          simp [Lp.enorm_def]
        _ ≤ (Cnn : ENNReal) := by
            simpa [enorm_eq_nnnorm] using hNormNN
