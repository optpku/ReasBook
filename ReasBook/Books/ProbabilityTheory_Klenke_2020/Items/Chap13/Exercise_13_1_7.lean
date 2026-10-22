/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib
import Books.ProbabilityTheory_Klenke_2020.Items.Chap13.Exercise_13_1_6

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory Set Filter intervalIntegral
open scoped Pointwise Topology

/-- Helper for Exercise 13.1.7: translated dilates have the expected Lebesgue volume. -/
private lemma translatedSmul_volumeReal {d : ℕ} {C : Set (Fin d → ℝ)}
    (_hC_meas : MeasurableSet C) (x : Fin d → ℝ) {r : ℝ} (hr : 0 < r) :
    volume.real (({x} : Set (Fin d → ℝ)) + r • C) = r ^ d * volume.real C := by
  -- Rewrite the translated dilate by translation invariance and then apply the scaling law.
  have hvol :
      volume (({x} : Set (Fin d → ℝ)) + r • C) = ENNReal.ofReal (r ^ d) * volume C := by
    calc
      volume (({x} : Set (Fin d → ℝ)) + r • C)
        = volume (r • C) := by
            have h :=
              measure_preimage_add_right (μ := volume) x ((fun y : Fin d → ℝ ↦ x + y) '' (r • C))
            simpa [singleton_add, add_comm, add_left_comm, add_assoc] using h.symm
      _ = ENNReal.ofReal (r ^ d) * volume C := by
            simpa [Module.finrank_fin_fun, abs_of_nonneg hr.le] using
              (Measure.addHaar_smul_of_nonneg (μ := volume) hr.le C)
  rw [measureReal_def, hvol, ENNReal.toReal_mul, ENNReal.toReal_ofReal (pow_nonneg hr.le _),
    measureReal_def]

/-- Helper for Exercise 13.1.7: an open bounded set containing `0` has positive Lebesgue volume. -/
private lemma volumeReal_pos_of_open_of_mem_zero {d : ℕ} {C : Set (Fin d → ℝ)}
    (hC_open : IsOpen C) (hC_bounded : Bornology.IsBounded C) (hC_zero : (0 : Fin d → ℝ) ∈ C) :
    0 < volume.real C := by
  -- Open neighborhoods of `0` have positive volume, and boundedness gives finiteness.
  refine ENNReal.toReal_pos (hC_open.measure_pos volume ⟨0, hC_zero⟩).ne' ?_
  exact hC_bounded.measure_lt_top.ne

/-- Helper for Exercise 13.1.7: local integrability gives integrability on every bounded translated
dilate of `C`. -/
private lemma integrableOn_translatedDilate {d : ℕ} {g : (Fin d → ℝ) → ℝ}
    (hg : LocallyIntegrable g volume) {C : Set (Fin d → ℝ)} (hC_bounded : Bornology.IsBounded C)
    (x : Fin d → ℝ) (r : ℝ) (hr : 0 ≤ r) :
    IntegrableOn g (({x} : Set (Fin d → ℝ)) + r • C) volume := by
  -- The translated dilate is bounded, so its closure is compact and local integrability applies.
  obtain ⟨R, hR_pos, hRC⟩ := hC_bounded.subset_closedBall_lt (0 : ℝ) (0 : Fin d → ℝ)
  have hs_subset :
      (({x} : Set (Fin d → ℝ)) + r • C) ⊆ Metric.closedBall x (r * R) :=
    translatedSmul_subset_closedBall (C := C) hRC hr x
  have hs_bounded : Bornology.IsBounded (({x} : Set (Fin d → ℝ)) + r • C) :=
    Bornology.IsBounded.subset Metric.isBounded_closedBall hs_subset
  have hs_compact : IsCompact (closure (({x} : Set (Fin d → ℝ)) + r • C)) :=
    hs_bounded.isCompact_closure
  exact (hg.integrableOn_isCompact hs_compact).mono_set subset_closure

/-- Helper for Exercise 13.1.7: `setAverage` is monotone for globally ordered integrands. -/
private lemma setAverage_mono {d : ℕ} {s : Set (Fin d → ℝ)} {u v : (Fin d → ℝ) → ℝ}
    (hs0 : volume s ≠ 0) (hsfin : volume s ≠ ⊤)
    (hu : IntegrableOn u s volume) (hv : IntegrableOn v s volume)
    (h : ∀ x, u x ≤ v x) :
    ⨍ x in s, u x ∂volume ≤ ⨍ x in s, v x ∂volume := by
  -- Rewrite `setAverage` as an integral against the normalized restricted measure.
  rw [setAverage_eq', setAverage_eq']
  have hu' : Integrable u ((volume s)⁻¹ • volume.restrict s) :=
    (integrable_inv_smul_measure hs0 hsfin).2 hu
  have hv' : Integrable v ((volume s)⁻¹ • volume.restrict s) :=
    (integrable_inv_smul_measure hs0 hsfin).2 hv
  exact integral_mono_ae hu' hv' (Filter.Eventually.of_forall h)

/-- Helper for Exercise 13.1.7: `setAverage` respects addition on integrable summands. -/
private lemma setAverage_add {d : ℕ} {s : Set (Fin d → ℝ)} {u v : (Fin d → ℝ) → ℝ}
    (hs0 : volume s ≠ 0) (hsfin : volume s ≠ ⊤)
    (hu : IntegrableOn u s volume) (hv : IntegrableOn v s volume) :
    ⨍ x in s, (u x + v x) ∂volume = (⨍ x in s, u x ∂volume) + (⨍ x in s, v x ∂volume) := by
  -- Work with the normalized restricted measure where `setAverage` is just an integral.
  rw [setAverage_eq', setAverage_eq', setAverage_eq']
  have hu' : Integrable u ((volume s)⁻¹ • volume.restrict s) :=
    (integrable_inv_smul_measure hs0 hsfin).2 hu
  have hv' : Integrable v ((volume s)⁻¹ • volume.restrict s) :=
    (integrable_inv_smul_measure hs0 hsfin).2 hv
  rw [integral_add hu' hv']

/-- Helper for Exercise 13.1.7: adding a constant commutes with `setAverage`. -/
private lemma setAverage_const_add {d : ℕ} {s : Set (Fin d → ℝ)} {g : (Fin d → ℝ) → ℝ}
    (hs0 : volume s ≠ 0) (hsfin : volume s ≠ ⊤) (hg : IntegrableOn g s volume) (c : ℝ) :
    ⨍ x in s, (c + g x) ∂volume = c + ⨍ x in s, g x ∂volume := by
  -- Split the average into the constant part and the fluctuating part.
  calc
    ⨍ x in s, (c + g x) ∂volume
      = (⨍ x in s, (fun _ : Fin d → ℝ ↦ c) x ∂volume) + (⨍ x in s, g x ∂volume) := by
          exact setAverage_add hs0 hsfin (integrableOn_const hsfin) hg
    _ = c + ⨍ x in s, g x ∂volume := by
          rw [setAverage_const hs0 hsfin c]

/-- Helper for Exercise 13.1.7: the positive part `(f - c)^+` of a locally integrable function is
again locally integrable. -/
private lemma locallyIntegrable_posPart_sub_const {d : ℕ} {f : (Fin d → ℝ) → ℝ}
    (hf : LocallyIntegrable f volume) (c : ℝ) :
    LocallyIntegrable (fun x ↦ max (f x - c) 0) volume := by
  -- Compare the positive part pointwise with `|f - c|`.
  have hsub : LocallyIntegrable (fun x ↦ f x - c) volume :=
    hf.sub (MeasureTheory.locallyIntegrable_const c)
  refine hsub.mono ?_ ?_
  · exact
      AEMeasurable.aestronglyMeasurable
        ((hf.aestronglyMeasurable.aemeasurable.sub aemeasurable_const).max aemeasurable_const)
  · refine Filter.Eventually.of_forall fun x ↦ ?_
    have hnonneg : 0 ≤ max (f x - c) 0 := le_max_right _ _
    rw [Real.norm_eq_abs, abs_of_nonneg hnonneg, Real.norm_eq_abs]
    by_cases hxc : 0 ≤ f x - c
    · rw [max_eq_left hxc, abs_of_nonneg hxc]
    · rw [max_eq_right (le_of_not_ge hxc)]
      exact abs_nonneg _

/-- Helper for Exercise 13.1.7: the positive part `(c - f)^+` of a locally integrable function is
again locally integrable. -/
private lemma locallyIntegrable_posPart_const_sub {d : ℕ} {f : (Fin d → ℝ) → ℝ}
    (hf : LocallyIntegrable f volume) (c : ℝ) :
    LocallyIntegrable (fun x ↦ max (c - f x) 0) volume := by
  -- This is the same estimate applied to `c - f`.
  have hsub : LocallyIntegrable (fun x ↦ c - f x) volume :=
    (MeasureTheory.locallyIntegrable_const c).sub hf
  refine hsub.mono ?_ ?_
  · exact
      AEMeasurable.aestronglyMeasurable
        ((aemeasurable_const.sub hf.aestronglyMeasurable.aemeasurable).max aemeasurable_const)
  · refine Filter.Eventually.of_forall fun x ↦ ?_
    have hnonneg : 0 ≤ max (c - f x) 0 := le_max_right _ _
    rw [Real.norm_eq_abs, abs_of_nonneg hnonneg, Real.norm_eq_abs]
    by_cases hxc : 0 ≤ c - f x
    · rw [max_eq_left hxc, abs_of_nonneg hxc]
    · rw [max_eq_right (le_of_not_ge hxc)]
      exact abs_nonneg _

/-- Helper for Exercise 13.1.7: a nonnegative locally integrable density induces a locally finite
`withDensity` measure. -/
private lemma isLocallyFiniteMeasure_withDensity_ofReal_of_nonneg_locallyIntegrable
    {d : ℕ} {g : (Fin d → ℝ) → ℝ} (hg : LocallyIntegrable g volume) (hg_nonneg : ∀ x, 0 ≤ g x) :
    IsLocallyFiniteMeasure (volume.withDensity fun x ↦ ENNReal.ofReal (g x)) := by
  -- Use closed balls as finite neighborhoods and rewrite the density mass as a finite lintegral.
  refine ⟨fun x ↦ ?_⟩
  let s : Set (Fin d → ℝ) := Metric.closedBall x 1
  refine ⟨s, by simpa [s] using Metric.closedBall_mem_nhds x zero_lt_one, ?_⟩
  rw [withDensity_apply _ Metric.isClosed_closedBall.measurableSet]
  have hg_int : IntegrableOn g s volume := by
    simpa [s] using
      hg.integrableOn_isCompact (k := Metric.closedBall x 1) (isCompact_closedBall x (1 : ℝ))
  have hg_int' : Integrable g (volume.restrict s) := by
    simpa [IntegrableOn] using hg_int
  have h_nonneg : 0 ≤ᵐ[volume.restrict s] g := Filter.Eventually.of_forall hg_nonneg
  exact lt_top_iff_ne_top.2 <|
    (MeasureTheory.lintegral_ofReal_ne_top_iff_integrable hg_int'.aestronglyMeasurable h_nonneg).2
      hg_int'

/-- Helper for Exercise 13.1.7: the real mass of a nonnegative `withDensity` measure on `s`
coincides with the set integral of the density over `s`. -/
private lemma withDensityReal_apply_eq_setIntegral_of_nonneg {d : ℕ}
    {g : (Fin d → ℝ) → ℝ} {s : Set (Fin d → ℝ)}
    (hg : IntegrableOn g s volume) (hg_nonneg : ∀ x, 0 ≤ g x) :
    (volume.withDensity (fun x ↦ ENNReal.ofReal (g x))).real s = ∫ x in s, g x ∂volume := by
  have hg' : Integrable g (volume.restrict s) := by
    simpa [IntegrableOn] using hg
  have h_meas :
      AEMeasurable (fun x ↦ ENNReal.ofReal (g x)) (volume.restrict s) := by
    exact hg'.aestronglyMeasurable.aemeasurable.ennreal_ofReal
  have h_top :
      ∀ᵐ x ∂volume.restrict s, ENNReal.ofReal (g x) < ⊤ :=
    Filter.Eventually.of_forall fun _ ↦ ENNReal.ofReal_lt_top
  calc
    (volume.withDensity (fun x ↦ ENNReal.ofReal (g x))).real s
      = ∫ x in s, (1 : ℝ) ∂(volume.withDensity fun x ↦ ENNReal.ofReal (g x)) := by
          simpa using
            (setIntegral_const
              (μ := volume.withDensity fun x ↦ ENNReal.ofReal (g x))
              (s := s) (c := (1 : ℝ))).symm
    _ = ∫ x in s, ((ENNReal.ofReal (g x)).toReal : ℝ) ∂volume := by
          simpa using
            (setIntegral_withDensity_eq_setIntegral_toReal_smul₀'
              (μ := volume) (s := s) h_meas h_top (fun _ ↦ (1 : ℝ)))
    _ = ∫ x in s, g x ∂volume := by
          -- Proof comment: nonnegativity identifies `ENNReal.ofReal (g x)` with `g x`.
          refine integral_congr_ae ?_
          filter_upwards with x
          simp [hg_nonneg x]

/-- Helper for Exercise 13.1.7: the average of a nonnegative density over a translated dilate is
the normalized `withDensity` mass ratio from Exercise 13.1.6. -/
private lemma translatedDilate_setAverage_eq_massRatio {d : ℕ}
    {g : (Fin d → ℝ) → ℝ} {C : Set (Fin d → ℝ)}
    (hC_open : IsOpen C) (hC_bounded : Bornology.IsBounded C) (hC_zero : (0 : Fin d → ℝ) ∈ C)
    (x : Fin d → ℝ) {r : ℝ} (hr : 0 < r)
    (hg : IntegrableOn g (({x} : Set (Fin d → ℝ)) + r • C) volume)
    (hg_nonneg : ∀ y, 0 ≤ g y) :
    ⨍ y in ({x} : Set (Fin d → ℝ)) + r • C, g y ∂volume =
      (volume.real C)⁻¹ *
        ((volume.withDensity (fun y ↦ ENNReal.ofReal (g y))).real
            (({x} : Set (Fin d → ℝ)) + r • C) / r ^ d) := by
  let s : Set (Fin d → ℝ) := ({x} : Set (Fin d → ℝ)) + r • C
  have hC_pos : 0 < volume.real C :=
    volumeReal_pos_of_open_of_mem_zero hC_open hC_bounded hC_zero
  have hs_real :
      volume.real s = r ^ d * volume.real C := by
    simpa [s] using translatedSmul_volumeReal hC_open.measurableSet x hr
  calc
    ⨍ y in s, g y ∂volume = (volume.real s)⁻¹ * ∫ y in s, g y ∂volume := by
      rw [setAverage_eq]
      simp [s, smul_eq_mul]
    _ =
        (volume.real s)⁻¹ *
          (volume.withDensity (fun y ↦ ENNReal.ofReal (g y))).real s := by
            rw [withDensityReal_apply_eq_setIntegral_of_nonneg hg hg_nonneg]
    _ =
        (volume.real C)⁻¹ *
          ((volume.withDensity (fun y ↦ ENNReal.ofReal (g y))).real s / r ^ d) := by
            -- Proof comment: normalize the translated-dilate volume with the explicit scaling law.
            rw [hs_real]
            field_simp [pow_ne_zero d hr.ne', hC_pos.ne']
    _ =
        (volume.real C)⁻¹ *
          ((volume.withDensity (fun y ↦ ENNReal.ofReal (g y))).real
              (({x} : Set (Fin d → ℝ)) + r • C) / r ^ d) := by
            simp [s]

/-- Helper for Exercise 13.1.7: a nonnegative locally integrable density has vanishing averages on
its zero set along the translated dilates of `C`. -/
private lemma ae_tendsto_zero_average_over_convex_dilates_on_zeroSet {d : ℕ}
    {g : (Fin d → ℝ) → ℝ} (hg : LocallyIntegrable g volume) (hg_nonneg : ∀ x, 0 ≤ g x)
    {C : Set (Fin d → ℝ)} (hC_open : IsOpen C) (hC_convex : Convex ℝ C)
    (hC_bounded : Bornology.IsBounded C) (hC_zero : (0 : Fin d → ℝ) ∈ C) :
    ∀ᵐ x ∂(volume.restrict {x | g x = 0}),
      Tendsto
        (fun r : ℝ ↦ ⨍ y in ({x} : Set (Fin d → ℝ)) + r • C, g y ∂volume)
        (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  -- Route correction: first rewrite the `withDensity` mass ratio into a set average, then
  -- import the Exercise 13.1.6 limit through `Tendsto.congr'`.
  let νg : Measure (Fin d → ℝ) := volume.withDensity fun x ↦ ENNReal.ofReal (g x)
  letI : IsLocallyFiniteMeasure νg :=
    isLocallyFiniteMeasure_withDensity_ofReal_of_nonneg_locallyIntegrable hg hg_nonneg
  have h_null : νg {x | g x = 0} = 0 := by
    have h_zero_set :
        NullMeasurableSet {x | g x = 0} volume :=
      hg.aestronglyMeasurable.nullMeasurableSet_eq_fun aestronglyMeasurable_zero
    have h_zero_ae :
        ∀ᵐ x ∂volume.restrict {x | g x = 0}, ENNReal.ofReal (g x) = 0 := by
      refine (ae_restrict_iff'₀ h_zero_set).2 ?_
      filter_upwards with x hx
      simp [hx]
    have h_null_aux :
        (volume.withDensity fun x ↦ ENNReal.ofReal (g x)) {x | g x = 0} = 0 := by
      rw [withDensity_apply' _ {x | g x = 0}, lintegral_congr_ae h_zero_ae, lintegral_zero]
    simpa [νg] using h_null_aux
  have h_mass :
      ∀ᵐ x ∂(volume.restrict {x | g x = 0}),
        Tendsto
          (fun r : ℝ ↦ νg.real (({x} : Set (Fin d → ℝ)) + r • C) / r ^ d)
          (𝓝[>] (0 : ℝ)) (𝓝 0) :=
    ae_tendsto_zero_scaled_set_density_of_null
      (μ := νg) h_null hC_bounded hC_convex hC_open hC_zero
  have hC_pos : 0 < volume.real C :=
    volumeReal_pos_of_open_of_mem_zero hC_open hC_bounded hC_zero
  filter_upwards [h_mass] with x hx
  have h_scaled :
      Tendsto
        (fun r : ℝ ↦ (volume.real C)⁻¹ * (νg.real (({x} : Set (Fin d → ℝ)) + r • C) / r ^ d))
        (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    simpa [zero_mul] using
      ((tendsto_const_nhds : Tendsto (fun _ : ℝ ↦ (volume.real C)⁻¹) (𝓝[>] (0 : ℝ))
        (𝓝 ((volume.real C)⁻¹))).mul hx)
  have h_rewrite :
      (fun r : ℝ ↦ ⨍ y in ({x} : Set (Fin d → ℝ)) + r • C, g y ∂volume) =ᶠ[𝓝[>] (0 : ℝ)]
        (fun r : ℝ ↦ (volume.real C)⁻¹ * (νg.real (({x} : Set (Fin d → ℝ)) + r • C) / r ^ d)) :=
    by
      filter_upwards [self_mem_nhdsWithin] with r hr
      simpa [νg] using
        translatedDilate_setAverage_eq_massRatio hC_open hC_bounded hC_zero x hr
          (integrableOn_translatedDilate hg hC_bounded x r hr.le) hg_nonneg
  exact Tendsto.congr' h_rewrite.symm h_scaled

/-- Exercise 13.1.7: for a locally integrable function on `ℝ^d`, the averages over the dilates
`x + r C` of an open bounded convex set `C` containing `0` converge almost everywhere to the value
`f x` as `r ↓ 0`. -/
-- Proof sketch: this is the source-facing specialization of the owner theorem
-- `VitaliFamily.ae_tendsto_average` to the Vitali family generated by the translated dilates
-- `{x} + r • C`, as suggested by Exercise 13.1.6.
theorem ae_tendsto_average_over_convex_dilates {d : ℕ}
    {f : (Fin d → ℝ) → ℝ} (hf : LocallyIntegrable f volume)
    {C : Set (Fin d → ℝ)} (hC_open : IsOpen C) (hC_convex : Convex ℝ C)
    (hC_bounded : Bornology.IsBounded C) (hC_zero : (0 : Fin d → ℝ) ∈ C) :
    ∀ᵐ x ∂volume,
      Tendsto
        (fun r : ℝ ↦ ⨍ y in ({x} + r • C), f y ∂volume)
        (𝓝[>] (0 : ℝ)) (𝓝 (f x)) := by
  have hUpperRat :
      ∀ q : ℚ, ∀ᵐ x ∂volume,
        f x ≤ q →
          Tendsto
            (fun r : ℝ ↦
              ⨍ y in ({x} : Set (Fin d → ℝ)) + r • C, max (f y - q) 0 ∂volume)
            (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    intro q
    let gq : (Fin d → ℝ) → ℝ := fun y ↦ max (f y - q) 0
    have hgq : LocallyIntegrable gq volume :=
      locallyIntegrable_posPart_sub_const hf q
    have h_zero :
        ∀ᵐ x ∂(volume.restrict {x | gq x = 0}),
          Tendsto
            (fun r : ℝ ↦ ⨍ y in ({x} : Set (Fin d → ℝ)) + r • C, gq y ∂volume)
            (𝓝[>] (0 : ℝ)) (𝓝 0) :=
      ae_tendsto_zero_average_over_convex_dilates_on_zeroSet hgq
        (fun _ ↦ le_max_right _ _) hC_open hC_convex hC_bounded hC_zero
    have h_set : {x | gq x = 0} = {x | f x ≤ q} := by
      ext x
      by_cases hfx : f x ≤ q
      · have hnonpos : f x - q ≤ 0 := sub_nonpos.mpr hfx
        simp [gq, hfx, max_eq_right hnonpos]
      · have hqf : q < f x := lt_of_not_ge hfx
        have hpos : 0 < f x - q := sub_pos.mpr hqf
        simp [gq, hfx, max_eq_left (le_of_lt hpos), ne_of_gt hpos]
    have h_null :
        NullMeasurableSet {x | f x ≤ q} volume :=
      hf.aestronglyMeasurable.nullMeasurableSet_le aestronglyMeasurable_const
    have h_zero' :
        ∀ᵐ x ∂(volume.restrict {x | f x ≤ q}),
          Tendsto
            (fun r : ℝ ↦
              ⨍ y in ({x} : Set (Fin d → ℝ)) + r • C, max (f y - q) 0 ∂volume)
            (𝓝[>] (0 : ℝ)) (𝓝 0) := by
      simpa [gq, h_set] using h_zero
    exact (ae_restrict_iff'₀ h_null).1 h_zero'
  have hLowerRat :
      ∀ q : ℚ, ∀ᵐ x ∂volume,
        q ≤ f x →
          Tendsto
            (fun r : ℝ ↦
              ⨍ y in ({x} : Set (Fin d → ℝ)) + r • C, max (q - f y) 0 ∂volume)
            (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    intro q
    let gq : (Fin d → ℝ) → ℝ := fun y ↦ max (q - f y) 0
    have hgq : LocallyIntegrable gq volume :=
      locallyIntegrable_posPart_const_sub hf q
    have h_zero :
        ∀ᵐ x ∂(volume.restrict {x | gq x = 0}),
          Tendsto
            (fun r : ℝ ↦ ⨍ y in ({x} : Set (Fin d → ℝ)) + r • C, gq y ∂volume)
            (𝓝[>] (0 : ℝ)) (𝓝 0) :=
      ae_tendsto_zero_average_over_convex_dilates_on_zeroSet hgq
        (fun _ ↦ le_max_right _ _) hC_open hC_convex hC_bounded hC_zero
    have h_set : {x | gq x = 0} = {x | q ≤ f x} := by
      ext x
      by_cases hqf : q ≤ f x
      · have hnonpos : q - f x ≤ 0 := sub_nonpos.mpr hqf
        simp [gq, hqf, max_eq_right hnonpos]
      · have hfxq : f x < q := lt_of_not_ge hqf
        have hpos : 0 < q - f x := sub_pos.mpr hfxq
        simp [gq, hqf, max_eq_left (le_of_lt hpos), ne_of_gt hpos]
    have h_null :
        NullMeasurableSet {x | q ≤ f x} volume :=
      aestronglyMeasurable_const.nullMeasurableSet_le hf.aestronglyMeasurable
    have h_zero' :
        ∀ᵐ x ∂(volume.restrict {x | q ≤ f x}),
          Tendsto
            (fun r : ℝ ↦
              ⨍ y in ({x} : Set (Fin d → ℝ)) + r • C, max (q - f y) 0 ∂volume)
            (𝓝[>] (0 : ℝ)) (𝓝 0) := by
      simpa [gq, h_set] using h_zero
    exact (ae_restrict_iff'₀ h_null).1 h_zero'
  have hUpperAll :
      ∀ᵐ x ∂volume,
        ∀ q : ℚ,
          f x ≤ q →
            Tendsto
              (fun r : ℝ ↦
                ⨍ y in ({x} : Set (Fin d → ℝ)) + r • C, max (f y - q) 0 ∂volume)
              (𝓝[>] (0 : ℝ)) (𝓝 0) :=
    ae_all_iff.2 hUpperRat
  have hLowerAll :
      ∀ᵐ x ∂volume,
        ∀ q : ℚ,
          q ≤ f x →
            Tendsto
              (fun r : ℝ ↦
                ⨍ y in ({x} : Set (Fin d → ℝ)) + r • C, max (q - f y) 0 ∂volume)
              (𝓝[>] (0 : ℝ)) (𝓝 0) :=
    ae_all_iff.2 hLowerRat
  filter_upwards [hUpperAll, hLowerAll] with x hxUpper hxLower
  -- Proof comment: squeeze the average of `f` between rational barriers from above and below.
  refine tendsto_order.2 ⟨?_, ?_⟩
  · intro a ha
    obtain ⟨q, haq, hqf⟩ := exists_rat_btwn ha
    have hq_tendsto :=
      hxLower q (show (q : ℝ) ≤ f x by exact le_of_lt hqf)
    have hq_eventually :
        ∀ᶠ r : ℝ in 𝓝[>] (0 : ℝ),
          ⨍ y in ({x} : Set (Fin d → ℝ)) + r • C, max ((q : ℝ) - f y) 0 ∂volume < q - a :=
      (tendsto_order.1 hq_tendsto).2 (q - a) (sub_pos.mpr haq)
    filter_upwards [self_mem_nhdsWithin, hq_eventually] with r hr hsmall
    let s : Set (Fin d → ℝ) := ({x} : Set (Fin d → ℝ)) + r • C
    have hs_real :
        volume.real s = r ^ d * volume.real C := by
      simpa [s] using translatedSmul_volumeReal hC_open.measurableSet x hr
    have hs0 : volume s ≠ 0 := by
      refine fun hs0 => ?_
      have hzero : volume.real s = 0 := by simpa [measureReal_def, hs0] using rfl
      have hC_pos : 0 < volume.real C :=
        volumeReal_pos_of_open_of_mem_zero hC_open hC_bounded hC_zero
      rw [hs_real] at hzero
      exact (mul_ne_zero (pow_ne_zero d hr.ne') hC_pos.ne' hzero)
    have hs_bounded_set :
        Bornology.IsBounded s := by
      obtain ⟨R, _hR_pos, hRC⟩ :=
        hC_bounded.subset_closedBall_lt (0 : ℝ) (0 : Fin d → ℝ)
      have hs_subset : s ⊆ Metric.closedBall x (r * R) :=
        by simpa [s] using translatedSmul_subset_closedBall (C := C) hRC hr.le x
      exact Bornology.IsBounded.subset Metric.isBounded_closedBall hs_subset
    have hsfin : volume s ≠ ⊤ := hs_bounded_set.measure_lt_top.ne
    have hf_int : IntegrableOn f s volume := by
      simpa [s] using integrableOn_translatedDilate hf hC_bounded x r hr.le
    have hminus_int : IntegrableOn (fun y ↦ max ((q : ℝ) - f y) 0) s volume := by
      simpa [s] using
        integrableOn_translatedDilate
          (locallyIntegrable_posPart_const_sub hf q) hC_bounded x r hr.le
    have hbound :
        (q : ℝ) ≤
          ⨍ y in s, f y ∂volume +
            ⨍ y in s, max ((q : ℝ) - f y) 0 ∂volume := by
      have hmono :
          ⨍ y in s, (q : ℝ) ∂volume ≤
            ⨍ y in s, f y + max ((q : ℝ) - f y) 0 ∂volume :=
        setAverage_mono hs0 hsfin (integrableOn_const hsfin) (hf_int.add hminus_int) <| by
          intro y
          by_cases hy : (q : ℝ) ≤ f y
          · have hnonpos : (q : ℝ) - f y ≤ 0 := sub_nonpos.mpr hy
            rw [max_eq_right hnonpos]
            linarith
          · have hy' : f y < (q : ℝ) := lt_of_not_ge hy
            have hpos : 0 < (q : ℝ) - f y := sub_pos.mpr hy'
            rw [max_eq_left (le_of_lt hpos)]
            linarith
      rw [setAverage_const hs0 hsfin (q : ℝ), setAverage_add hs0 hsfin hf_int hminus_int] at hmono
      exact hmono
    have : a < ⨍ y in s, f y ∂volume := by
      linarith
    simpa [s] using this
  · intro b hb
    obtain ⟨q, hfxq, hqb⟩ := exists_rat_btwn hb
    have hq_tendsto :=
      hxUpper q (show f x ≤ (q : ℝ) by exact le_of_lt hfxq)
    have hq_eventually :
        ∀ᶠ r : ℝ in 𝓝[>] (0 : ℝ),
          ⨍ y in ({x} : Set (Fin d → ℝ)) + r • C, max (f y - q) 0 ∂volume < b - q :=
      (tendsto_order.1 hq_tendsto).2 (b - q) (sub_pos.mpr hqb)
    filter_upwards [self_mem_nhdsWithin, hq_eventually] with r hr hsmall
    let s : Set (Fin d → ℝ) := ({x} : Set (Fin d → ℝ)) + r • C
    have hs_real :
        volume.real s = r ^ d * volume.real C := by
      simpa [s] using translatedSmul_volumeReal hC_open.measurableSet x hr
    have hs0 : volume s ≠ 0 := by
      refine fun hs0 => ?_
      have hzero : volume.real s = 0 := by simpa [measureReal_def, hs0] using rfl
      have hC_pos : 0 < volume.real C :=
        volumeReal_pos_of_open_of_mem_zero hC_open hC_bounded hC_zero
      rw [hs_real] at hzero
      exact (mul_ne_zero (pow_ne_zero d hr.ne') hC_pos.ne' hzero)
    have hs_bounded_set :
        Bornology.IsBounded s := by
      obtain ⟨R, _hR_pos, hRC⟩ :=
        hC_bounded.subset_closedBall_lt (0 : ℝ) (0 : Fin d → ℝ)
      have hs_subset : s ⊆ Metric.closedBall x (r * R) :=
        by simpa [s] using translatedSmul_subset_closedBall (C := C) hRC hr.le x
      exact Bornology.IsBounded.subset Metric.isBounded_closedBall hs_subset
    have hsfin : volume s ≠ ⊤ := hs_bounded_set.measure_lt_top.ne
    have hf_int : IntegrableOn f s volume := by
      simpa [s] using integrableOn_translatedDilate hf hC_bounded x r hr.le
    have hplus_int : IntegrableOn (fun y ↦ max (f y - q) 0) s volume := by
      simpa [s] using
        integrableOn_translatedDilate
          (locallyIntegrable_posPart_sub_const hf q) hC_bounded x r hr.le
    have hbound :
        ⨍ y in s, f y ∂volume ≤ (q : ℝ) + ⨍ y in s, max (f y - q) 0 ∂volume := by
      have hmono :
          ⨍ y in s, f y ∂volume ≤
            ⨍ y in s, (q : ℝ) + max (f y - q) 0 ∂volume :=
        setAverage_mono hs0 hsfin hf_int
          ((integrableOn_const hsfin).add hplus_int) <| by
            intro y
            by_cases hy : f y ≤ (q : ℝ)
            · have hnonpos : f y - q ≤ 0 := sub_nonpos.mpr hy
              rw [max_eq_right hnonpos]
              linarith
            · have hy' : (q : ℝ) < f y := lt_of_not_ge hy
              have hpos : 0 < f y - q := sub_pos.mpr hy'
              rw [max_eq_left (le_of_lt hpos)]
              linarith
      rw [setAverage_const_add hs0 hsfin hplus_int (q : ℝ)] at hmono
      exact hmono
    have : ⨍ y in s, f y ∂volume < b := by
      linarith
    simpa [s] using this

/-- The one-dimensional primitive `x ↦ ∫ t in 0..x, f t` has derivative `f x` almost everywhere
for locally integrable `f`. -/
-- Proof sketch: apply `LocallyIntegrable.ae_hasDerivAt_integral` to `hf` with
-- base point `c = 0`, then pass from `HasDerivAt` to `deriv`.
theorem ae_deriv_intervalIntegral_from_zero_eq {f : ℝ → ℝ} (hf : LocallyIntegrable f volume) :
    ∀ᵐ x ∂volume, deriv (fun x ↦ ∫ t in (0 : ℝ)..x, f t) x = f x := by
  filter_upwards [LocallyIntegrable.ae_hasDerivAt_integral hf] with x hx
  simpa using (hx 0).deriv
