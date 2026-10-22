/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory ProbabilityTheory
open scoped ENNReal Topology

universe u

variable {Ω : Type u} [MeasurableSpace Ω]

noncomputable section

/-- Helper for Exercise 15.1.5: the Mellin transform of a measure on `[0, ∞)`. -/
abbrev mellinTransform (μ : Measure NNReal) (s : ℝ) : ℝ≥0∞ :=
  ∫⁻ x, (x : ℝ≥0∞) ^ s ∂μ

/-- Helper for Exercise 15.1.5: the Mellin transform of the law of a nonnegative random variable
can be rewritten as a lower integral on the base probability space. -/
theorem mellinTransform_map (μ : Measure Ω) (X : Ω → NNReal) (hX : AEMeasurable X μ) (s : ℝ) :
    mellinTransform (μ.map X) s =
      ∫⁻ ω, (X ω : ℝ≥0∞) ^ s ∂μ := by
  -- Rewrite the pushforward lower integral using `lintegral_map'`.
  have hpow : AEMeasurable (fun x : NNReal ↦ (x : ℝ≥0∞) ^ s) (μ.map X) := by
    fun_prop
  simpa [mellinTransform] using lintegral_map' hpow hX

section

variable {μ ν : Measure NNReal} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] {ε ε₀ : ℝ}

/-- Helper for Exercise 15.1.5: the positive Mellin kernel at a smaller exponent is bounded by
`1 + x ^ ε₀`. -/
lemma ennreal_rpow_le_one_add_rpow (x : NNReal) {s ε₀ : ℝ} (hs : 0 ≤ s) (hs_le : s ≤ ε₀) :
    ((x : ℝ≥0∞) ^ s) ≤ 1 + ((x : ℝ≥0∞) ^ ε₀) := by
  -- Split into the regimes `x ≤ 1` and `1 ≤ x`, where exponent monotonicity changes direction.
  by_cases hx : (x : ℝ≥0∞) ≤ 1
  · calc
      (x : ℝ≥0∞) ^ s ≤ (x : ℝ≥0∞) ^ (0 : ℝ) :=
        ENNReal.rpow_le_rpow_of_exponent_ge hx hs
      _ = 1 := by simp
      _ ≤ 1 + (x : ℝ≥0∞) ^ ε₀ := by simp
  · have hx' : (1 : ℝ≥0∞) ≤ (x : ℝ≥0∞) := le_of_not_ge hx
    calc
      (x : ℝ≥0∞) ^ s ≤ (x : ℝ≥0∞) ^ ε₀ :=
        ENNReal.rpow_le_rpow_of_exponent_le hx' hs_le
      _ ≤ 1 + (x : ℝ≥0∞) ^ ε₀ := by simp

/-- Helper for Exercise 15.1.5: a finite positive Mellin moment controls all smaller nonnegative
exponents. -/
lemma mellinTransform_lt_top_of_le_exponent (μ : Measure NNReal) [IsProbabilityMeasure μ]
    {s ε₀ : ℝ} (hs : 0 ≤ s) (hs_le : s ≤ ε₀) (hμ_moment : mellinTransform μ ε₀ < ∞) :
    mellinTransform μ s < ∞ := by
  -- Compare the smaller kernel against an integrable envelope.
  calc
    mellinTransform μ s = ∫⁻ x, (x : ℝ≥0∞) ^ s ∂μ := rfl
    _ ≤ ∫⁻ x, (1 + (x : ℝ≥0∞) ^ ε₀) ∂μ := by
      refine lintegral_mono fun x ↦ ?_
      exact ennreal_rpow_le_one_add_rpow x hs hs_le
    _ < ∞ := by
      rw [lintegral_add_right]
      · have hone : (∫⁻ x, (1 : ℝ≥0∞) ∂μ) < ∞ := by
          simp
        simpa [mellinTransform] using ENNReal.add_lt_top.2 ⟨hone, hμ_moment⟩
      · fun_prop

/-- Helper for Exercise 15.1.5: pushing the positive-part log-pushforward forward by `exp`
recovers the original restriction to `(0, ∞)`. -/
lemma map_exp_positiveLogRestrict (μ : Measure NNReal) :
    (((μ.restrict (Set.Ioi 0)).map (fun x : NNReal ↦ Real.log x)).map
      (fun y : ℝ ↦ (⟨Real.exp y, by positivity⟩ : NNReal))) = μ.restrict (Set.Ioi 0) := by
  -- Collapse the two pushforwards and then use `exp (log x) = x` on the restricted support.
  rw [Measure.map_map]
  · have hcomp :
        ((fun y : ℝ ↦ (⟨Real.exp y, by positivity⟩ : NNReal)) ∘ fun x : NNReal ↦ Real.log x)
          =ᵐ[μ.restrict (Set.Ioi 0)] id := by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
      have hxR : 0 < (x : ℝ) := by
        exact_mod_cast hx
      exact Subtype.ext (by simpa [Function.comp_apply] using Real.exp_log hxR)
    exact (Measure.map_congr hcomp).trans
      (Measure.map_id : Measure.map id (μ.restrict (Set.Ioi 0)) = _)
  · fun_prop
  · fun_prop

/-- Helper for Exercise 15.1.5: for probability measures on `NNReal`, equality on `(0, ∞)`
already determines the atom at `0`, hence the whole measure. -/
lemma measure_eq_of_restrictIoi_eq_of_isProbability
    (h : μ.restrict (Set.Ioi 0) = ν.restrict (Set.Ioi 0)) :
    μ = ν := by
  -- Compare the positive masses first, then recover the remaining mass at `0` from total mass `1`.
  have hIoi : μ (Set.Ioi (0 : NNReal)) = ν (Set.Ioi (0 : NNReal)) := by
    have h' := congrArg (fun ρ : Measure NNReal ↦ ρ Set.univ) h
    simpa [Measure.restrict_apply, measurableSet_Ioi] using h'
  have h_union_univ : Set.Ioi (0 : NNReal) ∪ ({0} : Set NNReal) = Set.univ := by
    ext x
    by_cases hx : x = 0
    · simp [hx]
    · simp
  have hμsplit : μ (Set.Ioi (0 : NNReal)) + μ ({0} : Set NNReal) = 1 := by
    calc
      μ (Set.Ioi (0 : NNReal)) + μ ({0} : Set NNReal)
          = μ (Set.Ioi (0 : NNReal) ∪ ({0} : Set NNReal)) := by
              symm
              refine measure_union ?_ (measurableSet_singleton (0 : NNReal))
              refine Set.disjoint_left.2 ?_
              intro a ha hzero
              exact (ne_of_gt ha) hzero
      _ = μ Set.univ := by
        rw [h_union_univ]
      _ = 1 := by
        simp
  have hνsplit : ν (Set.Ioi (0 : NNReal)) + ν ({0} : Set NNReal) = 1 := by
    calc
      ν (Set.Ioi (0 : NNReal)) + ν ({0} : Set NNReal)
          = ν (Set.Ioi (0 : NNReal) ∪ ({0} : Set NNReal)) := by
              symm
              refine measure_union ?_ (measurableSet_singleton (0 : NNReal))
              refine Set.disjoint_left.2 ?_
              intro a ha hzero
              exact (ne_of_gt ha) hzero
      _ = ν Set.univ := by
        rw [h_union_univ]
      _ = 1 := by
        simp
  have hμsplitR := congrArg ENNReal.toReal hμsplit
  have hνsplitR := congrArg ENNReal.toReal hνsplit
  rw [ENNReal.toReal_add (measure_lt_top _ _).ne (measure_lt_top _ _).ne,
    ENNReal.toReal_one] at hμsplitR hνsplitR
  have hIoiR := congrArg ENNReal.toReal hIoi
  have hzero_toReal : (μ ({0} : Set NNReal)).toReal = (ν ({0} : Set NNReal)).toReal := by
    linarith
  have hzero : μ ({0} : Set NNReal) = ν ({0} : Set NNReal) := by
    exact
      (ENNReal.toReal_eq_toReal_iff' (measure_lt_top _ _).ne (measure_lt_top _ _).ne).mp
        hzero_toReal
  ext s hs
  let spos : Set NNReal := s ∩ Set.Ioi (0 : NNReal)
  let szero : Set NNReal := s ∩ ({0} : Set NNReal)
  have hspos : MeasurableSet spos := hs.inter measurableSet_Ioi
  have hszero : MeasurableSet szero := hs.inter (measurableSet_singleton (0 : NNReal))
  have hdecomp : s = spos ∪ szero := by
    ext x
    by_cases hx : x = 0
    · simp [spos, szero, hx]
    · simp [spos, szero, hx, pos_iff_ne_zero]
  have hdisj : Disjoint spos szero := by
    refine Set.disjoint_left.2 ?_
    intro a ha hzeroa
    exact (ne_of_gt ha.2) hzeroa.2
  have hpos : μ spos = ν spos := by
    have h' := congrArg (fun ρ : Measure NNReal ↦ ρ s) h
    simpa [spos, Measure.restrict_apply, hspos] using h'
  have hzero_set : μ szero = ν szero := by
    by_cases h0 : (0 : NNReal) ∈ s
    · have hszero_eq : szero = ({0} : Set NNReal) := by
        ext x
        by_cases hx : x = 0
        · simp [szero, h0, hx]
        · simp [szero, hx]
      simp [hszero_eq, hzero]
    · have hszero_eq : szero = (∅ : Set NNReal) := by
        ext x
        by_cases hx : x = 0
        · simp [szero, h0, hx]
        · simp [szero, hx]
      simp [hszero_eq]
  -- Assemble the two pieces of the partition `s = (s ∩ Ioi 0) ∪ (s ∩ {0})`.
  calc
    μ s = μ spos + μ szero := by
      rw [hdecomp, measure_union hdisj hszero]
    _ = ν spos + ν szero := by
      rw [hpos, hzero_set]
    _ = ν s := by
      rw [hdecomp, measure_union hdisj hszero]

/-- Helper for Exercise 15.1.5: a positive finite Mellin moment identifies the exponential
moments of the positive-part log-pushforward. -/
lemma mgf_logRestrict_eq_mellinTransform (μ : Measure NNReal) {s : ℝ}
    (hs : 0 < s) (hμ_moment : mellinTransform μ s < ∞) :
    Integrable (fun y : ℝ ↦ Real.exp (s * y))
        ((μ.restrict (Set.Ioi 0)).map fun x : NNReal ↦ Real.log x) ∧
      ProbabilityTheory.mgf id
          ((μ.restrict (Set.Ioi 0)).map fun x : NNReal ↦ Real.log x) s =
        (mellinTransform μ s).toReal := by
  let ρ : Measure ℝ := (μ.restrict (Set.Ioi 0)).map fun x : NNReal ↦ Real.log x
  let f : ℝ → ℝ≥0∞ := fun y ↦ ENNReal.ofReal (Real.exp (s * y))
  have hf_meas : AEMeasurable f ρ := by
    dsimp [f, ρ]
    fun_prop
  have hlog_ae : AEMeasurable (fun x : NNReal ↦ Real.log x) (μ.restrict (Set.Ioi 0)) := by
    exact (Real.measurable_log.comp measurable_coe_nnreal_real).aemeasurable
  have hlintegral : ∫⁻ y, f y ∂ρ = mellinTransform μ s := by
    -- Rewrite the log-pushforward integral back on `(0, ∞)` and simplify `exp (s * log x)`.
    rw [show ρ = (μ.restrict (Set.Ioi 0)).map (fun x : NNReal ↦ Real.log x) by rfl]
    rw [lintegral_map' hf_meas hlog_ae]
    change ∫⁻ x in Set.Ioi (0 : NNReal), ENNReal.ofReal (Real.exp (s * Real.log x)) ∂μ =
      mellinTransform μ s
    have hkernel :
        (fun x : NNReal ↦ ENNReal.ofReal (Real.exp (s * Real.log x))) =ᵐ[μ.restrict (Set.Ioi 0)]
          fun x ↦ (x : ℝ≥0∞) ^ s := by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
      have hxR : 0 < (x : ℝ) := by
        exact_mod_cast hx
      have hlogexp : Real.exp (s * Real.log x) = (x : ℝ) ^ s := by
        rw [mul_comm, Real.rpow_def_of_pos hxR]
      rw [hlogexp]
      simpa using
        (ENNReal.ofReal_rpow_of_nonneg (show 0 ≤ (x : ℝ) by exact_mod_cast x.2) hs.le).symm
    rw [lintegral_congr_ae hkernel]
    have hsupport :
        Function.support (fun x : NNReal ↦ (x : ℝ≥0∞) ^ s) ⊆ Set.Ioi (0 : NNReal) := by
      intro x hx
      by_cases hx0 : x = 0
      · exfalso
        apply hx
        simp [hx0, hs]
      · simpa [pos_iff_ne_zero] using hx0
    simpa [mellinTransform] using
      (setLIntegral_eq_of_support_subset (μ := μ)
        (s := Set.Ioi (0 : NNReal)) (f := fun x : NNReal ↦ (x : ℝ≥0∞) ^ s) hsupport)
  have h_integrable_toReal :
      Integrable (fun y ↦ (f y).toReal) ρ := by
    exact integrable_toReal_of_lintegral_ne_top hf_meas (by
      rw [hlintegral]
      exact ne_of_lt hμ_moment)
  have h_integrable :
      Integrable (fun y : ℝ ↦ Real.exp (s * y)) ρ := by
    -- The `ENNReal.ofReal` kernel has the same real-valued `toReal`.
    convert h_integrable_toReal using 1
    ext y
    simp [f, Real.exp_nonneg]
  refine ⟨h_integrable, ?_⟩
  -- Evaluate the mgf by converting the nonnegative integral back to its `lintegral`.
  rw [ProbabilityTheory.mgf, integral_eq_lintegral_of_nonneg_ae]
  · change (∫⁻ y, f y ∂ρ).toReal = (mellinTransform μ s).toReal
    exact congrArg ENNReal.toReal hlintegral
  · exact Filter.Eventually.of_forall fun y ↦ (Real.exp_pos _).le
  · exact h_integrable.aestronglyMeasurable

/-- Helper for Exercise 15.1.5: Mellin equality on a positive real interval extends to equality of
the complex mgf on the corresponding vertical strip of the positive-part log-pushforwards. -/
lemma complexMGF_logRestrict_eqOn_strip_of_mellinTransform_eq
    (μ ν : Measure NNReal) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] {η : ℝ} (hη : 0 < η)
    (hμ_eta : mellinTransform μ η < ∞) (hν_eta : mellinTransform ν η < ∞)
    (h_eq : ∀ s ∈ Set.Ioo (0 : ℝ) η, mellinTransform μ s = mellinTransform ν s) :
    Set.EqOn
      (ProbabilityTheory.complexMGF id
        ((μ.restrict (Set.Ioi 0)).map fun x : NNReal ↦ Real.log x))
      (ProbabilityTheory.complexMGF id
        ((ν.restrict (Set.Ioi 0)).map fun x : NNReal ↦ Real.log x))
      {z : ℂ | z.re ∈ Set.Ioo 0 η} := by
  let ρ : Measure ℝ := (μ.restrict (Set.Ioi 0)).map fun x : NNReal ↦ Real.log x
  let σ : Measure ℝ := (ν.restrict (Set.Ioi 0)).map fun x : NNReal ↦ Real.log x
  let t : ℝ := η / 2
  have ht : t ∈ Set.Ioo (0 : ℝ) η := by
    dsimp [t]
    constructor <;> linarith
  have hρ0 : 0 ∈ ProbabilityTheory.integrableExpSet id ρ := by
    -- At exponent `0`, the kernel is the integrable constant `1`.
    simpa [ProbabilityTheory.integrableExpSet] using
      (integrable_const (1 : ℝ) : Integrable (fun _ : ℝ ↦ (1 : ℝ)) ρ)
  have hσ0 : 0 ∈ ProbabilityTheory.integrableExpSet id σ := by
    simpa [ProbabilityTheory.integrableExpSet] using
      (integrable_const (1 : ℝ) : Integrable (fun _ : ℝ ↦ (1 : ℝ)) σ)
  have hρ_eta : η ∈ ProbabilityTheory.integrableExpSet id ρ := by
    simpa [ρ, ProbabilityTheory.integrableExpSet] using
      (mgf_logRestrict_eq_mellinTransform μ hη hμ_eta).1
  have hσ_eta : η ∈ ProbabilityTheory.integrableExpSet id σ := by
    simpa [σ, ProbabilityTheory.integrableExpSet] using
      (mgf_logRestrict_eq_mellinTransform ν hη hν_eta).1
  have hρ_strip :
      Set.Ioo (0 : ℝ) η ⊆ interior (ProbabilityTheory.integrableExpSet id ρ) := by
    rw [isOpen_Ioo.subset_interior_iff]
    exact ProbabilityTheory.convex_integrableExpSet.Ioo_subset_of_mem_closure
      (subset_closure hρ0) (subset_closure hρ_eta)
  have hσ_strip :
      Set.Ioo (0 : ℝ) η ⊆ interior (ProbabilityTheory.integrableExpSet id σ) := by
    rw [isOpen_Ioo.subset_interior_iff]
    exact ProbabilityTheory.convex_integrableExpSet.Ioo_subset_of_mem_closure
      (subset_closure hσ0) (subset_closure hσ_eta)
  have hmgf_eq :
      ∀ s ∈ Set.Ioo (0 : ℝ) η, ProbabilityTheory.mgf id ρ s = ProbabilityTheory.mgf id σ s := by
    intro s hsIoo
    rw [(mgf_logRestrict_eq_mellinTransform μ hsIoo.1
        (mellinTransform_lt_top_of_le_exponent μ hsIoo.1.le hsIoo.2.le hμ_eta)).2]
    rw [(mgf_logRestrict_eq_mellinTransform ν hsIoo.1
        (mellinTransform_lt_top_of_le_exponent ν hsIoo.1.le hsIoo.2.le hν_eta)).2]
    rw [h_eq s hsIoo]
  have hρ_analytic :
      AnalyticOnNhd ℂ (ProbabilityTheory.complexMGF id ρ) {z : ℂ | z.re ∈ Set.Ioo 0 η} := by
    intro z hz
    exact ProbabilityTheory.analyticOnNhd_complexMGF z (hρ_strip hz)
  have hσ_analytic :
      AnalyticOnNhd ℂ (ProbabilityTheory.complexMGF id σ) {z : ℂ | z.re ∈ Set.Ioo 0 η} := by
    intro z hz
    exact ProbabilityTheory.analyticOnNhd_complexMGF z (hσ_strip hz)
  have h_real :
      ∃ᶠ x : ℝ in 𝓝[≠] t,
        ProbabilityTheory.complexMGF id ρ x = ProbabilityTheory.complexMGF id σ x := by
    -- Equality on the whole real interval gives the punctured-neighborhood input for the identity
    -- theorem at the midpoint `t`.
    have hIoo : ∀ᶠ x : ℝ in 𝓝[≠] t, x ∈ Set.Ioo (0 : ℝ) η :=
      mem_nhdsWithin_of_mem_nhds <| isOpen_Ioo.mem_nhds ht
    have hEq :
        ∀ᶠ x : ℝ in 𝓝[≠] t,
          ProbabilityTheory.complexMGF id ρ x = ProbabilityTheory.complexMGF id σ x := by
      filter_upwards [hIoo] with x hx
      rw [ProbabilityTheory.complexMGF_ofReal, ProbabilityTheory.complexMGF_ofReal, hmgf_eq x hx]
    exact Filter.Eventually.frequently hEq
  refine AnalyticOnNhd.eqOn_of_preconnected_of_frequently_eq hρ_analytic hσ_analytic
    ((convex_Ioo (0 : ℝ) η).linear_preimage Complex.reLm).isPreconnected (z₀ := (t : ℂ)) ?_ ?_
  · simpa [t] using ht
  · rw [Filter.frequently_iff_seq_forall] at h_real ⊢
    obtain ⟨xs, hx_tendsto, hx_eq⟩ := h_real
    refine ⟨fun n ↦ (xs n : ℂ), ?_, fun n ↦ ?_⟩
    · rw [tendsto_nhdsWithin_iff] at hx_tendsto ⊢
      constructor
      · exact (Complex.continuous_ofReal.tendsto _).comp hx_tendsto.1
      · simpa using hx_tendsto.2
    · simpa using hx_eq n

/-- Helper for Exercise 15.1.5: weighting a real measure by `exp (r * ·)` turns its characteristic
function into the strip value `complexMGF id _ (r + t * I)`. -/
lemma charFun_expWeightedLogMeasure_eq_complexMGF (ρ : Measure ℝ) {r t : ℝ} :
    charFun
        (ρ.withDensity fun y ↦ ENNReal.ofReal (Real.exp (r * y))) t =
      ProbabilityTheory.complexMGF id ρ (r + t * Complex.I) := by
  let f : ℝ → ℝ≥0∞ := fun y ↦ ENNReal.ofReal (Real.exp (r * y))
  have hf : Measurable f := by
    dsimp [f]
    fun_prop
  have hf_lt_top : ∀ᵐ y ∂ρ, f y < ∞ := by
    filter_upwards with y
    simp [f]
  -- Rewrite the weighted characteristic function as a plain integral on `ρ`.
  rw [← ProbabilityTheory.complexMGF_id_mul_I
    (μ := ρ.withDensity fun y ↦ ENNReal.ofReal (Real.exp (r * y))) t]
  rw [ProbabilityTheory.complexMGF, ProbabilityTheory.complexMGF]
  rw [integral_withDensity_eq_integral_toReal_smul hf hf_lt_top]
  -- The density contributes the real factor `exp (r * y)`, which combines into the complex
  -- exponential at `r + t * I`.
  refine integral_congr_ae <| Filter.Eventually.of_forall fun y ↦ ?_
  have hmul :
      ((r : ℂ) * y) + (((t : ℂ) * Complex.I) * y) = (r + t * Complex.I) * y := by
    ring
  change (f y).toReal • Complex.exp ((t : ℂ) * Complex.I * y) =
    Complex.exp (((r : ℂ) + (t : ℂ) * Complex.I) * y)
  have hreal : (ENNReal.ofReal (Real.exp (r * y))).toReal = Real.exp (r * y) := by
    simp [Real.exp_nonneg]
  rw [hreal]
  change ((Real.exp (r * y) : ℂ) * Complex.exp ((t : ℂ) * Complex.I * y)) =
    Complex.exp (((r : ℂ) + (t : ℂ) * Complex.I) * y)
  rw [show ((Real.exp (r * y) : ℝ) : ℂ) = Complex.exp ((r : ℂ) * y) by
    simp [Complex.ofReal_exp]]
  rw [← Complex.exp_add, hmul]

/-- Helper for Exercise 15.1.5: equality of the exponentially weighted `withDensity` measures
forces equality of the original measures. -/
lemma measure_eq_of_expWeighted_eq (ρ σ : Measure ℝ) (r : ℝ)
    (h :
      ρ.withDensity (fun y ↦ ENNReal.ofReal (Real.exp (r * y))) =
        σ.withDensity (fun y ↦ ENNReal.ofReal (Real.exp (r * y)))) :
    ρ = σ := by
  let f : ℝ → ℝ≥0∞ := fun y ↦ ENNReal.ofReal (Real.exp (r * y))
  have hf : Measurable f := by
    dsimp [f]
    fun_prop
  have hf_ne_zero_ρ : ∀ᵐ y ∂ρ, f y ≠ 0 := by
    filter_upwards with y
    simp [f, Real.exp_pos]
  have hf_ne_top_ρ : ∀ᵐ y ∂ρ, f y ≠ ∞ := by
    filter_upwards with y
    simp [f]
  have hf_ne_zero_σ : ∀ᵐ y ∂σ, f y ≠ 0 := by
    filter_upwards with y
    simp [f, Real.exp_pos]
  have hf_ne_top_σ : ∀ᵐ y ∂σ, f y ≠ ∞ := by
    filter_upwards with y
    simp [f]
  -- Apply the inverse density on both sides to recover the original measures.
  have h_inv :=
    congrArg (fun τ : Measure ℝ ↦ τ.withDensity fun y ↦ (f y)⁻¹) h
  calc
    ρ = (ρ.withDensity f).withDensity (fun y ↦ (f y)⁻¹) := by
      symm
      exact MeasureTheory.withDensity_inv_same hf hf_ne_zero_ρ hf_ne_top_ρ
    _ = (σ.withDensity f).withDensity (fun y ↦ (f y)⁻¹) := by
      simpa [f] using h_inv
    _ = σ := by
      exact MeasureTheory.withDensity_inv_same hf hf_ne_zero_σ hf_ne_top_σ

/-- Helper for Exercise 15.1.5: among nonnegative probability laws with one positive finite
Mellin moment, equality of the Mellin transform on `[0, ε]` determines the law. -/
theorem measure_eq_of_mellinTransform_eq_on_Icc_of_exists_lt_top
    (hε : 0 < ε) (hε₀ : 0 < ε₀)
    (hμ_moment : mellinTransform μ ε₀ < ∞)
    (h_eq : ∀ s ∈ Set.Icc (0 : ℝ) ε,
      mellinTransform μ s = mellinTransform ν s) :
    μ = ν := by
  -- Route correction: pass to the log-pushforward on `(0, ∞)` and use analytic continuation
  -- there, rather than trying to extend the smoothing route inside the product-cancellation proof.
  let η : ℝ := min ε ε₀
  have hη_pos : 0 < η := by
    exact lt_min hε hε₀
  have hμ_eta : mellinTransform μ η < ∞ := by
    exact mellinTransform_lt_top_of_le_exponent μ (le_of_lt hη_pos) (min_le_right _ _) hμ_moment
  have hη_mem : η ∈ Set.Icc (0 : ℝ) ε := by
    exact ⟨le_of_lt hη_pos, min_le_left _ _⟩
  have hν_eta : mellinTransform ν η < ∞ := by
    rw [← h_eq η hη_mem]
    exact hμ_eta
  let ρ : Measure ℝ := (μ.restrict (Set.Ioi 0)).map fun x : NNReal ↦ Real.log x
  let σ : Measure ℝ := (ν.restrict (Set.Ioi 0)).map fun x : NNReal ↦ Real.log x
  have hρσ : ρ = σ := by
    let r : ℝ := η / 2
    have hr : r ∈ Set.Ioo (0 : ℝ) η := by
      dsimp [r]
      constructor <;> linarith
    have h_eq_strip :
        ∀ s ∈ Set.Ioo (0 : ℝ) η, mellinTransform μ s = mellinTransform ν s := by
      intro s hs
      exact h_eq s ⟨le_of_lt hs.1, le_trans hs.2.le (min_le_left _ _)⟩
    have hstrip :
        Set.EqOn (ProbabilityTheory.complexMGF id ρ) (ProbabilityTheory.complexMGF id σ)
          {z : ℂ | z.re ∈ Set.Ioo 0 η} := by
      -- Extend the real Mellin equality to the strip where the log-pushforward complex mgfs are
      -- analytic.
      simpa [ρ, σ] using
        complexMGF_logRestrict_eqOn_strip_of_mellinTransform_eq μ ν hη_pos hμ_eta hν_eta
          h_eq_strip
    have hμ_r : mellinTransform μ r < ∞ := by
      exact mellinTransform_lt_top_of_le_exponent μ hr.1.le hr.2.le hμ_eta
    have hν_r : mellinTransform ν r < ∞ := by
      exact mellinTransform_lt_top_of_le_exponent ν hr.1.le hr.2.le hν_eta
    have hρ_r_int :
        Integrable (fun y : ℝ ↦ Real.exp (r * y)) ρ := by
      simpa [ρ] using (mgf_logRestrict_eq_mellinTransform μ hr.1 hμ_r).1
    have hσ_r_int :
        Integrable (fun y : ℝ ↦ Real.exp (r * y)) σ := by
      simpa [σ] using (mgf_logRestrict_eq_mellinTransform ν hr.1 hν_r).1
    let τρ : Measure ℝ := ρ.withDensity fun y ↦ ENNReal.ofReal (Real.exp (r * y))
    let τσ : Measure ℝ := σ.withDensity fun y ↦ ENNReal.ofReal (Real.exp (r * y))
    haveI : IsFiniteMeasure τρ := by
      dsimp [τρ]
      exact MeasureTheory.isFiniteMeasure_withDensity_ofReal hρ_r_int.2
    haveI : IsFiniteMeasure τσ := by
      dsimp [τσ]
      exact MeasureTheory.isFiniteMeasure_withDensity_ofReal hσ_r_int.2
    have hweighted : τρ = τσ := by
      -- Compare the weighted measures through their characteristic functions, which are the strip
      -- values of the original complex mgfs on the vertical line `re = r`.
      apply Measure.ext_of_charFun
      funext t
      rw [show τρ = ρ.withDensity (fun y ↦ ENNReal.ofReal (Real.exp (r * y))) by rfl]
      rw [show τσ = σ.withDensity (fun y ↦ ENNReal.ofReal (Real.exp (r * y))) by rfl]
      rw [charFun_expWeightedLogMeasure_eq_complexMGF ρ]
      rw [charFun_expWeightedLogMeasure_eq_complexMGF σ]
      exact hstrip (by simpa [r] using hr)
    -- Undo the exponential weight to recover equality of the original log-pushforwards.
    exact measure_eq_of_expWeighted_eq ρ σ r (by simpa [τρ, τσ] using hweighted)
  have hrestrict : μ.restrict (Set.Ioi 0) = ν.restrict (Set.Ioi 0) := by
    -- Map the equal log-pushforwards back by `exp` to recover equality on `(0, ∞)`.
    have hmap :=
      congrArg
        (fun τ : Measure ℝ ↦
          τ.map (fun y : ℝ ↦ (⟨Real.exp y, by positivity⟩ : NNReal)))
        hρσ
    simpa [ρ, σ, map_exp_positiveLogRestrict] using hmap
  exact measure_eq_of_restrictIoi_eq_of_isProbability hrestrict

end

section

variable {μ : Measure Ω} [IsProbabilityMeasure μ] {X Y Z : Ω → NNReal}

section

variable {ρX ρY : Measure NNReal} [IsProbabilityMeasure ρX] [IsProbabilityMeasure ρY]

/-- Helper for Exercise 15.1.5: once the Mellin transforms of two probability laws agree on
`[0, s₀]` and one positive witness moment is finite, the local Mellin uniqueness theorem
identifies the laws. -/
lemma measure_eq_of_mellinTransform_eq_on_Icc_at_witness
    {s₀ : ℝ} (hs₀_pos : 0 < s₀) (hρX_s₀_lt_top : mellinTransform ρX s₀ < ∞)
    (hXY_eq : ∀ t ∈ Set.Icc (0 : ℝ) s₀, mellinTransform ρX t = mellinTransform ρY t) :
    ρX = ρY := by
  -- Reuse the interval-uniqueness theorem with both interval parameters set to the witness
  -- exponent `s₀`.
  exact measure_eq_of_mellinTransform_eq_on_Icc_of_exists_lt_top
    (μ := ρX) (ν := ρY) hs₀_pos hs₀_pos hρX_s₀_lt_top hXY_eq

end

-- Proof sketch: for measurable nonnegative random variables `X`, `Y`, and `Z`, push forward
-- their laws to finite measures on `[0, ∞)`.
-- The assumptions `IndepFun X Z μ` and `IndepFun Y Z μ` identify the laws of `XZ` and `YZ` with
-- the multiplicative convolutions of the laws of `X` and `Y` with the law of `Z`. The Mellin
-- hypothesis is expressed through the canonical owner `mellinTransform`; by
-- `mellinTransform_map` it is the same as a positive finite Mellin moment of `XZ`.
-- The hypothesis `ℙ[Z > 0] > 0` prevents the Mellin transform of `Z` from vanishing identically,
-- so one cancels it and applies
-- `measure_eq_of_mellinTransform_eq_on_Icc_of_exists_lt_top` to the laws of `X` and `Y`
-- (equivalently, uniqueness of Laplace transforms after taking logarithms).
/-- Helper for Exercise 15.1.5: the Mellin transform of the law of a product of independent
nonnegative random variables factors into the product of their Mellin transforms. -/
lemma mellinTransform_map_mul_eq
    {U V : Ω → NNReal} (hU : Measurable U) (hV : Measurable V)
    (hUV_indep : IndepFun U V μ) {t : ℝ} :
    mellinTransform (μ.map (U * V)) t =
      mellinTransform (μ.map U) t * mellinTransform (μ.map V) t := by
  -- Rewrite all Mellin transforms as lower integrals on `Ω`.
  rw [mellinTransform_map (μ := μ) (X := U * V) (hX := (hU.mul hV).aemeasurable) t]
  rw [mellinTransform_map (μ := μ) (X := U) (hX := hU.aemeasurable) t]
  rw [mellinTransform_map (μ := μ) (X := V) (hX := hV.aemeasurable) t]
  -- Independence is preserved after composing with the Mellin kernel.
  have hkernel_meas : Measurable (fun x : NNReal ↦ (x : ℝ≥0∞) ^ t) := by
    exact (Measurable.coe_nnreal_ennreal measurable_id).pow_const t
  have hpow_indep :
      IndepFun (fun ω ↦ (U ω : ℝ≥0∞) ^ t) (fun ω ↦ (V ω : ℝ≥0∞) ^ t) μ := by
    exact hUV_indep.comp hkernel_meas hkernel_meas
  -- The product kernel splits because `(uv)^t = u^t v^t` for `t ≥ 0`.
  simpa [Pi.mul_apply, ENNReal.coe_mul_rpow] using
    ProbabilityTheory.lintegral_mul_eq_lintegral_mul_lintegral_of_indepFun'
      ((hU.aemeasurable.coe_nnreal_ennreal).pow_const t)
      ((hV.aemeasurable.coe_nnreal_ennreal).pow_const t) hpow_indep

/-- Helper for Exercise 15.1.5: a nonnegative random variable that is positive with positive
probability has a strictly positive Mellin transform at every positive exponent. -/
lemma mellinTransform_pos_of_measure_preimage_Ioi_pos
    {V : Ω → NNReal} (hV : Measurable V) {t : ℝ} (ht : 0 < t)
    (hV_pos : 0 < μ (V ⁻¹' Set.Ioi 0)) :
    0 < mellinTransform (μ.map V) t := by
  -- Rewrite the Mellin transform on `Ω` and detect positivity through the function support.
  rw [mellinTransform_map (μ := μ) (X := V) (hX := hV.aemeasurable) t]
  rw [MeasureTheory.lintegral_pos_iff_support]
  · refine lt_of_lt_of_le hV_pos ?_
    refine measure_mono ?_
    intro ω hω
    have hω_pos : 0 < (V ω : ℝ≥0∞) := by
      simpa [Set.mem_preimage, Set.mem_Ioi] using hω
    exact (ENNReal.rpow_pos_of_nonneg hω_pos ht.le).ne'
  · fun_prop

/-- Helper for Exercise 15.1.5: if the product Mellin factor is `∞` at the witness exponent, then
the other factor must vanish in order for the product Mellin transform to stay finite. -/
lemma mellinTransform_eq_zero_of_mul_eq_top
    {a b : ℝ≥0∞} (hprod : a * b < ∞) (hb_top : b = ∞) :
    a = 0 := by
  -- A finite product with an infinite factor can only occur when the other factor is zero.
  rcases (ENNReal.mul_lt_top_iff.mp hprod) with hfin | ha_zero | hb_zero
  · exfalso
    simpa [hb_top] using hfin.2
  · exact ha_zero
  · exfalso
    simp [hb_top] at hb_zero

/-- Helper for Exercise 15.1.5: a finite product with a positive finite right factor has a finite
left factor. -/
lemma ennreal_ltTop_left_of_mul_ltTop_of_right_pos
    {a b : ℝ≥0∞} (hprod : a * b < ∞) (hb_pos : 0 < b) :
    a < ∞ := by
  -- Route correction: instead of rebuilding local Mellin uniqueness, first isolate the basic
  -- ENNReal finiteness cancellation needed to expose the canonical Exercise 15.1.4 theorem.
  refine lt_top_iff_ne_top.mpr fun ha_top ↦ ?_
  rw [ha_top] at hprod
  simpa only [ENNReal.top_mul hb_pos.ne', lt_self_iff_false] using hprod

/-- Exercise 15.1.5: if `X`, `Y`, and `Z` are nonnegative measurable random variables, `Z` is
independent of both `X` and `Y`, `XZ =ᵈ YZ`, `Z` is positive with positive probability, and the
law of `XZ` has a finite Mellin transform at some positive exponent, then `X =ᵈ Y`. -/
theorem identDistrib_of_mul_identDistrib_of_indepFun
    (hX : Measurable X) (hY : Measurable Y) (hZ : Measurable Z)
    (hXZ_indep : IndepFun X Z μ)
    (hYZ_indep : IndepFun Y Z μ)
    (hZ_pos : 0 < μ (Z ⁻¹' Set.Ioi 0))
    (h_mellin : ∃ s : ℝ, 0 < s ∧
      mellinTransform (μ.map (X * Z)) s < ∞)
    (h_mul : IdentDistrib (X * Z) (Y * Z) μ μ) :
    IdentDistrib X Y μ μ := by
  rcases h_mellin with ⟨s₀, hs₀_pos, hXZ_s₀_lt_top⟩
  let ρX : Measure NNReal := μ.map X
  let ρY : Measure NNReal := μ.map Y
  let ρZ : Measure NNReal := μ.map Z
  letI : IsProbabilityMeasure ρX := MeasureTheory.Measure.isProbabilityMeasure_map hX.aemeasurable
  letI : IsProbabilityMeasure ρY := MeasureTheory.Measure.isProbabilityMeasure_map hY.aemeasurable
  letI : IsProbabilityMeasure ρZ := MeasureTheory.Measure.isProbabilityMeasure_map hZ.aemeasurable
  have hmul_map_eq :
      ∀ t : ℝ,
        mellinTransform (μ.map (X * Z)) t = mellinTransform (μ.map (Y * Z)) t := by
    intro t
    exact congrArg (fun ν : Measure NNReal ↦ mellinTransform ν t) h_mul.map_eq
  by_cases hZ_s₀_top : mellinTransform ρZ s₀ = ∞
  · -- If the `Z` factor is infinite, finiteness of the product moment forces both `X` and `Y`
    -- to vanish almost surely.
    have hX_s₀_eq_zero : mellinTransform ρX s₀ = 0 := by
      have hprod_lt_top :
          mellinTransform ρX s₀ * mellinTransform ρZ s₀ < ∞ := by
        rw [← mellinTransform_map_mul_eq (μ := μ) hX hZ hXZ_indep]
        simpa [ρX, ρZ] using hXZ_s₀_lt_top
      exact mellinTransform_eq_zero_of_mul_eq_top hprod_lt_top hZ_s₀_top
    have hYZ_s₀_lt_top : mellinTransform (μ.map (Y * Z)) s₀ < ∞ := by
      rw [← hmul_map_eq s₀]
      exact hXZ_s₀_lt_top
    have hY_s₀_eq_zero : mellinTransform ρY s₀ = 0 := by
      have hprod_lt_top :
          mellinTransform ρY s₀ * mellinTransform ρZ s₀ < ∞ := by
        rw [← mellinTransform_map_mul_eq (μ := μ) hY hZ hYZ_indep]
        simpa [ρY, ρZ] using hYZ_s₀_lt_top
      exact mellinTransform_eq_zero_of_mul_eq_top hprod_lt_top hZ_s₀_top
    -- A zero Mellin moment at a positive exponent means the random variable is zero almost surely.
    rw [mellinTransform_map (μ := μ) (X := X) (hX := hX.aemeasurable) s₀] at hX_s₀_eq_zero
    rw [mellinTransform_map (μ := μ) (X := Y) (hX := hY.aemeasurable) s₀] at hY_s₀_eq_zero
    have hX_ae_zero : X =ᵐ[μ] 0 := by
      have hX_ae_zero_ennreal :
          (fun ω ↦ (X ω : ℝ≥0∞)) =ᵐ[μ] 0 := by
        exact ENNReal.ae_eq_zero_of_lintegral_rpow_eq_zero hs₀_pos.le
          hX.aemeasurable.coe_nnreal_ennreal hX_s₀_eq_zero
      filter_upwards [hX_ae_zero_ennreal] with ω hω
      exact ENNReal.coe_eq_zero.mp hω
    have hY_ae_zero : Y =ᵐ[μ] 0 := by
      have hY_ae_zero_ennreal :
          (fun ω ↦ (Y ω : ℝ≥0∞)) =ᵐ[μ] 0 := by
        exact ENNReal.ae_eq_zero_of_lintegral_rpow_eq_zero hs₀_pos.le
          hY.aemeasurable.coe_nnreal_ennreal hY_s₀_eq_zero
      filter_upwards [hY_ae_zero_ennreal] with ω hω
      exact ENNReal.coe_eq_zero.mp hω
    -- Both laws coincide with the Dirac mass at `0`.
    exact (IdentDistrib.of_ae_eq hX.aemeasurable hX_ae_zero).trans
      (IdentDistrib.of_ae_eq hY.aemeasurable hY_ae_zero).symm
  · -- In the finite branch, cancel the positive Mellin factor of `Z` on `[0, s₀]`.
    -- Route correction: reuse the canonical Exercise 15.1.4 uniqueness theorem after proving
    -- intervalwise Mellin cancellation for the laws of `X` and `Y`.
    have hZ_s₀_lt_top : mellinTransform ρZ s₀ < ∞ := by
      exact lt_top_iff_ne_top.mpr hZ_s₀_top
    have hYZ_s₀_lt_top : mellinTransform (μ.map (Y * Z)) s₀ < ∞ := by
      rw [← hmul_map_eq s₀]
      exact hXZ_s₀_lt_top
    have hZ_s₀_pos : 0 < mellinTransform ρZ s₀ := by
      simpa [ρZ] using
        mellinTransform_pos_of_measure_preimage_Ioi_pos (μ := μ) hZ hs₀_pos hZ_pos
    have hX_s₀_lt_top : mellinTransform ρX s₀ < ∞ := by
      have hprod_lt_top :
          mellinTransform ρX s₀ * mellinTransform ρZ s₀ < ∞ := by
        rw [← mellinTransform_map_mul_eq (μ := μ) hX hZ hXZ_indep]
        simpa [ρX, ρZ] using hXZ_s₀_lt_top
      exact ennreal_ltTop_left_of_mul_ltTop_of_right_pos hprod_lt_top hZ_s₀_pos
    have hY_s₀_lt_top : mellinTransform ρY s₀ < ∞ := by
      have hprod_lt_top :
          mellinTransform ρY s₀ * mellinTransform ρZ s₀ < ∞ := by
        rw [← mellinTransform_map_mul_eq (μ := μ) hY hZ hYZ_indep]
        simpa [ρY, ρZ] using hYZ_s₀_lt_top
      exact ennreal_ltTop_left_of_mul_ltTop_of_right_pos hprod_lt_top hZ_s₀_pos
    have hXY_eq :
        ∀ t ∈ Set.Icc (0 : ℝ) s₀, mellinTransform ρX t = mellinTransform ρY t := by
      intro t ht
      rcases eq_or_lt_of_le ht.1 with rfl | ht_pos
      · -- At exponent `0`, every probability law has Mellin transform `1`.
        simp [ρX, ρY, mellinTransform]
      · -- For positive exponents, factor through `Z`, cancel its positive Mellin transform, and
        -- compare the remaining `X` and `Y` factors.
        have hZ_t_lt_top : mellinTransform ρZ t < ∞ := by
          exact mellinTransform_lt_top_of_le_exponent (μ := ρZ) ht.1 ht.2 hZ_s₀_lt_top
        have hX_t_lt_top : mellinTransform ρX t < ∞ := by
          exact mellinTransform_lt_top_of_le_exponent (μ := ρX) ht.1 ht.2 hX_s₀_lt_top
        have hY_t_lt_top : mellinTransform ρY t < ∞ := by
          exact mellinTransform_lt_top_of_le_exponent (μ := ρY) ht.1 ht.2 hY_s₀_lt_top
        have hZ_t_pos : 0 < mellinTransform ρZ t := by
          simpa [ρZ] using
            mellinTransform_pos_of_measure_preimage_Ioi_pos (μ := μ) hZ ht_pos hZ_pos
        have hmul_t :
            mellinTransform ρX t * mellinTransform ρZ t =
              mellinTransform ρY t * mellinTransform ρZ t := by
          calc
            mellinTransform ρX t * mellinTransform ρZ t
                = mellinTransform (μ.map (X * Z)) t := by
                    symm
                    simpa [ρX, ρZ] using
                      (mellinTransform_map_mul_eq (μ := μ) hX hZ hXZ_indep (t := t))
            _ = mellinTransform (μ.map (Y * Z)) t := by
              exact hmul_map_eq t
            _ = mellinTransform ρY t * mellinTransform ρZ t := by
              simpa [ρY, ρZ] using
                (mellinTransform_map_mul_eq (μ := μ) hY hZ hYZ_indep (t := t))
        have hmul_t_real := congrArg ENNReal.toReal hmul_t
        rw [ENNReal.toReal_mul, ENNReal.toReal_mul] at hmul_t_real
        have hZ_t_toReal_ne_zero : (mellinTransform ρZ t).toReal ≠ 0 := by
          exact (ENNReal.toReal_pos (ne_of_gt hZ_t_pos) hZ_t_lt_top.ne).ne'
        exact (ENNReal.toReal_eq_toReal_iff' hX_t_lt_top.ne hY_t_lt_top.ne).mp <|
          mul_right_cancel₀ hZ_t_toReal_ne_zero hmul_t_real
    have hρ_eq : ρX = ρY := by
      -- Route correction: the final step now directly reuses the earlier uniqueness theorem,
      -- so the finite-branch work only has to produce intervalwise Mellin equality.
      exact measure_eq_of_mellinTransform_eq_on_Icc_at_witness hs₀_pos hX_s₀_lt_top hXY_eq
    -- Package equality of pushforward laws back into `IdentDistrib`.
    refine ⟨hX.aemeasurable, hY.aemeasurable, ?_⟩
    simpa [ρX, ρY] using hρ_eq

end
