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

/-- The Mellin transform of a measure on `[0, ∞)`. -/
abbrev mellinTransform (μ : Measure NNReal) (s : ℝ) : ℝ≥0∞ :=
  ∫⁻ x, (x : ℝ≥0∞) ^ s ∂μ

-- Proof sketch: unfold `mellinTransform` for the pushforward law `Measure.map X μ` and rewrite the
-- lower integral using `lintegral_map'`, so the Mellin transform becomes the extended expectation
-- of the canonical `ℝ≥0∞` power of `X`.
/-- The Mellin transform of the law of a nonnegative random variable is the lower integral of
`x ↦ x ^ s` along that variable. -/
theorem mellinTransform_map (μ : Measure Ω) (X : Ω → NNReal) (hX : AEMeasurable X μ) (s : ℝ) :
    mellinTransform (μ.map X) s =
      ∫⁻ ω, (X ω : ℝ≥0∞) ^ s ∂μ := by
  have hpow : AEMeasurable (fun x : NNReal ↦ (x : ℝ≥0∞) ^ s) (μ.map X) :=
    by fun_prop
  simpa [mellinTransform] using
    (lintegral_map' hpow hX)

section

variable {μ ν : Measure NNReal} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] {ε ε₀ : ℝ}

/-- Helper for Exercise 15.1.4: the positive Mellin kernel at a smaller exponent is bounded by
`1 + x ^ ε₀`. -/
lemma ennreal_rpow_le_one_add_rpow (x : NNReal) {s ε₀ : ℝ} (hs : 0 ≤ s) (hs_le : s ≤ ε₀) :
    ((x : ℝ≥0∞) ^ s) ≤ 1 + ((x : ℝ≥0∞) ^ ε₀) := by
  -- Split into the regimes `x ≤ 1` and `1 ≤ x`, where exponent monotonicity goes in opposite
  -- directions.
  by_cases hx : (x : ℝ≥0∞) ≤ 1
  · calc
      ((x : ℝ≥0∞) ^ s) ≤ (x : ℝ≥0∞) ^ (0 : ℝ) :=
        ENNReal.rpow_le_rpow_of_exponent_ge hx hs
      _ = 1 := by simp
      _ ≤ 1 + ((x : ℝ≥0∞) ^ ε₀) := by simp
  · have hx' : (1 : ℝ≥0∞) ≤ (x : ℝ≥0∞) := le_of_not_ge hx
    calc
      ((x : ℝ≥0∞) ^ s) ≤ (x : ℝ≥0∞) ^ ε₀ :=
        ENNReal.rpow_le_rpow_of_exponent_le hx' hs_le
      _ ≤ 1 + ((x : ℝ≥0∞) ^ ε₀) := by simp

/-- Helper for Exercise 15.1.4: the negative Mellin kernel at a smaller exponent is bounded by
`1 + x ^ (-ε₀)`. -/
lemma ennreal_rpow_neg_le_one_add_rpow_neg (x : NNReal) {s ε₀ : ℝ}
    (hs : 0 ≤ s) (hs_le : s ≤ ε₀) :
    ((x : ℝ≥0∞) ^ (-s)) ≤ 1 + ((x : ℝ≥0∞) ^ (-ε₀)) := by
  -- The same two-region split works after reversing exponent monotonicity on `[0,1]`.
  by_cases hx : (x : ℝ≥0∞) ≤ 1
  · calc
      ((x : ℝ≥0∞) ^ (-s)) ≤ (x : ℝ≥0∞) ^ (-ε₀) := by
        refine ENNReal.rpow_le_rpow_of_exponent_ge hx ?_
        linarith
      _ ≤ 1 + ((x : ℝ≥0∞) ^ (-ε₀)) := by simp
  · have hx' : (1 : ℝ≥0∞) ≤ (x : ℝ≥0∞) := le_of_not_ge hx
    calc
      ((x : ℝ≥0∞) ^ (-s)) ≤ (x : ℝ≥0∞) ^ (0 : ℝ) := by
        refine ENNReal.rpow_le_rpow_of_exponent_le hx' ?_
        linarith
      _ = 1 := by simp
      _ ≤ 1 + ((x : ℝ≥0∞) ^ (-ε₀)) := by simp

/-- Helper for Exercise 15.1.4: a finite positive Mellin moment controls all smaller
nonnegative exponents. -/
lemma mellinTransform_lt_top_of_le_exponent (μ : Measure NNReal) [IsProbabilityMeasure μ]
    {s ε₀ : ℝ} (hs : 0 ≤ s) (hs_le : s ≤ ε₀) (hμ_moment : mellinTransform μ ε₀ < ∞) :
    mellinTransform μ s < ∞ := by
  -- Compare the kernel pointwise with an integrable envelope and integrate the inequality.
  calc
    mellinTransform μ s
      = ∫⁻ x, (x : ℝ≥0∞) ^ s ∂μ := rfl
    _ ≤ ∫⁻ x, (1 + (x : ℝ≥0∞) ^ ε₀) ∂μ := by
      refine lintegral_mono fun x ↦ ?_
      exact ennreal_rpow_le_one_add_rpow x hs hs_le
    _ < ∞ := by
      rw [lintegral_add_right]
      · have hone : (∫⁻ x, (1 : ℝ≥0∞) ∂μ) < ∞ := by
          simp
        simpa [mellinTransform] using ENNReal.add_lt_top.2 ⟨hone, hμ_moment⟩
      · fun_prop

/-- Helper for Exercise 15.1.4: a finite negative Mellin moment controls all smaller
nonnegative exponents. -/
lemma mellinTransform_neg_lt_top_of_le_exponent (μ : Measure NNReal) [IsProbabilityMeasure μ]
    {s ε₀ : ℝ} (hs : 0 ≤ s) (hs_le : s ≤ ε₀) (hμ_moment : mellinTransform μ (-ε₀) < ∞) :
    mellinTransform μ (-s) < ∞ := by
  -- The negative kernels admit the same `1 + x ^ (-ε₀)` envelope.
  calc
    mellinTransform μ (-s)
      = ∫⁻ x, (x : ℝ≥0∞) ^ (-s) ∂μ := rfl
    _ ≤ ∫⁻ x, (1 + (x : ℝ≥0∞) ^ (-ε₀)) ∂μ := by
      refine lintegral_mono fun x ↦ ?_
      exact ennreal_rpow_neg_le_one_add_rpow_neg x hs hs_le
    _ < ∞ := by
      rw [lintegral_add_right]
      · have hone : (∫⁻ x, (1 : ℝ≥0∞) ∂μ) < ∞ := by
          simp
        simpa [mellinTransform] using ENNReal.add_lt_top.2 ⟨hone, hμ_moment⟩
      · fun_prop

/-- Helper for Exercise 15.1.4: finiteness of a negative Mellin moment forces zero mass at `0`. -/
lemma measure_zero_of_mellinTransform_neg_lt_top (μ : Measure NNReal) [IsProbabilityMeasure μ]
    {s : ℝ} (hs : 0 < s) (hμ_moment : mellinTransform μ (-s) < ∞) :
    μ {0} = 0 := by
  -- A positive atom at `0` would contribute `∞` to the negative Mellin integral.
  by_contra hμ_zero
  have hsingleton :
      (∫⁻ x in ({0} : Set NNReal), (x : ℝ≥0∞) ^ (-s) ∂μ) = ∞ := by
    have hconst :
        (fun x : NNReal ↦ (x : ℝ≥0∞) ^ (-s)) =ᵐ[μ.restrict ({0} : Set NNReal)] fun _ ↦ ∞ := by
      filter_upwards [ae_restrict_mem (measurableSet_singleton (0 : NNReal))] with x hx
      have hx0 : x = 0 := by
        simpa using hx
      simp [hx0, hs]
    rw [lintegral_congr_ae hconst, lintegral_const]
    simp [hμ_zero]
  have htop : mellinTransform μ (-s) = ∞ := by
    apply top_unique
    calc
      ∞ = ∫⁻ x in ({0} : Set NNReal), (x : ℝ≥0∞) ^ (-s) ∂μ := hsingleton.symm
      _ ≤ ∫⁻ x, (x : ℝ≥0∞) ^ (-s) ∂μ := by
        simpa using
          (lintegral_mono_set (μ := μ) (f := fun x : NNReal ↦ (x : ℝ≥0∞) ^ (-s))
            (Set.singleton_subset_iff.mpr (by simp : (0 : NNReal) ∈ Set.univ)))
  exact (ne_of_lt hμ_moment) htop

/-- Helper for Exercise 15.1.4: Mellin transforms of inversion pushforwards are the negative
Mellin transforms, once the law has no atom at `0`. -/
lemma mellinTransform_map_inv_eq_neg (μ : Measure NNReal) (hμ0 : μ {0} = 0) {s : ℝ} :
    mellinTransform (μ.map fun x : NNReal ↦ x⁻¹) s = mellinTransform μ (-s) := by
  -- Rewrite the pushforward integral and compare the kernels away from the null atom at `0`.
  rw [mellinTransform_map (μ := μ) (X := fun x : NNReal ↦ x⁻¹)]
  · refine lintegral_congr_ae ?_
    have hμ_ae : ∀ᵐ x ∂μ, x ≠ 0 := by
      rw [ae_iff]
      simp [hμ0]
    filter_upwards [hμ_ae] with x hx
    rw [ENNReal.coe_inv hx, ENNReal.inv_rpow, ENNReal.rpow_neg]
  · fun_prop

/-- Helper for Exercise 15.1.4: pushing the positive-part log-pushforward forward by `exp`
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
    exact
      (Measure.map_congr hcomp).trans
        (Measure.map_id : Measure.map id (μ.restrict (Set.Ioi 0)) = _)
  · fun_prop
  · fun_prop

/-- Helper for Exercise 15.1.4: for probability measures on `NNReal`, equality on `(0, ∞)`
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

/-- Helper for Exercise 15.1.4: a positive finite Mellin moment identifies the exponential
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

/-- Helper for Exercise 15.1.4: Mellin equality on a positive real interval extends to equality of
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
    change Integrable (fun x : ℝ ↦ Real.exp (0 * x)) ρ
    simp
  have hσ0 : 0 ∈ ProbabilityTheory.integrableExpSet id σ := by
    change Integrable (fun x : ℝ ↦ Real.exp (0 * x)) σ
    simp
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

/-- Helper for Exercise 15.1.4: weighting a real measure by `exp (r * ·)` turns its characteristic
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

/-- Helper for Exercise 15.1.4: equality of the exponentially weighted `withDensity` measures
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

-- Proof sketch: first handle laws with continuous densities on `[0, ∞)` by identifying the
-- Mellin transform with a holomorphic Mellin integral and invoking analytic continuation. Then
-- smooth arbitrary laws by multiplying with an independent `U_[1 - δ, 1]` factor, compare the
-- smoothed Mellin transforms on `[0, ε]`, and let `δ ↓ 0` using convergence in distribution of
-- the smoothed laws.
/-- Exercise 15.1.4: among nonnegative probability laws with some positive finite Mellin moment,
the values of the Mellin transform on any interval `[0, ε]` determine the law. -/
theorem measure_eq_of_mellinTransform_eq_on_Icc_of_exists_lt_top
    (hε : 0 < ε) (hε₀ : 0 < ε₀)
    (hμ_moment : mellinTransform μ ε₀ < ∞)
    (h_eq : ∀ s ∈ Set.Icc (0 : ℝ) ε,
      mellinTransform μ s = mellinTransform ν s) :
    μ = ν := by
  -- Route correction: the textbook smoothing hint preserves any atom at `0`, so the stable Lean
  -- route is to pass to the log-pushforward on `(0, ∞)` and then use analytic continuation there.
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

-- Proof sketch: apply the positive-exponent characterization theorem to the pushforwards of `μ`
-- and `ν` under inversion `x ↦ x⁻¹`. The finite negative Mellin moment becomes a positive Mellin
-- moment for the inverted laws, and equality of `m(-s)` on `[0, ε]` becomes equality of the
-- ordinary Mellin transforms of those inverted laws.
/-- The negative-exponent Mellin data `m(-s)` on `[0, ε]` determine a nonnegative probability law
once one negative Mellin moment is finite. -/
theorem measure_eq_of_mellinTransform_neg_eq_on_Icc_of_exists_lt_top
    (hε : 0 < ε) (hε₀ : 0 < ε₀)
    (hμ_moment : mellinTransform μ (-ε₀) < ∞)
    (h_eq : ∀ s ∈ Set.Icc (0 : ℝ) ε,
      mellinTransform μ (-s) = mellinTransform ν (-s)) :
    μ = ν := by
  -- Pass to the inversion pushforwards, where negative Mellin data become positive Mellin data.
  have hμ0 : μ {0} = 0 := measure_zero_of_mellinTransform_neg_lt_top μ hε₀ hμ_moment
  let η : ℝ := min ε ε₀
  have hη_pos : 0 < η := by
    exact lt_min hε hε₀
  have hη_mem : η ∈ Set.Icc (0 : ℝ) ε := by
    exact ⟨le_of_lt hη_pos, min_le_left _ _⟩
  have hμ_eta : mellinTransform μ (-η) < ∞ := by
    exact mellinTransform_neg_lt_top_of_le_exponent μ (le_of_lt hη_pos) (min_le_right _ _)
      hμ_moment
  have hν_eta : mellinTransform ν (-η) < ∞ := by
    rw [← h_eq η hη_mem]
    exact hμ_eta
  have hν0 : ν {0} = 0 := measure_zero_of_mellinTransform_neg_lt_top ν hη_pos hν_eta
  have hμ_map : mellinTransform (μ.map fun x : NNReal ↦ x⁻¹) ε₀ < ∞ := by
    rw [mellinTransform_map_inv_eq_neg μ hμ0]
    exact hμ_moment
  have hmap_eq :
      ∀ s ∈ Set.Icc (0 : ℝ) ε,
        mellinTransform (μ.map fun x : NNReal ↦ x⁻¹) s =
          mellinTransform (ν.map fun x : NNReal ↦ x⁻¹) s := by
    intro s hs
    rw [mellinTransform_map_inv_eq_neg μ hμ0, mellinTransform_map_inv_eq_neg ν hν0]
    exact h_eq s hs
  haveI : IsProbabilityMeasure (μ.map fun x : NNReal ↦ x⁻¹) :=
    Measure.isProbabilityMeasure_map (by fun_prop)
  haveI : IsProbabilityMeasure (ν.map fun x : NNReal ↦ x⁻¹) :=
    Measure.isProbabilityMeasure_map (by fun_prop)
  have hmap :
      μ.map (fun x : NNReal ↦ x⁻¹) = ν.map (fun x : NNReal ↦ x⁻¹) := by
    exact measure_eq_of_mellinTransform_eq_on_Icc_of_exists_lt_top hε hε₀ hμ_map hmap_eq
  -- Map once more by inversion and use involutivity to recover the original laws.
  have hmap_inv := congrArg (fun ρ : Measure NNReal ↦ ρ.map (fun x : NNReal ↦ x⁻¹)) hmap
  have hμ_back :
      (μ.map (fun x : NNReal ↦ x⁻¹)).map (fun x : NNReal ↦ x⁻¹) = μ := by
    rw [Measure.map_map (by fun_prop) (by fun_prop)]
    have hcongr : (fun x : NNReal ↦ (x⁻¹)⁻¹) =ᵐ[μ] id := by
      filter_upwards with x
      simp
    have hmap' :
        Measure.map (fun x : NNReal ↦ (x⁻¹)⁻¹) μ = Measure.map (fun x : NNReal ↦ x) μ :=
      Measure.map_congr hcongr
    calc
      Measure.map (fun x : NNReal ↦ (x⁻¹)⁻¹) μ = Measure.map id μ := hmap'
      _ = μ := Measure.map_id
  have hν_back :
      (ν.map (fun x : NNReal ↦ x⁻¹)).map (fun x : NNReal ↦ x⁻¹) = ν := by
    rw [Measure.map_map (by fun_prop) (by fun_prop)]
    have hcongr : (fun x : NNReal ↦ (x⁻¹)⁻¹) =ᵐ[ν] id := by
      filter_upwards with x
      simp
    have hmap' :
        Measure.map (fun x : NNReal ↦ (x⁻¹)⁻¹) ν = Measure.map (fun x : NNReal ↦ x) ν :=
      Measure.map_congr hcongr
    calc
      Measure.map (fun x : NNReal ↦ (x⁻¹)⁻¹) ν = Measure.map id ν := hmap'
      _ = ν := Measure.map_id
  exact hμ_back.symm.trans (hmap_inv.trans hν_back)

end
