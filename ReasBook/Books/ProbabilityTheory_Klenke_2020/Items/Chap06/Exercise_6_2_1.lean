/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Books.ProbabilityTheory_Klenke_2020.Items.Chap06.Definition_6_2
import Books.ProbabilityTheory_Klenke_2020.Items.Chap06.Remark_6_4
import Books.ProbabilityTheory_Klenke_2020.Items.Chap06.Theorem_6_7

open Filter MeasureTheory
open scoped ENNReal Topology

universe u v

variable {Ω : Type u} [MeasurableSpace Ω]

noncomputable section

/-- The canonical weighted owner measure attached to a real-valued density `H`. -/
def weightedMeasure (μ : Measure Ω) (H : Ω → ℝ) : Measure Ω :=
  μ.withDensity (fun ω ↦ ENNReal.ofReal (H ω))

/-- Helper for Exercise 6.2.1: replacing `H` by the measurable representative supplied by
integrability does not change `weightedMeasure μ H`. -/
theorem weightedMeasure_eq_densityRepresentative
    (μ : Measure Ω) {H : Ω → ℝ} (hH_int : Integrable H μ) :
    weightedMeasure μ H =
      weightedMeasure μ (hH_int.aestronglyMeasurable.mk H) := by
  -- `withDensity` depends on the density only up to `μ`-almost-everywhere equality.
  rw [weightedMeasure, weightedMeasure]
  refine withDensity_congr_ae ?_
  filter_upwards [hH_int.aestronglyMeasurable.ae_eq_mk] with ω hω
  simp [hω]

/-- Helper for Exercise 6.2.1: the measurable representative supplied by integrability preserves
the almost-everywhere positivity of the original density. -/
theorem densityRepresentative_pos_ae
    (μ : Measure Ω) {H : Ω → ℝ} (hH_int : Integrable H μ)
    (hH_pos : ∀ᵐ ω ∂μ, 0 < H ω) :
    ∀ᵐ ω ∂μ, 0 < hH_int.aestronglyMeasurable.mk H ω := by
  -- Proof comment: combine the original positivity with the almost-everywhere equality to the
  -- measurable representative.
  filter_upwards [hH_pos, hH_int.aestronglyMeasurable.ae_eq_mk] with ω hω hmk
  simpa [hmk] using hω

/-- Helper for Exercise 6.2.1: on a null-measurable set where the density is bounded below by
`(N + 1)⁻¹`, the ambient measure is controlled by the weighted measure. -/
theorem measure_le_nat_mul_weightedMeasure_of_lowerBound
    (μ : Measure Ω) {Hm : Ω → ℝ} {s : Set Ω}
    (hs : NullMeasurableSet s μ) (N : ℕ)
    (h_lower : ∀ ω ∈ s, (1 : ℝ) / (N + 1) ≤ Hm ω) :
    μ s ≤ (N + 1 : ℝ≥0∞) * weightedMeasure μ Hm s := by
  -- Proof comment: on `s`, the pointwise inequality `1 ≤ (N + 1) * Hm` integrates to the
  -- desired measure comparison.
  rw [weightedMeasure, withDensity_apply₀ (μ := μ) (f := fun ω ↦ ENNReal.ofReal (Hm ω)) hs]
  calc
    μ s = ∫⁻ ω in s, (1 : ℝ≥0∞) ∂μ := by simp
    _ ≤ ∫⁻ ω in s, (N + 1 : ℝ≥0∞) * ENNReal.ofReal (Hm ω) ∂μ := by
          refine lintegral_mono_ae ?_
          refine (ae_restrict_iff'₀ hs).2 <| Filter.Eventually.of_forall fun ω hω ↦ ?_
          have hω_lower : (1 : ℝ) / (N + 1) ≤ Hm ω := h_lower ω hω
          have hω_nonneg : 0 ≤ Hm ω := le_trans (by positivity) hω_lower
          have hN_pos : (0 : ℝ) < N + 1 := by positivity
          have hmul : (1 : ℝ) ≤ Hm ω * (N + 1) := by
            have hscaled := hω_lower
            have hN_ne : (N + 1 : ℝ) ≠ 0 := by positivity
            field_simp [hN_ne] at hscaled ⊢
            nlinarith
          calc
            (1 : ℝ≥0∞) = ENNReal.ofReal (1 : ℝ) := by norm_num
            _ ≤ ENNReal.ofReal (Hm ω * (N + 1 : ℝ)) := by
                  exact ENNReal.ofReal_le_ofReal hmul
            _ = (N + 1 : ℝ≥0∞) * ENNReal.ofReal (Hm ω) := by
                  rw [ENNReal.ofReal_mul hω_nonneg]
                  have hcast : ENNReal.ofReal (N + 1 : ℝ) = (N + 1 : ℝ≥0∞) := by
                    simpa using (ENNReal.ofReal_natCast (N + 1))
                  rw [hcast, mul_comm]
    _ = (N + 1 : ℝ≥0∞) * ∫⁻ ω in s, ENNReal.ofReal (Hm ω) ∂μ := by
          simpa using
            (lintegral_const_mul' (μ := μ.restrict s) (r := (N + 1 : ℝ≥0∞))
              (f := fun ω ↦ ENNReal.ofReal (Hm ω)) (by simp))

/-- Helper for Exercise 6.2.1: on a null-measurable set where the density is bounded above by
`N + 1`, the weighted measure is controlled by the ambient measure. -/
theorem weightedMeasure_le_nat_mul_measure_of_upperBound
    (μ : Measure Ω) {Hm : Ω → ℝ} {s : Set Ω}
    (hs : NullMeasurableSet s μ) (N : ℕ)
    (h_upper : ∀ ω ∈ s, Hm ω < N + 1) :
    weightedMeasure μ Hm s ≤ (N + 1 : ℝ≥0∞) * μ s := by
  -- Proof comment: on `s`, the density itself is pointwise bounded by `N + 1`.
  rw [weightedMeasure, withDensity_apply₀ (μ := μ) (f := fun ω ↦ ENNReal.ofReal (Hm ω)) hs]
  calc
    ∫⁻ ω in s, ENNReal.ofReal (Hm ω) ∂μ ≤ ∫⁻ ω in s, (N + 1 : ℝ≥0∞) ∂μ := by
          refine lintegral_mono_ae ?_
          refine (ae_restrict_iff'₀ hs).2 <| Filter.Eventually.of_forall fun ω hω ↦ ?_
          calc
            ENNReal.ofReal (Hm ω) ≤ ENNReal.ofReal (N + 1 : ℝ) := by
              exact ENNReal.ofReal_le_ofReal (le_of_lt (h_upper ω hω))
            _ = (N + 1 : ℝ≥0∞) := by simpa using (ENNReal.ofReal_natCast (N + 1))
    _ = (N + 1 : ℝ≥0∞) * μ s := by simp

/-- Helper for Exercise 6.2.1: on a finite-measure set, the part where the density representative
is very small has vanishing `μ`-measure. -/
theorem tendsto_measure_smallDensityTail_zero
    (μ : Measure Ω) {Hm : Ω → ℝ} (hHm_meas : Measurable Hm)
    (hHm_pos : ∀ᵐ ω ∂μ, 0 < Hm ω)
    {A : Set Ω} (hA : MeasurableSet A) (hA_fin : μ A < ∞) :
    Tendsto (fun N : ℕ ↦ μ (A ∩ {ω | Hm ω < (1 : ℝ) / (N + 1)})) atTop (𝓝 0) := by
  let s : ℕ → Set Ω := fun N ↦ A ∩ {ω | Hm ω < (1 : ℝ) / (N + 1)}
  have hs_null : ∀ N, NullMeasurableSet (s N) μ := by
    intro N
    exact (hA.inter (hHm_meas measurableSet_Iio)).nullMeasurableSet
  have hs_anti : Antitone s := by
    intro m n hmn ω hω
    refine ⟨hω.1, ?_⟩
    have hω_lt : Hm ω < (1 : ℝ) / (n + 1) := by
      simpa [s] using hω.2
    exact lt_of_lt_of_le hω_lt (Nat.one_div_le_one_div hmn)
  have h_inter :
      (⋂ N, s N) = A ∩ {ω | Hm ω ≤ 0} := by
    ext ω
    constructor
    · intro hω
      refine ⟨(Set.mem_iInter.1 hω 0).1, ?_⟩
      by_contra hpos
      have hω_pos : 0 < Hm ω := lt_of_not_ge hpos
      obtain ⟨N, hN⟩ := exists_nat_one_div_lt hω_pos
      have hωN : Hm ω < (1 : ℝ) / (N + 1) := by
        simpa [s] using (Set.mem_iInter.1 hω N).2
      exact not_lt_of_ge (le_of_lt hN) hωN
    · intro hω
      refine Set.mem_iInter.2 fun N ↦ ?_
      refine ⟨hω.1, ?_⟩
      have hpos : (0 : ℝ) < (1 : ℝ) / (N + 1) := by positivity
      exact lt_of_le_of_lt hω.2 hpos
  have h_nonpos_null : μ (A ∩ {ω | Hm ω ≤ 0}) = 0 := by
    have h_pos_set : ∀ᵐ ω ∂μ, ω ∈ {ω | 0 < Hm ω} := by
      simpa using hHm_pos
    have h_pos_compl : μ ({ω | 0 < Hm ω}ᶜ) = 0 := by
      exact ae_iff.1 h_pos_set
    exact measure_mono_null (by intro ω hω; exact hω.2) <| by
      simpa [Set.compl_setOf, not_lt] using h_pos_compl
  have h_tendsto :=
    tendsto_measure_iInter_atTop (μ := μ) hs_null hs_anti
      ⟨0, ne_top_of_le_ne_top hA_fin.ne <| measure_mono (by intro ω hω; exact hω.1)⟩
  have h_tendsto' : Tendsto (fun N ↦ μ (s N)) atTop (𝓝 (μ (A ∩ {ω | Hm ω ≤ 0}))) := by
    simpa [Function.comp, h_inter] using h_tendsto
  simpa [s, h_nonpos_null] using h_tendsto'

/-- Helper for Exercise 6.2.1: the weighted measure of the two-sided cutoff tail tends to `0`. -/
theorem tendsto_weightedMeasure_twoSidedCutoffTail_zero
    (μ : Measure Ω) {Hm : Ω → ℝ} (hHm_meas : Measurable Hm)
    (hHm_int : Integrable Hm μ) :
    Tendsto
      (fun N : ℕ ↦
        weightedMeasure μ Hm
          ({ω | (1 : ℝ) / (N + 1) ≤ Hm ω ∧ Hm ω < N + 1}ᶜ))
      atTop (𝓝 0) := by
  let ν := weightedMeasure μ Hm
  letI : IsFiniteMeasure ν := isFiniteMeasure_withDensity_ofReal hHm_int.hasFiniteIntegral
  let s : ℕ → Set Ω := fun N ↦ {ω | (1 : ℝ) / (N + 1) ≤ Hm ω ∧ Hm ω < N + 1}ᶜ
  have hs_null : ∀ N, NullMeasurableSet (s N) ν := by
    intro N
    exact
      ((hHm_meas measurableSet_Ici).inter (hHm_meas measurableSet_Iio)).compl.nullMeasurableSet
  have hs_anti : Antitone s := by
    intro m n hmn ω hω
    intro hωm
    have h_lower_n : (1 : ℝ) / (n + 1) ≤ Hm ω := by
      exact le_trans (Nat.one_div_le_one_div hmn) hωm.1
    have h_upper_n : Hm ω < n + 1 := by
      exact lt_of_lt_of_le hωm.2 (by exact_mod_cast Nat.succ_le_succ hmn)
    have h_lower_n' : ((n : ℝ) + 1)⁻¹ ≤ Hm ω := by
      simpa [one_div] using h_lower_n
    exact hω <| by simpa [s, one_div] using ⟨h_lower_n', h_upper_n⟩
  have h_inter : (⋂ N, s N) = {ω | Hm ω ≤ 0} := by
    ext ω
    constructor
    · intro hω
      by_contra hpos
      have hω_pos : 0 < Hm ω := lt_of_not_ge hpos
      obtain ⟨N₁, hN₁⟩ := exists_nat_one_div_lt hω_pos
      obtain ⟨N₂, hN₂⟩ := exists_nat_gt (Hm ω)
      let N := max N₁ N₂
      have h_lower : (1 : ℝ) / (N + 1) ≤ Hm ω := by
        exact le_of_lt <| lt_of_le_of_lt (Nat.one_div_le_one_div (le_max_left _ _)) hN₁
      have h_upper : Hm ω < N + 1 := by
        calc
          Hm ω < N₂ := hN₂
          _ < N + 1 := by
            exact_mod_cast Nat.lt_succ_of_le (le_max_right N₁ N₂)
      exact (Set.mem_iInter.1 hω N) ⟨h_lower, h_upper⟩
    · intro hω
      refine Set.mem_iInter.2 fun N ↦ ?_
      have hω_le : Hm ω ≤ 0 := by simpa using hω
      have hN_pos : (0 : ℝ) < (1 : ℝ) / (N + 1) := by positivity
      change ¬ (((1 : ℝ) / (N + 1) ≤ Hm ω) ∧ Hm ω < N + 1)
      intro hN
      exact not_le_of_gt (lt_of_le_of_lt hω_le hN_pos) hN.1
  have h_zero : ν {ω | Hm ω ≤ 0} = 0 := by
    change weightedMeasure μ Hm {ω | Hm ω ≤ 0} = 0
    rw [weightedMeasure, withDensity_apply_eq_zero hHm_meas.ennreal_ofReal]
    have h_empty : {x | 0 < Hm x} ∩ {ω | Hm ω ≤ 0} = ∅ := by
      ext ω
      simp
    simp [h_empty]
  have h_tendsto :=
    tendsto_measure_iInter_atTop (μ := ν) hs_null hs_anti
      ⟨0, ne_top_of_le_ne_top (measure_ne_top ν Set.univ) (measure_mono (by intro ω hω; simp))⟩
  have h_tendsto' : Tendsto (fun N ↦ ν (s N)) atTop (𝓝 (ν {ω | Hm ω ≤ 0})) := by
    simpa [Function.comp, h_inter] using h_tendsto
  simpa [s, h_zero] using h_tendsto'

/-- Helper for Exercise 6.2.1: on a fixed finite-measure set `A`, the local deviation measure is
controlled by the small-density tail in `A` plus the weighted deviation measure on the large-density
part of `A`. -/
theorem lowerCutoff_restrictDeviationReal_le_tail_add_weighted
    (μ : Measure Ω) {Hm : Ω → ℝ} (hHm_meas : Measurable Hm) (hHm_int : Integrable Hm μ)
    {A : Set Ω} (hA : MeasurableSet A) (hA_fin : μ A < ∞)
    {E : Type v} [MetricSpace E] [MeasurableSpace E] [BorelSpace E]
    {f g : Ω →ₘ[μ] E} {ε : ℝ} (N : ℕ) :
    (μ.restrict A).real {ω | ε ≤ dist (f ω) (g ω)}
      ≤ μ.real (A ∩ {ω | Hm ω < (1 : ℝ) / (N + 1)}) +
          (N + 1 : ℝ) * (weightedMeasure μ Hm).real {ω | ε ≤ dist (f ω) (g ω)} := by
  let ν := weightedMeasure μ Hm
  let dev : Set Ω := {ω | ε ≤ dist (f ω) (g ω)}
  let tail : Set Ω := A ∩ {ω | Hm ω < (1 : ℝ) / (N + 1)}
  let core : Set Ω := A ∩ dev ∩ {ω | (1 : ℝ) / (N + 1) ≤ Hm ω}
  letI : IsFiniteMeasure ν := isFiniteMeasure_withDensity_ofReal hHm_int.hasFiniteIntegral
  have h_dev_null : NullMeasurableSet dev μ := by
    -- Proof comment: the deviation set is null measurable because the pointwise distance is
    -- a.e.-measurable.
    have h_aemeas :
        AEMeasurable (fun ω ↦ dist (f ω) (g ω)) μ :=
      (f.aestronglyMeasurable.dist g.aestronglyMeasurable).aemeasurable
    simpa [dev] using
      h_aemeas.nullMeasurableSet_preimage measurableSet_Ici
  have h_dev_null_restrict : NullMeasurableSet dev (μ.restrict A) := by
    exact h_dev_null.mono_ac (Measure.absolutelyContinuous_of_le Measure.restrict_le_self)
  have h_tail_subset_A : tail ⊆ A := by
    intro ω hω
    exact hω.1
  have h_core_subset_A : core ⊆ A := by
    intro ω hω
    exact hω.1.1
  have h_union_subset_A : tail ∪ core ⊆ A := by
    intro ω hω
    rcases hω with hω | hω
    · exact h_tail_subset_A hω
    · exact h_core_subset_A hω
  have h_tail_ne_top : μ tail ≠ ∞ := by
    exact ne_top_of_le_ne_top hA_fin.ne <| measure_mono h_tail_subset_A
  have h_core_ne_top : μ core ≠ ∞ := by
    exact ne_top_of_le_ne_top hA_fin.ne <| measure_mono h_core_subset_A
  have h_union_ne_top : μ (tail ∪ core) ≠ ∞ := by
    exact ne_top_of_le_ne_top hA_fin.ne <| measure_mono h_union_subset_A
  have h_restrict :
      (μ.restrict A).real dev = μ.real (A ∩ dev) := by
    -- Proof comment: normalize the restricted real measure once so the main theorem can stay in
    -- its final local-measure form.
    simpa [Set.inter_comm] using measureReal_restrict_apply₀ h_dev_null_restrict
  have h_cover : A ∩ dev ⊆ tail ∪ core := by
    intro ω hω
    by_cases hsmall : Hm ω < (1 : ℝ) / (N + 1)
    · exact Or.inl ⟨hω.1, hsmall⟩
    · have hlarge : (1 : ℝ) / (N + 1) ≤ Hm ω := le_of_not_gt hsmall
      exact Or.inr ⟨⟨hω.1, hω.2⟩, hlarge⟩
  have h_core_null : NullMeasurableSet core μ := by
    exact ((hA.nullMeasurableSet.inter h_dev_null).inter
      (hHm_meas measurableSet_Ici).nullMeasurableSet)
  have h_core_weighted :
      μ.real core ≤ (N + 1 : ℝ) * ν.real core := by
    have h_core_enn :
        μ core ≤ (N + 1 : ℝ≥0∞) * ν core :=
      measure_le_nat_mul_weightedMeasure_of_lowerBound
        (μ := μ) (Hm := Hm) h_core_null N fun ω hω ↦ hω.2
    have h_rhs_ne_top : ((N + 1 : ℝ≥0∞) * ν core) ≠ ∞ := by
      exact ENNReal.mul_ne_top ENNReal.coe_ne_top (measure_ne_top ν core)
    calc
      μ.real core = (μ core).toReal := by rw [measureReal_def]
      _ ≤ (((N + 1 : ℝ≥0∞) * ν core)).toReal := by
            exact (ENNReal.toReal_le_toReal h_core_ne_top h_rhs_ne_top).2 h_core_enn
      _ = (N + 1 : ℝ) * ν.real core := by
        rw [ENNReal.toReal_mul]
        have hNatReal : ((N + 1 : ℝ≥0∞)).toReal = (N + 1 : ℝ) := by
          simpa using (ENNReal.toReal_natCast (N + 1))
        rw [hNatReal, measureReal_def]
  have h_core_mono :
      ν.real core ≤ ν.real dev := by
    refine measureReal_mono ?_ (measure_ne_top ν dev)
    intro ω hω
    exact hω.1.2
  -- Proof comment: split `A ∩ dev` into the small-density tail and the large-density core, then
  -- control the core by the weighted measure through the lower density bound.
  calc
    (μ.restrict A).real dev = μ.real (A ∩ dev) := h_restrict
    _ ≤ μ.real (tail ∪ core) := by
          exact measureReal_mono h_cover h_union_ne_top
    _ ≤ μ.real tail + μ.real core := measureReal_union_le _ _
    _ ≤ μ.real tail + (N + 1 : ℝ) * ν.real core := by
          gcongr
    _ ≤ μ.real tail + (N + 1 : ℝ) * ν.real dev := by
          gcongr
    _ = μ.real (A ∩ {ω | Hm ω < (1 : ℝ) / (N + 1)}) +
          (N + 1 : ℝ) * (weightedMeasure μ Hm).real {ω | ε ≤ dist (f ω) (g ω)} := by
          simp [ν, tail, dev]

/-- Helper for Exercise 6.2.1: the weighted deviation measure is controlled by the restriction to a
two-sided density cutoff together with the weighted cutoff tail. -/
theorem weightedDeviationReal_le_twoSidedCore_add_tail
    (μ : Measure Ω) {Hm : Ω → ℝ} (hHm_meas : Measurable Hm) (hHm_int : Integrable Hm μ)
    {E : Type v} [MetricSpace E] [MeasurableSpace E] [BorelSpace E]
    {f g : Ω →ₘ[μ] E} {ε : ℝ} (N : ℕ) :
    (weightedMeasure μ Hm).real {ω | ε ≤ dist (f ω) (g ω)}
      ≤ (N + 1 : ℝ) *
          (μ.restrict {ω | (1 : ℝ) / (N + 1) ≤ Hm ω ∧ Hm ω < N + 1}).real
            {ω | ε ≤ dist (f ω) (g ω)} +
          (weightedMeasure μ Hm).real
            ({ω | (1 : ℝ) / (N + 1) ≤ Hm ω ∧ Hm ω < N + 1}ᶜ) := by
  let ν := weightedMeasure μ Hm
  let B : Set Ω := {ω | (1 : ℝ) / (N + 1) ≤ Hm ω ∧ Hm ω < N + 1}
  let dev : Set Ω := {ω | ε ≤ dist (f ω) (g ω)}
  let core : Set Ω := B ∩ dev
  letI : IsFiniteMeasure ν := isFiniteMeasure_withDensity_ofReal hHm_int.hasFiniteIntegral
  have hB_meas : MeasurableSet B := by
    exact (hHm_meas measurableSet_Ici).inter (hHm_meas measurableSet_Iio)
  have hB_null : NullMeasurableSet B μ := hB_meas.nullMeasurableSet
  have h_dev_null : NullMeasurableSet dev μ := by
    -- Proof comment: as above, the deviation set is null measurable.
    have h_aemeas :
        AEMeasurable (fun ω ↦ dist (f ω) (g ω)) μ :=
      (f.aestronglyMeasurable.dist g.aestronglyMeasurable).aemeasurable
    simpa [dev] using
      h_aemeas.nullMeasurableSet_preimage measurableSet_Ici
  have h_core_null : NullMeasurableSet core μ := hB_null.inter h_dev_null
  have hB_finite : μ B < ∞ := by
    have hB_enn :
        μ B ≤ (N + 1 : ℝ≥0∞) * ν B :=
      measure_le_nat_mul_weightedMeasure_of_lowerBound
        (μ := μ) (Hm := Hm) hB_null N fun ω hω ↦ hω.1
    have h_rhs_lt_top : ((N + 1 : ℝ≥0∞) * ν B) < ∞ := by
      exact ENNReal.mul_lt_top ENNReal.coe_lt_top (measure_lt_top ν B)
    exact lt_of_le_of_lt hB_enn h_rhs_lt_top
  have h_core_restrict :
      (μ.restrict B).real dev = μ.real core := by
    have h_dev_null_restrict : NullMeasurableSet dev (μ.restrict B) := by
      exact h_dev_null.mono_ac (Measure.absolutelyContinuous_of_le Measure.restrict_le_self)
    -- Proof comment: normalize the finite restriction once so the theorem body can use local
    -- convergence on the cutoff set directly.
    simpa [B, core, Set.inter_assoc, Set.inter_comm, Set.inter_left_comm] using
      measureReal_restrict_apply₀ h_dev_null_restrict
  have h_core_weighted :
      ν.real core ≤ (N + 1 : ℝ) * (μ.restrict B).real dev := by
    have h_core_enn :
        ν core ≤ (N + 1 : ℝ≥0∞) * μ core :=
      weightedMeasure_le_nat_mul_measure_of_upperBound
        (μ := μ) (Hm := Hm) h_core_null N fun ω hω ↦ hω.1.2
    have h_core_ne_top : μ core ≠ ∞ := by
      exact ne_top_of_le_ne_top hB_finite.ne <| measure_mono fun ω hω ↦ hω.1
    have h_rhs_ne_top : ((N + 1 : ℝ≥0∞) * μ core) ≠ ∞ := by
      exact ENNReal.mul_ne_top ENNReal.coe_ne_top h_core_ne_top
    calc
      ν.real core = (ν core).toReal := by rw [measureReal_def]
      _ ≤ (((N + 1 : ℝ≥0∞) * μ core)).toReal := by
            exact (ENNReal.toReal_le_toReal (measure_ne_top ν core) h_rhs_ne_top).2 h_core_enn
      _ = (N + 1 : ℝ) * μ.real core := by
        rw [ENNReal.toReal_mul]
        have hNatReal : ((N + 1 : ℝ≥0∞)).toReal = (N + 1 : ℝ) := by
          simpa using (ENNReal.toReal_natCast (N + 1))
        rw [hNatReal, measureReal_def]
      _ = (N + 1 : ℝ) * (μ.restrict B).real dev := by rw [h_core_restrict]
  have h_cover : dev ⊆ core ∪ Bᶜ := by
    intro ω hω
    by_cases hωB : ω ∈ B
    · exact Or.inl ⟨hωB, hω⟩
    · exact Or.inr hωB
  -- Proof comment: split the weighted deviation set into the cutoff core and its weighted tail,
  -- then estimate the core by the ambient measure on the finite cutoff set.
  calc
    ν.real dev ≤ ν.real (core ∪ Bᶜ) := by
      exact measureReal_mono h_cover (measure_ne_top ν (core ∪ Bᶜ))
    _ ≤ ν.real core + ν.real Bᶜ := measureReal_union_le _ _
    _ ≤ (N + 1 : ℝ) * (μ.restrict B).real dev + ν.real Bᶜ := by
          gcongr
    _ = (N + 1 : ℝ) *
          (μ.restrict {ω | (1 : ℝ) / (N + 1) ≤ Hm ω ∧ Hm ω < N + 1}).real
            {ω | ε ≤ dist (f ω) (g ω)} +
          (weightedMeasure μ Hm).real
            ({ω | (1 : ℝ) / (N + 1) ≤ Hm ω ∧ Hm ω < N + 1}ᶜ) := by
          simp [ν, B, dev]

section PseudoMetric

variable {E : Type v} [PseudoMetricSpace E]
variable (μ : Measure Ω) (H : Ω → ℝ)

/-- Helper for Exercise 6.2.1: `weightedTruncDist μ H` is the truncated integral distance on
almost-everywhere measurable `E`-valued functions, computed with respect to the canonical
weighted measure `weightedMeasure μ H`. Integrability of `H` is used only in the
metric and convergence results below, where one needs the weighted measure to be finite. -/
def weightedTruncDist (f g : Ω →ₘ[μ] E) : ℝ :=
  ∫ ω, min (1 : ℝ) (dist (f ω) (g ω)) ∂ weightedMeasure μ H

/-- Helper for Exercise 6.2.1: the pointwise truncated distance is subadditive in every
pseudometric space. -/
theorem truncatedDist_triangle
    (x y z : E) :
    min (1 : ℝ) (dist x z) ≤ min (1 : ℝ) (dist x y) + min (1 : ℝ) (dist y z) := by
  -- The ambient pseudometric triangle inequality survives truncation by `min 1`.
  have hxy_nonneg : 0 ≤ dist x y := dist_nonneg
  have hyz_nonneg : 0 ≤ dist y z := dist_nonneg
  calc
    min (1 : ℝ) (dist x z) ≤ min (1 : ℝ) (dist x y + dist y z) := by
      gcongr
      exact dist_triangle _ _ _
    _ ≤ min (1 : ℝ) (dist x y) + min (1 : ℝ) (dist y z) := by
      by_cases hxy : dist x y ≤ 1
      · by_cases hyz : dist y z ≤ 1
        · rw [min_eq_right hxy, min_eq_right hyz]
          by_cases hsum : dist x y + dist y z ≤ 1
          · simp [min_eq_right hsum]
          · have hsum' : 1 ≤ dist x y + dist y z := le_of_not_ge hsum
            rw [min_eq_left hsum']
            linarith
        · have hyz' : 1 ≤ dist y z := le_of_not_ge hyz
          rw [min_eq_left hyz']
          have hleft : min (1 : ℝ) (dist x y + dist y z) ≤ 1 := min_le_left _ _
          have hright : 0 ≤ min (1 : ℝ) (dist x y) := le_min zero_le_one hxy_nonneg
          linarith
      · have hxy' : 1 ≤ dist x y := le_of_not_ge hxy
        rw [min_eq_left hxy']
        have hleft : min (1 : ℝ) (dist x y + dist y z) ≤ 1 := min_le_left _ _
        have hright : 0 ≤ min (1 : ℝ) (dist y z) := le_min zero_le_one hyz_nonneg
        linarith

/-- Helper for Exercise 6.2.1: when `H` is integrable, the truncated distance integrand is
integrable for the weighted measure `weightedMeasure μ H`. -/
theorem weightedTruncDistIntegrable
    (hH_int : Integrable H μ) (f g : Ω →ₘ[μ] E) :
    Integrable (fun ω ↦ min (1 : ℝ) (dist (f ω) (g ω))) (weightedMeasure μ H) := by
  let ν := weightedMeasure μ H
  letI : IsFiniteMeasure ν := isFiniteMeasure_withDensity_ofReal hH_int.hasFiniteIntegral
  have hf : AEStronglyMeasurable f ν := by
    -- The weighted measure is absolutely continuous with respect to `μ`.
    exact AEStronglyMeasurable.mono_ac
      (withDensity_absolutelyContinuous μ (fun ω ↦ ENNReal.ofReal (H ω)))
      f.aestronglyMeasurable
  have hg : AEStronglyMeasurable g ν := by
    -- The same absolute-continuity transfer applies to the second argument.
    exact AEStronglyMeasurable.mono_ac
      (withDensity_absolutelyContinuous μ (fun ω ↦ ENNReal.ofReal (H ω)))
      g.aestronglyMeasurable
  have h_meas :
      AEStronglyMeasurable (fun ω ↦ min (1 : ℝ) (dist (f ω) (g ω))) ν := by
    -- Truncating the pointwise distance preserves a.e.-strong measurability.
    exact (aemeasurable_const.min (hf.dist hg).aemeasurable).aestronglyMeasurable
  -- The integrand is bounded by the integrable constant `1` on the finite weighted measure space.
  refine Integrable.mono' (integrable_const (1 : ℝ)) h_meas ?_
  filter_upwards with ω
  have h_nonneg : 0 ≤ min (1 : ℝ) (dist (f ω) (g ω)) := by
    positivity
  have h_le : min (1 : ℝ) (dist (f ω) (g ω)) ≤ 1 := min_le_left _ _
  simp [Real.norm_of_nonneg h_nonneg, h_le]

/-- The weighted truncated distance from a function to itself is zero. -/
@[simp] theorem weightedTruncDist_self
    (f : Ω →ₘ[μ] E) :
    weightedTruncDist μ H f f = 0 := by
  -- The diagonal integrand vanishes pointwise.
  simp [weightedTruncDist]

/-- The weighted truncated distance is symmetric. -/
theorem weightedTruncDist_comm
    (f g : Ω →ₘ[μ] E) :
    weightedTruncDist μ H f g = weightedTruncDist μ H g f := by
  -- Symmetry comes from the ambient metric inside the integral.
  simp [weightedTruncDist, dist_comm]

/-- The weighted truncated distance satisfies the triangle inequality for an integrable
real-valued weight. -/
theorem weightedTruncDist_triangle
    (hH_int : Integrable H μ)
    (f g h : Ω →ₘ[μ] E) :
    weightedTruncDist μ H f h ≤
      weightedTruncDist μ H f g + weightedTruncDist μ H g h := by
  have h_int_fh := weightedTruncDistIntegrable μ H hH_int f h
  have h_int_fg := weightedTruncDistIntegrable μ H hH_int f g
  have h_int_gh := weightedTruncDistIntegrable μ H hH_int g h
  have h_int_sum :
      Integrable
        (fun ω ↦ min (1 : ℝ) (dist (f ω) (g ω)) + min (1 : ℝ) (dist (g ω) (h ω)))
        (weightedMeasure μ H) := by
    -- The sum of the two truncated-distance integrands is integrable termwise.
    exact h_int_fg.add h_int_gh
  have h_mono :
      ∫ ω, min (1 : ℝ) (dist (f ω) (h ω)) ∂ weightedMeasure μ H
        ≤
          ∫ ω,
            (min (1 : ℝ) (dist (f ω) (g ω)) + min (1 : ℝ) (dist (g ω) (h ω)))
            ∂ weightedMeasure μ H := by
    -- Integrate the pointwise triangle inequality for the truncated distance.
    exact integral_mono_ae h_int_fh h_int_sum <| Filter.Eventually.of_forall fun ω ↦
      truncatedDist_triangle (f ω) (g ω) (h ω)
  have h_add :
      ∫ ω,
          (min (1 : ℝ) (dist (f ω) (g ω)) + min (1 : ℝ) (dist (g ω) (h ω)))
          ∂ weightedMeasure μ H
        =
          weightedTruncDist μ H f g + weightedTruncDist μ H g h := by
    -- Split the integral of the sum into the sum of the two integrals.
    simpa [weightedTruncDist] using integral_add h_int_fg h_int_gh
  calc
    weightedTruncDist μ H f h
      = ∫ ω, min (1 : ℝ) (dist (f ω) (h ω)) ∂ weightedMeasure μ H := by
          rfl
    _ ≤
          ∫ ω,
            (min (1 : ℝ) (dist (f ω) (g ω)) + min (1 : ℝ) (dist (g ω) (h ω)))
            ∂ weightedMeasure μ H := h_mono
    _ = weightedTruncDist μ H f g + weightedTruncDist μ H g h := h_add

/-- For an integrable weight, `weightedTruncDist` defines the canonical pseudometric
structure on `Ω →ₘ[μ] E` attached to the weighted truncated integral distance. -/
@[reducible]
def weightedTruncPseudoMetricSpace
    (hH_int : Integrable H μ)
    : PseudoMetricSpace (Ω →ₘ[μ] E) where
  dist := weightedTruncDist μ H
  dist_self := weightedTruncDist_self μ H
  dist_comm := weightedTruncDist_comm μ H
  dist_triangle := weightedTruncDist_triangle μ H hH_int

end PseudoMetric

section Metric

variable {E : Type v} [MetricSpace E]
variable (μ : Measure Ω) (H : Ω → ℝ)

/-- An integrable weight that is strictly positive `μ`-almost everywhere separates
almost-everywhere classes. -/
@[simp] theorem weightedTruncDist_eq_zero_iff
    (hH_int : Integrable H μ) (hH_pos : ∀ᵐ ω ∂μ, 0 < H ω) {f g : Ω →ₘ[μ] E} :
    weightedTruncDist μ H f g = 0 ↔ f = g := by
  let ν := weightedMeasure μ H
  letI : IsFiniteMeasure ν := isFiniteMeasure_withDensity_ofReal hH_int.hasFiniteIntegral
  refine ⟨fun hfg ↦ ?_, fun hfg ↦ by simpa [hfg] using weightedTruncDist_self μ H f⟩
  have h_int := weightedTruncDistIntegrable μ H hH_int f g
  have h_nonneg :
      0 ≤ᵐ[ν] fun ω ↦ min (1 : ℝ) (dist (f ω) (g ω)) := by
    filter_upwards with ω
    positivity
  have h_zero_ae :
      (fun ω ↦ min (1 : ℝ) (dist (f ω) (g ω))) =ᵐ[ν] 0 := by
    -- A nonnegative integrable function with zero integral vanishes almost everywhere.
    exact (integral_eq_zero_iff_of_nonneg_ae h_nonneg h_int).mp <| by
      simpa [weightedTruncDist, ν] using hfg
  have h_eq_ae_ν : f =ᵐ[ν] g := by
    -- Vanishing truncated distance forces the pointwise distance to vanish almost everywhere.
    filter_upwards [h_zero_ae] with ω hω
    by_cases hdist : dist (f ω) (g ω) = 0
    · exact dist_eq_zero.mp hdist
    · have hdist_pos : 0 < dist (f ω) (g ω) := by
        exact lt_of_le_of_ne dist_nonneg (by simpa [eq_comm] using hdist)
      have hmin_pos : 0 < min (1 : ℝ) (dist (f ω) (g ω)) := by
        by_cases hle : dist (f ω) (g ω) ≤ 1
        · simpa [min_eq_right hle] using hdist_pos
        · have hone_le : 1 ≤ dist (f ω) (g ω) := le_of_not_ge hle
          have hmin_one : min (1 : ℝ) (dist (f ω) (g ω)) = 1 := by
            simp [min_eq_left hone_le]
          linarith [show (0 : ℝ) < 1 by norm_num]
      have hzero : min (1 : ℝ) (dist (f ω) (g ω)) = 0 := by
        simpa using hω
      linarith
  have h_pos_ne_zero :
      ∀ᵐ ω ∂μ, ENNReal.ofReal (H ω) ≠ 0 := by
    filter_upwards [hH_pos] with ω hω
    simpa [ENNReal.ofReal_ne_zero_iff] using hω
  have h_eq_ae_μ : f =ᵐ[μ] g := by
    -- Positivity of the density identifies `ν`-a.e. equality with `μ`-a.e. equality.
    exact
      (withDensity_ae_eq
        (μ := μ)
        (d := fun ω ↦ ENNReal.ofReal (H ω))
        hH_int.aestronglyMeasurable.aemeasurable.ennreal_ofReal
        h_pos_ne_zero).1 h_eq_ae_ν
  exact AEEqFun.ext h_eq_ae_μ

/-- The weighted truncated distance induces a metric structure on `Ω →ₘ[μ] E` once the weight is
integrable and strictly positive `μ`-almost everywhere. This is a named metric structure rather
than a global instance, since different choices of `H` give different metrics on the same type. -/
@[reducible]
def weightedTruncMetricSpace
    (hH_int : Integrable H μ)
    (hH_pos : ∀ᵐ ω ∂μ, 0 < H ω) :
    MetricSpace (Ω →ₘ[μ] E) where
  toPseudoMetricSpace := weightedTruncPseudoMetricSpace μ H hH_int
  eq_of_dist_eq_zero := fun hfg ↦ (weightedTruncDist_eq_zero_iff μ H hH_int hH_pos).1 hfg

end Metric

section MeasureTheoretic

variable {E : Type v} [MetricSpace E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace.SeparableSpace E]
variable (μ : Measure Ω) (H : Ω → ℝ)

/-- Helper for Exercise 6.2.1: a small weighted truncated distance forces the corresponding
deviation set to be small for the finite weighted measure. -/
theorem weightedTruncDist_deviationMeasure_le
    (hH_int : Integrable H μ) {f g : Ω →ₘ[μ] E} {ε : ℝ}
    (hε_pos : 0 < ε) (hε_le : ε ≤ 1) :
    (weightedMeasure μ H).real {ω | ε ≤ dist (f ω) (g ω)} ≤
      ε⁻¹ * weightedTruncDist μ H f g := by
  let ν := weightedMeasure μ H
  have h_int := weightedTruncDistIntegrable μ H hH_int f g
  have h_nonneg :
      0 ≤ᵐ[ν] fun ω ↦ min (1 : ℝ) (dist (f ω) (g ω)) := by
    -- Proof comment: the truncated distance integrand is pointwise nonnegative.
    filter_upwards with ω
    positivity
  have h_event :
      {ω | ε ≤ dist (f ω) (g ω)} =
        {ω | ε ≤ min (1 : ℝ) (dist (f ω) (g ω))} := by
    -- Proof comment: since `ε ≤ 1`, the threshold can be tested after truncating by `min 1`.
    ext ω
    constructor
    · intro hω
      exact le_min hε_le hω
    · intro hω
      exact le_trans hω (min_le_right (1 : ℝ) (dist (f ω) (g ω)))
  have h_mul :
      ε * ν.real {ω | ε ≤ dist (f ω) (g ω)} ≤ weightedTruncDist μ H f g := by
    -- Proof comment: Markov's inequality converts the integral control into a deviation bound.
    simpa [weightedTruncDist, ν, h_event] using
      (MeasureTheory.mul_meas_ge_le_integral_of_nonneg (μ := ν) h_nonneg h_int ε)
  have h_div :
      ν.real {ω | ε ≤ dist (f ω) (g ω)} ≤ weightedTruncDist μ H f g / ε := by
    -- Proof comment: divide the Markov estimate by the positive threshold `ε`.
    exact (le_div_iff₀ hε_pos).2 <| by
      simpa [mul_comm, mul_left_comm, mul_assoc] using h_mul
  simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using h_div

/-- Helper for Exercise 6.2.1: the weighted truncated distance is bounded by a deviation measure
plus a small deterministic error term. -/
theorem weightedTruncDist_le_deviation_add
    (hH_int : Integrable H μ) {f g : Ω →ₘ[μ] E} {η : ℝ}
    (hη_pos : 0 < η) (hη_le : η ≤ 1) :
    weightedTruncDist μ H f g ≤
      (weightedMeasure μ H).real {ω | η ≤ dist (f ω) (g ω)} +
        η * (weightedMeasure μ H).real Set.univ := by
  let ν := weightedMeasure μ H
  letI : IsFiniteMeasure ν := isFiniteMeasure_withDensity_ofReal hH_int.hasFiniteIntegral
  let dev : Set Ω := {ω | η ≤ dist (f ω) (g ω)}
  have h_int := weightedTruncDistIntegrable μ H hH_int f g
  have h_int_univ :
      IntegrableOn (fun ω ↦ min (1 : ℝ) (dist (f ω) (g ω))) Set.univ ν := by
    -- Proof comment: reinterpret the global integrability as integrability on the whole space.
    simpa [IntegrableOn] using h_int
  have hf : AEStronglyMeasurable f ν := by
    -- Proof comment: absolute continuity transfers a.e.-strong measurability from `μ` to `ν`.
    exact AEStronglyMeasurable.mono_ac
      (withDensity_absolutelyContinuous μ (fun ω ↦ ENNReal.ofReal (H ω)))
      f.aestronglyMeasurable
  have hg : AEStronglyMeasurable g ν := by
    -- Proof comment: the same transfer applies to the second function.
    exact AEStronglyMeasurable.mono_ac
      (withDensity_absolutelyContinuous μ (fun ω ↦ ENNReal.ofReal (H ω)))
      g.aestronglyMeasurable
  have h_dev_null : NullMeasurableSet dev ν := by
    -- Proof comment: the deviation set is null measurable because the distance is a.e.-measurable.
    simpa [dev] using
      ((hf.dist hg).aemeasurable.nullMeasurableSet_preimage measurableSet_Ici)
  have h_split := integral_inter_add_diff₀ h_dev_null h_int_univ
  have h_int_inter :
      IntegrableOn (fun ω ↦ min (1 : ℝ) (dist (f ω) (g ω))) (Set.univ ∩ dev) ν :=
    h_int_univ.mono_set (by
      intro ω hω
      simp)
  have h_int_diff :
      IntegrableOn (fun ω ↦ min (1 : ℝ) (dist (f ω) (g ω))) (Set.univ \ dev) ν :=
    h_int_univ.mono_set (by
      intro ω hω
      simp)
  have h_inter_le :
      ∫ ω in Set.univ ∩ dev, min (1 : ℝ) (dist (f ω) (g ω)) ∂ν ≤ ν.real dev := by
    -- Proof comment: on the deviation set, the truncated distance is bounded above by `1`.
    calc
      ∫ ω in Set.univ ∩ dev, min (1 : ℝ) (dist (f ω) (g ω)) ∂ν
        ≤ ∫ ω in Set.univ ∩ dev, (1 : ℝ) ∂ν := by
            exact
              setIntegral_mono_on₀ h_int_inter
                (integrableOn_const ((measure_lt_top ν (Set.univ ∩ dev)).ne))
                (MeasurableSet.univ.nullMeasurableSet.inter h_dev_null)
                (fun ω hω ↦ min_le_left _ _)
      _ = ν.real (Set.univ ∩ dev) := by
            rw [setIntegral_one_eq_measureReal]
      _ = ν.real dev := by simp
  have h_diff_le :
      ∫ ω in Set.univ \ dev, min (1 : ℝ) (dist (f ω) (g ω)) ∂ν ≤ η * ν.real Set.univ := by
    have h_aux :
        ∫ ω in Set.univ \ dev, min (1 : ℝ) (dist (f ω) (g ω)) ∂ν
          ≤ ∫ ω in Set.univ \ dev, η ∂ν := by
      -- Proof comment: off the deviation set, the ambient distance is `< η`, hence so is the
      -- truncated distance because `η ≤ 1`.
      exact
        setIntegral_mono_on₀ h_int_diff
          (integrableOn_const ((measure_lt_top ν (Set.univ \ dev)).ne))
          (MeasurableSet.univ.nullMeasurableSet.diff h_dev_null)
          (fun ω hω ↦ by
            have hω_not : ω ∉ dev := by
              simpa [Set.mem_diff, dev] using hω.2
            have hdist_lt : dist (f ω) (g ω) < η := by
              exact lt_of_not_ge hω_not
            calc
              min (1 : ℝ) (dist (f ω) (g ω)) ≤ dist (f ω) (g ω) := min_le_right _ _
              _ ≤ η := le_of_lt hdist_lt)
    calc
      ∫ ω in Set.univ \ dev, min (1 : ℝ) (dist (f ω) (g ω)) ∂ν
        ≤ ∫ ω in Set.univ \ dev, η ∂ν := h_aux
      _ = η * ν.real (Set.univ \ dev) := by
            rw [setIntegral_const]
            simp [smul_eq_mul, mul_comm]
      _ ≤ η * ν.real Set.univ := by
            have hmono : ν.real (Set.univ \ dev) ≤ ν.real Set.univ := by
              exact measureReal_mono (by intro ω hω; simp) (measure_lt_top ν Set.univ).ne
            exact mul_le_mul_of_nonneg_left hmono (le_of_lt hη_pos)
  -- Proof comment: split the integral into the deviation set and its complement and apply the
  -- two deterministic bounds.
  calc
    weightedTruncDist μ H f g
      = ∫ ω, min (1 : ℝ) (dist (f ω) (g ω)) ∂ weightedMeasure μ H := by
          rfl
    _ = ∫ ω in Set.univ, min (1 : ℝ) (dist (f ω) (g ω)) ∂ weightedMeasure μ H := by
          rw [Measure.restrict_univ]
    _ = ∫ ω in Set.univ, min (1 : ℝ) (dist (f ω) (g ω)) ∂ν := by
          rfl
    _ =
        ∫ ω in Set.univ ∩ dev, min (1 : ℝ) (dist (f ω) (g ω)) ∂ν +
          ∫ ω in Set.univ \ dev, min (1 : ℝ) (dist (f ω) (g ω)) ∂ν := by
            symm
            exact h_split
    _ ≤ ν.real dev + η * ν.real Set.univ := add_le_add h_inter_le h_diff_le
    _ = (weightedMeasure μ H).real {ω | η ≤ dist (f ω) (g ω)} +
          η * (weightedMeasure μ H).real Set.univ := by
            rfl

/-- Helper for Exercise 6.2.1: before comparing `weightedMeasure μ H` with local `μ`-measure,
the weighted truncated distance already matches convergence in measure for the finite weighted
measure on the same carrier `Ω →ₘ[μ] E`. -/
theorem tendsto_weightedTruncDist_iff_tendstoInMeasure_weightedMeasure
    (hH_int : Integrable H μ) {fSeq : ℕ → Ω →ₘ[μ] E} {f : Ω →ₘ[μ] E} :
    Tendsto (fun n ↦ weightedTruncDist μ H (fSeq n) f) atTop (𝓝 0) ↔
      TendstoInMeasure (weightedMeasure μ H) (fun n ω ↦ fSeq n ω) atTop f := by
  let ν := weightedMeasure μ H
  letI : IsFiniteMeasure ν := isFiniteMeasure_withDensity_ofReal hH_int.hasFiniteIntegral
  refine ⟨fun hdist ↦ ?_, fun h_meas ↦ ?_⟩
  · refine (tendstoInMeasure_iff_measureReal_dist).2 ?_
    intro ε hε
    let ε₀ : ℝ := min ε 1
    have hε₀_pos : 0 < ε₀ := by
      -- Proof comment: the weighted deviation estimate needs a threshold in `(0, 1]`.
      unfold ε₀
      exact lt_min hε (by norm_num)
    have hε₀_le : ε₀ ≤ 1 := by
      unfold ε₀
      exact min_le_right _ _
    have hε₀_le_ε : ε₀ ≤ ε := by
      unfold ε₀
      exact min_le_left _ _
    have hscaled :
        Tendsto (fun n ↦ ε₀⁻¹ * weightedTruncDist μ H (fSeq n) f) atTop (𝓝 0) := by
      -- Proof comment: the fixed threshold rescales the weighted distance without changing the
      -- limit `0`.
      simpa using (hdist.const_mul ε₀⁻¹)
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
      hscaled (fun _ ↦ measureReal_nonneg) ?_
    intro n
    have h_subset :
        {ω | ε ≤ dist (fSeq n ω) (f ω)} ⊆ {ω | ε₀ ≤ dist (fSeq n ω) (f ω)} := by
      -- Proof comment: passing from `ε` to `min ε 1` only enlarges the deviation set.
      intro ω hω
      exact le_trans hε₀_le_ε hω
    calc
      ν.real {ω | ε ≤ dist (fSeq n ω) (f ω)}
        ≤ ν.real {ω | ε₀ ≤ dist (fSeq n ω) (f ω)} := by
            exact measureReal_mono h_subset (measure_lt_top ν _).ne
      _ ≤ ε₀⁻¹ * weightedTruncDist μ H (fSeq n) f := by
            exact weightedTruncDist_deviationMeasure_le (μ := μ) (H := H) hH_int hε₀_pos hε₀_le
  · have h_meas_real := (tendstoInMeasure_iff_measureReal_dist.1 h_meas)
    refine Metric.tendsto_atTop.2 ?_
    intro δ hδ
    let mass : ℝ := ν.real Set.univ
    let η : ℝ := min 1 (δ / (2 * (mass + 1)))
    have hη_pos : 0 < η := by
      -- Proof comment: choose a threshold small enough to control the deterministic error term.
      unfold η
      refine lt_min (by norm_num) ?_
      positivity
    have hη_le : η ≤ 1 := by
      unfold η
      exact min_le_left _ _
    have hη_error_le : η * mass ≤ δ / 2 := by
      have hmass_nonneg : 0 ≤ mass := measureReal_nonneg
      have hmass_le : mass ≤ mass + 1 := by linarith
      have hη_upper : η ≤ δ / (2 * (mass + 1)) := by
        unfold η
        exact min_le_right _ _
      calc
        η * mass ≤ η * (mass + 1) := by
          gcongr
        _ ≤ (δ / (2 * (mass + 1))) * (mass + 1) := by
          gcongr
        _ = δ / 2 := by
          have hmass_one_pos : 0 < mass + 1 := by linarith
          field_simp [hmass_one_pos.ne']
    obtain ⟨N, hN⟩ := (Metric.tendsto_atTop.1 (h_meas_real η hη_pos)) (δ / 2) (by linarith)
    refine ⟨N, fun n hn ↦ ?_⟩
    have h_head :
        ν.real {ω | η ≤ dist (fSeq n ω) (f ω)} < δ / 2 := by
      have hdist : dist (ν.real {ω | η ≤ dist (fSeq n ω) (f ω)}) 0 < δ / 2 := hN n hn
      simpa [Real.dist_eq, abs_of_nonneg measureReal_nonneg] using hdist
    have h_bound :=
      weightedTruncDist_le_deviation_add (μ := μ) (H := H) hH_int
        (f := fSeq n) (g := f) hη_pos hη_le
    have h_dist_nonneg : 0 ≤ weightedTruncDist μ H (fSeq n) f := by
      -- Proof comment: the weighted truncated distance is an integral of a nonnegative function.
      rw [weightedTruncDist]
      exact integral_nonneg fun _ ↦ by positivity
    have h_lt :
        weightedTruncDist μ H (fSeq n) f < δ := by
      have h_lt_half :
          ν.real {ω | η ≤ dist (fSeq n ω) (f ω)} + η * mass < δ / 2 + δ / 2 := by
        exact add_lt_add_of_lt_of_le h_head hη_error_le
      have h_lt' :
          weightedTruncDist μ H (fSeq n) f < δ / 2 + δ / 2 := by
        exact lt_of_le_of_lt (by simpa [ν, mass] using h_bound) h_lt_half
      nlinarith
    have hdist_eq : dist (weightedTruncDist μ H (fSeq n) f) 0 = weightedTruncDist μ H (fSeq n) f := by
      rw [Real.dist_eq, sub_zero, abs_of_nonneg h_dist_nonneg]
    rw [hdist_eq]
    exact h_lt

/-- Helper for Exercise 6.2.1: convergence of the weighted truncated distance to `0` is equivalent to
convergence in `μ`-measure on every measurable set of finite `μ`-measure. -/
theorem tendsto_weightedTruncDist_iff_tendstoInMeasureOnFiniteMeasureSets
    (hH_int : Integrable H μ) (hH_pos : ∀ᵐ ω ∂μ, 0 < H ω)
    {fSeq : ℕ → Ω →ₘ[μ] E} {f : Ω →ₘ[μ] E} :
    Tendsto (fun n ↦ weightedTruncDist μ H (fSeq n) f) atTop (𝓝 0) ↔
      TendstoInMeasureOnFiniteMeasureSets μ (fun n ↦ fSeq n) f := by
  let Hm := hH_int.aestronglyMeasurable.mk H
  have hHm_meas : Measurable Hm := hH_int.aestronglyMeasurable.measurable_mk
  have hHm_int : Integrable Hm μ := by
    have hHm_eq : H =ᵐ[μ] Hm := by
      simpa [Hm] using hH_int.aestronglyMeasurable.ae_eq_mk
    exact hH_int.congr hHm_eq
  have hHm_pos : ∀ᵐ ω ∂μ, 0 < Hm ω := by
    simpa [Hm] using densityRepresentative_pos_ae μ hH_int hH_pos
  have h_weighted_eq : weightedMeasure μ H = weightedMeasure μ Hm := by
    simpa [Hm] using weightedMeasure_eq_densityRepresentative (μ := μ) hH_int
  -- Route correction: rather than transport the whole theorem body through repeated
  -- `Measure.restrict` and `.real` rewrites, rewrite once to the measurable density
  -- representative and use the two cutoff comparison lemmas as the only bridge.
  rw [tendsto_weightedTruncDist_iff_tendstoInMeasure_weightedMeasure (μ := μ) (H := H) hH_int]
  refine ⟨fun h_weighted ↦ ?_, fun h_local ↦ ?_⟩
  · have h_weightedHm : TendstoInMeasure (weightedMeasure μ Hm) (fun n ω ↦ fSeq n ω) atTop f := by
      simpa [h_weighted_eq] using h_weighted
    letI : IsFiniteMeasure (weightedMeasure μ Hm) :=
      isFiniteMeasure_withDensity_ofReal hHm_int.hasFiniteIntegral
    have h_weighted_real := (tendstoInMeasure_iff_measureReal_dist.1 h_weightedHm)
    rw [tendstoInMeasureOnFiniteMeasureSets_iff_forall_measurable]
    intro A hA hA_fin
    letI : IsFiniteMeasure (μ.restrict A) := isFiniteMeasure_restrict.2 hA_fin.ne
    refine (tendstoInMeasure_iff_measureReal_dist).2 ?_
    intro ε hε
    refine Metric.tendsto_atTop.2 ?_
    intro δ hδ
    have hδ_half : 0 < δ / 2 := by linarith
    have hδ_quarter : 0 < δ / 4 := by linarith
    have hδ_quarter_nonneg : 0 ≤ δ / 4 := le_of_lt hδ_quarter
    have h_tail_tendsto :
        Tendsto (fun N : ℕ ↦ μ (A ∩ {ω | Hm ω < (1 : ℝ) / (N + 1)})) atTop (𝓝 0) :=
      tendsto_measure_smallDensityTail_zero
        (μ := μ) (Hm := Hm) hHm_meas hHm_pos hA hA_fin
    rw [ENNReal.tendsto_atTop_zero] at h_tail_tendsto
    obtain ⟨N, hN⟩ :=
      h_tail_tendsto (ENNReal.ofReal (δ / 4)) (by positivity)
    have h_scaled :
        Tendsto
          (fun n ↦
            (N + 1 : ℝ) *
              (weightedMeasure μ Hm).real {ω | ε ≤ dist (fSeq n ω) (f ω)})
          atTop (𝓝 0) := by
      simpa using (h_weighted_real ε hε).const_mul (N + 1 : ℝ)
    obtain ⟨M, hM⟩ := (Metric.tendsto_atTop.1 h_scaled) (δ / 2) hδ_half
    refine ⟨max N M, fun n hn ↦ ?_⟩
    have h_tail_small :
        μ.real (A ∩ {ω | Hm ω < (1 : ℝ) / (N + 1)}) ≤ δ / 4 := by
      have h_tail_enn :
          μ (A ∩ {ω | Hm ω < (1 : ℝ) / (N + 1)}) ≤ ENNReal.ofReal (δ / 4) :=
        hN N le_rfl
      have h_tail_ne_top :
          μ (A ∩ {ω | Hm ω < (1 : ℝ) / (N + 1)}) ≠ ∞ := by
        exact ne_top_of_le_ne_top hA_fin.ne <| measure_mono fun ω hω ↦ hω.1
      have h_tail_real :
          μ.real (A ∩ {ω | Hm ω < (1 : ℝ) / (N + 1)}) ≤ (ENNReal.ofReal (δ / 4)).toReal := by
        exact (ENNReal.toReal_le_toReal h_tail_ne_top (by simp)).2 h_tail_enn
      simpa [ENNReal.toReal_ofReal hδ_quarter_nonneg] using h_tail_real
    have h_weighted_small :
        (N + 1 : ℝ) * (weightedMeasure μ Hm).real {ω | ε ≤ dist (fSeq n ω) (f ω)} < δ / 2 := by
      have hdist :
          dist
            ((N + 1 : ℝ) * (weightedMeasure μ Hm).real {ω | ε ≤ dist (fSeq n ω) (f ω)}) 0 <
            δ / 2 :=
        hM n (le_trans (le_max_right _ _) hn)
      have h_nonneg :
          0 ≤
            (N + 1 : ℝ) * (weightedMeasure μ Hm).real {ω | ε ≤ dist (fSeq n ω) (f ω)} := by
        positivity
      rw [Real.dist_eq, sub_zero, abs_of_nonneg h_nonneg] at hdist
      exact hdist
    have h_main :
        (μ.restrict A).real {ω | ε ≤ dist (fSeq n ω) (f ω)} < δ := by
      calc
        (μ.restrict A).real {ω | ε ≤ dist (fSeq n ω) (f ω)}
          ≤ μ.real (A ∩ {ω | Hm ω < (1 : ℝ) / (N + 1)}) +
              (N + 1 : ℝ) *
                (weightedMeasure μ Hm).real {ω | ε ≤ dist (fSeq n ω) (f ω)} := by
                exact lowerCutoff_restrictDeviationReal_le_tail_add_weighted
                  (μ := μ) (Hm := Hm) hHm_meas hHm_int hA hA_fin
                  (f := fSeq n) (g := f) (N := N)
        _ < δ / 4 + δ / 2 := add_lt_add_of_le_of_lt h_tail_small h_weighted_small
        _ < δ := by linarith
    rw [Real.dist_eq, sub_zero, abs_of_nonneg measureReal_nonneg]
    exact h_main
  · have h_local_meas := (tendstoInMeasureOnFiniteMeasureSets_iff_forall_measurable μ).1 h_local
    have h_weightedHm : TendstoInMeasure (weightedMeasure μ Hm) (fun n ω ↦ fSeq n ω) atTop f := by
      letI : IsFiniteMeasure (weightedMeasure μ Hm) :=
        isFiniteMeasure_withDensity_ofReal hHm_int.hasFiniteIntegral
      refine (tendstoInMeasure_iff_measureReal_dist).2 ?_
      intro ε hε
      refine Metric.tendsto_atTop.2 ?_
      intro δ hδ
      have hδ_half : 0 < δ / 2 := by linarith
      have hδ_quarter : 0 < δ / 4 := by linarith
      have hδ_quarter_nonneg : 0 ≤ δ / 4 := le_of_lt hδ_quarter
      have h_tail_tendsto :
          Tendsto
            (fun N : ℕ ↦
              (weightedMeasure μ Hm) ({ω | (1 : ℝ) / (N + 1) ≤ Hm ω ∧ Hm ω < N + 1}ᶜ))
            atTop (𝓝 0) :=
        tendsto_weightedMeasure_twoSidedCutoffTail_zero
          (μ := μ) (Hm := Hm) hHm_meas hHm_int
      rw [ENNReal.tendsto_atTop_zero] at h_tail_tendsto
      obtain ⟨N, hN⟩ :=
        h_tail_tendsto (ENNReal.ofReal (δ / 4)) (by positivity)
      let B : Set Ω := {ω | (1 : ℝ) / (N + 1) ≤ Hm ω ∧ Hm ω < N + 1}
      have hB_meas : MeasurableSet B := by
        exact (hHm_meas measurableSet_Ici).inter (hHm_meas measurableSet_Iio)
      have hB_finite : μ B < ∞ := by
        have hB_enn :
            μ B ≤ (N + 1 : ℝ≥0∞) * (weightedMeasure μ Hm) B :=
          measure_le_nat_mul_weightedMeasure_of_lowerBound
            (μ := μ) (Hm := Hm) hB_meas.nullMeasurableSet N fun ω hω ↦ hω.1
        have h_rhs_lt_top : ((N + 1 : ℝ≥0∞) * (weightedMeasure μ Hm) B) < ∞ := by
          exact ENNReal.mul_lt_top ENNReal.coe_lt_top (measure_lt_top (weightedMeasure μ Hm) B)
        exact lt_of_le_of_lt hB_enn h_rhs_lt_top
      letI : IsFiniteMeasure (μ.restrict B) := isFiniteMeasure_restrict.2 hB_finite.ne
      have h_localB : TendstoInMeasure (μ.restrict B) (fun n ω ↦ fSeq n ω) atTop f :=
        h_local_meas B hB_meas hB_finite
      have h_localB_real := (tendstoInMeasure_iff_measureReal_dist.1 h_localB)
      have h_scaled :
          Tendsto
            (fun n ↦
              (N + 1 : ℝ) *
                (μ.restrict B).real {ω | ε ≤ dist (fSeq n ω) (f ω)})
            atTop (𝓝 0) := by
        simpa using (h_localB_real ε hε).const_mul (N + 1 : ℝ)
      obtain ⟨M, hM⟩ := (Metric.tendsto_atTop.1 h_scaled) (δ / 2) hδ_half
      refine ⟨max N M, fun n hn ↦ ?_⟩
      have h_tail_small :
          (weightedMeasure μ Hm).real (Bᶜ) ≤ δ / 4 := by
        have h_tail_enn : (weightedMeasure μ Hm) (Bᶜ) ≤ ENNReal.ofReal (δ / 4) := by
          simpa [B] using hN N le_rfl
        have h_tail_real :
            (weightedMeasure μ Hm).real (Bᶜ) ≤ (ENNReal.ofReal (δ / 4)).toReal := by
          exact (ENNReal.toReal_le_toReal (measure_ne_top (weightedMeasure μ Hm) (Bᶜ)) (by simp)).2
            h_tail_enn
        simpa [ENNReal.toReal_ofReal hδ_quarter_nonneg] using h_tail_real
      have h_core_small :
          (N + 1 : ℝ) * (μ.restrict B).real {ω | ε ≤ dist (fSeq n ω) (f ω)} < δ / 2 := by
        have hdist :
            dist ((N + 1 : ℝ) * (μ.restrict B).real {ω | ε ≤ dist (fSeq n ω) (f ω)}) 0 <
              δ / 2 :=
          hM n (le_trans (le_max_right _ _) hn)
        have h_nonneg :
            0 ≤ (N + 1 : ℝ) * (μ.restrict B).real {ω | ε ≤ dist (fSeq n ω) (f ω)} := by
          positivity
        rw [Real.dist_eq, sub_zero, abs_of_nonneg h_nonneg] at hdist
        exact hdist
      have h_main :
          (weightedMeasure μ Hm).real {ω | ε ≤ dist (fSeq n ω) (f ω)} < δ := by
        calc
          (weightedMeasure μ Hm).real {ω | ε ≤ dist (fSeq n ω) (f ω)}
            ≤ (N + 1 : ℝ) * (μ.restrict B).real {ω | ε ≤ dist (fSeq n ω) (f ω)} +
                (weightedMeasure μ Hm).real (Bᶜ) := by
                  simpa [B] using
                    weightedDeviationReal_le_twoSidedCore_add_tail
                      (μ := μ) (Hm := Hm) hHm_meas hHm_int
                      (f := fSeq n) (g := f) (N := N)
          _ < δ / 2 + δ / 4 := add_lt_add_of_lt_of_le h_core_small h_tail_small
          _ < δ := by linarith
      rw [Real.dist_eq, sub_zero, abs_of_nonneg measureReal_nonneg]
      exact h_main
    simpa [h_weighted_eq] using h_weightedHm

/-- On a finite measure space, the weighted truncated distance also detects mathlib's canonical
global convergence-in-measure notion. -/
theorem tendsto_weightedTruncDist_iff_tendstoInMeasure
    [IsFiniteMeasure μ]
    (hH_int : Integrable H μ) (hH_pos : ∀ᵐ ω ∂μ, 0 < H ω)
    {fSeq : ℕ → Ω →ₘ[μ] E} {f : Ω →ₘ[μ] E} :
    Tendsto (fun n ↦ weightedTruncDist μ H (fSeq n) f) atTop (𝓝 0) ↔
      TendstoInMeasure μ (fun n ↦ fSeq n) atTop f := by
  -- On a finite measure space, the local textbook notion is exactly mathlib's global one.
  rw [tendsto_weightedTruncDist_iff_tendstoInMeasureOnFiniteMeasureSets (μ := μ) (H := H)
    hH_int hH_pos]
  exact tendstoInMeasureOnFiniteMeasureSets_iff_mathlib_tendstoInMeasure μ

/-- Helper for Exercise 6.2.1: a Cauchy sequence in the weighted truncated metric admits a strict
subsequence with geometrically small successive weighted distances. -/
private lemma exists_strictMono_subsequence_geometric_weightedTruncDist
    (hH_int : Integrable H μ) (hH_pos : ∀ᵐ ω ∂μ, 0 < H ω)
    {u : ℕ → Ω →ₘ[μ] E}
    (hu : ∀ ε > 0, ∃ N, ∀ m ≥ N, ∀ n ≥ N, weightedTruncDist μ H (u m) (u n) < ε) :
    ∃ ns : ℕ → ℕ, StrictMono ns ∧
      ∀ k, weightedTruncDist μ H (u (ns k)) (u (ns (k + 1))) < (1 / 4 : ℝ) ^ k := by
  letI : MetricSpace (Ω →ₘ[μ] E) := weightedTruncMetricSpace μ H hH_int hH_pos
  -- Proof comment: extract a subsequence whose future tail stays within the prescribed geometric
  -- bound, then evaluate that control at the next subsequence term.
  obtain ⟨ns, hns, hns_bound⟩ :=
    Metric.exists_subseq_bounded_of_cauchySeq
      u (Metric.cauchySeq_iff.2 hu) (fun k ↦ (1 / 4 : ℝ) ^ k) fun _ ↦ by positivity
  refine ⟨ns, hns, fun k ↦ ?_⟩
  have hstep :
      dist (u (ns (k + 1))) (u (ns k)) < (1 / 4 : ℝ) ^ k :=
    hns_bound k (ns (k + 1)) (hns.monotone (Nat.le_succ k))
  simpa [weightedTruncMetricSpace, weightedTruncPseudoMetricSpace, dist_comm] using hstep

/-- Helper for Exercise 6.2.1: geometric weighted-distance control converts into a summable bound
for the weighted bad sets where a subsequence jump exceeds the corresponding half-power
threshold. -/
private lemma weightedBadSet_le_geometric_of_fastSubsequence
    (hH_int : Integrable H μ)
    {u : ℕ → Ω →ₘ[μ] E} {ns : ℕ → ℕ}
    (hstep : ∀ k, weightedTruncDist μ H (u (ns k)) (u (ns (k + 1))) < (1 / 4 : ℝ) ^ k) :
    ∀ k,
      weightedMeasure μ H
          {ω | ((1 / 2 : ℝ) ^ k) ≤ dist (u (ns k) ω) (u (ns (k + 1)) ω)}
        ≤ ((1 / 2 : ℝ≥0∞) ^ k) := by
  intro k
  have hpow_ofReal :
      ENNReal.ofReal (((1 / 2 : ℝ) ^ k)) = (ENNReal.ofReal (1 / 2 : ℝ)) ^ k := by
    induction k with
    | zero =>
        simp
    | succ k ih =>
        rw [pow_succ, pow_succ, ENNReal.ofReal_mul (by positivity), ih]
  have hpow_ennreal : ENNReal.ofReal (((1 / 2 : ℝ) ^ k)) = ((1 / 2 : ℝ≥0∞) ^ k) := by
    simpa [one_div] using hpow_ofReal
  let ν := weightedMeasure μ H
  let bad : Set Ω := {ω | ((1 / 2 : ℝ) ^ k) ≤ dist (u (ns k) ω) (u (ns (k + 1)) ω)}
  letI : IsFiniteMeasure ν := isFiniteMeasure_withDensity_ofReal hH_int.hasFiniteIntegral
  have hε_pos : 0 < ((1 / 2 : ℝ) ^ k) := by
    positivity
  have hε_le : ((1 / 2 : ℝ) ^ k) ≤ 1 := by
    exact pow_le_one₀ (by positivity) (by norm_num)
  have hbad_real : ν.real bad ≤ ((1 / 2 : ℝ) ^ k) := by
    -- Proof comment: apply the weighted Markov estimate at threshold `(1 / 2)^k`, then use the
    -- quarter-power control on the weighted distance to recover the matching geometric bound.
    calc
      ν.real bad
        ≤ ((1 / 2 : ℝ) ^ k)⁻¹ * weightedTruncDist μ H (u (ns k)) (u (ns (k + 1))) := by
            simpa [ν, bad] using
              weightedTruncDist_deviationMeasure_le
                (μ := μ) (H := H) hH_int (f := u (ns k)) (g := u (ns (k + 1)))
                hε_pos hε_le
      _ ≤ ((1 / 2 : ℝ) ^ k)⁻¹ * (1 / 4 : ℝ) ^ k := by
            gcongr
            exact le_of_lt (hstep k)
      _ = ((1 / 2 : ℝ) ^ k) := by
            have hhalf_pow_pos : 0 < ((1 / 2 : ℝ) ^ k) := by positivity
            rw [show (1 / 4 : ℝ) ^ k = ((1 / 2 : ℝ) ^ k) * ((1 / 2 : ℝ) ^ k) by
                  rw [show (1 / 4 : ℝ) = (1 / 2 : ℝ) * (1 / 2 : ℝ) by norm_num, mul_pow],
              inv_eq_one_div]
            field_simp [hhalf_pow_pos.ne']
  have hbad_enn : ν bad ≤ ENNReal.ofReal (((1 / 2 : ℝ) ^ k)) := by
    rw [measureReal_def] at hbad_real
    exact (ENNReal.le_ofReal_iff_toReal_le (measure_ne_top ν bad) (by positivity)).2 hbad_real
  calc
    ν bad ≤ ENNReal.ofReal (((1 / 2 : ℝ) ^ k)) := hbad_enn
    _ = ((1 / 2 : ℝ≥0∞) ^ k) := hpow_ennreal

/-- Helper for Exercise 6.2.1: a fast weighted subsequence has a pointwise limit for
`weightedMeasure μ H`-almost every point. -/
private lemma ae_exists_limit_of_fastWeightedSubsequence [CompleteSpace E]
    (hH_int : Integrable H μ)
    {u : ℕ → Ω →ₘ[μ] E} {ns : ℕ → ℕ}
    (hstep : ∀ k, weightedTruncDist μ H (u (ns k)) (u (ns (k + 1))) < (1 / 4 : ℝ) ^ k) :
    ∀ᵐ ω ∂weightedMeasure μ H, ∃ l : E, Tendsto (fun k ↦ u (ns k) ω) atTop (𝓝 l) := by
  let ν := weightedMeasure μ H
  letI : IsFiniteMeasure ν := isFiniteMeasure_withDensity_ofReal hH_int.hasFiniteIntegral
  let bad : ℕ → Set Ω := fun k ↦
    {ω | ((1 / 2 : ℝ) ^ k) ≤ dist (u (ns k) ω) (u (ns (k + 1)) ω)}
  have hbad_le :
      ∀ k, ν (bad k) ≤ ((1 / 2 : ℝ≥0∞) ^ k) := by
    intro k
    change
      weightedMeasure μ H
          {ω | ((1 / 2 : ℝ) ^ k) ≤ dist (u (ns k) ω) (u (ns (k + 1)) ω)}
        ≤ ((1 / 2 : ℝ≥0∞) ^ k)
    exact
      weightedBadSet_le_geometric_of_fastSubsequence
        (μ := μ) (H := H) hH_int (u := u) (ns := ns) hstep k
  have hgeom_ne_top : ∑' k, ((1 / 2 : ℝ≥0∞) ^ k) ≠ ∞ := by
    have hratio : (1 / 2 : ℝ≥0∞) < 1 := by norm_num
    exact ((tsum_geometric_lt_top).2 hratio).ne
  have hbad_ne_top : ∑' k, ν (bad k) ≠ ∞ := by
    exact ne_top_of_le_ne_top hgeom_ne_top (ENNReal.tsum_le_tsum hbad_le)
  have h_bad_limsup : ν (limsup bad atTop) = 0 :=
    measure_limsup_atTop_eq_zero hbad_ne_top
  have h_exists_limit :
      ∀ ω ∈ (limsup bad atTop)ᶜ, ∃ l : E, Tendsto (fun k ↦ u (ns k) ω) atTop (𝓝 l) := by
    intro ω hω
    have h_eventually_not : ∀ᶠ k in atTop, ω ∉ bad k := by
      rw [Set.mem_compl_iff, mem_limsup_iff_frequently_mem, not_frequently] at hω
      exact hω
    rcases eventually_atTop.1 h_eventually_not with ⟨N, hN⟩
    let tail : ℕ → E := fun k ↦ u (ns (k + N)) ω
    have htail :
        ∀ k, dist (tail k) (tail (k + 1)) ≤ ((1 / 2 : ℝ) ^ (k + N)) := by
      intro k
      have hnot_mem : ω ∉ bad (N + k) := hN (N + k) (Nat.le_add_right N k)
      have hle :
          dist (u (ns (N + k)) ω) (u (ns (N + k + 1)) ω) < ((1 / 2 : ℝ) ^ (N + k)) := by
        exact lt_of_not_ge (by simpa [bad] using hnot_mem)
      exact le_of_lt <| by
        simpa [tail, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hle
    have htail_sum : Summable (fun k : ℕ ↦ ((1 / 2 : ℝ) ^ (k + N))) := by
      simpa using
        (_root_.summable_nat_add_iff (f := fun k : ℕ ↦ ((1 / 2 : ℝ) ^ k)) N).2
          summable_geometric_two
    have htail_cauchy : CauchySeq tail :=
      cauchySeq_of_dist_le_of_summable _ htail htail_sum
    obtain ⟨l, htail_tendsto⟩ := cauchySeq_tendsto_of_complete htail_cauchy
    refine ⟨l, ?_⟩
    -- Proof comment: the convergent shifted tail gives convergence of the whole subsequence after
    -- discarding finitely many initial terms.
    exact (tendsto_add_atTop_iff_nat (f := fun k ↦ u (ns k) ω) N).1 <| by
      simpa [tail, Function.comp, Nat.add_assoc] using htail_tendsto
  -- Proof comment: Borel-Cantelli shows that almost every point lies outside the limsup of the
  -- bad sets, so the pointwise geometric tail estimate yields a limit there.
  rw [ae_iff]
  refine measure_mono_null (fun ω hω ↦ ?_) h_bad_limsup
  rw [Set.mem_setOf_eq] at hω
  by_contra hlimsup
  exact hω (h_exists_limit ω hlimsup)

/-- Helper for Exercise 6.2.1: the fast weighted subsequence converges in local `μ`-measure to a
measurable almost-everywhere class. -/
private lemma tendstoInMeasureOnFiniteMeasureSets_subsequence_of_fastWeightedSubsequence
    [CompleteSpace E]
    (hH_int : Integrable H μ) (hH_pos : ∀ᵐ ω ∂μ, 0 < H ω)
    {u : ℕ → Ω →ₘ[μ] E} {ns : ℕ → ℕ}
    (hstep : ∀ k, weightedTruncDist μ H (u (ns k)) (u (ns (k + 1))) < (1 / 4 : ℝ) ^ k) :
    ∃ f : Ω →ₘ[μ] E, TendstoInMeasureOnFiniteMeasureSets μ (fun k ↦ u (ns k)) f := by
  have h_ae_exists_weighted :
      ∀ᵐ ω ∂weightedMeasure μ H, ∃ l : E, Tendsto (fun k ↦ u (ns k) ω) atTop (𝓝 l) :=
    ae_exists_limit_of_fastWeightedSubsequence
      (μ := μ) (H := H) hH_int (u := u) (ns := ns) hstep
  have h_pos_ne_zero :
      ∀ᵐ ω ∂μ, ENNReal.ofReal (H ω) ≠ 0 := by
    filter_upwards [hH_pos] with ω hω
    simpa [ENNReal.ofReal_ne_zero_iff] using hω
  have h_ae_exists :
      ∀ᵐ ω ∂μ, ∃ l : E, Tendsto (fun k ↦ u (ns k) ω) atTop (𝓝 l) := by
    have h_null_weighted :
        weightedMeasure μ H
          {ω | ¬ ∃ l : E, Tendsto (fun k ↦ u (ns k) ω) atTop (𝓝 l)} = 0 := by
      simpa [ae_iff] using h_ae_exists_weighted
    have h_null :
        μ {ω | ¬ ∃ l : E, Tendsto (fun k ↦ u (ns k) ω) atTop (𝓝 l)} = 0 := by
      exact
        (withDensity_absolutelyContinuous'
          hH_int.aestronglyMeasurable.aemeasurable.ennreal_ofReal h_pos_ne_zero)
          h_null_weighted
    simpa [ae_iff] using h_null
  obtain ⟨fLim, hfLim_sm, h_ae_tendsto⟩ :=
    exists_stronglyMeasurable_limit_of_tendsto_ae
      (fun k ↦ (u (ns k)).aestronglyMeasurable) h_ae_exists
  let f : Ω →ₘ[μ] E := AEEqFun.mk fLim hfLim_sm.aestronglyMeasurable
  have h_ae_tendsto_f :
      ∀ᵐ ω ∂μ, Tendsto (fun k ↦ u (ns k) ω) atTop (𝓝 (f ω)) := by
    -- Proof comment: replace the chosen strongly measurable representative by its `AEEqFun`
    -- class without changing the almost-everywhere pointwise limit.
    filter_upwards [h_ae_tendsto, AEEqFun.coeFn_mk fLim hfLim_sm.aestronglyMeasurable] with ω hω hω_eq
    simpa [f, hω_eq] using hω
  have h_subseq_local :
      TendstoInMeasureOnFiniteMeasureSets μ (fun k ↦ u (ns k)) f := by
    exact tendstoInMeasureOnFiniteMeasureSets_of_tendsto_ae μ
      (fun k ↦ (u (ns k)).aestronglyMeasurable) h_ae_tendsto_f
  exact ⟨f, h_subseq_local⟩

/-- Exercise 6.2.1 (ii): if `E` is complete, then the named metric space
`weightedTruncMetricSpace μ H hH_int hH_pos` is complete. -/
theorem weightedTruncMetricSpace_complete [CompleteSpace E]
    (hH_int : Integrable H μ) (hH_pos : ∀ᵐ ω ∂μ, 0 < H ω) :
    by
      letI : MetricSpace (Ω →ₘ[μ] E) := weightedTruncMetricSpace μ H hH_int hH_pos
      exact CompleteSpace (Ω →ₘ[μ] E) := by
  letI : MetricSpace (Ω →ₘ[μ] E) := weightedTruncMetricSpace μ H hH_int hH_pos
  -- Route correction: part (i) is now available, so the remaining completeness proof should
  -- extract a rapidly Cauchy subsequence in `weightedTruncDist`, prove that its weighted
  -- deviation events are summable, apply a direct Borel-Cantelli argument to obtain an a.e.
  -- pointwise limit for the subsequence, choose a measurable limit, and then upgrade subsequence
  -- convergence to full metric convergence via `tendsto_nhds_of_cauchySeq_of_subseq`.
  refine Metric.complete_of_cauchySeq_tendsto fun u hu ↦ ?_
  have hu_weighted :
      ∀ ε > 0, ∃ N, ∀ m ≥ N, ∀ n ≥ N, weightedTruncDist μ H (u m) (u n) < ε := by
    simpa [weightedTruncMetricSpace, weightedTruncPseudoMetricSpace] using (Metric.cauchySeq_iff.1 hu)
  obtain ⟨ns, hns, hstep⟩ :=
    exists_strictMono_subsequence_geometric_weightedTruncDist
      (μ := μ) (H := H) hH_int hH_pos hu_weighted
  obtain ⟨f, hsubseq_local⟩ :=
    tendstoInMeasureOnFiniteMeasureSets_subsequence_of_fastWeightedSubsequence
      (μ := μ) (H := H) hH_int hH_pos (u := u) (ns := ns) hstep
  have hdist_zero :
      Tendsto (fun k ↦ weightedTruncDist μ H (u (ns k)) f) atTop (𝓝 0) := by
    exact
      (tendsto_weightedTruncDist_iff_tendstoInMeasureOnFiniteMeasureSets
        (μ := μ) (H := H) hH_int hH_pos).2 hsubseq_local
  have hf : Tendsto (fun k ↦ u (ns k)) atTop (𝓝 f) := by
    refine (tendsto_iff_dist_tendsto_zero).2 ?_
    simpa [weightedTruncMetricSpace, weightedTruncPseudoMetricSpace] using hdist_zero
  -- Proof comment: once one strict subsequence converges, the original weighted-metric Cauchy
  -- sequence has the same limit.
  exact ⟨f, tendsto_nhds_of_cauchySeq_of_subseq hu hns.tendsto_atTop hf⟩

end MeasureTheoretic
