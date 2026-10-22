/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory
open Set
open scoped Topology unitInterval

universe u

variable {E : Type u} [MeasurableSpace E] [StandardBorelSpace E]
variable (μ : Measure E) [NoAtoms μ] {A : Set E} (n : ℕ+)

/-- Helper for Exercise 8.3.1: the cdf of an atom-free real probability measure is continuous. -/
lemma cdfContinuousOfNoAtoms (ρ : Measure ℝ) [NoAtoms ρ] [IsProbabilityMeasure ρ] :
    Continuous (ProbabilityTheory.cdf ρ) := by
  have hleft : ∀ x : ℝ, Function.leftLim (ProbabilityTheory.cdf ρ) x = ProbabilityTheory.cdf ρ x := by
    intro x
    -- Proof comment: atom-freeness makes the singleton jump vanish, so the left and right values
    -- of the monotone cdf coincide.
    have hmeasure : (ProbabilityTheory.cdf ρ).measure {x} = 0 := by
      rw [ProbabilityTheory.measure_cdf]
      simp
    have hmono := ProbabilityTheory.monotone_cdf ρ
    have hle :
        Function.leftLim (ProbabilityTheory.cdf ρ) x ≤ ProbabilityTheory.cdf ρ x :=
      hmono.leftLim_le le_rfl
    have hnonpos :
        ProbabilityTheory.cdf ρ x - Function.leftLim (ProbabilityTheory.cdf ρ) x ≤ 0 := by
      rwa [StieltjesFunction.measure_singleton, ENNReal.ofReal_eq_zero] at hmeasure
    linarith
  refine continuous_iff_continuousAt.2 ?_
  intro x
  -- Proof comment: monotone functions are continuous exactly when their left and right limits agree.
  have hmono := ProbabilityTheory.monotone_cdf ρ
  rw [hmono.continuousAt_iff_leftLim_eq_rightLim, hleft x, StieltjesFunction.rightLim_eq]

/-- Helper for Exercise 8.3.1: pushing an atom-free measure forward along a measurable embedding
preserves the no-atoms property. -/
lemma mapNoAtomsOfMeasurableEmbedding {α : Type*} {β : Type*} [MeasurableSpace α]
    [MeasurableSpace β] (ν : Measure α) [NoAtoms ν] {e : α → β} (he : MeasurableEmbedding e) :
    NoAtoms (ν.map e) where
  measure_singleton b := by
    -- A measurable embedding turns singleton fibers into subsingletons, so their measure stays `0`.
    rw [he.map_apply ν {b}]
    refine Set.Subsingleton.measure_zero ?_ ν
    intro x hx y hy
    have hx' : e x = b := by simpa using hx
    have hy' : e y = b := by simpa using hy
    exact he.injective (hx'.trans hy'.symm)

/-- Helper for Exercise 8.3.1: a measurable set of nonzero mass in an atom-free space is
uncountable. -/
lemma subtypeNotCountableOfMeasureNeZero (hA : MeasurableSet A) (hA0 : μ A ≠ 0) :
    ¬ Countable A := by
  -- A countable measurable set has zero mass under an atom-free measure.
  intro hcount
  exact hA0 (Set.Countable.measure_zero hcount μ)

/-- Helper for Exercise 8.3.1: for an atom-free probability measure on `unitInterval`, the
distribution function `x ↦ λ (Set.Icc 0 x)` is continuous. -/
lemma unitIntervalCdfContinuous (ρ : Measure unitInterval)
    [NoAtoms ρ] [IsProbabilityMeasure ρ] :
    Continuous fun x : unitInterval ↦ ProbabilityTheory.cdf (ρ.map Subtype.val) x := by
  -- Proof comment: push `ρ` forward to `ℝ` and reuse continuity of atom-free real cdfs.
  have he : MeasurableEmbedding (fun x : unitInterval ↦ (x : ℝ)) := by
    simpa using
      (MeasurableEmbedding.subtype_coe measurableSet_Icc :
        MeasurableEmbedding ((↑) : Set.Icc (0 : ℝ) 1 → ℝ))
  have hmap : NoAtoms (ρ.map Subtype.val) :=
    mapNoAtomsOfMeasurableEmbedding (ν := ρ) he
  letI : NoAtoms (ρ.map Subtype.val) := hmap
  letI : IsProbabilityMeasure (ρ.map Subtype.val) :=
    Measure.isProbabilityMeasure_map (by fun_prop)
  have hcont : Continuous (ProbabilityTheory.cdf (ρ.map Subtype.val)) :=
    cdfContinuousOfNoAtoms (ρ.map Subtype.val)
  simpa using hcont.comp continuous_subtype_val

/-- Helper for Exercise 8.3.1: an atom-free probability measure on `unitInterval` realizes every
target mass in `[0, 1]` as the measure of an initial segment `Set.Icc 0 x`. -/
lemma existsUnitIntervalInitialSegmentMeasureEq (ρ : Measure unitInterval)
    [NoAtoms ρ] [IsProbabilityMeasure ρ] {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r ≤ 1) :
    ∃ x : unitInterval, ρ (Set.Icc 0 x) = ENNReal.ofReal r := by
  let ν : Measure ℝ := ρ.map Subtype.val
  have he : MeasurableEmbedding (fun x : unitInterval ↦ (x : ℝ)) := by
    simpa using
      (MeasurableEmbedding.subtype_coe measurableSet_Icc :
        MeasurableEmbedding ((↑) : Set.Icc (0 : ℝ) 1 → ℝ))
  have hmap : NoAtoms ν :=
    mapNoAtomsOfMeasurableEmbedding (ν := ρ) he
  letI : NoAtoms ν := hmap
  letI : IsProbabilityMeasure ν := Measure.isProbabilityMeasure_map (by fun_prop)
  have hcont : Continuous (ProbabilityTheory.cdf ν) := cdfContinuousOfNoAtoms ν
  have hzero : ProbabilityTheory.cdf ν 0 = 0 := by
    -- Proof comment: the left endpoint contributes only the singleton `{0}`, which has zero mass.
    calc
      ProbabilityTheory.cdf ν 0 = ρ.real ({0} : Set unitInterval) := by
        simpa [ν] using (ProbabilityTheory.unitInterval.cdf_eq_real (μ := ρ) (0 : unitInterval))
      _ = 0 := by
        rw [MeasureTheory.Measure.real_def]
        simp
  have hone : ProbabilityTheory.cdf ν 1 = 1 := by
    -- Proof comment: the full interval `Icc 0 1` is all of `unitInterval`.
    calc
      ProbabilityTheory.cdf ν 1 = ρ.real (Set.Icc 0 (1 : unitInterval)) := by
        simpa [ν] using (ProbabilityTheory.unitInterval.cdf_eq_real (μ := ρ) (1 : unitInterval))
      _ = 1 := by
        have hIcc : (Set.Icc 0 (1 : unitInterval) : Set unitInterval) = Set.univ := by
          ext x
          constructor
          · intro _
            simp
          · intro _
            exact ⟨x.2.1, x.2.2⟩
        rw [hIcc]
        simp [MeasureTheory.Measure.real_def]
  have hr_mem :
      r ∈ Set.Icc (ProbabilityTheory.cdf ν 0) (ProbabilityTheory.cdf ν 1) := by
    simpa [hzero, hone] using ⟨hr0, hr1⟩
  have hrange :
      r ∈ (ProbabilityTheory.cdf ν) '' Set.Icc (0 : ℝ) 1 := by
    exact intermediate_value_Icc zero_le_one hcont.continuousOn hr_mem
  rcases hrange with ⟨x, hxIcc, hxr⟩
  refine ⟨⟨x, hxIcc⟩, ?_⟩
  -- Proof comment: rewrite the cdf back to the measure of the initial segment in `unitInterval`.
  rw [← hxr, ProbabilityTheory.unitInterval.cdf_eq_real (μ := ρ) ⟨x, hxIcc⟩, MeasureTheory.Measure.real_def,
    ENNReal.ofReal_toReal]
  exact measure_ne_top ρ _

/-- Helper for Exercise 8.3.1: scaling an atom-free measure preserves the no-atoms property. -/
lemma smulNoAtoms {α : Type*} [MeasurableSpace α] (ν : Measure α) [NoAtoms ν] (c : ENNReal) :
    NoAtoms (c • ν) := by
  refine ⟨fun x ↦ ?_⟩
  -- Singleton fibers still have zero mass after scalar multiplication.
  simp [Measure.smul_apply, measure_singleton x]

/-- Helper for Exercise 8.3.1: normalizing `μ.restrict A` rewrites its mass on measurable sets as
division by `μ A`. -/
lemma normalizeRestrict_apply_eq_div
    [Nonempty E] (hA : MeasurableSet A) (hA0 : μ A ≠ 0) (hA_top : μ A ≠ ⊤) {B : Set E} :
    let νA : FiniteMeasure E := by
      have hfin : IsFiniteMeasure (μ.restrict A) := by
        refine IsFiniteMeasure.mk ?_
        simpa [Measure.restrict_apply_univ, hA] using hA_top.lt_top
      exact ⟨μ.restrict A, hfin⟩
    νA.normalize.toFiniteMeasure B = μ (A ∩ B) / μ A := by
  let νA : FiniteMeasure E := by
    have hfin : IsFiniteMeasure (μ.restrict A) := by
      refine IsFiniteMeasure.mk ?_
      simpa [Measure.restrict_apply_univ, hA] using hA_top.lt_top
    exact ⟨μ.restrict A, hfin⟩
  have hνA0 : νA ≠ 0 := by
    intro hzero
    apply hA0
    -- Proof comment: if the normalized finite wrapper were zero, then its total mass `μ A`
    -- would already vanish.
    have hzero_univ : ((νA : Measure E) Set.univ) = 0 := by
      simpa using congrArg (fun ν : FiniteMeasure E ↦ ((ν : Measure E) Set.univ)) hzero
    simpa [νA, Measure.restrict_apply_univ, hA] using hzero_univ
  have hmeasure := FiniteMeasure.toMeasure_normalize_eq_of_nonzero νA hνA0
  have hnorm :
      νA.normalize.toFiniteMeasure B = (↑νA.mass : ENNReal)⁻¹ * (νA : Measure E) B := by
    -- Proof comment: evaluate the normalized-measure identity on the measurable set `B`.
    have hmass0 : νA.mass ≠ 0 := (FiniteMeasure.mass_nonzero_iff νA).2 hνA0
    have hnormMeasure :
        ((νA.normalize : ProbabilityMeasure E) : Measure E) B =
          (↑νA.mass : ENNReal)⁻¹ * (νA : Measure E) B := by
      have htmp := congrArg (fun ν : Measure E ↦ ν B) hmeasure
      simpa [Measure.smul_apply, ENNReal.coe_inv hmass0] using htmp
    simpa using hnormMeasure
  have hmass : (↑νA.mass : ENNReal) = μ A := by
    simpa [FiniteMeasure.ennreal_mass, νA, Measure.restrict_apply_univ, hA]
  have happly : (νA : Measure E) B = μ (A ∩ B) := by
    simpa [νA, Measure.restrict_apply' hA, Set.inter_comm]
  calc
    νA.normalize.toFiniteMeasure B = (↑νA.mass : ENNReal)⁻¹ * (νA : Measure E) B := hnorm
    _ = μ (A ∩ B) / μ A := by
      rw [hmass, happly, ENNReal.div_eq_inv_mul]

/-- Helper for Exercise 8.3.1: from a measurable set of finite mass, one can carve out a
measurable subset of any prescribed smaller mass. -/
lemma existsMeasurableSubset_measure_eq_of_ne_top
    (hA : MeasurableSet A) (hA_top : μ A ≠ ⊤) {r : ENNReal} (hr : r ≤ μ A) :
    ∃ B ⊆ A, MeasurableSet B ∧ μ B = r := by
  by_cases hA0 : μ A = 0
  · -- Proof comment: when `μ A = 0`, every admissible target mass is already `0`.
    have hr0 : r = 0 := by
      exact le_antisymm (by simpa [hA0] using hr) (zero_le _)
    refine ⟨∅, Set.empty_subset A, MeasurableSet.empty, ?_⟩
    simp [hr0]
  · have hA_nonempty : A.Nonempty := nonempty_of_measure_ne_zero hA0
    letI : Nonempty E := ⟨hA_nonempty.choose⟩
    let νA : FiniteMeasure E := by
      have hfin : IsFiniteMeasure (μ.restrict A) := by
        refine IsFiniteMeasure.mk ?_
        simpa [Measure.restrict_apply_univ, hA] using hA_top.lt_top
      exact ⟨μ.restrict A, hfin⟩
    let g : E → unitInterval := unitInterval.sigmoid ∘ embeddingReal E
    have hg : MeasurableEmbedding g := measurableEmbedding_sigmoid_comp_embeddingReal E
    have hnormNoAtoms : NoAtoms ((νA.normalize.toFiniteMeasure : FiniteMeasure E) : Measure E) := by
      refine NoAtoms.mk ?_
      intro x
      -- Proof comment: normalized singletons are still zero because the restriction stays atom-free.
      have hsingleton :
          ((νA.normalize.toFiniteMeasure : FiniteMeasure E) : Measure E) ({x} : Set E) =
            μ (A ∩ {x}) / μ A := by
        simpa [νA] using
          normalizeRestrict_apply_eq_div (μ := μ) (A := A) hA hA0 hA_top
            (B := ({x} : Set E))
      calc
        ((νA.normalize.toFiniteMeasure : FiniteMeasure E) : Measure E) ({x} : Set E) =
            μ (A ∩ {x}) / μ A := hsingleton
        _ = 0 := by
          have hsubset : A ∩ ({x} : Set E) ⊆ ({x} : Set E) := by
            intro y hy
            exact hy.2
          rw [ENNReal.div_eq_zero_iff]
          left
          exact measure_mono_null hsubset (measure_singleton x)
    letI : NoAtoms ((νA.normalize.toFiniteMeasure : FiniteMeasure E) : Measure E) := hnormNoAtoms
    letI : NoAtoms ((νA.normalize : ProbabilityMeasure E) : Measure E) := by
      simpa using hnormNoAtoms
    let ρ : Measure unitInterval := Measure.map g ((νA.normalize : ProbabilityMeasure E) : Measure E)
    letI : NoAtoms ρ := mapNoAtomsOfMeasurableEmbedding
      (ν := ((νA.normalize : ProbabilityMeasure E) : Measure E)) hg
    letI : IsProbabilityMeasure ρ := Measure.isProbabilityMeasure_map hg.measurable.aemeasurable
    have hr_top : r ≠ ⊤ := (lt_of_le_of_lt hr hA_top.lt_top).ne
    have hdiv_top : r / μ A ≠ ⊤ := ENNReal.div_ne_top hr_top hA0
    have hdiv_le_one : r / μ A ≤ 1 := by
      rw [ENNReal.div_le_iff hA0 hA_top]
      simpa using hr
    have hratio_nonneg : 0 ≤ (r / μ A).toReal := ENNReal.toReal_nonneg
    have hratio_le_one : (r / μ A).toReal ≤ 1 := by
      exact ENNReal.toReal_le_of_le_ofReal zero_le_one (by simpa using hdiv_le_one)
    obtain ⟨x, hx⟩ :=
      existsUnitIntervalInitialSegmentMeasureEq (ρ := ρ) hratio_nonneg hratio_le_one
    let B : Set E := A ∩ g ⁻¹' Set.Icc 0 x
    have hpre : MeasurableSet (g ⁻¹' Set.Icc 0 x) := hg.measurable measurableSet_Icc
    have hB_meas : MeasurableSet B := hA.inter hpre
    have hB_subset : B ⊆ A := Set.inter_subset_left
    have hmap_cut : μ B / μ A = r / μ A := by
      -- Proof comment: the chosen initial segment has exactly the target normalized mass, and the
      -- bridge lemma rewrites that normalized mass back in terms of `μ`.
      calc
        μ B / μ A = νA.normalize.toFiniteMeasure (g ⁻¹' Set.Icc 0 x) := by
          simpa [B, νA] using
            (normalizeRestrict_apply_eq_div (μ := μ) (A := A) hA hA0 hA_top
              (B := g ⁻¹' Set.Icc 0 x)).symm
        _ = ρ (Set.Icc 0 x) := by
          simpa [ρ] using (hg.map_apply ((νA.normalize : ProbabilityMeasure E) : Measure E)
            (Set.Icc 0 x)).symm
        _ = ENNReal.ofReal ((r / μ A).toReal) := hx
        _ = r / μ A := by rw [ENNReal.ofReal_toReal hdiv_top]
    have hB_mass : μ B = r := by
      -- Proof comment: cancel the common nonzero finite factor `μ A` from the normalized identity.
      have hmul := congrArg (fun z : ENNReal ↦ μ A * z) hmap_cut
      simpa [B, hA0, hA_top, ENNReal.mul_div_cancel, mul_comm, mul_left_comm, mul_assoc] using hmul
    exact ⟨B, hB_subset, hB_meas, hB_mass⟩

/-- Helper for Exercise 8.3.1: if `μ A = 0`, then the constant classifier already gives an
equal-mass partition. -/
lemma exists_measurable_fiber_partition_eq_of_noAtoms_of_measure_zero
    (hA : MeasurableSet A) (hA0 : μ A = 0) :
    ∃ f : E → Fin n, Measurable f ∧ ∀ i, μ.restrict A (f ⁻¹' {i}) = μ A / n := by
  refine ⟨fun _ ↦ 0, measurable_const, ?_⟩
  intro i
  by_cases hi : i = 0
  · -- The distinguished fiber is all of `A`, so its restricted mass is exactly `μ A = 0`.
    subst hi
    simp [Measure.restrict_apply' hA, hA0]
  · -- Every other fiber is empty because the classifier is constant.
    have hpre : (fun _ : E ↦ (0 : Fin n)) ⁻¹' ({i} : Set (Fin n)) = ∅ := by
      ext x
      simp [eq_comm, hi]
    simp [hpre, hA0]

/-- Helper for Exercise 8.3.1: if a measurable set `s` has finite mass `(m : ENNReal) * r`, then
it admits a measurable `Fin m`-classifier whose fibers all have restricted mass `r`. -/
lemma existsFiniteFiberPartitionOfMeasureEq
    {m : ℕ} (hm : 0 < m) {s : Set E} (hs : MeasurableSet s) (hs_top : μ s ≠ ⊤) {r : ENNReal}
    (hr : μ s = (m : ENNReal) * r) :
    ∃ f : E → Fin m, Measurable f ∧ ∀ i, μ.restrict s (f ⁻¹' {i}) = r := by
  revert hm s hs hs_top r hr
  refine Nat.strong_induction_on m ?_
  intro m ih hm s hs hs_top r hr
  rcases m with _ | m
  · cases hm
  rcases m with _ | k
  · refine ⟨fun _ ↦ 0, measurable_const, ?_⟩
    intro i
    fin_cases i
    -- For `Fin 1`, the unique fiber is all of `s`, so its mass is exactly `r`.
    calc
      μ.restrict s ((fun _ : E ↦ (0 : Fin 1)) ⁻¹' ({0} : Set (Fin 1))) = μ.restrict s Set.univ := by
        congr 1
        ext x
        simp
      _ = μ s := by
        rw [Measure.restrict_apply' hs]
        simp
      _ = r := by simpa using hr
  · have hm_ne_zero : (((k + 2 : ℕ) : ENNReal)) ≠ 0 := by
      exact_mod_cast Nat.succ_ne_zero (k + 1)
    have hr_top : r ≠ ⊤ := by
      intro hr_top
      apply hs_top
      calc
        μ s = (((k + 2 : ℕ) : ENNReal)) * r := hr
        _ = ⊤ := by simp [hr_top, hm_ne_zero]
    have hshare_le : r ≤ μ s := by
      have hone_le : (1 : ENNReal) ≤ (((k + 2 : ℕ) : ENNReal)) := by
        exact_mod_cast (show (1 : ℕ) ≤ k + 2 by omega)
      calc
        r = (1 : ENNReal) * r := by simp
        _ ≤ (((k + 2 : ℕ) : ENNReal)) * r := by
          gcongr
        _ = μ s := hr.symm
    obtain ⟨B, hB_subset, hB_meas, hBμ⟩ :=
      existsMeasurableSubset_measure_eq_of_ne_top (μ := μ) (A := s) hs hs_top hshare_le
    have hs_diff : MeasurableSet (s \ B) := hs.diff hB_meas
    have hmass_split :
        (((k + 2 : ℕ) : ENNReal)) * r = (((k + 1 : ℕ) : ENNReal)) * r + r := by
      have hcast : (((k + 2 : ℕ) : ENNReal)) = (((k + 1 : ℕ) : ENNReal) + 1) := by
        calc
          (((k + 2 : ℕ) : ENNReal)) = ((((k + 1) + 1 : ℕ) : ENNReal)) := by
            congr
          _ = (((k + 1 : ℕ) : ENNReal) + 1) := by
            norm_num
      calc
        (((k + 2 : ℕ) : ENNReal)) * r = ((((k + 1 : ℕ) : ENNReal) + 1) * r) := by
          rw [hcast]
        _ = (((k + 1 : ℕ) : ENNReal)) * r + 1 * r := by rw [add_mul]
        _ = (((k + 1 : ℕ) : ENNReal)) * r + r := by simp
    have hs_diff_mass : μ (s \ B) = ((k + 1 : ℕ) : ENNReal) * r := by
      -- Removing one `r`-piece leaves exactly `(k + 1)` many `r`-pieces.
      have hB_ne_top : μ B ≠ ⊤ := by
        rw [hBμ]
        exact hr_top
      calc
        μ (s \ B) = μ s - μ B := by
          rw [measure_diff hB_subset hB_meas.nullMeasurableSet hB_ne_top]
        _ = ((((k + 2 : ℕ) : ENNReal)) * r) - r := by rw [hr, hBμ]
        _ = ((((k + 1 : ℕ) : ENNReal)) * r + r) - r := by rw [hmass_split]
        _ = (((k + 1 : ℕ) : ENNReal)) * r := ENNReal.add_sub_cancel_right hr_top
    have hs_diff_top : μ (s \ B) ≠ ⊤ := by
      rw [hs_diff_mass]
      exact ENNReal.mul_ne_top (by simp) hr_top
    obtain ⟨g, hg_meas, hg_mass⟩ :=
      ih (k + 1) (Nat.lt_succ_self (k + 1)) (Nat.succ_pos _)
        (s := s \ B) hs_diff hs_diff_top (r := r) hs_diff_mass
    classical
    let f : E → Fin (k + 2) := fun x ↦ if x ∈ B then 0 else Fin.succ (g x)
    have hsucc_meas : Measurable fun x ↦ Fin.succ (g x) := by
      exact (measurable_of_finite (fun j : Fin (k + 1) => Fin.succ j)).comp hg_meas
    have hf_meas : Measurable f := by
      exact Measurable.ite hB_meas measurable_const hsucc_meas
    refine ⟨f, hf_meas, ?_⟩
    intro i
    refine Fin.cases ?_ ?_ i
    · -- The zero fiber is exactly the carved set `B`.
      calc
        μ.restrict s (f ⁻¹' ({0} : Set (Fin (k + 2)))) = μ.restrict s B := by
          congr 1
          ext x
          by_cases hx : x ∈ B
          · simp [f, hx]
          · have hsucc : Fin.succ (g x) ≠ (0 : Fin (k + 2)) := Fin.succ_ne_zero (g x)
            simp [f, hx, hsucc]
        _ = μ B := by
          rw [Measure.restrict_apply hB_meas]
          simp [Set.inter_eq_left.mpr hB_subset]
        _ = r := hBμ
    · intro j
      -- A successor fiber is the corresponding recursive fiber on the measurable remainder.
      calc
        μ.restrict s (f ⁻¹' ({Fin.succ j} : Set (Fin (k + 2)))) =
            μ.restrict s (Bᶜ ∩ g ⁻¹' ({j} : Set (Fin (k + 1)))) := by
          congr 1
          ext x
          by_cases hx : x ∈ B
          · have hsucc : (0 : Fin (k + 2)) ≠ Fin.succ j := by
              intro h
              exact Fin.succ_ne_zero j h.symm
            simp [f, hx, hsucc]
          · simp [f, hx]
        _ = μ.restrict (s \ B) (g ⁻¹' ({j} : Set (Fin (k + 1)))) := by
          rw [Measure.restrict_apply' hs, Measure.restrict_apply' hs_diff]
          congr 1
          ext x
          simp [Set.diff_eq, and_left_comm, and_assoc, and_comm]
        _ = r := hg_mass j

/-- Helper for Exercise 8.3.1: a sigma-finite infinite measure admits a subsequence of
`spanningSets μ` whose successive jumps all exceed a prescribed finite threshold. -/
lemma existsLargeBlockSubsequenceOfSigmaFiniteTop
    [SigmaFinite μ] (c : ENNReal) (hc0 : 0 < c) (hc_top : c < ⊤) (hμ_top : μ Set.univ = ⊤) :
    ∃ ψ : ℕ → ℕ, StrictMono ψ ∧
      c < μ (spanningSets μ (ψ 0)) ∧
      (∀ n, μ (spanningSets μ (ψ n)) + c < μ (spanningSets μ (ψ (n + 1)))) := by
  have hlarge : ∀ r : ENNReal, r < (⊤ : ENNReal) → ∃ n, r < μ (spanningSets μ n) := by
    intro r hr
    have hr_univ : r < μ Set.univ := by simpa [hμ_top] using hr
    rw [← Measure.iSup_restrict_spanningSets (μ := μ) Set.univ] at hr_univ
    rw [lt_iSup_iff] at hr_univ
    rcases hr_univ with ⟨n, hn⟩
    refine ⟨n, ?_⟩
    simpa [Measure.restrict_apply, measurableSet_spanningSets, Set.inter_univ] using hn
  have hnext :
      ∀ N : ℕ, ∃ n, N < n ∧ μ (spanningSets μ N) + c < μ (spanningSets μ n) := by
    intro N
    have htarget : μ (spanningSets μ N) + c < (⊤ : ENNReal) := by
      exact ENNReal.add_lt_top.2 ⟨measure_spanningSets_lt_top μ N, hc_top⟩
    rcases hlarge (μ (spanningSets μ N) + c) htarget with ⟨n, hn⟩
    have hgt : N < n := by
      by_contra hnot
      have hle : n ≤ N := Nat.not_lt.mp hnot
      have hmono : μ (spanningSets μ n) ≤ μ (spanningSets μ N) :=
        measure_mono (monotone_spanningSets μ hle)
      exact (not_lt_of_ge (hmono.trans (le_add_of_nonneg_right bot_le))) hn
    exact ⟨n, hgt, hn⟩
  choose φ hφgt hφmeasure using hnext
  let ψ : ℕ → ℕ := Nat.rec (φ 0) fun _ m => φ m
  have hψsucc : ∀ n, ψ n < ψ (n + 1) := by
    intro n
    -- Proof comment: each recursive application of `φ` jumps strictly forward.
    simpa [ψ] using hφgt (ψ n)
  have hψmono : StrictMono ψ := strictMono_nat_of_lt_succ hψsucc
  have hψzero_aux : μ (spanningSets μ 0) + c < μ (spanningSets μ (ψ 0)) := by
    -- Proof comment: the initial chosen index already satisfies the same jump estimate.
    simpa [ψ] using hφmeasure 0
  have hψzero : c < μ (spanningSets μ (ψ 0)) := by
    have hbase : c ≤ μ (spanningSets μ 0) + c := by
      simpa [add_comm] using
        (le_add_of_nonneg_left (show 0 ≤ μ (spanningSets μ 0) by exact bot_le) : c ≤ _)
    exact lt_of_le_of_lt hbase hψzero_aux
  refine ⟨ψ, hψmono, hψzero, ?_⟩
  intro n
  -- Proof comment: reapplying the same jump estimate at the previously chosen index gives the
  -- inductive growth along the subsequence.
  simpa [ψ] using hφmeasure (ψ n)

/-- Helper for Exercise 8.3.1: a sigma-finite infinite measure contains countably many pairwise
disjoint measurable finite-mass blocks whose measures all dominate a prescribed threshold. -/
lemma existsPairwiseDisjointLargeFiniteBlocksOfSigmaFiniteTop
    [SigmaFinite μ] (c : ENNReal) (hc0 : 0 < c) (hc_top : c < ⊤) (hμ_top : μ Set.univ = ⊤) :
    ∃ s : ℕ → Set E, Pairwise (fun i j ↦ Disjoint (s i) (s j)) ∧ (∀ n, MeasurableSet (s n)) ∧
      (∀ n, c ≤ μ (s n)) ∧ (∀ n, μ (s n) < ⊤) := by
  obtain ⟨ψ, hψmono, hψzero, hψstep⟩ :=
    existsLargeBlockSubsequenceOfSigmaFiniteTop (μ := μ) c hc0 hc_top hμ_top
  let F : ℕ → Set E := fun n ↦ spanningSets μ (ψ n)
  have hFmono : Monotone F := by
    intro m n hmn
    exact monotone_spanningSets μ (hψmono.monotone hmn)
  have hFmeas : ∀ n, MeasurableSet (F n) := by
    intro n
    simpa [F] using measurableSet_spanningSets (μ := μ) (ψ n)
  have hFpairwise : Pairwise (fun i j ↦ Disjoint (disjointed F i) (disjointed F j)) :=
    disjoint_disjointed F
  have hFfinite : ∀ n, μ (disjointed F n) < ⊤ := by
    intro n
    have htop : μ (F n) < ⊤ := by
      simpa [F] using measure_spanningSets_lt_top μ (ψ n)
    exact (measure_mono (disjointed_subset F n)).trans_lt htop
  have hFlarge : ∀ n, c ≤ μ (disjointed F n) := by
    intro n
    cases n with
    | zero =>
        -- Proof comment: the first disjoint block is the first chosen spanning set itself.
        simpa [F, disjointed_zero] using hψzero.le
    | succ n =>
        have hdisj : Disjoint (disjointed F (n + 1)) (F n) := by
          rw [show disjointed F n.succ = F n.succ \ F n by
            simpa using hFmono.disjointed_succ (i := n) (by exact not_isMax n)]
          refine Set.disjoint_left.2 ?_
          intro x hx hx'
          exact hx.2 hx'
        have hsplit : μ (F (n + 1)) = μ (disjointed F (n + 1)) + μ (F n) := by
          -- Proof comment: splitting the next stage into the old stage plus its new block
          -- turns the jump estimate into a lower bound on the block itself.
          have hsup : disjointed F (n + 1) ∪ F n = F (n + 1) := by
            simpa [Nat.succ_eq_add_one] using hFmono.disjointed_succ_sup n
          rw [← hsup, measure_union hdisj (hFmeas n)]
        have hstep : μ (F n) + c < μ (F (n + 1)) := by
          simpa [F] using hψstep n
        have hnot_lt : ¬ μ (disjointed F (n + 1)) < c := by
          intro hlt
          have hle : μ (disjointed F (n + 1)) + μ (F n) ≤ c + μ (F n) := by
            gcongr
          have : μ (F (n + 1)) ≤ μ (F n) + c := by
            calc
              μ (F (n + 1)) = μ (disjointed F (n + 1)) + μ (F n) := hsplit
              _ ≤ c + μ (F n) := hle
              _ = μ (F n) + c := by rw [add_comm]
          exact (not_lt_of_ge this) (by simpa [add_comm] using hstep)
        exact le_of_not_gt hnot_lt
  refine ⟨fun n ↦ disjointed F n, hFpairwise, fun n ↦ MeasurableSet.disjointed hFmeas n,
    hFlarge, hFfinite⟩

/-- Helper for Exercise 8.3.1: a sigma-finite infinite atom-free measure contains countably many
pairwise disjoint measurable sets of mass exactly `1`. -/
lemma existsPairwiseDisjointUnitMassSequenceOfSigmaFiniteTop
    [SigmaFinite μ] (hμ_top : μ Set.univ = ⊤) :
    ∃ s : ℕ → Set E, Pairwise (fun i j ↦ Disjoint (s i) (s j)) ∧ (∀ n, MeasurableSet (s n)) ∧
      (∀ n, μ (s n) = 1) := by
  obtain ⟨t, ht_disj, ht_meas, ht_large, ht_finite⟩ :=
    existsPairwiseDisjointLargeFiniteBlocksOfSigmaFiniteTop (μ := μ) (c := 1)
      zero_lt_one (by simp) hμ_top
  choose s hs_subset hs_meas hs_mass using fun n ↦
    existsMeasurableSubset_measure_eq_of_ne_top (μ := μ) (A := t n) (ht_meas n)
      (ht_finite n).ne (show (1 : ENNReal) ≤ μ (t n) from ht_large n)
  refine ⟨s, ?_, hs_meas, hs_mass⟩
  intro i j hij
  exact (ht_disj hij).mono (hs_subset i) (hs_subset j)

/-- Helper for Exercise 8.3.1: a sigma-finite atom-free measure of total mass `∞` admits a
measurable `Fin n`-classifier whose fibers all have mass `∞`. -/
lemma existsSigmaFiniteInfiniteFiberPartitionEqTop {m : ℕ+} [SigmaFinite μ]
    (hμ_top : μ Set.univ = ⊤) :
    ∃ f : E → Fin m, Measurable f ∧ ∀ i, μ (f ⁻¹' {i}) = ⊤ := by
  classical
  -- Route correction: the stable sigma-finite route is a measurable `Nat`-classifier on
  -- countably many disjoint unit-mass pieces, followed by reduction modulo `m`.
  obtain ⟨s, hs_disj, hs_meas, hs_mass⟩ :=
    existsPairwiseDisjointUnitMassSequenceOfSigmaFiniteTop (μ := μ) hμ_top
  let leftover : Set E := (⋃ n, s n)ᶜ
  have hleftover_meas : MeasurableSet leftover := (MeasurableSet.iUnion hs_meas).compl
  have hs_not_leftover : ∀ n, Disjoint (s n) leftover := by
    intro n
    exact (Set.subset_iUnion s n).disjoint_compl_right
  let witness : ∀ x, x ∉ leftover → ∃ n, x ∈ s n := by
    intro x hx
    have hx' : x ∈ ⋃ n, s n := by
      simpa [leftover] using hx
    simpa using Set.mem_iUnion.mp hx'
  let K : E → ℕ := fun x ↦
    if hx : x ∈ leftover then 0 else Nat.succ (Nat.find (witness x hx))
  have hK_zero : K ⁻¹' ({0} : Set ℕ) = leftover := by
    ext x
    by_cases hx : x ∈ leftover
    · simp [K, hx]
    · simp [K, hx]
  have hK_succ : ∀ n, K ⁻¹' ({n + 1} : Set ℕ) = s n := by
    intro n
    ext x
    constructor
    · intro hx
      by_cases hx_left : x ∈ leftover
      · have : (0 : ℕ) = n + 1 := by simpa [K, hx_left] using hx
        omega
      · have hfind_eq : Nat.find (witness x hx_left) = n := by
          have hx_eq : K x = n + 1 := by simpa using hx
          simpa [K, hx_left] using hx_eq
        simpa [hfind_eq] using Nat.find_spec (witness x hx_left)
    · intro hx
      have hx_left : x ∉ leftover := by
        intro hleft
        have : x ∈ ((s n) ∩ leftover : Set E) := ⟨hx, hleft⟩
        have hbot : ((s n) ∩ leftover : Set E) = ∅ := (hs_not_leftover n).eq_bot
        have hempty : x ∈ (∅ : Set E) := by rwa [hbot] at this
        exact hempty.elim
      have hfind_eq : Nat.find (witness x hx_left) = n := by
        have hfind_mem : x ∈ s (Nat.find (witness x hx_left)) := Nat.find_spec (witness x hx_left)
        by_contra hne
        have : x ∈ ((s (Nat.find (witness x hx_left))) ∩ s n : Set E) := ⟨hfind_mem, hx⟩
        have hbot : ((s (Nat.find (witness x hx_left))) ∩ s n : Set E) = ∅ := (hs_disj hne).eq_bot
        have hempty : x ∈ (∅ : Set E) := by rwa [hbot] at this
        exact hempty.elim
      simp [K, hx_left, hfind_eq]
  have hK_meas : Measurable K := by
    apply measurable_to_countable'
    intro k
    rcases k with _ | n
    · simpa [hK_zero] using hleftover_meas
    · simpa [hK_succ n] using hs_meas n
  let encode : ℕ → Fin m := fun
    | 0 => 0
    | n + 1 => ⟨n % m, Nat.mod_lt _ m.pos⟩
  have hencode_meas : Measurable encode := measurable_of_countable encode
  refine ⟨encode ∘ K, hencode_meas.comp hK_meas, ?_⟩
  intro i
  let stripe : ℕ → Set E := fun q ↦ s (i + q * m)
  have hstripe_disj : Pairwise (fun q r ↦ Disjoint (stripe q) (stripe r)) := by
    intro q r hqr
    exact hs_disj (by
      intro hEq
      apply hqr
      exact Nat.eq_of_mul_eq_mul_right m.pos (Nat.add_left_cancel hEq))
  have hstripe_meas : ∀ q, MeasurableSet (stripe q) := by
    intro q
    exact hs_meas (i + q * m)
  have hstripe_sub :
      (⋃ q, stripe q) ⊆ (encode ∘ K) ⁻¹' ({i} : Set (Fin m)) := by
    intro x hx
    rcases Set.mem_iUnion.mp hx with ⟨q, hq⟩
    have hKx : K x = i + q * m + 1 := by
      have hx' : x ∈ K ⁻¹' ({i + q * m + 1} : Set ℕ) := by
        rw [hK_succ (i + q * m)]
        simpa [stripe] using hq
      simpa using hx'
    have hmod : ((i + q * m) % m : ℕ) = i := by
      simpa [Nat.mod_eq_of_lt i.isLt] using Nat.add_mul_mod_self_left i q m
    simp [Function.comp, encode, hKx, hmod]
  have hstripe_top : μ (⋃ q, stripe q) = ⊤ := by
    have htsum : (∑' q : ℕ, (1 : ENNReal)) = ⊤ := by
      simpa using (ENNReal.tsum_const_eq_top_of_ne_zero (α := ℕ) one_ne_zero)
    calc
      μ (⋃ q, stripe q) = ∑' q, μ (stripe q) := measure_iUnion hstripe_disj hstripe_meas
      _ = (∑' q : ℕ, (1 : ENNReal)) := by simp [stripe, hs_mass]
      _ = ⊤ := htsum
  exact measure_mono_top hstripe_sub hstripe_top

/-- Helper for Exercise 8.3.1: the finite positive-mass branch is obtained by recursively carving
off measurable pieces of mass `μ A / n` from measurable remainders of `A`. -/
lemma exists_measurable_fiber_partition_eq_of_noAtoms_of_ne_top
    (hA : MeasurableSet A) (hA_top : μ A ≠ ⊤) :
    ∃ f : E → Fin n, Measurable f ∧ ∀ i, μ.restrict A (f ⁻¹' {i}) = μ A / n := by
  by_cases hA0 : μ A = 0
  · -- The finite branch still contains the degenerate zero-mass case, already handled above.
    exact exists_measurable_fiber_partition_eq_of_noAtoms_of_measure_zero μ n hA hA0
  -- Route correction: the bounded branch is handled directly by recursive exact cuts on
  -- measurable remainders, not by transporting to a one-dimensional model first.
  have hn_ne_zero : ((n : ℕ) : ENNReal) ≠ 0 := by
    exact_mod_cast n.ne_zero
  have hmass : μ A = (n : ENNReal) * (μ A / n) := by
    -- Choosing `r = μ A / n` matches the total finite mass of `A`.
    calc
      μ A = (μ A / n) * n := by
        rw [ENNReal.div_mul_cancel hn_ne_zero (by simp)]
      _ = (n : ENNReal) * (μ A / n) := by rw [mul_comm]
  obtain ⟨f, hf_meas, hf_mass⟩ :=
    existsFiniteFiberPartitionOfMeasureEq (μ := μ) (m := n) n.pos hA hA_top
      (r := μ A / n) hmass
  refine ⟨f, hf_meas, ?_⟩
  intro i
  simpa using hf_mass i

/-- Helper for Exercise 8.3.1: for an atom-free real measure, finite mass on a closed left ray is
equivalent to finite mass on the corresponding open left ray. -/
lemma measureIic_ltTop_iff_measureIio_ltTop (ρ : Measure ℝ) [NoAtoms ρ] (x : ℝ) :
    ρ (Set.Iic x) < ⊤ ↔ ρ (Set.Iio x) < ⊤ := by
  -- Proof comment: atom-freeness identifies the two restrictions because the boundary singleton
  -- carries zero mass.
  rw [← Measure.restrict_apply_univ (μ := ρ) (Set.Iic x),
    ← Measure.restrict_apply_univ (μ := ρ) (Set.Iio x), restrict_Iio_eq_restrict_Iic]

/-- Helper for Exercise 8.3.1: if every real cut has one finite side, then the measure is
`σ`-finite. -/
lemma sigmaFiniteOfFiniteSidedCuts (ρ : Measure ℝ) [NoAtoms ρ]
    (hside : ∀ x : ℝ, ρ (Set.Iio x) < ⊤ ∨ ρ (Set.Ioi x) < ⊤) : SigmaFinite ρ := by
  classical
  by_cases hallLeft : ∀ x : ℝ, ρ (Set.Iio x) < ⊤
  · let cover : Set (Set ℝ) := Set.range fun n : ℕ => Set.Iio (n : ℝ)
    have hcount : cover.Countable := Set.countable_range _
    have hfinite : ∀ s ∈ cover, ρ s < ⊤ := by
      intro s hs
      rcases hs with ⟨n, rfl⟩
      exact hallLeft n
    have hcover : ⋃₀ cover = Set.univ := by
      ext x
      constructor
      · intro _
        simp
      · intro _
        obtain ⟨n, hn⟩ := exists_nat_gt x
        exact Set.mem_sUnion.2 ⟨Set.Iio (n : ℝ), ⟨n, rfl⟩, hn⟩
    exact Measure.sigmaFinite_of_countable hcount hfinite hcover
  by_cases hallRight : ∀ x : ℝ, ρ (Set.Ioi x) < ⊤
  · let cover : Set (Set ℝ) := Set.range fun n : ℕ => Set.Ioi (-(n : ℝ))
    have hcount : cover.Countable := Set.countable_range _
    have hfinite : ∀ s ∈ cover, ρ s < ⊤ := by
      intro s hs
      rcases hs with ⟨n, rfl⟩
      exact hallRight (-(n : ℝ))
    have hcover : ⋃₀ cover = Set.univ := by
      ext x
      constructor
      · intro _
        simp
      · intro _
        obtain ⟨n, hn⟩ := exists_nat_gt (-x)
        have hmem : -(n : ℝ) < x := by linarith
        exact Set.mem_sUnion.2 ⟨Set.Ioi (-(n : ℝ)), ⟨n, rfl⟩, hmem⟩
    exact Measure.sigmaFinite_of_countable hcount hfinite hcover
  obtain ⟨xRight, hxRight⟩ := not_forall.mp hallLeft
  obtain ⟨xLeft, hxLeft⟩ := not_forall.mp hallRight
  let leftFinite : Set ℝ := {x : ℝ | ρ (Set.Iio x) < ⊤}
  have hleft_nonempty : leftFinite.Nonempty := by
    rcases hside xLeft with hx | hx
    · exact ⟨xLeft, hx⟩
    · exact (hxLeft hx).elim
  have hleft_bdd : BddAbove leftFinite := by
    refine ⟨xRight, ?_⟩
    intro y hy
    by_contra hyx
    have hyx' : xRight < y := lt_of_not_ge hyx
    have hsubset : Set.Iio xRight ⊆ Set.Iio y := by
      intro z hz
      exact lt_trans hz hyx'
    exact hxRight ((measure_mono hsubset).trans_lt hy)
  let c : ℝ := sSup leftFinite
  have hleft_of_lt : ∀ {x : ℝ}, x < c → ρ (Set.Iio x) < ⊤ := by
    intro x hx
    rcases (lt_csSup_iff hleft_bdd hleft_nonempty).1 (by simpa [c] using hx) with
      ⟨y, hy, hxy⟩
    have hsubset : Set.Iio x ⊆ Set.Iio y := by
      intro z hz
      exact lt_trans hz hxy
    exact (measure_mono hsubset).trans_lt hy
  have hright_of_gt : ∀ {x : ℝ}, c < x → ρ (Set.Ioi x) < ⊤ := by
    intro x hx
    have hx_not_mem : x ∉ leftFinite := by
      exact notMem_of_csSup_lt (by simpa [c] using hx) hleft_bdd
    exact (hside x).resolve_left hx_not_mem
  let leftSeq : ℕ → Set ℝ := fun n ↦ Set.Iio (c - 1 / ((n : ℝ) + 1))
  let rightSeq : ℕ → Set ℝ := fun n ↦ Set.Ioi (c + 1 / ((n : ℝ) + 1))
  let cover : Set (Set ℝ) :=
    Set.range leftSeq ∪ Set.range rightSeq ∪ Set.singleton ({c} : Set ℝ)
  have hcount : cover.Countable := by
    refine ((Set.countable_range leftSeq).union (Set.countable_range rightSeq)).union ?_
    exact (Set.finite_singleton ({c} : Set ℝ)).countable
  have hfinite : ∀ s ∈ cover, ρ s < ⊤ := by
    intro s hs
    rcases hs with hs | hs
    · rcases hs with ⟨n, rfl⟩ | ⟨n, rfl⟩
      · have hpos : 0 < (1 : ℝ) / ((n : ℝ) + 1) := by positivity
        exact hleft_of_lt (by linarith [hpos])
      · have hpos : 0 < (1 : ℝ) / ((n : ℝ) + 1) := by positivity
        exact hright_of_gt (by linarith [hpos])
    · rcases hs with rfl
      simpa [measure_singleton c]
  have hcover : ⋃₀ cover = Set.univ := by
    ext x
    constructor
    · intro _
      simp
    · intro _
      by_cases hxc : x < c
      · have hε : 0 < c - x := sub_pos.mpr hxc
        obtain ⟨n, hn⟩ := exists_nat_one_div_lt hε
        have hxmem : x < c - 1 / ((n : ℝ) + 1) := by linarith
        exact Set.mem_sUnion.2 ⟨leftSeq n, Or.inl (Or.inl ⟨n, rfl⟩), hxmem⟩
      · by_cases hcx : c < x
        · have hε : 0 < x - c := sub_pos.mpr hcx
          obtain ⟨n, hn⟩ := exists_nat_one_div_lt hε
          have hxmem : c + 1 / ((n : ℝ) + 1) < x := by linarith
          exact Set.mem_sUnion.2 ⟨rightSeq n, Or.inl (Or.inr ⟨n, rfl⟩), hxmem⟩
        · have hxeq : x = c := le_antisymm (not_lt.mp hcx) (not_lt.mp hxc)
          subst hxeq
          exact Set.mem_sUnion.2 ⟨({c} : Set ℝ), Or.inr rfl, by simp⟩
  exact Measure.sigmaFinite_of_countable hcount hfinite hcover

/-- Helper for Exercise 8.3.1: a non-`σ`-finite atom-free measure on a standard Borel space has
some real cut under `embeddingReal E` whose left and right pieces both have mass `∞`. -/
lemma existsRealCutWithInfiniteHalvesOfNotSigmaFinite (ν : Measure E) [NoAtoms ν]
    (hν : ¬ SigmaFinite ν) :
    ∃ x : ℝ,
      ν ((embeddingReal E) ⁻¹' Set.Iic x) = ⊤ ∧
      ν ((embeddingReal E) ⁻¹' Set.Ioi x) = ⊤ := by
  by_contra hcut
  let ρ : Measure ℝ := ν.map (embeddingReal E)
  letI : NoAtoms ρ :=
    mapNoAtomsOfMeasurableEmbedding (ν := ν) (measurableEmbedding_embeddingReal E)
  have hside : ∀ x : ℝ, ρ (Set.Iio x) < ⊤ ∨ ρ (Set.Ioi x) < ⊤ := by
    intro x
    -- Proof comment: if both sides were infinite at `x`, that would already be the forbidden cut.
    by_cases hleft : ν ((embeddingReal E) ⁻¹' Set.Iic x) = ⊤
    · right
      have hright : ν ((embeddingReal E) ⁻¹' Set.Ioi x) ≠ ⊤ := by
        intro hright
        exact hcut ⟨x, hleft, hright⟩
      simpa [ρ, Measure.map_apply (measurable_embeddingReal E) measurableSet_Ioi] using
        (Ne.lt_top hright)
    · left
      have hmapLeft : ρ (Set.Iic x) < ⊤ := by
        simpa [ρ, Measure.map_apply (measurable_embeddingReal E) measurableSet_Iic] using
          (Ne.lt_top hleft)
      exact (measureIic_ltTop_iff_measureIio_ltTop ρ x).1 hmapLeft
  have hσρ : SigmaFinite ρ := sigmaFiniteOfFiniteSidedCuts ρ hside
  exact hν (SigmaFinite.of_map ν (measurable_embeddingReal E).aemeasurable hσρ)

/-- Helper for Exercise 8.3.1: an infinite-mass measurable set contains a measurable subset whose
complement inside the set still has mass `∞`. -/
lemma existsMeasurableSubset_measure_eq_top_compl_eq_top
    (hA : MeasurableSet A) (hA_top : μ A = ⊤) :
    ∃ B ⊆ A, MeasurableSet B ∧ μ B = ⊤ ∧ μ (A \ B) = ⊤ := by
  let ν : Measure E := μ.restrict A
  have hν_top : ν Set.univ = ⊤ := by
    simpa [ν, hA_top] using (Measure.restrict_apply_univ (μ := μ) A)
  by_cases hσ : SigmaFinite ν
  · obtain ⟨f, hf, hmass⟩ :=
      existsSigmaFiniteInfiniteFiberPartitionEqTop (μ := ν) (m := (2 : ℕ+)) hν_top
    let B0 : Set E := f ⁻¹' ({0} : Set (Fin 2))
    let B : Set E := A ∩ B0
    have hB_subset : B ⊆ A := Set.inter_subset_left
    have hB_meas : MeasurableSet B := hA.inter (hf (measurableSet_singleton 0))
    have hB_top : μ B = ⊤ := by
      -- Proof comment: the `0`-fiber already has infinite mass for the restricted measure `ν`.
      simpa [ν, B, B0, Measure.restrict_apply' hA, Set.inter_assoc, Set.inter_left_comm,
        Set.inter_comm] using hmass 0
    have hB0_compl :
        B0ᶜ = f ⁻¹' ({1} : Set (Fin 2)) := by
      have hsingleton : ({0} : Set (Fin 2))ᶜ = ({1} : Set (Fin 2)) := by
        ext i
        fin_cases i <;> simp
      simpa [B0] using congrArg (fun s : Set (Fin 2) ↦ f ⁻¹' s) hsingleton
    have hdiff : A \ B = A ∩ B0ᶜ := by
      ext y
      constructor
      · intro hy
        refine ⟨hy.1, ?_⟩
        intro hyB0
        exact hy.2 ⟨hy.1, hyB0⟩
      · intro hy
        refine ⟨hy.1, ?_⟩
        intro hyB
        exact hy.2 hyB.2
    have hdiff_top : μ (A \ B) = ⊤ := by
      -- Proof comment: inside `A`, the complement of the `0`-fiber is exactly the `1`-fiber.
      rw [hdiff, hB0_compl]
      simpa [ν, B0, Measure.restrict_apply' hA, Set.inter_assoc, Set.inter_left_comm,
        Set.inter_comm] using hmass 1
    exact ⟨B, hB_subset, hB_meas, hB_top, hdiff_top⟩
  · let ν : Measure E := μ.restrict A
    obtain ⟨x, hxLeft, hxRight⟩ :=
      existsRealCutWithInfiniteHalvesOfNotSigmaFinite (ν := ν) hσ
    let B0 : Set E := (embeddingReal E) ⁻¹' Set.Iic x
    let B : Set E := A ∩ B0
    have hB_subset : B ⊆ A := Set.inter_subset_left
    have hB_meas : MeasurableSet B :=
      hA.inter ((measurable_embeddingReal E) measurableSet_Iic)
    have hB_top : μ B = ⊤ := by
      -- Proof comment: pull the infinite closed-half-line mass back through `embeddingReal`.
      simpa [ν, B, B0, Measure.restrict_apply' hA, Set.inter_assoc, Set.inter_left_comm,
        Set.inter_comm] using hxLeft
    have hB0_compl : B0ᶜ = (embeddingReal E) ⁻¹' Set.Ioi x := by
      ext y
      simp [B0]
    have hdiff : A \ B = A ∩ B0ᶜ := by
      ext y
      constructor
      · intro hy
        refine ⟨hy.1, ?_⟩
        intro hyB0
        exact hy.2 ⟨hy.1, hyB0⟩
      · intro hy
        refine ⟨hy.1, ?_⟩
        intro hyB
        exact hy.2 hyB.2
    have hdiff_top : μ (A \ B) = ⊤ := by
      -- Proof comment: the remainder inside `A` is the pulled-back open right ray.
      rw [hdiff, hB0_compl]
      simpa [ν, B0, Measure.restrict_apply' hA, Set.inter_assoc, Set.inter_left_comm,
        Set.inter_comm] using hxRight
    exact ⟨B, hB_subset, hB_meas, hB_top, hdiff_top⟩

/-- Helper for Exercise 8.3.1: an infinite-mass measurable set admits a measurable `Fin m`
classifier whose fibers all still have mass `∞`. -/
lemma existsInfiniteFiberPartitionOfMeasureEqTop
    {m : ℕ} (hm : 0 < m) {s : Set E} (hs : MeasurableSet s) (hs_top : μ s = ⊤) :
    ∃ f : E → Fin m, Measurable f ∧ ∀ i, μ.restrict s (f ⁻¹' {i}) = ⊤ := by
  revert hm s hs hs_top
  refine Nat.strong_induction_on m ?_
  intro m ih hm s hs hs_top
  rcases m with _ | m
  · cases hm
  rcases m with _ | k
  · refine ⟨fun _ ↦ 0, measurable_const, ?_⟩
    intro i
    fin_cases i
    rw [Measure.restrict_apply' hs]
    simp [hs_top]
  · obtain ⟨B, hB_subset, hB_meas, hB_top, hs_diff_top⟩ :=
      existsMeasurableSubset_measure_eq_top_compl_eq_top (μ := μ) (A := s) hs hs_top
    have hs_diff : MeasurableSet (s \ B) := hs.diff hB_meas
    obtain ⟨g, hg_meas, hg_mass⟩ :=
      ih (k + 1) (Nat.lt_succ_self (k + 1)) (Nat.succ_pos _)
        (s := s \ B) hs_diff hs_diff_top
    classical
    let f : E → Fin (k + 2) := fun x ↦ if x ∈ B then 0 else Fin.succ (g x)
    have hsucc_meas : Measurable fun x ↦ Fin.succ (g x) := by
      exact (measurable_of_finite (fun j : Fin (k + 1) => Fin.succ j)).comp hg_meas
    have hf_meas : Measurable f := by
      exact Measurable.ite hB_meas measurable_const hsucc_meas
    refine ⟨f, hf_meas, ?_⟩
    intro i
    refine Fin.cases ?_ ?_ i
    · -- The zero fiber is the carved measurable subset `B`, which already has mass `∞`.
      calc
        μ.restrict s (f ⁻¹' ({0} : Set (Fin (k + 2)))) = μ.restrict s B := by
          congr 1
          ext x
          by_cases hx : x ∈ B
          · simp [f, hx]
          · have hsucc : Fin.succ (g x) ≠ (0 : Fin (k + 2)) := Fin.succ_ne_zero (g x)
            simp [f, hx, hsucc]
        _ = μ B := by
          rw [Measure.restrict_apply hB_meas]
          simp [Set.inter_eq_left.mpr hB_subset]
        _ = ⊤ := hB_top
    · intro j
      -- Every successor fiber comes from the recursive partition of the infinite remainder.
      calc
        μ.restrict s (f ⁻¹' ({Fin.succ j} : Set (Fin (k + 2)))) =
            μ.restrict s (Bᶜ ∩ g ⁻¹' ({j} : Set (Fin (k + 1)))) := by
          congr 1
          ext x
          by_cases hx : x ∈ B
          · have hsucc : (0 : Fin (k + 2)) ≠ Fin.succ j := by
              intro h
              exact Fin.succ_ne_zero j h.symm
            simp [f, hx, hsucc]
          · simp [f, hx]
        _ = μ.restrict (s \ B) (g ⁻¹' ({j} : Set (Fin (k + 1)))) := by
          rw [Measure.restrict_apply' hs, Measure.restrict_apply' hs_diff]
          congr 1
          ext x
          simp [Set.diff_eq, and_left_comm, and_assoc, and_comm]
        _ = ⊤ := hg_mass j

/-- Helper for Exercise 8.3.1: the infinite-mass branch is obtained by recursively carving off
measurable pieces whose mass and complement mass are both `∞`. -/
lemma exists_measurable_fiber_partition_eq_of_noAtoms_of_eq_top
    (hA : MeasurableSet A) (hA_top : μ A = ⊤) :
    ∃ f : E → Fin n, Measurable f ∧ ∀ i, μ.restrict A (f ⁻¹' {i}) = μ A / n := by
  obtain ⟨f, hf_meas, hf_mass⟩ :=
    existsInfiniteFiberPartitionOfMeasureEqTop (μ := μ) (m := n) n.pos hA hA_top
  have htop_div : (⊤ : ENNReal) / n = ⊤ := by
    simpa using ENNReal.top_div_of_ne_top (show ((n : ENNReal)) ≠ ⊤ by simp)
  refine ⟨f, hf_meas, ?_⟩
  intro i
  rw [hA_top, htop_div]
  exact hf_mass i

/-- Exercise 8.3.1: In a standard Borel space with an atom-free measure, every measurable set
admits an equal-measure partition into `n` measurable pieces. A canonical library-facing
bridge/view is a measurable map `f : E → Fin n`; the pieces are its fibers measured with respect
to the restricted measure `μ.restrict A`. -/
-- Proof sketch: Embed the standard Borel space measurably into `ℝ`, transfer the restricted
-- measure on `A` to the image, cut the image into `n` measurable pieces of equal mass by
-- successive one-dimensional measure cuts, and pull the pieces back to `E`.
theorem exists_measurable_fiber_partition_eq_of_noAtoms
    (hA : MeasurableSet A) :
    ∃ f : E → Fin n, Measurable f ∧ ∀ i, μ.restrict A (f ⁻¹' {i}) = μ A / n := by
  by_cases hA0 : μ A = 0
  · -- Zero mass is the easy degenerate case: a constant classifier already works.
    exact exists_measurable_fiber_partition_eq_of_noAtoms_of_measure_zero μ n hA hA0
  · by_cases hA_top : μ A = ⊤
    · -- Route correction: the remaining hard case is genuinely the infinite-mass branch.
      exact exists_measurable_fiber_partition_eq_of_noAtoms_of_eq_top μ n hA hA_top
    · -- The remaining branch is finite positive mass, handled by recursive exact cuts on `A`.
      exact exists_measurable_fiber_partition_eq_of_noAtoms_of_ne_top μ n hA hA_top

/-- Exercise 8.3.1 in the source-text family-of-sets form: the equal-measure partition pieces may
be empty, so the public textbook-facing statement is an indexed family of measurable sets rather
than a `Finpartition`. -/
theorem exists_pairwiseDisjoint_iUnion_eq_measure_eq_of_noAtoms
    (hA : MeasurableSet A) :
    ∃ s : Fin n → Set E,
      (Pairwise fun i j ↦ Disjoint (s i) (s j)) ∧
      (∀ i, MeasurableSet (s i)) ∧
      (⋃ i, s i) = A ∧
      ∀ i, μ (s i) = μ A / n := by
  obtain ⟨f, hf, hμ⟩ := exists_measurable_fiber_partition_eq_of_noAtoms μ n hA
  refine ⟨fun i ↦ A ∩ f ⁻¹' {i}, ?_, ?_, ?_, ?_⟩
  · intro i j hij
    refine Set.disjoint_left.2 fun x hxi hxj ↦ ?_
    have hix : f x = i := by simpa using hxi.2
    have hjx : f x = j := by simpa using hxj.2
    exact hij (hix.symm.trans hjx)
  · intro i
    exact hA.inter (hf (measurableSet_singleton i))
  · ext x
    simp
  · intro i
    simpa [Measure.restrict_apply' hA, Set.inter_comm] using hμ i
