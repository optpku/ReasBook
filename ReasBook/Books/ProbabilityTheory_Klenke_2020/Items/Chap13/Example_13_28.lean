/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib
import Books.ProbabilityTheory_Klenke_2020.Items.Chap13.Definition_13_4
import Books.ProbabilityTheory_Klenke_2020.Items.Chap13.Definition_13_26

-- Declarations for this item will be appended below by the statement pipeline.

open Set MeasureTheory

open scoped ENNReal

universe u v

/-- Helper for Example 13.28: every compact subset of `ℝ` is contained in a centered closed
interval. -/
private lemma subset_Icc_neg_pos_of_isCompact {K : Set ℝ} (hK : IsCompact K) :
    ∃ R > 0, K ⊆ Set.Icc (-R) R := by
  -- Compact sets in `ℝ` are bounded, so a single norm bound controls both sides.
  obtain ⟨R, hRpos, hRbound⟩ := hK.isBounded.exists_pos_norm_le
  refine ⟨R, hRpos, ?_⟩
  intro x hx
  have hxabs : |x| ≤ R := by
    simpa [Real.norm_eq_abs] using hRbound x hx
  exact abs_le.mp hxabs

/-- Helper for Example 13.28: the complement of `[-R,R]` is the strict norm tail `{x | R < ‖x‖}`.
-/
private lemma compl_Icc_neg_eq_norm_gt {R : ℝ} (_hR : 0 ≤ R) :
    (Set.Icc (-R) R : Set ℝ)ᶜ = {x : ℝ | R < ‖x‖} := by
  ext x
  constructor
  · intro hx
    have hxIcc : x ∉ Set.Icc (-R) R := hx
    have hnot : ¬ |x| ≤ R := by
      intro hxabs
      exact hxIcc (abs_le.mp hxabs)
    exact by
      simpa [Real.norm_eq_abs] using lt_of_not_ge hnot
  · intro hx
    have hxnorm : R < |x| := by
      simpa [Real.norm_eq_abs] using hx
    have hxIcc : x ∉ Set.Icc (-R) R := by
      intro hxmem
      exact not_lt_of_ge (abs_le.mpr hxmem) hxnorm
    exact hxIcc

/-- Helper for Example 13.28: a uniform first-moment bound yields a small escape probability
outside a centered interval. -/
private lemma measure_centeredInterval_compl_lt_of_firstMomentBound
    (ν : ProbabilityMeasure ℝ) {C : ℝ≥0∞} (hC : C < ⊤)
    (hbound : ∫⁻ x, ENNReal.ofReal |x| ∂(ν : Measure ℝ) ≤ C)
    {ε : ℝ} (hε : 0 < ε) :
    (ν : Measure ℝ) (Set.Icc (-((C.toReal + 1) / ε)) ((C.toReal + 1) / ε))ᶜ <
      ENNReal.ofReal ε := by
  let R : ℝ := (C.toReal + 1) / ε
  have hRpos : 0 < R := by
    dsimp [R]
    positivity
  have hRnonzero : ENNReal.ofReal R ≠ 0 := by
    exact (ENNReal.ofReal_ne_zero_iff).2 hRpos
  have hmeas :
      AEMeasurable (fun x : ℝ ↦ ENNReal.ofReal |x|) (ν : Measure ℝ) := by
    -- The absolute-value control function is measurable.
    fun_prop
  have hmarkov :
      (ν : Measure ℝ) {x : ℝ | ENNReal.ofReal R ≤ ENNReal.ofReal |x|} ≤
        (∫⁻ x, ENNReal.ofReal |x| ∂(ν : Measure ℝ)) / ENNReal.ofReal R :=
    MeasureTheory.meas_ge_le_lintegral_div hmeas hRnonzero ENNReal.ofReal_ne_top
  have hcompl_le :
      (ν : Measure ℝ) (Set.Icc (-R) R)ᶜ ≤
        (ν : Measure ℝ) {x : ℝ | ENNReal.ofReal R ≤ ENNReal.ofReal |x|} := by
    refine measure_mono ?_
    intro x hx
    have hxnorm : R < ‖x‖ := by
      rw [compl_Icc_neg_eq_norm_gt hRpos.le] at hx
      exact hx
    change ENNReal.ofReal R ≤ ENNReal.ofReal |x|
    have hxle : R ≤ |x| := by
      simpa [Real.norm_eq_abs] using hxnorm.le
    exact ENNReal.ofReal_le_ofReal hxle
  have hbound' :
      ∫⁻ x, ENNReal.ofReal |x| ∂(ν : Measure ℝ) ≤ ENNReal.ofReal C.toReal := by
    simpa [ENNReal.ofReal_toReal hC.ne] using hbound
  have hdiv_lt :
      (∫⁻ x, ENNReal.ofReal |x| ∂(ν : Measure ℝ)) / ENNReal.ofReal R <
        ENNReal.ofReal ε := by
    have hstep :
        (∫⁻ x, ENNReal.ofReal |x| ∂(ν : Measure ℝ)) / ENNReal.ofReal R ≤
          ENNReal.ofReal C.toReal / ENNReal.ofReal R := by
      gcongr
    have hratio_lt : C.toReal / R < ε := by
      dsimp [R]
      have hεne : ε ≠ 0 := by linarith
      rw [div_lt_iff₀ hRpos]
      have hmul : ε * ((C.toReal + 1) / ε) = C.toReal + 1 := by
        field_simp [hεne]
      rw [hmul]
      linarith
    calc
      (∫⁻ x, ENNReal.ofReal |x| ∂(ν : Measure ℝ)) / ENNReal.ofReal R
          ≤ ENNReal.ofReal C.toReal / ENNReal.ofReal R := hstep
      _ = ENNReal.ofReal (C.toReal / R) := by
        rw [ENNReal.ofReal_div_of_pos hRpos]
      _ < ENNReal.ofReal ε := by
        exact (ENNReal.ofReal_lt_ofReal_iff hε).2 hratio_lt
  -- Combine the interval-complement inclusion with Markov's inequality.
  have hfinal := lt_of_le_of_lt (le_trans hcompl_le hmarkov) hdiv_lt
  simpa [R] using hfinal

/- Item (iv) lives in the tightness domain for laws on `ℝ`. The source-facing object is a family
of probability distributions, so the canonical owner abstraction is `ProbabilityMeasure ℝ`; the
raw measure view is derived via `ProbabilityMeasure.toMeasure`. -/
/-- Helper for Example 13.28: the normalized restriction of Lebesgue measure to `[-n,n]` is a
probability measure when `n ≠ 0`. -/
private lemma symmetricIntervalUniform_isProbabilityMeasure {n : ℕ} (hn : n ≠ 0) :
    IsProbabilityMeasure
      (ENNReal.ofReal (1 / (2 * n : ℝ)) • volume.restrict (Icc (-(n : ℝ)) n)) := by
  -- Compute the total mass of the normalized restriction measure on `[-n,n]`.
  rw [isProbabilityMeasure_iff]
  calc
    (ENNReal.ofReal (1 / (2 * n : ℝ)) • volume.restrict (Icc (-(n : ℝ)) n)) Set.univ
        = ENNReal.ofReal (1 / (2 * n : ℝ)) * volume (Icc (-(n : ℝ)) n) := by
            simp [Measure.smul_apply]
    _ = ENNReal.ofReal (1 / (2 * n : ℝ)) * ENNReal.ofReal ((n : ℝ) + n) := by
          simp [Real.volume_Icc]
    _ = ENNReal.ofReal ((1 / (2 * n : ℝ)) * ((n : ℝ) + n)) := by
          rw [← ENNReal.ofReal_mul]
          positivity
    _ = 1 := by
          have hnreal : (n : ℝ) ≠ 0 := by
            exact_mod_cast hn
          have hmul : (1 / (2 * n : ℝ)) * ((n : ℝ) + n) = 1 := by
            field_simp [hnreal]
            ring
          rw [hmul]
          norm_num

/-- The uniform probability law on the symmetric interval `[-n,n]`, with the degenerate case
`n = 0` realized as the Dirac law at `0`. -/
noncomputable def symmetricIntervalUniformLaw (n : ℕ) : ProbabilityMeasure ℝ :=
  if h : n = 0 then
    diracProba 0
  else
    ⟨ENNReal.ofReal (1 / (2 * n : ℝ)) • volume.restrict (Icc (-(n : ℝ)) n),
      symmetricIntervalUniform_isProbabilityMeasure h⟩

-- Proof sketch: unfold the definition and simplify the nonzero branch.
/-- On a nondegenerate interval, the law `symmetricIntervalUniformLaw n` has as underlying measure
the normalized restriction of Lebesgue measure to `[-n,n]`. -/
theorem symmetricIntervalUniformLaw_toMeasure_of_ne_zero {n : ℕ} (hn : n ≠ 0) :
    (symmetricIntervalUniformLaw n : Measure ℝ) =
      ENNReal.ofReal (1 / (2 * n : ℝ)) •
        volume.restrict (Icc (-(n : ℝ)) n) := by
  simp [symmetricIntervalUniformLaw, hn]

/-- Helper for Example 13.28: inside `[-n,n]`, the symmetric uniform law assigns mass `R / n`
to the centered interval `[-R,R]`. -/
private lemma symmetricIntervalUniformLaw_apply_Icc_of_le {n : ℕ} (hn : n ≠ 0)
    {R : ℝ} (_hRnonneg : 0 ≤ R) (hRle : R ≤ n) :
    (symmetricIntervalUniformLaw n : Measure ℝ) (Set.Icc (-R) R) =
      ENNReal.ofReal (R / n) := by
  -- Rewrite to the normalized restriction measure on `[-n,n]`.
  rw [symmetricIntervalUniformLaw_toMeasure_of_ne_zero hn]
  have hmeas : MeasurableSet (Set.Icc (-R) R) := isClosed_Icc.measurableSet
  have hinter :
      Set.Icc (-R) R ∩ Set.Icc (-(n : ℝ)) (n : ℝ) = Set.Icc (-R) R := by
    ext x
    constructor
    · intro hx
      exact hx.1
    · intro hx
      refine ⟨hx, ?_⟩
      constructor
      · exact le_trans (neg_le_neg hRle) hx.1
      · exact le_trans hx.2 hRle
  have hnreal : (n : ℝ) ≠ 0 := by
    exact_mod_cast hn
  -- The restriction contributes exactly the interval length `2R`.
  rw [Measure.smul_apply, Measure.restrict_apply hmeas, hinter, Real.volume_Icc]
  calc
    ENNReal.ofReal (1 / (2 * n : ℝ)) * ENNReal.ofReal (R - (-R))
        = ENNReal.ofReal ((1 / (2 * n : ℝ)) * (R - (-R))) := by
            rw [← ENNReal.ofReal_mul]
            positivity
    _ = ENNReal.ofReal (R / n) := by
      congr 1
      field_simp [hnreal]
      ring

section Compact

variable (E : Type u) [MeasurableSpace E] [TopologicalSpace E] [CompactSpace E]

-- Proof sketch: apply `IsTightMeasureSet.of_compactSpace` to the image of the canonical owner type
-- `ProbabilityMeasure E` in `Measure E`.
/-- Item (i) of Example 13.28. If `E` is compact, then the family `𝓜₁(E)` of probability
measures on `E` is tight. -/
theorem compact_probability_measures_are_tight :
    IsTightMeasureSet (Set.range
      (ProbabilityMeasure.toMeasure : ProbabilityMeasure E → Measure E)) := by
  exact IsTightMeasureSet.of_compactSpace

-- Proof sketch: apply `IsTightMeasureSet.of_compactSpace` to the image in `Measure E` of the
-- canonical mass bound `μ.mass ≤ 1` on `FiniteMeasure E`.
/-- Item (i) of Example 13.28. If `E` is compact, then the family `𝓜_{≤ 1}(E)` of
subprobability measures on `E` is tight. -/
theorem compact_subprobability_measures_are_tight :
    IsTightMeasureSet (FiniteMeasure.toMeasure ''
      {μ : FiniteMeasure E | μ.mass ≤ 1}) := by
  exact IsTightMeasureSet.of_compactSpace

end Compact

-- Proof sketch: use the canonical tightness criterion on `ℝ` together with Markov's inequality for
-- the nonnegative function `x ↦ ENNReal.ofReal |x|`, obtaining a uniform tail bound from the
-- finite extended first-moment bound.
/-- Item (ii) of Example 13.28. A family of laws on `ℝ` with uniformly bounded first absolute
moment, expressed as a finite extended nonnegative expectation, is tight. -/
theorem laws_with_bounded_first_moment_are_tight {I : Type v}
    (μ : I → ProbabilityMeasure ℝ) {C : ℝ≥0∞} (hC : C < ⊤)
    (hbound : ∀ i, ∫⁻ x, ENNReal.ofReal |x| ∂(μ i : Measure ℝ) ≤ C) :
    IsTightMeasureSet (ProbabilityMeasure.toMeasure '' Set.range μ) := by
  have himage :
      ProbabilityMeasure.toMeasure '' Set.range μ =
        FiniteMeasure.toMeasure '' Set.range (fun i ↦ (μ i).toFiniteMeasure) := by
    ext ν
    constructor
    · rintro ⟨σ, ⟨i, rfl⟩, rfl⟩
      exact ⟨(μ i).toFiniteMeasure, ⟨i, rfl⟩, by simp⟩
    · rintro ⟨σ, ⟨i, rfl⟩, hσ⟩
      exact ⟨μ i, ⟨i, rfl⟩, by simpa using hσ⟩
  rw [himage]
  refine (MeasureTheory.FiniteMeasure.tight_family_iff_forall_exists_isCompact_measure_compl_lt
    (Set.range fun i ↦ (μ i).toFiniteMeasure)).2 ?_
  intro ε hε
  let R : ℝ := (C.toReal + 1) / ε
  refine ⟨Set.Icc (-R) R, isCompact_Icc, ?_⟩
  intro ν hν
  rcases Set.mem_range.mp hν with ⟨i, rfl⟩
  -- Markov's inequality gives the required uniform escape bound.
  simpa [R] using
    measure_centeredInterval_compl_lt_of_firstMomentBound (ν := μ i) hC (hbound i) hε

-- Proof sketch: for any compact set `K ⊆ ℝ`, choose `n` outside a bounded interval containing
-- `K`; then the Dirac mass at `n` gives mass `1` to `Kᶜ`.
/-- Item (iii) of Example 13.28. The family `(δₙ)ₙ` of Dirac probability measures on `ℝ` is not
tight. -/
theorem dirac_nat_family_not_tight :
    ¬ IsTightMeasureSet
      (ProbabilityMeasure.toMeasure '' Set.range (fun n : ℕ ↦ diracProba (n : ℝ))) := by
  intro htight
  have hhalf : 0 < (1 / 2 : ℝ≥0∞) := by
    norm_num
  obtain ⟨K, hKcompact, hKcompl⟩ :=
    (isTightMeasureSet_iff_exists_isCompact_measure_compl_le.mp htight) (1 / 2) hhalf
  obtain ⟨R, hRpos, hKsubset⟩ := subset_Icc_neg_pos_of_isCompact hKcompact
  let n : ℕ := Nat.ceil R + 1
  have hn_gt : R < (n : ℝ) := by
    have hceil : R ≤ (Nat.ceil R : ℝ) := Nat.le_ceil R
    have hsucc : (Nat.ceil R : ℝ) < (Nat.ceil R : ℝ) + 1 := by
      exact lt_add_one _
    exact by
      simpa [n] using lt_of_le_of_lt hceil hsucc
  have hn_not_mem_Icc : (n : ℝ) ∉ Set.Icc (-R) R := by
    intro hnmem
    exact not_lt_of_ge hnmem.2 hn_gt
  have hn_not_mem_K : (n : ℝ) ∉ K := by
    intro hmem
    exact hn_not_mem_Icc (hKsubset hmem)
  have hdirac_le :
      ((diracProba (n : ℝ) : ProbabilityMeasure ℝ) : Measure ℝ) Kᶜ ≤ 1 / 2 := by
    exact hKcompl _ ⟨diracProba (n : ℝ), ⟨n, rfl⟩, rfl⟩
  have hdirac_eq :
      ((diracProba (n : ℝ) : ProbabilityMeasure ℝ) : Measure ℝ) Kᶜ = 1 := by
    simpa using
      (MeasureTheory.diracProba_toMeasure_apply_of_mem (A := Kᶜ) hn_not_mem_K)
  rw [hdirac_eq] at hdirac_le
  norm_num at hdirac_le

-- Proof sketch: any compact set is contained in some bounded interval, and for sufficiently large
-- `n` the normalized Lebesgue mass of that compact set inside `[-n,n]` stays strictly below `1`.
/-- Example 13.28 (5): Item (iv). The family of uniform distributions on the intervals `[-n,n]`
is not tight. -/
theorem symmetric_interval_uniform_family_not_tight :
    ¬ IsTightMeasureSet (ProbabilityMeasure.toMeasure '' Set.range symmetricIntervalUniformLaw) :=
  by
  intro htight
  have hhalf : 0 < (1 / 2 : ℝ≥0∞) := by
    norm_num
  obtain ⟨K, hKcompact, hKcompl⟩ :=
    (isTightMeasureSet_iff_exists_isCompact_measure_compl_le.mp htight) (1 / 2) hhalf
  obtain ⟨R, hRpos, hKsubset⟩ := subset_Icc_neg_pos_of_isCompact hKcompact
  let n : ℕ := max 1 (Nat.ceil (2 * R) + 1)
  have hn_nonzero : n ≠ 0 := by
    have h1 : 1 ≤ n := by
      dsimp [n]
      exact le_max_left 1 (Nat.ceil (2 * R) + 1)
    exact Nat.ne_of_gt (lt_of_lt_of_le Nat.zero_lt_one h1)
  have htwoR_lt : 2 * R < (n : ℝ) := by
    have hceil : 2 * R ≤ (Nat.ceil (2 * R) : ℝ) := Nat.le_ceil (2 * R)
    have hsucc : (Nat.ceil (2 * R) : ℝ) < ((Nat.ceil (2 * R) + 1 : ℕ) : ℝ) := by
      exact_mod_cast Nat.lt_succ_self (Nat.ceil (2 * R))
    have haux : 2 * R < ((Nat.ceil (2 * R) + 1 : ℕ) : ℝ) := by
      exact lt_of_le_of_lt hceil hsucc
    have hmax : ((Nat.ceil (2 * R) + 1 : ℕ) : ℝ) ≤ (n : ℝ) := by
      dsimp [n]
      exact_mod_cast le_max_right 1 (Nat.ceil (2 * R) + 1)
    exact lt_of_lt_of_le haux hmax
  have hRle : R ≤ (n : ℝ) := by
    linarith
  have hratio_lt_half : R / (n : ℝ) < 1 / 2 := by
    have hnreal_pos : 0 < (n : ℝ) := by
      exact_mod_cast Nat.pos_of_ne_zero hn_nonzero
    rw [div_lt_iff₀ hnreal_pos]
    linarith
  have hinterval_compl_gt :
      (1 / 2 : ℝ≥0∞) <
        (symmetricIntervalUniformLaw n : Measure ℝ) (Set.Icc (-R) R)ᶜ := by
    have hnreal_pos : 0 < (n : ℝ) := by
      exact_mod_cast Nat.pos_of_ne_zero hn_nonzero
    have hright_pos : 0 < 1 - R / (n : ℝ) := by
      linarith
    have hhalf_lt_real : (1 / 2 : ℝ) < 1 - R / (n : ℝ) := by
      linarith
    have hhalf_eq : (1 / 2 : ℝ≥0∞) = ENNReal.ofReal (1 / 2 : ℝ) := by
      rw [ENNReal.ofReal_div_of_pos (show (0 : ℝ) < 2 by norm_num)]
      norm_num
    have hhalf_lt_enn :
        ENNReal.ofReal (1 / 2 : ℝ) < ENNReal.ofReal (1 - R / (n : ℝ)) := by
      exact (ENNReal.ofReal_lt_ofReal_iff hright_pos).2 hhalf_lt_real
    calc
      (1 / 2 : ℝ≥0∞) = ENNReal.ofReal (1 / 2 : ℝ) := hhalf_eq
      _ < ENNReal.ofReal (1 - R / (n : ℝ)) := hhalf_lt_enn
      _ = (symmetricIntervalUniformLaw n : Measure ℝ) (Set.Icc (-R) R)ᶜ := by
        rw [MeasureTheory.prob_compl_eq_one_sub measurableSet_Icc]
        rw [symmetricIntervalUniformLaw_apply_Icc_of_le hn_nonzero hRpos.le hRle]
        rw [show (1 : ℝ≥0∞) = ENNReal.ofReal (1 : ℝ) by norm_num]
        rw [← ENNReal.ofReal_sub 1 (div_nonneg hRpos.le hnreal_pos.le)]
  have hsubset_compl : (Set.Icc (-R) R : Set ℝ)ᶜ ⊆ Kᶜ := by
    intro x hx hxK
    exact hx (hKsubset hxK)
  have hKcompl_gt :
      (1 / 2 : ℝ≥0∞) < (symmetricIntervalUniformLaw n : Measure ℝ) Kᶜ := by
    exact lt_of_lt_of_le hinterval_compl_gt (measure_mono hsubset_compl)
  have hKcompl_le_n :
      (symmetricIntervalUniformLaw n : Measure ℝ) Kᶜ ≤ 1 / 2 := by
    exact hKcompl _ ⟨symmetricIntervalUniformLaw n, ⟨n, rfl⟩, rfl⟩
  exact not_lt_of_ge hKcompl_le_n hKcompl_gt
