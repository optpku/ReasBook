/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib
import Books.ProbabilityTheory_Klenke_2020.Items.Chap13.Definition_13_26

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory Set Filter

open scoped ENNReal NNReal

universe u

namespace MeasureTheory

section

variable {E : Type u} [MeasurableSpace E] [TopologicalSpace E] [PolishSpace E] [BorelSpace E]

/- Layer triage for Exercise 13.4.1.
- `source-facing`: a tightness criterion for families of probability measures on
  `ProbabilityMeasure E`, phrased using small escape-mass events in the base space `E`.
- `core/canonical`: `IsTightMeasureSet` on measures over `ProbabilityMeasure E`.
- `bridge/view`: the chapter owner bridge
  `FiniteMeasure.tight_family_iff_forall_exists_isCompact_measure_compl_lt`, applied on the
  ambient space `ProbabilityMeasure E`, together with the canonical Prokhorov compactness API for
  compact families of probability measures on `E`.
-/

-- Proof sketch: first use the owner bridge
-- `FiniteMeasure.tight_family_iff_forall_exists_isCompact_measure_compl_lt` on the ambient space
-- `ProbabilityMeasure E` to reduce meta-tightness to compact control by subsets of
-- `ProbabilityMeasure E`. For the forward implication, apply this to a compact family of
-- probability measures on `E`, then use Prokhorov tightness on `E` to obtain one compact
-- `K ⊆ E` controlling the escape mass of every measure in the compact family. For the reverse
-- implication, choose compact sets in `E` for a summable sequence of tolerances, replace them by
-- finite unions to get a monotone compact sequence, and apply the Prokhorov compactness theorem
-- to the set of probability measures whose masses outside these compacts are uniformly small.

/-- Helper for Exercise 13.4.1: the canonical view of a family of probability measures on `E` as
ordinary measures on `E`. -/
def probabilityMeasureView (C : Set (ProbabilityMeasure E)) : Set (Measure E) :=
  {((μ : ProbabilityMeasure E) : Measure E) | μ ∈ C}

/-- Helper for Exercise 13.4.1: a compact family of probability measures on `E` is tight when
viewed as a family of measures on `E`. -/
lemma compactProbabilityMeasureViewIsTight {C : Set (ProbabilityMeasure E)} (hC : IsCompact C) :
    IsTightMeasureSet (probabilityMeasureView C) := by
  -- Cache a compatible complete metric so Prokhorov's theorem can use the Polish structure.
  letI := TopologicalSpace.upgradeIsCompletelyMetrizable E
  -- Freeze the closure compactness in the exact spelling expected by Prokhorov's theorem.
  have hclosureC : IsCompact (closure C) := by
    simpa [hC.isClosed.closure_eq] using hC
  -- Route correction: use the compact-closure theorem on the exact measure-view set.
  simpa [probabilityMeasureView] using
    (isTightMeasureSet_of_isCompact_closure (S := C) hclosureC)

/-- Helper for Exercise 13.4.1: a compact family of probability measures on `E` admits one compact
set in `E` that uniformly bounds all escape masses. -/
lemma existsIsCompactUniformEscapeBoundOfIsCompact {C : Set (ProbabilityMeasure E)}
    (hC : IsCompact C) {ε : ℝ} (hε : 0 < ε) :
    ∃ K : Set E, IsCompact K ∧ ∀ μ ∈ C, μ Kᶜ ≤ ENNReal.ofReal ε := by
  -- Route correction: first view `C` as a tight family of measures, then unpack the compact bound.
  have htightC : IsTightMeasureSet (probabilityMeasureView C) :=
    compactProbabilityMeasureViewIsTight (C := C) hC
  have hε' : 0 < ENNReal.ofReal ε := by
    simpa using ENNReal.ofReal_pos.mpr hε
  -- The standard tightness criterion returns the compact set controlling all measures in the view.
  obtain ⟨K, hK, hKbound⟩ :=
    (isTightMeasureSet_iff_exists_isCompact_measure_compl_le.mp htightC) (ENNReal.ofReal ε) hε'
  refine ⟨K, hK, ?_⟩
  intro μ hμ
  -- Apply the extracted estimate to the exact representative `(μ : Measure E)`.
  have hμview : ((μ : ProbabilityMeasure E) : Measure E) ∈ probabilityMeasureView C := by
    exact ⟨μ, hμ, rfl⟩
  have hbound : ((μ : ProbabilityMeasure E) : Measure E) Kᶜ ≤ ENNReal.ofReal ε := by
    exact hKbound _ hμview
  simpa [ProbabilityMeasure.ennreal_coeFn_eq_coeFn_toMeasure] using hbound

/-- Helper for Exercise 13.4.1: Prokhorov compactness applies directly to a monotone compact
control sequence. -/
lemma isCompactUniformEscapeClassOfMonotone {u : ℕ → ℝ≥0} {K : ℕ → Set E}
    (hu : Tendsto u atTop (nhds 0)) (hK : ∀ n, IsCompact (K n)) (hmono : Monotone K) :
    IsCompact {μ : ProbabilityMeasure E | ∀ n, μ (K n)ᶜ ≤ u n} := by
  -- The monotone alternative matches the Prokhorov compactness theorem directly.
  simpa using
    (isCompact_setOf_probabilityMeasure_mass_eq_compl_isCompact_le (u := u) (K := K)
      hu hK (Or.inr hmono))

section

omit [TopologicalSpace E] [PolishSpace E] [BorelSpace E]

/-- Helper for Exercise 13.4.1: if a probability measure fails the uniform compact-control class,
then it violates one of the original escape bounds. -/
lemma complUniformEscapeClass_subset_iUnion_smallEscape {u : ℕ → ℝ≥0}
    {A K : ℕ → Set E} (hAK : ∀ n, A n ⊆ K n) :
    {μ : ProbabilityMeasure E | ∀ n, μ (K n)ᶜ ≤ u n}ᶜ ⊆
      ⋃ n, {μ : ProbabilityMeasure E | (u n : ℝ≥0∞) < μ (A n)ᶜ} := by
  intro μ hμ
  -- Failing one of the `K n` bounds forces the corresponding `A n` escape event.
  have hnot : ¬ ∀ n, μ (K n)ᶜ ≤ u n := by
    simpa using hμ
  rcases not_forall.mp hnot with ⟨n, hn⟩
  refine mem_iUnion.mpr ⟨n, ?_⟩
  have hltK : (u n : ℝ≥0∞) < μ (K n)ᶜ := by
    exact_mod_cast not_le.mp hn
  exact lt_of_lt_of_le hltK <| by
    exact_mod_cast ProbabilityMeasure.apply_mono μ (compl_subset_compl.mpr (hAK n))

/-- Helper for Exercise 13.4.1: a summable union bound gives a strict estimate on the complement
of the compact control class. -/
lemma measureComplUniformEscapeClass_lt_ofSeriesBound
    (μbar : ProbabilityMeasure (ProbabilityMeasure E))
    {s : ℕ → Set (ProbabilityMeasure E)} {B : Set (ProbabilityMeasure E)}
    {u : ℕ → ℝ≥0} {ε : ℝ} (hB : B ⊆ ⋃ n, s n)
    (hs : ∀ n, μbar (s n) < (u n : ℝ≥0∞))
    (hu : ∑' n, (u n : ℝ≥0∞) < ENNReal.ofReal ε) :
    μbar B < ENNReal.ofReal ε := by
  -- After moving to the ambient measure, one application of countable subadditivity closes.
  have hmeasure : (μbar : Measure (ProbabilityMeasure E)) B < ENNReal.ofReal ε := by
    calc
      (μbar : Measure (ProbabilityMeasure E)) B
          ≤ (μbar : Measure (ProbabilityMeasure E)) (⋃ n, s n) := measure_mono hB
      _ ≤ ∑' n, (μbar : Measure (ProbabilityMeasure E)) (s n) := measure_iUnion_le _
      _ ≤ ∑' n, (u n : ℝ≥0∞) := by
        refine ENNReal.tsum_le_tsum fun n ↦ ?_
        simpa [ProbabilityMeasure.ennreal_coeFn_eq_coeFn_toMeasure] using (hs n).le
      _ < ENNReal.ofReal ε := hu
  simpa [ProbabilityMeasure.ennreal_coeFn_eq_coeFn_toMeasure] using hmeasure

/-- Helper for Exercise 13.4.1: passing from `ProbabilityMeasure.toMeasure` to the corresponding
family of finite measures does not change the meta-tightness set. -/
lemma probabilityMeasureImage_eq_toFiniteMeasureImage
    (𝒦 : Set (ProbabilityMeasure (ProbabilityMeasure E))) :
    ProbabilityMeasure.toMeasure '' 𝒦 =
      FiniteMeasure.toMeasure '' (ProbabilityMeasure.toFiniteMeasure '' 𝒦) := by
  ext ν
  constructor
  · rintro ⟨μbar, hμbar, rfl⟩
    exact ⟨μbar.toFiniteMeasure, ⟨μbar, hμbar, rfl⟩, by simp⟩
  · rintro ⟨μbar, ⟨νbar, hνbar, rfl⟩, hμbar⟩
    exact ⟨νbar, hνbar, by simpa using hμbar⟩

end

/-- Helper for Exercise 13.4.1: the quarter-scaled geometric sequence tends to `0` in `ℝ≥0`. -/
lemma tendsto_quarterGeometric (εQuarter : ℝ≥0) :
    Tendsto (fun n : ℕ ↦ εQuarter * (1 / 2 : ℝ≥0) ^ n) atTop (nhds 0) := by
  -- The geometric factor tends to zero, so multiplying by the fixed quarter-scale preserves this.
  have hpow : Tendsto (fun n : ℕ ↦ (1 / 2 : ℝ≥0) ^ n) atTop (nhds 0) := by
    exact NNReal.tendsto_pow_atTop_nhds_zero_of_lt_one
      (show (1 / 2 : ℝ≥0) < 1 by norm_num)
  simpa using hpow.const_mul εQuarter

/-- Helper for Exercise 13.4.1: the `ℝ≥0∞` sum of the quarter-scaled geometric sequence is the
scale multiplied by `2`. -/
lemma tsum_coe_quarterGeometric (εQuarter : ℝ≥0) :
    ∑' n, ((εQuarter * (1 / 2 : ℝ≥0) ^ n : ℝ≥0) : ℝ≥0∞) = (εQuarter : ℝ≥0∞) * 2 := by
  -- Rewrite the series through `ℝ≥0` first, then evaluate the geometric sum explicitly.
  have hsummable : Summable (fun n : ℕ ↦ εQuarter * (1 / 2 : ℝ≥0) ^ n) := by
    exact (NNReal.summable_geometric (show (1 / 2 : ℝ≥0) < 1 by norm_num)).mul_left εQuarter
  calc
    (∑' n, ((εQuarter * (1 / 2 : ℝ≥0) ^ n : ℝ≥0) : ℝ≥0∞))
        = (((∑' n, εQuarter * (1 / 2 : ℝ≥0) ^ n : ℝ≥0)) : ℝ≥0∞) := by
            simpa using (ENNReal.coe_tsum hsummable).symm
    _ = ((εQuarter * ∑' n, ((1 / 2 : ℝ≥0) ^ n) : ℝ≥0) : ℝ≥0∞) := by
      congr 1
      simpa using
        NNReal.tsum_mul_left εQuarter (fun n : ℕ ↦ (1 / 2 : ℝ≥0) ^ n)
    _ = (εQuarter : ℝ≥0∞) * 2 := by
      rw [NNReal.tsum_geometric (show (1 / 2 : ℝ≥0) < 1 by norm_num)]
      have hgeom : ((1 - (1 / 2 : ℝ≥0))⁻¹ : ℝ≥0) = 2 := by
        exact_mod_cast (by norm_num : (((1 - (1 / 2 : ℝ≥0))⁻¹ : ℝ≥0) : ℝ) = 2)
      calc
        (((εQuarter * (1 - (1 / 2 : ℝ≥0))⁻¹ : ℝ≥0)) : ℝ≥0∞)
            = (((εQuarter * 2 : ℝ≥0)) : ℝ≥0∞) := by rw [hgeom]
        _ = (εQuarter : ℝ≥0∞) * 2 := by norm_num

/-- Helper for Exercise 13.4.1: tightness of the meta-family gives the compact small-escape
criterion in the base space `E`. -/
lemma forall_existsIsCompact_smallEscape_of_tight
    (𝒦 : Set (ProbabilityMeasure (ProbabilityMeasure E)))
    (htight : IsTightMeasureSet (ProbabilityMeasure.toMeasure '' 𝒦)) :
    ∀ ε : ℝ, 0 < ε → ∃ K : Set E, IsCompact K ∧
      ∀ μbar ∈ 𝒦,
        μbar {μ : ProbabilityMeasure E | ENNReal.ofReal ε < μ Kᶜ} < ENNReal.ofReal ε := by
  rw [probabilityMeasureImage_eq_toFiniteMeasureImage 𝒦] at htight
  intro ε hε
  -- First obtain a compact class of probability measures on `E` controlling the meta-family.
  obtain ⟨C, hC, hCsmall⟩ :=
    (FiniteMeasure.tight_family_iff_forall_exists_isCompact_measure_compl_lt
      (ProbabilityMeasure.toFiniteMeasure '' 𝒦)).1 htight (ε / 2) (by positivity)
  -- Then tighten that compact class in `ProbabilityMeasure E` down to one compact set in `E`.
  obtain ⟨K, hK, hKbound⟩ :=
    existsIsCompactUniformEscapeBoundOfIsCompact (C := C) hC hε
  refine ⟨K, hK, ?_⟩
  intro μbar hμbar
  have h_escape_subset : {μ : ProbabilityMeasure E | ENNReal.ofReal ε < μ Kᶜ} ⊆ Cᶜ := by
    intro μ hμ hμC
    exact (not_lt_of_ge (hKbound μ hμC)) hμ
  have hCsmall' : (μbar : Measure (ProbabilityMeasure E)) Cᶜ < ENNReal.ofReal (ε / 2) := by
    simpa using hCsmall μbar.toFiniteMeasure ⟨μbar, hμbar, rfl⟩
  have hhalf_lt : ENNReal.ofReal (ε / 2) < ENNReal.ofReal ε := by
    exact (ENNReal.ofReal_lt_ofReal_iff hε).2 (by nlinarith)
  -- The bad escape event is contained in the complement of the compact class `C`.
  have hmeasure :
      (μbar : Measure (ProbabilityMeasure E))
        {μ : ProbabilityMeasure E | ENNReal.ofReal ε < μ Kᶜ} < ENNReal.ofReal ε := by
    calc
      (μbar : Measure (ProbabilityMeasure E))
          {μ : ProbabilityMeasure E | ENNReal.ofReal ε < μ Kᶜ}
          ≤ (μbar : Measure (ProbabilityMeasure E)) Cᶜ := measure_mono h_escape_subset
      _ < ENNReal.ofReal (ε / 2) := hCsmall'
      _ < ENNReal.ofReal ε := hhalf_lt
  simpa [ProbabilityMeasure.ennreal_coeFn_eq_coeFn_toMeasure] using hmeasure

/-- Helper for Exercise 13.4.1: the compact small-escape criterion on `E` implies tightness of the
meta-family on `ProbabilityMeasure E`. -/
lemma tight_of_forall_existsIsCompact_smallEscape
    (𝒦 : Set (ProbabilityMeasure (ProbabilityMeasure E)))
    (hsmall : ∀ ε : ℝ, 0 < ε → ∃ K : Set E, IsCompact K ∧
      ∀ μbar ∈ 𝒦,
        μbar {μ : ProbabilityMeasure E | ENNReal.ofReal ε < μ Kᶜ} < ENNReal.ofReal ε) :
    IsTightMeasureSet (ProbabilityMeasure.toMeasure '' 𝒦) := by
  rw [probabilityMeasureImage_eq_toFiniteMeasureImage 𝒦]
  refine
    (FiniteMeasure.tight_family_iff_forall_exists_isCompact_measure_compl_lt
      (ProbabilityMeasure.toFiniteMeasure '' 𝒦)).2 ?_
  intro ε hε
  let εHalf : ℝ≥0 := ⟨ε / 2, by positivity⟩
  let εQuarter : ℝ≥0 := εHalf / 2
  let u : ℕ → ℝ≥0 := fun n ↦ εQuarter * (1 / 2 : ℝ≥0) ^ n
  have hεHalf_pos : 0 < εHalf := by
    exact_mod_cast (show 0 < ε / 2 by nlinarith)
  have hεQuarter_pos : 0 < εQuarter := by
    dsimp [εQuarter]
    exact div_pos hεHalf_pos (by norm_num)
  have hu_pos_nnreal (n : ℕ) : 0 < u n := by
    dsimp [u]
    exact mul_pos hεQuarter_pos (pow_pos (by norm_num) n)
  have hu_pos (n : ℕ) : 0 < (u n : ℝ) := by
    exact_mod_cast hu_pos_nnreal n
  have hu_tendsto : Tendsto u atTop (nhds 0) := by
    simpa [u] using tendsto_quarterGeometric εQuarter
  have hAexists (n : ℕ) :
      ∃ A : Set E, IsCompact A ∧
        ∀ μbar ∈ 𝒦,
          μbar {μ : ProbabilityMeasure E | (u n : ℝ≥0∞) < μ Aᶜ} < (u n : ℝ≥0∞) := by
    obtain ⟨A, hA, hAescape⟩ := hsmall (u n : ℝ) (hu_pos n)
    refine ⟨A, hA, ?_⟩
    intro μbar hμbar
    simpa [ENNReal.ofReal_coe_nnreal] using hAescape μbar hμbar
  choose A hAcompact hAescape using hAexists
  let K : ℕ → Set E := fun n ↦ ⋃ i ∈ Set.Iic n, A i
  have hKcompact : ∀ n, IsCompact (K n) := by
    intro n
    -- Finite unions preserve compactness along the monotone exhaustion.
    simpa [K] using (finite_Iic n).isCompact_biUnion (fun i _ ↦ hAcompact i)
  have hKmono : Monotone K := by
    intro a b hab
    simp only [K, mem_Iic, le_eq_subset, iUnion_subset_iff]
    intro i hi
    apply subset_biUnion_of_mem
    exact hi.trans hab
  let C : Set (ProbabilityMeasure E) := {μ : ProbabilityMeasure E | ∀ n, μ (K n)ᶜ ≤ u n}
  have hCcompact : IsCompact C := by
    -- Prokhorov compactness closes the class defined by the geometric escape controls.
    simpa [C] using
      isCompactUniformEscapeClassOfMonotone (u := u) (K := K) hu_tendsto hKcompact hKmono
  have hA_subset_K : ∀ n, A n ⊆ K n := by
    intro n x hx
    exact mem_iUnion.mpr ⟨n, mem_iUnion.mpr ⟨by simp, hx⟩⟩
  have hCcompl_subset :
      Cᶜ ⊆ ⋃ n, {μ : ProbabilityMeasure E | (u n : ℝ≥0∞) < μ (A n)ᶜ} := by
    simpa [C] using
      complUniformEscapeClass_subset_iUnion_smallEscape (u := u) (A := A) (K := K) hA_subset_K
  have hu_sum_lt : ∑' n, (u n : ℝ≥0∞) < ENNReal.ofReal ε := by
    calc
      ∑' n, (u n : ℝ≥0∞)
          = (εQuarter : ℝ≥0∞) * 2 := by
              simpa [u] using tsum_coe_quarterGeometric εQuarter
      _ = (εHalf : ℝ≥0∞) := by
        change ((((εHalf / 2 : ℝ≥0) * 2 : ℝ≥0)) : ℝ≥0∞) = (εHalf : ℝ≥0∞)
        norm_num
      _ = ENNReal.ofReal (ε / 2) := by
        simpa [εHalf] using
          (show (εHalf : ℝ≥0∞) = ENNReal.ofReal (εHalf : ℝ) from ENNReal.ofReal_coe_nnreal.symm)
      _ < ENNReal.ofReal ε := by
        exact (ENNReal.ofReal_lt_ofReal_iff hε).2 (by nlinarith)
  refine ⟨C, hCcompact, ?_⟩
  intro ν hν
  rcases hν with ⟨μbar, hμbar, rfl⟩
  -- The complement of `C` sits inside a countable union of small escape events.
  simpa [C] using
    measureComplUniformEscapeClass_lt_ofSeriesBound (μbar := μbar) hCcompl_subset
      (fun n ↦ hAescape n μbar hμbar) hu_sum_lt

/-- Exercise 13.4.1: a family of probability measures on `ProbabilityMeasure E` is tight if and
only if, for every `ε > 0`, there is a compact set `K ⊆ E` such that every meta-measure in the
family gives mass `< ε` to the set of probability measures assigning mass `> ε` to `Kᶜ`. -/
theorem tight_probabilityMeasureFamily_iff_forall_exists_isCompact_small_escape
    (𝒦 : Set (ProbabilityMeasure (ProbabilityMeasure E))) :
    IsTightMeasureSet (ProbabilityMeasure.toMeasure '' 𝒦) ↔
      ∀ ε : ℝ, 0 < ε → ∃ K : Set E, IsCompact K ∧
        ∀ μbar ∈ 𝒦,
          μbar {μ : ProbabilityMeasure E | ENNReal.ofReal ε < μ Kᶜ} < ENNReal.ofReal ε := by
  constructor
  · exact forall_existsIsCompact_smallEscape_of_tight 𝒦
  · exact tight_of_forall_existsIsCompact_smallEscape 𝒦

end

end MeasureTheory
