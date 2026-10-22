/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Set.FiniteExhaustion
public import Mathlib.MeasureTheory.Covering.Vitali
public import Mathlib.MeasureTheory.Measure.Real
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.Order.Interval.Set.OrdConnected

public section

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory Set
open scoped BigOperators

-- Semantic recall note: `lean_leansearch` timed out on this repair pass, so the repair follows the
-- provided textbook item content directly. The source-facing family hypothesis is that members of
-- `𝓤` are genuine bounded intervals with strict endpoints, matching the hint's use of interval
-- lengths and triple enlargements.

/-- An admissible finite subfamily for Exercise 13.1.4 is a finite pairwise disjoint subfamily of
`𝓤`. -/
def Exercise13_1_4AdmissibleSubfamily (𝓤 : Set (Set ℝ)) (s : Finset (Set ℝ)) : Prop :=
  (s : Set (Set ℝ)) ⊆ 𝓤 ∧ (s : Set (Set ℝ)).PairwiseDisjoint id

/-- A genuine nondegenerate interval in `ℝ`, encoded as one of the standard bounded interval
shapes with strict endpoints. -/
def IsNondegenerateInterval (U : Set ℝ) : Prop :=
  ∃ a b : ℝ, a < b ∧
    (U = Set.Icc a b ∨ U = Set.Ioc a b ∨ U = Set.Ico a b ∨ U = Set.Ioo a b)

/-- Source-facing interval predicate for Exercise 13.1.4: genuine intervals in `ℝ` with positive
length. -/
abbrev Exercise13_1_4IsInterval (U : Set ℝ) : Prop :=
  IsNondegenerateInterval U

/-- Helper for Exercise 13.1.4: the left endpoint extracted from a nondegenerate
interval witness. -/
noncomputable def intervalLeftEndpoint (U : Set ℝ) (hU : IsNondegenerateInterval U) : ℝ :=
  Classical.choose hU

/-- Helper for Exercise 13.1.4: the right endpoint extracted from a nondegenerate
interval witness. -/
noncomputable def intervalRightEndpoint (U : Set ℝ) (hU : IsNondegenerateInterval U) : ℝ :=
  Classical.choose (Classical.choose_spec hU)

/-- Helper for Exercise 13.1.4: the geometric length of a nondegenerate interval. -/
noncomputable def intervalLength (U : Set ℝ) (hU : IsNondegenerateInterval U) : ℝ :=
  intervalRightEndpoint U hU - intervalLeftEndpoint U hU

/-- Helper for Exercise 13.1.4: the fixed `ρ`-enlargement of a nondegenerate interval. -/
noncomputable def intervalExpansion (U : Set ℝ) (hU : IsNondegenerateInterval U) (ρ : ℝ) : Set ℝ :=
  Set.Icc (intervalLeftEndpoint U hU - ρ * intervalLength U hU)
    (intervalRightEndpoint U hU + ρ * intervalLength U hU)

/-- Helper for Exercise 13.1.4: the extracted endpoints satisfy the expected strict inequality. -/
lemma intervalLeft_lt_right (U : Set ℝ) (hU : IsNondegenerateInterval U) :
    intervalLeftEndpoint U hU < intervalRightEndpoint U hU :=
  (Classical.choose_spec (Classical.choose_spec hU)).1

/-- Helper for Exercise 13.1.4: the interval is one of the four standard bounded shapes with the
extracted endpoints. -/
lemma interval_shape (U : Set ℝ) (hU : IsNondegenerateInterval U) :
    U = Set.Icc (intervalLeftEndpoint U hU) (intervalRightEndpoint U hU) ∨
      U = Set.Ioc (intervalLeftEndpoint U hU) (intervalRightEndpoint U hU) ∨
      U = Set.Ico (intervalLeftEndpoint U hU) (intervalRightEndpoint U hU) ∨
      U = Set.Ioo (intervalLeftEndpoint U hU) (intervalRightEndpoint U hU) :=
  (Classical.choose_spec (Classical.choose_spec hU)).2

/-- Helper for Exercise 13.1.4: every nondegenerate interval is measurable. -/
lemma measurableSet_of_isNondegenerateInterval {U : Set ℝ} (hU : IsNondegenerateInterval U) :
    MeasurableSet U := by
  -- Proof comment: unpack the witness and reduce to the standard measurable interval lemmas.
  rcases interval_shape U hU with h | h | h | h <;> rw [h]
  · exact measurableSet_Icc
  · exact measurableSet_Ioc
  · exact measurableSet_Ico
  · exact measurableSet_Ioo

/-- Helper for Exercise 13.1.4: every point of a nondegenerate interval lies between the extracted
endpoints. -/
lemma mem_intervalEndpoints {U : Set ℝ} (hU : IsNondegenerateInterval U) {x : ℝ} (hx : x ∈ U) :
    intervalLeftEndpoint U hU ≤ x ∧ x ≤ intervalRightEndpoint U hU := by
  -- Proof comment: after reducing to one of the four standard shapes, membership already encodes
  -- the endpoint inequalities.
  rcases interval_shape U hU with h | h | h | h
  · rw [h] at hx
    simpa using hx
  · rw [h] at hx
    exact ⟨hx.1.le, hx.2⟩
  · rw [h] at hx
    exact ⟨hx.1, hx.2.le⟩
  · rw [h] at hx
    exact ⟨hx.1.le, hx.2.le⟩

/-- Helper for Exercise 13.1.4: nondegenerate intervals have nonempty interior. -/
lemma interior_nonempty_of_isNondegenerateInterval {U : Set ℝ} (hU : IsNondegenerateInterval U) :
    (interior U).Nonempty := by
  -- Proof comment: each standard interval shape contains the open interval between its endpoints.
  rcases interval_shape U hU with h | h | h | h
  · rw [h, interior_Icc]
    exact Set.nonempty_Ioo.mpr (intervalLeft_lt_right U hU)
  · rw [h, interior_Ioc]
    exact Set.nonempty_Ioo.mpr (intervalLeft_lt_right U hU)
  · rw [h, interior_Ico]
    exact Set.nonempty_Ioo.mpr (intervalLeft_lt_right U hU)
  · rw [h, interior_Ioo]
    exact Set.nonempty_Ioo.mpr (intervalLeft_lt_right U hU)

/-- Helper for Exercise 13.1.4: the measure of a nondegenerate interval is its extracted length. -/
lemma volumeReal_eq_intervalLength {U : Set ℝ} (hU : IsNondegenerateInterval U) :
    volume.real U = intervalLength U hU := by
  -- Proof comment: all four bounded interval shapes have the same Lebesgue measure `b - a`.
  rcases interval_shape U hU with h | h | h | h
  · calc
      volume.real U =
          volume.real (Set.Icc (intervalLeftEndpoint U hU) (intervalRightEndpoint U hU)) := by
            exact congrArg volume.real h
      _ = intervalRightEndpoint U hU - intervalLeftEndpoint U hU := by
        have hMeasure :
            volume.real (Set.Icc (intervalLeftEndpoint U hU) (intervalRightEndpoint U hU)) =
              intervalRightEndpoint U hU - intervalLeftEndpoint U hU :=
          Real.volume_real_Icc_of_le (intervalLeft_lt_right U hU).le
        simpa using hMeasure
      _ = intervalLength U hU := by rfl
  · calc
      volume.real U =
          volume.real (Set.Ioc (intervalLeftEndpoint U hU) (intervalRightEndpoint U hU)) := by
            exact congrArg volume.real h
      _ = intervalRightEndpoint U hU - intervalLeftEndpoint U hU := by
        have hMeasure :
            volume.real (Set.Ioc (intervalLeftEndpoint U hU) (intervalRightEndpoint U hU)) =
              intervalRightEndpoint U hU - intervalLeftEndpoint U hU :=
          Real.volume_real_Ioc_of_le (intervalLeft_lt_right U hU).le
        simpa using hMeasure
      _ = intervalLength U hU := by rfl
  · calc
      volume.real U =
          volume.real (Set.Ico (intervalLeftEndpoint U hU) (intervalRightEndpoint U hU)) := by
            exact congrArg volume.real h
      _ = intervalRightEndpoint U hU - intervalLeftEndpoint U hU := by
        have hMeasure :
            volume.real (Set.Ico (intervalLeftEndpoint U hU) (intervalRightEndpoint U hU)) =
              intervalRightEndpoint U hU - intervalLeftEndpoint U hU :=
          Real.volume_real_Ico_of_le (intervalLeft_lt_right U hU).le
        simpa using hMeasure
      _ = intervalLength U hU := by rfl
  · calc
      volume.real U =
          volume.real (Set.Ioo (intervalLeftEndpoint U hU) (intervalRightEndpoint U hU)) := by
            exact congrArg volume.real h
      _ = intervalRightEndpoint U hU - intervalLeftEndpoint U hU := by
        have hMeasure :
            volume.real (Set.Ioo (intervalLeftEndpoint U hU) (intervalRightEndpoint U hU)) =
              intervalRightEndpoint U hU - intervalLeftEndpoint U hU :=
          Real.volume_real_Ioo_of_le (intervalLeft_lt_right U hU).le
        simpa using hMeasure
      _ = intervalLength U hU := by rfl

/-- Helper for Exercise 13.1.4: nondegenerate intervals are nonempty. -/
lemma nonempty_of_isNondegenerateInterval {U : Set ℝ} (hU : IsNondegenerateInterval U) :
    U.Nonempty := by
  -- Proof comment: the midpoint belongs to each standard interval shape when the endpoints are
  -- strictly ordered.
  rcases hU with ⟨a, b, hab, hU | hU | hU | hU⟩ <;> subst U
  · refine ⟨(a + b) / 2, ?_⟩
    constructor <;> linarith
  · refine ⟨(a + b) / 2, ?_⟩
    constructor <;> linarith
  · refine ⟨(a + b) / 2, ?_⟩
    constructor <;> linarith
  · refine ⟨(a + b) / 2, ?_⟩
    constructor <;> linarith

/-- Helper for Exercise 13.1.4: every element of a nondegenerate interval stays within one length
of any other point of the same interval. -/
lemma abs_sub_le_intervalLength_of_mem {U : Set ℝ} (hU : IsNondegenerateInterval U)
    {x y : ℝ} (hx : x ∈ U) (hy : y ∈ U) :
    |x - y| ≤ intervalLength U hU := by
  -- Proof comment: both points lie between the extracted endpoints, so their distance is bounded
  -- by the total interval length.
  obtain ⟨hxL, hxR⟩ := mem_intervalEndpoints hU hx
  obtain ⟨hyL, hyR⟩ := mem_intervalEndpoints hU hy
  simpa [intervalLength] using
    abs_sub_le_of_le_of_le hxL hxR hyL hyR

/-- Helper for Exercise 13.1.4: the `ρ`-expansion has the expected Lebesgue measure. -/
lemma volume_intervalExpansion {U : Set ℝ} (hU : IsNondegenerateInterval U)
    {ρ : ℝ} (_hρ : 0 ≤ ρ) :
    volume (intervalExpansion U hU ρ) = ENNReal.ofReal ((1 + 2 * ρ) * volume.real U) := by
  -- Proof comment: the expansion is a closed interval whose new length is `(1 + 2ρ)` times the
  -- original length.
  rw [intervalExpansion, Real.volume_Icc]
  have hcalc :
      (intervalRightEndpoint U hU + ρ * intervalLength U hU) -
          (intervalLeftEndpoint U hU - ρ * intervalLength U hU) =
        (1 + 2 * ρ) * intervalLength U hU := by
    unfold intervalLength
    ring
  rw [hcalc, volumeReal_eq_intervalLength hU]

/-- Helper for Exercise 13.1.4: an interval intersecting `V` with no larger than `ρ` times the
measure of `V` is contained in the fixed `ρ`-expansion of `V`. -/
lemma subset_intervalExpansion_of_inter_nonempty_of_volume_le
    {U V : Set ℝ} (hU : IsNondegenerateInterval U) (hV : IsNondegenerateInterval V)
    {ρ : ℝ} (_hρ : 0 ≤ ρ) (hinter : (U ∩ V).Nonempty)
    (hvol : volume.real U ≤ ρ * volume.real V) :
    U ⊆ intervalExpansion V hV ρ := by
  -- Proof comment: choose one intersection point `z`; every point of `U` lies within one interval
  -- length of `z`, and that length is bounded by `ρ` times the length of `V`.
  rcases hinter with ⟨z, hzU, hzV⟩
  intro x hxU
  rw [intervalExpansion]
  obtain ⟨hzL, hzR⟩ := mem_intervalEndpoints hV hzV
  have hxDist : |x - z| ≤ intervalLength U hU := abs_sub_le_intervalLength_of_mem hU hxU hzU
  have hlen :
      intervalLength U hU ≤ ρ * intervalLength V hV := by
    simpa [volumeReal_eq_intervalLength hU, volumeReal_eq_intervalLength hV] using hvol
  have hleft : intervalLeftEndpoint V hV - ρ * intervalLength V hV ≤ x := by
    have hxLeft : z - intervalLength U hU ≤ x := sub_le_of_abs_sub_le_left hxDist
    linarith
  have hright : x ≤ intervalRightEndpoint V hV + ρ * intervalLength V hV := by
    have hxRight : x ≤ z + intervalLength U hU := by
      have : x - intervalLength U hU ≤ z := sub_le_of_abs_sub_le_right hxDist
      linarith
    linarith
  exact ⟨hleft, hright⟩

/-- Helper for Exercise 13.1.4: the printed finite large-measure selection conclusion. -/
def Exercise13_1_4HasLargeMeasureSelection (𝓤 : Set (Set ℝ)) : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∃ s : Finset (Set ℝ),
      Exercise13_1_4AdmissibleSubfamily 𝓤 s ∧
      ((1 - ε) / 3) * volume.real (⋃₀ 𝓤) < ∑ U ∈ s, volume.real U

/-- The printed large-selection claim in Exercise 13.1.4. -/
def Exercise13_1_4PrintedClaim : Prop :=
  ∀ 𝓤 : Set (Set ℝ),
  (∀ U ∈ 𝓤, Exercise13_1_4IsInterval U) →
    0 < volume.real (⋃₀ 𝓤) →
    volume (⋃₀ 𝓤) < ⊤ →
    Exercise13_1_4HasLargeMeasureSelection 𝓤

/-- Helper for Exercise 13.1.4: Vitali's abstract disjoint-subfamily theorem yields a countable
pairwise disjoint subfamily whose members control the sizes of all intervals in `𝓤`. -/
lemma existsCountableDisjointCoveringSubfamily
    (𝓤 : Set (Set ℝ)) (h𝓤 : ∀ U ∈ 𝓤, Exercise13_1_4IsInterval U)
    (h𝓤_fin : volume (⋃₀ 𝓤) < ⊤) {τ : ℝ} (hτ : 1 < τ) :
    ∃ u ⊆ 𝓤,
      u.PairwiseDisjoint id ∧
      u.Countable ∧
      ∀ U ∈ 𝓤, ∃ V ∈ u, (U ∩ V).Nonempty ∧ volume.real U ≤ τ * volume.real V := by
  classical
  -- Proof comment: apply the abstract Vitali theorem with the interval itself as the body and
  -- `volume.real` as the size function, then package countability from nonempty interiors.
  obtain ⟨u, hu_subset, hu_disj, hu_cover⟩ :=
    Vitali.exists_disjoint_subfamily_covering_enlargement
      id 𝓤 (fun U ↦ volume.real U) τ hτ
      (fun U hU ↦ measureReal_nonneg)
      (volume.real (⋃₀ 𝓤))
      (fun U hU ↦ measureReal_mono (subset_sUnion_of_mem hU) h𝓤_fin.ne)
      (fun U hU ↦ nonempty_of_isNondegenerateInterval (h𝓤 U hU))
  have hu_count : u.Countable := by
    -- Proof comment: disjoint intervals with nonempty interiors form a countable family in `ℝ`.
    exact hu_disj.countable_of_nonempty_interior fun U hU ↦
      interior_nonempty_of_isNondegenerateInterval (h𝓤 U (hu_subset hU))
  exact ⟨u, hu_subset, hu_disj, hu_count, hu_cover⟩

/-- Helper for Exercise 13.1.4: if every interval in `𝓤` is controlled by a selected interval in a
countable disjoint subfamily `u`, then the union of `𝓤` has measure at most `(1 + 2τ)` times the
measure of `⋃₀ u`. -/
lemma measure_sUnion_le_scaledSelection
    (𝓤 : Set (Set ℝ)) (h𝓤 : ∀ U ∈ 𝓤, Exercise13_1_4IsInterval U)
    (h𝓤_fin : volume (⋃₀ 𝓤) < ⊤)
    {u : Set (Set ℝ)} (hu_subset : u ⊆ 𝓤) (hu_count : u.Countable)
    (hu_disj : u.PairwiseDisjoint id) {τ : ℝ} (hτ : 0 ≤ τ)
    (hcover : ∀ U ∈ 𝓤, ∃ V ∈ u, (U ∩ V).Nonempty ∧ volume.real U ≤ τ * volume.real V) :
    volume.real (⋃₀ 𝓤) ≤ (1 + 2 * τ) * volume.real (⋃₀ u) := by
  classical
  have hu_union_fin : volume (⋃₀ u) < ⊤ := by
    exact lt_of_le_of_lt (measure_mono (sUnion_subset_sUnion hu_subset)) h𝓤_fin
  have hu_meas : ∀ U ∈ u, MeasurableSet U := by
    intro U hU
    exact measurableSet_of_isNondegenerateInterval (h𝓤 U (hu_subset hU))
  have hu_mem_fin : ∀ U ∈ u, volume U ≠ ⊤ := by
    intro U hU
    exact ne_top_of_le_ne_top hu_union_fin.ne (measure_mono (subset_sUnion_of_mem hU))
  have hcover_subset :
      ⋃₀ 𝓤 ⊆ ⋃ V : u, intervalExpansion V.1 (h𝓤 V.1 (hu_subset V.2)) τ := by
    -- Proof comment: each `U ∈ 𝓤` is contained in the `τ`-expansion of a selected interval that
    -- intersects it and has comparable measure.
    intro x hx
    rcases mem_sUnion.1 hx with ⟨U, hU, hxU⟩
    rcases hcover U hU with ⟨V, hV, hinter, hvol⟩
    refine mem_iUnion.2 ⟨⟨V, hV⟩, ?_⟩
    exact subset_intervalExpansion_of_inter_nonempty_of_volume_le
      (h𝓤 U hU) (h𝓤 V (hu_subset hV)) hτ hinter hvol hxU
  have hmeasure :
      volume (⋃₀ 𝓤) ≤ ENNReal.ofReal (1 + 2 * τ) * volume (⋃₀ u) := by
    haveI : Encodable u := hu_count.toEncodable
    have hfactor_nonneg : 0 ≤ 1 + 2 * τ := by
      linarith
    calc
      volume (⋃₀ 𝓤)
          ≤ volume (⋃ V : u, intervalExpansion V.1 (h𝓤 V.1 (hu_subset V.2)) τ) := by
            exact measure_mono hcover_subset
      _ ≤ ∑' V : u, volume (intervalExpansion V.1 (h𝓤 V.1 (hu_subset V.2)) τ) := by
            exact measure_iUnion_le _
      _ = ∑' V : u, ENNReal.ofReal ((1 + 2 * τ) * volume.real V.1) := by
            congr with V
            simpa using volume_intervalExpansion (h𝓤 V.1 (hu_subset V.2)) hτ
      _ = ∑' V : u, ENNReal.ofReal (1 + 2 * τ) * volume V.1 := by
            refine tsum_congr fun V ↦ ?_
            rw [ENNReal.ofReal_mul hfactor_nonneg,
              MeasureTheory.ofReal_measureReal (hu_mem_fin V.1 V.2)]
      _ = ENNReal.ofReal (1 + 2 * τ) * ∑' V : u, volume V.1 := by
            rw [ENNReal.tsum_mul_left]
      _ = ENNReal.ofReal (1 + 2 * τ) * volume (⋃₀ u) := by
            rw [measure_sUnion hu_count hu_disj hu_meas]
  have hfactor_nonneg : 0 ≤ 1 + 2 * τ := by
    linarith
  have hscaled_fin :
      ENNReal.ofReal (1 + 2 * τ) * volume (⋃₀ u) ≠ ⊤ := by
    exact ENNReal.mul_ne_top (by simp) hu_union_fin.ne
  -- Proof comment: after the ENNReal estimate is established, convert it back to real measure
  -- using finiteness of `⋃₀ u`.
  have hreal := ENNReal.toReal_mono hscaled_fin hmeasure
  calc
    volume.real (⋃₀ 𝓤) ≤ (ENNReal.ofReal (1 + 2 * τ) * volume (⋃₀ u)).toReal := hreal
    _ = (ENNReal.ofReal (1 + 2 * τ)).toReal * volume.real (⋃₀ u) := by
      rw [ENNReal.toReal_mul, Measure.real_def]
    _ = (1 + 2 * τ) * volume.real (⋃₀ u) := by
      rw [ENNReal.toReal_ofReal hfactor_nonneg]

/-- Helper for Exercise 13.1.4: a countable disjoint measurable interval family with finite union
measure has a finite subfamily whose total measure exceeds any smaller target. -/
lemma existsFinset_sum_gt_of_lt_volumeReal_sUnion
    {u : Set (Set ℝ)} (hu_count : u.Countable) (hu_disj : u.PairwiseDisjoint id)
    (hu_meas : ∀ U ∈ u, MeasurableSet U) (hu_fin : volume (⋃₀ u) < ⊤)
    {c : ℝ} (hc : c < volume.real (⋃₀ u)) :
    ∃ s : Finset (Set ℝ),
      (s : Set (Set ℝ)) ⊆ u ∧
      (s : Set (Set ℝ)).PairwiseDisjoint id ∧
      c < ∑ U ∈ s, volume.real U := by
  classical
  let K := hu_count.finiteExhaustion
  have hK_subset (n : ℕ) : K n ⊆ u := by
    intro U hU
    have : U ∈ ⋃ n, K n := mem_iUnion.2 ⟨n, hU⟩
    simpa [K.iUnion_eq] using this
  have hK_union : (⋃ n, ⋃₀ K n) = ⋃₀ u := by
    ext x
    constructor
    · intro hx
      rcases mem_iUnion.1 hx with ⟨n, hx⟩
      rcases mem_sUnion.1 hx with ⟨U, hU, hxU⟩
      exact mem_sUnion.2 ⟨U, hK_subset n hU, hxU⟩
    · intro hx
      rcases mem_sUnion.1 hx with ⟨U, hU, hxU⟩
      have : U ∈ ⋃ n, K n := by simpa [K.iUnion_eq] using hU
      rcases mem_iUnion.1 this with ⟨n, hU_n⟩
      exact mem_iUnion.2 ⟨n, mem_sUnion.2 ⟨U, hU_n, hxU⟩⟩
  have hK_mono : Monotone fun n ↦ ⋃₀ K n := by
    intro m n hmn
    exact sUnion_subset_sUnion (K.mono hmn)
  have hK_tendsto_enn :
      Filter.Tendsto (fun n ↦ volume (⋃₀ K n)) Filter.atTop (nhds (volume (⋃₀ u))) := by
    simpa [hK_union] using (tendsto_measure_iUnion_atTop (μ := volume) hK_mono)
  have hK_tendsto :
      Filter.Tendsto (fun n ↦ volume.real (⋃₀ K n)) Filter.atTop (nhds (volume.real (⋃₀ u))) := by
    rw [← ENNReal.tendsto_toReal_iff
      (fun n ↦ ne_top_of_le_ne_top hu_fin.ne (measure_mono (sUnion_subset_sUnion (hK_subset n))))
      hu_fin.ne] at hK_tendsto_enn
    simpa [Measure.real_def] using hK_tendsto_enn
  have hδ : 0 < volume.real (⋃₀ u) - c := sub_pos.mpr hc
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.1 hK_tendsto (volume.real (⋃₀ u) - c) hδ
  have hstage_le : volume.real (⋃₀ K N) ≤ volume.real (⋃₀ u) := by
    exact measureReal_mono (sUnion_subset_sUnion (hK_subset N)) hu_fin.ne
  have hdist : dist (volume.real (⋃₀ u)) (volume.real (⋃₀ K N)) < volume.real (⋃₀ u) - c := by
    simpa [dist_comm] using hN N le_rfl
  have hstage_gt : c < volume.real (⋃₀ K N) := by
    have hdiff :
        volume.real (⋃₀ u) - volume.real (⋃₀ K N) < volume.real (⋃₀ u) - c := by
      simpa [Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr hstage_le)] using hdist
    linarith
  let s : Finset (Set ℝ) := (K.finite N).toFinset
  have hs_eq : (s : Set (Set ℝ)) = K N := by
    ext U
    simp [s]
  have hs_subset : (s : Set (Set ℝ)) ⊆ u := by
    intro U hU
    exact hK_subset N (by simpa [hs_eq] using hU)
  have hs_disj : (s : Set (Set ℝ)).PairwiseDisjoint id := hu_disj.subset hs_subset
  have hs_mem_fin : ∀ U ∈ s, volume U ≠ ⊤ := by
    intro U hU
    exact ne_top_of_le_ne_top hu_fin.ne
      (measure_mono (subset_sUnion_of_mem (hs_subset (by simpa using hU))))
  have hs_sum :
      volume.real (⋃₀ K N) = ∑ U ∈ s, volume.real U := by
    rw [← hs_eq]
    rw [Set.sUnion_eq_biUnion]
    exact measureReal_biUnion_finset (μ := volume) hs_disj
      (fun U hU ↦ hu_meas U (hs_subset (by simpa using hU))) hs_mem_fin
  exact ⟨s, hs_subset, hs_disj, by simpa [hs_sum] using hstage_gt⟩

/-- Exercise 13.1.4: if `𝓤` is a family of genuine intervals in `ℝ` whose union has finite
positive Lebesgue measure, then for every `ε > 0` there is a finite pairwise disjoint subfamily
whose total measure is larger than `((1 - ε) / 3) * volume.real (⋃₀ 𝓤)`. -/
theorem exercise_13_1_4 :
    Exercise13_1_4PrintedClaim := by
  -- Route correction: the positive-union hypothesis rules out the empty-family obstruction from
  -- earlier false starts, so the whole-family Vitali selection route is valid here.
  intro 𝓤 h𝓤 h𝓤_pos h𝓤_fin ε hε
  let τ : ℝ := 1 + ε / 4
  have hτ_gt : 1 < τ := by
    -- Proof comment: the Vitali selection parameter is chosen slightly above `1`.
    dsimp [τ]
    linarith
  have hτ_nonneg : 0 ≤ τ := by
    -- Proof comment: nonnegativity is the only hypothesis needed for the interval-expansion bound.
    dsimp [τ]
    linarith
  obtain ⟨u, hu_subset, hu_disj, hu_count, hu_cover⟩ :=
    existsCountableDisjointCoveringSubfamily 𝓤 h𝓤 h𝓤_fin hτ_gt
  have hu_fin : volume (⋃₀ u) < ⊤ := by
    exact lt_of_le_of_lt (measure_mono (sUnion_subset_sUnion hu_subset)) h𝓤_fin
  have hu_meas : ∀ U ∈ u, MeasurableSet U := by
    intro U hU
    exact measurableSet_of_isNondegenerateInterval (h𝓤 U (hu_subset hU))
  have hscaled :
      volume.real (⋃₀ 𝓤) ≤ (1 + 2 * τ) * volume.real (⋃₀ u) := by
    -- Proof comment: the selected intervals cover `⋃₀ 𝓤` after fixed-size enlargement, so the
    -- total selected measure already carries a definite fraction of the whole union.
    exact measure_sUnion_le_scaledSelection 𝓤 h𝓤 h𝓤_fin hu_subset hu_count hu_disj hτ_nonneg
      hu_cover
  have hu_nonneg : 0 ≤ volume.real (⋃₀ u) := measureReal_nonneg
  have hfactor_lt_one : ((1 - ε) / 3 : ℝ) * (1 + 2 * τ) < 1 := by
    -- Proof comment: the special choice `τ = 1 + ε / 4` makes the resulting coefficient strictly
    -- smaller than `1`, which is the arithmetic heart of the `1/3` bound.
    dsimp [τ]
    nlinarith [hε]
  have htarget :
      ((1 - ε) / 3) * volume.real (⋃₀ 𝓤) < volume.real (⋃₀ u) := by
    by_cases hcoef_nonneg : 0 ≤ ((1 - ε) / 3 : ℝ)
    · have hscaled' :
          ((1 - ε) / 3 : ℝ) * volume.real (⋃₀ 𝓤) ≤
            (((1 - ε) / 3 : ℝ) * (1 + 2 * τ)) * volume.real (⋃₀ u) := by
        have := mul_le_mul_of_nonneg_left hscaled hcoef_nonneg
        simpa [mul_assoc] using this
      have hstrict :
          (((1 - ε) / 3 : ℝ) * (1 + 2 * τ)) * volume.real (⋃₀ u) <
            1 * volume.real (⋃₀ u) := by
        nlinarith [hfactor_lt_one, hu_nonneg]
      exact lt_of_le_of_lt hscaled' (by simpa using hstrict)
    · have hleft_neg : ((1 - ε) / 3 : ℝ) * volume.real (⋃₀ 𝓤) < 0 := by
        nlinarith [hcoef_nonneg, h𝓤_pos]
      exact lt_of_lt_of_le hleft_neg hu_nonneg
  obtain ⟨s, hs_subset, hs_disj, hs_sum⟩ :=
    existsFinset_sum_gt_of_lt_volumeReal_sUnion hu_count hu_disj hu_meas hu_fin htarget
  exact ⟨s, ⟨hs_subset.trans hu_subset, hs_disj⟩, hs_sum⟩
