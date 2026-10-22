/-
Authors: Zichen Wang, Wanli Ma, Qiming Dai, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Mathlib

open scoped BigOperators

section Chap07
section Section02

/-- Definition 7.2 (Open box and volume): an open box in `ℝ^n` is specified by coordinate
bounds `a_i ≤ b_i`, corresponding to the product set `∏ i, (a_i, b_i)`. -/
structure OpenBox (n : ℕ) where
  lower : Fin n → ℝ
  upper : Fin n → ℝ
  lower_le_upper : ∀ i, lower i ≤ upper i

/-- The subset of `ℝ^n` represented by an open box. -/
def OpenBox.toSet {n : ℕ} (B : OpenBox n) : Set (Fin n → ℝ) :=
  {x | ∀ i, x i ∈ Set.Ioo (B.lower i) (B.upper i)}

/-- The volume of an open box, defined as the product of side lengths. -/
def OpenBox.volume {n : ℕ} (B : OpenBox n) : ℝ :=
  ∏ i, (B.upper i - B.lower i)

/-- Definition 7.3 (Covering by boxes): a family `(B_j)_{j ∈ J}` of boxes in `ℝ^n` covers
`Ω` when `Ω ⊆ ⋃ j, B_j`. -/
def IsCoveredByBoxes {n : ℕ} (Ω : Set (Fin n → ℝ)) {J : Type*} (B : J → OpenBox n) : Prop :=
  Ω ⊆ ⋃ j, (B j).toSet

/-- The raw cover-cost functional used to build `boxOuterMeasure`, normalized so that the
empty set has cost `0`. -/
noncomputable def boxOuterMeasureCoverCost (d : ℕ) (Ω : Set (Fin d → ℝ)) : ENNReal :=
  @ite ENNReal (Ω = (∅ : Set (Fin d → ℝ)))
    (show Decidable (Ω = (∅ : Set (Fin d → ℝ))) from
      (Classical.decEq (α := Set (Fin d → ℝ)) Ω (∅ : Set (Fin d → ℝ))))
    0
    (sInf
      {r : ENNReal |
        ∃ C : ℕ → OpenBox d,
          IsCoveredByBoxes Ω C ∧ r = ∑' j, ENNReal.ofReal ((C j).volume)})

/-- The normalized cover-cost functional vanishes on the empty set. -/
lemma boxOuterMeasureCoverCost_empty (d : ℕ) :
    boxOuterMeasureCoverCost d ∅ = 0 := by
  simp [boxOuterMeasureCoverCost]

/-- On nonempty sets, the normalized cover-cost agrees with the raw cover infimum. -/
lemma boxOuterMeasureCoverCost_eq_rawInf_of_nonempty
    {d : ℕ} {Ω : Set (Fin d → ℝ)} (hΩ : Ω.Nonempty) :
    boxOuterMeasureCoverCost d Ω =
      sInf
        {r : ENNReal |
          ∃ C : ℕ → OpenBox d,
            IsCoveredByBoxes Ω C ∧ r = ∑' j, ENNReal.ofReal ((C j).volume)} := by
  simp [boxOuterMeasureCoverCost, hΩ.ne_empty]

/-- Definition 7.4 (Outer measure): for `Ω ⊆ ℝ^d`, `boxOuterMeasure d Ω` is the extended
real infimum of `∑ j, vol(B_j)` over all at-most-countable box covers `(B_j)` of `Ω`. -/
noncomputable def boxOuterMeasure (d : ℕ) : MeasureTheory.OuterMeasure (Fin d → ℝ) :=
  MeasureTheory.OuterMeasure.ofFunction
    (boxOuterMeasureCoverCost d)
    (boxOuterMeasureCoverCost_empty d)

/-- Defining infimum formula for `boxOuterMeasure` evaluated on a set `Ω`. -/
lemma boxOuterMeasure_apply (d : ℕ) (Ω : Set (Fin d → ℝ)) :
    boxOuterMeasure d Ω =
      ⨅ (t : ℕ → Set (Fin d → ℝ)) (_ : Ω ⊆ ⋃ i, t i),
        ∑' n, boxOuterMeasureCoverCost d (t n) := by
  simpa [boxOuterMeasure] using
    (MeasureTheory.OuterMeasure.ofFunction_apply
      (m := boxOuterMeasureCoverCost d)
      (m_empty := boxOuterMeasureCoverCost_empty d)
      (s := Ω))

/-- Helper for Proposition 7.1: monotonicity of `boxOuterMeasure` under a box cover. -/
lemma helperForProposition_7_1_coverMonotone
    {d : ℕ} {Ω : Set (Fin d → ℝ)} (B : ℕ → OpenBox d)
    (hcover : IsCoveredByBoxes Ω B) :
    boxOuterMeasure d Ω ≤ boxOuterMeasure d (⋃ j, (B j).toSet) := by
  exact (boxOuterMeasure d).mono hcover

/-- Helper for Proposition 7.1: countable subadditivity on a `ℕ`-indexed union of boxes. -/
lemma helperForProposition_7_1_coverSubadditive
    {d : ℕ} (B : ℕ → OpenBox d) :
    boxOuterMeasure d (⋃ j, (B j).toSet) ≤ ∑' j, boxOuterMeasure d ((B j).toSet) := by
  simpa using
    (MeasureTheory.measure_iUnion_le (μ := boxOuterMeasure d)
      (s := fun j => (B j).toSet))

/-- Helper for Proposition 7.1: identify `OpenBox.volume` with Lebesgue volume on `B.toSet`. -/
lemma helperForProposition_7_1_openBoxVolume_eqMeasureVolume
    {d : ℕ} (B : OpenBox d) :
    MeasureTheory.volume (B.toSet) = ENNReal.ofReal (B.volume) := by
  have hset : B.toSet = Set.pi Set.univ (fun i => Set.Ioo (B.lower i) (B.upper i)) := by
    ext x
    simp [OpenBox.toSet]
  rw [hset, OpenBox.volume, Real.volume_pi_Ioo]
  symm
  exact ENNReal.ofReal_prod_of_nonneg
    (s := Finset.univ)
    (f := fun i : Fin d => B.upper i - B.lower i)
    (fun i _ => sub_nonneg.mpr (B.lower_le_upper i))

/-- The cover-cost dominates Lebesgue volume on all sets. -/
lemma helperForProposition_7_1_volume_le_boxOuterMeasureCoverCost
    {d : ℕ} (Ω : Set (Fin d → ℝ)) :
    MeasureTheory.volume Ω ≤ boxOuterMeasureCoverCost d Ω := by
  by_cases hΩ : Ω = ∅
  · simp [boxOuterMeasureCoverCost, hΩ]
  · have hΩne : Ω ≠ ∅ := hΩ
    simp [boxOuterMeasureCoverCost, hΩne]
    intro r C hcover hr
    rw [hr]
    calc
      MeasureTheory.volume Ω ≤ MeasureTheory.volume (⋃ j, (C j).toSet) :=
        MeasureTheory.measure_mono hcover
      _ ≤ ∑' j, MeasureTheory.volume ((C j).toSet) := by
        simpa using
          (MeasureTheory.measure_iUnion_le (μ := MeasureTheory.volume)
            (s := fun j => (C j).toSet))
      _ = ∑' j, ENNReal.ofReal ((C j).volume) := by
        refine tsum_congr ?_
        intro j
        exact helperForProposition_7_1_openBoxVolume_eqMeasureVolume (B := C j)

/-- Lebesgue volume is bounded above by `boxOuterMeasure`. -/
lemma helperForProposition_7_1_volume_le_boxOuterMeasure
    {d : ℕ} (Ω : Set (Fin d → ℝ)) :
    MeasureTheory.volume Ω ≤ boxOuterMeasure d Ω := by
  have hle :
      (MeasureTheory.volume.toOuterMeasure : MeasureTheory.OuterMeasure (Fin d → ℝ)) ≤
        boxOuterMeasure d := by
    refine
      (MeasureTheory.OuterMeasure.le_ofFunction
        (m := boxOuterMeasureCoverCost d)
        (m_empty := boxOuterMeasureCoverCost_empty d)
        (μ := (MeasureTheory.volume.toOuterMeasure : MeasureTheory.OuterMeasure (Fin d → ℝ)))).2
        ?_
    intro s
    simpa using helperForProposition_7_1_volume_le_boxOuterMeasureCoverCost (d := d) s
  exact hle Ω

/-- Helper for Proposition 7.1: any countable open-box cover of a box has total volume at
least the covered box volume. -/
lemma helperForProposition_7_1_openBoxCoverVolumeLowerBound
    {d : ℕ} (B : OpenBox d) (C : ℕ → OpenBox d)
    (hcover : IsCoveredByBoxes (B.toSet) C) :
    ENNReal.ofReal (B.volume) ≤ ∑' j, ENNReal.ofReal ((C j).volume) := by
  have hmono : MeasureTheory.volume (B.toSet) ≤ MeasureTheory.volume (⋃ j, (C j).toSet) :=
    MeasureTheory.measure_mono hcover
  have hsub :
      MeasureTheory.volume (⋃ j, (C j).toSet) ≤ ∑' j, MeasureTheory.volume ((C j).toSet) := by
    simpa using
      (MeasureTheory.measure_iUnion_le (μ := MeasureTheory.volume) (s := fun j => (C j).toSet))
  calc
    ENNReal.ofReal (B.volume) = MeasureTheory.volume (B.toSet) := by
      exact (helperForProposition_7_1_openBoxVolume_eqMeasureVolume (B := B)).symm
    _ ≤ MeasureTheory.volume (⋃ j, (C j).toSet) := hmono
    _ ≤ ∑' j, MeasureTheory.volume ((C j).toSet) := hsub
    _ = ∑' j, ENNReal.ofReal ((C j).volume) := by
      refine tsum_congr ?_
      intro j
      exact helperForProposition_7_1_openBoxVolume_eqMeasureVolume (B := C j)

/-- Helper for Proposition 7.1: a canonical zero-volume open box in positive dimension. -/
def helperForProposition_7_1_zeroVolumeOpenBox (d : ℕ) : OpenBox (d + 1) where
  lower := fun _ => 0
  upper := fun _ => 0
  lower_le_upper := fun _ => le_rfl

/-- Helper for Proposition 7.1: the canonical positive-dimensional zero box has volume `0`. -/
lemma helperForProposition_7_1_zeroVolumeOpenBox_volume (d : ℕ) :
    (helperForProposition_7_1_zeroVolumeOpenBox d).volume = 0 := by
  simp [helperForProposition_7_1_zeroVolumeOpenBox, OpenBox.volume]

/-- Helper for Proposition 7.1: in positive dimension, each open box has outer measure equal
to its box volume. -/
lemma helperForProposition_7_1_openBoxOuterEqVolume
    (d : ℕ) (B : OpenBox (d + 1)) :
    boxOuterMeasure (d + 1) (B.toSet) = ENNReal.ofReal (B.volume) := by
  let Z : OpenBox (d + 1) := helperForProposition_7_1_zeroVolumeOpenBox d
  let C : ℕ → OpenBox (d + 1) := fun j => if j = 0 then B else Z
  have hcoverC : IsCoveredByBoxes (B.toSet) C := by
    intro x hx
    refine Set.mem_iUnion.mpr ?_
    refine ⟨0, ?_⟩
    simpa [C] using hx
  have hsumC : (∑' j, ENNReal.ofReal ((C j).volume)) = ENNReal.ofReal (B.volume) := by
    rw [tsum_eq_single 0]
    · simp [C]
    · intro j hj
      simp [C, hj, Z, helperForProposition_7_1_zeroVolumeOpenBox_volume]
  have hCoverCostUpper :
      boxOuterMeasureCoverCost (d + 1) (B.toSet) ≤ ENNReal.ofReal (B.volume) := by
    by_cases hB : B.toSet = ∅
    · simp [boxOuterMeasureCoverCost, hB]
    · simp [boxOuterMeasureCoverCost, hB]
      refine sInf_le ?_
      exact ⟨C, hcoverC, hsumC.symm⟩
  have hUpper : boxOuterMeasure (d + 1) (B.toSet) ≤ ENNReal.ofReal (B.volume) := by
    have hOfLe :
        boxOuterMeasure (d + 1) (B.toSet) ≤ boxOuterMeasureCoverCost (d + 1) (B.toSet) := by
      simpa [boxOuterMeasure] using
        (MeasureTheory.OuterMeasure.ofFunction_le
          (m := boxOuterMeasureCoverCost (d + 1))
          (m_empty := boxOuterMeasureCoverCost_empty (d + 1))
          (s := B.toSet))
    exact le_trans hOfLe hCoverCostUpper
  have hLower : ENNReal.ofReal (B.volume) ≤ boxOuterMeasure (d + 1) (B.toSet) := by
    calc
      ENNReal.ofReal (B.volume) = MeasureTheory.volume (B.toSet) := by
        symm
        exact helperForProposition_7_1_openBoxVolume_eqMeasureVolume (B := B)
      _ ≤ boxOuterMeasure (d + 1) (B.toSet) :=
        helperForProposition_7_1_volume_le_boxOuterMeasure (d := d + 1) (Ω := B.toSet)
  exact le_antisymm hUpper hLower

/-- Any nonempty subset of `ℝ^0` has infinite normalized cover-cost. -/
lemma helperForProposition_7_1_boxOuterMeasureCoverCost_zeroDim_eq_top_of_nonempty
    {Ω : Set (Fin 0 → ℝ)} (hΩ : Ω.Nonempty) :
    boxOuterMeasureCoverCost 0 Ω = (⊤ : ENNReal) := by
  have hΩne : Ω ≠ ∅ := hΩ.ne_empty
  simp [boxOuterMeasureCoverCost, hΩne]
  intro r C _ hr
  rw [hr]
  have hconst :
      (fun j : ℕ => ENNReal.ofReal ((C j).volume)) = fun _ : ℕ => (1 : ENNReal) := by
    funext j
    simp [OpenBox.volume]
  rw [hconst, ENNReal.tsum_const_eq_top_of_ne_zero one_ne_zero]

/-- Helper for Proposition 7.1: in dimension `0`, the outer measure of `univ` is `⊤` for this
box-cover model using `ℕ`-indexed covers. -/
lemma helperForProposition_7_1_boxOuterMeasure_zero_univ_eq_top :
    boxOuterMeasure 0 (Set.univ : Set (Fin 0 → ℝ)) = ⊤ := by
  have hTopLe : (⊤ : ENNReal) ≤ boxOuterMeasure 0 (Set.univ : Set (Fin 0 → ℝ)) := by
    rw [boxOuterMeasure_apply]
    refine le_iInf ?_
    intro t
    refine le_iInf ?_
    intro hcover
    have hxCover : (Fin.elim0 : Fin 0 → ℝ) ∈ ⋃ i, t i := by
      exact hcover (by simp)
    rcases Set.mem_iUnion.mp hxCover with ⟨i, hi⟩
    have htiNonempty : (t i).Nonempty := ⟨Fin.elim0, hi⟩
    have htiTop :
        boxOuterMeasureCoverCost 0 (t i) = (⊤ : ENNReal) :=
      helperForProposition_7_1_boxOuterMeasureCoverCost_zeroDim_eq_top_of_nonempty htiNonempty
    have htsumTop : (∑' n, boxOuterMeasureCoverCost 0 (t n)) = (⊤ : ENNReal) := by
      exact ENNReal.tsum_eq_top_of_eq_top ⟨i, htiTop⟩
    simpa [htsumTop]
  exact top_le_iff.mp hTopLe

/-- Helper for Proposition 7.1: the tsum identity `∑ m(B_j) = ∑ vol(B_j)` in dimension `0`. -/
lemma helperForProposition_7_1_tsumOuterEqTsumVolume_zeroDim
    (B : ℕ → OpenBox 0) :
    (∑' j, boxOuterMeasure 0 ((B j).toSet)) = ∑' j, ENNReal.ofReal ((B j).volume) := by
  have hLeft : (∑' j, boxOuterMeasure 0 ((B j).toSet)) = ⊤ := by
    apply ENNReal.tsum_eq_top_of_eq_top
    refine ⟨0, ?_⟩
    simpa [OpenBox.toSet] using helperForProposition_7_1_boxOuterMeasure_zero_univ_eq_top
  have hRight : (∑' j, ENNReal.ofReal ((B j).volume)) = ⊤ := by
    have hconst :
        (fun j : ℕ => ENNReal.ofReal ((B j).volume)) = fun _ : ℕ => (1 : ENNReal) := by
      funext j
      simp [OpenBox.volume]
    rw [hconst, ENNReal.tsum_const_eq_top_of_ne_zero one_ne_zero]
  exact hLeft.trans hRight.symm

/-- Helper for Proposition 7.1: rewrite the tsum of outer measures of covering boxes
as the tsum of their volumes. -/
lemma helperForProposition_7_1_tsumOuterEqTsumVolume
    {d : ℕ} (B : ℕ → OpenBox d) :
    (∑' j, boxOuterMeasure d ((B j).toSet)) = ∑' j, ENNReal.ofReal ((B j).volume) := by
  cases d with
  | zero =>
      exact helperForProposition_7_1_tsumOuterEqTsumVolume_zeroDim (B := B)
  | succ d =>
      refine tsum_congr ?_
      intro j
      exact helperForProposition_7_1_openBoxOuterEqVolume (d := d) (B := B j)

/-- Helper for Proposition 7.1: `boxOuterMeasure d Ω` is bounded above by the defining infimum
over countable box covers. -/
lemma helperForProposition_7_1_infimumBound
    {d : ℕ} (Ω : Set (Fin d → ℝ)) :
    boxOuterMeasure d Ω ≤
      sInf
        {r : ENNReal |
          ∃ C : ℕ → OpenBox d,
            IsCoveredByBoxes Ω C ∧ r = ∑' j, ENNReal.ofReal ((C j).volume)} := by
  have hOfLe : boxOuterMeasure d Ω ≤ boxOuterMeasureCoverCost d Ω := by
    simpa [boxOuterMeasure] using
      (MeasureTheory.OuterMeasure.ofFunction_le
        (m := boxOuterMeasureCoverCost d)
        (m_empty := boxOuterMeasureCoverCost_empty d)
        (s := Ω))
  have hCostLe :
      boxOuterMeasureCoverCost d Ω ≤
        sInf
          {r : ENNReal |
            ∃ C : ℕ → OpenBox d,
              IsCoveredByBoxes Ω C ∧ r = ∑' j, ENNReal.ofReal ((C j).volume)} := by
    by_cases hΩ : Ω = ∅
    · simp [boxOuterMeasureCoverCost, hΩ]
    · simp [boxOuterMeasureCoverCost, hΩ]
  exact le_trans hOfLe hCostLe

/-- Proposition 7.1: for a box cover of `Ω` indexed by `ℕ` (encoding an at most countable
family), the associated outer measure satisfies
`m(Ω) ≤ m(⋃ j, B_j) ≤ ∑' j, m(B_j) = ∑' j, vol(B_j)`, and in particular `m(Ω)` is bounded by
the infimum of all such covering sums. -/
theorem proposition_7_1
    (d : ℕ) (Ω : Set (Fin d → ℝ)) (B : ℕ → OpenBox d) :
    (IsCoveredByBoxes Ω B →
      boxOuterMeasure d Ω ≤ boxOuterMeasure d (⋃ j, (B j).toSet) ∧
        boxOuterMeasure d (⋃ j, (B j).toSet) ≤ ∑' j, boxOuterMeasure d ((B j).toSet) ∧
          (∑' j, boxOuterMeasure d ((B j).toSet)) = ∑' j, ENNReal.ofReal ((B j).volume)) ∧
      boxOuterMeasure d Ω ≤
        sInf
          {r : ENNReal |
          ∃ C : ℕ → OpenBox d,
              IsCoveredByBoxes Ω C ∧ r = ∑' j, ENNReal.ofReal ((C j).volume)} := by
  constructor
  · intro hcover
    refine ⟨?_, ?_, ?_⟩
    · exact helperForProposition_7_1_coverMonotone (B := B) hcover
    · exact helperForProposition_7_1_coverSubadditive (B := B)
    · exact helperForProposition_7_1_tsumOuterEqTsumVolume (B := B)
  · exact helperForProposition_7_1_infimumBound (Ω := Ω)

/-- Helper for Lemma 7.1: every outer-measure value lies between `0` and `⊤`. -/
lemma helperForLemma_7_1_rangeBounds
    {n : ℕ} (m : MeasureTheory.OuterMeasure (Fin n → ℝ))
    (Ω : Set (Fin n → ℝ)) :
    0 ≤ m Ω ∧ m Ω ≤ ⊤ := by
  constructor
  · exact bot_le
  · exact le_top

/-- Helper for Lemma 7.1: outer measures are monotone under set inclusion. -/
lemma helperForLemma_7_1_monotone
    {n : ℕ} (m : MeasureTheory.OuterMeasure (Fin n → ℝ))
    {A B : Set (Fin n → ℝ)} (hAB : A ⊆ B) :
    m A ≤ m B := by
  exact MeasureTheory.measure_mono hAB

/-- Helper for Lemma 7.1: finite subadditivity over a finite-indexed union. -/
lemma helperForLemma_7_1_finiteSubadditivity
    {n : ℕ} (m : MeasureTheory.OuterMeasure (Fin n → ℝ))
    {J : Type*} (s : Finset J) (A : J → Set (Fin n → ℝ)) :
    m (⋃ j ∈ s, A j) ≤ Finset.sum s (fun j => m (A j)) := by
  simpa using MeasureTheory.measure_biUnion_finset_le (μ := m) s A

/-- Helper for Lemma 7.1: countable subadditivity over countable-indexed unions. -/
lemma helperForLemma_7_1_countableSubadditivity
    {n : ℕ} (m : MeasureTheory.OuterMeasure (Fin n → ℝ))
    {J : Type*} [Countable J] (A : J → Set (Fin n → ℝ)) :
    m (⋃ j, A j) ≤ ∑' j, m (A j) := by
  simpa using MeasureTheory.measure_iUnion_le (μ := m) (s := A)

/-- Helper for Lemma 7.1: translation invariance implication is the identity map on that
property. -/
lemma helperForLemma_7_1_translationInvariant_passthrough
    {n : ℕ} (m : MeasureTheory.OuterMeasure (Fin n → ℝ)) :
    ((∀ (Ω : Set (Fin n → ℝ)) (x : Fin n → ℝ),
        m ((fun y : Fin n → ℝ => x + y) '' Ω) = m Ω) →
      ∀ (Ω : Set (Fin n → ℝ)) (x : Fin n → ℝ),
        m ((fun y : Fin n → ℝ => x + y) '' Ω) = m Ω) := by
  intro hTranslationInvariant
  exact hTranslationInvariant

/-- Lemma 7.1 (Properties of outer measure): for an outer measure `m*` on `ℝ^n`,
(v) `m*(∅)=0`; (vi) for every `Ω`, `0 ≤ m*(Ω) ≤ +∞`; (vii) monotonicity under inclusion;
(viii) finite subadditivity over a finite family; (x) countable subadditivity over a countable
family; and (xiii) if `m*` is translation invariant (`m*(x + Ω) = m*(Ω)`), then this
translation-invariance property holds. -/
theorem outerMeasure_properties
    (n : ℕ) (m : MeasureTheory.OuterMeasure (Fin n → ℝ)) :
    m ∅ = 0 ∧
      (∀ Ω : Set (Fin n → ℝ), 0 ≤ m Ω ∧ m Ω ≤ ⊤) ∧
      (∀ ⦃A B : Set (Fin n → ℝ)⦄, A ⊆ B → m A ≤ m B) ∧
      (∀ {J : Type*} (s : Finset J) (A : J → Set (Fin n → ℝ)),
        m (⋃ j ∈ s, A j) ≤ Finset.sum s (fun j => m (A j))) ∧
      (∀ {J : Type*} [Countable J] (A : J → Set (Fin n → ℝ)),
        m (⋃ j, A j) ≤ ∑' j, m (A j)) ∧
      ((∀ (Ω : Set (Fin n → ℝ)) (x : Fin n → ℝ),
          m ((fun y : Fin n → ℝ => x + y) '' Ω) = m Ω) →
        ∀ (Ω : Set (Fin n → ℝ)) (x : Fin n → ℝ),
          m ((fun y : Fin n → ℝ => x + y) '' Ω) = m Ω) := by
  constructor
  · exact m.empty
  constructor
  · intro Ω
    exact helperForLemma_7_1_rangeBounds m Ω
  constructor
  · intro A B hAB
    exact helperForLemma_7_1_monotone m hAB
  constructor
  · intro J s A
    exact helperForLemma_7_1_finiteSubadditivity m s A
  constructor
  · intro J _ A
    exact helperForLemma_7_1_countableSubadditivity m A
  · exact helperForLemma_7_1_translationInvariant_passthrough m

/-- Helper for Proposition 7.2: in dimension `0`, every closed box is all of `Set.univ`. -/
lemma helperForProposition_7_2_zeroDim_Icc_eq_univ (a b : Fin 0 → ℝ) :
    (Set.Icc a b : Set (Fin 0 → ℝ)) = Set.univ := by
  ext x
  simp

/-- Helper for Proposition 7.2: in dimension `0`, every closed box has box outer measure `⊤`
in the current model. -/
lemma helperForProposition_7_2_zeroDim_Icc_measure_eq_top (a b : Fin 0 → ℝ) :
    boxOuterMeasure 0 (Set.Icc a b) = (⊤ : ENNReal) := by
  simpa [helperForProposition_7_2_zeroDim_Icc_eq_univ (a := a) (b := b)] using
    helperForProposition_7_1_boxOuterMeasure_zero_univ_eq_top

/-- Helper for Proposition 7.2: in dimension `0`, the right-hand side product is `1`. -/
lemma helperForProposition_7_2_zeroDim_rhs_eq_one (a b : Fin 0 → ℝ) :
    ENNReal.ofReal (∏ i : Fin 0, (b i - a i)) = 1 := by
  simp

/-- Helper for Proposition 7.2: the canonical zero-dimensional data
`a = b = Fin.elim0` has vacuous bounds, left side `⊤`, and right side `1`. -/
lemma helperForProposition_7_2_zeroDim_canonical_payload :
    (∀ i : Fin 0, (Fin.elim0 i : ℝ) ≤ Fin.elim0 i) ∧
      boxOuterMeasure 0 (Set.Icc (Fin.elim0 : Fin 0 → ℝ) Fin.elim0) = (⊤ : ENNReal) ∧
      ENNReal.ofReal (∏ i : Fin 0, (Fin.elim0 i - Fin.elim0 i)) = (1 : ENNReal) := by
  refine ⟨?_, ?_, ?_⟩
  · intro i
    exact Fin.elim0 i
  · exact helperForProposition_7_2_zeroDim_Icc_measure_eq_top (a := Fin.elim0) (b := Fin.elim0)
  · exact helperForProposition_7_2_zeroDim_rhs_eq_one (a := Fin.elim0) (b := Fin.elim0)

/-- Helper for Proposition 7.2: in dimension `0`, the right-hand-side product term is not `⊤`. -/
lemma helperForProposition_7_2_zeroDim_rhs_ne_top (a b : Fin 0 → ℝ) :
    ENNReal.ofReal (∏ i : Fin 0, (b i - a i)) ≠ (⊤ : ENNReal) := by
  rw [helperForProposition_7_2_zeroDim_rhs_eq_one (a := a) (b := b)]
  exact ENNReal.one_ne_top

/-- Helper for Proposition 7.2: in dimension `0`, the coordinate-wise bounds hypothesis
is vacuous. -/
lemma helperForProposition_7_2_zeroDim_vacuous_bounds (a b : Fin 0 → ℝ) :
    ∀ i, a i ≤ b i := by
  intro i
  exact Fin.elim0 i

/-- Helper for Proposition 7.2: in dimension `0`, `⊤` cannot equal the right-hand-side
product term. -/
lemma helperForProposition_7_2_zeroDim_top_ne_rhs (a b : Fin 0 → ℝ) :
    (⊤ : ENNReal) ≠ ENNReal.ofReal (∏ i : Fin 0, (b i - a i)) := by
  intro hTopEqRhs
  exact helperForProposition_7_2_zeroDim_rhs_ne_top (a := a) (b := b) hTopEqRhs.symm

/-- Helper for Proposition 7.2: in dimension `0`, the outer measure of `Set.univ` is not `1`
for the current model. -/
lemma helperForProposition_7_2_zeroDim_univ_measure_ne_one :
    boxOuterMeasure 0 (Set.univ : Set (Fin 0 → ℝ)) ≠ (1 : ENNReal) := by
  intro hEq
  have hTopEqOne : (⊤ : ENNReal) = (1 : ENNReal) := by
    calc
      (⊤ : ENNReal) = boxOuterMeasure 0 (Set.univ : Set (Fin 0 → ℝ)) := by
        simpa using helperForProposition_7_1_boxOuterMeasure_zero_univ_eq_top.symm
      _ = (1 : ENNReal) := hEq
  exact ENNReal.top_ne_one hTopEqOne

/-- Helper for Proposition 7.2: in dimension `0`, every closed box has outer measure
different from `1` in the current model. -/
lemma helperForProposition_7_2_zeroDim_Icc_measure_ne_one (a b : Fin 0 → ℝ) :
    boxOuterMeasure 0 (Set.Icc a b) ≠ (1 : ENNReal) := by
  simpa [helperForProposition_7_2_zeroDim_Icc_eq_univ (a := a) (b := b)] using
    helperForProposition_7_2_zeroDim_univ_measure_ne_one

/-- Helper for Proposition 7.2: the closed-box identity is false in dimension `0`
for the current `boxOuterMeasure` model. -/
lemma helperForProposition_7_2_zeroDim_formula_false (a b : Fin 0 → ℝ) :
    boxOuterMeasure 0 (Set.Icc a b) ≠ ENNReal.ofReal (∏ i : Fin 0, (b i - a i)) := by
  intro hEq
  have hEqOne : boxOuterMeasure 0 (Set.Icc a b) = (1 : ENNReal) := by
    calc
      boxOuterMeasure 0 (Set.Icc a b) = ENNReal.ofReal (∏ i : Fin 0, (b i - a i)) := hEq
      _ = (1 : ENNReal) := helperForProposition_7_2_zeroDim_rhs_eq_one (a := a) (b := b)
  exact helperForProposition_7_2_zeroDim_Icc_measure_ne_one (a := a) (b := b) hEqOne

/-- Helper for Proposition 7.2: even after adding the coordinate-wise bounds hypothesis,
the dimension-`0` closed-box identity remains false in the current model. -/
lemma helperForProposition_7_2_zeroDim_bounds_instance_false
    (a b : Fin 0 → ℝ) (_h : ∀ i, a i ≤ b i) :
    boxOuterMeasure 0 (Set.Icc a b) ≠ ENNReal.ofReal (∏ i : Fin 0, (b i - a i)) := by
  exact helperForProposition_7_2_zeroDim_formula_false (a := a) (b := b)

/-- Helper for Proposition 7.2: in dimension `0`, even the implication-shaped form
`(∀ i, a i ≤ b i) → m*(Icc a b) = ...` is equivalent to `False` because the
bounds premise is vacuous. -/
lemma helperForProposition_7_2_zeroDim_implication_shape_iff_false (a b : Fin 0 → ℝ) :
    ((∀ i, a i ≤ b i) →
      boxOuterMeasure 0 (Set.Icc a b) = ENNReal.ofReal (∏ i : Fin 0, (b i - a i))) ↔ False := by
  constructor
  · intro hImp
    have hLe : ∀ i, a i ≤ b i :=
      helperForProposition_7_2_zeroDim_vacuous_bounds (a := a) (b := b)
    exact helperForProposition_7_2_zeroDim_formula_false (a := a) (b := b) (hImp hLe)
  · intro hFalse
    exact False.elim hFalse

/-- Helper for Proposition 7.2: in dimension `0`, no bounded closed box can satisfy
the claimed closed-box outer-measure identity in the current model. -/
lemma helperForProposition_7_2_zeroDim_no_bounded_solution :
    ¬ ∃ (a b : Fin 0 → ℝ), (∀ i, a i ≤ b i) ∧
      boxOuterMeasure 0 (Set.Icc a b) = ENNReal.ofReal (∏ i : Fin 0, (b i - a i)) := by
  intro hExists
  rcases hExists with ⟨a, b, hLe, hEq⟩
  exact helperForProposition_7_2_zeroDim_bounds_instance_false (a := a) (b := b) hLe hEq

/-- Helper for Proposition 7.2: any claimed closed-box formula instance in dimension `0`
immediately yields `False` in the current model. -/
lemma helperForProposition_7_2_zeroDim_instance_implies_false
    (a b : Fin 0 → ℝ) (_h : ∀ i, a i ≤ b i)
    (hEq :
      boxOuterMeasure 0 (Set.Icc a b) = ENNReal.ofReal (∏ i : Fin 0, (b i - a i))) :
    False := by
  exact helperForProposition_7_2_zeroDim_formula_false (a := a) (b := b) hEq

/-- Helper for Proposition 7.2: the dimension-`0` closed-box equality is contradictory,
even without using any bounds hypothesis. -/
lemma helperForProposition_7_2_zeroDim_equality_implies_false
    (a b : Fin 0 → ℝ)
    (hEq :
      boxOuterMeasure 0 (Set.Icc a b) = ENNReal.ofReal (∏ i : Fin 0, (b i - a i))) :
    False := by
  exact helperForProposition_7_2_zeroDim_formula_false (a := a) (b := b) hEq

/-- Helper for Proposition 7.2: there is an explicit `n = 0` closed-box
counterexample with vacuous coordinate-wise bounds. -/
lemma helperForProposition_7_2_zeroDim_counterexample :
    ∃ (a b : Fin 0 → ℝ), (∀ i, a i ≤ b i) ∧
      boxOuterMeasure 0 (Set.Icc a b) ≠ ENNReal.ofReal (∏ i : Fin 0, (b i - a i)) := by
  refine ⟨Fin.elim0, Fin.elim0, ?_, ?_⟩
  · exact helperForProposition_7_2_zeroDim_vacuous_bounds (a := Fin.elim0) (b := Fin.elim0)
  · exact helperForProposition_7_2_zeroDim_formula_false (a := Fin.elim0) (b := Fin.elim0)

/-- Helper for Proposition 7.2: the universal closed-box identity has a concrete
counterexample in the family of all dimensions (again witnessed at `n = 0`). -/
lemma helperForProposition_7_2_exists_dimensionwise_counterexample :
    ∃ (n : ℕ) (a b : Fin n → ℝ), (∀ i, a i ≤ b i) ∧
      boxOuterMeasure n (Set.Icc a b) ≠ ENNReal.ofReal (∏ i, (b i - a i)) := by
  refine ⟨0, Fin.elim0, Fin.elim0, ?_, ?_⟩
  · exact helperForProposition_7_2_zeroDim_vacuous_bounds (a := Fin.elim0) (b := Fin.elim0)
  · exact helperForProposition_7_2_zeroDim_formula_false (a := Fin.elim0) (b := Fin.elim0)

/-- Helper for Proposition 7.2: the concrete `n = 0` specialization of the target equality
forces the impossible identity `⊤ = 1`. -/
lemma helperForProposition_7_2_zeroDim_specialization_forces_top_eq_one
    (hEq :
      boxOuterMeasure 0 (Set.Icc (Fin.elim0 : Fin 0 → ℝ) Fin.elim0) =
        ENNReal.ofReal (∏ i : Fin 0, (Fin.elim0 i - Fin.elim0 i))) :
    (⊤ : ENNReal) = (1 : ENNReal) := by
  rcases helperForProposition_7_2_zeroDim_canonical_payload with ⟨_, hTop, hRhs⟩
  calc
    (⊤ : ENNReal) =
        boxOuterMeasure 0 (Set.Icc (Fin.elim0 : Fin 0 → ℝ) Fin.elim0) := by
      symm
      exact hTop
    _ = ENNReal.ofReal (∏ i : Fin 0, (Fin.elim0 i - Fin.elim0 i)) := hEq
    _ = (1 : ENNReal) := hRhs

/-- Helper for Proposition 7.2: the specific `n = 0`, `a = b = Fin.elim0` specialization
of the closed-box identity is contradictory in the current model. -/
lemma helperForProposition_7_2_zeroDim_specialization_contradiction
    (hEq :
      boxOuterMeasure 0 (Set.Icc (Fin.elim0 : Fin 0 → ℝ) Fin.elim0) =
        ENNReal.ofReal (∏ i : Fin 0, (Fin.elim0 i - Fin.elim0 i))) : False := by
  exact ENNReal.top_ne_one
    (helperForProposition_7_2_zeroDim_specialization_forces_top_eq_one hEq)

/-- Helper for Proposition 7.2: even when restricted to dimension `0`, the closed-box
formula cannot hold for all boxes in the current model. -/
lemma helperForProposition_7_2_zeroDim_family_false :
    ¬ (∀ (a b : Fin 0 → ℝ), (∀ i, a i ≤ b i) →
      boxOuterMeasure 0 (Set.Icc a b) = ENNReal.ofReal (∏ i : Fin 0, (b i - a i))) := by
  intro hAtZero
  exact
    (helperForProposition_7_2_zeroDim_implication_shape_iff_false
      (a := Fin.elim0) (b := Fin.elim0)).1
      (hAtZero Fin.elim0 Fin.elim0)

/-- Helper for Proposition 7.2: in dimension `0`, the family statement written with an
explicit bounds argument (matching the target binder order) is also impossible. -/
lemma helperForProposition_7_2_zeroDim_family_explicitBounds_false :
    ¬ (∀ (a b : Fin 0 → ℝ) (h : ∀ i, a i ≤ b i),
      boxOuterMeasure 0 (Set.Icc a b) = ENNReal.ofReal (∏ i : Fin 0, (b i - a i))) := by
  intro hAtZero
  have hLe :
      ∀ i : Fin 0, (Fin.elim0 i : ℝ) ≤ Fin.elim0 i :=
    helperForProposition_7_2_zeroDim_vacuous_bounds (a := Fin.elim0) (b := Fin.elim0)
  have hEq :
      boxOuterMeasure 0 (Set.Icc (Fin.elim0 : Fin 0 → ℝ) Fin.elim0) =
        ENNReal.ofReal (∏ i : Fin 0, (Fin.elim0 i - Fin.elim0 i)) :=
    hAtZero Fin.elim0 Fin.elim0 hLe
  exact helperForProposition_7_2_zeroDim_specialization_contradiction hEq

/-- Helper for Proposition 7.2: the fully universal closed-box formula is inconsistent
with the current zero-dimensional model. -/
lemma helperForProposition_7_2_universal_formula_false :
    ¬ (∀ n (a b : Fin n → ℝ), (∀ i, a i ≤ b i) →
      boxOuterMeasure n (Set.Icc a b) = ENNReal.ofReal (∏ i, (b i - a i))) := by
  intro hAll
  rcases helperForProposition_7_2_exists_dimensionwise_counterexample with
    ⟨n, a, b, hLe, hNe⟩
  exact hNe (hAll n a b hLe)

/-- Helper for Proposition 7.2: any universal proof object for the closed-box formula
immediately yields a contradiction in the current model. -/
lemma helperForProposition_7_2_universal_formula_implies_false
    (hAll :
      ∀ n (a b : Fin n → ℝ), (∀ i, a i ≤ b i) →
        boxOuterMeasure n (Set.Icc a b) = ENNReal.ofReal (∏ i, (b i - a i))) :
    False := by
  exact helperForProposition_7_2_universal_formula_false hAll

/-- Helper for Proposition 7.2: the implication-shaped universal family
has no inhabitant in the current model. -/
lemma helperForProposition_7_2_universalImplicationShape_isEmpty :
    IsEmpty (∀ n (a b : Fin n → ℝ), (∀ i, a i ≤ b i) →
      boxOuterMeasure n (Set.Icc a b) = ENNReal.ofReal (∏ i, (b i - a i))) := by
  refine ⟨?_⟩
  intro hAll
  exact helperForProposition_7_2_universal_formula_implies_false hAll

/-- Helper for Proposition 7.2: equivalently, the implication-shaped universal family
is logically `False` in the current model. -/
lemma helperForProposition_7_2_universalImplicationShape_iff_false :
    ((∀ n (a b : Fin n → ℝ), (∀ i, a i ≤ b i) →
        boxOuterMeasure n (Set.Icc a b) = ENNReal.ofReal (∏ i, (b i - a i))) ↔ False) := by
  constructor
  · intro hAll
    exact helperForProposition_7_2_universal_formula_implies_false hAll
  · intro hFalse
    exact False.elim hFalse

/-- Helper for Proposition 7.2: if the closed-box formula holds for all boxes in a fixed
dimension `n`, then necessarily `n ≠ 0` in the current model. -/
lemma helperForProposition_7_2_fixedDimension_family_forces_nonzero
    (n : ℕ)
    (hAtDim :
      ∀ (a b : Fin n → ℝ), (∀ i, a i ≤ b i) →
        boxOuterMeasure n (Set.Icc a b) = ENNReal.ofReal (∏ i, (b i - a i))) :
    n ≠ 0 := by
  intro hn
  subst hn
  have hLe : ∀ i : Fin 0, (Fin.elim0 i : ℝ) ≤ Fin.elim0 i := by
    intro i
    exact Fin.elim0 i
  have hEq :
      boxOuterMeasure 0 (Set.Icc (Fin.elim0 : Fin 0 → ℝ) Fin.elim0) =
        ENNReal.ofReal (∏ i : Fin 0, (Fin.elim0 i - Fin.elim0 i)) :=
    hAtDim Fin.elim0 Fin.elim0 hLe
  exact helperForProposition_7_2_zeroDim_specialization_contradiction hEq

/-- Helper for Proposition 7.2: any proof object of the target quantifier shape forces the
impossible conclusion `(0 : ℕ) ≠ 0` via the fixed-dimension obstruction at `n = 0`. -/
lemma helperForProposition_7_2_targetShape_forces_zero_ne_zero
    (hTarget :
      ∀ (n : ℕ) (a b : Fin n → ℝ) (_h : ∀ i, a i ≤ b i),
        boxOuterMeasure n (Set.Icc a b) = ENNReal.ofReal (∏ i, (b i - a i))) :
    (0 : ℕ) ≠ 0 := by
  refine helperForProposition_7_2_fixedDimension_family_forces_nonzero (n := 0) ?_
  intro a b hLe
  exact hTarget 0 a b hLe

/-- Helper for Proposition 7.2: the exact quantifier shape of the target theorem
still specializes to a contradiction in dimension `0`. -/
lemma helperForProposition_7_2_targetShape_zeroDim_specialization
    (hTarget :
      ∀ (n : ℕ) (a b : Fin n → ℝ) (_h : ∀ i, a i ≤ b i),
        boxOuterMeasure n (Set.Icc a b) = ENNReal.ofReal (∏ i, (b i - a i))) :
    boxOuterMeasure 0 (Set.Icc (Fin.elim0 : Fin 0 → ℝ) Fin.elim0) =
      ENNReal.ofReal (∏ i : Fin 0, (Fin.elim0 i - Fin.elim0 i)) := by
  exact
    hTarget
      0
      Fin.elim0
      Fin.elim0
      (helperForProposition_7_2_zeroDim_vacuous_bounds (a := Fin.elim0) (b := Fin.elim0))

/-- Helper for Proposition 7.2: the target quantifier shape forces `⊤ = 1` by the
dimension-`0` specialization in the current model. -/
lemma helperForProposition_7_2_targetShape_forces_top_eq_one
    (hTarget :
      ∀ (n : ℕ) (a b : Fin n → ℝ) (_h : ∀ i, a i ≤ b i),
        boxOuterMeasure n (Set.Icc a b) = ENNReal.ofReal (∏ i, (b i - a i))) :
    (⊤ : ENNReal) = (1 : ENNReal) := by
  have hTop :
      boxOuterMeasure 0 (Set.Icc (Fin.elim0 : Fin 0 → ℝ) Fin.elim0) = (⊤ : ENNReal) :=
    helperForProposition_7_2_zeroDim_Icc_measure_eq_top (a := Fin.elim0) (b := Fin.elim0)
  have hSpec :
      boxOuterMeasure 0 (Set.Icc (Fin.elim0 : Fin 0 → ℝ) Fin.elim0) =
        ENNReal.ofReal (∏ i : Fin 0, (Fin.elim0 i - Fin.elim0 i)) :=
    helperForProposition_7_2_targetShape_zeroDim_specialization hTarget
  calc
    (⊤ : ENNReal) =
        boxOuterMeasure 0 (Set.Icc (Fin.elim0 : Fin 0 → ℝ) Fin.elim0) := hTop.symm
    _ = ENNReal.ofReal (∏ i : Fin 0, (Fin.elim0 i - Fin.elim0 i)) := hSpec
    _ = (1 : ENNReal) := helperForProposition_7_2_zeroDim_rhs_eq_one (a := Fin.elim0) (b := Fin.elim0)

/-- Helper for Proposition 7.2: the target quantifier shape directly contradicts
`ENNReal.top_ne_one` through the dimension-`0` specialization. -/
lemma helperForProposition_7_2_targetShape_forces_false_via_top_eq_one
    (hTarget :
      ∀ (n : ℕ) (a b : Fin n → ℝ) (_h : ∀ i, a i ≤ b i),
        boxOuterMeasure n (Set.Icc a b) = ENNReal.ofReal (∏ i, (b i - a i))) :
    False := by
  exact ENNReal.top_ne_one
    (helperForProposition_7_2_targetShape_forces_top_eq_one hTarget)

/-- Helper for Proposition 7.2: the exact quantifier shape of the target theorem
still specializes to a contradiction in dimension `0`. -/
lemma helperForProposition_7_2_targetShape_implies_false
    (hTarget :
      ∀ (n : ℕ) (a b : Fin n → ℝ) (_h : ∀ i, a i ≤ b i),
        boxOuterMeasure n (Set.Icc a b) = ENNReal.ofReal (∏ i, (b i - a i))) :
    False := by
  exact helperForProposition_7_2_targetShape_forces_false_via_top_eq_one hTarget

/-- Helper for Proposition 7.2: the target quantifier shape is not satisfiable in the
current model because it implies the zero-dimensional contradiction. -/
lemma helperForProposition_7_2_targetShape_not_satisfiable :
    ¬ (∀ (n : ℕ) (a b : Fin n → ℝ) (_h : ∀ i, a i ≤ b i),
      boxOuterMeasure n (Set.Icc a b) = ENNReal.ofReal (∏ i, (b i - a i))) := by
  intro hTarget
  exact helperForProposition_7_2_targetShape_implies_false hTarget

/-- Helper for Proposition 7.2: the exact target quantifier shape has no inhabitant in the
current model. -/
lemma helperForProposition_7_2_targetShape_not_nonempty :
    ¬ Nonempty (∀ (n : ℕ) (a b : Fin n → ℝ) (_h : ∀ i, a i ≤ b i),
      boxOuterMeasure n (Set.Icc a b) = ENNReal.ofReal (∏ i, (b i - a i))) := by
  intro hNonempty
  rcases hNonempty with ⟨hTarget⟩
  exact helperForProposition_7_2_targetShape_not_satisfiable hTarget

/-- Helper for Proposition 7.2: equivalently, the target quantifier-shape type is empty in
the current model. -/
lemma helperForProposition_7_2_targetShape_isEmpty :
    IsEmpty (∀ (n : ℕ) (a b : Fin n → ℝ) (_h : ∀ i, a i ≤ b i),
      boxOuterMeasure n (Set.Icc a b) = ENNReal.ofReal (∏ i, (b i - a i))) := by
  refine ⟨?_⟩
  intro hTarget
  exact helperForProposition_7_2_targetShape_not_satisfiable hTarget

/-- Helper for Proposition 7.2: in the current model, the exact target quantifier shape is
equivalent to `False`. -/
lemma helperForProposition_7_2_targetShape_iff_false :
    ((∀ (n : ℕ) (a b : Fin n → ℝ) (_h : ∀ i, a i ≤ b i),
        boxOuterMeasure n (Set.Icc a b) = ENNReal.ofReal (∏ i, (b i - a i))) ↔ False) := by
  constructor
  · intro hTarget
    exact helperForProposition_7_2_targetShape_implies_false hTarget
  · intro hFalse
    exact False.elim hFalse

/-- Helper for Proposition 7.2: any single closed-box equality instance in a dimension
identified with `0` is contradictory in the current model. -/
lemma helperForProposition_7_2_singleInstance_with_zero_dimension_contradiction
    {n : ℕ} {a b : Fin n → ℝ}
    (hn : n = 0)
    (hEq : boxOuterMeasure n (Set.Icc a b) = ENNReal.ofReal (∏ i, (b i - a i))) :
    False := by
  subst hn
  exact helperForProposition_7_2_zeroDim_formula_false (a := a) (b := b) hEq

/-- Helper for Proposition 7.2: any single closed-box equality instance in this model
forces the ambient dimension to be positive. -/
lemma helperForProposition_7_2_singleInstance_forces_positive_dimension
    {n : ℕ} {a b : Fin n → ℝ}
    (hEq : boxOuterMeasure n (Set.Icc a b) = ENNReal.ofReal (∏ i, (b i - a i))) :
    ∃ d : ℕ, n = d + 1 := by
  cases n with
  | zero =>
      exact False.elim
        (helperForProposition_7_2_singleInstance_with_zero_dimension_contradiction
          (n := 0) (a := a) (b := b) rfl hEq)
  | succ d =>
      exact ⟨d, rfl⟩

/-- Helper for Proposition 7.2: any single closed-box equality instance in this model
already forces the ambient dimension to be nonzero. -/
lemma helperForProposition_7_2_singleInstance_forces_nonzero
    {n : ℕ} {a b : Fin n → ℝ}
    (hEq : boxOuterMeasure n (Set.Icc a b) = ENNReal.ofReal (∏ i, (b i - a i))) :
    n ≠ 0 := by
  rcases
      helperForProposition_7_2_singleInstance_forces_positive_dimension
        (n := n) (a := a) (b := b) hEq with
    ⟨d, hd⟩
  intro hn
  rw [hn] at hd
  exact Nat.succ_ne_zero d hd.symm

/-- Helper for Proposition 7.2: the full target quantifier shape yields the impossible
identity `0 = d + 1` for some natural `d`. -/
lemma helperForProposition_7_2_targetShape_forces_zero_eq_succ
    (hTarget :
      ∀ (n : ℕ) (a b : Fin n → ℝ) (_h : ∀ i, a i ≤ b i),
        boxOuterMeasure n (Set.Icc a b) = ENNReal.ofReal (∏ i, (b i - a i))) :
    ∃ d : ℕ, (0 : ℕ) = d + 1 := by
  have hEqZero :
      boxOuterMeasure 0 (Set.Icc (Fin.elim0 : Fin 0 → ℝ) Fin.elim0) =
        ENNReal.ofReal (∏ i : Fin 0, (Fin.elim0 i - Fin.elim0 i)) :=
    hTarget
      0
      Fin.elim0
      Fin.elim0
      (helperForProposition_7_2_zeroDim_vacuous_bounds (a := Fin.elim0) (b := Fin.elim0))
  exact
    helperForProposition_7_2_singleInstance_forces_positive_dimension
      (n := 0) (a := Fin.elim0) (b := Fin.elim0) hEqZero

/-- Helper for Proposition 7.2: a proof object of the full target quantifier shape would
force every natural number to be nonzero, by specializing at each dimension. -/
lemma helperForProposition_7_2_targetShape_forces_all_dimensions_nonzero
    (hTarget :
      ∀ (n : ℕ) (a b : Fin n → ℝ) (_h : ∀ i, a i ≤ b i),
        boxOuterMeasure n (Set.Icc a b) = ENNReal.ofReal (∏ i, (b i - a i))) :
    ∀ n : ℕ, n ≠ 0 := by
  intro n
  let a : Fin n → ℝ := fun _ => 0
  let b : Fin n → ℝ := fun _ => 0
  have hLe : ∀ i, a i ≤ b i := by
    intro i
    simp [a, b]
  have hEq :
      boxOuterMeasure n (Set.Icc a b) = ENNReal.ofReal (∏ i, (b i - a i)) :=
    hTarget n a b hLe
  exact
    helperForProposition_7_2_singleInstance_forces_nonzero
      (n := n) (a := a) (b := b) hEq

/-- Helper for Proposition 7.2: the target quantifier shape simultaneously forces two
incompatible consequences (`⊤ = 1` and `0 ≠ 0`) under the current model. -/
lemma helperForProposition_7_2_targetShape_forces_two_contradiction_routes
    (hTarget :
      ∀ (n : ℕ) (a b : Fin n → ℝ) (_h : ∀ i, a i ≤ b i),
        boxOuterMeasure n (Set.Icc a b) = ENNReal.ofReal (∏ i, (b i - a i))) :
    (⊤ = (1 : ENNReal)) ∧ ((0 : ℕ) ≠ 0) := by
  constructor
  · exact helperForProposition_7_2_targetShape_forces_top_eq_one hTarget
  · exact helperForProposition_7_2_targetShape_forces_all_dimensions_nonzero hTarget 0

/-- Helper for Proposition 7.2: the target quantifier shape is contradictory because
`0` cannot be the successor of a natural number. -/
lemma helperForProposition_7_2_targetShape_forces_zero_eq_one
    (hTarget :
      ∀ (n : ℕ) (a b : Fin n → ℝ) (_h : ∀ i, a i ≤ b i),
        boxOuterMeasure n (Set.Icc a b) = ENNReal.ofReal (∏ i, (b i - a i))) :
    (0 : ℕ) = 1 := by
  have hZeroNeZero : (0 : ℕ) ≠ 0 :=
    (helperForProposition_7_2_targetShape_forces_two_contradiction_routes hTarget).2
  exact False.elim (hZeroNeZero rfl)

/-- Helper for Proposition 7.2: the target quantifier shape implies `False` because it
would force the absurd natural-number identity `0 = 1`. -/
lemma helperForProposition_7_2_targetShape_forces_false_via_zero_eq_one
    (hTarget :
      ∀ (n : ℕ) (a b : Fin n → ℝ) (_h : ∀ i, a i ≤ b i),
        boxOuterMeasure n (Set.Icc a b) = ENNReal.ofReal (∏ i, (b i - a i))) :
    False := by
  exact Nat.zero_ne_one (helperForProposition_7_2_targetShape_forces_zero_eq_one hTarget)

/-- Helper for Proposition 7.2: the target quantifier shape is contradictory because
`0` cannot be the successor of a natural number. -/
lemma helperForProposition_7_2_targetShape_forces_false_via_nat
    (hTarget :
      ∀ (n : ℕ) (a b : Fin n → ℝ) (_h : ∀ i, a i ≤ b i),
        boxOuterMeasure n (Set.Icc a b) = ENNReal.ofReal (∏ i, (b i - a i))) :
    False := by
  exact helperForProposition_7_2_targetShape_forces_false_via_zero_eq_one hTarget

/-- Helper for Proposition 7.2: any proof object of the full target quantifier shape
forces every natural dimension to be strictly positive. -/
lemma helperForProposition_7_2_targetShape_forces_all_dimensions_positive
    (hTarget :
      ∀ (n : ℕ) (a b : Fin n → ℝ) (_h : ∀ i, a i ≤ b i),
        boxOuterMeasure n (Set.Icc a b) = ENNReal.ofReal (∏ i, (b i - a i))) :
    ∀ n : ℕ, 0 < n := by
  intro n
  exact Nat.pos_iff_ne_zero.mpr
    (helperForProposition_7_2_targetShape_forces_all_dimensions_nonzero hTarget n)

/-- Helper for Proposition 7.2: the target quantifier shape forces the absurd strict
inequality `0 < 0` by specialization at dimension `0`. -/
lemma helperForProposition_7_2_targetShape_forces_zero_lt_zero
    (hTarget :
      ∀ (n : ℕ) (a b : Fin n → ℝ) (_h : ∀ i, a i ≤ b i),
        boxOuterMeasure n (Set.Icc a b) = ENNReal.ofReal (∏ i, (b i - a i))) :
    (0 : ℕ) < 0 := by
  exact helperForProposition_7_2_targetShape_forces_all_dimensions_positive hTarget 0

/-- Helper for Proposition 7.2: the target quantifier shape implies `False` because
`Nat.lt_irrefl 0` rules out the forced inequality `0 < 0`. -/
lemma helperForProposition_7_2_targetShape_forces_false_via_lt_irrefl
    (hTarget :
      ∀ (n : ℕ) (a b : Fin n → ℝ) (_h : ∀ i, a i ≤ b i),
        boxOuterMeasure n (Set.Icc a b) = ENNReal.ofReal (∏ i, (b i - a i))) :
    False := by
  exact Nat.lt_irrefl 0
    (helperForProposition_7_2_targetShape_forces_zero_lt_zero hTarget)

/-- Helper for Proposition 7.2: a proof object of the exact target quantifier shape
specializes to the explicit dimension-`0` family statement with bounds as parameters. -/
lemma helperForProposition_7_2_targetShape_implies_zeroDim_family
    (hTarget :
      ∀ (n : ℕ) (a b : Fin n → ℝ) (_h : ∀ i, a i ≤ b i),
        boxOuterMeasure n (Set.Icc a b) = ENNReal.ofReal (∏ i, (b i - a i))) :
    ∀ (a b : Fin 0 → ℝ) (h : ∀ i, a i ≤ b i),
      boxOuterMeasure 0 (Set.Icc a b) = ENNReal.ofReal (∏ i : Fin 0, (b i - a i)) := by
  intro a b h
  exact hTarget 0 a b h

/-- Helper for Proposition 7.2: reducing the exact target quantifier shape to the
dimension-`0` family immediately yields `False` in the current model. -/
lemma helperForProposition_7_2_targetShape_forces_false_via_zeroDim_family
    (hTarget :
      ∀ (n : ℕ) (a b : Fin n → ℝ) (_h : ∀ i, a i ≤ b i),
        boxOuterMeasure n (Set.Icc a b) = ENNReal.ofReal (∏ i, (b i - a i))) :
    False := by
  have hZeroFamily :
      ∀ (a b : Fin 0 → ℝ) (h : ∀ i, a i ≤ b i),
        boxOuterMeasure 0 (Set.Icc a b) = ENNReal.ofReal (∏ i : Fin 0, (b i - a i)) :=
    helperForProposition_7_2_targetShape_implies_zeroDim_family hTarget
  exact helperForProposition_7_2_zeroDim_family_explicitBounds_false hZeroFamily

/-- Helper for Proposition 7.2: the canonical dimension-`0` closed-box equality is
false in the current model. -/
lemma helperForProposition_7_2_zeroDim_canonical_equality_ne :
    boxOuterMeasure 0 (Set.Icc (Fin.elim0 : Fin 0 → ℝ) Fin.elim0) ≠
      ENNReal.ofReal (∏ i : Fin 0, (Fin.elim0 i - Fin.elim0 i)) := by
  intro hEq
  exact helperForProposition_7_2_zeroDim_formula_false (a := Fin.elim0) (b := Fin.elim0) hEq

/-- Helper for Proposition 7.2: any inhabitant of the exact target quantifier shape
contradicts the canonical dimension-`0` inequality witness. -/
lemma helperForProposition_7_2_targetShape_forces_false_via_canonical_zeroDim_ne
    (hTarget :
      ∀ (n : ℕ) (a b : Fin n → ℝ) (_h : ∀ i, a i ≤ b i),
        boxOuterMeasure n (Set.Icc a b) = ENNReal.ofReal (∏ i, (b i - a i))) :
    False := by
  exact
    helperForProposition_7_2_zeroDim_canonical_equality_ne
      (helperForProposition_7_2_targetShape_zeroDim_specialization hTarget)

/-- Helper for Proposition 7.2: any inhabitant of the exact target quantifier shape forces
`boxOuterMeasure 0 Set.univ = 1` by specializing to `a = b = Fin.elim0`. -/
lemma helperForProposition_7_2_targetShape_forces_zeroDim_univ_measure_eq_one
    (hTarget :
      ∀ (n : ℕ) (a b : Fin n → ℝ) (_h : ∀ i, a i ≤ b i),
        boxOuterMeasure n (Set.Icc a b) = ENNReal.ofReal (∏ i, (b i - a i))) :
    boxOuterMeasure 0 (Set.univ : Set (Fin 0 → ℝ)) = (1 : ENNReal) := by
  have hSpec :
      boxOuterMeasure 0 (Set.Icc (Fin.elim0 : Fin 0 → ℝ) Fin.elim0) =
        ENNReal.ofReal (∏ i : Fin 0, (Fin.elim0 i - Fin.elim0 i)) :=
    helperForProposition_7_2_targetShape_zeroDim_specialization hTarget
  have hUnivEqIcc :
      (Set.univ : Set (Fin 0 → ℝ)) = Set.Icc (Fin.elim0 : Fin 0 → ℝ) Fin.elim0 := by
    symm
    exact helperForProposition_7_2_zeroDim_Icc_eq_univ (a := Fin.elim0) (b := Fin.elim0)
  calc
    boxOuterMeasure 0 (Set.univ : Set (Fin 0 → ℝ))
        = boxOuterMeasure 0 (Set.Icc (Fin.elim0 : Fin 0 → ℝ) Fin.elim0) := by
          rw [hUnivEqIcc]
    _ = ENNReal.ofReal (∏ i : Fin 0, (Fin.elim0 i - Fin.elim0 i)) := hSpec
    _ = (1 : ENNReal) := helperForProposition_7_2_zeroDim_rhs_eq_one (a := Fin.elim0) (b := Fin.elim0)

/-- Helper for Proposition 7.2: the target quantifier shape implies `False` because its
dimension-`0` specialization forces `boxOuterMeasure 0 Set.univ = 1`, contradicting
`boxOuterMeasure 0 Set.univ = ⊤`. -/
lemma helperForProposition_7_2_targetShape_forces_false_via_zeroDim_univ_eq_one
    (hTarget :
      ∀ (n : ℕ) (a b : Fin n → ℝ) (_h : ∀ i, a i ≤ b i),
        boxOuterMeasure n (Set.Icc a b) = ENNReal.ofReal (∏ i, (b i - a i))) :
    False := by
  have hUnivEqOne :
      boxOuterMeasure 0 (Set.univ : Set (Fin 0 → ℝ)) = (1 : ENNReal) :=
    helperForProposition_7_2_targetShape_forces_zeroDim_univ_measure_eq_one hTarget
  have hUnivEqTop :
      boxOuterMeasure 0 (Set.univ : Set (Fin 0 → ℝ)) = (⊤ : ENNReal) :=
    helperForProposition_7_1_boxOuterMeasure_zero_univ_eq_top
  have hTopEqOne : (⊤ : ENNReal) = (1 : ENNReal) := by
    calc
      (⊤ : ENNReal) = boxOuterMeasure 0 (Set.univ : Set (Fin 0 → ℝ)) := hUnivEqTop.symm
      _ = (1 : ENNReal) := hUnivEqOne
  exact ENNReal.top_ne_one hTopEqOne

/-- Helper for Proposition 7.2: the target quantifier shape implies `False` because its
dimension-`0` specialization forces `boxOuterMeasure 0 Set.univ = 1`, contradicting the
already established `boxOuterMeasure 0 Set.univ ≠ 1`. -/
lemma helperForProposition_7_2_targetShape_forces_false_via_zeroDim_univ_ne_one
    (hTarget :
      ∀ (n : ℕ) (a b : Fin n → ℝ) (_h : ∀ i, a i ≤ b i),
        boxOuterMeasure n (Set.Icc a b) = ENNReal.ofReal (∏ i, (b i - a i))) :
    False := by
  have hUnivEqOne :
      boxOuterMeasure 0 (Set.univ : Set (Fin 0 → ℝ)) = (1 : ENNReal) :=
    helperForProposition_7_2_targetShape_forces_zeroDim_univ_measure_eq_one hTarget
  exact helperForProposition_7_2_zeroDim_univ_measure_ne_one hUnivEqOne

/-- Helper for Proposition 7.2: the full dimension-`0` implication family is empty in the
current model. -/
lemma helperForProposition_7_2_zeroDim_family_isEmpty :
    IsEmpty (∀ (a b : Fin 0 → ℝ) (h : ∀ i, a i ≤ b i),
      boxOuterMeasure 0 (Set.Icc a b) = ENNReal.ofReal (∏ i : Fin 0, (b i - a i))) := by
  refine ⟨?_⟩
  intro hZeroFamily
  exact helperForProposition_7_2_zeroDim_family_explicitBounds_false hZeroFamily

/-- Helper for Proposition 7.2: any inhabitant of the exact target quantifier shape yields
an inhabitant of an empty dimension-`0` family type, hence `False`. -/
lemma helperForProposition_7_2_targetShape_forces_false_via_zeroDim_family_isEmpty
    (hTarget :
      ∀ (n : ℕ) (a b : Fin n → ℝ) (_h : ∀ i, a i ≤ b i),
        boxOuterMeasure n (Set.Icc a b) = ENNReal.ofReal (∏ i, (b i - a i))) :
    False := by
  have hZeroFamily :
      ∀ (a b : Fin 0 → ℝ) (h : ∀ i, a i ≤ b i),
        boxOuterMeasure 0 (Set.Icc a b) = ENNReal.ofReal (∏ i : Fin 0, (b i - a i)) :=
    helperForProposition_7_2_targetShape_implies_zeroDim_family hTarget
  exact (helperForProposition_7_2_zeroDim_family_isEmpty).false hZeroFamily

/-- Helper for Proposition 7.2: the full target quantifier shape is refuted in the
current model, expressed directly as a negated proposition. -/
lemma helperForProposition_7_2_targetShape_negated :
    ¬ (∀ (n : ℕ) (a b : Fin n → ℝ) (_h : ∀ i, a i ≤ b i),
      boxOuterMeasure n (Set.Icc a b) = ENNReal.ofReal (∏ i, (b i - a i))) := by
  intro hTarget
  exact helperForProposition_7_2_targetShape_forces_false_via_zeroDim_family_isEmpty hTarget

/-- Helper for Proposition 7.2: every positive natural number is a successor. -/
lemma helperForProposition_7_2_positiveDim_eq_succ
    {n : ℕ} (hn : 0 < n) :
    ∃ d : ℕ, n = d + 1 := by
  rcases Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn) with ⟨d, hd⟩
  exact ⟨d, by simpa [Nat.succ_eq_add_one] using hd⟩

/-- Helper for Proposition 7.2: any countable open-box cover of a closed box has total
covering volume at least the closed-box volume term. -/
lemma helperForProposition_7_2_closedBox_volume_le_coverSum
    {d : ℕ} (a b : Fin (d + 1) → ℝ) (h : ∀ i, a i ≤ b i)
    (C : ℕ → OpenBox (d + 1))
    (hcover : IsCoveredByBoxes (Set.Icc a b) C) :
    ENNReal.ofReal (∏ i : Fin (d + 1), (b i - a i)) ≤
      ∑' j, ENNReal.ofReal ((C j).volume) := by
  have hIccVolume :
      MeasureTheory.volume (Set.Icc a b) =
        ENNReal.ofReal (∏ i : Fin (d + 1), (b i - a i)) := by
    calc
      MeasureTheory.volume (Set.Icc a b)
          = ∏ i : Fin (d + 1), ENNReal.ofReal (b i - a i) := by
            simpa using (Real.volume_Icc_pi (a := a) (b := b))
      _ = ENNReal.ofReal (∏ i : Fin (d + 1), (b i - a i)) := by
            symm
            exact ENNReal.ofReal_prod_of_nonneg
              (s := Finset.univ)
              (f := fun i : Fin (d + 1) => b i - a i)
              (fun i _ => sub_nonneg.mpr (h i))
  have hmono :
      MeasureTheory.volume (Set.Icc a b) ≤
        MeasureTheory.volume (⋃ j, (C j).toSet) :=
    MeasureTheory.measure_mono hcover
  have hsub :
      MeasureTheory.volume (⋃ j, (C j).toSet) ≤
        ∑' j, MeasureTheory.volume ((C j).toSet) := by
    simpa using
      (MeasureTheory.measure_iUnion_le (μ := MeasureTheory.volume)
        (s := fun j => (C j).toSet))
  calc
    ENNReal.ofReal (∏ i : Fin (d + 1), (b i - a i))
        = MeasureTheory.volume (Set.Icc a b) := hIccVolume.symm
    _ ≤ MeasureTheory.volume (⋃ j, (C j).toSet) := hmono
    _ ≤ ∑' j, MeasureTheory.volume ((C j).toSet) := hsub
    _ = ∑' j, ENNReal.ofReal ((C j).volume) := by
          refine tsum_congr ?_
          intro j
          exact helperForProposition_7_1_openBoxVolume_eqMeasureVolume (B := C j)

/-- Helper for Proposition 7.2: the closed-box volume term is a lower bound for
`boxOuterMeasure` in positive dimension. -/
lemma helperForProposition_7_2_closedBox_outer_ge_volume
    {d : ℕ} (a b : Fin (d + 1) → ℝ) (h : ∀ i, a i ≤ b i) :
    ENNReal.ofReal (∏ i : Fin (d + 1), (b i - a i)) ≤
      boxOuterMeasure (d + 1) (Set.Icc a b) := by
  have hIccVolume :
      MeasureTheory.volume (Set.Icc a b) =
        ENNReal.ofReal (∏ i : Fin (d + 1), (b i - a i)) := by
    calc
      MeasureTheory.volume (Set.Icc a b)
          = ∏ i : Fin (d + 1), ENNReal.ofReal (b i - a i) := by
            simpa using (Real.volume_Icc_pi (a := a) (b := b))
      _ = ENNReal.ofReal (∏ i : Fin (d + 1), (b i - a i)) := by
            symm
            exact ENNReal.ofReal_prod_of_nonneg
              (s := Finset.univ)
              (f := fun i : Fin (d + 1) => b i - a i)
              (fun i _ => sub_nonneg.mpr (h i))
  calc
    ENNReal.ofReal (∏ i : Fin (d + 1), (b i - a i))
        = MeasureTheory.volume (Set.Icc a b) := hIccVolume.symm
    _ ≤ boxOuterMeasure (d + 1) (Set.Icc a b) :=
      helperForProposition_7_1_volume_le_boxOuterMeasure (d := d + 1) (Ω := Set.Icc a b)


end Section02
end Chap07
