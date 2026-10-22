/-
Authors: Zichen Wang, Wanli Ma, Qiming Dai, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Mathlib

open scoped BigOperators

/-- By cardinality, there exists a subset of `ℝ` that is not measurable. -/
lemma exists_notMeasurableSet_real :
    ∃ E : Set ℝ, ¬ MeasurableSet E := by
  by_contra hExists
  push_neg at hExists
  have hCountable : Set.Countable (MeasurableSpace.countableGeneratingSet ℝ) :=
    MeasurableSpace.countable_countableGeneratingSet (α := ℝ)
  have hGeneratorCard :
      Cardinal.mk (MeasurableSpace.countableGeneratingSet ℝ) ≤ Cardinal.continuum := by
    exact hCountable.le_aleph0.trans Cardinal.aleph0_le_continuum
  have hMeasurableCard :
      Cardinal.mk { s : Set ℝ // MeasurableSet s } ≤ Cardinal.continuum := by
    rw [← MeasurableSpace.generateFrom_countableGeneratingSet (α := ℝ)]
    exact MeasurableSpace.cardinal_measurableSet_le_continuum
      (s := MeasurableSpace.countableGeneratingSet ℝ) hGeneratorCard
  have hSetToMeasurable :
      Cardinal.mk (Set ℝ) ≤ Cardinal.mk { s : Set ℝ // MeasurableSet s } := by
    refine Cardinal.mk_le_of_injective
      (f := fun s : Set ℝ => (⟨s, hExists s⟩ : { s : Set ℝ // MeasurableSet s })) ?_
    intro s t hst
    exact congrArg Subtype.val hst
  have hSetCardLeContinuum : Cardinal.mk (Set ℝ) ≤ Cardinal.continuum :=
    hSetToMeasurable.trans hMeasurableCard
  have hSetCardEq : Cardinal.mk (Set ℝ) = 2 ^ Cardinal.continuum := by
    calc
      Cardinal.mk (Set ℝ) = 2 ^ Cardinal.mk ℝ := Cardinal.mk_set (α := ℝ)
      _ = 2 ^ Cardinal.continuum := by rw [Cardinal.mk_real]
  have hContinuumLtSet : Cardinal.continuum < Cardinal.mk (Set ℝ) := by
    rw [hSetCardEq]
    exact Cardinal.cantor Cardinal.continuum
  exact (not_le_of_gt hContinuumLtSet) hSetCardLeContinuum

/-- If a measure is not complete, then there exists a measure-zero set that is not measurable. -/
lemma exists_zeroMeasure_notMeasurableSet_of_not_isComplete
    {α : Type*} [MeasurableSpace α] (μ : MeasureTheory.Measure α)
    (hIncomplete : ¬ μ.IsComplete) :
    ∃ E : Set α, μ E = 0 ∧ ¬ MeasurableSet E := by
  rw [MeasureTheory.Measure.isComplete_iff] at hIncomplete
  push_neg at hIncomplete
  rcases hIncomplete with ⟨E, hE_zero, hE_not_meas⟩
  exact ⟨E, hE_zero, hE_not_meas⟩

/-- Any measure-zero set is Carathéodory measurable for the outer measure induced by the same
measure. -/
lemma isCaratheodory_of_measure_eq_zero
    {α : Type*} [MeasurableSpace α] (μ : MeasureTheory.Measure α) {E : Set α}
    (hE_zero : μ E = 0) :
    μ.toOuterMeasure.IsCaratheodory E := by
  intro T
  simpa [MeasureTheory.Measure.toOuterMeasure_apply] using
    (MeasureTheory.measure_inter_add_diff₀ (μ := μ) T
      (MeasureTheory.NullMeasurableSet.of_null hE_zero)).symm

/-- For Lebesgue outer measure on `ℝ`, Carathéodory measurability implies null measurability
for the associated measure `volume`. -/
lemma isCaratheodory_implies_nullMeasurable_for_volume
    {E : Set ℝ}
    (hE : ((MeasureTheory.volume : MeasureTheory.Measure ℝ).toOuterMeasure).IsCaratheodory E) :
    MeasureTheory.NullMeasurableSet E (MeasureTheory.volume : MeasureTheory.Measure ℝ) := by
  let U : ℕ → Set ℝ := fun n =>
    MeasureTheory.toMeasurable (MeasureTheory.volume : MeasureTheory.Measure ℝ)
      (E ∩ Set.Icc (-(n : ℝ)) n)
  have hU_meas : ∀ n : ℕ, MeasurableSet (U n) := by
    intro n
    exact MeasureTheory.measurableSet_toMeasurable (MeasureTheory.volume : MeasureTheory.Measure ℝ)
      (E ∩ Set.Icc (-(n : ℝ)) n)
  have hU_diff_zero : ∀ n : ℕ,
      (MeasureTheory.volume : MeasureTheory.Measure ℝ) (U n \ E) = 0 := by
    intro n
    have hU_eq :
        (MeasureTheory.volume : MeasureTheory.Measure ℝ) (U n) =
          (MeasureTheory.volume : MeasureTheory.Measure ℝ) (E ∩ Set.Icc (-(n : ℝ)) n) := by
      simp [U, MeasureTheory.measure_toMeasurable]
    have hInter_le :
        (MeasureTheory.volume : MeasureTheory.Measure ℝ) (E ∩ Set.Icc (-(n : ℝ)) n) ≤
          (MeasureTheory.volume : MeasureTheory.Measure ℝ) (U n ∩ E) := by
      apply MeasureTheory.measure_mono
      intro x hx
      exact ⟨MeasureTheory.subset_toMeasurable (MeasureTheory.volume : MeasureTheory.Measure ℝ)
        (E ∩ Set.Icc (-(n : ℝ)) n) hx, hx.1⟩
    have hUinter_le :
        (MeasureTheory.volume : MeasureTheory.Measure ℝ) (U n ∩ E) ≤
          (MeasureTheory.volume : MeasureTheory.Measure ℝ) (U n) := by
      exact MeasureTheory.measure_mono Set.inter_subset_left
    have hUinter_ge :
        (MeasureTheory.volume : MeasureTheory.Measure ℝ) (U n) ≤
          (MeasureTheory.volume : MeasureTheory.Measure ℝ) (U n ∩ E) := by
      calc
        (MeasureTheory.volume : MeasureTheory.Measure ℝ) (U n) =
            (MeasureTheory.volume : MeasureTheory.Measure ℝ) (E ∩ Set.Icc (-(n : ℝ)) n) := hU_eq
        _ ≤ (MeasureTheory.volume : MeasureTheory.Measure ℝ) (U n ∩ E) := hInter_le
    have hUinter_eq :
        (MeasureTheory.volume : MeasureTheory.Measure ℝ) (U n ∩ E) =
          (MeasureTheory.volume : MeasureTheory.Measure ℝ) (U n) := by
      exact le_antisymm hUinter_le hUinter_ge
    have hCarU :
        (MeasureTheory.volume : MeasureTheory.Measure ℝ) (U n) =
          (MeasureTheory.volume : MeasureTheory.Measure ℝ) (U n ∩ E) +
            (MeasureTheory.volume : MeasureTheory.Measure ℝ) (U n \ E) :=
      hE (U n)
    have hUfinite : (MeasureTheory.volume : MeasureTheory.Measure ℝ) (U n) ≠ ⊤ := by
      rw [hU_eq]
      refine (lt_of_le_of_lt
        (MeasureTheory.measure_mono
          (Set.inter_subset_right : E ∩ Set.Icc (-(n : ℝ)) n ⊆ Set.Icc (-(n : ℝ)) n))
        ?_).ne
      simp [Real.volume_Icc]
    have hAdd :
        (MeasureTheory.volume : MeasureTheory.Measure ℝ) (U n) + 0 =
          (MeasureTheory.volume : MeasureTheory.Measure ℝ) (U n) +
            (MeasureTheory.volume : MeasureTheory.Measure ℝ) (U n \ E) := by
      simpa [hUinter_eq] using hCarU
    have hAdd' :
        (MeasureTheory.volume : MeasureTheory.Measure ℝ) (U n) +
            (MeasureTheory.volume : MeasureTheory.Measure ℝ) (U n \ E) =
          (MeasureTheory.volume : MeasureTheory.Measure ℝ) (U n) + 0 :=
      hAdd.symm
    exact (ENNReal.add_right_inj hUfinite).1 hAdd'
  let V : Set ℝ := ⋃ n : ℕ, U n
  have hSubset : E ⊆ V := by
    intro x hx
    obtain ⟨n, hn⟩ := exists_nat_ge |x|
    have hxIcc : x ∈ Set.Icc (-(n : ℝ)) n := by
      have habs : -(n : ℝ) ≤ x ∧ x ≤ (n : ℝ) := (abs_le).1 hn
      exact ⟨habs.1, habs.2⟩
    have hxU : x ∈ U n := by
      exact MeasureTheory.subset_toMeasurable (MeasureTheory.volume : MeasureTheory.Measure ℝ)
        (E ∩ Set.Icc (-(n : ℝ)) n) ⟨hx, hxIcc⟩
    exact Set.mem_iUnion.2 ⟨n, hxU⟩
  have hV_meas : MeasurableSet V := by
    exact MeasurableSet.iUnion hU_meas
  have hV_diff_zero : (MeasureTheory.volume : MeasureTheory.Measure ℝ) (V \ E) = 0 := by
    refine le_antisymm ?_ bot_le
    calc
      (MeasureTheory.volume : MeasureTheory.Measure ℝ) (V \ E) =
          (MeasureTheory.volume : MeasureTheory.Measure ℝ) (⋃ n : ℕ, U n \ E) := by
            simp [V, Set.iUnion_diff]
      _ ≤ ∑' n : ℕ, (MeasureTheory.volume : MeasureTheory.Measure ℝ) (U n \ E) :=
            MeasureTheory.measure_iUnion_le (fun n => U n \ E)
      _ = 0 := by simp [hU_diff_zero]
  have hAE : E =ᵐ[(MeasureTheory.volume : MeasureTheory.Measure ℝ)] V := by
    refine (MeasureTheory.ae_eq_set).2 ?_
    constructor
    · have hEmpty : E \ V = ∅ := Set.diff_eq_empty.2 hSubset
      simp [hEmpty]
    · exact hV_diff_zero
  exact ⟨V, hV_meas, hAE⟩

/-- A set that is not almost-everywhere equal to any measurable set is not null measurable for
Lebesgue volume. -/
lemma nonNullMeasurable_of_notAEEq_any_measurable_for_volume
    {E : Set ℝ}
    (hNotAEEq :
      ∀ t : Set ℝ, MeasurableSet t →
        ¬ (E =ᵐ[(MeasureTheory.volume : MeasureTheory.Measure ℝ)] t)) :
    ¬ MeasureTheory.NullMeasurableSet E (MeasureTheory.volume : MeasureTheory.Measure ℝ) := by
  intro hE_nullMeasurable
  rcases hE_nullMeasurable.exists_measurable_superset_ae_eq with ⟨t, _, ht_meas, ht_ae_eq⟩
  exact hNotAEEq t ht_meas ht_ae_eq.symm

/-- A witness that is not almost-everywhere equal to any measurable set yields a global witness
that is not null measurable for Lebesgue volume. -/
lemma exists_nonNullMeasurableSet_for_volume_of_exists_notAEEq
    (hExists :
      ∃ E : Set ℝ,
        ∀ t : Set ℝ, MeasurableSet t →
          ¬ (E =ᵐ[(MeasureTheory.volume : MeasureTheory.Measure ℝ)] t)) :
    ∃ E : Set ℝ,
      ¬ MeasureTheory.NullMeasurableSet E (MeasureTheory.volume : MeasureTheory.Measure ℝ) := by
  rcases hExists with ⟨E, hE⟩
  exact ⟨E, nonNullMeasurable_of_notAEEq_any_measurable_for_volume hE⟩

/-- Vitali-type bounded witness in `Set.Icc (0 : ℝ) 1`
that is not null measurable for Lebesgue measure. -/
theorem exists_nonNullMeasurableSet_volume_Icc_real :
    ∃ E : Set ℝ,
      E ⊆ Set.Icc (0 : ℝ) 1 ∧
        ¬ MeasureTheory.NullMeasurableSet E (MeasureTheory.volume : MeasureTheory.Measure ℝ) := by
  let I : Type := {x : ℝ // x ∈ Set.Icc (0 : ℝ) 1}
  let ratDiffSetoid : Setoid I :=
    { r := fun x y => ∃ q : ℚ, ((x : ℝ) - (y : ℝ)) = q
      iseqv := by
        refine ⟨?_, ?_, ?_⟩
        · intro x
          exact ⟨0, by norm_num⟩
        · intro x y hxy
          rcases hxy with ⟨q, hq⟩
          refine ⟨-q, ?_⟩
          calc
            ((y : ℝ) - (x : ℝ)) = -(((x : ℝ) - (y : ℝ))) := by ring
            _ = -((q : ℚ) : ℝ) := by simp [hq]
            _ = (((-q : ℚ)) : ℝ) := by norm_num
        · intro x y z hxy hyz
          rcases hxy with ⟨q1, hq1⟩
          rcases hyz with ⟨q2, hq2⟩
          refine ⟨q1 + q2, ?_⟩
          calc
            ((x : ℝ) - (z : ℝ)) = ((x : ℝ) - (y : ℝ)) + ((y : ℝ) - (z : ℝ)) := by ring
            _ = ((q1 : ℚ) : ℝ) + ((q2 : ℚ) : ℝ) := by simp [hq1, hq2]
            _ = (((q1 + q2 : ℚ)) : ℝ) := by norm_num }
  let mkQ : I → Quotient ratDiffSetoid := fun x => Quotient.mk'' x
  let chooseRep : Quotient ratDiffSetoid → I := fun c => Classical.choose (Quotient.exists_rep c)
  have chooseRep_spec : ∀ c : Quotient ratDiffSetoid, mkQ (chooseRep c) = c := by
    intro c
    exact Classical.choose_spec (Quotient.exists_rep c)
  let E : Set ℝ := Set.range fun c : Quotient ratDiffSetoid => ((chooseRep c : I) : ℝ)
  have E_subset_Icc : E ⊆ Set.Icc (0 : ℝ) 1 := by
    intro x hx
    rcases hx with ⟨c, rfl⟩
    exact (chooseRep c).property
  have E_diff_rat_eq :
      ∀ {x y : ℝ}, x ∈ E → y ∈ E → (∃ q : ℚ, x - y = q) → x = y := by
    intro x y hx hy hxy
    rcases hx with ⟨cx, rfl⟩
    rcases hy with ⟨cy, rfl⟩
    rcases hxy with ⟨q, hq⟩
    have hclass : mkQ (chooseRep cx) = mkQ (chooseRep cy) := by
      exact Quotient.sound ⟨q, hq⟩
    have hcx : mkQ (chooseRep cx) = cx := chooseRep_spec cx
    have hcy : mkQ (chooseRep cy) = cy := chooseRep_spec cy
    have hcxcy : cx = cy := by simpa [hcx, hcy] using hclass
    simp [hcxcy]
  let T : ℚ → Set ℝ := fun q => {x : ℝ | x - (q : ℝ) ∈ E}
  let Q0 : Type := {q : ℚ // (-1 : ℝ) ≤ (q : ℝ) ∧ (q : ℝ) ≤ (1 : ℝ)}
  have disjoint_T_of_ne : ∀ {q1 q2 : ℚ}, q1 ≠ q2 → Disjoint (T q1) (T q2) := by
    intro q1 q2 hneq
    refine Set.disjoint_left.2 ?_
    intro x hx1 hx2
    have hrat : ∃ q : ℚ, (x - (q1 : ℝ)) - (x - (q2 : ℝ)) = q := by
      refine ⟨q2 - q1, ?_⟩
      norm_num [sub_eq_add_neg, add_comm, add_left_comm, add_assoc]
    have hEq : (x - (q1 : ℝ)) = (x - (q2 : ℝ)) := E_diff_rat_eq hx1 hx2 hrat
    have : (q1 : ℝ) = (q2 : ℝ) := by linarith
    exact hneq (Rat.cast_inj.1 this)
  have cover_Icc_by_Q0 : Set.Icc (0 : ℝ) 1 ⊆ ⋃ q : Q0, T q.1 := by
    intro x hx
    let xI : I := ⟨x, hx⟩
    let c : Quotient ratDiffSetoid := mkQ xI
    let vI : I := chooseRep c
    have hvInE : (vI : ℝ) ∈ E := by
      refine ⟨c, rfl⟩
    have hclassEq : mkQ vI = mkQ xI := by
      simp [c, vI, chooseRep_spec]
    have hrel : ratDiffSetoid.r vI xI := Quotient.exact hclassEq
    rcases hrel with ⟨r, hr⟩
    have hr' : (vI : ℝ) - x = (r : ℝ) := by simpa [xI] using hr
    have hDiffEq : x - (vI : ℝ) = ((-r : ℚ) : ℝ) := by
      calc
        x - (vI : ℝ) = -((vI : ℝ) - x) := by ring
        _ = -((r : ℝ)) := by simp [hr']
        _ = ((-r : ℚ) : ℝ) := by norm_num
    have hqLower : (-1 : ℝ) ≤ ((-r : ℚ) : ℝ) := by
      have hDiffLower : (-1 : ℝ) ≤ x - (vI : ℝ) := by
        have hx0 : (0 : ℝ) ≤ x := hx.1
        have hv1 : (vI : ℝ) ≤ 1 := vI.property.2
        linarith
      simpa [hDiffEq] using hDiffLower
    have hqUpper : (((-r : ℚ) : ℝ)) ≤ (1 : ℝ) := by
      have hDiffUpper : x - (vI : ℝ) ≤ (1 : ℝ) := by
        have hx1 : x ≤ (1 : ℝ) := hx.2
        have hv0 : (0 : ℝ) ≤ (vI : ℝ) := vI.property.1
        linarith
      simpa [hDiffEq] using hDiffUpper
    refine Set.mem_iUnion.2 ⟨⟨-r, hqLower, hqUpper⟩, ?_⟩
    have hxplus : x + (r : ℝ) = (vI : ℝ) := by linarith [hr']
    have hxplusIn : x + (r : ℝ) ∈ E := by simpa [hxplus] using hvInE
    simpa [T, sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hxplusIn
  have union_Q0_subset_Icc : (⋃ q : Q0, T q.1) ⊆ Set.Icc (-1 : ℝ) 2 := by
    intro x hx
    rcases Set.mem_iUnion.1 hx with ⟨q, hxq⟩
    have hInE : x - (q.1 : ℝ) ∈ E := hxq
    have hInIcc : x - (q.1 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := E_subset_Icc hInE
    have hq0 : (-1 : ℝ) ≤ (q.1 : ℝ) := q.2.1
    have hq1 : (q.1 : ℝ) ≤ (1 : ℝ) := q.2.2
    constructor
    · have hx0 : (0 : ℝ) ≤ x - (q.1 : ℝ) := hInIcc.1
      linarith
    · have hx1 : x - (q.1 : ℝ) ≤ (1 : ℝ) := hInIcc.2
      linarith
  have hE_not_null :
      ¬ MeasureTheory.NullMeasurableSet E (MeasureTheory.volume : MeasureTheory.Measure ℝ) := by
    intro hE_null
    have hT_null : ∀ q : ℚ,
        MeasureTheory.NullMeasurableSet (T q) (MeasureTheory.volume : MeasureTheory.Measure ℝ) := by
      intro q
      change MeasureTheory.NullMeasurableSet (((fun x : ℝ => x + (-(q : ℝ))) ⁻¹' E))
        (MeasureTheory.volume : MeasureTheory.Measure ℝ)
      exact hE_null.preimage
        (MeasureTheory.quasiMeasurePreserving_add_right
          (μ := (MeasureTheory.volume : MeasureTheory.Measure ℝ)) (g := (-(q : ℝ))))
    have hT_measure : ∀ q : ℚ,
        (MeasureTheory.volume : MeasureTheory.Measure ℝ) (T q) =
          (MeasureTheory.volume : MeasureTheory.Measure ℝ) E := by
      intro q
      change (MeasureTheory.volume : MeasureTheory.Measure ℝ) (((fun x : ℝ => x + (-(q : ℝ))) ⁻¹' E))
        = (MeasureTheory.volume : MeasureTheory.Measure ℝ) E
      exact MeasureTheory.measure_preimage_add_right
        (μ := (MeasureTheory.volume : MeasureTheory.Measure ℝ)) (g := (-(q : ℝ))) (A := E)
    have hLowerQ0 :
        (1 : ENNReal) ≤
          (MeasureTheory.volume : MeasureTheory.Measure ℝ) (⋃ q : Q0, T q.1) := by
      calc
        (1 : ENNReal) = (MeasureTheory.volume : MeasureTheory.Measure ℝ) (Set.Icc (0 : ℝ) 1) := by
          simp [Real.volume_Icc]
        _ ≤ (MeasureTheory.volume : MeasureTheory.Measure ℝ) (⋃ q : Q0, T q.1) :=
          MeasureTheory.measure_mono cover_Icc_by_Q0
    by_cases hZero : (MeasureTheory.volume : MeasureTheory.Measure ℝ) E = 0
    · haveI : Countable Q0 := inferInstance
      have hPairwiseQ0 : Pairwise (fun q1 q2 : Q0 => Disjoint (T q1.1) (T q2.1)) := by
        intro q1 q2 hne
        exact disjoint_T_of_ne (fun hEq => hne (Subtype.ext hEq))
      have hPairwiseAeQ0 :
          Pairwise (fun q1 q2 : Q0 =>
            MeasureTheory.AEDisjoint (MeasureTheory.volume : MeasureTheory.Measure ℝ)
              (T q1.1) (T q2.1)) := by
        intro q1 q2 hne
        exact (hPairwiseQ0 hne).aedisjoint
      have hU0 :
          (MeasureTheory.volume : MeasureTheory.Measure ℝ) (⋃ q : Q0, T q.1) = 0 := by
        calc
          (MeasureTheory.volume : MeasureTheory.Measure ℝ) (⋃ q : Q0, T q.1)
              = ∑' q : Q0, (MeasureTheory.volume : MeasureTheory.Measure ℝ) (T q.1) :=
                  MeasureTheory.measure_iUnion₀ hPairwiseAeQ0 (fun q => hT_null q.1)
          _ = 0 := by simp [hT_measure, hZero]
      have hImpossible : ¬ ((1 : ENNReal) ≤ 0) := by simp
      have hLowerQ0' := hLowerQ0
      rw [hU0] at hLowerQ0'
      exact hImpossible hLowerQ0'
    · let qSeq : ℕ → Q0 := fun n => by
        refine ⟨(1 : ℚ) / (n + 2), ?_⟩
        constructor
        · have hnonnegQ : (0 : ℚ) ≤ (1 : ℚ) / (n + 2) := by positivity
          have hnonnegR : (0 : ℝ) ≤ (((1 : ℚ) / (n + 2) : ℚ) : ℝ) := by exact_mod_cast hnonnegQ
          linarith
        · have hpos : (0 : ℚ) < (n + 2 : ℚ) := by positivity
          have hden_ge_one_nat : (1 : ℕ) ≤ n + 2 := by omega
          have hden_ge_one_q : (1 : ℚ) ≤ (n + 2 : ℚ) := by exact_mod_cast hden_ge_one_nat
          have hleQ : (1 : ℚ) / (n + 2) ≤ 1 := by
            exact (div_le_iff₀ hpos).2 (by simpa using hden_ge_one_q)
          exact_mod_cast hleQ
      have qSeq_injective : Function.Injective qSeq := by
        intro m n hmn
        have hVal : (qSeq m).1 = (qSeq n).1 := congrArg Subtype.val hmn
        change (1 : ℚ) / (m + 2) = (1 : ℚ) / (n + 2) at hVal
        have hmn_den : (m + 2 : ℚ) = (n + 2 : ℚ) := by
          have hinv : ((m + 2 : ℚ)⁻¹) = ((n + 2 : ℚ)⁻¹) := by simpa [one_div] using hVal
          exact inv_injective hinv
        have hNat : m + 2 = n + 2 := by exact_mod_cast hmn_den
        omega
      have hPairwiseSeq : Pairwise (fun m n : ℕ => Disjoint (T (qSeq m).1) (T (qSeq n).1)) := by
        intro m n hmn
        exact disjoint_T_of_ne (fun hEq => hmn (qSeq_injective (Subtype.ext hEq)))
      have hPairwiseAeSeq :
          Pairwise (fun m n : ℕ =>
            MeasureTheory.AEDisjoint (MeasureTheory.volume : MeasureTheory.Measure ℝ)
              (T (qSeq m).1) (T (qSeq n).1)) := by
        intro m n hmn
        exact (hPairwiseSeq hmn).aedisjoint
      have hUSeq_top :
          (MeasureTheory.volume : MeasureTheory.Measure ℝ) (⋃ n : ℕ, T (qSeq n).1) = ⊤ := by
        calc
          (MeasureTheory.volume : MeasureTheory.Measure ℝ) (⋃ n : ℕ, T (qSeq n).1)
              = ∑' n : ℕ, (MeasureTheory.volume : MeasureTheory.Measure ℝ) (T (qSeq n).1) :=
                  MeasureTheory.measure_iUnion₀ hPairwiseAeSeq (fun n => hT_null (qSeq n).1)
          _ = ∑' n : ℕ, (MeasureTheory.volume : MeasureTheory.Measure ℝ) E := by simp [hT_measure]
          _ = ⊤ := ENNReal.tsum_const_eq_top_of_ne_zero (α := ℕ) hZero
      have hSeqSubset : (⋃ n : ℕ, T (qSeq n).1) ⊆ Set.Icc (-1 : ℝ) 2 := by
        intro x hx
        have hxQ0 : x ∈ ⋃ q : Q0, T q.1 := by
          rcases Set.mem_iUnion.1 hx with ⟨n, hn⟩
          exact Set.mem_iUnion.2 ⟨qSeq n, hn⟩
        exact union_Q0_subset_Icc hxQ0
      have hUSeq_lt_top :
          (MeasureTheory.volume : MeasureTheory.Measure ℝ) (⋃ n : ℕ, T (qSeq n).1) < ⊤ := by
        have hIcc_lt_top :
            (MeasureTheory.volume : MeasureTheory.Measure ℝ) (Set.Icc (-1 : ℝ) 2) < ⊤ := by
          simp [Real.volume_Icc]
        exact lt_of_le_of_lt (MeasureTheory.measure_mono hSeqSubset) hIcc_lt_top
      have : (⊤ : ENNReal) < ⊤ := by
        rw [hUSeq_top] at hUSeq_lt_top
        exact hUSeq_lt_top
      exact lt_irrefl _ this
  exact ⟨E, E_subset_Icc, hE_not_null⟩
