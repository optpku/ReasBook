/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Books.ProbabilityTheory_Klenke_2020.Items.Chap24.Definition_24_3
import Books.ProbabilityTheory_Klenke_2020.Items.Chap24.Definition_24_1
import Books.ProbabilityTheory_Klenke_2020.Items.Chap24.Definition_24_8

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory ENNReal

universe u u' v

namespace ProbabilityTheory

variable {Ω : Type u} [MeasurableSpace Ω]
variable {Ω' : Type u'} [MeasurableSpace Ω']
variable {E : Type v} [PseudoMetricSpace E] [MeasurableSpace E] [BorelSpace E]
  [LocallyCompactSpace E] [PolishSpace E] [T2Space E]

-- Definition 24.8 is stated for kernels. For a source-level random measure
-- `X : Ω → Measure E`, the matching owner-facing notion is independence of the
-- evaluation family `ω ↦ X ω (A i)` on pairwise disjoint measurable subsets of `E`.
/-- A source-level random measure `X` has independent increments under `P` if evaluations on every
finite family of pairwise disjoint measurable sets are independent random variables. -/
def HasIndependentIncrements (P : ProbabilityMeasure Ω) (X : Ω → Measure E) : Prop :=
  ∀ n, ∀ A : Fin n → Set E,
    (∀ i, MeasurableSet (A i)) →
    Pairwise (fun i j ↦ Disjoint (A i) (A j)) →
    iIndepFun (fun i ω ↦ X ω (A i)) (P : Measure Ω)

/-- Helper for Corollary 24.9: restricting a locally finite measure to a compact set gives a
finite measure. -/
lemma restrict_lt_top_of_isCompact
    {μ : Measure E} [IsLocallyFiniteMeasure μ] {K A : Set E}
    (hK : IsCompact K) (hA : MeasurableSet A) :
    (μ.restrict K) A < ∞ := by
  -- Proof comment: the restricted mass is bounded by the mass of the compact carrier `K`.
  rw [Measure.restrict_apply hA]
  exact lt_of_le_of_lt (measure_mono Set.inter_subset_right) hK.measure_lt_top

/-- Helper for Corollary 24.9: the restriction of a locally finite measure to a compact set is
boundedly finite. -/
noncomputable def restrictToBoundedlyFiniteMeasure
    (μ : Measure E) [IsLocallyFiniteMeasure μ] (K : Set E) (hK : IsCompact K) :
    BoundedlyFiniteMeasure E :=
  ⟨μ.restrict K, fun _ hA _hA_bdd ↦ restrict_lt_top_of_isCompact (μ := μ) (K := K) hK hA⟩

/-- Helper for Corollary 24.9: restricting a random measure to a compact set preserves the
independent-increments property. -/
lemma HasIndependentIncrements.restrict
    {P : ProbabilityMeasure Ω} {X : Ω → Measure E}
    (hX_indep : HasIndependentIncrements P X) {K : Set E} (hK : MeasurableSet K) :
    HasIndependentIncrements P (fun ω ↦ (X ω).restrict K) := by
  intro n A hA hdisj
  -- Proof comment: the restricted increments are evaluations on the pairwise disjoint sets
  -- `A i ∩ K`, so the original independent-increments hypothesis applies directly.
  simpa [Measure.restrict_apply, hA] using
    hX_indep n (fun i ↦ A i ∩ K) (fun i ↦ (hA i).inter hK) <| by
      intro i j hij
      exact (hdisj hij).mono_left Set.inter_subset_left |>.mono_right Set.inter_subset_left

/-- Helper for Corollary 24.9: the bounded-set evaluation laws remain identical after restricting
both random measures to the same compact set. -/
lemma boundedEval_identDistrib_restrict_compact
    {P : ProbabilityMeasure Ω} {Q : ProbabilityMeasure Ω'}
    {X : Ω → Measure E} {Y : Ω' → Measure E} {K A : Set E}
    (hK_meas : MeasurableSet K) (_hK_bdd : Bornology.IsBounded K)
    (hA : MeasurableSet A) (hA_bdd : Bornology.IsBounded A)
    (h_eval :
      ∀ S : Set E, MeasurableSet S → Bornology.IsBounded S →
        IdentDistrib
          (fun ω ↦ X ω S)
          (fun ω ↦ Y ω S)
          (P : Measure Ω) (Q : Measure Ω')) :
    IdentDistrib
      (fun ω ↦ (X ω).restrict K A)
      (fun ω ↦ (Y ω).restrict K A)
      (P : Measure Ω) (Q : Measure Ω') := by
  -- Proof comment: evaluation of the restricted measure is evaluation on the bounded measurable
  -- intersection `A ∩ K`.
  simpa [Measure.restrict_apply, hA, Set.inter_comm, Set.inter_left_comm, Set.inter_assoc] using
    h_eval (A ∩ K) (hA.inter hK_meas)
      (Bornology.IsBounded.subset hA_bdd Set.inter_subset_left)

section BoundedEvaluationFamily

/-- Helper for Corollary 24.9: bounded measurable subsets of `E`. -/
private abbrev BoundedMeasurableSet :=
  {A : Set E // MeasurableSet A ∧ Bornology.IsBounded A}

/-- Helper for Corollary 24.9: the finite tuple of evaluations of a measure on a family of sets. -/
private def measureDisjointSetTuple {n : ℕ} (As : Fin n → Set E) :
    Measure E → Fin n → ENNReal :=
  fun μ i ↦ μ (As i)

/-- Helper for Corollary 24.9: evaluating the tuple map at a coordinate reads off the
corresponding set mass. -/
private theorem measureDisjointSetTuple_apply {n : ℕ} (As : Fin n → Set E)
    (μ : Measure E) (i : Fin n) :
    measureDisjointSetTuple As μ i = μ (As i) := by
  -- Proof comment: this is the defining value of the tuple function at coordinate `i`.
  rfl

/-- Helper for Corollary 24.9: the full bounded-set evaluation family on `Measure E`. -/
private def measureBoundedSetEvaluationFamily :
    Measure E → BoundedMeasurableSet (E := E) → ENNReal :=
  fun μ A ↦ μ A.1

/-- Helper for Corollary 24.9: the bounded-set evaluation family is measurable coordinatewise. -/
private theorem measurable_measureBoundedSetEvaluationFamily :
    Measurable (measureBoundedSetEvaluationFamily (E := E)) := by
  -- Proof comment: each coordinate is an ordinary measurable-set evaluation map on `Measure E`.
  exact measurable_pi_lambda _ fun A ↦ Measure.measurable_coe A.2.1

/-- Helper for Corollary 24.9: a probability measure on a pullback product sigma-algebra is
determined by its pushforward along the full coordinate family. -/
private theorem probabilityMeasureEqOfMapEqOfComapPi
    {Ω : Type*} {ι : Type*} {α : ι → Type*} [mΩ : MeasurableSpace Ω]
    [∀ i, MeasurableSpace (α i)] {P Q : ProbabilityMeasure Ω} {X : Ω → ∀ i, α i}
    (hX :
      mΩ =
        MeasurableSpace.comap X (inferInstance : MeasurableSpace ((i : ι) → α i)))
    (hmap : (P : Measure Ω).map X = (Q : Measure Ω).map X) :
    P = Q := by
  apply ProbabilityMeasure.toMeasure_injective
  have hXm : Measurable X := by
    exact Measurable.of_comap_le (by simpa [hX])
  let G : Set (Set Ω) := Set.preimage X '' measurableCylinders α
  have hgen : mΩ = MeasurableSpace.generateFrom G := by
    -- Proof comment: the domain sigma-algebra is the pullback of the cylinder generator.
    calc
      mΩ = MeasurableSpace.comap X (inferInstance : MeasurableSpace ((i : ι) → α i)) := hX
      _ = MeasurableSpace.comap X (MeasurableSpace.generateFrom (measurableCylinders α)) := by
            rw [generateFrom_measurableCylinders]
      _ = MeasurableSpace.generateFrom G := by
            rw [MeasurableSpace.comap_generateFrom]
  have hG : IsPiSystem G := by
    have hmc : IsPiSystem (measurableCylinders α) := by
      simpa using
        (isPiSystem_measurableCylinders : IsPiSystem (measurableCylinders α))
    intro s hs t ht hst
    rcases hs with ⟨u, hu, rfl⟩
    rcases ht with ⟨v, hv, rfl⟩
    have huv_nonempty : (u ∩ v).Nonempty := by
      rcases hst with ⟨ω, hωu, hωv⟩
      exact ⟨X ω, hωu, hωv⟩
    refine ⟨u ∩ v, hmc u hu v hv huv_nonempty, ?_⟩
    ext ω
    rfl
  refine ext_of_generate_finite G hgen hG ?_ ?_
  · intro s hs
    rcases hs with ⟨u, hu, rfl⟩
    have hu_meas : MeasurableSet u := MeasurableSet.of_mem_measurableCylinders hu
    rw [← Measure.map_apply hXm hu_meas, hmap, Measure.map_apply hXm hu_meas]
  · simp

/-- Helper for Corollary 24.9: the Giry measurable space on `Measure E` is already generated by
bounded-set evaluations. -/
private theorem measureMeasurableSpace_eq_comap_boundedSetEvaluationFamily :
    (inferInstance : MeasurableSpace (Measure E)) =
      MeasurableSpace.comap
        (measureBoundedSetEvaluationFamily (E := E))
        (inferInstance : MeasurableSpace (BoundedMeasurableSet (E := E) → ENNReal)) := by
  let F := measureBoundedSetEvaluationFamily (E := E)
  have hF_meas :
      @Measurable (Measure E) (BoundedMeasurableSet (E := E) → ENNReal)
        (inferInstance : MeasurableSpace (Measure E))
        (inferInstance : MeasurableSpace (BoundedMeasurableSet (E := E) → ENNReal))
        F :=
    measurable_measureBoundedSetEvaluationFamily (E := E)
  refine le_antisymm ?_ hF_meas.comap_le
  rw [show (inferInstance : MeasurableSpace (Measure E)) =
      ⨆ (A : Set E) (_ : MeasurableSet A), (borel ENNReal).comap (fun μ : Measure E ↦ μ A) by
        rfl]
  refine iSup₂_le ?_
  intro A hA
  have hfamily_meas :
      @Measurable (Measure E) (BoundedMeasurableSet (E := E) → ENNReal)
        (MeasurableSpace.comap F (inferInstance : MeasurableSpace (BoundedMeasurableSet (E := E) → ENNReal)))
        (inferInstance : MeasurableSpace (BoundedMeasurableSet (E := E) → ENNReal))
        F :=
    Measurable.of_comap_le le_rfl
  have h_eval_meas :
      @Measurable (Measure E) ENNReal
        (MeasurableSpace.comap F (inferInstance : MeasurableSpace (BoundedMeasurableSet (E := E) → ENNReal)))
        (borel ENNReal)
        (fun μ : Measure E ↦ μ A) := by
    let K : CompactExhaustion E := CompactExhaustion.choice E
    have hpiece :
        ∀ n,
          @Measurable (Measure E) ENNReal
            (MeasurableSpace.comap F
              (inferInstance : MeasurableSpace (BoundedMeasurableSet (E := E) → ENNReal)))
            (borel ENNReal)
            (fun μ : Measure E ↦ μ (A ∩ K n)) := by
      intro n
      let An : BoundedMeasurableSet (E := E) :=
        ⟨A ∩ K n, hA.inter (K.isCompact n).measurableSet,
          (K.isCompact n).isBounded.subset Set.inter_subset_right⟩
      -- Proof comment: each compact-cut evaluation is one coordinate of the bounded family.
      simpa [F, An] using (measurable_pi_apply An).comp hfamily_meas
    have h_eval_eq :
        (fun μ : Measure E ↦ μ A) =
          (fun μ : Measure E ↦ ⨆ n, μ (A ∩ K n)) := by
      funext μ
      have hmono : Monotone fun n : ℕ ↦ A ∩ K n := fun m n hmn x hx ↦
        ⟨hx.1, K.subset hmn hx.2⟩
      have hUnion : ⋃ n, A ∩ K n = A := by
        ext x
        constructor
        · intro hxU
          rcases Set.mem_iUnion.1 hxU with ⟨n, hx⟩
          exact hx.1
        · intro hxA
          rcases K.exists_mem x with ⟨n, hxK⟩
          exact Set.mem_iUnion.2 ⟨n, ⟨hxA, hxK⟩⟩
      calc
        μ A = μ (⋃ n, A ∩ K n) := by
          exact congrArg (μ ·) hUnion.symm
        _ = ⨆ n, μ (A ∩ K n) := hmono.measure_iUnion
    -- Proof comment: arbitrary measurable evaluations are monotone suprema of bounded ones.
    simpa [h_eval_eq] using Measurable.iSup hpiece
  exact MeasurableSpace.comap_le_iff_le_map.2 h_eval_meas

/-- Helper for Corollary 24.9: pairwise-disjoint bounded evaluations have the same tuple law once
the one-dimensional bounded evaluations agree and the increments are independent. -/
private theorem identDistrib_disjointMeasureSetTuple_of_boundedEvalIdentDistrib
    {P : ProbabilityMeasure Ω} {Q : ProbabilityMeasure Ω'}
    {X : Ω → Measure E} {Y : Ω' → Measure E} {n : ℕ}
    (As : Fin n → Set E)
    (hA : ∀ i, MeasurableSet (As i))
    (hA_bdd : ∀ i, Bornology.IsBounded (As i))
    (hdisj : Pairwise (fun i j ↦ Disjoint (As i) (As j)))
    (hX_indep : HasIndependentIncrements P X)
    (hY_indep : HasIndependentIncrements Q Y)
    (h_eval :
      ∀ A : Set E, MeasurableSet A → Bornology.IsBounded A →
        IdentDistrib
          (fun ω ↦ X ω A)
          (fun ω ↦ Y ω A)
          (P : Measure Ω) (Q : Measure Ω')) :
    IdentDistrib
      (fun ω ↦ measureDisjointSetTuple As (X ω))
      (fun ω ↦ measureDisjointSetTuple As (Y ω))
      (P : Measure Ω) (Q : Measure Ω') := by
  have hcoord :
      ∀ i, IdentDistrib
        (fun ω ↦ X ω (As i))
        (fun ω ↦ Y ω (As i))
        (P : Measure Ω) (Q : Measure Ω') := fun i ↦ h_eval (As i) (hA i) (hA_bdd i)
  have hX_tuple : iIndepFun (fun i ω ↦ X ω (As i)) (P : Measure Ω) :=
    hX_indep n As hA hdisj
  have hY_tuple : iIndepFun (fun i ω ↦ Y ω (As i)) (Q : Measure Ω') :=
    hY_indep n As hA hdisj
  -- Proof comment: the tuple law is the product law of the independent coordinates.
  simpa [measureDisjointSetTuple] using
    (ProbabilityTheory.IdentDistrib.pi
      (μ := (P : Measure Ω))
      (ν := (Q : Measure Ω'))
      hcoord hX_tuple hY_tuple)

/-- Helper for Corollary 24.9: the membership-pattern cell of a finite bounded-set family records
exactly which sets contain a point. -/
private def membershipPatternCell {m : ℕ} (As : Fin m → BoundedMeasurableSet (E := E))
    (s : Finset (Fin m)) : Set E :=
  {x | ∀ i, x ∈ (As i).1 ↔ i ∈ s}

/-- Helper for Corollary 24.9: every membership-pattern cell is measurable. -/
private theorem measurableSet_membershipPatternCell {m : ℕ}
    (As : Fin m → BoundedMeasurableSet (E := E)) (s : Finset (Fin m)) :
    MeasurableSet (membershipPatternCell As s) := by
  have hrepr :
      membershipPatternCell As s =
        ⋂ i, if i ∈ s then (As i).1 else ((As i).1)ᶜ := by
    ext x
    constructor
    · intro hx
      simp only [Set.mem_iInter]
      intro i
      by_cases hi : i ∈ s
      · simpa [hi] using (hx i).2 hi
      · have hnotin : x ∉ (As i).1 := by
          intro hxi
          exact hi ((hx i).1 hxi)
        simpa [hi, Set.mem_compl_iff, hnotin]
    · intro hx
      have hx' : ∀ i, x ∈ if i ∈ s then (As i).1 else ((As i).1)ᶜ := by
        simpa [Set.mem_iInter] using hx
      intro i
      constructor
      · intro hxi
        by_cases hi : i ∈ s
        · exact hi
        · have hcompl : x ∈ ((As i).1)ᶜ := by
            simpa [hi] using hx' i
          exact False.elim (hcompl hxi)
      · intro hi
        simpa [hi] using hx' i
  -- Proof comment: the cell is a finite intersection of measurable sets and complements.
  rw [hrepr]
  exact MeasurableSet.iInter fun i ↦ by
    by_cases hi : i ∈ s
    · simpa [hi] using (As i).2.1
    · simpa [hi] using (As i).2.1.compl

/-- Helper for Corollary 24.9: a nonempty membership-pattern cell is bounded because it sits
inside one of the original bounded sets. -/
private theorem isBounded_membershipPatternCell {m : ℕ}
    (As : Fin m → BoundedMeasurableSet (E := E)) {s : Finset (Fin m)} (hs : s.Nonempty) :
    Bornology.IsBounded (membershipPatternCell As s) := by
  rcases hs with ⟨i, hi⟩
  -- Proof comment: every point in the cell belongs to `As i` when `i ∈ s`.
  exact (As i).2.2.subset fun x hx ↦ (hx i).2 hi

/-- Helper for Corollary 24.9: distinct membership patterns define disjoint cells. -/
private theorem disjoint_membershipPatternCell {m : ℕ}
    (As : Fin m → BoundedMeasurableSet (E := E)) {s t : Finset (Fin m)} (hst : s ≠ t) :
    Disjoint (membershipPatternCell As s) (membershipPatternCell As t) := by
  -- Proof comment: a common point would force the same membership pattern twice.
  refine Set.disjoint_left.2 fun x hsx htx ↦ ?_
  apply hst
  ext i
  constructor
  · intro hi
    exact (htx i).1 ((hsx i).2 hi)
  · intro hi
    exact (hsx i).1 ((htx i).2 hi)

/-- Helper for Corollary 24.9: reindexing a finite bounded-set tuple identifies it with the
restriction of the full bounded-set evaluation family. -/
private theorem restrict_boundedSetEvaluationFamily_eq_piCongrLeft_comp
    (I : Finset (BoundedMeasurableSet (E := E))) :
    let e : Fin I.card ≃ I :=
      (Fintype.equivFinOfCardEq (show Fintype.card I = I.card by simp)).symm
    let es : (Fin I.card → ENNReal) ≃ᵐ (I → ENNReal) :=
      MeasurableEquiv.piCongrLeft (fun _ : I ↦ ENNReal) e
    es ∘ measureDisjointSetTuple
      (fun i ↦ (((e i : I) : BoundedMeasurableSet (E := E)).1 : Set E)) =
      fun μ : Measure E ↦
        I.restrict (measureBoundedSetEvaluationFamily (E := E) μ) := by
  classical
  let e : Fin I.card ≃ I :=
    (Fintype.equivFinOfCardEq (show Fintype.card I = I.card by simp)).symm
  let es : (Fin I.card → ENNReal) ≃ᵐ (I → ENNReal) :=
    MeasurableEquiv.piCongrLeft (fun _ : I ↦ ENNReal) e
  have hcomp :
      es ∘ measureDisjointSetTuple
        (fun i ↦ (((e i : I) : BoundedMeasurableSet (E := E)).1 : Set E)) =
        fun μ : Measure E ↦
          I.restrict (measureBoundedSetEvaluationFamily (E := E) μ) := by
    funext μ
    ext i
    -- Proof comment: `piCongrLeft` only reindexes the same finite coordinate tuple.
    have hcoord :
        es (measureDisjointSetTuple
            (fun i ↦ (((e i : I) : BoundedMeasurableSet (E := E)).1 : Set E)) μ) i =
          measureDisjointSetTuple
            (fun i ↦ (((e i : I) : BoundedMeasurableSet (E := E)).1 : Set E)) μ (e.symm i) := by
      simpa [es] using
        (Equiv.piCongrLeft_apply_apply
          (fun _ : I ↦ ENNReal)
          e
          (measureDisjointSetTuple
            (fun i ↦ (((e i : I) : BoundedMeasurableSet (E := E)).1 : Set E)) μ)
          (e.symm i))
    simpa [measureDisjointSetTuple, measureBoundedSetEvaluationFamily,
      Finset.restrict] using hcoord
  simpa [e, es] using hcomp

/-- Helper for Corollary 24.9: any finite bounded-set tuple factors through the disjoint tuple of
its nonempty membership-pattern cells. -/
private theorem boundedSetTuple_factorsThroughPatternCells {m : ℕ}
    (As : Fin m → BoundedMeasurableSet (E := E)) :
    ∃ k : ℕ, ∃ Bs : Fin k → BoundedMeasurableSet (E := E),
      Pairwise (fun i j ↦ Disjoint ((Bs i).1 : Set E) ((Bs j).1 : Set E)) ∧
      ∃ collapse : (Fin k → ENNReal) → Fin m → ENNReal,
        Measurable collapse ∧
        ∀ μ : Measure E,
          measureDisjointSetTuple (fun i ↦ (As i).1) μ =
            collapse (measureDisjointSetTuple (fun j ↦ (Bs j).1) μ) := by
  classical
  let patterns : Finset (Finset (Fin m)) :=
    ((Finset.univ : Finset (Fin m)).powerset.filter Finset.Nonempty)
  let k : ℕ := patterns.card
  let e : Fin k ≃ patterns :=
    (Fintype.equivFinOfCardEq (show Fintype.card patterns = patterns.card by simp)).symm
  have hpattern_nonempty :
      ∀ j : Fin k, (((e j : patterns) : Finset (Fin m))).Nonempty := by
    intro j
    exact (Finset.mem_filter.mp (show (((e j : patterns) : Finset (Fin m))) ∈ patterns from (e j).2)).2
  let Bs : Fin k → BoundedMeasurableSet (E := E) := fun j ↦
    ⟨membershipPatternCell As ((e j : patterns) : Finset (Fin m)),
      measurableSet_membershipPatternCell (E := E) As ((e j : patterns) : Finset (Fin m)),
      isBounded_membershipPatternCell (E := E) As (hpattern_nonempty j)⟩
  have hBs_pairwise :
      Pairwise (fun i j ↦ Disjoint (((Bs i).1 : Set E)) (((Bs j).1 : Set E))) := by
    intro i j hij
    have hpatterns_ne :
        (((e i : patterns) : Finset (Fin m))) ≠ (((e j : patterns) : Finset (Fin m))) := by
      intro hEq
      apply hij
      apply e.injective
      apply Subtype.ext
      simpa using hEq
    simpa [Bs] using disjoint_membershipPatternCell (E := E) As hpatterns_ne
  let supportIndices : Fin m → Finset (Fin k) := fun i ↦
    Finset.univ.filter (fun j : Fin k ↦ i ∈ (((e j : patterns) : Finset (Fin m))))
  let collapse : (Fin k → ENNReal) → Fin m → ENNReal := fun z i ↦
    Finset.sum (supportIndices i) fun j ↦ z j
  have hcollapse_meas : Measurable collapse := by
    -- Proof comment: each coordinate is a finite sum of measurable coordinate projections.
    exact measurable_pi_lambda _ fun i ↦
      Finset.measurable_sum _ fun j _ ↦ measurable_pi_apply j
  have hfactor :
      ∀ μ : Measure E,
        measureDisjointSetTuple (fun i ↦ (As i).1) μ =
          collapse (measureDisjointSetTuple (fun j ↦ (Bs j).1) μ) := by
    intro μ
    ext i
    let Si : Finset (Fin k) := supportIndices i
    have hSi_disjoint :
        Set.PairwiseDisjoint (↑Si : Set (Fin k)) (fun j ↦ (((Bs j).1 : Set E))) := by
      intro a ha b hb hab
      exact hBs_pairwise hab
    have hAs_union :
        (As i).1 = ⋃ j ∈ Si, (((Bs j).1 : Set E)) := by
      ext x
      constructor
      · intro hx
        let sx : Finset (Fin m) :=
          (Finset.univ : Finset (Fin m)).filter fun j ↦ x ∈ (As j).1
        have hi_sx : i ∈ sx := by
          simp [sx, hx]
        have hsx_mem_patterns : sx ∈ patterns := by
          refine Finset.mem_filter.2 ?_
          constructor
          · exact Finset.mem_powerset.2 (by intro j _; simp)
          · exact ⟨i, hi_sx⟩
        let p : patterns := ⟨sx, hsx_mem_patterns⟩
        have hxcell : x ∈ membershipPatternCell As sx := by
          intro j
          by_cases hj : x ∈ (As j).1
          · simp [sx, hj]
          · simp [sx, hj]
        have hxBs : x ∈ (((Bs (e.symm p)).1 : Set E)) := by
          simpa [Bs, p] using hxcell
        have hmemSi : e.symm p ∈ Si := by
          simp [Si, supportIndices, p, sx, hi_sx]
        exact Set.mem_biUnion hmemSi hxBs
      · intro hx
        simp only [Set.mem_iUnion] at hx
        rcases hx with ⟨j, hj⟩
        rcases hj with ⟨hjSi, hxBj⟩
        have hi_pattern : i ∈ (((e j : patterns) : Finset (Fin m))) := by
          simp [Si, supportIndices] at hjSi
          exact hjSi
        have hxcell :
            x ∈ membershipPatternCell As (((e j : patterns) : Finset (Fin m))) := by
          simpa [Bs] using hxBj
        exact (hxcell i).2 hi_pattern
    -- Proof comment: each original set is the finite disjoint union of the cells that carry
    -- the corresponding membership pattern.
    calc
      measureDisjointSetTuple (fun j ↦ (As j).1) μ i = μ ((As i).1) := by
        rfl
      _ = μ (⋃ j ∈ Si, (((Bs j).1 : Set E))) := by
        rw [hAs_union]
      _ = Finset.sum Si (fun j ↦ μ (((Bs j).1 : Set E))) := by
        rw [measure_biUnion_finset hSi_disjoint]
        intro j hj
        exact (Bs j).2.1
      _ = collapse (measureDisjointSetTuple (fun j ↦ (Bs j).1) μ) i := by
        simp [collapse, Si, supportIndices, measureDisjointSetTuple]
  exact ⟨k, Bs, hBs_pairwise, collapse, hcollapse_meas, hfactor⟩

/-- Helper for Corollary 24.9: equality of the pairwise-disjoint bounded-set tuple laws implies
equality of the law of any finite bounded-set tuple. -/
private theorem identDistrib_boundedSetTuple_of_boundedEvalIdentDistrib
    {P : ProbabilityMeasure Ω} {Q : ProbabilityMeasure Ω'}
    {X : Ω → Measure E} {Y : Ω' → Measure E} {m : ℕ}
    (As : Fin m → BoundedMeasurableSet (E := E))
    (hX_indep : HasIndependentIncrements P X)
    (hY_indep : HasIndependentIncrements Q Y)
    (h_eval :
      ∀ A : Set E, MeasurableSet A → Bornology.IsBounded A →
        IdentDistrib
          (fun ω ↦ X ω A)
          (fun ω ↦ Y ω A)
          (P : Measure Ω) (Q : Measure Ω')) :
    IdentDistrib
      (fun ω ↦ measureDisjointSetTuple (fun i ↦ (As i).1) (X ω))
      (fun ω ↦ measureDisjointSetTuple (fun i ↦ (As i).1) (Y ω))
      (P : Measure Ω) (Q : Measure Ω') := by
  obtain ⟨k, Bs, hBs_pairwise, collapse, hcollapse_meas, hfactor⟩ :=
    boundedSetTuple_factorsThroughPatternCells (E := E) As
  have hBs_ident :
      IdentDistrib
        (fun ω ↦ measureDisjointSetTuple (fun j ↦ (Bs j).1) (X ω))
        (fun ω ↦ measureDisjointSetTuple (fun j ↦ (Bs j).1) (Y ω))
        (P : Measure Ω) (Q : Measure Ω') :=
    identDistrib_disjointMeasureSetTuple_of_boundedEvalIdentDistrib
      (E := E) (P := P) (Q := Q)
      (X := X) (Y := Y) (fun j ↦ (Bs j).1)
      (fun j ↦ (Bs j).2.1) (fun j ↦ (Bs j).2.2) hBs_pairwise
      hX_indep hY_indep h_eval
  have hcollapse_ident :
      IdentDistrib
        (fun ω ↦ collapse (measureDisjointSetTuple (fun j ↦ (Bs j).1) (X ω)))
        (fun ω ↦ collapse (measureDisjointSetTuple (fun j ↦ (Bs j).1) (Y ω)))
        (P : Measure Ω) (Q : Measure Ω') :=
    hBs_ident.comp hcollapse_meas
  have hXeq :
      (fun ω ↦ collapse (measureDisjointSetTuple (fun j ↦ (Bs j).1) (X ω))) =ᵐ[(P : Measure Ω)]
        fun ω ↦ measureDisjointSetTuple (fun i ↦ (As i).1) (X ω) := by
    exact Filter.Eventually.of_forall fun ω ↦ (hfactor (X ω)).symm
  have hYeq :
      (fun ω ↦ collapse (measureDisjointSetTuple (fun j ↦ (Bs j).1) (Y ω))) =ᵐ[(Q : Measure Ω')]
        fun ω ↦ measureDisjointSetTuple (fun i ↦ (As i).1) (Y ω) := by
    exact Filter.Eventually.of_forall fun ω ↦ (hfactor (Y ω)).symm
  -- Proof comment: collapse the disjoint pattern-cell tuple back to the original tuple.
  exact
    (IdentDistrib.of_ae_eq hcollapse_ident.aemeasurable_fst hXeq).symm.trans
      (hcollapse_ident.trans (IdentDistrib.of_ae_eq hcollapse_ident.aemeasurable_snd hYeq))

/-- Helper for Corollary 24.9: the full bounded-set evaluation process law is determined by the
one-dimensional bounded evaluations and independent increments. -/
private theorem map_boundedSetEvaluationFamily_eq_of_boundedEvalIdentDistrib
    {P : ProbabilityMeasure Ω} {Q : ProbabilityMeasure Ω'}
    {X : Ω → Measure E} {Y : Ω' → Measure E}
    (hX_random : IsRandomMeasure P X) (hY_random : IsRandomMeasure Q Y)
    (hX_indep : HasIndependentIncrements P X)
    (hY_indep : HasIndependentIncrements Q Y)
    (h_eval :
      ∀ A : Set E, MeasurableSet A → Bornology.IsBounded A →
        IdentDistrib
          (fun ω ↦ X ω A)
          (fun ω ↦ Y ω A)
          (P : Measure Ω) (Q : Measure Ω')) :
    Measure.map
        (fun ω ↦ fun A : BoundedMeasurableSet (E := E) ↦ X ω A.1)
        (P : Measure Ω) =
      Measure.map
        (fun ω ↦ fun A : BoundedMeasurableSet (E := E) ↦ Y ω A.1)
        (Q : Measure Ω') := by
  classical
  let evalProcessX : BoundedMeasurableSet (E := E) → Ω → ENNReal := fun A ω ↦ X ω A.1
  let evalProcessY : BoundedMeasurableSet (E := E) → Ω' → ENNReal := fun A ω ↦ Y ω A.1
  have hrestrict :
      ∀ I : Finset (BoundedMeasurableSet (E := E)),
        Measure.map (fun ω ↦ I.restrict (evalProcessX · ω)) (P : Measure Ω) =
          Measure.map (fun ω ↦ I.restrict (evalProcessY · ω)) (Q : Measure Ω') := by
    intro I
    let e : Fin I.card ≃ I :=
      (Fintype.equivFinOfCardEq (show Fintype.card I = I.card by simp)).symm
    let es : (Fin I.card → ENNReal) ≃ᵐ (I → ENNReal) :=
      MeasurableEquiv.piCongrLeft (fun _ : I ↦ ENNReal) e
    let AsI : Fin I.card → BoundedMeasurableSet (E := E) := fun i ↦ (e i : I)
    have htuple :
        IdentDistrib
          (fun ω ↦ measureDisjointSetTuple (fun i ↦ (AsI i).1) (X ω))
          (fun ω ↦ measureDisjointSetTuple (fun i ↦ (AsI i).1) (Y ω))
          (P : Measure Ω) (Q : Measure Ω') :=
      identDistrib_boundedSetTuple_of_boundedEvalIdentDistrib
        (E := E) (P := P) (Q := Q) (X := X) (Y := Y) AsI hX_indep hY_indep h_eval
    have hcomp :
        es ∘ measureDisjointSetTuple (fun i ↦ (AsI i).1) =
          fun μ : Measure E ↦
            I.restrict (measureBoundedSetEvaluationFamily (E := E) μ) :=
      restrict_boundedSetEvaluationFamily_eq_piCongrLeft_comp (E := E) I
    have hreindexed :
        IdentDistrib
          (fun ω ↦ I.restrict (measureBoundedSetEvaluationFamily (E := E) (X ω)))
          (fun ω ↦ I.restrict (measureBoundedSetEvaluationFamily (E := E) (Y ω)))
          (P : Measure Ω) (Q : Measure Ω') := by
      have htuple_reindexed :
          IdentDistrib
            (fun ω ↦ es (measureDisjointSetTuple (fun i ↦ (AsI i).1) (X ω)))
            (fun ω ↦ es (measureDisjointSetTuple (fun i ↦ (AsI i).1) (Y ω)))
            (P : Measure Ω) (Q : Measure Ω') :=
        htuple.comp es.measurable
      have hXeq :
          (fun ω ↦ es (measureDisjointSetTuple (fun i ↦ (AsI i).1) (X ω))) =ᵐ[(P : Measure Ω)]
            fun ω ↦ I.restrict (measureBoundedSetEvaluationFamily (E := E) (X ω)) := by
        exact Filter.Eventually.of_forall fun ω ↦ congrFun hcomp (X ω)
      have hYeq :
          (fun ω ↦ es (measureDisjointSetTuple (fun i ↦ (AsI i).1) (Y ω))) =ᵐ[(Q : Measure Ω')]
            fun ω ↦ I.restrict (measureBoundedSetEvaluationFamily (E := E) (Y ω)) := by
        exact Filter.Eventually.of_forall fun ω ↦ congrFun hcomp (Y ω)
      -- Proof comment: finite restrictions are the same tuple laws after reindexing the
      -- coordinates through `piCongrLeft`.
      exact
        (IdentDistrib.of_ae_eq htuple_reindexed.aemeasurable_fst hXeq).symm.trans
          (htuple_reindexed.trans (IdentDistrib.of_ae_eq htuple_reindexed.aemeasurable_snd hYeq))
    simpa [evalProcessX, evalProcessY] using hreindexed.map_eq
  have hproc_measX :
      AEMeasurable (fun ω ↦ (evalProcessX · ω)) (P : Measure Ω) := by
    exact
      (measurable_pi_lambda _ fun A ↦
        (Measure.measurable_coe A.2.1).comp hX_random.measurable).aemeasurable
  have hproc_measY :
      AEMeasurable (fun ω ↦ (evalProcessY · ω)) (Q : Measure Ω') := by
    exact
      (measurable_pi_lambda _ fun A ↦
        (Measure.measurable_coe A.2.1).comp hY_random.measurable).aemeasurable
  have hprojP :
      IsProjectiveLimit
        (Measure.map (fun ω ↦ (evalProcessX · ω)) (P : Measure Ω))
        (fun I : Finset (BoundedMeasurableSet (E := E)) ↦
          Measure.map (fun ω ↦ I.restrict (evalProcessX · ω)) (P : Measure Ω)) :=
    ProbabilityTheory.isProjectiveLimit_map hproc_measX
  have hprojQ :
      IsProjectiveLimit
        (Measure.map (fun ω ↦ (evalProcessY · ω)) (Q : Measure Ω'))
        (fun I : Finset (BoundedMeasurableSet (E := E)) ↦
          Measure.map (fun ω ↦ I.restrict (evalProcessY · ω)) (Q : Measure Ω')) :=
    ProbabilityTheory.isProjectiveLimit_map hproc_measY
  -- Proof comment: equality of every finite bounded-set restriction determines the full process
  -- law by projective-limit uniqueness.
  refine hprojP.unique ?_
  simpa [hrestrict] using hprojQ

end BoundedEvaluationFamily

-- Proof sketch: apply the uniqueness theorem for independently scattered random measures from the
-- preceding development: finite-dimensional laws of the evaluations on pairwise disjoint bounded
-- measurable sets are products of the one-dimensional marginals, so equality of all marginals
-- forces equality of the law of the measure-valued random variable.
/-- Corollary 24.9: the distribution of a random measure with independent increments is uniquely
determined by the laws of the evaluations `X(A)` on bounded measurable sets `A`. -/
theorem identDistrib_of_bounded_eval_identDistrib_of_independentIncrements
    {P : ProbabilityMeasure Ω} {Q : ProbabilityMeasure Ω'}
    {X : Ω → Measure E} {Y : Ω' → Measure E}
    (hX_random : IsRandomMeasure P X) (hY_random : IsRandomMeasure Q Y)
    (hX_indep : HasIndependentIncrements P X)
    (hY_indep : HasIndependentIncrements Q Y)
    (h_eval :
      ∀ A : Set E, MeasurableSet A → Bornology.IsBounded A →
        IdentDistrib
          (fun ω ↦ X ω A)
          (fun ω ↦ Y ω A)
          (P : Measure Ω) (Q : Measure Ω')) :
    IdentDistrib X Y (P : Measure Ω) (Q : Measure Ω') := by
  let lawX : ProbabilityMeasure (Measure E) := P.map hX_random.aemeasurable
  let lawY : ProbabilityMeasure (Measure E) := Q.map hY_random.aemeasurable
  let evalFamily : Measure E → BoundedMeasurableSet (E := E) → ENNReal :=
    measureBoundedSetEvaluationFamily (E := E)
  have hmap_family :
      Measure.map
          (fun ω ↦ fun A : BoundedMeasurableSet (E := E) ↦ X ω A.1)
          (P : Measure Ω) =
        Measure.map
          (fun ω ↦ fun A : BoundedMeasurableSet (E := E) ↦ Y ω A.1)
          (Q : Measure Ω') :=
    map_boundedSetEvaluationFamily_eq_of_boundedEvalIdentDistrib
      (E := E) hX_random hY_random hX_indep hY_indep h_eval
  have hlaw_eq :
      lawX = lawY := by
    refine
      probabilityMeasureEqOfMapEqOfComapPi
        (ι := BoundedMeasurableSet (E := E))
        (α := fun _ ↦ ENNReal)
        (P := lawX)
        (Q := lawY)
        (X := evalFamily)
        ?_ ?_
    · simpa [evalFamily] using
        measureMeasurableSpace_eq_comap_boundedSetEvaluationFamily (E := E)
    · -- Proof comment: pushing the laws forward along the bounded evaluation family recovers the
      -- full bounded-evaluation process laws already matched above.
      calc
        Measure.map evalFamily (lawX : Measure (Measure E))
            = Measure.map
                (fun ω ↦ fun A : BoundedMeasurableSet (E := E) ↦ X ω A.1)
                (P : Measure Ω) := by
                  rw [ProbabilityMeasure.toMeasure_map,
                    Measure.map_map measurable_measureBoundedSetEvaluationFamily
                      hX_random.measurable]
                  rfl
        _ = Measure.map
              (fun ω ↦ fun A : BoundedMeasurableSet (E := E) ↦ Y ω A.1)
              (Q : Measure Ω') := hmap_family
        _ = Measure.map evalFamily (lawY : Measure (Measure E)) := by
              rw [ProbabilityMeasure.toMeasure_map,
                Measure.map_map measurable_measureBoundedSetEvaluationFamily
                  hY_random.measurable]
              rfl
  -- Proof comment: equal pushforward laws on `Measure E` are exactly identical distribution.
  refine ⟨hX_random.aemeasurable, hY_random.aemeasurable, ?_⟩
  simpa [lawX, lawY] using congrArg (fun μ : ProbabilityMeasure (Measure E) ↦ (μ : Measure (Measure E))) hlaw_eq

end ProbabilityTheory
