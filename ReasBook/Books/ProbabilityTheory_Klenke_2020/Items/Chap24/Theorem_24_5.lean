/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Books.ProbabilityTheory_Klenke_2020.Items.Chap24.Theorem_24_2

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open MeasureTheory

universe u

variable {E : Type u} [PseudoMetricSpace E] [MeasurableSpace E] [BorelSpace E]
  [LocallyCompactSpace E]
variable {n : ℕ}

/-- The finite tuple of integrals of a measure against nonnegative compactly supported continuous
test functions. -/
def random_measure_test_integral_tuple
    (fs : Fin n → CompactlySupportedContinuousMap E NNReal) :
    BoundedlyFiniteMeasure E → Fin n → ℝ :=
  fun μ i ↦ BoundedlyFiniteMeasure.nonnegativeVagueIntegral (fs i) μ

-- Proof sketch: unfold `random_measure_test_integral_tuple` and evaluate the resulting function at
-- the chosen index.
/-- Evaluating the integral tuple at a coordinate returns the corresponding nonnegative test
integral. -/
theorem random_measure_test_integral_tuple_apply
    (fs : Fin n → CompactlySupportedContinuousMap E NNReal)
    (μ : BoundedlyFiniteMeasure E) (i : Fin n) :
    random_measure_test_integral_tuple fs μ i =
      BoundedlyFiniteMeasure.nonnegativeVagueIntegral (fs i) μ := by
  -- Proof comment: this is just the defining value of the tuple function at coordinate `i`.
  rfl

/-- The finite tuple of evaluations of a measure on a family of sets. -/
def random_measure_disjoint_set_tuple (As : Fin n → Set E) :
    BoundedlyFiniteMeasure E → Fin n → ENNReal :=
  fun μ i ↦ (μ : Measure E) (As i)

-- Proof sketch: unfold `random_measure_disjoint_set_tuple` and read off the `i`-th coordinate.
/-- Evaluating the set tuple at a coordinate returns the measure of the corresponding set. -/
theorem random_measure_disjoint_set_tuple_apply (As : Fin n → Set E)
    (μ : BoundedlyFiniteMeasure E) (i : Fin n) :
    random_measure_disjoint_set_tuple As μ i = (μ : Measure E) (As i) := by
  -- Proof comment: unfold the tuple map and read off the `i`-th coordinate.
  rfl

section ChapterAmbient

variable [PolishSpace E] [T2Space E]

/-- Helper for Theorem 24.5: bounded measurable subsets of `E`. -/
private abbrev BoundedMeasurableSet :=
  {A : Set E // MeasurableSet A ∧ Bornology.IsBounded A}

/-- Helper for Theorem 24.5: the full family of nonnegative test-integral coordinates. -/
private def randomMeasureNonnegativeIntegralFamily :
    BoundedlyFiniteMeasure E → CompactlySupportedContinuousMap E NNReal → ℝ :=
  fun μ f ↦ BoundedlyFiniteMeasure.nonnegativeVagueIntegral f μ

/-- Helper for Theorem 24.5: the full family of bounded-set evaluation coordinates. -/
private def randomMeasureBoundedSetEvaluationFamily :
    BoundedlyFiniteMeasure E → BoundedMeasurableSet (E := E) → ENNReal :=
  fun μ A ↦ (μ : Measure E) A.1

/-- Helper for Theorem 24.5: the full integral family is measurable coordinatewise. -/
private theorem measurable_randomMeasureNonnegativeIntegralFamily :
    Measurable (randomMeasureNonnegativeIntegralFamily (E := E)) := by
  -- Proof comment: product measurability reduces to measurability of each test integral.
  exact measurable_pi_lambda _ fun f ↦ measurable_nonnegativeVagueIntegral f

/-- Helper for Theorem 24.5: the full bounded-set evaluation family is measurable coordinatewise. -/
private theorem measurable_randomMeasureBoundedSetEvaluationFamily :
    Measurable (randomMeasureBoundedSetEvaluationFamily (E := E)) := by
  -- Proof comment: each coordinate is one of the defining measurable bounded-set evaluations.
  exact measurable_pi_lambda _ fun A ↦ measurable_apply_of_isBounded A.1 A.2.1 A.2.2

/-- Helper for Theorem 24.5: the nonnegative-vague-integral sigma-algebra is the pullback of the
product sigma-algebra along the full integral family. -/
private theorem nonnegativeIntegralMeasurableSpace_eq_comap_family :
    nonnegativeCompactlySupportedContinuousIntegralMeasurableSpace E =
      MeasurableSpace.comap
        (randomMeasureNonnegativeIntegralFamily (E := E))
        (inferInstance :
          MeasurableSpace (CompactlySupportedContinuousMap E NNReal → ℝ)) := by
  -- Proof comment: the product sigma-algebra is the supremum of the coordinate sigma-algebras.
  rw [nonnegativeCompactlySupportedContinuousIntegralMeasurableSpace, MeasurableSpace.pi,
    MeasurableSpace.comap_iSup]
  refine iSup_congr fun f => ?_
  rw [MeasurableSpace.comap_comp]
  change MeasurableSpace.comap (BoundedlyFiniteMeasure.nonnegativeVagueIntegral f) (borel ℝ) =
    MeasurableSpace.comap
      (fun μ : BoundedlyFiniteMeasure E ↦
        BoundedlyFiniteMeasure.nonnegativeVagueIntegral f μ)
      Real.measurableSpace
  rfl

/-- Helper for Theorem 24.5: the random-measure sigma-algebra is the pullback of the product
sigma-algebra along the full bounded-set evaluation family. -/
private theorem randomMeasureMeasurableSpace_eq_comap_boundedSetEvaluationFamily :
    randomMeasureMeasurableSpace E =
      MeasurableSpace.comap
        (randomMeasureBoundedSetEvaluationFamily (E := E))
        (inferInstance : MeasurableSpace (BoundedMeasurableSet (E := E) → ENNReal)) := by
  -- Proof comment: this is the defining supremum formula rewritten as a product-space comap.
  rw [randomMeasureMeasurableSpace_def, MeasurableSpace.pi, MeasurableSpace.comap_iSup]
  refine le_antisymm ?_ ?_
  · refine iSup_le ?_
    intro A
    refine iSup_le ?_
    intro hA
    refine iSup_le ?_
    intro hA_bdd
    refine le_iSup_of_le ⟨A, hA, hA_bdd⟩ ?_
    rw [MeasurableSpace.comap_comp]
    rfl
  · refine iSup_le ?_
    intro A
    rcases A with ⟨A, hA, hA_bdd⟩
    exact le_iSup_of_le A <| le_iSup_of_le hA <| le_iSup_of_le hA_bdd <| by
      rw [MeasurableSpace.comap_comp]
      rfl

/-- Helper for Theorem 24.5: a probability law on a pullback product sigma-algebra is determined
by its pushforward along the full coordinate family. -/
private theorem probabilityMeasure_eq_of_map_eq_of_comap_pi
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
    -- Proof comment: pull back the canonical cylinder generator of the product sigma-algebra.
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

/-- Helper for Theorem 24.5: finite tuples of nonnegative test integrals are measurable. -/
private theorem measurable_random_measure_test_integral_tuple
    {m : ℕ} (fs : Fin m → CompactlySupportedContinuousMap E NNReal) :
    Measurable (random_measure_test_integral_tuple fs) := by
  -- Proof comment: each coordinate is a measurable nonnegative vague integral.
  exact measurable_pi_lambda _ fun i ↦ measurable_nonnegativeVagueIntegral (fs i)

/-- Helper for Theorem 24.5: finite tuples of bounded-set evaluations are measurable. -/
private theorem measurable_random_measure_disjoint_set_tuple
    {m : ℕ} (As : Fin m → Set E) (hA : ∀ i, MeasurableSet (As i))
    (hA_bdd : ∀ i, Bornology.IsBounded (As i)) :
    Measurable (random_measure_disjoint_set_tuple As) := by
  -- Proof comment: each coordinate is one bounded-set evaluation map.
  exact measurable_pi_lambda _ fun i ↦ measurable_apply_of_isBounded (As i) (hA i) (hA_bdd i)

/-- Helper for Theorem 24.5: reindexing a finite tuple of test functions identifies it with the
restriction of the full integral family to that finite set. -/
private theorem restrict_nonnegativeIntegralFamily_eq_piCongrLeft_comp
    (I : Finset (CompactlySupportedContinuousMap E NNReal)) :
    let e : Fin I.card ≃ I :=
      (Fintype.equivFinOfCardEq (show Fintype.card I = I.card by simp)).symm
    let es : (Fin I.card → ℝ) ≃ᵐ (I → ℝ) :=
      MeasurableEquiv.piCongrLeft (fun _ : I ↦ ℝ) e
    es ∘ random_measure_test_integral_tuple
      (fun i ↦ ((e i : I) : CompactlySupportedContinuousMap E NNReal)) =
      fun μ : BoundedlyFiniteMeasure E ↦
        I.restrict (randomMeasureNonnegativeIntegralFamily (E := E) μ) := by
  classical
  let e : Fin I.card ≃ I :=
    (Fintype.equivFinOfCardEq (show Fintype.card I = I.card by simp)).symm
  let es : (Fin I.card → ℝ) ≃ᵐ (I → ℝ) :=
    MeasurableEquiv.piCongrLeft (fun _ : I ↦ ℝ) e
  have hcomp :
      es ∘ random_measure_test_integral_tuple
        (fun i ↦ ((e i : I) : CompactlySupportedContinuousMap E NNReal)) =
        fun μ : BoundedlyFiniteMeasure E ↦
          I.restrict (randomMeasureNonnegativeIntegralFamily (E := E) μ) := by
    funext μ
    ext i
    -- Proof comment: `piCongrLeft` only reindexes the same coordinate tuple.
    have hcoord :
        es (random_measure_test_integral_tuple
            (fun i ↦ ((e i : I) : CompactlySupportedContinuousMap E NNReal)) μ) i =
          random_measure_test_integral_tuple
            (fun i ↦ ((e i : I) : CompactlySupportedContinuousMap E NNReal)) μ (e.symm i) := by
      simpa [es] using
        (Equiv.piCongrLeft_apply_apply
          (fun _ : I ↦ ℝ)
          e
          (random_measure_test_integral_tuple
            (fun i ↦ ((e i : I) : CompactlySupportedContinuousMap E NNReal)) μ)
          (e.symm i))
    simpa [random_measure_test_integral_tuple, randomMeasureNonnegativeIntegralFamily,
      Finset.restrict] using hcoord
  simpa [e, es] using hcomp

/-- Helper for Theorem 24.5: finite-dimensional equality of the nonnegative test-integral tuples
forces equality of the full product-space law of the integral family. -/
private theorem map_nonnegativeIntegralFamily_eq_of_finiteDimensionalDistributions
    {P Q : ProbabilityMeasure (BoundedlyFiniteMeasure E)}
    (h :
      ∀ n : ℕ, ∀ fs : Fin n → CompactlySupportedContinuousMap E NNReal,
        Measure.map (random_measure_test_integral_tuple fs) (P : Measure (BoundedlyFiniteMeasure E)) =
          Measure.map (random_measure_test_integral_tuple fs) (Q : Measure (BoundedlyFiniteMeasure E))) :
    Measure.map (randomMeasureNonnegativeIntegralFamily (E := E))
        (P : Measure (BoundedlyFiniteMeasure E)) =
      Measure.map (randomMeasureNonnegativeIntegralFamily (E := E))
        (Q : Measure (BoundedlyFiniteMeasure E)) := by
  classical
  have hrestrict :
      ∀ I : Finset (CompactlySupportedContinuousMap E NNReal),
        Measure.map (fun μ : BoundedlyFiniteMeasure E ↦
            I.restrict (randomMeasureNonnegativeIntegralFamily (E := E) μ))
            (P : Measure (BoundedlyFiniteMeasure E)) =
          Measure.map (fun μ : BoundedlyFiniteMeasure E ↦
            I.restrict (randomMeasureNonnegativeIntegralFamily (E := E) μ))
            (Q : Measure (BoundedlyFiniteMeasure E)) := by
    intro I
    let e : Fin I.card ≃ I :=
      (Fintype.equivFinOfCardEq (show Fintype.card I = I.card by simp)).symm
    let es : (Fin I.card → ℝ) ≃ᵐ (I → ℝ) :=
      MeasurableEquiv.piCongrLeft (fun _ : I ↦ ℝ) e
    let fs : Fin I.card → CompactlySupportedContinuousMap E NNReal :=
      fun i ↦ ((e i : I) : CompactlySupportedContinuousMap E NNReal)
    have hcomp :
        es ∘ random_measure_test_integral_tuple fs =
          fun μ : BoundedlyFiniteMeasure E ↦
            I.restrict (randomMeasureNonnegativeIntegralFamily (E := E) μ) :=
      restrict_nonnegativeIntegralFamily_eq_piCongrLeft_comp (E := E) I
    have htuple :
        Measure.map (random_measure_test_integral_tuple fs) (P : Measure (BoundedlyFiniteMeasure E)) =
          Measure.map (random_measure_test_integral_tuple fs)
            (Q : Measure (BoundedlyFiniteMeasure E)) :=
      h I.card fs
    have hmeasTuple : Measurable (random_measure_test_integral_tuple fs) :=
      measurable_random_measure_test_integral_tuple fs
    -- Proof comment: rewrite the finite restriction as a reindexed tuple law, then use the
    -- assumed finite-dimensional equality.
    calc
      Measure.map (fun μ : BoundedlyFiniteMeasure E ↦
          I.restrict (randomMeasureNonnegativeIntegralFamily (E := E) μ))
          (P : Measure (BoundedlyFiniteMeasure E))
          = (Measure.map (random_measure_test_integral_tuple fs)
              (P : Measure (BoundedlyFiniteMeasure E))).map es := by
              rw [← hcomp, Measure.map_map es.measurable hmeasTuple]
      _ = (Measure.map (random_measure_test_integral_tuple fs)
            (Q : Measure (BoundedlyFiniteMeasure E))).map es := by
            exact congrArg (fun m : Measure (Fin I.card → ℝ) ↦ m.map es) htuple
      _ = Measure.map (fun μ : BoundedlyFiniteMeasure E ↦
            I.restrict (randomMeasureNonnegativeIntegralFamily (E := E) μ))
            (Q : Measure (BoundedlyFiniteMeasure E)) := by
            rw [← hcomp, Measure.map_map es.measurable hmeasTuple]
  have hprojP :
      IsProjectiveLimit
        (Measure.map (randomMeasureNonnegativeIntegralFamily (E := E))
          (P : Measure (BoundedlyFiniteMeasure E)))
        (fun I : Finset (CompactlySupportedContinuousMap E NNReal) ↦
          Measure.map (fun μ : BoundedlyFiniteMeasure E ↦
            I.restrict (randomMeasureNonnegativeIntegralFamily (E := E) μ))
            (P : Measure (BoundedlyFiniteMeasure E))) := by
    -- Proof comment: the full coordinate law is the projective limit of its finite restrictions.
    simpa [randomMeasureNonnegativeIntegralFamily] using
      (ProbabilityTheory.isProjectiveLimit_map
        (P := (P : Measure (BoundedlyFiniteMeasure E)))
        (X := fun f (μ : BoundedlyFiniteMeasure E) ↦
          randomMeasureNonnegativeIntegralFamily (E := E) μ f)
        measurable_randomMeasureNonnegativeIntegralFamily.aemeasurable)
  have hprojQ :
      IsProjectiveLimit
        (Measure.map (randomMeasureNonnegativeIntegralFamily (E := E))
          (Q : Measure (BoundedlyFiniteMeasure E)))
        (fun I : Finset (CompactlySupportedContinuousMap E NNReal) ↦
          Measure.map (fun μ : BoundedlyFiniteMeasure E ↦
            I.restrict (randomMeasureNonnegativeIntegralFamily (E := E) μ))
            (Q : Measure (BoundedlyFiniteMeasure E))) := by
    -- Proof comment: the same projective-limit description holds for `Q`.
    simpa [randomMeasureNonnegativeIntegralFamily] using
      (ProbabilityTheory.isProjectiveLimit_map
        (P := (Q : Measure (BoundedlyFiniteMeasure E)))
        (X := fun f (μ : BoundedlyFiniteMeasure E) ↦
          randomMeasureNonnegativeIntegralFamily (E := E) μ f)
        measurable_randomMeasureNonnegativeIntegralFamily.aemeasurable)
  -- Proof comment: equality of all finite restrictions determines the full product-space law.
  refine hprojP.unique ?_
  simpa [hrestrict] using hprojQ

/-- Helper for Theorem 24.5: the membership-pattern cell of a finite bounded-set family records
exactly which sets contain a point. -/
private def membershipPatternCell {m : ℕ} (As : Fin m → BoundedMeasurableSet (E := E))
    (s : Finset (Fin m)) : Set E :=
  {x | ∀ i, x ∈ (As i).1 ↔ i ∈ s}

/-- Helper for Theorem 24.5: every membership-pattern cell is measurable. -/
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
  -- Proof comment: once the cell is written as a finite intersection of measurable sets and
  -- complements, measurability is immediate.
  rw [hrepr]
  exact MeasurableSet.iInter fun i ↦ by
    by_cases hi : i ∈ s
    · simpa [hi] using (As i).2.1
    · simpa [hi] using (As i).2.1.compl

/-- Helper for Theorem 24.5: a nonempty membership-pattern cell stays bounded because it lies in
one of the original bounded sets. -/
private theorem isBounded_membershipPatternCell {m : ℕ}
    (As : Fin m → BoundedMeasurableSet (E := E)) {s : Finset (Fin m)} (hs : s.Nonempty) :
    Bornology.IsBounded (membershipPatternCell As s) := by
  rcases hs with ⟨i, hi⟩
  -- Proof comment: points in the cell satisfy the defining membership pattern, hence belong to
  -- `As i`.
  exact (As i).2.2.subset fun x hx ↦ (hx i).2 hi

/-- Helper for Theorem 24.5: distinct membership patterns define disjoint cells. -/
private theorem disjoint_membershipPatternCell {m : ℕ}
    (As : Fin m → BoundedMeasurableSet (E := E)) {s t : Finset (Fin m)} (hst : s ≠ t) :
    Disjoint (membershipPatternCell As s) (membershipPatternCell As t) := by
  -- Proof comment: a point in both cells would induce the same membership pattern twice.
  refine Set.disjoint_left.2 fun x hsx htx ↦ ?_
  apply hst
  ext i
  constructor
  · intro hi
    exact (htx i).1 ((hsx i).2 hi)
  · intro hi
    exact (hsx i).1 ((htx i).2 hi)

/-- Helper for Theorem 24.5: reindexing a finite bounded-set tuple identifies it with the
restriction of the full bounded-set evaluation family. -/
private theorem restrict_boundedSetEvaluationFamily_eq_piCongrLeft_comp
    (I : Finset (BoundedMeasurableSet (E := E))) :
    let e : Fin I.card ≃ I :=
      (Fintype.equivFinOfCardEq (show Fintype.card I = I.card by simp)).symm
    let es : (Fin I.card → ENNReal) ≃ᵐ (I → ENNReal) :=
      MeasurableEquiv.piCongrLeft (fun _ : I ↦ ENNReal) e
    es ∘ random_measure_disjoint_set_tuple
      (fun i ↦ (((e i : I) : BoundedMeasurableSet (E := E)).1 : Set E)) =
      fun μ : BoundedlyFiniteMeasure E ↦
        I.restrict (randomMeasureBoundedSetEvaluationFamily (E := E) μ) := by
  classical
  let e : Fin I.card ≃ I :=
    (Fintype.equivFinOfCardEq (show Fintype.card I = I.card by simp)).symm
  let es : (Fin I.card → ENNReal) ≃ᵐ (I → ENNReal) :=
    MeasurableEquiv.piCongrLeft (fun _ : I ↦ ENNReal) e
  have hcomp :
      es ∘ random_measure_disjoint_set_tuple
        (fun i ↦ (((e i : I) : BoundedMeasurableSet (E := E)).1 : Set E)) =
        fun μ : BoundedlyFiniteMeasure E ↦
          I.restrict (randomMeasureBoundedSetEvaluationFamily (E := E) μ) := by
    funext μ
    ext i
    -- Proof comment: this is the same finite-restriction reindexing as in the integral branch.
    have hcoord :
        es (random_measure_disjoint_set_tuple
            (fun i ↦ (((e i : I) : BoundedMeasurableSet (E := E)).1 : Set E)) μ) i =
          random_measure_disjoint_set_tuple
            (fun i ↦ (((e i : I) : BoundedMeasurableSet (E := E)).1 : Set E)) μ (e.symm i) := by
      simpa [es] using
        (Equiv.piCongrLeft_apply_apply
          (fun _ : I ↦ ENNReal)
          e
          (random_measure_disjoint_set_tuple
            (fun i ↦ (((e i : I) : BoundedMeasurableSet (E := E)).1 : Set E)) μ)
          (e.symm i))
    simpa [random_measure_disjoint_set_tuple, randomMeasureBoundedSetEvaluationFamily,
      Finset.restrict] using hcoord
  simpa [e, es] using hcomp

/-- Helper for Theorem 24.5: any bounded-set tuple factors through the disjoint tuple of its
nonempty membership-pattern cells. -/
private theorem boundedSetTuple_factorsThroughPatternCells {m : ℕ}
    (As : Fin m → BoundedMeasurableSet (E := E)) :
    ∃ k : ℕ, ∃ Bs : Fin k → BoundedMeasurableSet (E := E),
      Pairwise (fun i j ↦ Disjoint ((Bs i).1 : Set E) ((Bs j).1 : Set E)) ∧
      ∃ collapse : (Fin k → ENNReal) → Fin m → ENNReal,
        Measurable collapse ∧
        ∀ μ : BoundedlyFiniteMeasure E,
          random_measure_disjoint_set_tuple (fun i ↦ (As i).1) μ =
            collapse (random_measure_disjoint_set_tuple (fun j ↦ (Bs j).1) μ) := by
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
  -- Proof comment: package each nonempty Boolean pattern cell as a bounded measurable set.
  let Bs : Fin k → BoundedMeasurableSet (E := E) := fun j ↦
    ⟨membershipPatternCell As ((e j : patterns) : Finset (Fin m)),
      measurableSet_membershipPatternCell As ((e j : patterns) : Finset (Fin m)),
      isBounded_membershipPatternCell As (hpattern_nonempty j)⟩
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
    simpa [Bs] using disjoint_membershipPatternCell As hpatterns_ne
  -- Proof comment: collapse the disjoint pattern-cell coordinates back to the original bounded
  -- tuple by summing all cells whose pattern contains the chosen index.
  let supportIndices : Fin m → Finset (Fin k) := fun i ↦
    Finset.univ.filter (fun j : Fin k ↦ i ∈ (((e j : patterns) : Finset (Fin m))))
  let collapse : (Fin k → ENNReal) → Fin m → ENNReal := fun z i ↦
    Finset.sum (supportIndices i) fun j ↦ z j
  have hcollapse_meas : Measurable collapse := by
    -- Proof comment: each coordinate is a finite sum of measurable coordinate projections.
    exact measurable_pi_lambda _ fun i ↦
      Finset.measurable_sum _ fun j _ ↦ measurable_pi_apply j
  have hfactor :
      ∀ μ : BoundedlyFiniteMeasure E,
        random_measure_disjoint_set_tuple (fun i ↦ (As i).1) μ =
          collapse (random_measure_disjoint_set_tuple (fun j ↦ (Bs j).1) μ) := by
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
    -- Proof comment: each original set is the finite disjoint union of the cells whose pattern
    -- contains the chosen index, so the corresponding measure is the finite sum of those cells.
    calc
      random_measure_disjoint_set_tuple (fun j ↦ (As j).1) μ i = (μ : Measure E) ((As i).1) := by
        rfl
      _ = (μ : Measure E) (⋃ j ∈ Si, (((Bs j).1 : Set E))) := by
        rw [hAs_union]
      _ = Finset.sum Si (fun j ↦ (μ : Measure E) (((Bs j).1 : Set E))) := by
        rw [measure_biUnion_finset hSi_disjoint]
        intro j hj
        exact (Bs j).2.1
      _ = collapse (random_measure_disjoint_set_tuple (fun j ↦ (Bs j).1) μ) i := by
        simp [collapse, Si, supportIndices, random_measure_disjoint_set_tuple]
  exact ⟨k, Bs, hBs_pairwise, collapse, hcollapse_meas, hfactor⟩

/-- Helper for Theorem 24.5: equality of the pairwise-disjoint bounded-set tuple laws implies
equality of the law of any bounded-set tuple. -/
private theorem map_boundedSetTuple_eq_of_disjointFiniteDimensionalDistributions
    {P Q : ProbabilityMeasure (BoundedlyFiniteMeasure E)}
    (h :
      ∀ n : ℕ, ∀ As : Fin n → Set E,
        (∀ i, MeasurableSet (As i)) →
        (∀ i, Bornology.IsBounded (As i)) →
        Pairwise (fun i j ↦ Disjoint (As i) (As j)) →
        Measure.map (random_measure_disjoint_set_tuple As) (P : Measure (BoundedlyFiniteMeasure E)) =
          Measure.map (random_measure_disjoint_set_tuple As) (Q : Measure (BoundedlyFiniteMeasure E)))
    {m : ℕ} (As : Fin m → BoundedMeasurableSet (E := E)) :
    Measure.map (random_measure_disjoint_set_tuple (fun i ↦ (As i).1))
        (P : Measure (BoundedlyFiniteMeasure E)) =
      Measure.map (random_measure_disjoint_set_tuple (fun i ↦ (As i).1))
        (Q : Measure (BoundedlyFiniteMeasure E)) := by
  obtain ⟨k, Bs, hBs_pairwise, collapse, hcollapse_meas, hfactor⟩ :=
    boundedSetTuple_factorsThroughPatternCells (E := E) As
  have hBs_map :
      Measure.map (random_measure_disjoint_set_tuple (fun j ↦ (Bs j).1))
          (P : Measure (BoundedlyFiniteMeasure E)) =
        Measure.map (random_measure_disjoint_set_tuple (fun j ↦ (Bs j).1))
          (Q : Measure (BoundedlyFiniteMeasure E)) := by
    -- Proof comment: the refined pattern-cell family is pairwise disjoint, so the hypothesis
    -- applies directly to its tuple law.
    exact h k (fun j ↦ (Bs j).1) (fun j ↦ (Bs j).2.1) (fun j ↦ (Bs j).2.2) hBs_pairwise
  have hmeasBs :
      Measurable (random_measure_disjoint_set_tuple (fun j ↦ (Bs j).1)) :=
    measurable_random_measure_disjoint_set_tuple (fun j ↦ (Bs j).1)
      (fun j ↦ (Bs j).2.1) (fun j ↦ (Bs j).2.2)
  -- Proof comment: push the disjoint-family equality through the measurable collapse map.
  calc
    Measure.map (random_measure_disjoint_set_tuple (fun i ↦ (As i).1))
        (P : Measure (BoundedlyFiniteMeasure E))
        = Measure.map (collapse ∘ random_measure_disjoint_set_tuple (fun j ↦ (Bs j).1))
            (P : Measure (BoundedlyFiniteMeasure E)) := by
            congr 1
            funext μ
            exact hfactor μ
    _ = (Measure.map (random_measure_disjoint_set_tuple (fun j ↦ (Bs j).1))
          (P : Measure (BoundedlyFiniteMeasure E))).map collapse := by
          rw [Measure.map_map hcollapse_meas hmeasBs]
    _ = (Measure.map (random_measure_disjoint_set_tuple (fun j ↦ (Bs j).1))
          (Q : Measure (BoundedlyFiniteMeasure E))).map collapse := by
          exact congrArg (fun m : Measure (Fin k → ENNReal) ↦ m.map collapse) hBs_map
    _ = Measure.map (collapse ∘ random_measure_disjoint_set_tuple (fun j ↦ (Bs j).1))
          (Q : Measure (BoundedlyFiniteMeasure E)) := by
          rw [Measure.map_map hcollapse_meas hmeasBs]
    _ = Measure.map (random_measure_disjoint_set_tuple (fun i ↦ (As i).1))
          (Q : Measure (BoundedlyFiniteMeasure E)) := by
          congr 1
          funext μ
          exact (hfactor μ).symm

/-- Helper for Theorem 24.5: equality of all pairwise-disjoint bounded-set tuple laws forces
equality of the full product-space law of the bounded-set evaluation family. -/
private theorem map_boundedSetEvaluationFamily_eq_of_disjointFiniteDimensionalDistributions
    {P Q : ProbabilityMeasure (BoundedlyFiniteMeasure E)}
    (h :
      ∀ n : ℕ, ∀ As : Fin n → Set E,
        (∀ i, MeasurableSet (As i)) →
        (∀ i, Bornology.IsBounded (As i)) →
        Pairwise (fun i j ↦ Disjoint (As i) (As j)) →
        Measure.map (random_measure_disjoint_set_tuple As) (P : Measure (BoundedlyFiniteMeasure E)) =
          Measure.map (random_measure_disjoint_set_tuple As) (Q : Measure (BoundedlyFiniteMeasure E))) :
    Measure.map (randomMeasureBoundedSetEvaluationFamily (E := E))
        (P : Measure (BoundedlyFiniteMeasure E)) =
      Measure.map (randomMeasureBoundedSetEvaluationFamily (E := E))
        (Q : Measure (BoundedlyFiniteMeasure E)) := by
  classical
  have hrestrict :
      ∀ I : Finset (BoundedMeasurableSet (E := E)),
        Measure.map (fun μ : BoundedlyFiniteMeasure E ↦
            I.restrict (randomMeasureBoundedSetEvaluationFamily (E := E) μ))
            (P : Measure (BoundedlyFiniteMeasure E)) =
          Measure.map (fun μ : BoundedlyFiniteMeasure E ↦
            I.restrict (randomMeasureBoundedSetEvaluationFamily (E := E) μ))
            (Q : Measure (BoundedlyFiniteMeasure E)) := by
    intro I
    let e : Fin I.card ≃ I :=
      (Fintype.equivFinOfCardEq (show Fintype.card I = I.card by simp)).symm
    let es : (Fin I.card → ENNReal) ≃ᵐ (I → ENNReal) :=
      MeasurableEquiv.piCongrLeft (fun _ : I ↦ ENNReal) e
    let AsI : Fin I.card → BoundedMeasurableSet (E := E) := fun i ↦ (e i : I)
    have htuple :
        Measure.map (random_measure_disjoint_set_tuple (fun i ↦ (AsI i).1))
            (P : Measure (BoundedlyFiniteMeasure E)) =
          Measure.map (random_measure_disjoint_set_tuple (fun i ↦ (AsI i).1))
            (Q : Measure (BoundedlyFiniteMeasure E)) :=
      map_boundedSetTuple_eq_of_disjointFiniteDimensionalDistributions (E := E) h AsI
    have hcomp :
        es ∘ random_measure_disjoint_set_tuple (fun i ↦ (AsI i).1) =
          fun μ : BoundedlyFiniteMeasure E ↦
            I.restrict (randomMeasureBoundedSetEvaluationFamily (E := E) μ) :=
      restrict_boundedSetEvaluationFamily_eq_piCongrLeft_comp (E := E) I
    have hmeasTuple :
        Measurable (random_measure_disjoint_set_tuple (fun i ↦ (AsI i).1)) :=
      measurable_random_measure_disjoint_set_tuple (fun i ↦ (AsI i).1)
        (fun i ↦ (AsI i).2.1) (fun i ↦ (AsI i).2.2)
    -- Proof comment: as in the integral branch, finite restrictions are just reindexed tuple laws.
    calc
      Measure.map (fun μ : BoundedlyFiniteMeasure E ↦
          I.restrict (randomMeasureBoundedSetEvaluationFamily (E := E) μ))
          (P : Measure (BoundedlyFiniteMeasure E))
          = (Measure.map (random_measure_disjoint_set_tuple (fun i ↦ (AsI i).1))
              (P : Measure (BoundedlyFiniteMeasure E))).map es := by
              rw [← hcomp, Measure.map_map es.measurable hmeasTuple]
      _ = (Measure.map (random_measure_disjoint_set_tuple (fun i ↦ (AsI i).1))
            (Q : Measure (BoundedlyFiniteMeasure E))).map es := by
            exact congrArg (fun m : Measure (Fin I.card → ENNReal) ↦ m.map es) htuple
      _ = Measure.map (fun μ : BoundedlyFiniteMeasure E ↦
            I.restrict (randomMeasureBoundedSetEvaluationFamily (E := E) μ))
            (Q : Measure (BoundedlyFiniteMeasure E)) := by
            rw [← hcomp, Measure.map_map es.measurable hmeasTuple]
  have hprojP :
      IsProjectiveLimit
        (Measure.map (randomMeasureBoundedSetEvaluationFamily (E := E))
          (P : Measure (BoundedlyFiniteMeasure E)))
        (fun I : Finset (BoundedMeasurableSet (E := E)) ↦
          Measure.map (fun μ : BoundedlyFiniteMeasure E ↦
            I.restrict (randomMeasureBoundedSetEvaluationFamily (E := E) μ))
            (P : Measure (BoundedlyFiniteMeasure E))) := by
    -- Proof comment: the full bounded-set evaluation law is the projective limit of its finite
    -- restrictions.
    simpa [randomMeasureBoundedSetEvaluationFamily] using
      (ProbabilityTheory.isProjectiveLimit_map
        (P := (P : Measure (BoundedlyFiniteMeasure E)))
        (X := fun A (μ : BoundedlyFiniteMeasure E) ↦
          randomMeasureBoundedSetEvaluationFamily (E := E) μ A)
        measurable_randomMeasureBoundedSetEvaluationFamily.aemeasurable)
  have hprojQ :
      IsProjectiveLimit
        (Measure.map (randomMeasureBoundedSetEvaluationFamily (E := E))
          (Q : Measure (BoundedlyFiniteMeasure E)))
        (fun I : Finset (BoundedMeasurableSet (E := E)) ↦
          Measure.map (fun μ : BoundedlyFiniteMeasure E ↦
            I.restrict (randomMeasureBoundedSetEvaluationFamily (E := E) μ))
            (Q : Measure (BoundedlyFiniteMeasure E))) := by
    -- Proof comment: the same projective-limit description holds for `Q`.
    simpa [randomMeasureBoundedSetEvaluationFamily] using
      (ProbabilityTheory.isProjectiveLimit_map
        (P := (Q : Measure (BoundedlyFiniteMeasure E)))
        (X := fun A (μ : BoundedlyFiniteMeasure E) ↦
          randomMeasureBoundedSetEvaluationFamily (E := E) μ A)
        measurable_randomMeasureBoundedSetEvaluationFamily.aemeasurable)
  -- Proof comment: equality of every finite bounded-set restriction determines the full law.
  refine hprojP.unique ?_
  simpa [hrestrict] using hprojQ

-- Proof sketch: the random-measure sigma-algebra on `BoundedlyFiniteMeasure E` is generated by
-- bounded-set evaluations, and Theorem 24.2 identifies it with one generated by the nonnegative
-- vague integral coordinates; equality of all finite-dimensional distributions from either
-- generating family therefore forces equality of the laws.
/-- Theorem 24.5: if two laws on random measures have the same finite-dimensional distributions for
all nonnegative compactly supported test-integral tuples (24.1), or for all tuples of pairwise
disjoint bounded Borel-set evaluations (24.2), then the two laws are equal. -/
theorem random_measure_law_eq_of_integral_or_disjoint_set_finite_dimensional_distributions
    {P Q : ProbabilityMeasure (BoundedlyFiniteMeasure E)}
    (h :
      (∀ n : ℕ, ∀ fs : Fin n → CompactlySupportedContinuousMap E NNReal,
          Measure.map (random_measure_test_integral_tuple fs) (P : Measure (BoundedlyFiniteMeasure E)) =
            Measure.map (random_measure_test_integral_tuple fs) (Q : Measure (BoundedlyFiniteMeasure E))) ∨
      (∀ n : ℕ, ∀ As : Fin n → Set E,
          (∀ i, MeasurableSet (As i)) →
          (∀ i, Bornology.IsBounded (As i)) →
          Pairwise (fun i j ↦ Disjoint (As i) (As j)) →
          Measure.map (random_measure_disjoint_set_tuple As) (P : Measure (BoundedlyFiniteMeasure E)) =
            Measure.map (random_measure_disjoint_set_tuple As) (Q : Measure (BoundedlyFiniteMeasure E)))) :
    P = Q := by
  rcases randomMeasureMeasurableSpace_eq_borel_vagueTopology (E := E) with
    ⟨hrandom_borel, hborel_compact, hcompact_nonnegative⟩
  rcases h with hIntegral | hDisjoint
  · have hmap :
      Measure.map (randomMeasureNonnegativeIntegralFamily (E := E))
          (P : Measure (BoundedlyFiniteMeasure E)) =
        Measure.map (randomMeasureNonnegativeIntegralFamily (E := E))
          (Q : Measure (BoundedlyFiniteMeasure E)) :=
      map_nonnegativeIntegralFamily_eq_of_finiteDimensionalDistributions (E := E) hIntegral
    -- Proof comment: Theorem 24.2 identifies the ambient measurable space with the pullback
    -- sigma-algebra generated by the full nonnegative-integral family.
    refine
      probabilityMeasure_eq_of_map_eq_of_comap_pi
        (ι := CompactlySupportedContinuousMap E NNReal)
        (α := fun _ ↦ ℝ)
        (X := randomMeasureNonnegativeIntegralFamily (E := E))
        ?_ hmap
    calc
        (inferInstance : MeasurableSpace (BoundedlyFiniteMeasure E))
            = randomMeasureMeasurableSpace E := rfl
        _ = borel (BoundedlyFiniteMeasure E) := hrandom_borel
        _ = compactlySupportedContinuousIntegralMeasurableSpace E := hborel_compact
        _ = nonnegativeCompactlySupportedContinuousIntegralMeasurableSpace E := hcompact_nonnegative
        _ = MeasurableSpace.comap
              (randomMeasureNonnegativeIntegralFamily (E := E))
              (inferInstance :
                MeasurableSpace (CompactlySupportedContinuousMap E NNReal → ℝ)) :=
              nonnegativeIntegralMeasurableSpace_eq_comap_family (E := E)
  · have hmap :
      Measure.map (randomMeasureBoundedSetEvaluationFamily (E := E))
          (P : Measure (BoundedlyFiniteMeasure E)) =
        Measure.map (randomMeasureBoundedSetEvaluationFamily (E := E))
          (Q : Measure (BoundedlyFiniteMeasure E)) :=
      map_boundedSetEvaluationFamily_eq_of_disjointFiniteDimensionalDistributions
        (E := E) hDisjoint
    -- Proof comment: the random-measure sigma-algebra is the pullback of the product sigma
    -- algebra along the full bounded-set evaluation family.
    refine
      probabilityMeasure_eq_of_map_eq_of_comap_pi
        (ι := BoundedMeasurableSet (E := E))
        (α := fun _ ↦ ENNReal)
        (X := randomMeasureBoundedSetEvaluationFamily (E := E))
        ?_ hmap
    calc
        (inferInstance : MeasurableSpace (BoundedlyFiniteMeasure E))
            = randomMeasureMeasurableSpace E := rfl
        _ = MeasurableSpace.comap
              (randomMeasureBoundedSetEvaluationFamily (E := E))
              (inferInstance :
                MeasurableSpace (BoundedMeasurableSet (E := E) → ENNReal)) :=
              randomMeasureMeasurableSpace_eq_comap_boundedSetEvaluationFamily (E := E)

end ChapterAmbient
