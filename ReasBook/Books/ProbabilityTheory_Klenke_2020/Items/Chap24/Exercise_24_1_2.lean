/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Books.ProbabilityTheory_Klenke_2020.Items.Chap24.Definition_24_1
import Mathlib.MeasureTheory.Measure.Prokhorov
import Mathlib.Topology.Separation.Hausdorff

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory
open Set Filter Metric
open scoped ENNReal NNReal Topology

universe u

variable {E : Type u} [PseudoMetricSpace E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace.SeparableSpace E]

/-- Helper for Exercise 24.1.2: evaluations on arbitrary measurable sets are measurable for the
restriction of `randomMeasureMeasurableSpace E` to `ProbabilityMeasure E`. -/
lemma randomMeasureComapEvalMeasurableOfMeasurableSet {A : Set E} (hA : MeasurableSet A) :
    @Measurable (ProbabilityMeasure E) ℝ≥0∞
      (MeasurableSpace.comap ProbabilityMeasure.toBoundedlyFiniteMeasure
        (randomMeasureMeasurableSpace E))
      (borel ℝ≥0∞)
      (fun μ ↦ (μ : Measure E) A) := by
  classical
  by_cases hE : Nonempty E
  · let x0 : E := Classical.choice hE
    have hbounded :
        ∀ n : ℕ,
          @Measurable (ProbabilityMeasure E) ℝ≥0∞
            (MeasurableSpace.comap ProbabilityMeasure.toBoundedlyFiniteMeasure
              (randomMeasureMeasurableSpace E))
            (borel ℝ≥0∞)
            (fun μ ↦ (μ : Measure E) (A ∩ Metric.closedBall x0 n)) := by
      intro n
      -- Proof comment: each truncated evaluation is one of the defining bounded generators.
      simpa [ProbabilityMeasure.toMeasure_toBoundedlyFiniteMeasure] using
        ((measurable_apply_of_isBounded (E := E) (A := A ∩ Metric.closedBall x0 n)
          (hA.inter measurableSet_closedBall)
          (Metric.isBounded_closedBall.subset (by intro x hx; exact hx.2))).comp
          (comap_measurable ProbabilityMeasure.toBoundedlyFiniteMeasure))
    have hmono : Monotone fun n : ℕ ↦ A ∩ Metric.closedBall x0 n := by
      intro m n hmn
      exact
        inter_subset_inter_right A
          (Metric.closedBall_subset_closedBall (Nat.cast_le.2 hmn))
    have hUnion : (⋃ n : ℕ, A ∩ Metric.closedBall x0 n) = A := by
      -- Proof comment: closed balls exhaust the ambient separable pseudometric space.
      simpa using Metric.iUnion_inter_closedBall_nat A x0
    have hMeasSup :
        @Measurable (ProbabilityMeasure E) ℝ≥0∞
          (MeasurableSpace.comap ProbabilityMeasure.toBoundedlyFiniteMeasure
            (randomMeasureMeasurableSpace E))
          (borel ℝ≥0∞)
          (fun μ : ProbabilityMeasure E ↦
            ⨆ n : ℕ, (μ : Measure E) (A ∩ Metric.closedBall x0 n)) :=
      Measurable.iSup hbounded
    have hpoint :
        ∀ μ : ProbabilityMeasure E,
          (μ : Measure E) A = ⨆ n : ℕ, (μ : Measure E) (A ∩ Metric.closedBall x0 n) := by
      intro μ
      -- Proof comment: continuity from below identifies the full evaluation with the supremum of
      -- its bounded truncations.
      have hmuUnion :
          (μ : Measure E) (⋃ n : ℕ, A ∩ Metric.closedBall x0 n) =
            ⨆ n : ℕ, (μ : Measure E) (A ∩ Metric.closedBall x0 n) :=
        hmono.measure_iUnion
      simpa [hUnion] using hmuUnion
    simpa [funext hpoint] using hMeasSup
  · have : IsEmpty (ProbabilityMeasure E) := by
      refine ⟨fun μ ↦ ?_⟩
      exact hE μ.nonempty
    -- Proof comment: if `E` is empty, there are no probability measures, so measurability is
    -- trivial.
    exact
      @Subsingleton.measurable (ProbabilityMeasure E) ℝ≥0∞
        (fun μ ↦ (μ : Measure E) A)
        (MeasurableSpace.comap ProbabilityMeasure.toBoundedlyFiniteMeasure
          (randomMeasureMeasurableSpace E))
        (borel ℝ≥0∞)
        inferInstance

/-- Helper for Exercise 24.1.2: restricting `randomMeasureMeasurableSpace E` to
`ProbabilityMeasure E` recovers the canonical Giry measurable space on probability measures. -/
lemma probabilityMeasureComapRandomMeasure_eq_measureComap :
    MeasurableSpace.comap ProbabilityMeasure.toBoundedlyFiniteMeasure
      (randomMeasureMeasurableSpace E) =
        MeasurableSpace.comap (fun μ : ProbabilityMeasure E ↦ (μ : Measure E))
          (inferInstance : MeasurableSpace (Measure E)) := by
  refine le_antisymm ?_ ?_
  · -- Proof comment: bounded measurable evaluations are already measurable for the inherited
    -- Giry sigma-algebra, so every generator of `𝕄` survives the restriction.
    rw [randomMeasureMeasurableSpace_def]
    simp_rw [MeasurableSpace.comap_iSup]
    refine iSup_le fun A ↦ iSup_le fun hA ↦ iSup_le fun _ ↦ ?_
    simpa [MeasurableSpace.comap_comp, ProbabilityMeasure.toMeasure_toBoundedlyFiniteMeasure]
      using
        (((Measure.measurable_coe hA).comp
          (comap_measurable (fun μ : ProbabilityMeasure E ↦ (μ : Measure E)))).comap_le)
  · -- Proof comment: arbitrary measurable-set evaluations are measurable by bounded-ball
    -- exhaustion, so the full Giry sigma-algebra is contained in the restriction of `𝕄`.
    exact
      (Measure.measurable_of_measurable_coe
        (fun μ : ProbabilityMeasure E ↦ (μ : Measure E))
        (fun A hA ↦ randomMeasureComapEvalMeasurableOfMeasurableSet (E := E) hA)).comap_le

/-- Helper for Exercise 24.1.2: evaluation on a closed set is weak-Borel measurable on
`ProbabilityMeasure E`. -/
lemma closedSetEvaluation_borelMeasurable {F : Set E} (hF : IsClosed F) :
    @Measurable (ProbabilityMeasure E) ℝ≥0∞
      (borel (ProbabilityMeasure E)) (borel ℝ≥0∞)
      (fun μ ↦ (μ : Measure E) F) := by
  -- Proof comment: the Portmanteau closed-set inequality identifies the evaluation map as upper
  -- semicontinuous for the weak topology, hence Borel measurable.
  have husc : UpperSemicontinuous fun μ : ProbabilityMeasure E ↦ (μ : Measure E) F := by
    rw [upperSemicontinuous_iff]
    intro μ
    rw [upperSemicontinuousAt_iff_limsup_le]
    simpa using
      (ProbabilityMeasure.limsup_measure_closed_le_of_tendsto
        (μs := fun ν : ProbabilityMeasure E ↦ ν)
        (μ := μ)
        tendsto_id
        (F := F)
        hF)
  letI : MeasurableSpace (ProbabilityMeasure E) := borel (ProbabilityMeasure E)
  letI : OpensMeasurableSpace (ProbabilityMeasure E) := ⟨le_rfl⟩
  simpa using husc.measurable

/-- Helper for Exercise 24.1.2: every measurable-set evaluation is weak-Borel measurable on
`ProbabilityMeasure E`. -/
lemma measureEvaluation_borelMeasurable {A : Set E} (hA : MeasurableSet A) :
    @Measurable (ProbabilityMeasure E) ℝ≥0∞
      (borel (ProbabilityMeasure E)) (borel ℝ≥0∞)
      (fun μ ↦ (μ : Measure E) A) := by
  -- Proof comment: closed sets generate the Borel sigma-algebra on `E`, so the measurable
  -- measure-valued map follows from the closed-set evaluation lemma.
  have hcoe :
      @Measurable (ProbabilityMeasure E) (Measure E)
        (borel (ProbabilityMeasure E))
        (inferInstance : MeasurableSpace (Measure E))
        (fun μ : ProbabilityMeasure E ↦ (μ : Measure E)) := by
    refine Measurable.measure_of_isPiSystem_of_isProbabilityMeasure ?_ isPiSystem_isClosed ?_
    · simpa [borel_eq_generateFrom_isClosed] using
        (show (inferInstance : MeasurableSpace E) =
          MeasurableSpace.generateFrom {s : Set E | IsClosed s} by
            rw [show (inferInstance : MeasurableSpace E) = borel E by
              simpa using (BorelSpace.measurable_eq (α := E))]
            exact borel_eq_generateFrom_isClosed)
    · intro s hs
      exact closedSetEvaluation_borelMeasurable (E := E) hs
  exact (Measure.measurable_coe hA).comp hcoe

/-- Helper for Exercise 24.1.2: weak-dual coordinates are measurable for the inherited Giry
sigma-algebra on `ProbabilityMeasure E`. -/
lemma probabilityMeasureWeakDualCoordinateMeasurable
    (f : BoundedContinuousFunction E ℝ≥0) :
    @Measurable (ProbabilityMeasure E) ℝ≥0
      (MeasurableSpace.comap (fun μ : ProbabilityMeasure E ↦ (μ : Measure E))
        (inferInstance : MeasurableSpace (Measure E)))
      inferInstance
      (fun μ ↦ μ.toWeakDualBCNN f) := by
  -- Proof comment: each weak-dual coordinate is the `toNNReal` of a measurable `lintegral`.
  simp_rw [ProbabilityMeasure.toWeakDualBCNN_apply]
  exact
    ENNReal.measurable_toNNReal.comp
      ((Measure.measurable_lintegral
        (measurable_coe_nnreal_ennreal.comp f.continuous.measurable)).comp
        (comap_measurable (fun μ : ProbabilityMeasure E ↦ (μ : Measure E))))

/-- Helper for Exercise 24.1.2: the weak topology on `ProbabilityMeasure E` is induced by the full
weak-dual coordinate map. -/
lemma probabilityMeasureTopology_eq_inducedWeakDualCoordinates :
    (inferInstance : TopologicalSpace (ProbabilityMeasure E)) =
      TopologicalSpace.induced
        (fun μ : ProbabilityMeasure E ↦
          fun f : BoundedContinuousFunction E ℝ≥0 ↦ μ.toWeakDualBCNN f)
        Pi.topologicalSpace := by
  -- Proof comment: rewrite the weak topology through `toFiniteMeasure` and `toWeakDualBCNN`,
  -- then identify the target weak-dual topology with the induced product topology of coordinate
  -- evaluation.
  let g : ProbabilityMeasure E → BoundedContinuousFunction E ℝ≥0 → ℝ≥0 :=
    fun μ f ↦ μ.toWeakDualBCNN f
  calc
    (inferInstance : TopologicalSpace (ProbabilityMeasure E))
      = TopologicalSpace.induced ProbabilityMeasure.toFiniteMeasure inferInstance := by
          rfl
    _ = TopologicalSpace.induced ProbabilityMeasure.toFiniteMeasure
          (TopologicalSpace.induced FiniteMeasure.toWeakDualBCNN inferInstance) := by
          rfl
    _ = TopologicalSpace.induced
          (fun μ : ProbabilityMeasure E ↦ FiniteMeasure.toWeakDualBCNN (μ.toFiniteMeasure))
          inferInstance := by
          rw [induced_compose]
          refine congrArg
            (fun h : ProbabilityMeasure E →
                WeakDual ℝ≥0 (BoundedContinuousFunction E ℝ≥0) =>
              TopologicalSpace.induced h inferInstance) ?_
          funext μ
          rfl
    _ = TopologicalSpace.induced (fun μ : ProbabilityMeasure E ↦ μ.toWeakDualBCNN)
          inferInstance := by
          rfl
    _ = TopologicalSpace.induced (fun μ : ProbabilityMeasure E ↦ μ.toWeakDualBCNN)
          (TopologicalSpace.induced
            (fun φ : WeakDual ℝ≥0 (BoundedContinuousFunction E ℝ≥0) ↦
              fun f ↦ φ f)
            Pi.topologicalSpace) := by
          rfl
    _ = TopologicalSpace.induced g Pi.topologicalSpace := by
          rw [induced_compose]
          rfl

/-- Helper for Exercise 24.1.2: the weak topology on `ProbabilityMeasure E` is generated by finite
intersections of scalar weak-dual coordinate preimages. -/
lemma probabilityMeasureTopology_eq_generateFromWeakDualCoordinates :
    (inferInstance : TopologicalSpace (ProbabilityMeasure E)) =
      TopologicalSpace.generateFrom
        ((fun t : Set (BoundedContinuousFunction E ℝ≥0 → ℝ≥0) ↦
            (fun μ : ProbabilityMeasure E ↦ fun f ↦ μ.toWeakDualBCNN f) ⁻¹' t) ''
          { t | ∃ u : BoundedContinuousFunction E ℝ≥0 → Set ℝ≥0,
              ∃ i : Finset (BoundedContinuousFunction E ℝ≥0),
                (∀ f ∈ i, IsOpen (u f)) ∧ t = Set.pi (↑i) u }) := by
  -- Proof comment: combine the induced weak-coordinate description with the standard
  -- `generateFrom` presentation of the product topology on the coordinate space.
  rw [probabilityMeasureTopology_eq_inducedWeakDualCoordinates (E := E)]
  rw [pi_eq_generateFrom, induced_generateFrom_eq]

/-- Helper for Exercise 24.1.2: pushing a probability measure forward by a measurable map that is
close to the identity outside a small exceptional set changes it by at most that error in
Lévy-Prokhorov distance. -/
lemma levyProkhorovDist_map_le_of_close
    (P : ProbabilityMeasure E) {q : E → E} (hq : Measurable q) {s : Set E}
    {δ : ℝ} (hδ : 0 ≤ δ)
    (hclose : ∀ x ∉ s, dist (q x) x ≤ δ)
    (hsmall : (P : Measure E) s ≤ ENNReal.ofReal δ) :
    dist
        (LevyProkhorov.ofMeasure
          (ProbabilityMeasure.map P hq.aemeasurable))
        (LevyProkhorov.ofMeasure P) ≤ δ := by
  letI : OpensMeasurableSpace E := BorelSpace.opensMeasurable
  have hdist :
      levyProkhorovDist
          (((ProbabilityMeasure.map P hq.aemeasurable : ProbabilityMeasure E) : Measure E))
          (P : Measure E) ≤ δ := by
    refine levyProkhorovDist_le_of_forall_le
      (μ := ((ProbabilityMeasure.map P hq.aemeasurable : ProbabilityMeasure E) : Measure E))
      (ν := (P : Measure E)) hδ ?_
    intro ε B hεδ hB
    have hsle : (P : Measure E) s ≤ ENNReal.ofReal ε := by
      exact hsmall.trans (ENNReal.ofReal_le_ofReal hεδ.le)
    have hsubset : q ⁻¹' B ⊆ Metric.thickening ε B ∪ s := by
      intro x hxB
      by_cases hx : x ∈ s
      · exact Or.inr hx
      · left
        -- Proof comment: outside the bad set, the pushforward stays within the target
        -- thickening because `q` is `δ`-close to the identity and `δ < ε`.
        refine Metric.mem_thickening_iff.mpr ?_
        refine ⟨q x, hxB, ?_⟩
        exact lt_of_le_of_lt (by simpa [dist_comm] using hclose x hx) hεδ
    -- Proof comment: compare the pushed-forward mass of `B` with the original mass of the
    -- `ε`-thickening plus the exceptional-set mass.
    calc
      (((ProbabilityMeasure.map P hq.aemeasurable : ProbabilityMeasure E) : Measure E)) B
          = (P : Measure E) (q ⁻¹' B) := by
              rw [ProbabilityMeasure.map_apply' _ hq.aemeasurable hB]
      _ ≤ (P : Measure E) (Metric.thickening ε B ∪ s) := measure_mono hsubset
      _ ≤ (P : Measure E) (Metric.thickening ε B) + (P : Measure E) s := measure_union_le _ _
      _ ≤ (P : Measure E) (Metric.thickening ε B) + ENNReal.ofReal ε := by
            exact add_le_add le_rfl hsle
  -- Proof comment: rewrite the owner metric as the measure-level Lévy-Prokhorov distance.
  simpa [LevyProkhorov.dist_probabilityMeasure_def] using hdist

/-- Helper for Exercise 24.1.2: once `ProbabilityMeasure E` is known to be separable, the
Lévy-Prokhorov metrization upgrades that separability to second countability automatically. -/
lemma probabilityMeasureSecondCountable_of_separable
    [TopologicalSpace.SeparableSpace (ProbabilityMeasure E)] :
    SecondCountableTopology (ProbabilityMeasure E) := by
  -- Proof comment: weak convergence is already metrizable on separable Borel spaces, so the
  -- remaining input for second countability is exactly separability of the measure space itself.
  letI : TopologicalSpace.PseudoMetrizableSpace (ProbabilityMeasure E) := inferInstance
  letI : UniformSpace (ProbabilityMeasure E) :=
    TopologicalSpace.pseudoMetrizableSpaceUniformity (ProbabilityMeasure E)
  letI :
      (uniformity (ProbabilityMeasure E)).IsCountablyGenerated :=
    TopologicalSpace.pseudoMetrizableSpaceUniformity_countably_generated
      (ProbabilityMeasure E)
  exact UniformSpace.secondCountable_of_separable (ProbabilityMeasure E)

/-- Helper for Exercise 24.1.2: a finitely ranged quantizer induces a canonical family of
probability measures on `E` by pushing forward probability measures on its finite range. -/
noncomputable def finiteRangeProbabilityMeasureImage (F : MeasureTheory.SimpleFunc E E) :
    ProbabilityMeasure (Set.range F) → LevyProkhorov (ProbabilityMeasure E) :=
  fun ν ↦
    LevyProkhorov.ofMeasure
      (ProbabilityMeasure.map ν continuous_subtype_val.measurable.aemeasurable)

/-- Helper for Exercise 24.1.2: the probability measures supported on the finite range of a
simple-function quantizer admit countable `ε`-nets after passing to the Lévy-Prokhorov model. -/
lemma existsCountableDenseFiniteRangeImage (F : MeasureTheory.SimpleFunc E E)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ s : Set (LevyProkhorov (ProbabilityMeasure E)),
      s.Countable ∧
        ∀ P : ProbabilityMeasure E,
          ∃ y ∈ s,
            dist
              (LevyProkhorov.ofMeasure
                (ProbabilityMeasure.map P F.measurable.aemeasurable))
              y ≤ ε := by
  classical
  -- Route correction: the compactness input must come from a discrete finite copy of `range F`,
  -- not from the inherited pseudometric subtype topology.
  letI : Finite (Set.range F) := F.finite_range
  letI : TopologicalSpace (Set.range F) := ⊥
  letI : DiscreteTopology (Set.range F) := ⟨rfl⟩
  letI : MeasurableSpace (Set.range F) := borel (Set.range F)
  letI : BorelSpace (Set.range F) := ⟨rfl⟩
  letI : OpensMeasurableSpace (Set.range F) := BorelSpace.opensMeasurable
  letI : CompactSpace (Set.range F) := inferInstance
  let toAmbient : Set.range F → E := fun y ↦ y.1
  have htoAmbientMeasurable : Measurable toAmbient := by
    exact measurable_of_finite toAmbient
  let finiteRangeImage :
      ProbabilityMeasure (Set.range F) → LevyProkhorov (ProbabilityMeasure E) :=
    fun ν ↦
      LevyProkhorov.ofMeasure
        (ProbabilityMeasure.map ν htoAmbientMeasurable.aemeasurable)
  have hcont :
      Continuous finiteRangeImage := by
    -- Proof comment: push-forward along the subtype inclusion is continuous on probability
    -- measures, and the Lévy-Prokhorov synonym preserves that topology.
    simpa [finiteRangeImage] using
      (LevyProkhorov.continuous_ofMeasure_probabilityMeasure (Ω := E)).comp
        (ProbabilityMeasure.continuous_map
          (Ω := Set.range F) (Ω' := E) (continuous_of_discreteTopology : Continuous toAmbient))
  have hcompact :
      IsCompact (Set.range finiteRangeImage) := by
    -- Proof comment: the source `ProbabilityMeasure (Set.range F)` is compact because `F.range`
    -- is finite, so its continuous image is compact as well.
    simpa [Set.image_univ] using isCompact_univ.image hcont
  obtain ⟨s, _, hsFinite, hsCover⟩ := hcompact.finite_cover_balls hε
  refine ⟨s, hsFinite.countable, ?_⟩
  intro P
  let liftToRange : E → Set.range F := fun x ↦ ⟨F x, ⟨x, rfl⟩⟩
  have hliftToRange : Measurable liftToRange := by
    -- Proof comment: on the finite discrete range, every measurable set is a finite union of
    -- singleton fibers of `F`.
    intro s hs
    let t : Finset (Set.range F) := (s.toFinite).toFinset
    have hpre :
        liftToRange ⁻¹' s = ⋃ y ∈ t, F ⁻¹' {y.1} := by
      ext x
      constructor
      · intro hx
        have hy : liftToRange x ∈ t := by
          simpa [t, liftToRange] using (s.toFinite.mem_toFinset.mpr hx)
        refine mem_iUnion.2 ?_
        refine ⟨liftToRange x, mem_iUnion.2 ?_⟩
        exact ⟨hy, by simp [liftToRange]⟩
      · intro hx
        rcases mem_iUnion.1 hx with ⟨y, hx⟩
        rcases mem_iUnion.1 hx with ⟨hy, hxy⟩
        have hy' : y ∈ s := by
          -- Proof comment: convert finset membership back to set membership through
          -- `Set.Finite.mem_toFinset` to avoid ambiguous coercions.
          simpa [t] using (s.toFinite.mem_toFinset.mp hy)
        have hLift : liftToRange x = y := by
          apply Subtype.ext
          simpa [liftToRange] using hxy
        simpa [hLift] using hy'
    rw [hpre]
    exact Finset.measurableSet_biUnion _ fun y _ ↦ F.measurableSet_fiber y.1
  have hpushforward :
      finiteRangeImage
          (ProbabilityMeasure.map P hliftToRange.aemeasurable) =
        LevyProkhorov.ofMeasure
          (ProbabilityMeasure.map P F.measurable.aemeasurable) := by
    -- Proof comment: mapping first into the finite range and then back by subtype inclusion is
    -- exactly the original simple-function pushforward.
    have hmap :
        ProbabilityMeasure.map
            (ProbabilityMeasure.map P hliftToRange.aemeasurable)
            htoAmbientMeasurable.aemeasurable =
          ProbabilityMeasure.map P F.measurable.aemeasurable := by
      apply ProbabilityMeasure.toMeasure_injective
      simpa [liftToRange, toAmbient, Function.comp] using
        (Measure.map_map (μ := (P : Measure E))
          htoAmbientMeasurable hliftToRange)
    simpa [finiteRangeImage] using congrArg LevyProkhorov.ofMeasure hmap
  have hmem :
      LevyProkhorov.ofMeasure
          (ProbabilityMeasure.map P F.measurable.aemeasurable) ∈
        Set.range finiteRangeImage := by
    refine ⟨ProbabilityMeasure.map P hliftToRange.aemeasurable, ?_⟩
    exact hpushforward
  rcases mem_iUnion.1 (hsCover hmem) with ⟨y, hy⟩
  rcases mem_iUnion.1 hy with ⟨hyS, hyBall⟩
  refine ⟨y, hyS, ?_⟩
  -- Proof comment: the finite ball cover of the compact image is the required `ε`-net.
  exact le_of_lt (by simpa [Metric.mem_ball] using hyBall)

/-- Helper for Exercise 24.1.2: a finite prefix of a dense sequence yields a simple-function
quantizer whose pushforward is close to the original probability measure in Lévy-Prokhorov
distance. -/
lemma existsNearestPtApproximation [Nonempty E] {ε : ℝ} (hε : 0 < ε)
    (P : ProbabilityMeasure E) :
    ∃ N : ℕ,
      dist
          (LevyProkhorov.ofMeasure
            (ProbabilityMeasure.map P
              ((SimpleFunc.nearestPt (TopologicalSpace.denseSeq E) N).measurable.aemeasurable)))
          (LevyProkhorov.ofMeasure P) < ε := by
  let δ : ℝ := ε / 2
  have hδ : 0 < δ := by
    positivity
  let c : ℕ → E := TopologicalSpace.denseSeq E
  let bad : ℕ → Set E := fun n ↦ (Metric.ball (c n) δ)ᶜ
  have hbadMeas : ∀ n, MeasurableSet (bad n) := by
    intro n
    exact (isOpen_ball.measurableSet).compl
  have hbadEmpty : ⋂ n, bad n = (∅ : Set E) := by
    ext x
    constructor
    · intro hx
      rcases Metric.denseRange_iff.1 (TopologicalSpace.denseRange_denseSeq E) x δ hδ with ⟨n, hn⟩
      have hxall : x ∈ bad n := by
        simpa [bad] using mem_iInter.1 hx n
      exact hxall hn
    · intro hx
      simp at hx
  obtain ⟨N, hN⟩ :=
    exists_measure_iInter_lt
      (μ := (P : Measure E))
      (f := bad)
      (hm := fun n ↦ (hbadMeas n).nullMeasurableSet)
      (hε := ENNReal.ofReal_pos.mpr hδ)
      (hfin := ⟨0, measure_ne_top (P : Measure E) _⟩)
      hbadEmpty
  let q : MeasureTheory.SimpleFunc E E := SimpleFunc.nearestPt c N
  have hclose : ∀ x ∉ ⋂ n ≤ N, bad n, dist (q x) x ≤ δ := by
    intro x hx
    simp only [bad, mem_iInter, mem_compl_iff, mem_ball, not_forall, not_lt] at hx
    rcases hx with ⟨n, hnN, hnx⟩
    have hnx' : dist x (c n) < δ := by
      linarith
    have hedist :
        edist (q x) x ≤ edist (c n) x :=
      SimpleFunc.edist_nearestPt_le c x hnN
    have hball :
        edist (c n) x < ENNReal.ofReal δ := by
      rw [edist_dist]
      exact (ENNReal.ofReal_lt_ofReal_iff hδ).2 (by simpa [dist_comm] using hnx')
    have hlt :
        edist (q x) x < ENNReal.ofReal δ := by
      exact lt_of_le_of_lt hedist hball
    have hdist' : dist (q x) x < δ := by
      rw [edist_dist] at hlt
      exact (ENNReal.ofReal_lt_ofReal_iff hδ).1 hlt
    exact le_of_lt hdist'
  have hdist :
      dist
          (LevyProkhorov.ofMeasure
            (ProbabilityMeasure.map P q.measurable.aemeasurable))
          (LevyProkhorov.ofMeasure P) ≤ δ :=
    levyProkhorovDist_map_le_of_close
      (E := E) P q.measurable hδ.le hclose hN.le
  refine ⟨N, ?_⟩
  -- Proof comment: the uncovered tail has mass `< ε / 2`, so the quantized measure lies inside
  -- the target `ε`-ball.
  exact lt_of_le_of_lt hdist (by
    dsimp [δ]
    linarith)

/-- Helper for Exercise 24.1.2: the weak topology on `ProbabilityMeasure E` is second countable on
a separable pseudometric space. -/
lemma probabilityMeasureSecondCountable :
    SecondCountableTopology (ProbabilityMeasure E) := by
  -- Route correction: the direct product-Borel argument only yields measurability for the full
  -- coordinate map into the product sigma-algebra, not the Borel sigma-algebra of the uncountable
  -- product topology.
  by_cases hE : Nonempty E
  · letI : Nonempty E := hE
    have hLP :
        SecondCountableTopology (LevyProkhorov (ProbabilityMeasure E)) := by
      refine Metric.secondCountable_of_almost_dense_set fun ε hε ↦ ?_
      let δ : ℝ := ε / 2
      have hδ : 0 < δ := by
        dsimp [δ]
        positivity
      let q : ℕ → MeasureTheory.SimpleFunc E E :=
        fun N ↦ SimpleFunc.nearestPt (TopologicalSpace.denseSeq E) N
      choose s hsCount hsApprox using
        fun N : ℕ ↦ existsCountableDenseFiniteRangeImage (E := E) (F := q N) hδ
      refine ⟨⋃ N, s N, Set.countable_iUnion hsCount, ?_⟩
      intro x
      rcases x with ⟨P⟩
      obtain ⟨N, hN⟩ := existsNearestPtApproximation (E := E) hδ P
      obtain ⟨y, hy, hyDist⟩ := hsApprox N P
      refine ⟨y, mem_iUnion.2 ⟨N, hy⟩, ?_⟩
      -- Proof comment: approximate first by nearest-point quantization, then use the finite-range
      -- `ε / 2`-net and finish with the triangle inequality in the Lévy-Prokhorov metric.
      have hdist : dist (LevyProkhorov.ofMeasure P) y < ε := by
        calc
          dist (LevyProkhorov.ofMeasure P) y
              ≤ dist
                  (LevyProkhorov.ofMeasure P)
                  (LevyProkhorov.ofMeasure
                    (ProbabilityMeasure.map P (q N).measurable.aemeasurable)) +
                dist
                  (LevyProkhorov.ofMeasure
                    (ProbabilityMeasure.map P (q N).measurable.aemeasurable))
                  y := dist_triangle _ _ _
          _ < δ + δ := by
            exact add_lt_add_of_lt_of_le (by simpa [dist_comm] using hN) hyDist
          _ = ε := by
            dsimp [δ]
            ring
      exact hdist.le
    letI : SecondCountableTopology (LevyProkhorov (ProbabilityMeasure E)) := hLP
    exact (LevyProkhorov.probabilityMeasureHomeomorph (Ω := E)).isEmbedding.secondCountableTopology
  · have hEmpty : IsEmpty (ProbabilityMeasure E) := by
      refine ⟨fun P ↦ ?_⟩
      exact hE P.nonempty
    letI : IsEmpty (ProbabilityMeasure E) := hEmpty
    infer_instance

/-- Helper for Exercise 24.1.2: once the weak topology on `ProbabilityMeasure E` is second
countable, its Borel sigma-algebra is generated by the finite weak-dual coordinate cylinders from
`probabilityMeasureTopology_eq_generateFromWeakDualCoordinates`. -/
lemma borel_probabilityMeasure_eq_generateFromWeakDualCoordinates
    [SecondCountableTopology (ProbabilityMeasure E)] :
    borel (ProbabilityMeasure E) =
      MeasurableSpace.generateFrom
        ((fun t : Set (BoundedContinuousFunction E ℝ≥0 → ℝ≥0) ↦
            (fun μ : ProbabilityMeasure E ↦ fun f ↦ μ.toWeakDualBCNN f) ⁻¹' t) ''
          { t | ∃ u : BoundedContinuousFunction E ℝ≥0 → Set ℝ≥0,
              ∃ i : Finset (BoundedContinuousFunction E ℝ≥0),
                (∀ f ∈ i, IsOpen (u f)) ∧ t = Set.pi (↑i) u }) := by
  -- Proof comment: second countability upgrades the established topological subbasis description
  -- directly to the Borel sigma-algebra generated by the same coordinate cylinders.
  simpa using
    (borel_eq_generateFrom_of_subbasis
      (s :=
        ((fun t : Set (BoundedContinuousFunction E ℝ≥0 → ℝ≥0) ↦
            (fun μ : ProbabilityMeasure E ↦ fun f ↦ μ.toWeakDualBCNN f) ⁻¹' t) ''
          { t | ∃ u : BoundedContinuousFunction E ℝ≥0 → Set ℝ≥0,
              ∃ i : Finset (BoundedContinuousFunction E ℝ≥0),
                (∀ f ∈ i, IsOpen (u f)) ∧ t = Set.pi (↑i) u }))
      probabilityMeasureTopology_eq_generateFromWeakDualCoordinates)

/-- Helper for Exercise 24.1.2: after supplying second countability on `ProbabilityMeasure E`,
each weak-topology cylinder generator is measurable for the inherited Giry sigma-algebra. -/
lemma borel_probabilityMeasure_le_measureComap_of_secondCountable
    [SecondCountableTopology (ProbabilityMeasure E)] :
    borel (ProbabilityMeasure E) ≤
      MeasurableSpace.comap (fun μ : ProbabilityMeasure E ↦ (μ : Measure E))
        (inferInstance : MeasurableSpace (Measure E)) := by
  -- Proof comment: rewrite the weak Borel sigma-algebra as a coordinate `generateFrom`, then
  -- prove measurability of each finite cylinder by assembling the already proved coordinate maps.
  rw [borel_probabilityMeasure_eq_generateFromWeakDualCoordinates (E := E)]
  refine MeasurableSpace.generateFrom_le ?_
  rintro _ ⟨t, ⟨u, i, hi, rfl⟩, rfl⟩
  have hcoords :
      @Measurable (ProbabilityMeasure E) (BoundedContinuousFunction E ℝ≥0 → ℝ≥0)
        (MeasurableSpace.comap (fun μ : ProbabilityMeasure E ↦ (μ : Measure E))
          (inferInstance : MeasurableSpace (Measure E)))
        inferInstance
        (fun μ ↦ fun f ↦ μ.toWeakDualBCNN f) := by
    -- Proof comment: measurability into the product space is equivalent to measurability of every
    -- scalar coordinate, already handled by `probabilityMeasureWeakDualCoordinateMeasurable`.
    rw [measurable_pi_iff]
    intro f
    simpa using probabilityMeasureWeakDualCoordinateMeasurable (E := E) f
  exact MeasurableSet.preimage
    (MeasurableSet.pi i.countable_toSet fun f hf ↦ (hi f hf).measurableSet)
    hcoords

/-- Helper for Exercise 24.1.2: the weak Borel sigma-algebra is contained in the inherited Giry
sigma-algebra on `ProbabilityMeasure E`. -/
lemma borel_probabilityMeasure_le_measureComap :
    borel (ProbabilityMeasure E) ≤
      MeasurableSpace.comap (fun μ : ProbabilityMeasure E ↦ (μ : Measure E))
        (inferInstance : MeasurableSpace (Measure E)) := by
  -- Proof comment: the remaining input is exactly the second-countability bridge isolated above.
  letI := probabilityMeasureSecondCountable (E := E)
  exact borel_probabilityMeasure_le_measureComap_of_secondCountable (E := E)

-- Proof sketch: identify `\mathcal M_1(E)` with `ProbabilityMeasure E`, pull back the
-- random-measure sigma-algebra `𝕄` along the canonical inclusion into `BoundedlyFiniteMeasure E`,
-- and compare the resulting generated sigma-algebra with the Borel sigma-algebra of the weak
-- topology on `ProbabilityMeasure E`.
/-- Exercise 24.1.2: the restriction of the random-measure sigma-algebra `𝕄` to the probability
measures `\mathcal M_1(E)` agrees with the Borel sigma-algebra of the weak-convergence topology
on `ProbabilityMeasure E`. -/
theorem randomMeasureMeasurableSpace_comap_probabilityMeasure_eq_borel :
    MeasurableSpace.comap ProbabilityMeasure.toBoundedlyFiniteMeasure
      (randomMeasureMeasurableSpace E) =
        borel (ProbabilityMeasure E) := by
  -- Route correction: rather than unfolding weak convergence directly on evaluation maps, first
  -- identify the left-hand side with the inherited Giry sigma-algebra on `ProbabilityMeasure E`.
  rw [probabilityMeasureComapRandomMeasure_eq_measureComap]
  refine le_antisymm ?_ borel_probabilityMeasure_le_measureComap
  -- Proof comment: once every measurable-set evaluation is weak-Borel measurable, the measure
  -- coercion becomes measurable and therefore the inherited Giry sigma-algebra is weak-Borel.
  have hcoe :
      @Measurable (ProbabilityMeasure E) (Measure E)
        (borel (ProbabilityMeasure E))
        (inferInstance : MeasurableSpace (Measure E))
        (fun μ : ProbabilityMeasure E ↦ (μ : Measure E)) := by
    exact Measure.measurable_of_measurable_coe _ fun A hA ↦
      measureEvaluation_borelMeasurable (E := E) hA
  exact hcoe.comap_le
