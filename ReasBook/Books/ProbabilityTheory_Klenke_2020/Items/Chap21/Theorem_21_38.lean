/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib
import Books.ProbabilityTheory_Klenke_2020.Items.Chap01.Lemma_1_42
import Books.ProbabilityTheory_Klenke_2020.Items.Chap13.Exercise_13_4_1
import Books.ProbabilityTheory_Klenke_2020.Items.Chap21.Theorem_21_31

-- Declarations for this item will be appended below by the statement pipeline.

open Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal

noncomputable section

namespace ProbabilityTheory

local notation "Ω" => C(NNReal, ℝ)

local instance continuousPathSpaceMeasurableSpace : MeasurableSpace Ω :=
  borel Ω

local instance continuousPathSpaceBorelSpace : BorelSpace Ω :=
  ⟨rfl⟩

/-- Helper for Theorem 21.38: the continuous path space is complete for its compact-open metric. -/
local instance continuousPathSpaceCompleteSpace : CompleteSpace Ω :=
  inferInstance

-- Proof sketch: each coordinate map `ω ↦ ω (times i)` is continuous on `C([0, ∞), ℝ)`, and a
-- finite product of measurable coordinate maps is measurable.
/-- The projection sending a continuous path to its values at a finite tuple of times is
measurable. -/
theorem measurable_continuousPathProjection {n : ℕ} (times : Fin (n + 1) → NNReal) :
    Measurable (fun ω : Ω ↦ fun i ↦ ω (times i)) := by
  -- Each coordinate evaluation is continuous, hence measurable, and finite products preserve
  -- measurability.
  exact measurable_pi_lambda _ fun i ↦ (continuous_eval_const (times i)).measurable

/-- The finite-dimensional marginal of a probability measure on `C([0, ∞), ℝ)` along the time
tuple `times`. -/
noncomputable def continuousPathFiniteDimensionalDistribution (μ : ProbabilityMeasure Ω)
    {n : ℕ} (times : Fin (n + 1) → NNReal) : ProbabilityMeasure (Fin (n + 1) → ℝ) :=
  ProbabilityMeasure.map μ (measurable_continuousPathProjection times).aemeasurable

-- Proof sketch: unfold `continuousPathFiniteDimensionalDistribution`; it is defined as the
-- pushforward of `μ` by the path-evaluation map `ω ↦ (ω (times i))ᵢ`.
/-- Coercing the finite-dimensional marginal to a measure recovers the corresponding pushforward
measure. -/
theorem continuousPathFiniteDimensionalDistribution_toMeasure (μ : ProbabilityMeasure Ω)
    {n : ℕ} (times : Fin (n + 1) → NNReal) :
    (continuousPathFiniteDimensionalDistribution μ times : Measure (Fin (n + 1) → ℝ)) =
      (μ : Measure Ω).map (fun ω ↦ fun i ↦ ω (times i)) := by
  -- This is exactly the defining coercion of `ProbabilityMeasure.map` to an underlying measure.
  rfl

/-- Helper for Theorem 21.38: equality of all finite-dimensional marginals forces equality of the
finite-coordinate pushforwards indexed by a nonempty finset of times. -/
private theorem map_restrict_eq_of_continuousPathMarginals_eq
    {P Q : ProbabilityMeasure Ω}
    (h :
      ∀ {n : ℕ} (times : Fin (n + 1) → NNReal),
        continuousPathFiniteDimensionalDistribution P times =
          continuousPathFiniteDimensionalDistribution Q times)
    {I : Finset NNReal} (hI : I.Nonempty) :
    (P : Measure Ω).map (fun ω : Ω ↦ I.restrict (ω : NNReal → ℝ)) =
      (Q : Measure Ω).map (fun ω : Ω ↦ I.restrict (ω : NNReal → ℝ)) := by
  classical
  let e : Fin ((I.card - 1) + 1) ≃ I :=
    (Fintype.equivFinOfCardEq
      (show Fintype.card I = ((I.card - 1) + 1) by
        simpa using (Nat.succ_pred_eq_of_pos (Finset.card_pos.2 hI)).symm)).symm
  let times : Fin ((I.card - 1) + 1) → NNReal := fun i ↦ (e i : NNReal)
  let f : Ω → Fin ((I.card - 1) + 1) → ℝ := fun ω i ↦ ω (times i)
  let eπ : (Fin ((I.card - 1) + 1) → ℝ) ≃ᵐ (I → ℝ) :=
    MeasurableEquiv.piCongrLeft (fun _ : I ↦ ℝ) e
  have hf : Measurable f := by
    -- The enumerated coordinate tuple is measurable coordinatewise.
    exact measurable_pi_lambda _ fun i ↦ (continuous_eval_const (times i)).measurable
  have hfin : (P : Measure Ω).map f = (Q : Measure Ω).map f := by
    -- Rewrite the chosen enumeration as a finite-dimensional distribution.
    simpa [continuousPathFiniteDimensionalDistribution, f, times]
      using congrArg
        ((↑) :
          ProbabilityMeasure (Fin ((I.card - 1) + 1) → ℝ) →
            Measure (Fin ((I.card - 1) + 1) → ℝ))
        (h times)
  have hcomp :
      eπ ∘ f =
        fun ω : Ω ↦ I.restrict (ω : NNReal → ℝ) := by
    -- The measurable equivalence merely reindexes the same finite tuple of coordinates.
    funext ω
    ext i
    simpa [eπ, f, times] using
      (MeasurableEquiv.piCongrLeft_apply_apply (β := fun _ : I ↦ ℝ) e (f ω) (e.symm i))
  calc
    (P : Measure Ω).map (fun ω : Ω ↦ I.restrict (ω : NNReal → ℝ))
      = ((P : Measure Ω).map f).map eπ := by
          rw [Measure.map_map eπ.measurable hf]
          simp [hcomp]
    _ = ((Q : Measure Ω).map f).map eπ := by
          exact congrArg
            (fun m : Measure (Fin ((I.card - 1) + 1) → ℝ) ↦
              m.map eπ)
            hfin
    _ = (Q : Measure Ω).map (fun ω : Ω ↦ I.restrict (ω : NNReal → ℝ)) := by
          rw [Measure.map_map eπ.measurable hf]
          simp [hcomp]

/-- Helper for Theorem 21.38: finite restriction maps on the path space are measurable. -/
private theorem measurable_finsetRestrict (I : Finset NNReal) :
    Measurable (fun ω : Ω ↦ I.restrict (ω : NNReal → ℝ)) := by
  -- Each restricted coordinate is an evaluation map at a deterministic time.
  exact measurable_pi_lambda _ fun i ↦ (continuous_eval_const (i : NNReal)).measurable

/-- Helper for Theorem 21.38: equality of all finite-dimensional marginals determines the whole
law on `C([0, ∞), ℝ)`. -/
private theorem probabilityMeasure_eq_of_continuousPathMarginals_eq
    {P Q : ProbabilityMeasure Ω}
    (h :
      ∀ {n : ℕ} (times : Fin (n + 1) → NNReal),
        continuousPathFiniteDimensionalDistribution P times =
          continuousPathFiniteDimensionalDistribution Q times) :
    P = Q := by
  classical
  let E : Set (Set Ω) :=
    Set.preimage ((↑) : Ω → NNReal → ℝ) '' measurableCylinders (fun _ : NNReal ↦ ℝ)
  have hA : borel Ω = MeasurableSpace.generateFrom E := by
    -- Theorem 21.31 identifies the path-space Borel structure with the pullback of the product
    -- measurable space along the coordinate inclusion.
    rw [← continuousPathSpace_comap_pi_eq_borel,
      ← (generateFrom_measurableCylinders :
        MeasurableSpace.generateFrom (measurableCylinders (fun _ : NNReal ↦ ℝ)) =
          MeasurableSpace.pi),
      MeasurableSpace.comap_generateFrom]
  have hE : IsPiSystem E := by
    have hmc : IsPiSystem (measurableCylinders (fun _ : NNReal ↦ ℝ)) := by
      simpa using
        (isPiSystem_measurableCylinders :
          IsPiSystem (measurableCylinders (fun _ : NNReal ↦ ℝ)))
    intro s hs t ht hst
    rcases hs with ⟨s', hs', rfl⟩
    rcases ht with ⟨t', ht', rfl⟩
    have hmc' := hmc s' hs' t' ht'
    refine ⟨s' ∩ t', hmc' ?_, rfl⟩
    rcases hst with ⟨ω, hsω, htω⟩
    exact ⟨(ω : NNReal → ℝ), hsω, htω⟩
  have hPQ : (P : Measure Ω) = (Q : Measure Ω) := by
    -- Equality on the generating cylinder `π`-system extends to the whole Borel `σ`-algebra.
    refine measure_ext_of_generateFrom_of_isProbabilityMeasure hA hE ?_
    intro t ht
    rcases ht with ⟨u, hu, rfl⟩
    obtain ⟨I, S, hS, rfl⟩ := (mem_measurableCylinders u).1 hu
    by_cases hI : I.Nonempty
    · have hmap := map_restrict_eq_of_continuousPathMarginals_eq h hI
      have hmap_apply_P :
          (P : Measure Ω).map (fun ω : Ω ↦ I.restrict (ω : NNReal → ℝ)) S =
            (P : Measure Ω) ((fun ω : Ω ↦ I.restrict (ω : NNReal → ℝ)) ⁻¹' S) :=
        Measure.map_apply (measurable_finsetRestrict I) hS
      have hmap_apply_Q :
          (Q : Measure Ω).map (fun ω : Ω ↦ I.restrict (ω : NNReal → ℝ)) S =
            (Q : Measure Ω) ((fun ω : Ω ↦ I.restrict (ω : NNReal → ℝ)) ⁻¹' S) :=
        Measure.map_apply (measurable_finsetRestrict I) hS
      rw [show ((↑) : Ω → NNReal → ℝ) ⁻¹' cylinder I S =
          (fun ω : Ω ↦ I.restrict (ω : NNReal → ℝ)) ⁻¹' S by
            rfl,
        ← hmap_apply_P,
        hmap,
        hmap_apply_Q]
    · have hI0 : I = ∅ := Finset.not_nonempty_iff_eq_empty.mp hI
      subst hI0
      have : Subsingleton ((i : (∅ : Finset NNReal)) → ℝ) := inferInstance
      rcases Set.eq_empty_or_nonempty S with hSempty | hSnonempty
      · simp [hSempty]
      · have hSuniv : S = Set.univ := Subsingleton.eq_univ_of_nonempty hSnonempty
        simp [hSuniv]
  exact ProbabilityMeasure.toMeasure_injective hPQ

/-- Helper for Theorem 21.38: weak convergence on path space implies weak convergence of every
finite-dimensional marginal law. -/
private theorem tendsto_continuousPathFiniteDimensionalDistribution_of_tendsto
    {μs : ℕ → ProbabilityMeasure Ω} {μ : ProbabilityMeasure Ω}
    (hμ : Tendsto μs atTop (𝓝 μ)) (n : ℕ) (times : Fin (n + 1) → NNReal) :
    Tendsto
      (fun k ↦ continuousPathFiniteDimensionalDistribution (μs k) times)
      atTop
      (𝓝 (continuousPathFiniteDimensionalDistribution μ times)) := by
  let f : Ω → Fin (n + 1) → ℝ := fun ω i ↦ ω (times i)
  have hf_cont : Continuous f := by
    -- The finite-time projection is continuous coordinatewise.
    exact continuous_pi fun i ↦ continuous_eval_const (times i)
  -- Apply the continuous-mapping theorem to the finite-time projection.
  simpa [continuousPathFiniteDimensionalDistribution, f]
    using ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous μs μ hμ hf_cont

/-- Helper for Theorem 21.38: adjoining the limit law gives a compactly controlled tight family
of path measures. -/
private theorem tightProbabilityMeasureInsertRange_of_tendsto
    {μ : ProbabilityMeasure Ω} {μn : ℕ → ProbabilityMeasure Ω}
    (hμ : Tendsto μn atTop (𝓝 μ)) :
    IsTightMeasureSet
      {((ν : ProbabilityMeasure Ω) : Measure Ω) | ν ∈ insert μ (Set.range μn)} := by
  -- Route correction: first freeze compactness of the inserted family, then invoke the compact
  -- family bridge instead of asking Lean to normalize the large `insert/range` term in place.
  have hCompactInsert : IsCompact (insert μ (Set.range μn)) := hμ.isCompact_insert_range
  -- Reuse the earlier compact-family bridge in the exact coercion view required here.
  simpa [MeasureTheory.probabilityMeasureView] using
    (MeasureTheory.compactProbabilityMeasureViewIsTight
      (C := insert μ (Set.range μn)) hCompactInsert)

/-- Helper for Theorem 21.38: a weakly convergent sequence of path laws has tight range. -/
private theorem tightProbabilityMeasureRange_of_tendsto
    {μ : ProbabilityMeasure Ω} {μn : ℕ → ProbabilityMeasure Ω}
    (hμ : Tendsto μn atTop (𝓝 μ)) :
    IsTightMeasureSet
      (Set.range fun n ↦ (μn n : Measure Ω)) := by
  have hTightInsert :
      IsTightMeasureSet
        {((ν : ProbabilityMeasure Ω) : Measure Ω) | ν ∈ insert μ (Set.range μn)} :=
    tightProbabilityMeasureInsertRange_of_tendsto (μ := μ) (μn := μn) hμ
  have hTightInsertImage :
      IsTightMeasureSet (((↑) : ProbabilityMeasure Ω → Measure Ω) '' insert μ (Set.range μn)) := by
    convert hTightInsert using 1
  -- Tightness is inherited by the range after removing the extra limit point `μ`.
  have hTightImage :
      IsTightMeasureSet (((↑) : ProbabilityMeasure Ω → Measure Ω) '' Set.range μn) := by
    refine hTightInsertImage.subset ?_
    rintro ν ⟨ρ, hρ, rfl⟩
    exact ⟨ρ, Or.inr hρ, rfl⟩
  convert hTightImage using 1
  ext ν
  constructor
  · rintro ⟨n, rfl⟩
    exact ⟨μn n, ⟨n, rfl⟩, rfl⟩
  · rintro ⟨ρ, ⟨n, rfl⟩, rfl⟩
    exact ⟨n, rfl⟩

/-- Helper for Theorem 21.38: any map cluster point with the prescribed finite-dimensional limits
must equal the target law. -/
private theorem mapClusterPt_eq_of_continuousPathMarginals_tendsto
    (P : ProbabilityMeasure Ω) (Pn : ℕ → ProbabilityMeasure Ω)
    (hfd :
      ∀ n : ℕ, ∀ times : Fin (n + 1) → NNReal,
        Tendsto (fun k ↦ continuousPathFiniteDimensionalDistribution (Pn k) times) atTop
          (𝓝 (continuousPathFiniteDimensionalDistribution P times)))
    {Q : ProbabilityMeasure Ω} (hQ : MapClusterPt Q atTop Pn) :
    Q = P := by
  obtain ⟨ψ, hψmono, hψtendsto⟩ :=
    TopologicalSpace.FirstCountableTopology.tendsto_subseq hQ
  -- Compare the finite-dimensional marginals along the convergent subsequence and use uniqueness
  -- of limits in the finite-dimensional target space.
  refine probabilityMeasure_eq_of_continuousPathMarginals_eq ?_
  intro n times
  have hQmarg :
      Tendsto
        (fun k ↦ continuousPathFiniteDimensionalDistribution (Pn (ψ k)) times)
        atTop
        (𝓝 (continuousPathFiniteDimensionalDistribution Q times)) :=
    tendsto_continuousPathFiniteDimensionalDistribution_of_tendsto hψtendsto n times
  have hPmarg :
      Tendsto
        (fun k ↦ continuousPathFiniteDimensionalDistribution (Pn (ψ k)) times)
        atTop
        (𝓝 (continuousPathFiniteDimensionalDistribution P times)) :=
    (hfd n times).comp hψmono.tendsto_atTop
  exact tendsto_nhds_unique hQmarg hPmarg

-- Proof sketch: weak convergence on `C([0, ∞), ℝ)` implies weak convergence of every finite-time
-- projection by continuity of the projection map, and Prokhorov yields tightness. Conversely,
-- tightness gives relative compactness, and Lemma 21.36 identifies every subsequential weak limit
-- with `P` from the common finite-dimensional marginals.
/-- Theorem 21.38: for probability measures on `C([0, ∞), ℝ)`, weak convergence is equivalent to
finite-dimensional-distribution convergence together with tightness of the sequence. -/
theorem tendsto_iff_finiteDimensionalDistribution_tendsto_and_isTight
    (P : ProbabilityMeasure Ω) (Pn : ℕ → ProbabilityMeasure Ω) :
    ((∀ n : ℕ, ∀ times : Fin (n + 1) → NNReal,
        Tendsto (fun k ↦ continuousPathFiniteDimensionalDistribution (Pn k) times) atTop
          (𝓝 (continuousPathFiniteDimensionalDistribution P times))) ∧
      IsTightMeasureSet (Set.range fun n ↦ (Pn n : Measure Ω))) ↔
        Tendsto Pn atTop (𝓝 P) := by
  constructor
  · rintro ⟨hfd, htight⟩
    have htightRange :
        IsTightMeasureSet (((↑) : ProbabilityMeasure Ω → Measure Ω) '' Set.range Pn) := by
      convert htight using 1
      ext μ
      constructor
      · rintro ⟨ν, ⟨n, rfl⟩, rfl⟩
        exact ⟨n, rfl⟩
      · rintro ⟨n, rfl⟩
        exact ⟨Pn n, ⟨n, rfl⟩, rfl⟩
    have hcomp : IsCompact (closure (Set.range Pn)) :=
      isCompact_closure_of_isTightMeasureSet (S := Set.range Pn) htightRange
    -- Tightness gives compact closure of the sequence, and the marginal hypothesis identifies all
    -- cluster points with `P`.
    refine hcomp.tendsto_nhds_of_unique_mapClusterPt ?_ ?_
    · exact Filter.Eventually.of_forall fun n ↦ subset_closure ⟨n, rfl⟩
    · intro Q _hQmem hQcluster
      exact mapClusterPt_eq_of_continuousPathMarginals_tendsto P Pn hfd hQcluster
  · intro hweak
    refine ⟨?_, ?_⟩
    · -- Weak convergence passes to every finite-time projection by continuity.
      intro n times
      exact tendsto_continuousPathFiniteDimensionalDistribution_of_tendsto hweak n times
    · -- The range is tight because a convergent sequence is relatively compact in measure space.
      exact tightProbabilityMeasureRange_of_tendsto (μ := P) (μn := Pn) hweak

end ProbabilityTheory
