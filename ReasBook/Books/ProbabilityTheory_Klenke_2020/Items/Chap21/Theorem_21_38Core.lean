/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib
import Books.ProbabilityTheory_Klenke_2020.Items.Chap01.Lemma_1_42
import Books.ProbabilityTheory_Klenke_2020.Items.Chap21.Theorem_21_31
import Mathlib.MeasureTheory.Constructions.Projective

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
    change f ω (e.symm i) = ω i
    simp [f, times]
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

/-- Helper for Theorem 21.38: equality of all finite-dimensional marginals determines the whole
law on `C([0, ∞), ℝ)`. -/
private theorem probabilityMeasure_eq_of_continuousPathMarginals_eq
    {P Q : ProbabilityMeasure Ω}
    (h :
      ∀ {n : ℕ} (times : Fin (n + 1) → NNReal),
        continuousPathFiniteDimensionalDistribution P times =
          continuousPathFiniteDimensionalDistribution Q times) :
    P = Q := by
  let f : Ω → NNReal → ℝ := (↑)
  have hf_emb : MeasurableEmbedding f :=
    continuous_coeFun.measurableEmbedding DFunLike.coe_injective
  have hrestrict :
      ∀ I : Finset NNReal,
        (P : Measure Ω).map (fun ω : Ω ↦ I.restrict (ω : NNReal → ℝ)) =
          (Q : Measure Ω).map (fun ω : Ω ↦ I.restrict (ω : NNReal → ℝ)) := by
    intro I
    by_cases hI : I.Nonempty
    · exact map_restrict_eq_of_continuousPathMarginals_eq h hI
    · have hI0 : I = ∅ := Finset.not_nonempty_iff_eq_empty.mp hI
      subst hI0
      simp
  have hprojP :
      IsProjectiveLimit ((P : Measure Ω).map f)
        (fun I : Finset NNReal ↦
          (P : Measure Ω).map (fun ω : Ω ↦ I.restrict (ω : NNReal → ℝ))) := by
    -- The law of the full coordinate process is the projective limit of its finite restrictions.
    simpa [f] using
      (ProbabilityTheory.isProjectiveLimit_map
        (P := (P : Measure Ω))
        (X := fun t (ω : Ω) ↦ ω t)
        (continuous_coeFun.measurable.aemeasurable))
  have hprojQ :
      IsProjectiveLimit ((Q : Measure Ω).map f)
        (fun I : Finset NNReal ↦
          (Q : Measure Ω).map (fun ω : Ω ↦ I.restrict (ω : NNReal → ℝ))) := by
    -- The same projective-limit description holds for `Q`.
    simpa [f] using
      (ProbabilityTheory.isProjectiveLimit_map
        (P := (Q : Measure Ω))
        (X := fun t (ω : Ω) ↦ ω t)
        (continuous_coeFun.measurable.aemeasurable))
  have hmap : (P : Measure Ω).map f = (Q : Measure Ω).map f := by
    -- Equality of all finite restrictions forces equality of the full path laws in product space.
    refine hprojP.unique ?_
    simpa [hrestrict] using hprojQ
  exact ProbabilityMeasure.toMeasure_injective (hf_emb.map_injective hmap)

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
    · have hcompInsert : IsCompact (insert P (Set.range Pn)) := hweak.isCompact_insert_range
      have hclosureInsert : IsCompact (closure (insert P (Set.range Pn))) := by
        simpa [closure_eq_iff_isClosed.mpr hcompInsert.isClosed] using hcompInsert
      have htightInsert :
          IsTightMeasureSet
            (((↑) : ProbabilityMeasure Ω → Measure Ω) '' insert P (Set.range Pn)) :=
        MeasureTheory.isTightMeasureSet_of_isCompact_closure
          (S := insert P (Set.range Pn)) hclosureInsert
      -- Tightness is inherited by subsets, so we may drop the extra limit point `P`.
      refine htightInsert.subset ?_
      intro μ hμ
      rcases hμ with ⟨n, rfl⟩
      exact ⟨Pn n, Or.inr ⟨n, rfl⟩, rfl⟩

end ProbabilityTheory
