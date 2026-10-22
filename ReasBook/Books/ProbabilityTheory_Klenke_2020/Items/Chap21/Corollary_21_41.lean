/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib.MeasureTheory.Measure.Tight
import Mathlib.MeasureTheory.Measure.AEMeasurable
import Mathlib.Topology.ContinuousMap.Algebra
import Mathlib.Topology.ContinuousMap.SecondCountableSpace

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory

universe u v

local notation "PathSpace" => ContinuousMap NNReal ℝ

local instance pathSpaceMeasurableSpace : MeasurableSpace PathSpace := borel _
local instance pathSpaceBorelSpace : BorelSpace PathSpace := ⟨rfl⟩

/-- Helper for Corollary 21.41: pointwise addition on `PathSpace` is measurable. -/
local instance pathSpaceMeasurableAdd₂ : MeasurableAdd₂ PathSpace := by
  refine ⟨?_⟩
  simpa using (continuous_fst.add continuous_snd).measurable

variable {I : Type v}

-- Proof sketch: apply the preceding tightness criterion on `C([0, ∞))`. The bounds needed there
-- for the family `X i + Y i` follow from the triangle inequality, both for uniform suprema on
-- compact time intervals and for the modulus-of-continuity terms.
/-- Corollary 21.41: if the laws of two families of continuous real-valued random variables on
`[0, ∞)` are tight, then the laws of their pointwise sums are tight. -/
theorem laws_of_sum_of_tight_continuous_process_families_are_tight
    {Ω : I → Type u} [∀ i, MeasurableSpace (Ω i)]
    (P : (i : I) → ProbabilityMeasure (Ω i))
    (X Y : (i : I) → Ω i → PathSpace)
    (hX : ∀ i, AEMeasurable (X i) (P i))
    (hY : ∀ i, AEMeasurable (Y i) (P i))
    (h_tight_X : IsTightMeasureSet (Set.range fun i ↦ ((P i).map (hX i) : Measure PathSpace)))
    (h_tight_Y : IsTightMeasureSet (Set.range fun i ↦ ((P i).map (hY i) : Measure PathSpace))) :
    IsTightMeasureSet
      (Set.range fun i ↦
        ((P i).map
          (show AEMeasurable (fun ω ↦ X i ω + Y i ω) (P i) from by
            simpa using (hX i).add (hY i)) : Measure PathSpace)) := by
  -- Route correction: the formal hypotheses already give tightness of the full law families,
  -- so the clean proof goes through joint laws and then a continuous pushforward by addition.
  let jointLaw : I → Measure (PathSpace × PathSpace) := fun i ↦
    ((P i).map ((hX i).prodMk (hY i)) : ProbabilityMeasure (PathSpace × PathSpace))
  let addPaths : PathSpace × PathSpace → PathSpace := fun p ↦ p.1 + p.2
  have h_addPaths_cont : Continuous addPaths := by
    simpa [addPaths] using (continuous_fst.add continuous_snd)
  have h_joint : IsTightMeasureSet (Set.range jointLaw) := by
    -- Tight marginals give a tight family of joint laws by using compact rectangles.
    rw [isTightMeasureSet_iff_exists_isCompact_measure_compl_le]
    intro ε hε
    obtain ⟨KX, hKX_compact, hKX⟩ :=
      (isTightMeasureSet_iff_exists_isCompact_measure_compl_le.mp h_tight_X) (ε / 2)
        (ENNReal.half_pos hε.ne')
    obtain ⟨KY, hKY_compact, hKY⟩ :=
      (isTightMeasureSet_iff_exists_isCompact_measure_compl_le.mp h_tight_Y) (ε / 2)
        (ENNReal.half_pos hε.ne')
    refine ⟨KX ×ˢ KY, hKX_compact.prod hKY_compact, ?_⟩
    intro μ hμ
    rcases hμ with ⟨i, rfl⟩
    have h_pair : AEMeasurable (fun ω ↦ (X i ω, Y i ω)) (P i) := (hX i).prodMk (hY i)
    have h_preimage :
        (fun ω ↦ (X i ω, Y i ω)) ⁻¹' ((KX ×ˢ KY)ᶜ) ⊆ (X i ⁻¹' KXᶜ) ∪ (Y i ⁻¹' KYᶜ) := by
      intro ω hω
      have hω' : ¬ (X i ω ∈ KX ∧ Y i ω ∈ KY) := by
        simpa [Set.mem_prod] using hω
      by_cases hXω : X i ω ∈ KX
      · right
        exact fun hYω ↦ hω' ⟨hXω, hYω⟩
      · left
        exact hXω
    calc
      jointLaw i ((KX ×ˢ KY)ᶜ)
          = (P i : Measure (Ω i)) ((fun ω ↦ (X i ω, Y i ω)) ⁻¹' ((KX ×ˢ KY)ᶜ)) := by
              simpa [jointLaw] using
                (Measure.map_apply_of_aemeasurable h_pair
                  (hKX_compact.prod hKY_compact).measurableSet.compl)
      _ ≤ (P i : Measure (Ω i)) ((X i ⁻¹' KXᶜ) ∪ (Y i ⁻¹' KYᶜ)) := by
        exact measure_mono h_preimage
      _ ≤ (P i : Measure (Ω i)) (X i ⁻¹' KXᶜ) + (P i : Measure (Ω i)) (Y i ⁻¹' KYᶜ) := by
        exact measure_union_le _ _
      _ =
          ((P i).map (hX i) : Measure PathSpace) KXᶜ
            + ((P i).map (hY i) : Measure PathSpace) KYᶜ := by
        -- Rewrite the marginal preimage terms through `ProbabilityMeasure.map_apply'`.
        rw [← (P i).map_apply' (hX i) hKX_compact.measurableSet.compl,
          ← (P i).map_apply' (hY i) hKY_compact.measurableSet.compl]
      _ ≤ ε / 2 + ε / 2 := by
        exact add_le_add (hKX _ ⟨i, rfl⟩) (hKY _ ⟨i, rfl⟩)
      _ = ε := ENNReal.add_halves ε
  have sumPathLaw_eq_map_add_jointLaw (i : I) :
      ((P i).map
        (show AEMeasurable (fun ω ↦ X i ω + Y i ω) (P i) from by
          simpa using (hX i).add (hY i)) : Measure PathSpace) =
        Measure.map addPaths (jointLaw i) := by
    -- The sum law is the joint law pushed forward by path addition.
    have h_sum : AEMeasurable (fun ω ↦ X i ω + Y i ω) (P i) := by
      simpa using (hX i).add (hY i)
    have h_pair : AEMeasurable (fun ω ↦ (X i ω, Y i ω)) (P i) := (hX i).prodMk (hY i)
    have h_add : AEMeasurable addPaths (jointLaw i) := h_addPaths_cont.aemeasurable
    -- First convert both probability laws to ordinary measure pushforwards.
    rw [ProbabilityMeasure.toMeasure_map (ν := P i) (hf := h_sum)]
    calc
      Measure.map (fun ω ↦ X i ω + Y i ω) (P i : Measure (Ω i))
          = Measure.map addPaths (Measure.map (fun ω ↦ (X i ω, Y i ω)) (P i : Measure (Ω i))) := by
              -- The sum map factors through the pair map followed by path addition.
              simpa [addPaths, Function.comp] using
                (AEMeasurable.map_map_of_aemeasurable
                  (μ := (P i : Measure (Ω i)))
                  (g := addPaths)
                  (f := fun ω ↦ (X i ω, Y i ω))
                  h_add h_pair).symm
      _ = Measure.map addPaths (jointLaw i) := by
        -- Unfold the joint law only at the final transport step.
        simp [jointLaw, ProbabilityMeasure.toMeasure_map]
  have h_joint_image :
      IsTightMeasureSet (Measure.map addPaths '' Set.range jointLaw) :=
    h_joint.map h_addPaths_cont
  have h_range_eq :
      Measure.map addPaths '' Set.range jointLaw =
        Set.range fun i ↦
          ((P i).map
            (show AEMeasurable (fun ω ↦ X i ω + Y i ω) (P i) from by
              simpa using (hX i).add (hY i)) : Measure PathSpace) := by
    -- The image family of the joint laws is exactly the target family of sum laws.
    ext μ
    constructor
    · rintro ⟨ν, hν, rfl⟩
      rcases hν with ⟨i, rfl⟩
      exact ⟨i, sumPathLaw_eq_map_add_jointLaw i⟩
    · rintro ⟨i, rfl⟩
      exact ⟨jointLaw i, ⟨i, rfl⟩, (sumPathLaw_eq_map_add_jointLaw i).symm⟩
  simpa [h_range_eq] using h_joint_image
