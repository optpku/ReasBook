/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib
import Books.ProbabilityTheory_Klenke_2020.Items.Chap23.Definition_23_7

-- Declarations for this item will be appended below by the statement pipeline.

open Filter MeasureTheory Topology
open scoped Topology

noncomputable section

universe u

namespace ProbabilityTheory

variable {E : Type u} [MeasurableSpace E]

/-- Helper for Theorem 23.8: enlarging the underlying set can only increase the scaled logarithmic
mass. -/
private theorem scaledLogMassAlong_mono {ι : Type*}
    (μ : ι → Measure E) (ε : ι → PositiveParameter) {s t : Set E}
    (hst : s ⊆ t) (i : ι) :
    scaledLogMassAlong μ ε s i ≤ scaledLogMassAlong μ ε t i := by
  -- Expand the definition once and use monotonicity of measure, `ENNReal.log`, and multiplication
  -- by the nonnegative parameter.
  rw [scaledLogMassAlong_def, scaledLogMassAlong_def]
  have hε : (0 : EReal) ≤ ((ε i : ℝ) : EReal) := by
    exact_mod_cast (le_of_lt (ε i).2)
  exact mul_le_mul_of_nonneg_left (ENNReal.log_le_log (measure_mono hst)) hε

variable [PseudoMetricSpace E]

/-- Helper for Theorem 23.8: the positive-parameter filter is nontrivial because `ε > 0`
approaches `0` from the right along a nonempty neighborhood basis. -/
private instance positiveParameterFilter_neBot :
    NeBot (positiveParameterFilter : Filter PositiveParameter) := by
  rw [positiveParameterFilter]
  exact (show NeBot (𝓝[>] (0 : ℝ)) from inferInstance).comap_of_range_mem (by
    simpa [PositiveParameter, Subtype.range_coe] using
      (self_mem_nhdsWithin : Set.Ioi (0 : ℝ) ∈ 𝓝[>] (0 : ℝ)))

/-- Helper for Theorem 23.8: a strict cutoff below `J x` remains valid on a sufficiently small
closed ball around `x`. -/
private theorem exists_closedBallSubsetSuperlevel_of_lowerSemicontinuous
    {J : E → ENNReal} (hJ : LowerSemicontinuous J) {x : E} {r : NNReal}
    (hr : (r : ENNReal) < J x) :
    ∃ δ > 0, Metric.closedBall x δ ⊆ {y | (r : ENNReal) < J y} := by
  -- Lower semicontinuity turns the strict superlevel set into an open neighborhood of `x`.
  have hOpen : IsOpen (J ⁻¹' Set.Ioi (r : ENNReal)) := hJ.isOpen_preimage (r : ENNReal)
  have hx : x ∈ J ⁻¹' Set.Ioi (r : ENNReal) := by
    simpa using hr
  rcases Metric.mem_nhds_iff.mp (hOpen.mem_nhds hx) with ⟨δ, hδpos, hδsubset⟩
  refine ⟨δ / 2, half_pos hδpos, ?_⟩
  -- Shrinking to a closed ball keeps us inside the same open neighborhood.
  intro y hy
  exact hδsubset <| Metric.closedBall_subset_ball (half_lt_self hδpos) hy

/-- Helper for Theorem 23.8: every strict `NNReal` cutoff below `J x` also lies below `I x` when
`I` and `J` arise from the same LDP family. -/
private theorem nnrealCutoff_le_leftRate_of_sameLdp (μ : PositiveProbabilityFamily E)
    {I J : E → ENNReal} (hI : HasLargeDeviationsPrinciple μ I)
    (hJ : HasLargeDeviationsPrinciple μ J) {x : E} {r : NNReal}
    (hr : (r : ENNReal) < J x) :
    (r : ENNReal) ≤ I x := by
  rcases exists_closedBallSubsetSuperlevel_of_lowerSemicontinuous hJ.lowerSemicontinuous hr with
    ⟨δ, hδpos, hδsubset⟩
  have hLower :
      -sInf ((fun y ↦ (I y : EReal)) '' Metric.ball x δ) ≤
        liminf (scaledLogMassAlong (fun ε ↦ (μ ε : Measure E)) id (Metric.ball x δ))
          positiveParameterFilter := by
    -- The open-ball lower bound is the lower-bound half of the LDP.
    simpa using hI.open_lower_bound (U := Metric.ball x δ) Metric.isOpen_ball
  have hUpper :
      limsup (scaledLogMassAlong (fun ε ↦ (μ ε : Measure E)) id (Metric.closedBall x δ))
          positiveParameterFilter ≤
        -sInf ((fun y ↦ (J y : EReal)) '' Metric.closedBall x δ) := by
    -- The closed-ball upper bound is the upper-bound half of the LDP.
    simpa using hJ.closed_upper_bound (C := Metric.closedBall x δ) Metric.isClosed_closedBall
  have hMono :
      liminf (scaledLogMassAlong (fun ε ↦ (μ ε : Measure E)) id (Metric.ball x δ))
          positiveParameterFilter ≤
        limsup (scaledLogMassAlong (fun ε ↦ (μ ε : Measure E)) id (Metric.closedBall x δ))
          positiveParameterFilter := by
    -- The mass of the ball is pointwise dominated by the mass of the closed ball.
    refine Filter.liminf_le_limsup_of_frequently_le ?_
    exact Filter.Frequently.of_forall fun ε =>
      scaledLogMassAlong_mono (μ := fun ε ↦ (μ ε : Measure E)) (ε := id)
        (s := Metric.ball x δ) (t := Metric.closedBall x δ) Metric.ball_subset_closedBall ε
  have hsInfJ_le_hsInfI :
      sInf ((fun y ↦ (J y : EReal)) '' Metric.closedBall x δ) ≤
        sInf ((fun y ↦ (I y : EReal)) '' Metric.ball x δ) := by
    -- Negating the chained LDP estimates converts them into an infimum comparison.
    have hneg :
        -sInf ((fun y ↦ (I y : EReal)) '' Metric.ball x δ) ≤
          -sInf ((fun y ↦ (J y : EReal)) '' Metric.closedBall x δ) := by
      exact le_trans hLower (le_trans hMono hUpper)
    exact EReal.neg_le_neg_iff.mp hneg
  have hr_le_sInfJ :
      (((r : ENNReal) : EReal)) ≤
        sInf ((fun y ↦ (J y : EReal)) '' Metric.closedBall x δ) := by
    -- Every point of the chosen closed ball stays above the cutoff `r`.
    refine le_sInf ?_
    rintro _ ⟨y, hy, rfl⟩
    exact EReal.coe_ennreal_le_coe_ennreal_iff.2 <| le_of_lt (hδsubset hy)
  have hsInfI_le_Ix :
      sInf ((fun y ↦ (I y : EReal)) '' Metric.ball x δ) ≤ (I x : EReal) := by
    -- The center belongs to the open ball, so its value bounds the infimum from above.
    refine sInf_le ?_
    exact ⟨x, Metric.mem_ball_self hδpos, rfl⟩
  have hEReal : (((r : ENNReal) : EReal)) ≤ (I x : EReal) := by
    -- Putting the cutoff estimate and the infimum comparison together yields the claim.
    exact le_trans hr_le_sInfJ (le_trans hsInfJ_le_hsInfI hsInfI_le_Ix)
  exact EReal.coe_ennreal_le_coe_ennreal_iff.mp hEReal

/-- Helper for Theorem 23.8: two LDP rate functions for the same family are pointwise ordered. -/
private theorem rateFunction_le_of_sameLdp (μ : PositiveProbabilityFamily E)
    {I J : E → ENNReal} (hI : HasLargeDeviationsPrinciple μ I)
    (hJ : HasLargeDeviationsPrinciple μ J) :
    ∀ x, J x ≤ I x := by
  intro x
  -- Compare all strict `NNReal` cutoffs below `J x`, then invoke the standard `ENNReal` order
  -- criterion.
  refine ENNReal.le_of_forall_nnreal_lt fun r hr ↦ ?_
  exact nnrealCutoff_le_leftRate_of_sameLdp μ hI hJ (x := x) hr

-- Proof sketch: apply the LDP lower bound to the open balls around `x` and the upper bound for the
-- second rate function to the corresponding closed balls; then let the radius tend to `0` and use
-- lower semicontinuity of both rate functions to get `I x ≤ J x` and `J x ≤ I x`.
/-- Theorem 23.8: if the same positive-parameter family of measures satisfies the large deviations
principle with rate functions `I` and `J`, then the two rate functions coincide pointwise. -/
theorem ldp_rateFunction_unique (μ : PositiveProbabilityFamily E) {I J : E → ENNReal}
    (hI : HasLargeDeviationsPrinciple μ I) (hJ : HasLargeDeviationsPrinciple μ J) :
    I = J := by
  -- Compare the two candidate rate functions in both directions and conclude by antisymmetry.
  funext x
  exact le_antisymm (rateFunction_le_of_sameLdp μ hJ hI x) (rateFunction_le_of_sameLdp μ hI hJ x)

end ProbabilityTheory
