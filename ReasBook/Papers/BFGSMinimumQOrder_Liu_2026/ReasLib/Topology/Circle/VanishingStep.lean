module

public import ReasLib.Topology.Real.VanishingStepModulo
public import Mathlib.Analysis.SpecialFunctions.Complex.Circle

public section

open Filter
open scoped Topology

namespace Circle

/-- The exponential image of a strictly decreasing real sequence tending to negative infinity
with successive drops tending to zero has every point of the circle as an `atTop` cluster
point. -/
theorem mapClusterPtExpOfVanishingStep {φ : ℕ → ℝ} (hstrict : StrictAnti φ)
    (hbot : Tendsto φ atTop atBot)
    (hstep : Tendsto (fun j : ℕ ↦ φ j - φ (j + 1)) atTop (𝓝 0)) (z : Circle) :
    MapClusterPt z atTop (fun j ↦ Circle.exp (φ j)) := by
  -- Represent the target point by an angle, then choose the first-crossing subsequence
  -- supplied by the real vanishing-step theorem.
  obtain ⟨θ, hθ⟩ := Circle.exp_surjective z
  obtain ⟨j, m, hj, hm⟩ :=
    Real.existsSubseqAddIntMulTendsto (2 * Real.pi) Real.two_pi_pos
      hstrict hbot hstep θ
  -- Integer multiples of the full period disappear after applying the circle exponential.
  have hperiodic : ∀ i,
      Circle.exp (φ (j i) + m i * (2 * Real.pi)) = Circle.exp (φ (j i)) := by
    intro i
    exact (Circle.periodic_exp.int_mul (m i)) (φ (j i))
  -- Continuity transports the corrected real limit, and periodicity identifies it with
  -- the uncorrected exponential subsequence.
  have hsubseq : Tendsto (fun i ↦ Circle.exp (φ (j i))) atTop (𝓝 (Circle.exp θ)) := by
    refine Tendsto.congr' (Eventually.of_forall hperiodic) ?_
    exact (Circle.exp.continuous.tendsto θ).comp hm
  have hcluster :
      MapClusterPt (Circle.exp θ) atTop ((fun n ↦ Circle.exp (φ n)) ∘ j) := by
    exact hsubseq.mapClusterPt
  -- The strict subsequence is cofinal, so its cluster point is a cluster point of the
  -- original sequence; the chosen angle then recovers the prescribed circle point.
  simpa only [hθ] using hcluster.of_comp hj.tendsto_atTop

end Circle
