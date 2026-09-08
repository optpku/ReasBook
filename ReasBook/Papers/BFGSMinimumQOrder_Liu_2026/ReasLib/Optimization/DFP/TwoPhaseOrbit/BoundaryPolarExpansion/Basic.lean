module

public import ReasLib.Optimization.DFP.TwoPhaseOrbit.EndpointSet
public import Mathlib.Analysis.Asymptotics.Lemmas

public section

open Filter
open scoped Asymptotics Topology

namespace DFP.TwoPhaseOrbit

/-- Helper for Lemma 4.8c/4.9a: center and radial vector remainders add to the full
endpoint displacement remainder. -/
theorem vectorExpansion_of_center_and_radialRemainders
    {ι V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {l : Filter ι} {point center direction : ι → V}
    {amplitude : ι → ℝ} {C : V} {scale : ι → ℝ}
    (hcenter : (fun i ↦ center i - C) =o[l] scale)
    (hradial :
      (fun i ↦ point i - center i - amplitude i • direction i) =o[l] scale) :
    (fun i ↦ point i - C - amplitude i • direction i) =o[l] scale := by
  refine (hcenter.add hradial).congr_left ?_
  intro i
  abel

/-- Helper for Lemma 4.8c/4.9a: an exact center-plus-amplitude/frame identity transports
a center remainder directly to the endpoint displacement expansion. -/
theorem vectorExpansion_of_centerRemainder
    {ι V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {l : Filter ι} {point center direction : ι → V}
    {amplitude : ι → ℝ} {C : V} {scale : ι → ℝ}
    (hidentity : ∀ᶠ i in l, point i = center i + amplitude i • direction i)
    (hcenter : (fun i ↦ center i - C) =o[l] scale) :
    (fun i ↦ point i - C - amplitude i • direction i) =o[l] scale := by
  refine hcenter.congr' ?_ Filter.EventuallyEq.rfl
  filter_upwards [hidentity] with i hi
  rw [hi]
  abel

/-- Helper for Lemma 4.8c/4.9a: a unit-vector affine representative bounds the distance
from a point to the corresponding limiting circle by its vector remainder. -/
theorem infDist_limitCircle_le_norm_vectorRemainder
    (C : EuclideanSpace ℝ (Fin 2)) (G : ℝ)
    (x u : EuclideanSpace ℝ (Fin 2)) (hu : ‖u‖ = 1) :
    Metric.infDist x (limitCircle C G) ≤ ‖x - C - G • u‖ := by
  have hmem : C + G • u ∈ limitCircle C G := by
    exact mem_limitCircle.mpr ⟨u, hu, rfl⟩
  have hdist := Metric.infDist_le_dist_of_mem (x := x) hmem
  have hdiff : x - (C + G • u) = x - C - G • u := by
    abel
  rw [dist_eq_norm, hdiff] at hdist
  exact hdist

/-- Helper for Lemma 4.8c/4.9a: a little-o vector remainder yields the same little-o
bound for distance to the limiting circle when the frame vectors are eventually unit. -/
theorem infDist_limitCircle_isLittleO_of_vectorRemainder
    {ι : Type*} {l : Filter ι}
    {x direction : ι → EuclideanSpace ℝ (Fin 2)}
    {C : EuclideanSpace ℝ (Fin 2)} {G : ℝ} {scale : ι → ℝ}
    (hunit : ∀ᶠ i in l, ‖direction i‖ = 1)
    (hrem :
      (fun i ↦ x i - C - G • direction i) =o[l] scale) :
    (fun i ↦ Metric.infDist (x i) (limitCircle C G)) =o[l] scale := by
  apply Asymptotics.IsLittleO.of_bound
  intro c hc
  filter_upwards [hunit, hrem.bound hc] with i hi hremi
  have hdist := infDist_limitCircle_le_norm_vectorRemainder
    C G (x i) (direction i) hi
  calc
    ‖Metric.infDist (x i) (limitCircle C G)‖ =
        Metric.infDist (x i) (limitCircle C G) := by
          rw [Real.norm_eq_abs, abs_of_nonneg Metric.infDist_nonneg]
    _ ≤ ‖x i - C - G • direction i‖ := hdist
    _ ≤ c * ‖scale i‖ := hremi

/-- Helper for Lemma 4.8c/4.9a: if the comparison scale tends to zero, the preceding
distance remainder also tends to zero. -/
theorem tendsto_infDist_limitCircle_of_vectorRemainder
    {ι : Type*} {l : Filter ι}
    {x direction : ι → EuclideanSpace ℝ (Fin 2)}
    {C : EuclideanSpace ℝ (Fin 2)} {G : ℝ} {scale : ι → ℝ}
    (hunit : ∀ᶠ i in l, ‖direction i‖ = 1)
    (hrem :
      (fun i ↦ x i - C - G • direction i) =o[l] scale)
    (hscale : Tendsto scale l (𝓝 0)) :
    Tendsto (fun i ↦ Metric.infDist (x i) (limitCircle C G)) l (𝓝 0) := by
  exact (infDist_limitCircle_isLittleO_of_vectorRemainder hunit hrem).tendsto_zero_of_tendsto
    hscale

end DFP.TwoPhaseOrbit
