module

public import Mathlib.Analysis.Asymptotics.AsymptoticEquivalent
public import Mathlib.Topology.MetricSpace.Thickening
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FieldSimp

public section

open Filter Topology
open scoped Asymptotics Topology

universe u

namespace Metric

/-- If center-to-target distance is asymptotic to a positive multiple of a
scale and the support radii are negligible relative to that distance, then
every point in the corresponding supports has target distance comparable to
the same scale. -/
theorem eventually_infDist_mem_Icc_of_support_radius_isLittleO
    {X : Type u} [PseudoMetricSpace X] (Γ : Set X)
    (x : ℕ → X) (scale radius : ℕ → ℝ) (support : ℕ → Set X) (q : ℝ)
    (hq : 0 < q) (hscale : ∀ k, 0 < scale k)
    (hdistance : (fun k ↦ infDist (x k) Γ) ~[atTop]
      (fun k ↦ q * scale k))
    (hradius : radius =o[atTop] (fun k ↦ infDist (x k) Γ))
    (hsupport : ∀ k, support k ⊆ closedBall (x k) (radius k)) :
    ∃ cLower > 0, ∃ cUpper > 0, ∀ᶠ k : ℕ in atTop,
      ∀ z ∈ support k,
        infDist z Γ ∈ Set.Icc (cLower * scale k) (cUpper * scale k) := by
  let d : ℕ → ℝ := fun k ↦ infDist (x k) Γ
  have hDistanceError : ∀ᶠ k in atTop,
      ‖d k - q * scale k‖ ≤ (1 / 4 : ℝ) * ‖q * scale k‖ :=
    (hdistance.isLittleO.forall_isBigOWith
      (by norm_num : (0 : ℝ) < 1 / 4)).bound
  have hRadiusSmall : ∀ᶠ k in atTop,
      ‖radius k‖ ≤ (1 / 4 : ℝ) * ‖d k‖ :=
    (hradius.forall_isBigOWith
      (by norm_num : (0 : ℝ) < 1 / 4)).bound
  refine ⟨q / 4, div_pos hq (by norm_num), 2 * q,
    mul_pos (by norm_num) hq, ?_⟩
  filter_upwards [hDistanceError, hRadiusSmall] with k hkDistance hkRadius
  intro z hz
  have hqs : 0 < q * scale k := mul_pos hq (hscale k)
  have hdNonneg : 0 ≤ d k := infDist_nonneg
  have hDistanceError' :
      |d k - q * scale k| ≤ (1 / 4 : ℝ) * (q * scale k) := by
    simpa only [Real.norm_eq_abs, abs_of_pos hqs] using hkDistance
  have hdLower : (3 / 4 : ℝ) * (q * scale k) ≤ d k := by
    linarith [(abs_le.mp hDistanceError').1]
  have hdUpper : d k ≤ (5 / 4 : ℝ) * (q * scale k) := by
    linarith [(abs_le.mp hDistanceError').2]
  have hRadiusSmall' : radius k ≤ (1 / 4 : ℝ) * d k := by
    have habs : |radius k| ≤ (1 / 4 : ℝ) * d k := by
      simpa only [Real.norm_eq_abs, abs_of_nonneg hdNonneg] using hkRadius
    exact (le_abs_self (radius k)).trans habs
  have hzDist : dist z (x k) ≤ radius k := by
    simpa only [mem_closedBall] using hsupport k hz
  have hzUpperRaw : infDist z Γ ≤ d k + dist z (x k) := by
    simpa only [d] using
      (infDist_le_infDist_add_dist (s := Γ) (x := z) (y := x k))
  have hzLowerRaw : d k ≤ infDist z Γ + dist z (x k) := by
    simpa only [d, dist_comm] using
      (infDist_le_infDist_add_dist (s := Γ) (x := x k) (y := z))
  constructor <;> nlinarith

/-- If both the center distance to a closed nonempty target and the radii tend
to zero, every positive closed thickening of the target eventually contains
the corresponding closed balls. -/
theorem eventually_closedBall_subset_cthickening_of_tendsto
    {X : Type u} [PseudoMetricSpace X] [ProperSpace X]
    (Γ : Set X) (x : ℕ → X) (radius : ℕ → ℝ)
    (hΓ : IsClosed Γ) (hΓne : Γ.Nonempty)
    (hx : Tendsto (fun k ↦ infDist (x k) Γ) atTop (𝓝 0))
    (hradius : Tendsto radius atTop (𝓝 0))
    (δ : ℝ) (hδ : 0 < δ) :
    ∀ᶠ k : ℕ in atTop, closedBall (x k) (radius k) ⊆ cthickening δ Γ := by
  have hsum : Tendsto
      (fun k ↦ infDist (x k) Γ + radius k) atTop (𝓝 0) := by
    simpa only [zero_add] using hx.add hradius
  have heventually : ∀ᶠ k : ℕ in atTop,
      infDist (x k) Γ + radius k < δ :=
    hsum.eventually (Iio_mem_nhds hδ)
  filter_upwards [heventually] with k hk
  intro y hy
  obtain ⟨q, hqΓ, hqDistance⟩ := hΓ.exists_infDist_eq_dist hΓne (x k)
  have hyCenter : dist y (x k) ≤ radius k := by
    simpa only [mem_closedBall] using hy
  have hyq : dist y q ≤ δ := by
    calc
      dist y q ≤ dist y (x k) + dist (x k) q := dist_triangle y (x k) q
      _ ≤ radius k + infDist (x k) Γ := by
        rw [hqDistance]
        exact add_le_add hyCenter le_rfl
      _ = infDist (x k) Γ + radius k := add_comm _ _
      _ ≤ δ := le_of_lt hk
  exact mem_cthickening_of_dist_le y q δ Γ hqΓ hyq

/-- A quantity bounded by a fixed multiple of a scale converges uniformly to
zero along support points approaching a target, provided target distance is
bounded below by a positive multiple of the same scale. -/
theorem uniform_decay_of_le_scale_of_mul_scale_le_infDist
    {X : Type u} [PseudoMetricSpace X] {ι : Type*}
    (Γ : Set X) (support : ι → Set X) (scale : ι → ℝ)
    (quantity : ι → X → ℝ) (c C : ℝ) (hc : 0 < c) (hC : 0 < C)
    (hdistance : ∀ i z, z ∈ support i → c * scale i ≤ infDist z Γ)
    (hquantity : ∀ i z, z ∈ support i → quantity i z ≤ C * scale i) :
    ∀ η > 0, ∃ δ > 0, ∀ i z, z ∈ support i →
      infDist z Γ < δ → quantity i z < η := by
  intro η hη
  let δ := c * (η / C)
  have hδ : 0 < δ := by
    dsimp only [δ]
    exact mul_pos hc (div_pos hη hC)
  refine ⟨δ, hδ, ?_⟩
  intro i z hz hzδ
  have hscale : scale i < η / C := by
    apply lt_of_mul_lt_mul_left _ hc.le
    exact (hdistance i z hz).trans_lt (by simpa only [δ] using hzδ)
  have hscaled : C * scale i < η := by
    calc
      C * scale i < C * (η / C) := mul_lt_mul_of_pos_left hscale hC
      _ = η := by field_simp [hC.ne']
  exact (hquantity i z hz).trans_lt hscaled

end Metric
