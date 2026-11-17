module

public import ReasLib.Optimization.DFP.Polar.General.RadiusProducts
public import ReasLib.Optimization.DFP.Polar.General.AngularBounds

public section

noncomputable section

open Filter
open scoped Topology

namespace DFP.Polar.General.ActualGeometry

/-- Helper for lem:polar-geometry: the concrete source points are the canonical
polar points used in the reusable near/far separation theorem. -/
theorem point_eq_polarPoint (p : Parameters) : p.point = Geometry.point p.radius p.angle := by
  funext k
  rw [p.point_def, Geometry.point_def]

/-- Helper for lem:polar-geometry: the complete geometric conclusions for one
actual source trajectory, together with the preceding radial construction data. -/
structure SourceGeometricData (p : Parameters) (j0 : ℕ)
    (N M B K c U a b s V : ℝ) : Prop where
  /-- Helper for lem:polar-geometry: actual radius asymptotics and both source decrement bounds. -/
  radial : RadiusProducts.SourceRadialData p j0 N M B K c U
  /-- Helper for lem:polar-geometry: both source angular increments are comparable to scale. -/
  angles : ∀ k,
    a * scale p.beta j0 (k / 2) ≤ (p.withStartIndex j0).angleIncrement k ∧
      (p.withStartIndex j0).angleIncrement k ≤ b * scale p.beta j0 (k / 2) ∧
        (p.withStartIndex j0).angleIncrement k < Real.pi
  /-- Helper for eq:polar-physical-step: every physical sine factor is positive. -/
  sine_pos : ∀ k, 0 < Real.sin ((p.withStartIndex j0).angleIncrement k)
  /-- Helper for eq:polar-separation: the source all-point-pair separation bound. -/
  separation : ∀ k m, k ≠ m →
    s * max (scale p.beta j0 (k / 2)) (scale p.beta j0 (m / 2)) ≤
      ‖(p.withStartIndex j0).point m - (p.withStartIndex j0).point k‖
  /-- Helper for eq:polar-orders: both sides of the source linear step-scale bound. -/
  steps : ∀ k,
    s * scale p.beta j0 (k / 2) ≤
        ‖(p.withStartIndex j0).point (k + 1) - (p.withStartIndex j0).point k‖ ∧
      ‖(p.withStartIndex j0).point (k + 1) - (p.withStartIndex j0).point k‖ ≤
        V * scale p.beta j0 (k / 2)
  /-- Helper for lem:polar-geometry: the full cluster set is exactly the unit circle. -/
  cluster : ∀ x : EuclideanSpace ℝ (Fin 2),
    MapClusterPt x atTop (p.withStartIndex j0).point ↔ ‖x‖ = 1

/-- lem:polar-geometry. The actual general polar construction has the source
radial principal term, quadratic decrements, linear step bounds, uniform all-pair
separation and complete unit-circle accumulation set. Every constant is chosen
before the final sufficiently large starting index. -/
theorem existsSourceGeometry (p : Parameters) (hβ : 0 < p.beta) (hβone : p.beta < 1) :
    ∃ N > 0, ∃ M > 0, ∃ B > 0, ∃ K > 0, ∃ c > 0, ∃ U > 0,
      ∃ a > 0, ∃ b > 0, ∃ s > 0, ∃ V > 0, ∃ J : ℕ, 0 < J ∧
        ∀ j0 : ℕ, J ≤ j0 → SourceGeometricData p j0 N M B K c U a b s V := by
  obtain ⟨N, hN, M, hM, B, hB, K, hK, c, hc, U, hU, JR, hJR, hRadial⟩ :=
    RadiusProducts.existsSourceRadialData p hβ hβone
  obtain ⟨a, ha, b, hb, JA, hJA, hAngles⟩ := AngularBounds.existsAngleBoundsWithSin p hβ
  let η := min 1 (Real.pi / b)
  have hη : 0 < η := lt_min zero_lt_one (div_pos Real.pi_pos hb)
  have hηone : η ≤ 1 := min_le_left _ _
  have hspan : b * η ≤ Real.pi := by
    have h := (le_div_iff₀ hb).mp (min_le_right 1 (Real.pi / b))
    simpa only [mul_comm] using h
  obtain ⟨s, hs, hSep⟩ := Geometry.exists_uniform_point_separation
    hβ hη hηone ha hb.le hc hspan
  have hsmall := (scale_tendsto_zero hβ 0).eventually (Iio_mem_nhds (half_pos hη))
  obtain ⟨JS, hJS⟩ := eventually_atTop.mp hsmall
  let V := U + B * b
  have hV : 0 < V := add_pos hU (mul_pos hB hb)
  refine ⟨N, hN, M, hM, B, hB, K, hK, c, hc, U, hU, a, ha, b, hb,
    s, hs, V, hV, max JR (max JA JS), hJR.trans_le (le_max_left _ _), ?_⟩
  intro j0 hj0
  have hjR : JR ≤ j0 := (le_max_left _ _).trans hj0
  have hjA : JA ≤ j0 := (le_max_left _ _).trans ((le_max_right _ _).trans hj0)
  have hjS : JS ≤ j0 := (le_max_right _ _).trans ((le_max_right _ _).trans hj0)
  have hstart : 0 < j0 := hJR.trans_le hjR
  let q := p.withStartIndex j0
  have hr := hRadial j0 hjR
  have hrNonneg (k : ℕ) : 0 ≤ q.radius k := zero_le_one.trans (hr.radii.above_one k).le
  have hLower (k : ℕ) : a * scale p.beta j0 (k / 2) ≤ q.angle (k + 1) - q.angle k := by
    simpa only [Parameters.angleIncrement_def] using (hAngles j0 hjA k).1.1
  have hUpper (k : ℕ) : q.angle (k + 1) - q.angle k ≤ b * scale p.beta j0 (k / 2) := by
    simpa only [Parameters.angleIncrement_def] using (hAngles j0 hjA k).1.2.1
  have hAngleNonneg (k : ℕ) : 0 ≤ q.angle (k + 1) - q.angle k :=
    (mul_nonneg ha.le (scale_nonneg p.beta j0 (k / 2))).trans (hLower k)
  have hScaleSmall : scale p.beta j0 0 ≤ η / 2 := by
    simpa only [scale_def, Nat.zero_add, Nat.add_zero] using (hJS j0 hjS).le
  have hSeparation (k m : ℕ) (hkm : k ≠ m) :
      s * max (scale p.beta j0 (k / 2)) (scale p.beta j0 (m / 2)) ≤
        ‖q.point m - q.point k‖ := by
    rw [point_eq_polarPoint]
    exact hSep j0 hstart hScaleSmall q.radius q.angle
      (fun k ↦ (hr.radii.above_one k).le) hLower hUpper hr.radii.drop_lower k m hkm
  have hSteps (k : ℕ) :
      s * scale p.beta j0 (k / 2) ≤ ‖q.point (k + 1) - q.point k‖ ∧
        ‖q.point (k + 1) - q.point k‖ ≤ V * scale p.beta j0 (k / 2) := by
    constructor
    · have hpair := hSeparation k (k + 1) (Nat.ne_of_lt (Nat.lt_succ_self k))
      exact (mul_le_mul_of_nonneg_left (le_max_left _ _) hs.le).trans hpair
    · have hDropNonneg (l : ℕ) : 0 ≤ q.radius l - q.radius (l + 1) :=
        (mul_nonneg hc.le (sq_nonneg _)).trans (hr.radii.drop_lower l)
      rw [point_eq_polarPoint]
      exact Geometry.point_step_upper_of_scalar_bounds hβ hstart hU.le hrNonneg
        hr.radii.upper hAngleNonneg hUpper hDropNonneg hr.radii.drop_upper k
  have hCluster (x : EuclideanSpace ℝ (Fin 2)) : MapClusterPt x atTop q.point ↔ ‖x‖ = 1 := by
    rw [point_eq_polarPoint]
    exact Geometry.point_cluster_iff_of_scalar_bounds hβ hstart ha hrNonneg
      hr.radii.tendsto_one hLower hUpper x
  exact ⟨hr, fun k ↦ (hAngles j0 hjA k).1, fun k ↦ (hAngles j0 hjA k).2,
    hSeparation, hSteps, hCluster⟩

end DFP.Polar.General.ActualGeometry
