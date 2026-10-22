/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap02.Text_2_0_10
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap03.Definition_3_8
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap03.Theorem_3_16_1
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap03.Theorem_3_16_2

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open scoped InnerProductSpace

variable {𝓗 : Type u} [NormedAddCommGroup 𝓗] [InnerProductSpace ℝ 𝓗]

/- A hyperplane with nonzero normal is the translate of the kernel of
`x ↦ ⟪x, u⟫_ℝ`. -/
private lemma innerProductLevelSet_eq_mk'_ker_innerSLFlip (u : 𝓗) (η : ℝ) (hu : u ≠ 0) :
    innerProductLevelSet u η =
      (AffineSubspace.mk' ((η / ‖u‖ ^ 2) • u) ((innerSLFlip ℝ u).ker) : Set 𝓗) := by
  have hu_norm : ‖u‖ ≠ 0 := by
    simpa using hu
  have hu_sq : ‖u‖ ^ 2 ≠ 0 := by
    rw [pow_two]
    exact mul_ne_zero hu_norm hu_norm
  ext x
  constructor
  · intro hx
    -- The hyperplane equation says that the displacement from the base point has zero inner
    -- product with `u`, so it lies in the kernel direction.
    change x ∈ AffineSubspace.mk' ((η / ‖u‖ ^ 2) • u) ((innerSLFlip ℝ u).ker)
    rw [AffineSubspace.mem_mk', LinearMap.mem_ker]
    calc
      ((innerSLFlip ℝ u) (x - (η / ‖u‖ ^ 2) • u))
          = ⟪x - (η / ‖u‖ ^ 2) • u, u⟫_ℝ := by
              rw [innerSLFlip_apply_apply]
      _ = ⟪x, u⟫_ℝ - (η / ‖u‖ ^ 2) * ⟪u, u⟫_ℝ := by
            rw [inner_sub_left, real_inner_smul_left]
      _ = η - η := by
            rw [mem_innerProductLevelSet_iff.mp hx, real_inner_self_eq_norm_sq]
            field_simp [hu_sq]
      _ = 0 := by
            ring
  · intro hx
    -- Conversely, a kernel displacement means the point has the prescribed inner product with `u`.
    rw [mem_innerProductLevelSet_iff]
    change x ∈ AffineSubspace.mk' ((η / ‖u‖ ^ 2) • u) ((innerSLFlip ℝ u).ker) at hx
    rw [AffineSubspace.mem_mk', LinearMap.mem_ker] at hx
    change ((innerSLFlip ℝ u) (x - (η / ‖u‖ ^ 2) • u)) = 0 at hx
    calc
      ⟪x, u⟫_ℝ
          = ((innerSLFlip ℝ u) (x - (η / ‖u‖ ^ 2) • u)) + (η / ‖u‖ ^ 2) * ⟪u, u⟫_ℝ := by
              rw [innerSLFlip_apply_apply, inner_sub_left, real_inner_smul_left]
              ring
      _ = η := by
            rw [hx, real_inner_self_eq_norm_sq]
            field_simp [hu_sq]
            ring

-- Proof sketch: write `hyperplane u η` as the preimage of the closed singleton `{η}` under the
-- continuous linear functional `x ↦ ⟪x, u⟫_ℝ`.
/-- The hyperplane cut out by a continuous real inner-product functional is closed. -/
theorem hyperplane_isClosed (u : 𝓗) (η : ℝ) :
    IsClosed (innerProductLevelSet u η) := by
  -- The defining equation is the preimage of the closed singleton `{η}` under `innerSLFlip`.
  have h_closed_preimage : IsClosed ((innerSLFlip ℝ u) ⁻¹' ({η} : Set ℝ)) :=
    isClosed_singleton.preimage (innerSLFlip ℝ u).continuous
  simpa [innerProductLevelSet, innerSLFlip_apply_apply] using
    h_closed_preimage

/- The normal correction sends `x` onto `innerProductLevelSet u η`. -/
private lemma corrected_point_mem_hyperplane (u : 𝓗) (η : ℝ) (hu : u ≠ 0) (x : 𝓗) :
    x - ((⟪x, u⟫_ℝ - η) / ‖u‖ ^ 2) • u ∈ innerProductLevelSet u η := by
  have hu_norm : ‖u‖ ≠ 0 := by
    simpa using hu
  have hu_sq : ‖u‖ ^ 2 ≠ 0 := by
    rw [pow_two]
    exact mul_ne_zero hu_norm hu_norm
  -- Compute the inner product of the corrected point with the normal vector.
  rw [mem_innerProductLevelSet_iff]
  calc
    ⟪x - ((⟪x, u⟫_ℝ - η) / ‖u‖ ^ 2) • u, u⟫_ℝ
        = ⟪x, u⟫_ℝ - (((⟪x, u⟫_ℝ - η) / ‖u‖ ^ 2) * ⟪u, u⟫_ℝ) := by
            rw [inner_sub_left, real_inner_smul_left]
    _ = ⟪x, u⟫_ℝ - (((⟪x, u⟫_ℝ - η) / ‖u‖ ^ 2) * (‖u‖ ^ 2)) := by
          rw [real_inner_self_eq_norm_sq]
    _ = ⟪x, u⟫_ℝ - (⟪x, u⟫_ℝ - η) := by
          field_simp [hu_sq]
    _ = η := by
          ring

/-- Helper for Example 3.23: the distance from `x` to its normal correction is the normalized
absolute inner-product defect. -/
private lemma dist_to_corrected_point_eq_abs_inner_sub_div_norm
    (u : 𝓗) (η : ℝ) (hu : u ≠ 0) (x : 𝓗) :
    dist x (x - ((⟪x, u⟫_ℝ - η) / ‖u‖ ^ 2) • u) = |⟪x, u⟫_ℝ - η| / ‖u‖ := by
  have hu_norm : ‖u‖ ≠ 0 := by
    simpa using hu
  -- Collapse the distance to the norm of the correction vector and simplify the scalar factor.
  calc
    dist x (x - ((⟪x, u⟫_ℝ - η) / ‖u‖ ^ 2) • u)
        = ‖((⟪x, u⟫_ℝ - η) / ‖u‖ ^ 2) • u‖ := by
            rw [dist_eq_norm]
            simp
    _ = |(⟪x, u⟫_ℝ - η) / ‖u‖ ^ 2| * ‖u‖ := by
          rw [norm_smul, Real.norm_eq_abs]
    _ = (|⟪x, u⟫_ℝ - η| / (‖u‖ ^ 2)) * ‖u‖ := by
          rw [abs_div, abs_of_nonneg (sq_nonneg ‖u‖)]
    _ = |⟪x, u⟫_ℝ - η| / ‖u‖ := by
          field_simp [pow_two, hu_norm]

/-- Helper for Example 3.23: the orthogonal foot of `x` on `innerProductLevelSet u η` realizes the
distance to that hyperplane. -/
private lemma orthogonal_foot_isBestApproximation_hyperplane
    (u : 𝓗) (η : ℝ) (hu : u ≠ 0) (x : 𝓗) :
    IsBestApproximation x (innerProductLevelSet u η)
      (x - ((⟪x, u⟫_ℝ - η) / ‖u‖ ^ 2) • u) := by
  -- Match the explicit orthogonal foot with the defining best-approximation predicate.
  rw [isBestApproximation_iff_mem_and_dist_eq_infDist]
  refine ⟨corrected_point_mem_hyperplane u η hu x, ?_⟩
  rw [dist_to_corrected_point_eq_abs_inner_sub_div_norm u η hu x,
    infDist_hyperplane_eq_abs_inner_sub_div_norm x u η hu]

variable [CompleteSpace 𝓗]

-- Proof sketch: the hyperplane is nonempty by the explicit point `((η / ‖u‖ ^ 2) • u)`, it is
-- closed by `hyperplane_isClosed`, and it is convex because it is an affine subspace; then apply
-- the Hilbert-space nearest-point theorem for nonempty closed convex sets.
/-- A closed hyperplane in a real Hilbert space is a Chebyshev set. -/
theorem hyperplane_isChebyshev (u : 𝓗) (η : ℝ) (hu : u ≠ 0) :
    IsChebyshev (innerProductLevelSet u η) := by
  have h_nonempty : (innerProductLevelSet u η).Nonempty := by
    refine ⟨((η / ‖u‖ ^ 2) • u), ?_⟩
    rw [innerProductLevelSet_eq_mk'_ker_innerSLFlip u η hu]
    exact AffineSubspace.self_mem_mk' _ _
  have h_convex : Convex ℝ (innerProductLevelSet u η) := by
    rw [innerProductLevelSet_eq_mk'_ker_innerSLFlip u η hu]
    exact (AffineSubspace.mk' ((η / ‖u‖ ^ 2) • u) ((innerSLFlip ℝ u).ker)).convex
  -- The general Hilbert-space projection theorem applies once the hyperplane is seen to be
  -- nonempty, closed, and convex.
  exact isChebyshev_of_nonempty_isClosed_convex h_nonempty (hyperplane_isClosed u η) h_convex

-- Proof sketch: show that the displayed point lies in `hyperplane u η`, and then use uniqueness of
-- best approximations in the Chebyshev set `hyperplane u η` to identify it with the canonical
-- projection point.
/-- Example 3.23: the metric projection of `x` onto the hyperplane
`innerProductLevelSet u η = {z | ⟪z, u⟫_ℝ = η}` is obtained by correcting `x` along the normal
vector `u`. -/
theorem projectionPoint_hyperplane_eq_explicit (u : 𝓗) (η : ℝ) (hu : u ≠ 0) (x : 𝓗) :
    projectionPoint (innerProductLevelSet u η) (hyperplane_isChebyshev u η hu) x =
      x + ((η - ⟪x, u⟫_ℝ) / ‖u‖ ^ 2) • u := by
  let p := x - ((⟪x, u⟫_ℝ - η) / ‖u‖ ^ 2) • u
  have hp_best : IsBestApproximation x (innerProductLevelSet u η) p := by
    -- The source proof’s orthogonal-foot candidate already realizes the distance.
    simpa [p] using orthogonal_foot_isBestApproximation_hyperplane u η hu x
  have hp_proj :
      p = projectionPoint (innerProductLevelSet u η) (hyperplane_isChebyshev u η hu) x := by
    -- Chebyshev uniqueness identifies any best approximation with the canonical projection point.
    exact (hyperplane_isChebyshev u η hu x).unique hp_best
      (projectionPoint_isBestApproximation (innerProductLevelSet u η)
        (hyperplane_isChebyshev u η hu) x)
  have hscalar :
      -((⟪x, u⟫_ℝ - η) / ‖u‖ ^ 2) = (η - ⟪x, u⟫_ℝ) / ‖u‖ ^ 2 := by
    ring
  have hsmul :
      (-((⟪x, u⟫_ℝ - η) / ‖u‖ ^ 2)) • u = ((η - ⟪x, u⟫_ℝ) / ‖u‖ ^ 2) • u := by
    exact congrArg (fun t : ℝ ↦ t • u) hscalar
  -- Rewrite the subtraction-form orthogonal foot into the textbook additive formula.
  calc
    projectionPoint (innerProductLevelSet u η) (hyperplane_isChebyshev u η hu) x = p := hp_proj.symm
    _ = x + ((η - ⟪x, u⟫_ℝ) / ‖u‖ ^ 2) • u := by
      calc
        p = x + (-((⟪x, u⟫_ℝ - η) / ‖u‖ ^ 2)) • u := by
              simp [p, sub_eq_add_neg]
        _ = x + ((η - ⟪x, u⟫_ℝ) / ‖u‖ ^ 2) • u := by
              rw [hsmul]

-- Proof sketch: use that the projection point is a best approximation, so its distance to `x`
-- equals `Metric.infDist x (innerProductLevelSet u η)`, and then apply the hyperplane distance
-- formula `infDist_hyperplane_eq_abs_inner_sub_div_norm`.
/-- The distance from `x` to its projection onto `innerProductLevelSet u η` is the normalized
absolute inner-product defect. -/
theorem dist_projectionPoint_hyperplane_eq_abs_inner_sub_div_norm
    (u : 𝓗) (η : ℝ) (hu : u ≠ 0) (x : 𝓗) :
    dist x (projectionPoint (innerProductLevelSet u η) (hyperplane_isChebyshev u η hu) x) =
      |⟪x, u⟫_ℝ - η| / ‖u‖ := by
  -- The canonical projection distance is exactly the set distance, and Chapter 2 already computed
  -- that set distance for hyperplanes.
  calc
    dist x (projectionPoint (innerProductLevelSet u η) (hyperplane_isChebyshev u η hu) x) =
        Metric.infDist x (innerProductLevelSet u η) :=
      (projectionPoint_isBestApproximation
        (innerProductLevelSet u η) (hyperplane_isChebyshev u η hu) x).2
    _ = |⟪x, u⟫_ℝ - η| / ‖u‖ :=
      infDist_hyperplane_eq_abs_inner_sub_div_norm x u η hu
