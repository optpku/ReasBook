/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap03.Theorem_3_16_2

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open EuclideanGeometry
open scoped InnerProductSpace

variable {𝓗 : Type u} [NormedAddCommGroup 𝓗] [InnerProductSpace ℝ 𝓗] [CompleteSpace 𝓗]

section

variable {C : AffineSubspace ℝ 𝓗}
variable (hC_nonempty : (C : Set 𝓗).Nonempty) (hC_closed : IsClosed (C : Set 𝓗))

local notation "P" =>
  projectionPoint (C : Set 𝓗)
    (isChebyshev_of_nonempty_isClosed_convex hC_nonempty hC_closed C.convex)

omit [CompleteSpace 𝓗] in
/-- Helper for Corollary 3.22: for a point `p ∈ C`, orthogonality of `x - p` to the direction
space is equivalent to orthogonality to every difference `y - z` with `y, z ∈ C`. -/
private lemma sub_mem_direction_orthogonal_iff {x p : 𝓗} (hp : p ∈ (C : Set 𝓗)) :
    x - p ∈ C.directionᗮ ↔
      ∀ y ∈ (C : Set 𝓗), ∀ z ∈ (C : Set 𝓗), ⟪y - z, x - p⟫_ℝ = 0 := by
  constructor
  · intro hx y hy z hz
    exact Submodule.inner_right_of_mem_orthogonal
      (by simpa [vsub_eq_sub] using C.vsub_mem_direction hy hz)
      hx
  · intro hx
    exact (C.direction.mem_orthogonal (x - p)).2 fun v hv ↦ by
      rcases (C.mem_direction_iff_eq_vsub_right hp v).mp hv with ⟨y, hy, rfl⟩
      simpa [vsub_eq_sub] using hx y hy p hp

/-- Helper for Corollary 3.22: on a nonempty closed affine subspace, the Chebyshev projection
coincides with the canonical affine orthogonal projection from mathlib. -/
theorem projectionPoint_eq_orthogonalProjection_of_nonempty_isClosed_affineSubspace
    [Nonempty C] [C.direction.HasOrthogonalProjection] (x : 𝓗) :
    P x = (orthogonalProjection C x : 𝓗) := by
  have hCheb : IsChebyshev (C : Set 𝓗) :=
    isChebyshev_of_nonempty_isClosed_convex hC_nonempty hC_closed C.convex
  have hproj_best : IsBestApproximation x (C : Set 𝓗) (P x) := by
    simpa using projectionPoint_isBestApproximation (C : Set 𝓗) hCheb x
  have horth_best :
      IsBestApproximation x (C : Set 𝓗) (orthogonalProjection C x : 𝓗) := by
    refine ⟨by
      change ((orthogonalProjection C x : C) : 𝓗) ∈ C
      exact orthogonalProjection_mem x, ?_⟩
    simpa using dist_orthogonalProjection_eq_infDist C x
  exact ExistsUnique.unique (hCheb x) hproj_best horth_best

-- Proof sketch: identify the metric projector with `orthogonalProjection C`, use the canonical
-- characterization `q = orthogonalProjection C x ↔ q ∈ C ∧ x - q ∈ C.directionᗮ`, and rewrite
-- membership in `C.directionᗮ` as orthogonality to all differences `y - z` with `y, z ∈ C`.
/-- Corollary 3.22 (1): for a nonempty closed affine subspace of a real Hilbert space, a point is
the metric projection of `x` exactly when it lies in the affine subspace and the residual `x - p`
is orthogonal to every direction `y - z` with `y, z ∈ C`. -/
theorem eq_projectionPoint_iff_mem_and_inner_sub_eq_zero_of_nonempty_isClosed_affineSubspace
    {x p : 𝓗} :
    p = P x ↔
      p ∈ (C : Set 𝓗) ∧
        ∀ y ∈ (C : Set 𝓗), ∀ z ∈ (C : Set 𝓗), ⟪y - z, x - p⟫_ℝ = 0 := by
  letI : Nonempty C := nonempty_subtype.mpr hC_nonempty
  have hdir_closed : IsClosed (C.direction : Set 𝓗) :=
    (AffineSubspace.isClosed_direction_iff C).mpr hC_closed
  letI : IsClosed (C.direction : Set 𝓗) := hdir_closed
  letI : CompleteSpace C.direction := IsClosed.completeSpace_coe
  letI : C.direction.HasOrthogonalProjection := by
    infer_instance
  calc
    p = P x ↔ p = (orthogonalProjection C x : 𝓗) := by
      rw [projectionPoint_eq_orthogonalProjection_of_nonempty_isClosed_affineSubspace
        hC_nonempty hC_closed]
    _ ↔ p ∈ (C : Set 𝓗) ∧ x - p ∈ C.directionᗮ := by
      simpa [eq_comm, vsub_eq_sub] using
        (coe_orthogonalProjection_eq_iff_mem :
          (orthogonalProjection C x : 𝓗) = p ↔ p ∈ (C : Set 𝓗) ∧ x - p ∈ C.directionᗮ)
    _ ↔ p ∈ (C : Set 𝓗) ∧
          ∀ y ∈ (C : Set 𝓗), ∀ z ∈ (C : Set 𝓗), ⟪y - z, x - p⟫_ℝ = 0 := by
      constructor
      · rintro ⟨hp, hx⟩
        exact ⟨hp, (sub_mem_direction_orthogonal_iff hp).mp hx⟩
      · rintro ⟨hp, hx⟩
        exact ⟨hp, (sub_mem_direction_orthogonal_iff hp).mpr hx⟩

-- Proof sketch: replace the metric projector by the canonical affine map
-- `orthogonalProjection C`, use that continuous affine maps commute with `AffineMap.lineMap`, and
-- translate back.
/-- Corollary 3.22 (2): the metric projection onto a nonempty closed affine subspace is an affine
operator. -/
theorem projectionPoint_lineMap_of_nonempty_isClosed_affineSubspace
    (x₁ x₂ : 𝓗) (t : ℝ) :
    P ((1 - t) • x₁ + t • x₂) = (1 - t) • P x₁ + t • P x₂ := by
  letI : Nonempty C := nonempty_subtype.mpr hC_nonempty
  have hdir_closed : IsClosed (C.direction : Set 𝓗) :=
    (AffineSubspace.isClosed_direction_iff C).mpr hC_closed
  letI : IsClosed (C.direction : Set 𝓗) := hdir_closed
  letI : CompleteSpace C.direction := IsClosed.completeSpace_coe
  letI : C.direction.HasOrthogonalProjection := by
    infer_instance
  calc
    P ((1 - t) • x₁ + t • x₂) = (orthogonalProjection C ((1 - t) • x₁ + t • x₂) : 𝓗) := by
      rw [projectionPoint_eq_orthogonalProjection_of_nonempty_isClosed_affineSubspace
        hC_nonempty hC_closed]
    _ =
        ((AffineMap.lineMap
            (orthogonalProjection C x₁)
            (orthogonalProjection C x₂)
            t : C) : 𝓗) := by
      have hline :
          orthogonalProjection C ((1 - t) • x₁ + t • x₂) =
            AffineMap.lineMap (orthogonalProjection C x₁) (orthogonalProjection C x₂) t := by
        simpa [AffineMap.lineMap_apply_module] using
          (orthogonalProjection C).apply_lineMap x₁ x₂ t
      exact congrArg Subtype.val hline
    _ = AffineMap.lineMap (orthogonalProjection C x₁ : 𝓗) (orthogonalProjection C x₂ : 𝓗) t := by
      rfl
    _ = (1 - t) • (orthogonalProjection C x₁ : 𝓗) + t • (orthogonalProjection C x₂ : 𝓗) := by
      simp [AffineMap.lineMap_apply_module]
    _ = (1 - t) • P x₁ + t • P x₂ := by
      rw [projectionPoint_eq_orthogonalProjection_of_nonempty_isClosed_affineSubspace
          hC_nonempty hC_closed,
        projectionPoint_eq_orthogonalProjection_of_nonempty_isClosed_affineSubspace
          hC_nonempty hC_closed]

end
