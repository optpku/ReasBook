/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap02.Text_2_0_14
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap02.Lemma_2_41
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap03.Corollary_3_22

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open EuclideanGeometry
open scoped InnerProductSpace

variable {𝓗 : Type u} [NormedAddCommGroup 𝓗] [InnerProductSpace ℝ 𝓗] [CompleteSpace 𝓗]

section

variable {C : AffineSubspace ℝ 𝓗}
variable (hC_nonempty : (C : Set 𝓗).Nonempty) (hC_closed : IsClosed (C : Set 𝓗))

local notation "P" =>
  @projectionPoint 𝓗 inferInstance (C : Set 𝓗)
    (isChebyshev_of_nonempty_isClosed_convex hC_nonempty hC_closed C.convex)

private lemma projectionPoint_difference_inner_residual_eq_zero (x y : 𝓗) :
    ⟪P x - P y, x - P x⟫_ℝ = 0 ∧ ⟪P x - P y, y - P y⟫_ℝ = 0 := by
  letI : Nonempty C := nonempty_subtype.mpr hC_nonempty
  have hdir_closed : IsClosed (C.direction : Set 𝓗) :=
    (AffineSubspace.isClosed_direction_iff C).mpr hC_closed
  letI : IsClosed (C.direction : Set 𝓗) := hdir_closed
  letI : CompleteSpace C.direction := IsClosed.completeSpace_coe
  letI : C.direction.HasOrthogonalProjection := by
    infer_instance
  have hx_mem : P x ∈ (C : Set 𝓗) := by
    exact
      projectionPoint_mem (C : Set 𝓗)
        (isChebyshev_of_nonempty_isClosed_convex hC_nonempty hC_closed C.convex) x
  have hy_mem : P y ∈ (C : Set 𝓗) := by
    exact
      projectionPoint_mem (C : Set 𝓗)
        (isChebyshev_of_nonempty_isClosed_convex hC_nonempty hC_closed C.convex) y
  have hdir : P x - P y ∈ C.direction := by
    simpa [vsub_eq_sub] using C.vsub_mem_direction hx_mem hy_mem
  have hx_orth : x - P x ∈ C.directionᗮ := by
    have hEq : x - P x = x -ᵥ (orthogonalProjection C x : C) := by
      simpa [vsub_eq_sub] using congrArg (fun z : 𝓗 ↦ x - z)
        (projectionPoint_eq_orthogonalProjection_of_nonempty_isClosed_affineSubspace
          hC_nonempty hC_closed x)
    rw [hEq]
    exact vsub_orthogonalProjection_mem_direction_orthogonal C x
  have hy_orth : y - P y ∈ C.directionᗮ := by
    have hEq : y - P y = y -ᵥ (orthogonalProjection C y : C) := by
      simpa [vsub_eq_sub] using congrArg (fun z : 𝓗 ↦ y - z)
        (projectionPoint_eq_orthogonalProjection_of_nonempty_isClosed_affineSubspace
          hC_nonempty hC_closed y)
    rw [hEq]
    exact vsub_orthogonalProjection_mem_direction_orthogonal C y
  constructor
  · exact Submodule.inner_right_of_mem_orthogonal hdir hx_orth
  · exact Submodule.inner_right_of_mem_orthogonal hdir hy_orth

-- Proof sketch: `Corollary 3.22 (2)` shows that the metric projector onto a nonempty closed affine
-- subspace is affine. Package that projector as a continuous affine self-map of `𝓗`, then apply
-- `Lemma 2.41` to obtain continuity from the weak topology to itself.
/-- Proposition 4.19 (1): for a nonempty closed affine subspace of a real Hilbert space, the
metric projector `P` is weakly continuous on the ambient space. -/
theorem projectionPoint_weaklyContinuous_of_nonempty_isClosed_affineSubspace :
    WeaklyContinuous (fun x : (Set.univ : Set 𝓗) ↦ P x) := by
  letI : Nonempty C := nonempty_subtype.mpr hC_nonempty
  have hdir_closed : IsClosed (C.direction : Set 𝓗) :=
    (AffineSubspace.isClosed_direction_iff C).mpr hC_closed
  letI : IsClosed (C.direction : Set 𝓗) := hdir_closed
  letI : CompleteSpace C.direction := IsClosed.completeSpace_coe
  letI : C.direction.HasOrthogonalProjection := by
    infer_instance
  let T : 𝓗 →ᴬ[ℝ] 𝓗 :=
    C.subtypeA.comp (EuclideanGeometry.orthogonalProjection C)
  have hweak :
      Continuous fun x : WeakSpace ℝ 𝓗 ↦
        toWeakSpace ℝ 𝓗 (P ((toWeakSpace ℝ 𝓗).symm x)) := by
    have hT_eq : (T : 𝓗 → 𝓗) = P := by
      funext x
      simpa [T] using
        (projectionPoint_eq_orthogonalProjection_of_nonempty_isClosed_affineSubspace
          hC_nonempty hC_closed x).symm
    have hbase :
        Continuous fun x : WeakSpace ℝ 𝓗 ↦
          toWeakSpace ℝ 𝓗 (T ((toWeakSpace ℝ 𝓗).symm x)) := by
      exact continuousAffineMap_continuous_toWeakSpace T
    refine Continuous.congr hbase ?_
    intro x
    rw [hT_eq]
  unfold WeaklyContinuous
  letI : TopologicalSpace {x : 𝓗 // x ∈ Set.univ} :=
    TopologicalSpace.induced
      (fun x : {x : 𝓗 // x ∈ Set.univ} ↦ toWeakSpace ℝ 𝓗 x) inferInstance
  simpa using hweak.comp continuous_induced_dom

-- Proof sketch: apply the firm nonexpansiveness inequality from Proposition 4.16 to the affine
-- subspace `C`. Then use Corollary 3.22 (1) to show that the residual vectors `x - P x` and
-- `y - P y` are both orthogonal to `P x - P y`; expanding
-- `⟪x - y, P x - P y⟫ = ⟪(x - P x) - (y - P y), P x - P y⟫ + ‖P x - P y‖^2`
-- makes the orthogonal term vanish and upgrades the inequality to an equality.
/-- Proposition 4.19 (2): for a nonempty closed affine subspace of a real Hilbert space, the
squared distance between two projection points equals the inner product of the original difference
with the difference of the projection points. -/
theorem norm_sq_projectionPoint_sub_eq_inner_sub_projectionPoint_sub_of_nonempty_isClosed_affineSubspace
    (x y : 𝓗) :
    ‖P x - P y‖ ^ (2 : ℕ) = ⟪x - y, P x - P y⟫_ℝ := by
  have hzero :
      ⟪P x - P y, x - P x⟫_ℝ = 0 ∧ ⟪P x - P y, y - P y⟫_ℝ = 0 := by
    exact
      projectionPoint_difference_inner_residual_eq_zero
        hC_nonempty hC_closed x y
  have hdecomp : x - y = (x - P x) + (P x - P y) - (y - P y) := by
    abel_nf
  have hinner :
      ⟪P x - P y, x - y⟫_ℝ = ‖P x - P y‖ ^ (2 : ℕ) := by
    calc
      ⟪P x - P y, x - y⟫_ℝ
          = ⟪P x - P y, (x - P x) + (P x - P y) - (y - P y)⟫_ℝ := by
              rw [hdecomp]
      _ = ⟪P x - P y, (x - P x) + (P x - P y)⟫_ℝ - ⟪P x - P y, y - P y⟫_ℝ := by
            rw [inner_sub_right]
      _ = ⟪P x - P y, x - P x⟫_ℝ + ⟪P x - P y, P x - P y⟫_ℝ - ⟪P x - P y, y - P y⟫_ℝ := by
            rw [inner_add_right]
      _ = ‖P x - P y‖ ^ (2 : ℕ) := by
            rw [hzero.1, hzero.2, zero_add, sub_zero, real_inner_self_eq_norm_sq]
  calc
    ‖P x - P y‖ ^ (2 : ℕ) = ⟪P x - P y, x - y⟫_ℝ := by
      exact hinner.symm
    _ = ⟪x - y, P x - P y⟫_ℝ := by
      rw [real_inner_comm]

end
