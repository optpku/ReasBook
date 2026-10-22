/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap03.Corollary_3_24
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap04.Proposition_4_31

open SubtypeFirmness

-- Declarations for this item will be appended below by the statement pipeline.

open EuclideanGeometry
open scoped InnerProductSpace
open Function

universe u

section

variable {𝓗 : Type u} [NormedAddCommGroup 𝓗] [InnerProductSpace ℝ 𝓗] [CompleteSpace 𝓗]

private instance (V : ClosedSubmodule ℝ 𝓗) : Nonempty V.toSubmodule.toAffineSubspace := by
  refine ⟨⟨0, ?_⟩⟩
  exact (Submodule.mem_toAffineSubspace).2 (by simp)

private instance (V : ClosedSubmodule ℝ 𝓗) :
    V.toSubmodule.toAffineSubspace.direction.HasOrthogonalProjection := by
  rw [Submodule.toAffineSubspace_direction]
  infer_instance

/-- Helper for Corollary 4.32: the orthogonal projector onto a closed linear subspace is firmly
nonexpansive. -/
private theorem starProjection_isFirmlyNonexpansive
    (V : ClosedSubmodule ℝ 𝓗) : FirmlyNonexpansive V.starProjection := by
  rw [firmlyNonexpansive_iff_norm_sq_le_inner]
  intro x y
  -- Reduce to the standard orthogonal-projection identity on `x - y`.
  have hproj := norm_sq_orthogonalProjection_eq_inner_starProjection V (x - y)
  simpa [map_sub] using hproj.le

/-- Helper for Corollary 4.32: on the affine subspace underlying `V`, the canonical affine
orthogonal projection agrees with the subspace star projection. -/
private theorem coe_orthogonalProjection_toAffineSubspace_eq_starProjection
    (V : ClosedSubmodule ℝ 𝓗) (x : 𝓗) :
    (orthogonalProjection V.toSubmodule.toAffineSubspace x : 𝓗) = V.starProjection x := by
  refine (coe_orthogonalProjection_eq_iff_mem).2 ?_
  constructor
  · exact (Submodule.mem_toAffineSubspace).2
      (Submodule.starProjection_apply_mem V.toSubmodule x)
  · rw [Submodule.toAffineSubspace_direction]
    exact Submodule.sub_starProjection_mem_orthogonal x

-- Proof sketch: apply Proposition 4.31 directly to the orthogonal projector `P_V`. Since
-- `douglasRachfordOperator V.starProjection T₂ x = P_V (2 • T₂ x - x) + x - T₂ x`, the canonical
-- Douglas--Rachford operator is exactly the textbook map
-- `x ↦ P_V (T₂ x) + P_{Vᗮ} (x - T₂ x)`.
/-- Corollary 4.32: if `V` is a closed linear subspace of a real Hilbert space and `T₂` is firmly
nonexpansive, then the Douglas--Rachford operator attached to `P_V` and `T₂`, equivalently the
map `x ↦ P_V (T₂ x) + P_{Vᗮ} (x - T₂ x)`, is firmly nonexpansive and its fixed point set is
`{x | P_V x = T₂ x}`. -/
theorem orthogonal_projector_residual_combination_firmlyNonexpansive_and_fixedPoints
    (V : ClosedSubmodule ℝ 𝓗) {T₂ : 𝓗 → 𝓗}
    (hT₂ : FirmlyNonexpansive T₂) :
    FirmlyNonexpansive (douglasRachfordOperator V.starProjection T₂) ∧
      fixedPoints (douglasRachfordOperator V.starProjection T₂) =
        {x : 𝓗 | V.starProjection x = T₂ x} := by
  have hfirm : FirmlyNonexpansive (douglasRachfordOperator V.starProjection T₂) := by
    exact douglasRachfordOperator_firmlyNonexpansive
      (starProjection_isFirmlyNonexpansive V) hT₂
  have hfix :
      fixedPoints (douglasRachfordOperator V.starProjection T₂) =
        {x : 𝓗 | V.starProjection x = T₂ x} := by
    have hfixA :
        fixedPoints
            (douglasRachfordOperator
              (fun x ↦ (orthogonalProjection V.toSubmodule.toAffineSubspace x : 𝓗)) T₂) =
          {x : 𝓗 | (orthogonalProjection V.toSubmodule.toAffineSubspace x : 𝓗) = T₂ x} :=
      fixedPoints_douglasRachfordOperator_eq_agreement_set_of_affine_projector
    simpa [coe_orthogonalProjection_toAffineSubspace_eq_starProjection] using hfixA
  constructor
  · exact hfirm
  · exact hfix

end
