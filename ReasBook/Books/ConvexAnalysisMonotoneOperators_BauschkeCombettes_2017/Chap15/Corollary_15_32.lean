/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap06.Proposition_6_44
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap15.Corollary_15_31

-- Declarations for this item will be appended below by the statement pipeline.

open scoped InnerProductSpace Pointwise

universe u v

namespace Set

section

variable {H : Type u} {K : Type v}
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable [NormedAddCommGroup K] [InnerProductSpace ℝ K] [CompleteSpace K]

variable (D : Set K) (L : H →L[ℝ] K)

-- Proof sketch: specialize Corollary 15.31(2) to `C = univ`, rewrite `L '' univ` as `Set.range L`,
-- and simplify the added term `univᵒ⊖` to `{0}` so the pointwise sum collapses to the adjoint
-- image alone.
/-- Corollary 15.32: if `D` is a closed convex cone and `D - Set.range L` is a closed
linear subspace, then the polar cone of `L ⁻¹' D` is exactly the adjoint image of the polar cone
of `D`. -/
theorem polarCone_preimage_eq_adjoint_image_polarCone_of_closed_subspace_sub_range
    (hD_closed : IsClosed D) (hD_convex : Convex ℝ D) (hD_cone : IsCone D)
    (hsubspace : D - Set.range L = (Submodule.span ℝ (D - Set.range L) : Set K))
    (hsubspace_closed : IsClosed (D - Set.range L)) :
    (L ⁻¹' D)ᵒ⊖ = L.adjoint '' (Dᵒ⊖) := by
  have huniv_cone : IsCone (Set.univ : Set H) := by
    change (Set.univ : Set H) = (Set.Ioi (0 : ℝ) : Set ℝ) • (Set.univ : Set H)
    ext x
    constructor
    · intro _
      refine ⟨1, by norm_num, x, by simp, by simp⟩
    · rintro ⟨a, ha, y, -, rfl⟩
      simp
  calc
    (L ⁻¹' D)ᵒ⊖ = ((Set.univ : Set H) ∩ L ⁻¹' D)ᵒ⊖ := by simp
    _ = (Set.univ : Set H)ᵒ⊖ + L.adjoint '' (Dᵒ⊖) := by
      simpa [Set.image_univ] using
        polarCone_inter_preimage_eq_add_adjoint_image_polarCone_of_closed_subspace_sub_image
          (Set.univ : Set H) D L
          isClosed_univ convex_univ huniv_cone hD_closed hD_convex hD_cone
          (by simpa [Set.image_univ] using hsubspace)
          (by simpa [Set.image_univ] using hsubspace_closed)
    _ = ({0} : Set H) + L.adjoint '' (Dᵒ⊖) := by
      rw [Set.polarCone_univ_eq_singleton_zero]
    _ = L.adjoint '' (Dᵒ⊖) := by
      ext x
      simp

end

end Set
