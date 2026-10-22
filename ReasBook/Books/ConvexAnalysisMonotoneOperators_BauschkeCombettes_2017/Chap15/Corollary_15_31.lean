/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap01.Text_1_0_2
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap06.Definition_6_22

-- Declarations for this item will be appended below by the statement pipeline.

open scoped InnerProductSpace Pointwise

universe u v

namespace Set

section

variable {H : Type u} {K : Type v}
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable [NormedAddCommGroup K] [InnerProductSpace ℝ K] [CompleteSpace K]

-- Proof sketch: apply Proposition 6.35 to the closed convex cones `C` and `L ⁻¹' D`. The
-- preimage cone is again nonempty, closed, convex, and a cone because both cones contain `0`.
-- Then identify `(L ⁻¹' D)ᵒ⊖` with `closure (L.adjoint '' (Dᵒ⊖))` via Theorem 6.37(1), and absorb
-- the extra closure inside the outer closure of the sum.
/-- Corollary 15.31 (1): the polar cone of `C ∩ L ⁻¹' D` is the closure of the sum of the polar
cone of `C` and the adjoint image of the polar cone of `D`. -/
theorem polarCone_inter_preimage_eq_closure_add_adjoint_image_polarCone
    (C : Set H) (D : Set K) (L : H →L[ℝ] K)
    (hC_nonempty : C.Nonempty) (hC_closed : IsClosed C)
    (hC_convex : Convex ℝ C) (hC_cone : IsCone C)
    (hD_nonempty : D.Nonempty) (hD_closed : IsClosed D)
    (hD_convex : Convex ℝ D) (hD_cone : IsCone D) :
    (C ∩ L ⁻¹' D)ᵒ⊖ = closure (Cᵒ⊖ + L.adjoint '' (Dᵒ⊖)) := sorry

-- Proof sketch: use Proposition 6.19 to turn the closed-linear-subspace hypothesis on
-- `D - L '' C` into `0 ∈ sri (D - L '' C)`. Apply Example 13.3(ii) and Theorem 15.27 to the
-- indicator functions of `C` and `D`, then rewrite the resulting exact infimal-convolution formula
-- as the displayed equality of polar cones.
/-- Corollary 15.31 (2): if `D - L '' C` is a closed linear subspace, then the closure in part
`(1)` is unnecessary. -/
theorem polarCone_inter_preimage_eq_add_adjoint_image_polarCone_of_closed_subspace_sub_image
    (C : Set H) (D : Set K) (L : H →L[ℝ] K)
    (hC_closed : IsClosed C) (hC_convex : Convex ℝ C) (hC_cone : IsCone C)
    (hD_closed : IsClosed D) (hD_convex : Convex ℝ D) (hD_cone : IsCone D)
    (hsubspace :
      D - L '' C = (Submodule.span ℝ (D - L '' C) : Set K))
    (hsubspace_closed : IsClosed (D - L '' C)) :
    (C ∩ L ⁻¹' D)ᵒ⊖ = Cᵒ⊖ + L.adjoint '' (Dᵒ⊖) := sorry

-- Proof sketch: both polar cones contain `0`, and the adjoint sends `0` to `0`, so the pointwise
-- sum also contains `0`.
/-- Corollary 15.31 (3): the sum `Cᵒ⊖ + L.adjoint '' (Dᵒ⊖)` is nonempty. -/
theorem nonempty_add_adjoint_image_polarCone
    (C : Set H) (D : Set K) (L : H →L[ℝ] K) :
    (Cᵒ⊖ + L.adjoint '' (Dᵒ⊖)).Nonempty := sorry

-- Proof sketch: combine clause `(2)` with Proposition 6.24(ii), which says that every polar cone
-- is closed.
/-- Corollary 15.31 (4): under the closed-linear-subspace hypothesis, the sum
`Cᵒ⊖ + L.adjoint '' (Dᵒ⊖)` is closed. -/
theorem isClosed_add_adjoint_image_polarCone_of_closed_subspace_sub_image
    (C : Set H) (D : Set K) (L : H →L[ℝ] K)
    (hC_closed : IsClosed C) (hC_convex : Convex ℝ C) (hC_cone : IsCone C)
    (hD_closed : IsClosed D) (hD_convex : Convex ℝ D) (hD_cone : IsCone D)
    (hsubspace :
      D - L '' C = (Submodule.span ℝ (D - L '' C) : Set K))
    (hsubspace_closed : IsClosed (D - L '' C)) :
    IsClosed (Cᵒ⊖ + L.adjoint '' (Dᵒ⊖)) := sorry

-- Proof sketch: Proposition 6.24(ii) makes each polar cone convex, continuous linear maps preserve
-- convexity, and pointwise sums of convex sets are convex.
/-- Corollary 15.31 (5): the sum `Cᵒ⊖ + L.adjoint '' (Dᵒ⊖)` is convex. -/
theorem convex_add_adjoint_image_polarCone
    (C : Set H) (D : Set K) (L : H →L[ℝ] K) :
    Convex ℝ (Cᵒ⊖ + L.adjoint '' (Dᵒ⊖)) := sorry

-- Proof sketch: Proposition 6.24(ii) makes each polar cone a cone, the adjoint image of a cone is
-- again a cone, and the pointwise sum of two cones is a cone.
/-- Corollary 15.31 (6): the sum `Cᵒ⊖ + L.adjoint '' (Dᵒ⊖)` is a cone. -/
theorem isCone_add_adjoint_image_polarCone
    (C : Set H) (D : Set K) (L : H →L[ℝ] K) :
    IsCone (Cᵒ⊖ + L.adjoint '' (Dᵒ⊖)) := sorry

end

end Set
