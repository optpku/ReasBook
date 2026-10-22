/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap04.Proposition_4_4
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap04.Proposition_4_16

open SubtypeFirmness

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open scoped InnerProductSpace

section

variable {𝓗 : Type u} [NormedAddCommGroup 𝓗] [InnerProductSpace ℝ 𝓗] [CompleteSpace 𝓗]
variable {C : Set 𝓗}
variable (hC_nonempty : C.Nonempty) (hC_closed : IsClosed C) (hC_convex : Convex ℝ C)

/-- The canonical metric projection onto `C`, viewed as a map on the subtype `Set.univ`. -/
local notation "P" =>
  fun x : Set.univ ↦
    projectionPoint C
      (isChebyshev_of_nonempty_isClosed_convex hC_nonempty hC_closed hC_convex) (x : 𝓗)

/-- Corollary 4.18: if `P` is the canonical metric projection onto a nonempty closed convex subset
`C` of a real Hilbert space, then its residual map `Id - P` is firmly nonexpansive and its
reflector `2P - Id` is nonexpansive. -/
theorem metricProjection_residual_firmlyNonexpansive_and_reflection_nonexpansive
    : FirmlyNonexpansiveOn (Set.univ : Set 𝓗) (residualMap (Set.univ : Set 𝓗) P) ∧
      LipschitzWith 1 (reflectedMap (Set.univ : Set 𝓗) P) := by
  have hP : FirmlyNonexpansiveOn (Set.univ : Set 𝓗) P := by
    rw [firmlyNonexpansiveOn_iff]
    intro x y
    rw [real_inner_comm]
    exact
      norm_sq_projectionPoint_sub_le_inner_projectionPoint_sub_of_nonempty_isClosed_convex
        hC_nonempty hC_closed hC_convex (x : 𝓗) (y : 𝓗)
  have hresidual :
      FirmlyNonexpansiveOn (Set.univ : Set 𝓗) (residualMap (Set.univ : Set 𝓗) P) := by
    exact (firmlyNonexpansiveOn_residualMap_iff (Set.univ : Set 𝓗) P).2 hP
  have hreflect :
      ∀ x y : Set.univ,
        ‖reflectedMap (Set.univ : Set 𝓗) P x - reflectedMap (Set.univ : Set 𝓗) P y‖ ≤
          ‖(x : 𝓗) - y‖ := by
    exact
      (reflectedMap_nonexpansive_iff_firmlyNonexpansiveOn (Set.univ : Set 𝓗) P).2 hP
  refine ⟨hresidual, ?_⟩
  -- Repackage the reflected-map pointwise inequality as a `1`-Lipschitz bound on `Set.univ`.
  refine LipschitzWith.of_dist_le_mul fun x y ↦ ?_
  simpa [Subtype.dist_eq, dist_eq_norm] using hreflect x y

end
