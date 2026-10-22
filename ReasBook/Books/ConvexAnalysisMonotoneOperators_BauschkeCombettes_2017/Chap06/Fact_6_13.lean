/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap06.Proposition_6_12

-- Declarations for this item will be appended below by the statement pipeline.

open Set Topology
open scoped Pointwise

universe u

namespace Proposition612Absorbent

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

-- Proof sketch: the cited external corollary says that a surjective continuous linear image of a
-- closed convex set in a Hilbert space has interior equal to core.  Apply it to the closed convex
-- product `C ×ˢ D` under the continuous linear map `(x, y) ↦ x - y`.
/-- External dependency for Fact 6.13, corresponding to Corollary 13.2 of the cited source: a
surjective continuous linear image of a closed convex subset of a Hilbert space has interior equal
to core. -/
theorem interior_image_eq_core_image_of_isClosed_of_convex_of_surjective
    {E F : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
    (L : E →L[ℝ] F) (hL : Function.Surjective L) {C : Set E}
    (hC_closed : IsClosed C) (hC_convex : Convex ℝ C) :
    interior (L '' C) = Set.core (L '' C) := sorry

/-- Fact 6.13: for closed convex subsets `C` and `D` of a real Hilbert space, the interior of the
difference set `C - D` coincides with its core. -/
theorem interior_sub_eq_core_sub_of_isClosed_of_convex {C D : Set H} (hC_closed : IsClosed C)
    (hD_closed : IsClosed D) (hC_convex : Convex ℝ C) (hD_convex : Convex ℝ D) :
    interior (C - D) = Set.core (C - D) := by
  let L : H × H →L[ℝ] H := (ContinuousLinearMap.fst ℝ H H) - (ContinuousLinearMap.snd ℝ H H)
  have hL_surj : Function.Surjective L := by
    intro z
    refine ⟨(z, 0), ?_⟩
    simp [L]
  have hprod_closed : IsClosed (C ×ˢ D : Set (H × H)) := hC_closed.prod hD_closed
  have hprod_convex : Convex ℝ (C ×ˢ D : Set (H × H)) := hC_convex.prod hD_convex
  have himage : L '' (C ×ˢ D : Set (H × H)) = C - D := by
    ext z
    constructor
    · rintro ⟨p, hp, rfl⟩
      exact Set.mem_sub.mpr ⟨p.1, hp.1, p.2, hp.2, by simp [L]⟩
    · intro hz
      rcases Set.mem_sub.mp hz with ⟨c, hc, d, hd, hz_eq⟩
      refine ⟨(c, d), ⟨hc, hd⟩, ?_⟩
      simpa [L] using hz_eq
  simpa [himage] using
    (interior_image_eq_core_image_of_isClosed_of_convex_of_surjective
      (L := L) hL_surj hprod_closed hprod_convex)

end Proposition612Absorbent
