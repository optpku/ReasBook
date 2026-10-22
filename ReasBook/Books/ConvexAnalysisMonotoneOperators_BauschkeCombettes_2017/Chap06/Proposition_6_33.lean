/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap06.Definition_6_9
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap06.Definition_6_22
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap06.Proposition_6_24
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap06.Proposition_6_28
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap06.Proposition_6_32

-- Declarations for this item will be appended below by the statement pipeline.

open scoped InnerProductSpace Pointwise

universe u

namespace Set

section

variable {𝓗 : Type u} [NormedAddCommGroup 𝓗] [InnerProductSpace ℝ 𝓗] [CompleteSpace 𝓗]

/-- Helper for Proposition 6.33: package `closure (cone C)` as a proper cone so that the
projection results from Propositions 6.28 and 6.32 apply to it. -/
abbrev closure_cone_properCone (C : Set 𝓗) (hC_nonempty : C.Nonempty) : ProperCone ℝ 𝓗 :=
  let K : ConvexCone ℝ 𝓗 := (ConvexCone.hull ℝ C).closure
  let hK_nonempty : (K : Set 𝓗).Nonempty := by
    rcases hC_nonempty with ⟨x, hx⟩
    refine ⟨x, ?_⟩
    -- Start from `x ∈ C`, move into the convex-cone hull, and then into its closure.
    simpa [Set.cone_def, ConvexCone.coe_closure] using
      (subset_closure (ConvexCone.subset_hull (R := ℝ) (s := C) hx))
  let hK_closed : IsClosed (K : Set 𝓗) := by
    -- The carrier of `K` is literally the closure of the convex-cone hull.
    change IsClosed (closure ((ConvexCone.hull ℝ C : Set 𝓗)))
    exact isClosed_closure
  ⟨K.toPointedCone <| ConvexCone.Pointed.of_nonempty_of_isClosed hK_nonempty hK_closed, hK_closed⟩

omit [CompleteSpace 𝓗] in
/-- Helper for Proposition 6.33: the proper cone built from `closure (cone C)` has exactly that
carrier. -/
lemma closure_cone_properCone_coe (C : Set 𝓗) (hC_nonempty : C.Nonempty) :
    ((closure_cone_properCone C hC_nonempty : ProperCone ℝ 𝓗) : Set 𝓗) = closure (cone C) := by
  let K : ConvexCone ℝ 𝓗 := (ConvexCone.hull ℝ C).closure
  have hK_nonempty : (K : Set 𝓗).Nonempty := by
    rcases hC_nonempty with ⟨x, hx⟩
    refine ⟨x, ?_⟩
    -- The closure of the cone hull still contains every point of `C`.
    simpa [K, Set.cone_def, ConvexCone.coe_closure] using
      (subset_closure (ConvexCone.subset_hull (R := ℝ) (s := C) hx))
  have hK_closed : IsClosed (K : Set 𝓗) := by
    -- `K` was defined as the closure of the cone hull.
    change IsClosed (closure ((ConvexCone.hull ℝ C : Set 𝓗)))
    exact isClosed_closure
  -- Reduce the bundled proper cone to its carrier and then unfold the cone notation.
  change (K : Set 𝓗) = closure (cone C)
  simp [K, Set.cone_def]

/-- Helper for Proposition 6.33: taking the polar cone commutes with replacing `C` by
`closure (cone C)`. -/
lemma polarCone_closure_cone_eq (C : Set 𝓗) :
    (closure (cone C))ᵒ⊖ = Cᵒ⊖ := by
  -- Rewrite each polar cone as the negative polar from Proposition 6.24, then use invariance under
  -- `closure` and `cone`.
  calc
    (closure (cone C))ᵒ⊖ = Set.negativePolar (closure (cone C)) := by
      simpa [Set.negativePolar] using Set.polarCone_eq_innerDual_neg (closure (cone C))
    _ = Set.negativePolar (cone C) := Set.negativePolar_closure_eq (cone C)
    _ = Set.negativePolar C := Set.negativePolar_cone_eq C
    _ = Cᵒ⊖ := by
      simpa [Set.negativePolar] using (Set.polarCone_eq_innerDual_neg C).symm

/-- Helper for Proposition 6.33: every point of `closure (cone C)` belongs to the bipolar of
`C`. -/
lemma closure_cone_subset_polarCone_polarCone (C : Set 𝓗) :
    closure (cone C) ⊆ (Cᵒ⊖)ᵒ⊖ := by
  intro x hx
  rw [Set.mem_polarCone_iff_forall_inner_nonpos]
  intro y hy
  have hy_closedCone : y ∈ (closure (cone C))ᵒ⊖ := by
    rwa [polarCone_closure_cone_eq C]
  -- Evaluate the polar inequality at `x ∈ closure (cone C)` and commute the inner product.
  have hxy : ⟪x, y⟫_ℝ ≤ 0 :=
    (Set.mem_polarCone_iff_forall_inner_nonpos.mp hy_closedCone) x hx
  simpa [real_inner_comm] using hxy

/-- Helper for Proposition 6.33: a point in the bipolar of `C` already lies in `closure (cone C)`.
-/
lemma mem_closure_cone_of_mem_polarCone_polarCone {C : Set 𝓗}
    (hC_nonempty : C.Nonempty) {x : 𝓗} (hx : x ∈ (Cᵒ⊖)ᵒ⊖) :
    x ∈ closure (cone C) := by
  let K : ProperCone ℝ 𝓗 := closure_cone_properCone C hC_nonempty
  let p : 𝓗 := projectionPoint (K : Set 𝓗) (properConeProjectionChebyshev K) x
  have hK_carrier : (K : Set 𝓗) = closure (cone C) := by
    simpa [K] using closure_cone_properCone_coe C hC_nonempty
  have hresidual_K : x - p ∈ (K : Set 𝓗)ᵒ⊖ := by
    -- Proposition 6.28 puts the projection residual in the polar cone of the closed cone `K`.
    simpa [p] using
      (sub_mem_polarCone_of_eq_projectionPoint_on_properCone K
        (p := p) (x := x) rfl)
  have hresidual_C : x - p ∈ Cᵒ⊖ := by
    -- Replace the polar cone of `K` by the original polar cone of `C`.
    rw [← polarCone_closure_cone_eq C]
    simpa [hK_carrier] using hresidual_K
  have hinner_residual : ⟪x - p, x⟫_ℝ ≤ 0 :=
    (Set.mem_polarCone_iff_forall_inner_nonpos.mp hx) (x - p) hresidual_C
  have hinner_projection : ⟪x, x - p⟫_ℝ ≤ 0 := by
    -- Proposition 6.32 expects the inner product in the opposite order.
    simpa [real_inner_comm] using hinner_residual
  have hxK : x ∈ K := by
    -- Proposition 6.32 now identifies `x` with a point of the proper cone `K`.
    simpa [p] using
      (mem_of_inner_sub_projectionPoint_nonpos_of_properCone
        (K := K) x hinner_projection)
  -- Rewrite the carrier of `K` back to `closure (cone C)`.
  have hxK' : x ∈ (K : Set 𝓗) := hxK
  rw [hK_carrier] at hxK'
  exact hxK'

-- Proof sketch: replace `C` by the nonempty closed convex cone `closure (cone C)`, whose polar
-- cone agrees with `Cᵒ⊖` by Proposition 6.24. Then apply the bipolar theorem for proper cones to
-- `closure (cone C)`. Equivalently, for the reverse inclusion, project onto `closure (cone C)` and
-- use Propositions 6.28 and 6.32 as in the textbook proof.
/-- Proposition 6.33: for a nonempty convex subset `C` of a real Hilbert space, the double polar
cone of `C` is the closure of the cone generated by `C`. -/
theorem polarCone_polarCone_eq_closure_cone_of_nonempty_convex {C : Set 𝓗}
    (hC_nonempty : C.Nonempty) (hC_convex : Convex ℝ C) :
    (Cᵒ⊖)ᵒ⊖ = closure (cone C) := by
  -- Route correction: the source proof works by projecting onto `closure (cone C)`, not by trying
  -- to manipulate the bipolar directly as a recursive cone construction.
  let _ := hC_convex
  have hforward : closure (cone C) ⊆ (Cᵒ⊖)ᵒ⊖ :=
    closure_cone_subset_polarCone_polarCone C
  have hreverse : (Cᵒ⊖)ᵒ⊖ ⊆ closure (cone C) := by
    intro x hx
    -- The reverse inclusion is exactly the projection argument from the textbook proof.
    exact mem_closure_cone_of_mem_polarCone_polarCone hC_nonempty hx
  -- The two inclusions identify the bipolar with the closed cone generated by `C`.
  exact Subset.antisymm hreverse hforward

end

end Set
