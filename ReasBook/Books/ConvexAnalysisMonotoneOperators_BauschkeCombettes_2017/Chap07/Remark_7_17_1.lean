/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap06.Definition_6_22

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open scoped InnerProductSpace Pointwise

namespace Set

section

variable {𝓗 : Type u} [NormedAddCommGroup 𝓗] [InnerProductSpace ℝ 𝓗]

/-- Helper for Remark 7.17.1: enlarging a set can only shrink its polar cone. -/
lemma polarCone_subset_of_subset {C D : Set 𝓗} (hCD : C ⊆ D) :
    Dᵒ⊖ ⊆ Cᵒ⊖ := by
  -- Rewrite the polar-cone condition pointwise and restrict along the set inclusion.
  intro u hu
  rw [mem_polarCone_iff_forall_inner_nonpos] at hu ⊢
  intro x hx
  exact hu x (hCD hx)

-- Proof sketch: if `x ∈ K` and `u ∈ Kᵒ⊖`, then the defining inequality for `u ∈ Kᵒ⊖` applied to
-- `x` gives `⟪x, u⟫ ≤ 0`, which is exactly the membership condition for `x ∈ (Kᵒ⊖)ᵒ⊖`.
/-- Remark 7.17.1 (1): every subset, and hence every cone, of a real Hilbert space is contained in
its bipolar cone. -/
theorem subset_polarCone_polarCone (K : Set 𝓗) :
    K ⊆ (Kᵒ⊖)ᵒ⊖ := by
  -- Unfold the target polar membership and test it against an arbitrary element of `Kᵒ⊖`.
  intro x hx
  rw [mem_polarCone_iff_forall_inner_nonpos]
  intro u hu
  rw [mem_polarCone_iff_forall_inner_nonpos] at hu
  -- The defining inequality for `u` at `x` is the required inequality after commuting the inner
  -- product.
  simpa [real_inner_comm] using hu x hx

-- Proof sketch: apply part (1) to `Kᵒ⊖` to obtain `Kᵒ⊖ ⊆ ((Kᵒ⊖)ᵒ⊖)ᵒ⊖`, and use the antitonicity
-- of the polar-cone operation for the reverse inclusion.
/-- Remark 7.17.1 (2): the triple polar cone of a subset equals its polar cone. -/
theorem polarCone_polarCone_polarCone_eq_polarCone (K : Set 𝓗) :
    ((Kᵒ⊖)ᵒ⊖)ᵒ⊖ = Kᵒ⊖ := by
  apply Subset.antisymm
  · -- Antitonicity converts the bipolar inclusion `K ⊆ Kᵒ⊖ᵒ⊖` into the reverse triple-polar
    -- inclusion.
    exact polarCone_subset_of_subset (subset_polarCone_polarCone K)
  · -- The forward inclusion is just part (1) applied to `Kᵒ⊖`.
    exact subset_polarCone_polarCone (Kᵒ⊖)

/-- Helper for Remark 7.17.1: a nonpositive inner-product inequality on `K` extends to
`closure (convexHull ℝ K)`. -/
lemma inner_nonpos_on_closure_convexHull {K : Set 𝓗} {u : 𝓗}
    (hu : ∀ x ∈ K, ⟪x, u⟫_ℝ ≤ 0) :
    ∀ x ∈ closure (convexHull ℝ K), ⟪x, u⟫_ℝ ≤ 0 := by
  -- Use the closed convex halfspace cut out by the linear functional `x ↦ ⟪x,u⟫`.
  let halfspace : Set 𝓗 := {x : 𝓗 | ⟪x, u⟫_ℝ ≤ 0}
  have hK : K ⊆ halfspace := by
    intro x hx
    exact hu x hx
  have hconvex : Convex ℝ halfspace := by
    -- The sublevel set of a linear functional is convex.
    simpa [halfspace, innerSLFlip_apply_apply] using
      (((innerSLFlip ℝ u).toLinearMap.convexOn (convex_univ : Convex ℝ (Set.univ : Set 𝓗))).convex_le
        (0 : ℝ))
  have hclosed : IsClosed halfspace := by
    -- The same halfspace is closed because `x ↦ ⟪x,u⟫` is continuous.
    simpa [halfspace] using
      (isClosed_le (continuous_id.inner continuous_const) continuous_const)
  have hconvexHull : convexHull ℝ K ⊆ halfspace :=
    convexHull_min hK hconvex
  have hclosure : closure (convexHull ℝ K) ⊆ halfspace :=
    closure_minimal hconvexHull hclosed
  -- Membership in the closed convex hull now lands in the halfspace by construction.
  intro x hx
  exact hclosure hx

-- Proof sketch: first pass from `K` to `convexHull ℝ K`, then to `closure (convexHull ℝ K)`,
-- using the standard facts that the polar cone is unchanged by convex hulls and by closure.
/-- Remark 7.17.1 (3): taking the polar cone commutes with passage to the closed convex hull. -/
theorem closure_convexHull_polarCone_eq (K : Set 𝓗) :
    (closure (convexHull ℝ K))ᵒ⊖ = Kᵒ⊖ := by
  apply Subset.antisymm
  · -- Since `K ⊆ closure (convexHull ℝ K)`, antitonicity gives the easy inclusion.
    exact polarCone_subset_of_subset ((subset_convexHull ℝ K).trans subset_closure)
  · intro u hu
    rw [mem_polarCone_iff_forall_inner_nonpos] at hu ⊢
    -- The halfspace transport lemma propagates the defining inequalities from `K` to its closed
    -- convex hull.
    intro x hx
    exact inner_nonpos_on_closure_convexHull hu x hx

end

end Set
