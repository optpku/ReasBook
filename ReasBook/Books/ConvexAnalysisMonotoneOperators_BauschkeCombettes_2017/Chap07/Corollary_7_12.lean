/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open scoped InnerProductSpace

variable {𝓗 : Type u} [NormedAddCommGroup 𝓗] [InnerProductSpace ℝ 𝓗] [CompleteSpace 𝓗]

-- Proof sketch: if `x ∉ C`, then the geometric Hahn-Banach theorem gives a continuous linear
-- functional that is strictly smaller on `C` than at `x`. The Riesz representation theorem turns
-- that functional into an inner-product normal vector, producing a closed halfspace that contains
-- `C` but excludes `x`.
/-- Helper for Corollary 7.12: a point outside a closed convex set is excluded by some real closed
halfspace that still contains the set. -/
lemma exists_closedHalfspace_separating_of_not_mem_of_isClosed_of_convex
    {C : Set 𝓗} (hC_closed : IsClosed C) (hC_convex : Convex ℝ C) {x : 𝓗} (hx : x ∉ C) :
    ∃ u : 𝓗, ∃ η : ℝ,
      C ⊆ {y : 𝓗 | ⟪y, u⟫_ℝ ≤ η} ∧ x ∉ {y : 𝓗 | ⟪y, u⟫_ℝ ≤ η} := by
  -- Separate `x` from `C` by a continuous linear functional and rewrite it as an inner product.
  obtain ⟨f, η, hC_lt, hx_lt⟩ := geometric_hahn_banach_closed_point hC_convex hC_closed hx
  let u : 𝓗 := (InnerProductSpace.toDual ℝ 𝓗).symm f
  refine ⟨u, η, ?_, ?_⟩
  · intro y hyC
    have hy_le : f y ≤ η := (hC_lt y hyC).le
    have hy_inner : ⟪u, y⟫_ℝ ≤ η := by
      simpa [u] using hy_le
    simpa [real_inner_comm] using hy_inner
  · intro hx_mem
    have hx_le : f x ≤ η := by
      have hx_inner : ⟪u, x⟫_ℝ ≤ η := by
        simpa [real_inner_comm] using hx_mem
      simpa [u] using hx_inner
    exact (not_le_of_gt hx_lt) hx_le

/-- Corollary 7.12: a closed convex subset `C` of a real Hilbert space is the intersection of all
closed half-spaces containing it, encoded here as the sets `{x | ⟪x, u⟫_ℝ ≤ η}` that contain
`C`. -/
theorem eq_iInter_closed_halfspaces_of_isClosed_of_convex {C : Set 𝓗} (hC_closed : IsClosed C)
    (hC_convex : Convex ℝ C) :
    C = ⋂ (u : 𝓗) (η : ℝ) (_ : C ⊆ {x : 𝓗 | ⟪x, u⟫_ℝ ≤ η}),
      {x : 𝓗 | ⟪x, u⟫_ℝ ≤ η} := by
  ext x
  constructor
  · intro hxC
    rw [Set.mem_iInter]
    intro u
    rw [Set.mem_iInter]
    intro η
    rw [Set.mem_iInter]
    intro hCη
    -- Every indexed halfspace on the right already contains `C` by assumption.
    exact hCη hxC
  · intro hx
    by_contra hxC
    rcases exists_closedHalfspace_separating_of_not_mem_of_isClosed_of_convex
        hC_closed hC_convex hxC with ⟨u, η, hCη, hxη⟩
    have hxη' : x ∈ {y : 𝓗 | ⟪y, u⟫_ℝ ≤ η} := by
      exact (Set.mem_iInter.mp (Set.mem_iInter.mp (Set.mem_iInter.mp hx u) η) hCη)
    exact hxη hxη'
