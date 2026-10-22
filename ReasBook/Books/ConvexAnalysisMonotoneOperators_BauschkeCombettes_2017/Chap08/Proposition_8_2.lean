/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap01.Definition_1_4

-- Declarations for this item will be appended below by the statement pipeline.

universe u

namespace ERealFunction

variable {H : Type u} [AddCommGroup H] [Module ℝ H]

omit [AddCommGroup H] [Module ℝ H] in
/-- Helper for Proposition 8.2: every point of the effective domain admits a real epigraph
ordinate above it. -/
private lemma exists_mem_epigraph_of_mem_dom (f : H → EReal) {x : H} (hx : x ∈ dom f) :
    ∃ ξ : ℝ, (x, ξ) ∈ epigraph f := by
  -- Convert domain membership into strict finiteness and pick an intermediate real height.
  rw [mem_dom_iff] at hx
  rcases EReal.lt_iff_exists_real_btwn.mp hx with ⟨ξ, hfx_lt_ξ, _⟩
  -- That real height places `(x, ξ)` in the epigraph.
  have hmem : (x, ξ) ∈ epigraph f := by
    rw [mem_epigraph_iff]
    exact le_of_lt hfx_lt_ξ
  exact ⟨ξ, hmem⟩

omit [AddCommGroup H] [Module ℝ H] in
/-- Helper for Proposition 8.2: the base point of a real-height epigraph point lies in the
effective domain. -/
private lemma mem_dom_of_mem_epigraph (f : H → EReal) {x : H} {ξ : ℝ}
    (hξ : (x, ξ) ∈ epigraph f) : x ∈ dom f := by
  -- Epigraph membership bounds `f x` by a finite real height.
  rw [mem_epigraph_iff] at hξ
  -- Hence `f x < ⊤`, which is exactly domain membership.
  rw [mem_dom_iff]
  exact lt_of_le_of_lt hξ (EReal.coe_lt_top ξ)

/-- Helper for Proposition 8.2: the effective domain is the first-coordinate image of the
epigraph. -/
private lemma dom_eq_fst_image_epigraph (f : H → EReal) :
    dom f = (LinearMap.fst ℝ H ℝ) '' epigraph f := by
  ext x
  constructor
  · intro hx
    -- A finite value gives an epigraph point whose projection is the original base point.
    rcases exists_mem_epigraph_of_mem_dom f hx with ⟨ξ, hξ⟩
    refine ⟨(x, ξ), hξ, rfl⟩
  · intro hx
    rcases hx with ⟨p, hp, hp_proj⟩
    rcases p with ⟨y, ξ⟩
    -- Conversely, any projected epigraph point has a finite base value.
    have hy : y ∈ dom f := mem_dom_of_mem_epigraph f hp
    simpa using hp_proj ▸ hy

-- Proof sketch: let `L : H × ℝ →ᵃ[ℝ] H` be the first-coordinate projection. Then
-- `dom f = L '' epigraph f`, and Proposition 3.5 identifies affine images of convex sets as convex.
/-- Proposition 8.2: if an extended-real-valued function on a real vector space has convex
epigraph, then its effective domain `dom f = {x | f x < ⊤}` is a convex subset of the ambient
space. -/
theorem convex_dom_of_convex_epigraph (f : H → EReal) (hconv : Convex ℝ (epigraph f)) :
    Convex ℝ (dom f) := by
  -- Follow the source proof: identify the domain with the first-coordinate image of the epigraph.
  rw [dom_eq_fst_image_epigraph (f := f)]
  -- Convexity is preserved by linear images, so the projection of a convex epigraph is convex.
  simpa using hconv.linear_image (LinearMap.fst ℝ H ℝ)

end ERealFunction
