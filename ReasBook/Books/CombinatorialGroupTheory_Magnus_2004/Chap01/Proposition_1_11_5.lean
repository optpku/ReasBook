/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

namespace Subgroup

section

variable {G : Type u} [Group G]
variable {α : Type v} [Preorder α]

/- Layer triage:
- `source-facing`: a predecessor-ordered family of vertices together with the subgroup attached to
  each vertex, and Proposition `1-11-5` itself in the common-predecessor form used by the proof.
- `core/canonical`: the order on `α`, the subgroup lattice on `Subgroup G`, and the owner
  declarations `Antitone` and `lowerBounds`.
- `bridge/view`: the stronger greatest-lower-bound packaging `IsGLB` is only a corollary view of
  the common-predecessor statement; the source tree language is represented only through the
  antitone labeling `Γ : α → Subgroup G`.

Domain sampling:
1. `ℕ →o Subgroup F` in Proposition `1-3-6` is the chapter's canonical owner shape for ordered
   subgroup families, so a bespoke `DirectedSubgroupTree` wrapper here would duplicate that owner
   level rather than reuse it.
2. `Antitone` from `Mathlib.Order.Monotone.Defs` is the canonical unbundled owner for a
   predecessor-reversing subgroup assignment.
3. `lowerBounds` from `Mathlib.Order.Bounds.Basic` is the canonical owner for common predecessors
   of a finite set of vertices, while `IsGLB` is its stronger greatest-lower-bound refinement.
4. `Subgroup G` already carries the lattice infimum `⊓`, so subgroup intersection is derived API,
   not primitive data of a local tree wrapper.

Primitive vs. derived:
the primitive public data are only the vertex type `α`, its preorder, and the antitone map
`Γ : α → Subgroup G`, together with the two comparison inequalities expressing that `D` is a common
predecessor of `C₁` and `C₂`. Membership in `lowerBounds ({C₁, C₂} : Set α)` and the stronger
`IsGLB ({C₁, C₂} : Set α) D` packaging are derived companion API.
-/

/-- Proposition 1-11-5 in primitive form: any common predecessor of `C₁` and `C₂` receives the
intersection subgroup `Γ C₁ ⊓ Γ C₂`. -/
theorem inf_le_of_common_predecessor {Γ : α → Subgroup G} (hΓ : Antitone Γ)
    {C₁ C₂ D : α} (hDC₁ : D ≤ C₁) (hDC₂ : D ≤ C₂) :
    Γ C₁ ⊓ Γ C₂ ≤ Γ D := by
  simpa using inf_le_inf (hΓ hDC₁) (hΓ hDC₂)

/-- Companion lower-bound reformulation of Proposition `1-11-5`: any common predecessor of `C₁`
and `C₂` forces the intersection subgroup to lie in the subgroup attached to that predecessor. -/
theorem inf_le_of_mem_lowerBounds {Γ : α → Subgroup G} (hΓ : Antitone Γ)
    {C₁ C₂ D : α} (hD : D ∈ lowerBounds ({C₁, C₂} : Set α)) :
    Γ C₁ ⊓ Γ C₂ ≤ Γ D := by
  exact inf_le_of_common_predecessor hΓ (hD <| by simp) (hD <| by simp)

/-- Proposition 1-11-5 in the source phrasing: a greatest common predecessor is in particular a
common predecessor, so the common-predecessor theorem applies directly. -/
theorem inf_le_of_isGLB {Γ : α → Subgroup G} (hΓ : Antitone Γ)
    {C₁ C₂ D : α} (hD : IsGLB ({C₁, C₂} : Set α) D) :
    Γ C₁ ⊓ Γ C₂ ≤ Γ D := by
  exact inf_le_of_mem_lowerBounds hΓ hD.1

end

end Subgroup
