/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

namespace TopologicalSpace

variable {X₁ : Type u} [TopologicalSpace X₁]
variable {X₂ : Type v} [TopologicalSpace X₂]

/-- Text 1.0.41: if `B₁` and `B₂` are bases for the given topologies on `X₁` and `X₂`, then the
family of rectangles `U ×ˢ V` with `U ∈ B₁` and `V ∈ B₂` is a basis for the product topology on
`X₁ × X₂`. This is the textbook set-builder form of the canonical theorem
`TopologicalSpace.IsTopologicalBasis.prod`. -/
theorem IsTopologicalBasis.rectangles {B₁ : Set (Set X₁)} {B₂ : Set (Set X₂)}
    (h₁ : IsTopologicalBasis B₁) (h₂ : IsTopologicalBasis B₂) :
    IsTopologicalBasis {s : Set (X₁ × X₂) | ∃ U ∈ B₁, ∃ V ∈ B₂, s = U ×ˢ V} := by
  have hrect :
      Set.image2 (· ×ˢ ·) B₁ B₂ =
        {s : Set (X₁ × X₂) | ∃ U ∈ B₁, ∃ V ∈ B₂, s = U ×ˢ V} := by
    ext s
    simp [Set.mem_image2, eq_comm]
  rw [← hrect]
  exact h₁.prod h₂

end TopologicalSpace
