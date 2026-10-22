/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

variable {X : Type u} {Y : Type v}

/-- Text 1.0.15: the image `T(C)` of a subset `C ⊆ X` under a single-valued map `T : X → Y`
is the canonical set-theoretic construction `Set.image T C`. -/
-- Proof sketch: this is definitional, since the notation `T '' C` expands to `Set.image T C`.
theorem image_eq_set_image (T : X → Y) (C : Set X) :
    T '' C = Set.image T C := rfl

/-- The preimage `T⁻¹(D)` of a subset `D ⊆ Y` under a map `T : X → Y` is the set
`Set.preimage T D`. -/
-- Proof sketch: this is definitional, since the notation `T ⁻¹' D` expands to
-- `Set.preimage T D`.
theorem preimage_eq_set_preimage (T : X → Y) (D : Set Y) :
    T ⁻¹' D = Set.preimage T D := rfl
