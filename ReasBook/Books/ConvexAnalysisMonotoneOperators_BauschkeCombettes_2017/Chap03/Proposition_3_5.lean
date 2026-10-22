/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

variable {E : Type u} {F : Type v}
variable [AddCommGroup E] [Module ℝ E]
variable [AddCommGroup F] [Module ℝ F]

/- Proposition 3.5, image clause: the image of a convex set under an affine map is convex,
canonically formalized by `Convex.affine_image`. -/
recall Convex.affine_image

/- Proposition 3.5, preimage clause: the preimage of a convex set under an affine map is convex,
canonically formalized by `Convex.affine_preimage`. -/
recall Convex.affine_preimage

/-- Proposition 3.5: the image of a convex set under an affine map is convex, and the preimage of
a convex set under an affine map is convex. -/
theorem affine_image_and_preimage_convex (T : E →ᵃ[ℝ] F) (C : Set E) (D : Set F)
    (hC : Convex ℝ C) (hD : Convex ℝ D) :
    Convex ℝ (T '' C) ∧ Convex ℝ (T ⁻¹' D) := by
  exact ⟨hC.affine_image T, hD.affine_preimage T⟩
