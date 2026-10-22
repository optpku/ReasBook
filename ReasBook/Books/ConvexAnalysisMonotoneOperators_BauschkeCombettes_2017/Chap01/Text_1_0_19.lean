/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

/-- Text 1.0.19: affine mappings between real vector spaces are the canonical affine maps
`X →ᵃ[ℝ] Y`. -/
theorem affineMap_notation_eq (X : Type u) (Y : Type v) [AddCommGroup X] [Module ℝ X]
    [AddCommGroup Y] [Module ℝ Y] :
    (X →ᵃ[ℝ] Y) = AffineMap ℝ X Y :=
  rfl

variable {X : Type u} {Y : Type v} [AddCommGroup X] [Module ℝ X]
  [AddCommGroup Y] [Module ℝ Y]

namespace AffineMap

/-- An affine map between real vector spaces preserves binary affine combinations. -/
theorem map_affine_combination (T : X →ᵃ[ℝ] Y) (x y : X) (a : ℝ) :
    T (a • x + (1 - a) • y) = a • T x + (1 - a) • T y := by
  simpa [AffineMap.lineMap_apply_module, add_comm, add_left_comm, add_assoc] using
    T.apply_lineMap y x a

end AffineMap
