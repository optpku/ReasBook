/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open Set

namespace EReal

/-- Text 1.0.27: the extended interval `]ξ, +∞]` is the usual real interval `]ξ, +∞[`,
embedded into `EReal`, with the point `+∞` adjoined. -/
theorem openClosedUpperInfiniteInterval_eq_image_Ioi_union_top (ξ : ℝ) :
    Ioi (ξ : EReal) = Real.toEReal '' Ioi ξ ∪ ({(⊤ : EReal)} : Set EReal) := by
  rw [image_coe_Ioi]
  ext x
  simp [lt_top_iff_ne_top]

end EReal
