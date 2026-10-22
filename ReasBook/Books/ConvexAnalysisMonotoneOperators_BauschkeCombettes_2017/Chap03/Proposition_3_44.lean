/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap01.Text_1_0_6

-- Declarations for this item will be appended below by the statement pipeline.

open Set AffineMap

universe u

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Proposition 3.44, pointwise form: if `C` is convex, `x ∈ interior C`, `y ∈ closure C`, and
`t ∈ [0,1)`, then the point `lineMap x y t` lies in `interior C`. -/
theorem lineMap_mem_interior_of_mem_Ico_of_mem_interior_of_mem_closure {C : Set E}
    (hC : Convex ℝ C) {x y : E} (hx : x ∈ interior C) (hy : y ∈ closure C)
    {t : ℝ} (ht : t ∈ Ico (0 : ℝ) 1) :
    lineMap x y t ∈ interior C := by
  rcases ht with ⟨ht0, ht1⟩
  simpa [lineMap_apply_module] using
    hC.combo_interior_closure_mem_interior hx hy
      (sub_pos.mpr ht1) ht0 (sub_add_cancel 1 t)

/-- Proposition 3.44: if `C` is convex, `x ∈ interior C`, and `y ∈ closure C`, then the half-open
segment `[x,y[` is contained in `interior C`. -/
theorem closedOpenSegment_subset_interior_of_mem_interior_of_mem_closure {C : Set E}
    (hC : Convex ℝ C) {x y : E} (hx : x ∈ interior C) (hy : y ∈ closure C) :
    closedOpenSegment x y ⊆ interior C := by
  intro z hz
  rcases mem_closedOpenSegment_iff.mp hz with ⟨t, ht, rfl⟩
  exact lineMap_mem_interior_of_mem_Ico_of_mem_interior_of_mem_closure hC hx hy ht
