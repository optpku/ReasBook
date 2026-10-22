/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap01.Text_1_0_6

universe u

open Set

variable {X : Type u} [AddCommGroup X] [Module ℝ X]

/-- Text 1.0.7: the half-open segment `]x,y]` coincides with the half-open segment `[y,x[`. -/
-- Proof sketch: rewrite both sides as images of `AffineMap.lineMap` on `Ioc 0 1` and `Ico 0 1`,
-- then use the change of variables `s = 1 - t` together with `AffineMap.lineMap_apply_one_sub`.
theorem text_1_0_7 (x y : X) :
    openClosedSegment x y = closedOpenSegment y x := by
  ext z
  constructor
  · intro hz
    rcases mem_openClosedSegment_iff.mp hz with ⟨t, ht, htz⟩
    -- Reverse the parameter by sending `t` to `1 - t`.
    refine mem_closedOpenSegment_iff.mpr ?_
    refine ⟨1 - t, ?_, ?_⟩
    · simpa using (Set.sub_mem_Ico_zero_iff_right : 1 - t ∈ Set.Ico (0 : ℝ) 1 ↔
        t ∈ Set.Ioc (0 : ℝ) 1).2 ht
    -- Reversing the endpoints of the line map matches the textbook identity.
    exact (AffineMap.lineMap_apply_one_sub y x t).trans htz
  · intro hz
    rcases mem_closedOpenSegment_iff.mp hz with ⟨s, hs, hsz⟩
    -- Apply the inverse parameter change `s ↦ 1 - s`.
    refine mem_openClosedSegment_iff.mpr ?_
    refine ⟨1 - s, ?_, ?_⟩
    · simpa using (Set.sub_mem_Ioc_zero_iff_right : 1 - s ∈ Set.Ioc (0 : ℝ) 1 ↔
        s ∈ Set.Ico (0 : ℝ) 1).2 hs
    -- The same line-map symmetry gives the converse inclusion.
    exact (AffineMap.lineMap_apply_one_sub x y s).trans hsz
