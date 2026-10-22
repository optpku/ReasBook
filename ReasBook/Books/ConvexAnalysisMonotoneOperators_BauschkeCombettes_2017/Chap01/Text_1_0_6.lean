/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

open Set

universe u

variable {X : Type u} [AddCommGroup X] [Module ℝ X]

/- Text 1.0.6 (1): The closed line segment `[x,y]` in a real vector space is mathlib's
`segment ℝ x y`. -/
recall segment

/- Text 1.0.6 (2): The open line segment `]x,y[` in a real vector space is mathlib's
`openSegment ℝ x y`. -/
recall openSegment

/-- Text 1.0.6 (1): The half-open line segment `[x,y[` is the image of the interval
`Set.Ico (0 : ℝ) 1` under the affine line map from `x` to `y`. -/
def closedOpenSegment (x y : X) : Set X :=
  AffineMap.lineMap x y '' Set.Ico (0 : ℝ) 1

/-- Membership in `closedOpenSegment x y` means lying on the affine line from `x` to `y`
with parameter in `[0,1)`. -/
theorem mem_closedOpenSegment_iff {x y z : X} :
    z ∈ closedOpenSegment x y ↔
      ∃ t : ℝ, t ∈ Set.Ico (0 : ℝ) 1 ∧ AffineMap.lineMap x y t = z := by
  simp [closedOpenSegment]

/-- Text 1.0.6 (2): The half-open line segment `]x,y]` is the image of the interval
`Set.Ioc (0 : ℝ) 1` under the affine line map from `x` to `y`. -/
def openClosedSegment (x y : X) : Set X :=
  AffineMap.lineMap x y '' Set.Ioc (0 : ℝ) 1

/-- Membership in `openClosedSegment x y` means lying on the affine line from `x` to `y`
with parameter in `(0,1]`. -/
theorem mem_openClosedSegment_iff {x y z : X} :
    z ∈ openClosedSegment x y ↔
      ∃ t : ℝ, t ∈ Set.Ioc (0 : ℝ) 1 ∧ AffineMap.lineMap x y t = z := by
  simp [openClosedSegment]
