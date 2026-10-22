/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap06.Definition_6_9

-- Declarations for this item will be appended below by the statement pipeline.

open Set
open scoped Pointwise

-- Proof sketch: compute the explicit difference sets in `ℝ²`. For the axis example, the
-- difference is all of `ℝ²`, so clause (iii) holds, while the horizontal axis has empty interior,
-- which is the finite-dimensional set-level rendering of clause (iv) via Corollary 8.39. For the
-- segment example, the difference set is the horizontal segment `[-1,1] × {0}`, whose origin lies
-- in its strong relative interior and whose relative interior is nonempty, while the core
-- condition fails.
/-- Remark 15.6: the regularity conditions in Proposition 15.5 are not equivalent. In `ℝ²`, for
the domain pair `ℝ × {0}` and `{0} × ℝ`, the finite-dimensional set-level form of clause (iv),
namely `interior C ∩ D ≠ ∅`, fails while clause (iii) holds. For the pair
`[0,1] × {0}` and `[0,1] × {0}`, clause (ii) fails while `(15.9)` and clause (v) hold. -/
theorem attouchBrezisRegularityConditions_not_equivalent :
    let horizontalAxis : Set (ℝ × ℝ) := (Set.univ : Set ℝ) ×ˢ ({0} : Set ℝ)
    let verticalAxis : Set (ℝ × ℝ) := ({0} : Set ℝ) ×ˢ (Set.univ : Set ℝ)
    let segment : Set (ℝ × ℝ) := Set.Icc (0 : ℝ) 1 ×ˢ ({0} : Set ℝ)
    (¬ (interior horizontalAxis ∩ verticalAxis).Nonempty ∧
      (0 : ℝ × ℝ) ∈ interior (horizontalAxis - verticalAxis)) ∧
      (¬ ((0 : ℝ × ℝ) ∈ core (segment - segment)) ∧
        (0 : ℝ × ℝ) ∈ sri (segment - segment) ∧
        (ri segment ∩ ri segment).Nonempty) := sorry
