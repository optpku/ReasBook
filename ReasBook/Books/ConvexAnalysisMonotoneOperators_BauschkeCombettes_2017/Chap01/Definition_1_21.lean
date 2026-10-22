/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

/- Definition 1.21: for an extended-real-valued function `f : X → EReal`, lower semicontinuity
at a point `x` is the canonical predicate `LowerSemicontinuousAt f x`, and lower semicontinuity
on `X` is the canonical predicate `LowerSemicontinuous f`. -/
recall LowerSemicontinuousAt

/- Companion recall: the textbook liminf inequality along every convergent net is expressed in
mathlib by the neighborhood-filter characterization `lowerSemicontinuousAt_iff_le_liminf`. -/
recall lowerSemicontinuousAt_iff_le_liminf

/- Companion recall: lower semicontinuity on the whole space is the canonical predicate
`LowerSemicontinuous f`. -/
recall LowerSemicontinuous

/- Companion recall: global lower semicontinuity is exactly pointwise lower semicontinuity. -/
recall lowerSemicontinuous_iff
