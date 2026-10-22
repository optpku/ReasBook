/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

/- Corollary 6.34: the bipolar theorem for a nonempty closed convex cone in a real Hilbert space is
canonically formalized by `ProperCone.innerDual_innerDual`, stating that a proper cone equals its
double inner dual. -/
recall ProperCone.innerDual_innerDual
