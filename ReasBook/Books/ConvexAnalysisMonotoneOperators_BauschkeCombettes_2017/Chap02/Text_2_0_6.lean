/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

/- Text 2.0.6: for real normed vector spaces `X` and `Y`, the textbook space
`\mathcal{B}(\mathcal{X},\mathcal{Y})` of bounded linear maps is formalized by the canonical
mathlib type `ContinuousLinearMap`, written `X →L[ℝ] Y`; in particular,
`\mathcal{B}(\mathcal{X})` is `X →L[ℝ] X`, and its operator norm is the ambient norm on this
space. -/
recall ContinuousLinearMap

/- The operator norm is exactly the supremum of `‖T x‖` over the closed unit ball, matching the
textbook definition. -/
recall ContinuousLinearMap.sSup_unitClosedBall_eq_norm
