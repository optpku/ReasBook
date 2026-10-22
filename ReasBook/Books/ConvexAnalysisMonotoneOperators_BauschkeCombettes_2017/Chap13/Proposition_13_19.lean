/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap12.Definition_12_20_Core
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap13.Definition_13_1

-- Declarations for this item will be appended below by the statement pipeline.

open scoped InnerProductSpace

universe u

namespace ERealFunction

section Conjugation

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

-- Proof sketch: one direction is Example 13.6, which identifies the conjugate of the quadratic
-- `x ↦ ‖x‖² / 2` with itself. For the converse, apply the Fenchel--Young inequality to `f` at
-- `(x, x)` to get the lower bound `‖x‖² / 2 ≤ f x`, then use the order-reversing property of
-- conjugation from Proposition 13.16 together with `f = f∗` to force the reverse inequality.
/-- Proposition 13.19: an extended-real-valued function on a real inner-product space is
self-conjugate exactly when it is the canonical quadratic owner `halfSquaredNorm.asEReal`. -/
theorem self_conjugate_iff_eq_half_squared_norm
    (f : H → EReal) :
    f = f∗ ↔
      f = halfSquaredNorm.asEReal := sorry

end Conjugation

end ERealFunction
