/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

/- Example 2.1: the Hilbert direct sum of a family of real Hilbert spaces is formalized by the
canonical `ℓ²` space `lp H 2` of square-summable dependent families. -/
recall lp

/- In the Hilbert direct sum `lp H 2`, the inner product is the coordinatewise series
`⟪x, y⟫ = ∑' i, ⟪x i, y i⟫`. -/
recall lp.inner_eq_tsum

/- The textbook net of finite partial sums is formalized by the canonical predicate `HasSum`,
whose default summation filter is unconditional convergence over finite subsets. -/
recall HasSum

/- The existence of such a sum is formalized by the canonical predicate `Summable`. -/
recall Summable
