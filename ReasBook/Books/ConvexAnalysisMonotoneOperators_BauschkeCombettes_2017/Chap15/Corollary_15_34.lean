/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib.Tactic.Recall
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap02.Fact_2_26

-- Declarations for this item will be appended below by the statement pipeline.

/- Corollary 15.34: for a bounded linear operator `L ∈ 𝓑(𝓗, 𝓚)`, the range of `L` is closed if
and only if the range of its adjoint `L*` is closed. This is exactly the earlier project owner
theorem `ContinuousLinearMap.isClosed_range_iff_isClosed_range_adjoint` from Fact 2.26. -/
recall ContinuousLinearMap.isClosed_range_iff_isClosed_range_adjoint
