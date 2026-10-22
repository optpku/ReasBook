/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap03.Definition_3_8

-- Declarations for this item will be appended below by the statement pipeline.

universe u

-- Proof sketch: for each `x`, discard the uniqueness part of the Chebyshev hypothesis and keep
-- the realizing best approximation.
/-- Proposition 3.15.1: a Chebyshev set is proximinal. -/
theorem isProximinalIn_of_isChebyshev {X : Type u} [PseudoMetricSpace X] {C : Set X}
    (hC : IsChebyshev C) :
    IsProximinalIn C := by
  intro x
  exact ExistsUnique.exists (hC x)
