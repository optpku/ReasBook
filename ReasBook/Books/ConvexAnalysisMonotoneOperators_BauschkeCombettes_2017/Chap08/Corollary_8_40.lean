/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u

-- Proof sketch: apply the finite-dimensional continuity theorem for convex functions on `Set.univ`,
-- for instance by first obtaining local Lipschitz continuity from `ConvexOn.locallyLipschitz` and
-- then deducing continuity from `LocallyLipschitz.continuous`.
/-- Corollary 8.40: every convex real-valued function on a finite-dimensional real Hilbert space is
continuous. -/
theorem continuous_of_convexOn_univ
    {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [FiniteDimensional ℝ H]
    (f : H → ℝ) (hconv : ConvexOn ℝ Set.univ f) :
    Continuous f := by
  -- Finite-dimensional convexity gives the local Lipschitz control that underlies the textbook
  -- continuity argument.
  have hloc : LocallyLipschitz f := hconv.locallyLipschitz
  -- A locally Lipschitz map is continuous.
  exact hloc.continuous
