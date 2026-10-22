/-
Authors: Ze Yuan, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import AlgebraicTopology_May_1999.Chap01.Construction_1_6_3

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open Metric
open scoped ContinuousMap

local notation "D²" => closedBall (0 : ℂ) 1

/-- Theorem 1.6.4: every continuous self-map of the closed unit disk `D²` has a fixed point. -/
-- Proof sketch: argue by contradiction. If `f` had no fixed point, then
-- `fixedPointFreeDiskRetraction` would give a continuous retraction of the disk onto its boundary
-- circle, contradicting `no_continuous_retraction_closed_unit_disk_to_circle`.
theorem brouwer_fixed_point_closed_unit_disk
    (f : C(D², D²)) :
    ∃ x : D², Function.IsFixedPt f x := by
  by_contra hf
  have hf' : ∀ x : D², f x ≠ x := by
    simpa [Function.IsFixedPt] using hf
  exact no_continuous_retraction_closed_unit_disk_to_circle
    ⟨fixedPointFreeDiskRetraction f hf',
      fixedPointFreeDiskRetraction_comp_circleToClosedUnitDisk f hf'⟩
