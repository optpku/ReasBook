/-
Authors: Ze Yuan, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open Metric

local notation "D²" => closedBall (0 : ℂ) 1

/-- Helper for Lemma 1.6.1: the closed unit disk `D²` is simply connected. -/
theorem closed_unit_disk_simplyConnected : SimplyConnectedSpace D² := by
  letI : ContractibleSpace D² :=
    contractibleSpace_closedBall zero_le_one
  exact SimplyConnectedSpace.ofContractible D²

/-- Lemma 1.6.1: the fundamental group of the closed unit disk `D²` is trivial at any basepoint. -/
-- Proof sketch: use the canonical chain
-- `contractibleSpace_closedBall -> SimplyConnectedSpace.ofContractible`; then identify
-- `FundamentalGroup D² x` with the quotient of loops at `x` up to homotopy.
theorem fundamental_group_closed_unit_disk_subsingleton (x : D²) :
    Subsingleton (FundamentalGroup D² x) := by
  letI : SimplyConnectedSpace D² := closed_unit_disk_simplyConnected
  change Subsingleton (Path.Homotopic.Quotient x x)
  infer_instance

/-- Every element of the fundamental group of the closed unit disk is the identity. -/
-- Proof sketch: apply the subsingleton statement for the fundamental group at the chosen
-- basepoint and compare any loop class with the unit element.
theorem fundamental_group_closed_unit_disk_eq_one (x : D²) (γ : FundamentalGroup D² x) :
    γ = 1 := by
  letI : Subsingleton (FundamentalGroup D² x) :=
    fundamental_group_closed_unit_disk_subsingleton x
  exact Subsingleton.elim _ _
