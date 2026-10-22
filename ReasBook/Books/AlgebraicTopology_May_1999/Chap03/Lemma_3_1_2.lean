/-
Authors: Ze Yuan, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib.Topology.Connected.LocPathConnected

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open TopologicalSpace

variable {X : Type u} [TopologicalSpace X]

/-- Lemma 3.1.2: a space is locally path connected exactly when its topology admits a basis
consisting of open path-connected sets. -/
-- Proof sketch: if `X` is locally path connected, use the open path-connected neighborhood basis
-- at each point and `IsTopologicalBasis.of_hasBasis_nhds`; conversely, a topological basis of open
-- path-connected sets yields a neighborhood basis of path-connected neighborhoods via
-- `IsTopologicalBasis.nhds_hasBasis`, giving `LocPathConnectedSpace X`.
theorem locPathConnectedSpace_iff_isTopologicalBasis_isOpen_isPathConnected :
    LocPathConnectedSpace X ↔
      IsTopologicalBasis {s : Set X | IsOpen s ∧ IsPathConnected s} where
  mp h := by
    letI : LocPathConnectedSpace X := h
    exact .of_hasBasis_nhds fun x ↦
      (isOpen_isPathConnected_basis x).congr
        (by simp [and_assoc, and_comm])
        (fun _ _ ↦ rfl)
  mpr h :=
    LocPathConnectedSpace.of_bases (fun x ↦ h.nhds_hasBasis) fun _ _ hs ↦ hs.1.2
