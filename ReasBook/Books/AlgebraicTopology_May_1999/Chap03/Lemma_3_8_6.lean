/-
Authors: Ze Yuan, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import AlgebraicTopology_May_1999.Chap03.Definition_3_8_1
import AlgebraicTopology_May_1999.Chap03.Lemma_3_8_5

-- Declarations for this item will be appended below by the statement pipeline.

universe u

variable {B : Type u} [TopologicalSpace B]

section

variable [LocPathConnectedSpace B] [SemilocallySimplyConnectedSpace B]

/- The owner fact behind Lemma 3.8.6 (2): the path-class space is locally path connected. -/
-- Proof sketch: the standard basic neighborhoods from Construction 3.8.3 are indexed by suitable
-- open neighborhoods in `B`. By Lemma 3.8.5, each such basic neighborhood is identified with its
-- indexing neighborhood, which is path connected by definition, so these basic sets form a
-- path-connected neighborhood basis on the total space.
instance instLocPathConnectedSpace_universalCoverCandidate (b : B) :
    LocPathConnectedSpace (universalCoverCandidate b) := by
  sorry

/- The owner fact behind Lemma 3.8.6 (3): the path-class space is simply connected. -/
-- Proof sketch: a loop in the total space based at the class of the constant path projects to a
-- loop in `B`. The endpoint-fixed path-class construction identifies the endpoint of the lifted
-- loop with the resulting path class in `B`, so a loop can close only when that class is trivial.
-- This makes every based loop null-homotopic, hence the total space is simply connected.
instance instSimplyConnectedSpace_universalCoverCandidate (b : B) :
    SimplyConnectedSpace (universalCoverCandidate b) := by
  sorry

end

/-- Lemma 3.8.6 (1): the path-class space constructed over the basepoint `b` is connected. -/
theorem universalCoverCandidate_connectedSpace
    (b : B) [LocPathConnectedSpace B] [SemilocallySimplyConnectedSpace B] :
    ConnectedSpace (universalCoverCandidate b) :=
  inferInstance

/-- Lemma 3.8.6 (2): the path-class space constructed over the basepoint `b` is locally path
connected. -/
theorem universalCoverCandidate_locPathConnectedSpace
    (b : B) [LocPathConnectedSpace B] [SemilocallySimplyConnectedSpace B] :
    LocPathConnectedSpace (universalCoverCandidate b) :=
  inferInstance

/-- Lemma 3.8.6 (3): the path-class space constructed over the basepoint `b` is simply connected.
-/
theorem universalCoverCandidate_simplyConnectedSpace
    (b : B) [LocPathConnectedSpace B] [SemilocallySimplyConnectedSpace B] :
    SimplyConnectedSpace (universalCoverCandidate b) :=
  inferInstance
