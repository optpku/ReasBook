/-
Authors: Ze Yuan, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import AlgebraicTopology_May_1999.Chap02.Proposition_2_4_6

-- Declarations for this item will be appended below by the statement pipeline.

universe u

variable {X : Type u} [TopologicalSpace X] [ContractibleSpace X]

/-- Corollary 2.4.7: a contractible space has trivial fundamental group at every basepoint. -/
-- Proof sketch: use the homotopy equivalence from a contractible space to `Unit`, transport the
-- fundamental group along Proposition 2.4.6, and then use that the point has trivial
-- fundamental group.
theorem fundamentalGroup_subsingleton_of_contractible (x : X) :
    Subsingleton (FundamentalGroup X x) := by
  -- Use the canonical homotopy equivalence from a contractible space to the point.
  obtain ⟨e⟩ := ContractibleSpace.hequiv_unit X
  -- Transport the fundamental group at `x` across the homotopy equivalence.
  let h := fundamentalGroupMulEquivOfHomotopyEquiv e x
  -- The point is simply connected, so its fundamental group is trivial.
  let _ : Subsingleton (FundamentalGroup Unit (e x)) := by
    let _ : SimplyConnectedSpace Unit := inferInstance
    change Subsingleton (Path.Homotopic.Quotient (e x) (e x))
    infer_instance
  -- Pull the subsingleton structure back along the induced equivalence.
  exact h.injective.subsingleton
