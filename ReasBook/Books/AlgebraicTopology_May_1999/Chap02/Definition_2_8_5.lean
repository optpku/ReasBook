/-
Authors: Ze Yuan, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u

/- Definition 2.8.5: a topological space is simply connected when it is path connected and its
fundamental group is trivial; the canonical mathlib owner for this notion is
`SimplyConnectedSpace`. -/
recall SimplyConnectedSpace (X : Type u) [TopologicalSpace X] : Prop

variable {X : Type u} [TopologicalSpace X]

/-- A simply connected space is path connected and has trivial fundamental group at every
basepoint. -/
theorem simplyConnectedSpace_iff_pathConnectedSpace_and_subsingleton_fundamentalGroup :
    SimplyConnectedSpace X ↔
      PathConnectedSpace X ∧ ∀ x : X, Subsingleton (FundamentalGroup X x) := by
  constructor
  · intro hX
    let _ : SimplyConnectedSpace X := hX
    refine ⟨inferInstance, fun x ↦ ?_⟩
    change Subsingleton (Path.Homotopic.Quotient x x)
    infer_instance
  · intro hX
    rcases hX with ⟨hPath, hπ₁⟩
    let _ : PathConnectedSpace X := hPath
    rw [simply_connected_iff_loops_nullhomotopic]
    refine ⟨hPath, fun x γ ↦ ?_⟩
    have hsub : Subsingleton (Path.Homotopic.Quotient x x) := by
      simpa using hπ₁ x
    exact Quotient.exact (@Subsingleton.elim (Path.Homotopic.Quotient x x) hsub ⟦γ⟧ ⟦Path.refl x⟧)
