/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

open Filter

variable {A : Type u} [Preorder A] [IsDirectedOrder A] [Nonempty A]
variable {X : Type v} [TopologicalSpace X]

/-- Text 1.0.44: a net `ξ` converges to `x` exactly when it is eventually contained in every
neighborhood of `x`; in mathlib this convergence is expressed by `Tendsto ξ atTop (nhds x)`. -/
-- Proof sketch: this is the canonical specialization of `tendsto_iff_forall_eventually_mem`
-- to the target filter `nhds x`, together with the tail characterization of `atTop`.
theorem tendsto_atTop_nhds_iff_forall_exists_forall_ge_mem (ξ : A → X) (x : X) :
    Tendsto ξ atTop (nhds x) ↔
      ∀ V ∈ nhds x, ∃ b, ∀ a ≥ b, ξ a ∈ V := by
  rw [tendsto_iff_forall_eventually_mem]
  constructor
  · intro h V hV
    exact eventually_atTop.mp (h V hV)
  · intro h V hV
    exact eventually_atTop.mpr (h V hV)
