/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.
open Filter Topology

universe u

/- The canonical interior operator in a topological space is `interior`. -/
recall interior {X : Type u} [TopologicalSpace X] (C : Set X) : Set X

/- A point belongs to `interior C` exactly when `C` is a neighborhood of that point. -/
#check mem_interior_iff_mem_nhds

/-- Text 1.0.38: equivalently, a point lies in `interior C` exactly when `C` contains a
neighborhood of that point. -/
theorem mem_interior_iff_exists_mem_nhds_subset {X : Type u} [TopologicalSpace X] {x : X}
    {C : Set X} : x ∈ interior C ↔ ∃ V : Set X, V ∈ 𝓝 x ∧ V ⊆ C := by
  rw [mem_interior_iff_mem_nhds]
  constructor
  · intro hC
    exact ⟨C, hC, fun _ hx ↦ hx⟩
  · rintro ⟨V, hV, hVC⟩
    exact Filter.mem_of_superset hV hVC
