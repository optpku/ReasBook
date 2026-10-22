/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

universe u

namespace TopologicalSpace

variable {X : Type u} [TopologicalSpace X]

/-
Text 1.0.37: if `B` is a basis for the topology on `X`, then every open set is the union of the
basis sets contained in it. This is the canonical theorem
`TopologicalSpace.IsTopologicalBasis.open_eq_sUnion'`.
-/
recall IsTopologicalBasis.open_eq_sUnion'

/-- Text 1.0.37 in the textbook's unpacked basis hypotheses. -/
theorem open_eq_sUnion_basis_subsets {B : Set (Set X)} (hB_open : ∀ V ∈ B, IsOpen V)
    (hB_basis : ∀ x (U : Set X), x ∈ U → IsOpen U → ∃ V ∈ B, x ∈ V ∧ V ⊆ U)
    {U : Set X} (hU : IsOpen U) :
    U = ⋃₀ {V ∈ B | V ⊆ U} := by
  simpa using (isTopologicalBasis_of_isOpen_of_nhds hB_open hB_basis).open_eq_sUnion' hU

end TopologicalSpace
