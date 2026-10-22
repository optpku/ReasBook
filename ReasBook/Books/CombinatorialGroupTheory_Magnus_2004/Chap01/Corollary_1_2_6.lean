/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import CombinatorialGroupTheory_Magnus_2004.Chap01.Proposition_1_2_5

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open FreeGroup
open scoped Pointwise Symmetrization

section

variable {X : Type u} [DecidableEq X]

namespace FreeGroup.IsNReduced

variable {U : Set (FreeGroup X)}

/-- Corollary 1-2-6: If `U` satisfies `(N0)` through `(N2)`, then any product
`w = u₁ ... u_t` with letters in `U^{±1}` and no adjacent inverse cancellation has reduced length
at least `t`. -/
-- Layer triage:
-- `source-facing`: this lower bound for reduced products.
-- `core/canonical`: the owner abstraction `FreeGroup.IsNReduced`.
-- `bridge/view`: the derived prefix/middle-segment API
-- `FreeGroup.IsNReduced.exists_prefix_middle_segments`.
-- Primitive hypotheses are only the Nielsen-reduced owner datum `hU`, the factor-membership
-- condition `hwU`, and the no-cancellation chain `hchain`; the displayed norm bound is derived
-- API.
theorem norm_list_prod_ge_length
    (hU : IsNReduced U)
    (w : List (FreeGroup X))
    (hwU : ∀ u ∈ w, u ∈ U^{±1})
    (hchain : List.IsChain (fun u v ↦ u * v ≠ 1) w) :
    w.length ≤ w.prod.norm := by
  rcases hU.exists_prefix_middle_segments with ⟨a, m, hm_ne, _, hsurvives⟩
  sorry

end FreeGroup.IsNReduced

end
