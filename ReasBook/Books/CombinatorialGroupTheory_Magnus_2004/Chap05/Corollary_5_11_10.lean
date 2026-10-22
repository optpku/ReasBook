/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import CombinatorialGroupTheory_Magnus_2004.Chap05.Theorem_5_11_9

-- Declarations for this item will be appended below by the statement pipeline.

universe u v w

set_option autoImplicit false

section

variable {H : Type u} {K : Type v} [Group H] [Group K] [IsFreeGroup H]

open Subgroup

/-!
Primary domain: `SQ`-universality of free products with amalgamation over free groups.

Layer triage:
- `source-facing`: a free group `H`, a finitely generated subgroup `A ≤ H` of infinite index, a
  proper subgroup `A' ≤ K` isomorphic to `A`, and the resulting free product with amalgamation
  `P = (H * K; A = A')`.
- `core/canonical`: `Subgroup.IsBlockingPair` from Definition `5-11-8` and
  `isSQUniversal_amalgamatedProductAlong_of_exists_blockingPair` from Theorem `5-11-9` are the
  chapter owner predicate and owner theorem for the Section `11` argument.
- `bridge/view`: this corollary turns the source free-group hypotheses `A.FG` and the canonical
  infinite-index condition `Infinite (H ⧸ A)` into the blocking-pair hypothesis needed by Theorem
  `5-11-9`; `Subgroup.index_eq_zero_iff_infinite` is only the internal mathlib bridge to the
  older index-sentinel encoding.

Domain sampling:
1. `Subgroup.IsBlockingPair` from Definition `5-11-8` is the source-facing owner predicate for
   the combinatorial obstruction used in Section `11`.
2. `isSQUniversal_amalgamatedProductAlong_of_exists_blockingPair` from Theorem `5-11-9` is the
   chapter owner theorem for the `SQ`-universality conclusion.
3. `amalgamatedProductAlong e` from Definition `4-2-9` is the canonical owner for the
   resulting free product with amalgamation.
4. `Subgroup.index`, `Subgroup.FiniteIndex`, and
   `Subgroup.index_eq_zero_iff_infinite` in `Mathlib/GroupTheory/Index` are the canonical owner
   API and bridge for subgroup index; the quotient-side `Infinite (H ⧸ A)` hypothesis is the
   mathematically faithful public surface here.
5. `IsFreeGroup H` and `A.FG` are the canonical encodings of the remaining source free-group
   hypotheses.

Primitive vs. derived:
the primitive data are exactly the two ambient groups, the subgroup `A ≤ H`, the proper copy
`A' ≤ K`, and the chosen isomorphism `e : A ≃* A'`. The blocking-pair witness is derived from the
free-group hypotheses and is therefore produced internally in the corollary proof rather than
exposed as a second local declaration with overlapping mathematical content. The index-sentinel
equation `A.index = 0` is likewise treated as derived bridge API, not primitive public data.
-/

-- Proof sketch: derive a blocking pair for `A` from the free-group hypotheses together with the
-- canonical quotient-infinitude input `Infinite (H ⧸ A)`, then apply the owner theorem
-- `isSQUniversal_amalgamatedProductAlong_of_exists_blockingPair`.
/-- Corollary 5-11-10: if `H` is free, `A ≤ H` is finitely generated of infinite index, and `K`
contains a proper subgroup `A'` isomorphic to `A`, then the amalgamated free product
`(H * K; A = A')` is `SQ`-universal. -/
theorem isSQUniversal_amalgamatedProductAlong_of_freeGroup_subgroup_fg_of_infiniteIndex
    (A : Subgroup H) (hA_fg : A.FG) (hA_quotient : Infinite (H ⧸ A))
    (A' : Subgroup K) (hA'_proper : A' < ⊤) (e : A ≃* A') :
    IsSQUniversal (amalgamatedProductAlong e) := by
  have hblocking : ∃ x₁ x₂, A.IsBlockingPair x₁ x₂ := by
    -- A finitely generated infinite-index subgroup of a free group admits a blocking pair in the
    -- sense of Definition `5-11-8`.
    -- The quotient-side infinitude needed for the classical free-group argument is supplied
    -- directly by `hA_quotient`.
    sorry
  intro L _ _
  exact isSQUniversal_amalgamatedProductAlong_of_exists_blockingPair A A' e hA'_proper hblocking

end
