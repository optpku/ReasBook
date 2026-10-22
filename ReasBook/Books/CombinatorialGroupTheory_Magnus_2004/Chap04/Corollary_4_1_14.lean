/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import CombinatorialGroupTheory_Magnus_2004.Chap01.Proposition_1_2_9
import CombinatorialGroupTheory_Magnus_2004.Chap03.Proposition_3_3_7

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

open Monoid

noncomputable section

section

variable {ι : Type u} {A : ι → Type v}
variable [Fintype ι] [∀ i, Group (A i)] [∀ i, Group.FG (A i)]

/-!
Primary domain: ranks of finitely generated groups and finite indexed free products.

Layer triage:
- `source-facing`: the rank of a finite free product `*ᵢ A i`.
- `core/canonical`: `Group.rank` is the owner for the minimum number of generators of a finitely
  generated group, `Monoid.CoprodI` is the owner abstraction for indexed free products, and
  `FreeGroupBasis.coprodI` is the canonical free-basis owner for free products of free groups.
- `bridge/view`: Proposition `3-3-7`, recalled later in Chapter 4 as Theorem `4-1-13`, is the
  owner bridge from a surjection out of a finitely generated free group onto `CoprodI A` to a
  corresponding free-product decomposition of that free group by subgroup factors mapping onto the
  ambient factors.

Domain sampling:
1. `Group.rank`, `Group.rank_spec`, and `Group.rank_le_of_surjective` in
   `Mathlib/GroupTheory/Rank` are the canonical owner API for finite generating-number statements.
2. `Monoid.CoprodI`, `Monoid.CoprodI.of`, and `Monoid.CoprodI.lift` in
   `Mathlib/GroupTheory/CoprodI` are the canonical free-product owners.
3. `FreeGroupBasis.coprodI` in `Mathlib/GroupTheory/CoprodI` is the owner theorem saying that a
   free product of free groups is free on the sigma-sum of the component bases.
4. `exists_freeProduct_subgroup_family_lifting_surjection_to_indexed_freeProduct` from Proposition
   `3-3-7` is the project owner bridge; Theorem `4-1-13` only recalls that declaration, so this
   file should depend on the owner directly rather than on the recall wrapper.

Primitive vs. derived:
- primitive public data: the finite family `A : ι → Type` of finitely generated groups;
- derived API: finite generation of `CoprodI A`, the sharp upper rank bound from the union of
  factor generating sets, and the free-group decomposition of a minimal-rank free cover used for
  the lower bound.
-/

private instance coprodI_fg : Group.FG (CoprodI A) := by
  sorry

/-- Corollary 4-1-14: for a finite free product `*ᵢ A i`, the minimum number of generators is the
sum of the minimum numbers of generators of the factors. -/
-- Proof sketch: the upper bound comes from taking minimal generating sets in each factor and
-- adjoining them through the canonical inclusions into the indexed free product. For the lower
-- bound, take a free cover of `CoprodI A` on exactly `Group.rank (CoprodI A)` generators and apply
-- Proposition `3-3-7` (recalled in Chapter 4 as Theorem `4-1-13`) to decompose that free group
-- as a free product of subgroup factors mapping onto the `A i`. The free-product basis theorem
-- `FreeGroupBasis.coprodI` identifies the total number of basis elements of those subgroup factors
-- with the rank of the covering free group, while each factor rank dominates the rank of the
-- corresponding quotient `A i`.
theorem rank_coprodI_eq_sum :
    Group.rank (CoprodI A) = ∑ i, Group.rank (A i) := by
  sorry

end
