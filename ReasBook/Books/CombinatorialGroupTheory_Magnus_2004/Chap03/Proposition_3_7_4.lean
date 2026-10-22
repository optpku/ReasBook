/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import CombinatorialGroupTheory_Magnus_2004.Chap03.Definition_3_5_3
import CombinatorialGroupTheory_Magnus_2004.Chap03.Proposition_3_5_5

-- Declarations for this item will be appended below by the statement pipeline.

universe u

set_option autoImplicit false

section

variable {G : Type u} [Group G]

/-!
Primary domain: `F`-groups, subgroup index, and free products of cyclic groups.

Layer triage:
- `source-facing`: a subgroup `H ≤ G` of an `F`-group `G`, with the two cases that `H` has finite
  or infinite index in `G`.
- `core/canonical`: `IsFGroup` from Definition `3-5-3`, `IsFreeProductOfCyclicGroups` from
  Proposition `3-5-5`, and mathlib's subgroup-index owner API `Subgroup.index` together with
  `Subgroup.FiniteIndex`.
- `bridge/view`: Proposition `3-7-3` already packages the subgroup-inheritance step at the
  Fuchsian-complex level through
  `exists_faceUnionRefinement_fuchsianComplex_of_subgroup`, while
  `Subgroup.index_eq_zero_iff_infinite` is the standard bridge from the subgroup-index owner to
  the quotient-side infinitude predicate. The present file records only the two source-facing
  consequences obtained from that owner-level refinement.

Domain sampling:
1. `IsFGroup` is the chapter owner predicate for the source notion of an `F`-group.
2. `IsFreeProductOfCyclicGroups` is the source-facing owner predicate for the alternative
   conclusion in the infinite-index case.
3. `Subgroup.index` and `Subgroup.FiniteIndex` in `Mathlib/GroupTheory/Index` are the canonical
   owner abstractions for subgroup index and finite-index subgroup inclusions.
4. `Subgroup.index_eq_zero_iff_infinite` is the standard bridge between infinite subgroup index
   and quotient infinitude.
5. `exists_faceUnionRefinement_fuchsianComplex_of_subgroup` from Proposition `3-7-3` is the
   chapter owner theorem for passing from a Fuchsian complex of `G` to one for `H`.

Primitive vs. derived:
- primitive public data: the `F`-group hypothesis on `G`, the subgroup `H ≤ G`, and the finite-
  or infinite-index hypothesis on `H`, recorded canonically by `[H.FiniteIndex]` and the explicit
  owner equality `H.index = 0`;
- derived API: the two subgroup conclusions `IsFGroup H` and
  `IsFreeProductOfCyclicGroups H`. No extra subgroup wrapper or chosen Fuchsian-complex package is
  introduced here.
-/

variable (H : Subgroup G)

/-- Proposition 3-7-4 (1): every finite-index subgroup of an `F`-group is again an `F`-group. -/
-- Proof sketch: use the Section `7` Fuchsian-complex model attached to `G` and the subgroup
-- inheritance theorem `exists_faceUnionRefinement_fuchsianComplex_of_subgroup` from Proposition
-- `3-7-3`. Finite index means each new face is assembled from only finitely many old faces, so the
-- subgroup remains in the `F`-group branch of the Section `5` planar alternative.
theorem isFGroup_of_finiteIndex_subgroup
    (hG : IsFGroup G)
    [H.FiniteIndex] :
    IsFGroup H := sorry

/-- Proposition 3-7-4 (2): every infinite-index subgroup of an `F`-group is a free product of
cyclic groups. -/
-- Proof sketch: start from the same subgroup Fuchsian-complex refinement from Proposition
-- `3-7-3`. Infinite index forces the coarse faces of the subgroup complex to be infinite unions of
-- original faces, so the subgroup falls in the free-product branch of the Section `5` planar
-- alternative.
theorem isFreeProductOfCyclicGroups_of_infiniteIndex_subgroup
    (hG : IsFGroup G)
    (hH : H.index = 0) :
    IsFreeProductOfCyclicGroups H := sorry

end
