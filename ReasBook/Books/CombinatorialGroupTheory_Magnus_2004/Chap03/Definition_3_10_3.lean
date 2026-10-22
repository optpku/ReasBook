/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import CombinatorialGroupTheory_Magnus_2004.Chap03.Definition_3_10_2

-- Declarations for this item will be appended below by the statement pipeline.

universe u

set_option autoImplicit false

section

namespace List

variable {G : Type u} [Group G]

/-!
Primary domain: finite list-valued Peiffer rewrites in a group.

Layer triage:
- `source-facing`: the second Peiffer transformation replacing an adjacent pair `(a, b)` by
  `(a * b * a⁻¹, a)`.
- `core/canonical`: `List.IsAdjacentConjugatingSwap` from Definition `3-10-2` is the chapter
  owner relation for this adjacent conjugating rewrite.
- `bridge/view`: the displayed textbook second-kind formula is exactly that owner relation, so the
  file recalls the canonical declaration directly instead of introducing a parallel local
  predicate.

Domain sampling:
1. `List G` is mathlib's owner abstraction for finite ordered sequences.
2. `List.IsAdjacentConjugatingSwap` is the project owner for the adjacent conjugating rewrite.
3. `List.length` is the first owner-side invariant of such a rewrite.
4. `List.prod` is the natural group-valued aggregate invariant of a Peiffer move.

Primitive vs. derived:
- primitive data: the owner relation `IsAdjacentConjugatingSwap` on the two lists;
- derived API: the owner-side invariants `length_eq_of_isAdjacentConjugatingSwap` and
  `prod_eq_of_isAdjacentConjugatingSwap`.
-/

/- Definition 3-10-3: the displayed second-kind Peiffer transformation is the chapter owner
relation `List.IsAdjacentConjugatingSwap`. Its basic invariants are part of that owner API, so
this file recalls the canonical declaration directly. -/
#check IsAdjacentConjugatingSwap
#check length_eq_of_isAdjacentConjugatingSwap
#check prod_eq_of_isAdjacentConjugatingSwap

end List

end
