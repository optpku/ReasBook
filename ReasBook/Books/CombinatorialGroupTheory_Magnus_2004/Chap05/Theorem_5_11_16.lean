/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import CombinatorialGroupTheory_Magnus_2004.Chap02.Proposition_2_5_31

-- Declarations for this item will be appended below by the statement pipeline.

universe u

section

variable {X : Type u}

/-!
Primary domain: one-relator groups and `SQ`-universality.

Layer triage:
- `source-facing`: a one-relator group on at least three generators, written in the text as
  `⟨t, b, c, ... ; r⟩`.
- `core/canonical`: `PresentedGroup (Set.singleton r)` is the project's owner for one-relator
  groups, `Cardinal.mk X` records the lower bound on the number of generators, and
  `IsSQUniversal` is the owner predicate for `SQ`-universality.
- `bridge/view`: the Chapter V proof route rewrites the relator using Lemma `5-11-15` and then
  applies an HNN-extension criterion, but those intermediate choices do not belong in the public
  statement. The resulting theorem is exactly the canonical one-relator statement already recorded
  in Proposition `2-5-31`.

Domain sampling:
1. `PresentedGroup (Set.singleton r)` is the established owner for one-relator groups in this
   project.
2. `IsSQUniversal` from Proposition `2-5-31` is the canonical owner predicate for the conclusion.
3. `isSQUniversal_of_three_generator_one_relator_group` already states the one-relator
   `SQ`-universality theorem with the exact owner-level interface needed here.

Primitive vs. derived:
the primitive public data are only the relator `r` and the cardinality hypothesis
`3 ≤ Cardinal.mk X`. The distinguished generator `t` from the proof, the zero exponent-sum
rewriting from Lemma `5-11-15`, and the HNN-extension decomposition are proof-level bridges, not
part of the statement API.
-/

/- Theorem 5-11-16: a group with a one-relator presentation on at least three generators is
`SQ`-universal.

This item adds no new public declaration beyond the canonical theorem
`isSQUniversal_of_three_generator_one_relator_group`; the Chapter V HNN-extension argument is a
proof route for that already existing owner-level statement. -/
#check (isSQUniversal_of_three_generator_one_relator_group :
  (r : FreeGroup X) → (hX : 3 ≤ Cardinal.mk X) →
    IsSQUniversal (PresentedGroup (Set.singleton r)))

end
