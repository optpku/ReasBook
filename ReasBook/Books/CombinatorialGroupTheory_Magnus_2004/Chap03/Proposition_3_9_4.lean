/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import CombinatorialGroupTheory_Magnus_2004.Chap02.Proposition_2_5_1

-- Declarations for this item will be appended below by the statement pipeline.

universe u

noncomputable section

section

variable {X : Type u}

local instance proposition_3_9_4_decidableEq : DecidableEq X := Classical.decEq X
local notation "basis" => FreeGroupBasis.ofFreeGroup X

-- Layer triage:
-- `source-facing`: Proposition 3-9-4 is the free-group specialization of Magnus's normal-closure
-- occurrence theorem for a cyclically reduced relator.
-- `core/canonical`: `FreeGroupBasis.ofFreeGroup X`, `basisLetterOccurs`,
-- `FreeGroup.IsCyclicallyReduced`, and `Subgroup.normalClosure`.
-- `bridge/view`: specializing the basis-level theorem to the canonical basis of `FreeGroup X`
-- recovers the textbook wording that a generator occurring in `r` must also occur in any
-- nontrivial consequence `w` of `r`.
--
-- Domain sampling:
-- 1. `FreeGroupBasis.ofFreeGroup X` is the canonical basis owner for `FreeGroup X`.
-- 2. `basisLetterOccurs` from Proposition `1-7-4` is the chapter owner predicate for the source
--    phrase “the generator `x` occurs in a word”.
-- 3. `FreeGroupBasis.basisLetterOccurs_of_mem_normalClosure_singleton_of_isCyclicallyReduced`
--    from
--    Proposition `2-5-1` is the already-canonical Magnus statement at the correct owner level.
-- 4. `FreeGroup.IsCyclicallyReduced` and `Subgroup.normalClosure` are the canonical reduced-word
--    and normal-closure constructions on which that theorem is built.
--
-- Primitive vs. derived:
-- the primitive data remain the relator `r`, the normal-closure element `w`, and the generator
-- `x`; the occurrence relation is derived owner-side API through the canonical basis, so this
-- file does not keep a second public theorem phrased by raw membership in `toWord.map Prod.fst`.

/- Proposition 3-9-4: for the canonical basis of `FreeGroup X`, this is exactly Proposition
`2-5-1`. The source phrase “`x` occurs in a word” is already captured by
`basisLetterOccurs basis x`, so this item is a direct recall of the upstream owner theorem rather
than a duplicate free-group-only wrapper. -/
#check
  (FreeGroupBasis.basisLetterOccurs_of_mem_normalClosure_singleton_of_isCyclicallyReduced basis :
    ∀ {r w : FreeGroup X} {x : X},
      FreeGroup.IsCyclicallyReduced r.toWord →
        basisLetterOccurs basis x r →
          w ∈ Subgroup.normalClosure ({r} : Set (FreeGroup X)) →
            w ≠ 1 →
              basisLetterOccurs basis x w)

end
