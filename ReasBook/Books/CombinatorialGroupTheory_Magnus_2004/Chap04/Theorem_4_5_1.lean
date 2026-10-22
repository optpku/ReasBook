/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import CombinatorialGroupTheory_Magnus_2004.Chap02.Theorem_2_6_1

-- Declarations for this item will be appended below by the statement pipeline.

universe u

noncomputable section

section

variable {X : Type u} (r : FreeGroup X)

local instance theorem_4_5_1_decidableEq : DecidableEq X := Classical.decEq X

local notation "basis" => FreeGroupBasis.ofFreeGroup X
local notation "G" => PresentedGroup (Set.singleton r)
local notation "gen" => (PresentedGroup.of : X → G)

/-!
Primary domain: one-relator groups and Magnus's Freiheitssatz.

Layer triage:
- `source-facing`: a one-relator quotient `G = ⟨X ; r⟩`, a subset `L ⊆ X` omitting a generator
  `x` that occurs in the cyclically reduced relator `r`, and the conclusion that the images of `L`
  form a free basis of the subgroup they generate.
- `core/canonical`: `PresentedGroup (Set.singleton r)` for the one-relator quotient,
  `PresentedGroup.of` for the generator map, and
  `freiheitssatz_injOn_presentedGroup_of_and_isFreeGroupBasis` from Theorem `2-6-1` as the owner
  theorem for this one-relator Freiheitssatz statement.
- `bridge/view`: `basisLetterOccurs basis x r` is the project's canonical occurrence predicate for
  the source phrase “the generator `x` occurs in `r`”.

Domain sampling:
1. `PresentedGroup (Set.singleton r)` is the owner abstraction for the one-relator group
   `⟨X ; r⟩`.
2. `PresentedGroup.of` is the canonical map sending each generator of `X` to its class in that
   quotient.
3. `basisLetterOccurs basis x r` is the established project API for occurrence of a generator in a
   relator.
4. `freiheitssatz_injOn_presentedGroup_of_and_isFreeGroupBasis` from Theorem `2-6-1` is the
   upstream owner theorem already expressing this chapter item at the canonical owner level.

Primitive vs. derived:
the primitive source data are the relator `r`, the subset `L`, and the omitted generator `x`
occurring in `r`; the subgroup `Subgroup.closure (gen '' L)` and the basis assertion on its
generator-image subset are derived owner-side objects. This item therefore recalls the Chapter
`2-6-1` owner theorem directly instead of keeping parallel local wrapper theorems.
-/

/- Theorem 4-5-1 adds no new owner-level construction beyond Theorem `2-6-1`. The recalled theorem
already contains the source-facing free-basis conclusion together with the stronger injectivity
statement for the generator images. -/
#check (freiheitssatz_injOn_presentedGroup_of_and_isFreeGroupBasis r :
  ∀ (L : Set X) {x : X},
    FreeGroup.IsCyclicallyReduced r.toWord →
      basisLetterOccurs basis x r →
        x ∉ L →
          Set.InjOn gen L ∧
            IsFreeGroupBasis {g : Subgroup.closure (gen '' L) | (g : G) ∈ gen '' L})

end
