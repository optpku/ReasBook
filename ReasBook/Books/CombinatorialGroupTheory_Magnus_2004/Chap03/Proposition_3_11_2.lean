/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import CombinatorialGroupTheory_Magnus_2004.Chap01.Definition_1_4_17
import CombinatorialGroupTheory_Magnus_2004.Chap01.Proposition_1_7_6
import CombinatorialGroupTheory_Magnus_2004.Chap01.Proposition_1_7_9

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

set_option autoImplicit false

noncomputable section

namespace GroupPresentation

variable {X : Type u}

local instance proposition_3_11_2_decidableEq : DecidableEq X := Classical.decEq X

/-!
Primary domain: small-cancellation style control of the normal closure of a relator family in a
free group.

Layer triage:
- `source-facing`: the normal closure `N` of the relators, the source symmetrized relator family
  `R*`, the “more than one half” segment condition on reduced words, and the conclusion that `N`
  has a basis consisting of conjugates of relators.
- `core/canonical`: `Subgroup.normalClosure R` is the owner for the subgroup `N`,
  `FreeGroupBasis` is the canonical owner for a chosen free basis of `N`, `CyclicWord X` is the
  chapter owner for reduced relators modulo cyclic permutation, `CyclicWord.toConjClasses` is the
  owner bridge from a cyclic word to the represented conjugacy class in the free group,
  `List.IsInfix` and `CyclicWord.HasPart` are the owner predicates for consecutive segments
  of canonical reduced and cyclically reduced words, and
  `IsConj` is the owner for conjugacy in the ambient free group.
- `bridge/view`: the source family `R*` is modeled as the set of cyclic words whose represented
  conjugacy class comes from a relator in `R` or its inverse, and the long-segment condition
  compares a linear segment of `w.toWord` with a cyclic segment of one of those symmetrized
  relators, using the chapter owner predicates for linear and cyclic occurrence.

Domain sampling:
1. `Subgroup.normalClosure R` is the canonical owner for the subgroup generated normally by the
   relators.
2. `FreeGroupBasis` is the canonical mathlib owner for a chosen free basis of a subgroup.
3. `List.IsInfix` from mathlib is the owner predicate for a segment of a reduced word.
4. `CyclicWord.HasPart` from Proposition `1-7-9` is the existing source-facing owner for a
   cyclic segment of a reduced cyclic word.
5. `CyclicWord.toConjClasses` from Definition `1-4-17` is the bridge from a reduced cyclic word
   to the represented conjugacy class.
6. `IsConj` is mathlib's owner predicate for conjugacy, so the conclusion should speak directly
   in that owner relation rather than through an explicit conjugator witness.

Primitive vs. derived:
- primitive data: the relator set `R`, a nontrivial element `w` of `Subgroup.normalClosure R`,
  and the existence of a segment in `w.toWord` longer than half the cyclic length of some
  symmetrized relator from `R*`, expressed through `List.IsInfix` and `CyclicWord.HasPart`;
- derived API: the existence of a basis of `Subgroup.normalClosure R` whose members are conjugates
  of relators from `R`.
-/

/-- The source symmetrized relator family `R*`, viewed as reduced cyclic words coming from a
relator in `R` or its inverse. -/
def symmetrizedRelatorFamily (R : Set (FreeGroup X)) : Set (CyclicWord X) :=
  { q | ∃ r : FreeGroup X, r ∈ R ∧
      (q.toConjClasses = ConjClasses.mk r ∨ q.toConjClasses = ConjClasses.mk r⁻¹) }

/-- A symmetrized relator from `R*` has the cyclic segment `part`, and its cyclic length is
strictly less than twice the length of `part`. -/
def HasLongSymmetrizedRelatorPart
    (R : Set (FreeGroup X)) (part : List (SignedLetter X)) : Prop :=
  ∃ q ∈ symmetrizedRelatorFamily R,
    q.HasPart part ∧ q.length < 2 * part.length

/-- A symmetrized relator from `R*` has the cyclic segment `part`, and `part` is longer than the
`numerator / denominator` fraction of that relator length. This is the natural fraction-parameter
bridge extending the half-relator owner `HasLongSymmetrizedRelatorPart`. -/
def HasLongSymmetrizedRelatorFractionPart
    (R : Set (FreeGroup X)) (numerator denominator : ℕ) (part : List (SignedLetter X)) : Prop :=
  ∃ q ∈ symmetrizedRelatorFamily R,
    q.HasPart part ∧ numerator * q.length < denominator * part.length

/-- The Chapter `3` half-relator owner is the `1 / 2` specialization of the general
fraction-parameter long-part predicate. -/
theorem hasLongSymmetrizedRelatorPart_iff_hasLongSymmetrizedRelatorFractionPart
    (R : Set (FreeGroup X)) (part : List (SignedLetter X)) :
    HasLongSymmetrizedRelatorPart R part ↔ HasLongSymmetrizedRelatorFractionPart R 1 2 part := by
  constructor
  · rintro ⟨q, hq, hpart, hlength⟩
    exact ⟨q, hq, hpart, by simpa using hlength⟩
  · rintro ⟨q, hq, hpart, hlength⟩
    exact ⟨q, hq, hpart, by simpa using hlength⟩

/-- The nontrivial element `w` of the relator subgroup has a segment longer than half the reduced
word of some symmetrized relator from the source family `R*`. -/
def HasLongRelatorSegment (R : Set (FreeGroup X)) (w : FreeGroup X) : Prop :=
  ∃ part : List (SignedLetter X), part <:+: w.toWord ∧ HasLongSymmetrizedRelatorPart R part

/-- Proposition 3-11-2: if every nontrivial element of the relator subgroup has a reduced-word
segment longer than half the cyclic length of some element of the source symmetrized relator
family `R*`, then the normal closure `N = Subgroup.normalClosure R` has a basis consisting of
conjugates of elements of `R`. -/
-- Proof sketch: use the half-overlap hypothesis to show that the collection of conjugates of
-- relators obtained by repeatedly shortening nontrivial elements of `N` is Nielsen reduced.
-- Then apply the Chapter `1` Nielsen basis criterion to that generating family inside
-- `Subgroup.normalClosure R`, yielding a basis whose elements remain conjugates of relators.
theorem exists_relator_conjugate_basis_of_normalClosure_of_long_relator_segments
    (R : Set (FreeGroup X))
    (hsegment : ∀ ⦃w : FreeGroup X⦄ (_ : w ∈ Subgroup.normalClosure R) (_ : w ≠ 1),
      HasLongRelatorSegment R w) :
    ∃ ι : Type v, ∃ basis : FreeGroupBasis ι (Subgroup.normalClosure R),
      ∀ i : ι, ∃ r : R, IsConj (basis i : FreeGroup X) r := sorry

end GroupPresentation

end
