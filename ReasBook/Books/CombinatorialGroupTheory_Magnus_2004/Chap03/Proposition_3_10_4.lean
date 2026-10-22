/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import CombinatorialGroupTheory_Magnus_2004.Chap03.Definition_3_10_1
import CombinatorialGroupTheory_Magnus_2004.Chap03.Definition_3_10_2
import CombinatorialGroupTheory_Magnus_2004.Chap03.Definition_3_10_3

-- Declarations for this item will be appended below by the statement pipeline.

universe u

set_option autoImplicit false

noncomputable section

/-!
Primary domain: aspherical presentations and identities among relations.

Layer triage:
- `source-facing`: a finite sequence of conjugates of relators and inverse relators whose total
  product is trivial, the elementary Peiffer moves on such sequences, and the equivalence between
  triviality of all such identities and asphericity of the presentation.
- `core/canonical`: `CayleyComplex.Coordinates` and `CayleyComplex.Coordinates.IsAspherical`
  from Definition `3-10-1` are the owner notions for spherical-diagram asphericity,
  `List (FreeGroup X)` is the owner for finite identities among relations, `IsConj` is the
  canonical owner for conjugacy in the free group, and `Relation.ReflTransGen` is the canonical
  owner for finite chains of elementary moves.
- `bridge/view`: Definitions `3-10-2` and `3-10-3` provide the two oriented adjacent conjugating
  rewrites used in a Peiffer move, while a separate local deletion step records cancellation of an
  adjacent inverse pair.

Domain sampling:
1. `CayleyComplex.Coordinates.IsAspherical` is already the chapter owner for the asphericity side
   of the equivalence, so the main theorem should reuse it directly.
2. `List (FreeGroup X)` is the canonical owner for a finite sequence `(p₁, ..., pₙ)` of
   conjugates.
3. `IsConj` from mathlib is the canonical owner for “is a conjugate of”.
4. `Relation.ReflTransGen` is the canonical closure operator for “obtainable by finitely many
   elementary moves”.
5. `List.IsAdjacentConjugatingSwap` is the chapter owner relation for the adjacent conjugating
   rewrite, and Definitions `3-10-2` and `3-10-3` contribute its two orientations
   `List.IsAdjacentConjugatingSwap π' π` and `List.IsAdjacentConjugatingSwap π π'`.

Primitive vs. derived:
- primitive data: a relator set `R`, a list `π : List (FreeGroup X)`, the termwise conjugacy
  condition, and the elementary local rewrite steps on `π`;
- derived API: triviality of an identity via finitely many Peiffer reductions and the main
  equivalence with asphericity.
-/

namespace GroupPresentation

variable {X : Type u}

/-- A term in an identity among relations for `(X; R)` is a conjugate of a relator or of the
inverse of a relator. -/
def IsRelatorConjugate (R : Set (FreeGroup X)) (p : FreeGroup X) : Prop :=
  ∃ r : FreeGroup X, r ∈ R ∧ (IsConj p r ∨ IsConj p r⁻¹)

/-- An identity among relations for `(X; R)` is a finite sequence of conjugates of relators or
inverse relators whose product in the free group is `1`. -/
def IsIdentityAmongRelations (R : Set (FreeGroup X)) (π : List (FreeGroup X)) : Prop :=
  (∀ p ∈ π, IsRelatorConjugate R p) ∧ π.prod = 1

/-- The defining conditions for an identity among relations are termwise relator conjugacy and
trivial total product. -/
-- Proof sketch: unfold `IsIdentityAmongRelations`.
theorem isIdentityAmongRelations_iff (R : Set (FreeGroup X)) (π : List (FreeGroup X)) :
    IsIdentityAmongRelations R π ↔ (∀ p ∈ π, IsRelatorConjugate R p) ∧ π.prod = 1 := sorry

/-- A deletion step cancels one adjacent inverse pair in a sequence. -/
def IsDeletionOfInversePair (π π' : List (FreeGroup X)) : Prop :=
  ∃ left right : List (FreeGroup X), ∃ a : FreeGroup X,
    π = left ++ [a, a⁻¹] ++ right ∧ π' = left ++ right

/-- An elementary Peiffer step is either one of the two oriented adjacent conjugating rewrites
from Definitions `3-10-2` and `3-10-3`, or deletion/insertion of an adjacent inverse pair. -/
def PeifferStep (π π' : List (FreeGroup X)) : Prop :=
  List.IsAdjacentConjugatingSwap π' π ∨
    List.IsAdjacentConjugatingSwap π π' ∨
      IsDeletionOfInversePair π π' ∨ IsDeletionOfInversePair π' π

/-- An identity among relations is trivial when finitely many elementary Peiffer steps transform
it into the empty identity. -/
def IsTrivialIdentityAmongRelations (π : List (FreeGroup X)) : Prop :=
  Relation.ReflTransGen PeifferStep π []

/-- A presentation admits a nontrivial identity among relations when some identity among
relations is not reducible to the empty identity by elementary Peiffer steps. -/
def HasNontrivialIdentityAmongRelations (R : Set (FreeGroup X)) : Prop :=
  ∃ π : List (FreeGroup X),
    IsIdentityAmongRelations R π ∧ ¬ IsTrivialIdentityAmongRelations π

/-- A nontrivial identity among relations is exactly an identity not connected to the empty one by
the Peiffer-step closure. -/
-- Proof sketch: unfold `HasNontrivialIdentityAmongRelations` and
-- `IsTrivialIdentityAmongRelations`.
theorem hasNontrivialIdentityAmongRelations_iff (R : Set (FreeGroup X)) :
    HasNontrivialIdentityAmongRelations R ↔
      ∃ π : List (FreeGroup X),
        IsIdentityAmongRelations R π ∧ ¬ Relation.ReflTransGen PeifferStep π [] := sorry

/-- Proposition 3-10-4: the actual Cayley complex `C(X; R)` is aspherical exactly when the
relator family `R` admits no nontrivial identity among relations. -/
-- Proof sketch: build from any identity among relations the spherical diagram obtained by sewing
-- together the corresponding bouquet of relator discs, and conversely decompose any spherical
-- diagram into such a bouquet. The elementary Peiffer moves are precisely the local modifications
-- that preserve the resulting spherical diagram, and trivial identities are exactly those that
-- reduce to the empty diagram.
theorem isAspherical_iff_no_nontrivial_identities_among_relations
    {R : Set (FreeGroup X)} {C : TwoComplex}
    (coords : CayleyComplex.Coordinates.PresentationCoordinates C R) :
    CayleyComplex.Coordinates.IsAspherical coords ↔
      ¬ HasNontrivialIdentityAmongRelations R := sorry

end GroupPresentation
