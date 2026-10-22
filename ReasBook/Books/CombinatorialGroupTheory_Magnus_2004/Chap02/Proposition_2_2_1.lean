/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u

namespace GroupPresentation

-- Layer triage:
-- `source-facing`: a finite presentation consists of a finite generator type together with a
-- finite relator set, and Tietze transformations are the elementary operations on such data.
-- `core/canonical`: `PresentedGroup` is the owner object attached to a relator set,
-- `Group.IsFinitelyPresented` is mathlib's owner predicate for the abstract group-level notion,
-- and `Relation.EqvGen` is the canonical owner for equivalence closure of elementary steps.
-- `bridge/view`: the proposition identifies equality up to a finite Tietze sequence on the
-- source-facing data with isomorphism of the associated canonical presented groups.
-- Domain sampling:
-- 1. `PresentedGroup rels` is mathlib's canonical group attached to generators and relations.
-- 2. `PresentedGroup.toGroup` and `PresentedGroup.equivPresentedGroup` are the owner transport
--    maps for changing generators and relators while preserving the presented group.
-- 3. `Group.IsFinitelyPresented` is the canonical abstract owner predicate for the existence of a
--    finite presentation.
-- 4. `Relation.EqvGen` is mathlib's canonical equivalence closure for a primitive one-step
--    relation, so a separate inductive closure API is unnecessary here.
-- 5. Definition `2-1-2` in this chapter already identifies "finite presentation" with the
--    primitive owner predicates `Finite X` and `Set.Finite R`, so no parallel wrapper structure
--    is needed here.
-- Primitive vs. derived:
-- the primitive source data are the generator type and relator set together with the owner
-- finiteness predicates `Finite X` and `Set.Finite R`, together with the one-step
-- source-facing Tietze expansion relation; the presented group, the abstract
-- finite-presentation property, and Tietze equivalence are derived owner-side API.

variable {X Y Z : Type u}
variable {R : Set (FreeGroup X)} {S : Set (FreeGroup Y)} {T : Set (FreeGroup Z)}

-- Proof sketch: choose an equivalence between the finite generator type `X` and some `Fin n`,
-- transport the relator set `R` across that equivalence using
-- `PresentedGroup.equivPresentedGroup`, and use the finiteness of the transported relator set to
-- instantiate `Group.IsFinitelyPresented`.
/-- The group canonically defined by a finite presentation is finitely presented in mathlib's
abstract sense. -/
theorem isFinitelyPresented_presentedGroup [Finite X] (hR : R.Finite) :
    Group.IsFinitelyPresented (PresentedGroup R) := sorry

/-- An elementary Tietze expansion either adjoins finitely many relators already implied by the
old ones, up to reindexing of generators, or adjoins finitely many new generators together with
defining relators expressing them as words in the old generators. -/
inductive TietzeExpansion :
    {X : Type u} → Set (FreeGroup X) → {Y : Type u} → Set (FreeGroup Y) → Prop
  | addConsequenceRelators
      {X Y : Type u}
      {R : Set (FreeGroup X)}
      {S : Set (FreeGroup Y)}
      (e : X ≃ Y)
      (T : Set (FreeGroup Y))
      (hTfinite : T.Finite)
      (hTclosure : T ⊆ Subgroup.normalClosure (FreeGroup.freeGroupCongr e '' R))
      (hS : S = FreeGroup.freeGroupCongr e '' R ∪ T) :
      TietzeExpansion R S
  | addGenerators
      {X Y : Type u}
      {R : Set (FreeGroup X)}
      {S : Set (FreeGroup Y)}
      (Z : Type u)
      [Finite Z]
      (e : X ⊕ Z ≃ Y)
      (words : Z → FreeGroup X)
      (hS :
        S =
          FreeGroup.freeGroupCongr e ''
            ((FreeGroup.lift (fun x : X ↦ FreeGroup.of (Sum.inl x)) '' R) ∪
              Set.range
                (fun z : Z ↦
                  (FreeGroup.of (Sum.inr z))⁻¹ *
                    FreeGroup.lift (fun x : X ↦ FreeGroup.of (Sum.inl x)) (words z)))) :
      TietzeExpansion R S

private abbrev Presentation :=
  Σ X : Type u, Set (FreeGroup X)

private abbrev presentation {X : Type u} (R : Set (FreeGroup X)) : Presentation :=
  ⟨X, R⟩

private inductive TietzeStep : Presentation → Presentation → Prop
  | mk
      {X Y : Type u}
      {R : Set (FreeGroup X)}
      {S : Set (FreeGroup Y)}
      (h : TietzeExpansion R S) :
      TietzeStep (presentation R) (presentation S)

/-- Two finite presentations are Tietze equivalent when one can be obtained from the other by a
finite sequence of elementary Tietze expansions and their inverses. -/
def TietzeEquivalent :
    {X : Type u} → Set (FreeGroup X) → {Y : Type u} → Set (FreeGroup Y) → Prop
  | _, R, _, S => Relation.EqvGen TietzeStep (presentation R) (presentation S)

-- Proof sketch: each elementary Tietze expansion preserves the associated presented group up to a
-- canonical multiplicative equivalence, so a finite sequence gives an isomorphism by composition.
-- Conversely, given an isomorphism between the groups defined by two finite presentations, pass to
-- a common presentation on the disjoint union of the generator sets, adjoin the finite defining
-- relators coming from the chosen words on each side, and realize each enlargement as a finite
-- Tietze sequence.
/-- Proposition 2-2-1: two finite presentations define isomorphic groups if and only if they are
related by a finite sequence of Tietze transformations. -/
theorem presentedGroup_mulEquiv_iff_tietzeEquivalent [Finite X] [Finite Y]
    (hR : R.Finite) (hS : S.Finite) :
    Nonempty (PresentedGroup R ≃* PresentedGroup S) ↔ TietzeEquivalent R S := sorry

end GroupPresentation
