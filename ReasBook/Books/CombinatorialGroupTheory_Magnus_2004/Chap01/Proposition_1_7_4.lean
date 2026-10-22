/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import CombinatorialGroupTheory_Magnus_2004.Chap01.Proposition_1_5_6

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

noncomputable section

section

variable {X : Type u} {F : Type v} [Group F]

local instance instDecidableEqQuadraticWordSet_174 : DecidableEq X := Classical.decEq X

-- Layer triage:
-- `source-facing`: quadratic word sets over a chosen free basis together with their incidence
-- graph.
-- `core/canonical`: `FreeGroupBasis X F` as the owner abstraction for the basis, together with
-- `reducedWordSupport` on the canonical free-group model `FreeGroup X`.
-- `bridge/view`: `basis.repr` is the canonical equivalence used to read an element of `F` as a
-- reduced word over the basis alphabet `X`; the letter-occurrence API below is the thin bridge
-- `x ∈ reducedWordSupport (basis.repr g)`.
--
-- Domain sampling:
-- 1. `FreeGroupBasis` in mathlib is the owner abstraction for a chosen basis of a free group.
-- 2. `reducedWordSupport` from Proposition `1-5-6` is the chapter owner for basis-support in a
--    canonical reduced word.
-- 3. The `FunLike` instance on `FreeGroupBasis` makes the basis map itself canonical, so the
--    corresponding subset of basis generators is `Set.range basis` rather than a parallel wrapper.
-- 4. `basis.repr` is the canonical transport from the intrinsic basis-level group `F` to
--    `FreeGroup X`.
-- Primitive vs. derived:
-- the primitive source-facing data here are the quadraticity predicate and its incidence graph;
-- the basis-generator subset appearing in the conclusion is derived owner API and is therefore
-- stated directly as `Set.range basis`, while the word-level occurrence relation is the thin
-- bridge from `basis.repr` to `reducedWordSupport`.

/-- A basis letter occurs in `g` when it appears in the canonical reduced word `basis.repr g`. -/
def basisLetterOccurs (basis : FreeGroupBasis X F) (x : X) (g : F) : Prop :=
  x ∈ reducedWordSupport (basis.repr g)

/-- The words of `S` in whose reduced form the basis letter `x` occurs. -/
def generatorFiber (basis : FreeGroupBasis X F) (S : Set F) (x : X) : Set F :=
  {s | s ∈ S ∧ basisLetterOccurs basis x s}

/-- A set of words is quadratic over the chosen basis if each basis letter occurs at most once in
each word and in at most two words of the set. -/
def IsQuadraticWordSet (basis : FreeGroupBasis X F) (S : Set F) : Prop :=
  (∀ s ∈ S, ((basis.repr s).toWord.map Prod.fst).Nodup) ∧
    ∀ x : X, (generatorFiber basis S x).encard ≤ 2

/-- The incidence graph of a set of words joins two words when their reduced words share a basis
letter. -/
def wordIncidenceGraph (basis : FreeGroupBasis X F) (S : Set F) : SimpleGraph S :=
  SimpleGraph.fromRel fun s t : S ↦
    ∃ x : X, basisLetterOccurs basis x s.1 ∧ basisLetterOccurs basis x t.1

/-- In a quadratic word set, each basis letter occurs in at most two words of the set. -/
-- Proof sketch: this is the second conjunct of `IsQuadraticWordSet basis S`.
theorem quadraticWordSet_generatorFiber_encard_le_two
    (basis : FreeGroupBasis X F) (S : Set F) (hS : IsQuadraticWordSet basis S) (x : X) :
    (generatorFiber basis S x).encard ≤ 2 :=
  hS.2 x

/-- Proposition 1-7-4: if `S` is quadratic over the basis `X`, connected via its incidence graph,
and infinite, then some automorphism of `F` carries `S` into the chosen basis subset. -/
-- Proof sketch: choose an infinite path in a maximal tree of the incidence graph, orient the tree
-- upward, and apply the preceding quadratic-word-set construction to obtain an automorphism whose
-- inverse sends each word of `S` to a basis generator.
theorem exists_automorphism_image_subset_basis_range_of_quadratic_connected_infinite
    (basis : FreeGroupBasis X F) (S : Set F)
    (hquadratic : IsQuadraticWordSet basis S)
    (hconnected : (wordIncidenceGraph basis S).Connected)
    (hinfinite : S.Infinite) :
    ∃ α : MulAut F, α '' S ⊆ Set.range basis := sorry

end
