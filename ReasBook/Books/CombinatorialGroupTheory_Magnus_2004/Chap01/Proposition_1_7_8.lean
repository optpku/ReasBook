/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import CombinatorialGroupTheory_Magnus_2004.Chap01.Proposition_1_7_6
import CombinatorialGroupTheory_Magnus_2004.Chap01.SignedLetter

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open scoped BigOperators

noncomputable section

section

variable {X : Type u}

local notation "basis" => FreeGroupBasis.ofFreeGroup X

local instance instDecidableEqX_1_7_8 : DecidableEq X := Classical.decEq X

-- Layer triage:
-- `source-facing`: a finite strictly quadratic word system in `FreeGroup X`, its Whitehead graph,
-- and the textbook conclusions "connected", "minimal", and "contains all generators".
-- `core/canonical`: `IsStrictlyQuadraticSet`, the owner namespace `FreeGroup.Finset` with
-- `totalLength`, `sigmaGraph`, `IsMinimal`, and `ContainsAllGenerators`,
-- `(wordIncidenceGraph basis (S : Set (FreeGroup X))).Connected`, `Finset.image`,
-- `FreeGroup.toWord`, `SimpleGraph.fromRel`, and `SimpleGraph.Connected`.
-- `bridge/view`: generator occurrence in reduced words translates Whitehead-graph connectedness
-- into the canonical word-incidence-graph connectedness predicate and the other source predicates
-- used below.
--
-- Domain sampling:
-- 1. `IsStrictlyQuadraticSet` from Proposition `1-7-6` is the chapter owner predicate for the
--    strict quadraticity of a finite set of free-group words, so this file reuses it directly.
-- 2. `wordIncidenceGraph basis` from Proposition `1-7-4` is the owner connectedness
--    construction for finite word systems, so the first theorem should conclude directly in that
--    owner form.
-- 3. In the source-facing Whitehead-graph formulation for finite-rank bases, the vertex set is
--    the full signed basis `X ± 1`, not merely the finite support of `S`, so the graph owner
--    below carries the weakest corresponding ambient hypothesis `[Finite X]`.
-- 4. `FreeGroup.Finset` is the natural owner namespace for finite free-group word systems in this
--    chapter, so the Whitehead graph, full-support predicate, and orbitwise minimality predicate
--    live there rather than as new bare globals.
-- 5. `basisLetterOccurs` and `generatorFiber` from Proposition `1-7-4` are the chapter owner
--    occurrence APIs for basis letters in a word system, so the full-support predicate below is
--    stated directly through them instead of rebuilding a parallel occurrence relation.
--
-- Primitive vs. derived:
-- the primitive source data are only the finite system `S : Finset (FreeGroup X)` and the reduced
-- word of each element. Strict quadraticity, word-incidence connectedness, and letter occurrence in
-- the system are reused owner notions; the Whitehead graph and automorphic minimality are derived
-- from them.

/-- The consecutive signed-letter pairs appearing in a reduced word. -/
private def adjacentPairs : List (SignedLetter X) → List (SignedLetter X × SignedLetter X)
  | [] => []
  | [_] => []
  | a :: b :: t => (a, b) :: adjacentPairs (b :: t)

namespace FreeGroup
namespace Finset

/-- The total reduced length of a finite word system. -/
def totalLength (S : Finset (FreeGroup X)) : ℕ :=
  S.sum fun g ↦ g.toWord.length

/-- The Whitehead-style signed-letter graph associated to a finite system of reduced words. Its
vertices are the signed generators `X ± 1`, and an edge joins `a` to `b⁻¹` when the consecutive
pair `(a, b)` appears in the canonical reduced word of some element of `S`. Because this source-
facing graph uses the full ambient signed basis as its vertex set, it is only exposed under the
finite-rank hypothesis `[Finite X]`. -/
def sigmaGraph [Finite X] (S : Finset (FreeGroup X)) : SimpleGraph (SignedLetter X) :=
  SimpleGraph.fromRel fun v w ↦
    ∃ g ∈ S, ∃ a b, (a, b) ∈ adjacentPairs g.toWord ∧ v = a ∧ w = b⁻¹

/-- A finite word system contains all generators when every ambient generator occurs in at least
one element of the system. -/
def ContainsAllGenerators (S : Finset (FreeGroup X)) : Prop :=
  ∀ x : X, (generatorFiber basis (S : Set (FreeGroup X)) x).Nonempty

/-- A finite word system is minimal if its total reduced length is minimal in its automorphic
orbit. -/
def IsMinimal (S : Finset (FreeGroup X)) : Prop :=
  ∀ α : MulAut (FreeGroup X), totalLength S ≤ totalLength (S.image α)

/-- Proposition 1-7-8 (1): if the Whitehead graph `Σ(S)` of a finite strictly quadratic system is
connected, then the system `S` is connected. -/
-- Proof sketch: a path in the signed-letter graph records a chain of generators shared by
-- successive words, and that chain lifts to a path in the canonical word-incidence graph.
theorem sigmaGraph_connected_implies_connected
    [Finite X] (S : Finset (FreeGroup X)) (hσ : (sigmaGraph S).Connected) :
    (wordIncidenceGraph basis (S : Set (FreeGroup X))).Connected := sorry

/-- Proposition 1-7-8 (2): if a finite strictly quadratic system has connected Whitehead graph,
then it is minimal in its automorphic orbit. -/
-- Proof sketch: if `S` were not minimal, Whitehead's reduction criterion would provide a
-- length-reducing Whitehead move. Strict quadraticity forces `Σ(S)` to be a union of cycles, and
-- connectedness rules out the small cut cardinalities needed for a length decrease.
theorem strictlyQuadratic_sigmaGraph_connected_implies_minimal
    [Finite X] (S : Finset (FreeGroup X)) (hstrict : IsStrictlyQuadraticSet S)
    (hσ : (sigmaGraph S).Connected) :
    IsMinimal S := sorry

/-- Proposition 1-7-8 (3): if the Whitehead graph `Σ(S)` is connected, then every generator of the
ambient basis occurs in `S`. -/
-- Proof sketch: a generator missing from `S` would contribute isolated signed vertices to
-- `Σ(S)`, contradicting connectedness.
theorem sigmaGraph_connected_implies_contains_all_generators
    [Finite X] (S : Finset (FreeGroup X)) (hσ : (sigmaGraph S).Connected) :
    ContainsAllGenerators S := sorry

end Finset
end FreeGroup

end
