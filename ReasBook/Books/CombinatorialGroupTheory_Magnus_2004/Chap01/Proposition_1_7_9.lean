/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import CombinatorialGroupTheory_Magnus_2004.Chap01.Proposition_1_4_1
import CombinatorialGroupTheory_Magnus_2004.Chap01.Proposition_1_7_11

universe u

open scoped Classical
open FreeGroupBasis

noncomputable section

set_option autoImplicit false

section

variable {X : Type u}

local notation "basis" => FreeGroupBasis.ofFreeGroup X

local instance instDecidableEqXProp179 : DecidableEq X := Classical.decEq X

-- Layer triage:
-- `source-facing`: finite strictly quadratic sets `S` of reduced cyclic words, the textbook
-- invariant `k(S)`, and one-step attached elementary Nielsen transformations `S ↦ Sσ`.
-- `core/canonical`: `Finset (CyclicWord X)` together with the owner namespace
-- `CyclicWord.Finset`, `CyclicWord.length`, `CyclicWord.map`, and the single-word Whitehead-graph
-- constructions `edgesOfWord` and `wordSupport` from Proposition `1-7-11`.
-- `bridge/view`: the finite-system Whitehead graph `Σ(S)` is derived by taking the union of the
-- single-word Whitehead edges and supports over the owner finite system `S`.
-- Domain sampling:
-- 1. `CyclicWord` from Definition `1-4-17` is the chapter owner abstraction for reduced cyclic
--    words.
-- 2. `CyclicWord.length` is the canonical size function on one reduced cyclic word, so the total
--    size `|S|` should be derived in the owner finite-system namespace.
-- 3. `edgesOfWord` and `wordSupport` from Proposition `1-7-11` are the owner one-word
--    Whitehead-graph constructions reused here for finite systems.
-- 4. `CyclicWord.map` from Definition `1-4-17` is the owner action of `Aut(FreeGroup X)` on
--    reduced cyclic words.
-- Primitive vs. derived:
-- the primitive source data are the finite set `S` of reduced cyclic words and the attached
-- elementary Nielsen step. The total length, signed-occurrence counts, strict quadraticity
-- predicate, and invariant `k(S)` are then derived directly from the owner cyclic-word and graph
-- APIs.

local instance instDecidableEqSignedLetterProp179 : DecidableEq (SignedLetter X) :=
  Classical.decEq _
local instance instDecidableEqSym2SignedLetterProp179 : DecidableEq (Sym2 (SignedLetter X)) :=
  Classical.decEq _

namespace CyclicWord
namespace Finset

/-- The total cyclic length `|S|` of a finite set of reduced cyclic words. -/
def totalLength (S : Finset (CyclicWord X)) : ℕ :=
  S.sum fun q ↦ q.length

/-- The total number of occurrences of one signed basis letter in a finite set of cyclic words. -/
def signedOccurrenceCount (S : Finset (CyclicWord X)) (a : SignedLetter X) : ℕ :=
  S.sum fun q ↦ q.signedOccurrenceCount a

/-- A finite set of reduced cyclic words is strictly quadratic when each basis letter occurs
equally often with the two signs and with each sign at most once across the whole set. -/
def IsStrictlyQuadratic (S : Finset (CyclicWord X)) : Prop :=
  ∀ x : X,
    signedOccurrenceCount S (x, true) = signedOccurrenceCount S (x, false) ∧
      signedOccurrenceCount S (x, true) ≤ 1

/-- The signed letters appearing in the finite system, together with their formal inverses. -/
private def support (S : Finset (CyclicWord X)) : Finset (SignedLetter X) :=
  S.biUnion wordSupport

/-- The Whitehead edges contributed by the whole finite system. -/
private def sigmaEdges (S : Finset (CyclicWord X)) : Finset (Sym2 (SignedLetter X)) :=
  S.biUnion edgesOfWord

/-- The support vertices of the system Whitehead graph. -/
private abbrev Vertex (S : Finset (CyclicWord X)) :=
  { a : SignedLetter X // a ∈ support S }

/-- The support vertices form a finite type. -/
private instance instFintypeVertex (S : Finset (CyclicWord X)) : Fintype (Vertex S) :=
  Fintype.ofFinset (support S) fun _ ↦ by
    simp

/-- The Whitehead graph of a finite set of cyclic words, restricted to its finite support. -/
noncomputable def sigmaGraph (S : Finset (CyclicWord X)) : SimpleGraph (Vertex S) :=
  SimpleGraph.fromEdgeSet { e | Sym2.map Subtype.val e ∈ sigmaEdges S }

/-- The textbook invariant `k(S)`, realized as the number of connected components of the
Whitehead graph `Σ(S)`. -/
noncomputable def cycleCount (S : Finset (CyclicWord X)) : ℤ :=
  Int.ofNat (Nat.card ((sigmaGraph S).ConnectedComponent))

end Finset

/-- A reduced cyclic word contains the cyclic part `part` when some representative list has `part`
as a consecutive sublist. -/
def HasPart (q : CyclicWord X) (part : List (SignedLetter X)) : Prop :=
  ∃ u v : List (SignedLetter X), q.1 = ((u ++ part ++ v : List (SignedLetter X)) :
    Cycle (SignedLetter X))

end CyclicWord

open CyclicWord.Finset

/-- The canonical regular Nielsen transvection `x ↦ x y^ε` relative to the free basis on `X`. -/
private def signedElementaryNielsenTransvection
    (x y : X) (ySign : Bool) (hxy : x ≠ y) : MulAut (FreeGroup X) :=
  if ySign then
    elementaryNielsenTransvection basis x y hxy
  else
    (elementaryNielsenTransvection basis x y hxy)⁻¹

/-- An attached elementary Nielsen transformation of a finite set of reduced cyclic words is a
regular Nielsen transvection `x ↦ x y^ε` whose attaching condition is witnessed by the occurrence
of the part `x y^{-ε}` in one member of the source set; the target set is the automorphic image
under that canonical transvection. -/
def AttachedElementaryNielsenTransformation (S S' : Finset (CyclicWord X)) : Prop :=
  ∃ x y : X, ∃ ySign : Bool, ∃ hxy : x ≠ y,
    (∃ q ∈ S, q.HasPart [(x, true), (y, !ySign)]) ∧
      S' = S.image (CyclicWord.map (signedElementaryNielsenTransvection x y ySign hxy))

/-- Proposition 1-7-9: if `σ` is an attached elementary Nielsen transformation of the finite
strictly quadratic set `S` of reduced cyclic words, then either `|Sσ| = |S|` and
`k(Sσ) = k(S)`, or `|Sσ| = |S| - 2` and `k(Sσ) = k(S) - 1`. -/
-- Proof sketch: write the attached move in the canonical form `x ↦ x y^ε`, so some member of `S`
-- contains the part `x y^{-ε}`. The second occurrence of `x` determines whether the local surgery
-- on the Whitehead graph merely reroutes two arcs or collapses a 2-cycle. In the first case both
-- the total cyclic length and `k(S)` are unchanged; in the second, one cancellation pair is
-- removed, so the total length drops by `2` and the number of connected components drops by `1`.
theorem attachedElementaryNielsenTransformation_totalLength_cycleCount_outcome
    {S S' : Finset (CyclicWord X)}
    (hstrict : IsStrictlyQuadratic S)
    (hstep : AttachedElementaryNielsenTransformation S S') :
    (totalLength S' = totalLength S ∧ cycleCount S' = cycleCount S) ∨
    (totalLength S' = totalLength S - 2 ∧ cycleCount S' = cycleCount S - 1) := sorry

end
