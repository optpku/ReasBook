/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import CombinatorialGroupTheory_Magnus_2004.Chap01.Proposition_1_7_11

universe u

open Finset List SimpleGraph
open scoped BigOperators

set_option autoImplicit false

noncomputable section

section

variable {α : Type u} [DecidableEq α]

-- Layer triage for Proposition 1-7-10:
-- `source-facing`: finite strictly quadratic systems of signed cyclic words, deletion of one
-- adjacent cancellation part `l l⁻¹`, and the Whitehead-graph component count `k(S)`.
-- `core/canonical`: `SignedLetter α` from Proposition `1-7-8`, `Cycle (SignedLetter α)` for the
-- unreduced cyclic-word model, and the reduced-system owner `CyclicWord.Finset.cycleCount` from
-- Proposition `1-7-9`.
-- `bridge/view`: the raw `Cycle` support and edge formulas from Proposition `1-7-11` are reused
-- only because this proposition is genuinely about the unreduced side of the cancellation move;
-- no extra local reduced-system packaging is kept here.
-- Domain sampling:
-- 1. `SignedLetter α` from Proposition `1-7-8` is the shared signed-letter vocabulary for
--    Section 7 cyclic-word constructions.
-- 2. `Cycle.whiteheadEdges` from Proposition `1-7-11` is the raw one-word edge formula reused
--    only because this proposition is stated for unreduced cyclic systems.
-- 3. `Cycle.whiteheadSupport` from Proposition `1-7-11` is the corresponding raw support
--    construction, so the system support is likewise a finite union.
-- 4. `CyclicWord.Finset.cycleCount` from Proposition `1-7-9` is the chapter owner once a system
--    is already reduced, so this file should avoid keeping a parallel reduced-system bridge API.
-- Primitive vs. derived:
-- the primitive data here are only `S`, `S'`, and the signed letter `l`; the Whitehead edges of
-- one word are reused from Proposition `1-7-11`, while system strict quadraticity, the
-- Whitehead graph, and one-step cancellation deletion are derived directly on the raw
-- finite-system owner `Cycle.Finset`.

namespace Cycle
namespace Finset

/-- The total number of occurrences of the basis symbol `x` in the finite system `S`. -/
private def occurrenceCount (S : Finset (Cycle (SignedLetter α))) (x : α) : ℕ :=
  S.sum fun w ↦ w.toMultiset.countP fun a ↦ a.1 = x

/-- A finite system is strictly quadratic when each basis symbol occurs either not at all or
exactly twice. -/
def IsStrictlyQuadratic (S : Finset (Cycle (SignedLetter α))) : Prop :=
  ∀ x : α, occurrenceCount S x = 0 ∨ occurrenceCount S x = 2

/-- The signed generators appearing in the system, together with their formal inverses. -/
private def support (S : Finset (Cycle (SignedLetter α))) : Finset (SignedLetter α) :=
  S.biUnion whiteheadSupport

/-- The Whitehead edges contributed by the whole finite system. -/
private def sigmaEdges (S : Finset (Cycle (SignedLetter α))) :
    Finset (Sym2 (SignedLetter α)) :=
  S.biUnion whiteheadEdges

/-- The finite support vertex type associated to `S`. -/
private abbrev Vertex (S : Finset (Cycle (SignedLetter α))) :=
  { a : SignedLetter α // a ∈ support S }

/-- The support vertices of `S` form a finite type. -/
private instance instFintypeVertex (S : Finset (Cycle (SignedLetter α))) : Fintype (Vertex S) :=
  Fintype.ofFinset (support S) fun _ ↦ by
    simp

/-- The Whitehead graph of the finite system, restricted to its finite support. -/
private def sigmaGraph (S : Finset (Cycle (SignedLetter α))) : SimpleGraph (Vertex S) :=
  fromEdgeSet { e | Sym2.map Subtype.val e ∈ sigmaEdges S }

/-- The quantity `k(S)` is the number of connected components of the system Whitehead graph. -/
noncomputable def cycleCount (S : Finset (Cycle (SignedLetter α))) : ℤ :=
  Int.ofNat (Nat.card (sigmaGraph S).ConnectedComponent)

end Finset

/-- The exceptional two-letter cyclic word `l l⁻¹` before any reduction is performed. -/
def cancellationPair (l : SignedLetter α) : Cycle (SignedLetter α) :=
  ([l, l⁻¹] : List (SignedLetter α))

/-- `DeletesCancellationPartFromWord l w w'` means that `w'` is obtained from `w` by deleting one
adjacent occurrence of the cancellation pair `l l⁻¹` in some representative list of `w`. -/
def DeletesCancellationPartFromWord (l : SignedLetter α)
    (w w' : Cycle (SignedLetter α)) : Prop :=
  ∃ u v : List (SignedLetter α),
    w = ((u ++ l :: l⁻¹ :: v) : List (SignedLetter α)) ∧
      w' = ((u ++ v) : List (SignedLetter α))

namespace Finset

/-- `DeletesCancellationPart S l S'` means that `S'` is obtained from `S` by replacing one member
word with the word obtained by deleting one adjacent occurrence of `l l⁻¹`. -/
def DeletesCancellationPart
    (S : Finset (Cycle (SignedLetter α))) (l : SignedLetter α)
    (S' : Finset (Cycle (SignedLetter α))) : Prop :=
  ∃ w ∈ S, ∃ w',
    DeletesCancellationPartFromWord l w w' ∧ S' = insert w' (erase S w)

end Finset
end Cycle

open Cycle Cycle.Finset

/-- Proposition 1-7-10: if `S` is a finite strictly quadratic system of cyclic words, and `S'` is
obtained from `S` by deleting a part `l l⁻¹`, then `k(S') = k(S) - 1` provided that the
exceptional word `l l⁻¹` is not itself a member of `S`. The source hypothesis that `S` is not
reduced is omitted from the interface because it already follows from the deletion hypothesis. -/
-- Proof sketch: compare the Whitehead graph attached to `S` with the one attached to `S'`.
-- Outside the exceptional case, deleting `l l⁻¹` replaces the local Whitehead-graph contribution
-- of that adjacent inverse pair by a single arc, so the number of connected components drops by
-- exactly one.
theorem cycleCount_eq_sub_one_of_delete_cancellation_part
    (S S' : Finset (Cycle (SignedLetter α))) (l : SignedLetter α)
    (hquad : IsStrictlyQuadratic S)
    (hdelete : DeletesCancellationPart S l S')
    (hnot_exceptional : cancellationPair l ∉ S) :
    cycleCount S' = cycleCount S - 1 := sorry

end
