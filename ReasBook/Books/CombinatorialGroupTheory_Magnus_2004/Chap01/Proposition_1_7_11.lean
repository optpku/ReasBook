/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import CombinatorialGroupTheory_Magnus_2004.Chap01.SignedLetter
import CombinatorialGroupTheory_Magnus_2004.Chap01.Proposition_1_4_25

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open Finset List SimpleGraph
open scoped BigOperators

noncomputable section

section

variable {X : Type u}

local instance instDecidableEqXProp1711 : DecidableEq X := Classical.decEq X

-- Layer triage:
-- `source-facing`: a minimal strictly quadratic cyclic word `q`, a generator `x` occurring in
-- `q`, the specialization `x ↦ 1`, and the Whitehead-graph component count `k(q)`.
-- `core/canonical`: `CyclicWord X` as the chapter owner abstraction for cyclic words,
-- `SignedLetter X` from Proposition `1-7-8` as the Section 7 signed-basis vocabulary,
-- `CyclicWord.length` as the canonical size function, and `CyclicWord.conjClassesEquiv` as the
-- owner bridge that returns the specialized conjugacy class to its reduced cyclic-word
-- representative.
-- `bridge/view`: the specialization and Whitehead graph are derived from the canonical cyclic-word
-- owner, with only the raw `Cycle` edge/support formulas retained as an internal view needed for
-- unreduced downstream constructions.
-- Domain sampling:
-- 1. `CyclicWord X` from Definition `1-4-17` is the chapter owner abstraction for cyclic words.
-- 2. `SignedLetter X` from Proposition `1-7-8` is the established Section 7 owner vocabulary for
--    signed basis letters, so this file reuses it directly.
-- 3. `CyclicWord.length` is the canonical size function on that owner abstraction.
-- 4. `CyclicWord.conjClassesEquiv` from Definition `1-4-17` is the owner equivalence returning
--    a conjugacy class to its canonical reduced cyclic-word representative, and `ConjClasses.map`
--    is the canonical specialization on that owner side.
-- 5. `CyclicWord.letters` and `CyclicWord.HasFullSupport` from Definition `1-4-17` are the owner
--    unsigned-support APIs, so support assumptions should remain separate from the meaning of
--    “minimal strictly quadratic”.
-- Primitive vs. derived:
-- the primitive source data here are the cyclic word `q` and the generator `x`. Signed-letter
-- occurrence counts, strict quadraticity, specialization, the Whitehead graph, and `k(q)` are all
-- derived from the owner cyclic-word API, while the support condition on `x` is expressed through
-- the owner unsigned-letter view `x ∈ q.letters`.

local instance instDecidableEqSignedLetterProp1711 : DecidableEq (SignedLetter X) :=
  Classical.decEq _
local instance instDecidableEqSym2SignedLetterProp1711 :
    DecidableEq (Sym2 (SignedLetter X)) :=
  Classical.decEq _

/-- The ambient free-group endomorphism that sets one generator `x` equal to `1` and fixes every
other generator. -/
private def specializeAtOneHom (x : X) : FreeGroup X →* FreeGroup X :=
  FreeGroup.lift fun y ↦ if y = x then 1 else FreeGroup.of y

namespace CyclicWord

/-- Setting `x ↦ 1` in a cyclic word means applying the ambient specialization to the represented
conjugacy class and then taking its canonical cyclically reduced representative. -/
def specializeAtOne (q : CyclicWord X) (x : X) : CyclicWord X :=
  CyclicWord.conjClassesEquiv.symm <|
    ConjClasses.map (specializeAtOneHom x) (CyclicWord.toConjClasses q)

/-- The number of occurrences of a signed basis letter in a cyclic word. -/
noncomputable def signedOccurrenceCount (q : CyclicWord X) (a : SignedLetter X) : ℕ :=
  letI : DecidableEq (SignedLetter X) := Classical.decEq (SignedLetter X)
  Multiset.count a q.1.toMultiset

/-- A cyclic word is strictly quadratic when each generator occurs equally often with the two
signs and each sign occurs at most once. -/
noncomputable def IsStrictlyQuadratic (q : CyclicWord X) : Prop :=
  ∀ x : X,
    q.signedOccurrenceCount (x, true) = q.signedOccurrenceCount (x, false) ∧
      q.signedOccurrenceCount (x, true) ≤ 1

/-- A cyclic word is minimal strictly quadratic when it has minimal cyclic length in its
automorphism orbit and is strictly quadratic. -/
noncomputable def IsMinimalStrictlyQuadratic (q : CyclicWord X) : Prop :=
  (∀ α : MulAut (FreeGroup X), q.length ≤ (CyclicWord.map α q).length) ∧
    q.IsStrictlyQuadratic

end CyclicWord

private def cyclicEdgesList (L : List (SignedLetter X)) : List (Sym2 (SignedLetter X)) :=
  List.zipWith (fun a b ↦ s(a⁻¹, b)) L (L.rotate 1)

private theorem cyclicEdgesList_toFinset_eq_of_isRotated
    {L₁ L₂ : List (SignedLetter X)} (h : L₁ ~r L₂) :
    (cyclicEdgesList L₁).toFinset = (cyclicEdgesList L₂).toFinset := by
  rcases h with ⟨n, rfl⟩
  have hzip :
      (cyclicEdgesList L₁).rotate n = cyclicEdgesList (L₁.rotate n) := by
    simpa [cyclicEdgesList, List.rotate_rotate, Nat.add_comm] using
      List.zipWith_rotate_distrib (fun a b ↦ s(a⁻¹, b)) L₁ (L₁.rotate 1) n (by simp)
  calc
    (cyclicEdgesList L₁).toFinset = ((cyclicEdgesList L₁).rotate n).toFinset := by
      exact List.toFinset_eq_of_perm _ _ (List.rotate_perm _ _).symm
    _ = (cyclicEdgesList (L₁.rotate n)).toFinset := by
      rw [hzip]

namespace Cycle

/-- The Whitehead edges of a raw cyclic list model. This bridge-level view is used only when a
construction genuinely starts from `Cycle (SignedLetter X)` rather than from the reduced owner
`CyclicWord X`. -/
noncomputable def whiteheadEdges (w : Cycle (SignedLetter X)) :
    Finset (Sym2 (SignedLetter X)) :=
  Quotient.liftOn w (fun L ↦ (cyclicEdgesList L).toFinset) fun _ _ h ↦
    cyclicEdgesList_toFinset_eq_of_isRotated h

/-- The signed letters appearing in a raw cyclic list model, together with their formal
inverses. -/
noncomputable def whiteheadSupport (w : Cycle (SignedLetter X)) : Finset (SignedLetter X) :=
  w.toMultiset.toFinset ∪ (w.map fun a ↦ a⁻¹).toMultiset.toFinset

end Cycle

namespace CyclicWord

/-- The Whitehead edges contributed by one reduced cyclic word. -/
noncomputable def edgesOfWord (q : CyclicWord X) : Finset (Sym2 (SignedLetter X)) :=
  q.1.whiteheadEdges

/-- The signed letters appearing in a reduced cyclic word, together with their formal inverses. -/
noncomputable def wordSupport (q : CyclicWord X) : Finset (SignedLetter X) :=
  q.1.whiteheadSupport

/-- The support vertex type attached to a reduced cyclic word. -/
abbrev Vertex (q : CyclicWord X) :=
  { a : SignedLetter X // a ∈ q.wordSupport }

/-- The support vertices of a reduced cyclic word form a finite type. -/
noncomputable instance instFintypeVertex (q : CyclicWord X) : Fintype (Vertex q) :=
  Fintype.ofFinset q.wordSupport fun _ ↦ by
    simp [wordSupport]

/-- The Whitehead graph of a reduced cyclic word, restricted to its finite support. -/
noncomputable def sigmaGraph (q : CyclicWord X) : SimpleGraph (Vertex q) :=
  fromEdgeSet { e | Sym2.map Subtype.val e ∈ q.edgesOfWord }

/-- The quantity `k(q)` is the number of connected components of the Whitehead graph of `q`. -/
noncomputable def cycleCount (q : CyclicWord X) : ℤ :=
  Int.ofNat (Nat.card q.sigmaGraph.ConnectedComponent)

end CyclicWord

/-- Proposition 1-7-11: if `q` is a minimal strictly quadratic cyclic word and `x` occurs in `q`,
then setting `x` equal to `1` either makes the cyclic length drop by `2` and changes `k` by at
most `1`, or makes the cyclic length drop by `4` and leaves `k` unchanged. -/
-- Proof sketch: analyze the two occurrences of `x` in the Whitehead graph of `q`. If the
-- specialized cyclic word is already reduced after deleting those two letters, then the cyclic
-- length drops by `2`, and the resulting local graph surgery changes the number of connected
-- components by at most `1`. If the deletion creates one cyclic cancellation pair, then the
-- canonical cyclic reduction removes two further letters, so the total drop is `4` and the
-- induced graph surgery preserves the number of components.
theorem specializeAtOne_length_cycleCount_outcome
    (q : CyclicWord X) (x : X) (hq : q.IsMinimalStrictlyQuadratic)
    (hx : x ∈ q.letters) :
    ((CyclicWord.specializeAtOne q x).length = q.length - 2 ∧
        |(CyclicWord.specializeAtOne q x).cycleCount - q.cycleCount| ≤ 1) ∨
      ((CyclicWord.specializeAtOne q x).length = q.length - 4 ∧
        (CyclicWord.specializeAtOne q x).cycleCount = q.cycleCount) := sorry

/-- For a minimal strictly quadratic cyclic word, setting an occurring generator equal to `1`
drops the cyclic length by `2` or by `4`. -/
theorem specializeAtOne_length_eq_sub_two_or_sub_four
    (q : CyclicWord X) (x : X) (hq : q.IsMinimalStrictlyQuadratic)
    (hx : x ∈ q.letters) :
    (CyclicWord.specializeAtOne q x).length = q.length - 2 ∨
      (CyclicWord.specializeAtOne q x).length = q.length - 4 := by
  rcases specializeAtOne_length_cycleCount_outcome q x hq hx with h | h
  · exact Or.inl h.1
  · exact Or.inr h.1

end
