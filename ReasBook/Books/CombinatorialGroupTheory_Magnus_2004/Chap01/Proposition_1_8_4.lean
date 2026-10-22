/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import CombinatorialGroupTheory_Magnus_2004.Chap01.Definition_1_4_17

-- Declarations for this item will be appended below by the statement pipeline.

universe u

noncomputable section

variable {X : Type u}

-- Layer triage:
-- `source-facing`: an element `g : FreeGroup X` together with a cyclically reduced conjugate whose
-- canonical cyclic word has the textbook Wicks form `u v w u⁻¹ v⁻¹ w⁻¹`.
-- `core/canonical`: mathlib's owner notion `commutatorSet (FreeGroup X)` for “`g` is a
-- commutator”.
-- `bridge/view`: the chapter owner `CyclicWord X` for cyclically reduced conjugacy data, together
-- with `CyclicWord.conjClassesEquiv` and the cycle quotient `Cycle (X × Bool)`.
-- Domain sampling:
-- 1. `commutatorSet (FreeGroup X)` with `mem_commutatorSet_iff` is the owner abstraction for the
--    statement that `g` is a commutator.
-- 2. `CyclicWord X` from Definition `1-4-17` is the chapter owner abstraction for cyclically
--    reduced words modulo cyclic permutation.
-- 3. `CyclicWord.toConjClasses` is the canonical bridge from a reduced cyclic word to the
--    conjugacy class it represents.
-- 4. `CyclicWord.conjClassesEquiv` is the owner equivalence showing that the cyclic-word witness
--    is canonically determined by the conjugacy class of `g`, so an existential witness should
--    not remain primitive public data.
-- Primitive vs. derived:
-- the primitive data are only the element `g` and the Wicks-form predicate on its canonical cyclic
-- word. The concrete six-block list is bridge-level data inside the cyclic-word owner, and the
-- cyclic-word witness itself is derived from `CyclicWord.conjClassesEquiv`.

namespace CyclicWord

/-- A cyclic word has Wicks triple factorization when one cyclic representative is
`u v w u⁻¹ v⁻¹ w⁻¹`. -/
def HasWicksTripleFactorization (q : CyclicWord X) : Prop :=
  ∃ u v w : List (X × Bool),
    ((u ++ v ++ w ++ FreeGroup.invRev u ++ FreeGroup.invRev v ++ FreeGroup.invRev w :
      List (X × Bool)) : Cycle (X × Bool)) = q.1

end CyclicWord

/-- Proposition 1-8-4: an element of a free group is a commutator exactly when some cyclically
reduced conjugate has cyclic word `u v w u⁻¹ v⁻¹ w⁻¹` for suitable blocks `u`, `v`, and `w`. The
statement is phrased using the canonical cyclic word of the conjugacy class of `g`. -/
-- Proof sketch: for a commutator `g = ⁅a, b⁆`, pass from the conjugacy class of `g` to its
-- canonical cyclic-word representative via `CyclicWord.conjClassesEquiv`, and read that cyclic
-- word in Wicks form. For the converse, a cyclic representative of the displayed six-block form is
-- itself a commutator, and commutatorhood is preserved under conjugacy, so the original element
-- lies in `commutatorSet`.
theorem mem_commutatorSet_iff_exists_reduced_triple_factorization (g : FreeGroup X) :
    g ∈ commutatorSet (FreeGroup X) ↔
      (CyclicWord.conjClassesEquiv.symm
        (ConjClasses.mk g)).HasWicksTripleFactorization :=
  sorry

end
