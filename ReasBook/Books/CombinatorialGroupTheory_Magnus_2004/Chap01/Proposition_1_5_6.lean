/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import CombinatorialGroupTheory_Magnus_2004.Chap01.Proposition_1_4_25

-- Declarations for this item will be appended below by the statement pipeline.

universe u

noncomputable section

section

variable {X : Type u}

open CyclicWord

local instance instDecidableEqBasisSupport_156 : DecidableEq X := Classical.decEq X

/-- The unsigned basis support of the canonical reduced word of a free-group element. -/
abbrev reducedWordSupport (g : FreeGroup X) : Finset X :=
  (g.toWord.map Prod.fst).toFinset

/-- Proposition 1-5-6: if the canonical reduced word of `g : FreeGroup X` has minimal length in
its `Aut(F(X))`-orbit, then every automorphic image of `g` has at least as many distinct basis
letters in its canonical reduced word. Equivalently, if exactly `n` basis letters occur in the
canonical reduced word of `g`, then at least `n` basis letters occur in every automorphic image. -/
-- Layer triage:
-- `source-facing`: an ordinary word of minimal length in its automorphic orbit together with the
-- number of distinct basis letters occurring in it.
-- `core/canonical`: the ambient owner `FreeGroup X`, the canonical reduced-word API
-- `FreeGroup.toWord`, and the automorphism group `MulAut (FreeGroup X)`.
-- `bridge/view`: a reduced list word is represented canonically by the corresponding element of
-- `FreeGroup X`, so support is read from `g.toWord` instead of from an arbitrary representative.
-- Domain sampling:
-- 1. `FreeGroup.toWord` is the owner reduced-word normal form on `FreeGroup X`.
-- 2. `reducedWordSupport g = (g.toWord.map Prod.fst).toFinset` is the source-facing finite
--    support view derived from that owner normal form.
-- 3. `CyclicWord.support` is the owner unsigned-support API derived from `CyclicWord.letters`.
-- 4. `MulAut (FreeGroup X)` is mathlib's owner abstraction for automorphisms of the free group.
-- Primitive vs. derived:
-- the primitive datum is the automorphic-orbit representative `g`; the occurring-basis-letter set
-- and its cardinality are derived from the canonical reduced word `g.toWord`.
-- Proof sketch: use Whitehead peak reduction to factor any automorphism into a chain whose
-- intermediate words never shorten below the minimal length. The first step at which a new basis
-- letter appears would have to be a Whitehead move inserting that letter, which necessarily
-- increases length, contradicting the monotone length bound.
theorem reducedWord_support_card_le_automorphic_image_support_card_of_minimal_length
    (g : FreeGroup X)
    (hmin : ∀ α : MulAut (FreeGroup X), g.toWord.length ≤ (α g).toWord.length)
    (α : MulAut (FreeGroup X)) :
    (reducedWordSupport g).card ≤ (reducedWordSupport (α g)).card := sorry

/-- Cyclic-word companion of the support monotonicity statement: a cyclic word of minimal cyclic
length in its automorphic orbit cannot lose distinct basis letters under an automorphism.
Equivalently, if exactly `n` basis letters occur in `w`, then at least `n` occur in every
automorphic image of `w`. -/
-- Proof sketch: factor the relevant automorphism by Whitehead peak reduction for cyclic words and
-- inspect the first step where a new basis letter would appear. As in the ordinary-word case,
-- that step inserts a new letter and so forces a strict increase in cyclic length.
theorem cyclicWord_support_card_le_automorphic_image_support_card_of_minimal_length
    (w : CyclicWord X)
    (hmin : ∀ α : MulAut (FreeGroup X), w.length ≤ (α • w).length)
    (α : MulAut (FreeGroup X)) :
    (support w).card ≤ (support (α • w)).card := sorry

end
