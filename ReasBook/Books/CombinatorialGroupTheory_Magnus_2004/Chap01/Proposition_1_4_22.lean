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

open scoped Whitehead

/-- Proposition 1-4-22: if a cyclic word `w'` is the image of a cyclic word `w` under an
automorphism `α` of the free group and `w'` is no longer than `w`, then `α` factors as a product
of Whitehead automorphisms whose nontrivial prefix images of `w` never exceed the original cyclic
length, and are strictly shorter whenever the terminal image is strictly shorter. -/
-- Layer triage:
-- `source-facing`: the cyclic words `w` and `w'`, the ambient automorphism
-- `α : MulAut (FreeGroup X)`, and Whitehead's generating set `Ω`.
-- `core/canonical`: `CyclicWord X`, its canonical length function `CyclicWord.length`, the
-- `MulAut (FreeGroup X)`-action on cyclic words, and the prefix product API
-- `Whitehead.prefixAut`.
-- `bridge/view`: the textbook right-action notation `w α` is rendered by the canonical left
-- action `α • w`, while membership in `Ω` is rendered by `τ ∈ Ω`.
-- Domain sampling:
-- 1. `CyclicWord` from Definition `1-4-17` is the owner abstraction for reduced cyclic words.
-- 2. The `MulAction (MulAut (FreeGroup X)) (CyclicWord X)` instance from Definition `1-4-17` is
--    the canonical `Aut(F(X))`-action on cyclic words.
-- 3. `Whitehead.automorphisms` from Proposition `1-4-25` is the source-facing owner set `Ω`.
-- 4. `Whitehead.prefixAut` from Proposition `1-4-25` is the owner API for the automorphism given
--    by the first `i` Whitehead factors, composed in the textbook left-to-right order.
-- Primitive vs. derived:
-- the primitive data are only `w`, `w'`, and the ambient automorphism `α`; the individual
-- prefix automorphisms and the intermediate cyclic words are derived from the chosen factor list,
-- so the proposition uses the chapter owner declarations directly instead of introducing a
-- parallel factorization wrapper.
-- Proof sketch: start from a Whitehead factorization of `α` and apply Whitehead peak reduction to
-- eliminate every peak whose cyclic length rises above `|w|`, while keeping the same terminal
-- image `w'`. Since `|w'| ≤ |w|`, every surviving interior prefix has length at most `|w|`, and
-- if `|w'| < |w|` then the first step already drops below `|w|`, forcing every later interior
-- prefix to stay strictly below `|w|` as well.
theorem exists_whitehead_factorization_of_cyclicWord_image_length_le
    (w w' : CyclicWord X) (α : MulAut (FreeGroup X))
    (himage : α • w = w')
    (hlen : w'.length ≤ w.length) :
    ∃ τs : List (MulAut (FreeGroup X)),
      τs.reverse.prod = α ∧
        (∀ τ ∈ τs, τ ∈ Ω) ∧
        (∀ i : ℕ, 0 < i → i < τs.length →
          (Whitehead.prefixAut τs i • w).length ≤ w.length) ∧
        (w'.length < w.length →
          ∀ i : ℕ, 0 < i → i < τs.length →
            (Whitehead.prefixAut τs i • w).length < w.length) := sorry

end
