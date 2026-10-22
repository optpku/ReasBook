/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import CombinatorialGroupTheory_Magnus_2004.Chap03.Proposition_3_13_1
import Mathlib

-- Declarations for this item are recorded in this dedicated item file.

universe u v w

set_option autoImplicit false

noncomputable section

/-!
Primary domain: Behr-style rewriting for group actions on an integer-valued metric space.

Layer triage:
- `source-facing`: a group action of `G` on `V`, a basepoint `o`, a generator alphabet `X` with
  distinguished subset `X₀`, an integer-valued distance, and the three bounded-word /
  bounded-descent hypotheses used in Behr's rewriting argument.
- `core/canonical`: `[MulAction G V]` is mathlib's owner abstraction for the action, `List X` is
  the source owner for finite positive words, `List.map` together with `List.prod` is the
  canonical concrete evaluation API for such words in the ambient group, and Proposition `3-13-1`
  already provides the owner abstractions `integerClosedBall` and
  `HasBoundedDescendingPathsInBall` for the descending-path condition.
- `bridge/view`: the two helper predicates below express the two bounded-word hypotheses against
  the canonical action.

Domain sampling:
1. `[MulAction G V]` is the mathlib owner abstraction for the action, so the lemma should live
   directly over the instance rather than a second packaged graph structure.
2. `List.map` and `List.prod` are the canonical concrete owner API for evaluating a positive
   `List X` word in `G`; equivalently, this is the `FreeMonoid.lift` evaluation specialized to
   the list model of `FreeMonoid`.
3. `integerClosedBall` together with the notation `S[d](o, l)` is the chapter owner for the
   closed ball `S_l(o)`.
4. `HasBoundedDescendingPathsInBall` is the chapter owner for Behr's bounded descending-path
   hypothesis in a fixed ball.

Primitive vs. derived:
- primitive public data: the action of `G` on `V`, the generator interpretation `X → G`, the
  distinguished subset `X₀ ⊆ X`, the step bound `k`, the basepoint `o`, and the distance
  function `d`;
- derived API: bounded word realizations of short metric steps, bounded distinguished words for
  stabilizer loops, and the resulting correction-word existence theorem.
-/

section

open scoped BehrDistance

variable {G : Type u} {V : Type v} {X : Type w}
variable [Group G] [MulAction G V]

/-- Every metric step of size at most `k` is realized by a positive generator word of length at
most `k`. This is the source-facing bridge from the metric Behr graph to the generator alphabet. -/
def HasBoundedStepWordRealization (generators : X → G) (d : V → V → ℕ) (k : ℕ) : Prop :=
  ∀ ⦃p q : V⦄, d p q ≤ k →
    ∃ letters : List X,
      letters.length ≤ k ∧ (letters.map generators).prod • p = q

/-- Every stabilizer element admits a distinguished positive word representative whose prefixes do
not move the chosen base vertex farther from the origin. -/
def HasBoundedDistinguishedStabilizerWords
    (generators : X → G) (X₀ : Set X) (o : V) (d : V → V → ℕ) : Prop :=
  ∀ ⦃v : V⦄ ⦃a : G⦄, a • v = v →
    ∃ letters : List X,
      (letters.map generators).prod = a ∧
        (∀ x ∈ letters, x ∈ X₀) ∧
        ∀ i, i ≤ letters.length →
          d o (((letters.take i).map generators).prod • v) ≤ d o v

variable (generators : X → G) (X₀ : Set X) (k : ℕ) (o : V) (d : V → V → ℕ)

/-- Lemma 3-13-5: assume Behr's bounded descending-path condition in the ball about `o`, together
with bounded generator realizations of short metric steps and bounded distinguished word
representatives for stabilizer loops. Then whenever `u` is obtained from `v` by the positive word
`g`, there is a correction word whose total product cancels `g`, whose tail
`correction.drop (|g| * k)` lies in `X₀`, and whose prefixes keep the intermediate translates of
`u` inside the radius `max {d(o, v), d(o, u)}`. -/
theorem exists_correction_word_with_bounded_prefix_distance
    (hdesc : ∀ l : ℕ, HasBoundedDescendingPathsInBall d k o l)
    (hstep : HasBoundedStepWordRealization generators d k)
    (hstab : HasBoundedDistinguishedStabilizerWords generators X₀ o d)
    (g : List X) (v u : V) (hu : u = (g.map generators).prod • v) :
    ∃ correction : List X,
      ((g ++ correction).map generators).prod = 1 ∧
        (∀ x ∈ correction.drop (g.length * k), x ∈ X₀) ∧
        ∀ i,
          d o (((correction.take i).map generators).prod • u) ≤
            max (d o v) (d o u) := sorry

end
