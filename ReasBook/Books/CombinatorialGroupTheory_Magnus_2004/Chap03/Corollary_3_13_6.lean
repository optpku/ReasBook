/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import CombinatorialGroupTheory_Magnus_2004.Chap03.Lemma_3_13_5

universe u v w

set_option autoImplicit false

noncomputable section

/-!
Primary domain: short-word specializations of Behr correction words.

Layer triage:
- `source-facing`: the canonical action of `G` on `V`, a positive generator word `g : List X` of
  length at most `3`, the endpoints `v` and `u`, and the same bounded-step / bounded-stabilizer /
  bounded-descent hypotheses as in Lemma `3-13-5`.
- `core/canonical`: `exists_correction_word_with_bounded_prefix_distance` from Lemma `3-13-5` is
  the chapter owner theorem for the correction-word construction.
- `bridge/view`: this corollary is the thin short-word specialization replacing the general tail
  threshold `g.length * k` by the uniform bound `3 * k`.

Domain sampling:
1. `[MulAction G V]` is the owner action abstraction inherited from Lemma `3-13-5`.
2. `List.map` together with `List.prod` is the canonical concrete evaluation API for a positive
   `List X` word in the ambient group.
3. `S[d](o, l)` from Proposition `3-13-1` is the chapter owner notation for the source ball
   condition used in `hdesc`.
4. `exists_correction_word_with_bounded_prefix_distance` is the owner theorem specialized here.

Primitive vs. derived:
- primitive public data: the action, generators, distinguished subset, step bound, basepoint,
  distance, short positive word `g`, vertices `v` and `u`, and the endpoint hypothesis `hu`;
- derived API: the corollary's uniform `3 * k` bound on the distinguished tail of the correction
  word.
-/

section

open scoped BehrDistance

variable {G : Type u} {V : Type v} {X : Type w}
variable [Group G] [MulAction G V]

variable (generators : X → G) (X₀ : Set X) (k : ℕ) (o : V) (d : V → V → ℕ)
variable
  (hdesc :
    ∀ l : ℕ,
      ∀ ⦃p q : V⦄,
        p ∈ S[d](o, l) →
          q ∈ S[d](o, l) →
            HasBoundedDescendingPathInBall d k o l p q)
  (hstep : HasBoundedStepWordRealization generators d k)
  (hstab : HasBoundedDistinguishedStabilizerWords generators X₀ o d)

include hdesc hstep hstab

/-- Corollary 3-13-6: for a positive generator word of length at most `3`, the correction word
from Lemma `3-13-5` may be chosen with the same bounded-prefix-distance control, and every letter
in the tail `correction.drop (3 * k)` lies in the distinguished subset `X₀`. -/
theorem exists_correction_word_with_bounded_prefix_distance_of_length_le_three
    (g : List X) (v u : V) (hg : g.length ≤ 3) (hu : u = (g.map generators).prod • v) :
    ∃ correction : List X,
      ((g ++ correction).map generators).prod = 1 ∧
        (∀ x ∈ correction.drop (3 * k), x ∈ X₀) ∧
        ∀ i,
          d o (((correction.take i).map generators).prod • u) ≤
            max (d o v) (d o u) := by
  rcases exists_correction_word_with_bounded_prefix_distance
      generators X₀ k o d hdesc hstep hstab g v u hu with
    ⟨correction, hprod, htail, hprefix⟩
  refine ⟨correction, hprod, ?_, hprefix⟩
  intro x hx
  have hle : g.length * k ≤ 3 * k := Nat.mul_le_mul_right k hg
  have hx' :
      x ∈ (correction.drop (g.length * k)).drop (3 * k - g.length * k) := by
    rw [List.drop_drop, Nat.add_sub_of_le hle]
    exact hx
  exact htail x (List.mem_of_mem_drop hx')

end
