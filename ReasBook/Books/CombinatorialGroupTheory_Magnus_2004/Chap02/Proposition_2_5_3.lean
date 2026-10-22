/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib

open scoped Monoid.Coprod
open Monoid.Coprod

-- Declarations for this item will be appended below by the statement pipeline.

universe u

section

variable {F : Type u} [Group F]

-- Primary domain: one-relator overgroups of free groups.
-- Layer triage:
-- `source-facing`: a finite ordered family `w : Fin n → F` of nontrivial coefficients in the free
-- group `F`, a parallel family `a : Fin n → ℤ` of nonzero exponents, and the alternating
-- one-variable equation `w₁ t^{a₁} ··· wₙ t^{aₙ} = 1`.
-- `core/canonical`: the owner object for a one-variable equation over `F` is the free product
-- `F ∗ Multiplicative ℤ`, evaluated in an overgroup by
-- `lift φ (zpowersHom G g) : F ∗ Multiplicative ℤ →* G`.
-- `bridge/view`: the source data determine the coproduct equation below; the overgroup witness is
-- still an injective homomorphism `φ : F →* G` together with an element `g : G` at which that
-- source-facing equation evaluates to `1`.
-- Domain sampling:
-- 1. `IsFreeGroup F` is mathlib's owner abstraction for the hypothesis that `F` is free.
-- 2. `F ∗ Multiplicative ℤ` together with `inl`, `inr`, and `lift` is the chapter/mathlib owner
--    API for one-variable words and their evaluation.
-- 3. `zpowersHom G g` is the canonical map sending the free variable to `g`.
-- 4. Proposition `1-8-3` already treats `F ∗ Multiplicative ℤ` as the owner type of one-variable
--    equations, so the local bridge should align with that owner vocabulary rather than introducing
--    a parallel evaluation API.
-- 5. `List.ofFn` and `List.prod` encode the ordered product matching the textbook equation word
--    `w₁ t^{a₁} ··· wₙ t^{aₙ}` inside the coproduct owner.
-- Primitive vs. derived:
-- the primitive source data are the free group `F`, the ordered coefficient family `w`, and the
-- ordered exponent family `a`, assembled directly into the canonical coproduct word
-- `w₁ t^{a₁} ··· wₙ t^{aₙ}`. The overgroup `G`, the injective homomorphism `φ`, and the chosen
-- element `g : G` are witness data in the proposition, and their evaluation map is derived from
-- the owner coproduct API.

/-- The alternating one-variable equation `w₁ t^{a₁} ··· wₙ t^{aₙ}` over `F`, encoded in the
canonical owner `F ∗ Multiplicative ℤ`. -/
def alternatingEquation {n : ℕ} (w : Fin n → F) (a : Fin n → ℤ) : F ∗ Multiplicative ℤ :=
  (List.ofFn fun i ↦ inl (w i) * inr (Multiplicative.ofAdd (a i))).prod

/-- Proposition 2-5-3: if `F` is a free group, `w : Fin n → F` is a family of nontrivial elements,
and `a : Fin n → ℤ` is a family of nonzero integers, then `F` embeds in a group containing an
element `g` for which the alternating word `w₁ t^{a₁} ··· wₙ t^{aₙ}` evaluates to the identity. -/
-- Proof sketch: adjoin a stable letter subject to the single relation
-- `w₁ t^{a₁} ··· wₙ t^{aₙ} = 1`, and then apply the Freiheitssatz for one-relator groups to show
-- that the canonical map from the original free group `F` into the resulting quotient is
-- injective.
theorem exists_embedding_realizing_alternating_relator [IsFreeGroup F] {n : ℕ}
    (w : Fin n → F) (a : Fin n → ℤ) (hw : ∀ i, w i ≠ 1) (ha : ∀ i, a i ≠ 0) :
    ∃ (G : Type u) (_ : Group G) (φ : F →* G),
      Function.Injective φ ∧
        ∃ g : G,
          lift φ (zpowersHom G g) (alternatingEquation w a) = 1 := sorry

end
