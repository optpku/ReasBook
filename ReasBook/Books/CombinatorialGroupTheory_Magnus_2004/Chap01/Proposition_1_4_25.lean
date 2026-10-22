/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import CombinatorialGroupTheory_Magnus_2004.Chap01.Definition_1_4_17
import CombinatorialGroupTheory_Magnus_2004.Chap01.SignedLetter

universe u

noncomputable section

section

variable {X : Type u}

-- Domain sampling for Whitehead automorphisms:
-- 1. `MulAut (FreeGroup X)` is the owner abstraction for automorphisms of the ambient free group.
-- 2. `SignedLetter X` is the project owner vocabulary for signed basis letters.
-- 3. `FreeGroup.mk [x]` is the canonical ambient free-group element represented by one signed
--    letter `x : SignedLetter X`.
-- 4. `SignedLetter` carries the owner involution on signed letters, written as `x⁻¹`.
-- Primitive data for Whitehead automorphisms of the second kind are therefore a multiplier
-- `a : SignedLetter X` together with a subset `A ⊆ X^{±1}` satisfying the textbook constraints
-- `a ∈ A` and `a⁻¹ ∉ A`; the four word-shapes are derived from the membership pattern of
-- `x` and `x⁻¹`.

/- Whitehead's textbook generating set is written `Ω`; membership is the canonical surface
`τ ∈ Ω`. -/
namespace Whitehead

open Classical in
/-- The canonical image of a signed basis letter under Whitehead's second-kind automorphism
determined by multiplier `a` and subset `A ⊆ X^{±1}`. The special letters `a` and `a⁻¹` are
fixed; for every other signed letter, the usual four Whitehead cases are derived from the
membership pattern of `x` and `x⁻¹` in `A`. -/
private def typeTwoImage (a : SignedLetter X) (A : Set (SignedLetter X))
    (x : SignedLetter X) : FreeGroup X :=
  if x = a ∨ x = a⁻¹ then
    FreeGroup.mk [x]
  else if x ∈ A then
    if x⁻¹ ∈ A then
      (FreeGroup.mk [a])⁻¹ * FreeGroup.mk [x] * FreeGroup.mk [a]
    else
      FreeGroup.mk [x] * FreeGroup.mk [a]
  else if x⁻¹ ∈ A then
    (FreeGroup.mk [a])⁻¹ * FreeGroup.mk [x]
  else
    FreeGroup.mk [x]

/-- Whitehead's generating set `Ω` of automorphisms of the free group on `X`. Membership is given
by the textbook disjunction between first-kind and second-kind Whitehead automorphisms. -/
def automorphisms : Set (MulAut (FreeGroup X)) := {τ |
  (∃ σ : Equiv.Perm X, ∃ ε : X → Bool,
      ∀ x : X,
        τ (FreeGroup.of x) = if ε x then FreeGroup.of (σ x) else (FreeGroup.of (σ x))⁻¹) ∨
    ∃ a : SignedLetter X, ∃ A : Set (SignedLetter X),
      a ∈ A ∧ a⁻¹ ∉ A ∧
        ∀ x : SignedLetter X, τ (FreeGroup.mk [x]) = typeTwoImage a A x}

scoped[Whitehead] notation "Ω" => automorphisms

/-- The automorphism given by the first `i` listed Whitehead factors, applied from left to right.
Thus the prefix `[τ₁, …, τᵢ]` acts as `τᵢ * ··· * τ₁`. -/
abbrev prefixAut (τs : List (MulAut (FreeGroup X))) (i : ℕ) : MulAut (FreeGroup X) :=
  (τs.take i).reverse.prod

end Whitehead

open scoped Whitehead

/-- Proposition 1-4-25: if the automorphic image of a finite family of cyclic words under `α` has
minimal total cyclic length among all automorphic images, then `α` admits a factorization into
Whitehead automorphisms such that the successive prefix images strictly decrease total cyclic
length until the terminal minimum is reached, and thereafter keep that minimum fixed. -/
-- Layer triage:
-- `source-facing`: the finite family `w : ι → CyclicWord X`, the automorphism
-- `α : MulAut (FreeGroup X)`, and the source set `Ω` of Whitehead automorphisms.
-- `core/canonical`: `CyclicWord X`, the owner automorphism group `MulAut (FreeGroup X)`, its
-- induced `MulAction` on `CyclicWord X` and on finite families `ι → CyclicWord X`, together
-- with ordinary `Fintype` sums of cyclic lengths.
-- `bridge/view`: `CyclicWord.map` transports the canonical action on conjugacy classes back to
-- reduced cyclic words, while `Whitehead.automorphisms` is the source-facing owner set `Ω`.
-- Domain sampling:
-- 1. `CyclicWord.toConjClasses` is the chapter's owner map from cyclic words to conjugacy classes.
-- 2. `CyclicWord.conjClassesEquiv` is the canonical equivalence used to transport the
--    automorphism action from conjugacy classes back to cyclic words.
-- 3. `ConjClasses.map` in mathlib is the canonical action of a homomorphism on conjugacy classes.
-- 4. The induced Pi-action gives the canonical owner action on finite families
--    `ι → CyclicWord X`, and `CyclicWord.totalLength` is already stated for arbitrary
--    `[Fintype ι]`, so no `Fin t`-specific family owner belongs in the public API here.
-- 5. `SignedLetter X` is the project owner vocabulary for letters of `X^{±1}`.
-- 6. `MulAut (FreeGroup X)` is the owner abstraction for automorphisms of the free group, while
--    the prefix dynamics are derived from `Whitehead.prefixAut`, the induced Pi-action, and
--    ordinary `Fintype` sums.
-- Primitive vs. derived:
-- the primitive data is the family of cyclic words together with the ambient free-group
-- automorphism `α`; the terminal family `α • w`, the cyclic-word action, the total-length
-- functional, and the prefix-stage lengths are derived.
theorem exists_whitehead_factorization_of_minimal_cyclic_word_total_length
    {ι : Type*} [Fintype ι] (w : ι → CyclicWord X) (α : MulAut (FreeGroup X))
    (hmin : ∀ α' : MulAut (FreeGroup X),
      CyclicWord.totalLength (α • w) ≤ CyclicWord.totalLength (α' • w)) :
    ∃ τs : List (MulAut (FreeGroup X)),
      τs.reverse.prod = α ∧
        (∀ τ ∈ τs, τ ∈ Ω) ∧
        ∀ i : ℕ, i < τs.length →
          let prefixLength := CyclicWord.totalLength (Whitehead.prefixAut τs i • w)
          let nextLength := CyclicWord.totalLength (Whitehead.prefixAut τs (i + 1) • w)
          let targetLength := CyclicWord.totalLength (α • w)
          nextLength ≤ prefixLength ∧
            (prefixLength ≠ targetLength → nextLength < prefixLength) := by
  sorry

end
