/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open scoped Classical

noncomputable section

set_option autoImplicit false

section

variable {G : Type u} [Group G]

namespace FreeGroup

variable {α : Type u}

/-- The canonical reduced-word length on `FreeGroup α`, with the implementation-only
`DecidableEq α` dependency kept internal. -/
noncomputable abbrev reducedWordLength (x : FreeGroup α) : ℕ :=
  let _ : DecidableEq α := Classical.decEq α
  norm x

end FreeGroup

-- Layer triage:
-- `source-facing`: a group `G` equipped with an abstract length function satisfying the textbook
-- axioms `A0` through `A4`.
-- `core/canonical`: `IsFreeGroup G`, `FreeGroup X`, `FreeGroup.norm`, and the canonical free-group
-- basis carried by the generators of `FreeGroup X`.
-- `bridge/view`: `FreeGroup.reducedWordLength`, together with an injective homomorphism
-- `G →* FreeGroup X` whose pullback of that canonical reduced-word length agrees with the given
-- abstract length function on `G`.
-- Domain sampling:
-- 1. `IsFreeGroup G` is mathlib's owner abstraction for the conclusion that `G` is a free group.
-- 2. `FreeGroup X` is the canonical target free group in which the source embedding lands.
-- 3. `FreeGroup.norm` is the canonical reduced-word length relative to the standard basis of
--    `FreeGroup X`, while `FreeGroup.reducedWordLength` is the thin owner-level bridge that hides
--    the proof-only `DecidableEq` implementation detail from public theorem surfaces.
-- 4. `IsFreeGroup.toFreeGroup` is the standard bridge from an abstract free group to its canonical
--    free-group model, so the embedding conclusion is stated directly into `FreeGroup X`.

/-- The overlap term `c(g,h)` attached to a natural-number-valued group length function. -/
def commonInitialLength (length : G → ℕ) (g h : G) : ℕ :=
  (length g + length h - length (g * h⁻¹)) / 2

scoped[AbstractLengthFunction] notation "c[" length "](" g ", " h ")" =>
  commonInitialLength length g h

open scoped AbstractLengthFunction

namespace AbstractLengthFunction

@[simp] theorem commonInitialLength_def (length : G → ℕ) (g h : G) :
    c[length](g, h) = (length g + length h - length (g * h⁻¹)) / 2 :=
  rfl

end AbstractLengthFunction

/-- A natural-number-valued length on `G` satisfying the textbook axioms `A1` through `A4` from
Section `9`. The primitive data is only the function `G → ℕ`; the axioms are recorded as the
owner predicate on that function. -/
class IsCoreAbstractLengthFunction (length : G → ℕ) : Prop where
  /-- Axiom `A1`: only the identity has length `0`. -/
  eq_zero_iff (g : G) : length g = 0 ↔ g = 1
  /-- Axiom `A2`: length is invariant under inversion. -/
  map_inv (g : G) : length g⁻¹ = length g
  /-- Axiom `A3`: the overlap term is integral and is given by the standard half-difference
  formula. -/
  overlap_eq (g h : G) :
    length g + length h = length (g * h⁻¹) + 2 * c[length](g, h)
  /-- Axiom `A4`: the overlap function satisfies the isosceles condition. -/
  overlap_isosceles (g h k : G) :
    c[length](g, h) > c[length](g, k) →
      c[length](h, k) = c[length](g, k)

/-- A natural-number-valued length on `G` satisfying the textbook axioms `A0` through `A4` from
Section `9`. This is the free-group specialization of
`IsCoreAbstractLengthFunction`, obtained by adjoining the square-growth axiom `A0`. -/
class IsAbstractLengthFunction (length : G → ℕ) : Prop
    extends IsCoreAbstractLengthFunction length where
  /-- Axiom `A0`: taking squares strictly increases the length of every nonidentity element. -/
  pow_two_strict (g : G) : g ≠ 1 → length g < length (g ^ 2)

/-- Proposition 1-9-1 (1): a group carrying an abstract length function satisfying axioms `A0`
through `A4` is a free group. -/
-- Proof sketch: first realize the abstract length function as the restriction of the canonical
-- reduced-word length along the embedding provided by the second clause. The image subgroup of a
-- free group is then free by Nielsen-Schreier, and the injective homomorphism identifies `G`
-- with that free subgroup.
theorem isFreeGroup_of_abstractLengthFunction
    (length : G → ℕ) [IsAbstractLengthFunction length] :
    IsFreeGroup G := sorry

private theorem abstractLengthFunction_eq_reducedWordLength_toFreeGroup
    (length : G → ℕ) [IsAbstractLengthFunction length] (g : G) :
    letI : IsFreeGroup G := isFreeGroup_of_abstractLengthFunction length
    length g = FreeGroup.reducedWordLength ((IsFreeGroup.toFreeGroup G) g) := sorry

/- The private bridge above identifies a Section `9` abstract length function with the canonical
reduced-word length on the owner free-group model
`FreeGroup (IsFreeGroup.Generators G)`. -/
-- Proof sketch: combine Proposition `1-9-1` (1) with the realization argument from clause (2),
-- then transport the resulting norm-preserving embedding across the canonical equivalence
-- `IsFreeGroup.toFreeGroup G`.
/-- Proposition 1-9-1 (2): an abstract length function satisfying axioms `A0` through `A4`
comes from restricting the canonical reduced-word length on some free group `FreeGroup X` to an
injective copy of `G`. -/
-- Proof sketch: use the canonical norm-preserving comparison with `IsFreeGroup.toFreeGroup G`,
-- then forget that this owner free-group model was canonical and package it as the existential
-- source-facing embedding requested by the textbook statement.
theorem exists_freeGroup_embedding_preserving_abstractLengthFunction
    (length : G → ℕ) [IsAbstractLengthFunction length] :
    ∃ X : Type u, ∃ φ : G →* FreeGroup X, Function.Injective φ ∧
      ∀ g : G, length g = FreeGroup.reducedWordLength (φ g) := by
  letI : IsFreeGroup G := isFreeGroup_of_abstractLengthFunction length
  refine ⟨IsFreeGroup.Generators G, (IsFreeGroup.toFreeGroup G).toMonoidHom,
    (IsFreeGroup.toFreeGroup G).injective, ?_⟩
  intro g
  simpa using abstractLengthFunction_eq_reducedWordLength_toFreeGroup length g

end
