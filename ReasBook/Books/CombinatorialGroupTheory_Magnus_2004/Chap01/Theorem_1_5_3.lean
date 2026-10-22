/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import CombinatorialGroupTheory_Magnus_2004.Chap01.Proposition_1_4_24

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open MulAction

noncomputable section

section

variable {F : Type u} [Group F]

namespace FreeGroupBasis

/-- The ordered product `x₁^{a₁} x₂^{a₂} ⋯ xₙ^{aₙ}` attached to a finite list of exponents with
respect to the chosen countable basis `basis`. -/
def orderedBasisPowerWord (basis : FreeGroupBasis ℕ F) (exponents : List ℕ) : F :=
  (List.ofFn fun i : Fin exponents.length ↦ basis ((i : ℕ) + 1) ^ exponents[i]).prod

end FreeGroupBasis

/- Theorem 1-5-3 lives in the domain of basis-dependent automorphism orbits in free groups. -/
-- Layer triage:
-- `source-facing`: a free group `F` equipped with a chosen countable basis
-- `basis : FreeGroupBasis ℕ F`, together with exponent lists specifying the words
-- `x₁^{a₁} ⋯ xₘ^{aₘ}` and `x₁^{b₁} ⋯ xₙ^{bₙ}`.
-- `core/canonical`: the owner abstraction `FreeGroupBasis ℕ F` and the orbit relation
-- `orbitRel (MulAut F) F`.
-- `bridge/view`: the concrete model `FreeGroup ℕ` is recovered by specializing
-- `basis := FreeGroupBasis.ofFreeGroup ℕ`.
-- Domain sampling:
-- 1. `FreeGroupBasis ℕ F` is the chapter's owner abstraction for “a free group with a chosen
--    countable basis”.
-- 2. `FreeGroupBasis.ofFreeGroup ℕ` is the canonical basis on the concrete model `FreeGroup ℕ`.
-- 3. `orbitRel (MulAut F) F` is mathlib's owner relation for automorphism-equivalence.
-- 4. `automorphism_orbitRel_iff_exists_automorphism_eq` is the chapter's canonical bridge back
--    to the source existential formulation.
-- Primitive vs. derived:
-- the primitive source data are the chosen basis and the exponent lists; the orbit relation and
-- automorphism-equivalence formulation are derived owner API.

/-- Theorem 1-5-3: for words of the form `x₁^{a₁} ⋯ xₘ^{aₘ}` and `x₁^{b₁} ⋯ xₙ^{bₙ}` with all
exponents at least `2`, the two basis words lie in the same automorphism orbit if and only if the
exponent lists are permutations of one another, equivalently if and only if they have the same
length and the `bᵢ` are a permutation of the `aᵢ`. -/
-- Proof sketch: the forward direction is Whitehead's length-preservation argument for these
-- positive power words, showing that any chain of Whitehead moves preserves the multiplicity data
-- of the exponents after transporting along `basis.repr`. For the reverse direction, a
-- permutation of the chosen basis generators induces the required automorphism.
theorem orderedBasisPowerWord_orbitRel_iff_perm
    (basis : FreeGroupBasis ℕ F) (a b : List ℕ)
    (ha : ∀ n ∈ a, 2 ≤ n)
    (hb : ∀ n ∈ b, 2 ≤ n) :
    orbitRel (MulAut F) F (basis.orderedBasisPowerWord b) (basis.orderedBasisPowerWord a) ↔
      List.Perm a b := sorry

/-- Source-facing reformulation of Theorem 1-5-3 via the chapter's canonical orbit bridge. -/
theorem exists_automorphism_eq_ordered_basis_power_word_iff_perm
    (basis : FreeGroupBasis ℕ F) (a b : List ℕ)
    (ha : ∀ n ∈ a, 2 ≤ n)
    (hb : ∀ n ∈ b, 2 ≤ n) :
    (∃ α : MulAut F, α (basis.orderedBasisPowerWord a) = basis.orderedBasisPowerWord b) ↔
      List.Perm a b := by
  rw [← automorphism_orbitRel_iff_exists_automorphism_eq
    (basis.orderedBasisPowerWord a) (basis.orderedBasisPowerWord b)]
  exact orderedBasisPowerWord_orbitRel_iff_perm basis a b ha hb

end
