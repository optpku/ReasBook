/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import CombinatorialGroupTheory_Magnus_2004.Chap01.Proposition_1_7_4

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

noncomputable section

section

variable {X : Type u} {F : Type v} [Group F]

local instance proposition_1_7_5_decidableEq : DecidableEq X := Classical.decEq X

-- Layer triage:
-- `source-facing`: finite connected quadratic word sets over a chosen free basis that are not
-- strictly quadratic.
-- `core/canonical`: `FreeGroupBasis X F`, `IsQuadraticWordSet`, `wordIncidenceGraph`, and
-- `MulAut F`.
-- `bridge/view`: `basisWordLetters`, `basisLetterOccurs`, and `generatorFiber` from
-- Proposition `1-7-4` are the owner-derived reduced-word occurrence API; the strictness predicate
-- below records that each basis generator occurs in either zero or two words of the set, matching
-- the textbook distinction between quadratic and strictly quadratic families.
--
-- Domain sampling:
-- 1. `FreeGroupBasis X F` is the owner abstraction for the chosen basis of the ambient free group.
-- 2. `IsQuadraticWordSet` and `wordIncidenceGraph` from Proposition `1-7-4` are the source-facing
--    owner declarations for quadratic families and their connectivity graph in this section.
-- 3. `generatorFiber basis S x` is the canonical derived owner view of the words of `S`
--    containing a given basis letter.
-- 4. The chosen basis subset of `F` is the canonical owner expression `Set.range basis`.

/-- A quadratic word set is strictly quadratic when every basis generator occurs in either zero or
two words of the set. -/
def IsStrictlyQuadraticWordSet (basis : FreeGroupBasis X F) (S : Set F) : Prop :=
  ∀ x : X, (generatorFiber basis S x).encard = 0 ∨ (generatorFiber basis S x).encard = 2

/-- A quadratic but not strictly quadratic word set has some basis generator that occurs in
exactly one word. -/
-- Proof sketch: choose a generator for which the strict `0-or-2` alternative fails. The quadratic
-- hypothesis bounds its incidence fiber by `2`, so the only remaining cardinal possibility is
-- `1`.
theorem exists_generatorFiber_encard_eq_one_of_quadratic_not_strictlyQuadratic
    (basis : FreeGroupBasis X F) (S : Set F) (hquadratic : IsQuadraticWordSet basis S)
    (hnotstrict : ¬ IsStrictlyQuadraticWordSet basis S) :
    ∃ x : X, (generatorFiber basis S x).encard = 1 := by
  classical
  have hnotstrict' :
      ¬ ∀ x : X, (generatorFiber basis S x).encard = 0 ∨ (generatorFiber basis S x).encard = 2 := by
    simpa [IsStrictlyQuadraticWordSet] using hnotstrict
  obtain ⟨x, hx⟩ := not_forall.mp hnotstrict'
  rw [not_or] at hx
  have hxle := quadraticWordSet_generatorFiber_encard_le_two basis S hquadratic x
  obtain ⟨n, hn, hnle⟩ := ENat.le_coe_iff.mp hxle
  have hn0 : n ≠ 0 := by
    intro h0
    apply hx.1
    simp [hn, h0]
  have hn2 : n ≠ 2 := by
    intro h2
    apply hx.2
    simp [hn, h2]
  interval_cases n
  · contradiction
  · exact ⟨x, hn⟩
  · contradiction

/-- Proposition 1-7-5: if `S` is quadratic over the chosen basis, not strictly quadratic, finite,
and connected, then some automorphism of `F` sends `S` into the chosen basis subset. -/
-- Proof sketch: choose a basis generator `x₀` occurring in exactly one word of `S`, orient the
-- finite incidence tree toward that distinguished word, and use the descending-chain argument from
-- Proposition `1-7-3` to build an automorphism whose image of `S` lies in the basis subset.
theorem exists_automorphism_image_subset_basis_range_of_quadratic_connected_finite_nonstrict
    (basis : FreeGroupBasis X F) (S : Set F)
    (hquadratic : IsQuadraticWordSet basis S)
    (hnotstrict : ¬ IsStrictlyQuadraticWordSet basis S) (hfinite : S.Finite)
    (hconnected : (wordIncidenceGraph basis S).Connected) :
    ∃ α : MulAut F, α '' S ⊆ Set.range basis := sorry

end
