/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import CombinatorialGroupTheory_Magnus_2004.Chap01.Proposition_1_4_1

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

open MulAction

section

variable {F : Type u} [Group F]

/-- The canonical automorphism-orbit relation recovers the textbook automorphism-equivalence
predicate. -/
-- Layer triage:
-- `source-facing`: two elements `w₁ w₂ : F` and the question whether some automorphism sends
-- `w₁` to `w₂`.
-- `core/canonical`: `orbitRel (MulAut F) F`.
-- `bridge/view`: the existential automorphism formulation is recovered by this theorem.
-- Domain sampling:
-- 1. `MulAut F` is mathlib's owner automorphism group of `F`.
-- 2. `orbitRel (MulAut F) F` is mathlib's owner relation for automorphism-equivalence.
-- 3. `mem_orbit_iff` is the canonical bridge from an orbit statement to the existence of a group
--    element realizing it.
theorem automorphism_orbitRel_iff_exists_automorphism_eq (w₁ w₂ : F) :
    orbitRel (MulAut F) F w₂ w₁ ↔
      ∃ α : MulAut F, α w₁ = w₂ := by
  rw [orbitRel_apply, mem_orbit_iff]
  constructor
  · rintro ⟨α, hα⟩
    exact ⟨α, by simpa using hα⟩
  · rintro ⟨α, hα⟩
    exact ⟨α, by simpa using hα⟩

end

noncomputable section

section FiniteBasisSearch

variable {ι : Type v} {F : Type u} [Group F]

private def signedBasisLetters (ι : Type v) [Fintype ι] : List (ι × Bool) :=
  ((Fintype.elems : Finset ι).toList).flatMap fun a ↦ [(a, false), (a, true)]

private def basisWordsOfLength (ι : Type v) [Fintype ι] : ℕ → List (List (ι × Bool))
  | 0 => [[]]
  | n + 1 =>
      (basisWordsOfLength ι n).flatMap fun w ↦ (signedBasisLetters ι).map fun a ↦ a :: w

private def basisElementsUpToNorm (basis : FreeGroupBasis ι F) [Finite ι] [DecidableEq ι]
    [DecidableEq F] (m : ℕ) : Finset F := by
  let _ : Fintype ι := Fintype.ofFinite ι
  exact
    (((List.range (m + 1)).flatMap (basisWordsOfLength ι)).map fun w ↦
      basis.repr.symm (FreeGroup.mk w)).toFinset

private def elementaryNielsenGenerators (basis : FreeGroupBasis ι F) [Finite ι] [DecidableEq ι] :
    Finset (MulAut F) := by
  classical
  let _ : Fintype ι := Fintype.ofFinite ι
  let inversions :=
    ((Fintype.elems : Finset ι).toList).map (basis.elementaryNielsenInversion)
  let transvections :=
    (Fintype.elems : Finset {p : ι × ι // p.1 ≠ p.2}).toList.map
      (fun xy ↦ basis.elementaryNielsenTransvection xy.1.1 xy.1.2 xy.2)
  exact (inversions ++ transvections ++ transvections.map (·⁻¹)).toFinset

private def nextOrbitStates [DecidableEq F] (gens : Finset (MulAut F))
    (candidates states : Finset F) : Finset F :=
  states.biUnion fun w ↦ (gens.image fun σ ↦ σ w).filter fun u ↦ u ∈ candidates

private def reachableOrbitStates [DecidableEq F] (gens : Finset (MulAut F))
    (candidates : Finset F) (w : F) : ℕ → Finset F
  | 0 => {w}
  | n + 1 =>
      let states := reachableOrbitStates gens candidates w n
      states ∪ nextOrbitStates gens candidates states

private noncomputable def automorphismOrbitSearch (basis : FreeGroupBasis ι F) [Finite ι]
    [DecidableEq ι] [DecidableEq F] (w₁ w₂ : F) : Bool := by
  let m := max (FreeGroup.norm (basis.repr w₁)) (FreeGroup.norm (basis.repr w₂))
  let candidates := basisElementsUpToNorm basis m
  let gens := elementaryNielsenGenerators basis
  exact decide (w₂ ∈ reachableOrbitStates gens candidates w₁ candidates.card)

/-- Internal bounded-search specification for Proposition 1-4-24: with respect to a chosen finite
free basis, the automorphism orbit problem is detected by exploring the finite graph of words of
bounded basis length under elementary Nielsen generators. -/
-- Layer triage:
-- `source-facing`: the words `w₁`, `w₂` in a finite-rank free group.
-- `core/canonical`: `orbitRel (MulAut F) F` and the owner basis object `FreeGroupBasis ι F`.
-- `bridge/view`: the search graph is built from elementary Nielsen generators relative to `basis`.
-- Domain sampling:
-- 1. `MulAut F` is mathlib's owner automorphism group.
-- 2. `orbitRel (MulAut F) F` is the owner automorphism-equivalence relation.
-- 3. `FreeGroupBasis ι F` is the chapter/mathlib owner abstraction for a chosen free basis.
-- 4. Proposition `1-4-1` identifies elementary Nielsen automorphisms as the canonical finite-rank
--    generating family of `Aut(F)`.
private theorem automorphism_orbitRel_iff_search_true (basis : FreeGroupBasis ι F) [Finite ι]
    [DecidableEq ι] [DecidableEq F] (w₁ w₂ : F) :
    orbitRel (MulAut F) F w₂ w₁ ↔
      automorphismOrbitSearch basis w₁ w₂ = true := by
  sorry

end FiniteBasisSearch

section AbstractFreeGroup

variable {F : Type u} [Group F] [IsFreeGroup F] [Finite (IsFreeGroup.Generators F)]

/-- Proposition 1-4-24: for a finitely generated free group `F`, it is decidable whether two
elements lie in the same automorphism orbit. -/
-- Layer triage:
-- `source-facing`: the ambient finite-rank free group `F` and the two elements `w₁` and `w₂`.
-- `core/canonical`: `orbitRel (MulAut F) F`.
-- `bridge/view`: `automorphism_orbitRel_iff_exists_automorphism_eq` recovers the textbook
-- existential formulation, while the internal search theorem
-- `automorphism_orbitRel_iff_search_true` realizes Whitehead-style finite-rank decidability using
-- the canonical basis `IsFreeGroup.basis F`.
-- Primitive vs. derived:
-- the primitive public inputs are just `w₁` and `w₂`; the chosen finite basis and the bounded
-- search graph are derived implementation data and stay out of the public interface.
noncomputable def automorphism_orbitRel_decidable (w₁ w₂ : F) :
    Decidable (orbitRel (MulAut F) F w₂ w₁) := by
  let _ : DecidableEq (IsFreeGroup.Generators F) := Classical.decEq _
  let _ : DecidableEq F := Classical.decEq _
  let basis : FreeGroupBasis (IsFreeGroup.Generators F) F := IsFreeGroup.basis F
  exact
    decidable_of_iff
      (automorphismOrbitSearch basis w₁ w₂ = true)
      (automorphism_orbitRel_iff_search_true basis w₁ w₂).symm

end AbstractFreeGroup

end
