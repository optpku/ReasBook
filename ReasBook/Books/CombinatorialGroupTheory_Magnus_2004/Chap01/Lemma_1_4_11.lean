/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import CombinatorialGroupTheory_Magnus_2004.Chap01.Lemma_1_4_8
import CombinatorialGroupTheory_Magnus_2004.Chap01.Proposition_1_4_10

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

section

open QuotientGroup

variable {F : Type u} [Group F] [IsFreeGroup F]

/-- Lemma 1-4-11: if `α ∈ IA(F)` and some positive power of `α` is inner, then `α` sends every
chosen basis element of `F` to a conjugate of itself. -/
-- Layer triage:
-- `source-facing`: a free group `F`, a chosen basis `basis : FreeGroupBasis X F`, an
-- automorphism `α : MulAut F`, and a basis element `x : X`.
-- `core/canonical`: the owner homomorphisms `MulAut.abelianization F` and
-- `MulAut.quotient F H`, the lower-central-series owner `lowerCentralSeries F`, the chosen
-- free-basis object `FreeGroupBasis X F`, the conjugacy relation `IsConj`, and the inner
-- automorphism owner subgroup `MulAut.innerAutomorphismSubgroup F`.
-- `bridge/view`: the textbook notation `IA(F)` is expressed by `MulAut.IA F`, while the local
-- inner-power hypothesis is rendered by `MulAut.innerAutomorphismSubgroup F`.
-- Domain sampling:
-- 1. `MulAut.IA F` and `MulAut.innerAutomorphismSubgroup F` in `Proposition_1_4_5` are the owner
--    subgroup declarations used in the surrounding section.
-- 2. `MulAut.quotient F H` in `Proposition_1_4_5` is the owner action on quotients by
--    characteristic subgroups.
-- 3. `lowerCentralSeries F n` in mathlib is the canonical lower-central-series owner, with each
--    term characteristic.
-- 4. `MonoidHom.map_isConj` in mathlib is the owner transport of conjugacy along quotient maps.
-- Primitive vs. derived:
-- the primitive data is the owner action `MulAut.quotient F H` on a quotient by a characteristic
-- subgroup `H`; the lower-central-series specialization and the subgroup conditions
-- `MulAut.IA F` and `MulAut.innerAutomorphismSubgroup F` are derived API.
-- Proof sketch: apply Lemma `1-4-8` to see that for every `n`, the element `α (basis x)` is
-- conjugate to `(basis x) * k` with `k ∈ lowerCentralSeries F n`. If `α (basis x)` were not
-- conjugate to `basis x`, Proposition `1-4-10` would separate their conjugacy classes in some
-- quotient `F ⧸ lowerCentralSeries F n`, contradicting the previous sentence because `k` dies in
-- that quotient.
theorem isConj_basisElement_of_mem_IA_of_pow_mem_inner
    {X : Type v} (basis : FreeGroupBasis X F) (α : MulAut F) (x : X) {N : ℕ}
    (hN : 0 < N)
    (hIA : α ∈ MulAut.IA F)
    (hInner : α ^ N ∈ JA(F)) :
    IsConj (α (basis x)) (basis x) := by
  by_contra hconj
  obtain ⟨n, hn⟩ :=
    exists_lowerCentralSeries_quotient_separating_nonconjugate (α (basis x)) (basis x) hconj
  obtain ⟨k, hkconj⟩ :=
    basis.exists_isConj_basisElement_mul_of_mem_IA_of_pow_mem_inner α x n hN hIA hInner
  exact hn <| by
    simpa [k.2] using (mk' (Subgroup.lowerCentralSeries F n)).map_isConj hkconj

end
