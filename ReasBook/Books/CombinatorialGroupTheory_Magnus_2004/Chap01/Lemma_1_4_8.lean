/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import CombinatorialGroupTheory_Magnus_2004.Chap01.Proposition_1_4_5

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

noncomputable section

section

variable {F : Type u} [Group F] [IsFreeGroup F]

namespace FreeGroupBasis

/-- Lemma 1-4-8: if `α ∈ IA(F)` and some positive power of `α` is inner, then for every chosen
basis element `basis x` and every lower-central-series term `lowerCentralSeries F n`, there is
some `k` in that term such that `α (basis x)` is conjugate to `(basis x) * k`. -/
-- Layer triage:
-- `source-facing`: a free group `F`, a chosen basis `basis : FreeGroupBasis X F`, an
-- automorphism `α : MulAut F`, a basis element `x : X`, and a lower-central-series index `n`.
-- `core/canonical`: the owner basis object `FreeGroupBasis X F`, the owner homomorphisms
-- `MulAut.abelianization F` and `MulAut.quotient F H`, the lower-central-series owner
-- `lowerCentralSeries F n`, the conjugacy relation `IsConj`, and the inner automorphism owner
-- subgroup `MulAut.innerAutomorphismSubgroup F`.
-- `bridge/view`: the textbook notation `IA(F)` is expressed by `MulAut.IA F`, while the local
-- textbook hypothesis that a power of `α` lies in `JA(F)` is rendered here by the canonical inner
-- automorphism owner `MulAut.innerAutomorphismSubgroup F`.
-- Domain sampling:
-- 1. `FreeGroupBasis X F` in mathlib is the canonical owner abstraction for a chosen free basis.
-- 2. `MulAut.quotient F H` in `Proposition_1_4_5` is the chapter owner action on quotients by a
--    characteristic subgroup.
-- 3. `MulAut.IA F` and `MulAut.innerAutomorphismSubgroup F` are the chapter owner subgroups used
--    for the source-facing `IA(F)` hypothesis and the local inner-power hypothesis.
-- 4. `lowerCentralSeries F n` in mathlib is the canonical descending central series, with each
--    term characteristic.
-- Primitive vs. derived:
-- the primitive data is the chosen basis element and the owner lower-central-series term
-- `lowerCentralSeries F n`; the witness should therefore live in that subgroup itself, while the
-- subgroup conditions are the derived API `MulAut.IA F` and
-- `MulAut.innerAutomorphismSubgroup F`.
-- Proof sketch: induct on `n`. For the induction step, use that `α ∈ IA(F)` makes `α` act
-- trivially on `F_n / F_{n+1}`, while `α ^ N` being inner gives the source-facing `JA(F)`
-- hypothesis used in the Baumslag-Taylor argument. Standard commutator-module structure of
-- `F_n / F_{n+1}` then improves the
-- lower-central-series error term from `F_n` to `F_{n+1}`.
theorem exists_isConj_basisElement_mul_of_mem_IA_of_pow_mem_inner
    {X : Type v} (basis : FreeGroupBasis X F) (α : MulAut F) (x : X) (n : ℕ) {N : ℕ}
    (hN : 0 < N)
    (hIA : α ∈ MulAut.IA F)
    (hInner : α ^ N ∈ JA(F)) :
    ∃ k : lowerCentralSeries F n, IsConj (α (basis x)) (basis x * k) := sorry

end FreeGroupBasis

end
