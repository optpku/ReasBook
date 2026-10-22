/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import CombinatorialGroupTheory_Magnus_2004.Basic
import CombinatorialGroupTheory_Magnus_2004.Chap01.Lemma_1_4_11

-- Declarations for this item will be appended below by the statement pipeline.

universe u

section

variable {F : Type u} [Group F] [IsFreeGroup F]

/-- Proposition 1-4-12: for a free group `F`, if an automorphism `α` acts trivially on the
abelianization and some positive power of `α` is inner, then `α` is inner. Here the textbook
notation `JA(F)` is expressed by the canonical subgroup
`MulAut.innerAutomorphismSubgroup F`. -/
-- Layer triage:
-- `source-facing`: the free group `F`, an automorphism `α : MulAut F`, the IA-subgroup
-- condition, and the textbook conclusion that `α` lies in `JA(F)`, which in this proposition is
-- the subgroup of inner automorphisms.
-- `core/canonical`: `MulAut F`, the canonical IA-subgroup `MulAut.IA F`, the intrinsic primitive
-- element predicate `IsPrimitiveElement`, and the canonical inner automorphism subgroup
-- `MulAut.innerAutomorphismSubgroup F`.
-- `bridge/view`: Lemma `1-4-11` gives the basis-level conjugacy statement, while the textbook
-- symbol `JA(F)` is rendered by the chapter's owner declaration
-- `MulAut.innerAutomorphismSubgroup F`.
-- Domain sampling:
-- 1. `MulAut.IA F` in `Proposition_1_4_5` is the project's canonical subgroup of automorphisms
--    acting trivially on the abelianization.
-- 2. `MulAut.conj : F →* MulAut F` in mathlib is the canonical inner-automorphism map.
-- 3. `IsPrimitiveElement` in `CombinatorialGroupTheory.Basic` is the project's intrinsic owner
--    for elements belonging to some free basis.
-- 4. `MulAut.innerAutomorphismSubgroup F` is the chapter owner abstraction for the subgroup of
--    inner automorphisms.
-- Primitive vs. derived:
-- the primitive public inputs are only `α`, the positive integer `N : ℕ+`, and the membership
-- hypotheses in `MulAut.IA F` and the inner-automorphism subgroup; no chosen basis or rank data
-- belongs in the statement header.
-- Proof sketch: first upgrade Lemma `1-4-11` from basis elements to the intrinsic primitive
-- elements of `F`. The Baumslag-Taylor argument then compares primitive pairs to show that all of
-- these conjugacies are realized by one common group element, so `α` itself is conjugation by
-- that element.
private theorem isConj_primitive_of_mem_IA_of_pow_mem_inner
    (α : MulAut F) (N : ℕ+) {p : F} (hp : IsPrimitiveElement p)
    (hIA : α ∈ MulAut.IA F)
    (hInner : α ^ (N : ℕ) ∈ JA(F)) :
    IsConj (α p) p := by
  rcases hp with ⟨X, basis, x, rfl⟩
  simpa using isConj_basisElement_of_mem_IA_of_pow_mem_inner basis α x N.2 hIA hInner

private theorem mem_inner_of_maps_primitive_to_conjugates
    (α : MulAut F)
    (hprimitive : ∀ {p : F}, IsPrimitiveElement p → IsConj (α p) p) :
    α ∈ JA(F) := by
  sorry

theorem mem_inner_of_mem_IA_of_pow_mem_inner
    (α : MulAut F) (N : ℕ+)
    (hIA : α ∈ MulAut.IA F)
    (hInner : α ^ (N : ℕ) ∈ JA(F)) :
    α ∈ JA(F) := by
  refine mem_inner_of_maps_primitive_to_conjugates α fun hp ↦ ?_
  exact isConj_primitive_of_mem_IA_of_pow_mem_inner α N hp hIA hInner

end
