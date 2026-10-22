/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import CombinatorialGroupTheory_Magnus_2004.Chap01.Proposition_1_6_8

-- Declarations for this item will be appended below by the statement pipeline.

universe u

section

variable {F : Type u} [Group F]

namespace FreeGroupBasis

-- Layer triage:
-- `source-facing`: a chosen basis of `F` with `2n` basis elements grouped into `n` ordered
-- pairs, a positive-rank hypothesis `0 < n`, together with a product of `m` squares representing
-- the corresponding product of paired commutators.
-- `core/canonical`: the owner abstraction `FreeGroupBasis (Fin n ⊕ Fin n) F`, the owner-derived
-- paired-commutator element `basis.pairedCommutatorProduct` from Proposition `1-6-8`, and finite
-- families `Fin m → F`.
-- `bridge/view`: the textbook basis elements `x₁, …, x₂n` are encoded by the two summands of
-- `Fin n ⊕ Fin n`, so pair `i` is `(basis (.inl i), basis (.inr i))`.
-- Domain sampling:
-- 1. `FreeGroupBasis (Fin n ⊕ Fin n) F` is the chapter and mathlib owner abstraction for a
--    chosen free basis grouped into `n` ordered pairs.
-- 2. `basis.pairedCommutatorProduct` from Proposition `1-6-8` is the chapter owner-derived
--    element encoding the textbook product `∏[i < n] [x₂i₊₁, x₂i₊₂]`.
-- 3. `basis.repr : F ≃* FreeGroup (Fin n ⊕ Fin n)` is the canonical transport to the standard
--    free-group model behind the textbook normal-form arguments.
-- 4. Proposition `1-6-8`, `genus_le_of_commutator_product_eq`, already uses the same owner
--    abstraction for paired commutator products, so this item should refine to that same basis
--    interface rather than introducing a parallel wrapper.
-- Primitive vs. derived:
-- the primitive source data are the chosen basis, the positive rank `n`, and the finite family of
-- square factors; the paired basis commutators are derived directly from the owner indexing type
-- `Fin n ⊕ Fin n`.
/-- Proposition 1-6-10: for positive rank `n`, the paired commutator product determined by a basis
of `F` can be written as a product of `m` squares if and only if `m ≥ 2n + 1`. -/
-- Proof sketch: for existence when `m = 2n + 1`, combine the classical rank-two identity
-- `[x₁, x₂] = u₁² u₂² v²` with the standard three-square decomposition of `a² [b, c]` and
-- iterate over the `n` commutator pairs. For the converse, pass to the quotient
-- `F / F'' (F')²`, record the square factors by a matrix over `ZMod 2`, and compare ranks of
-- `A * Aᵀ` and `A`.
theorem pairedCommutatorProduct_eq_square_product_iff
    {n m : ℕ}
    (basis : FreeGroupBasis (Fin n ⊕ Fin n) F)
    (hn : 0 < n) :
    (∃ u : Fin m → F,
      basis.pairedCommutatorProduct =
        (List.ofFn fun j ↦ u j ^ 2).prod) ↔
      2 * n + 1 ≤ m := sorry

end FreeGroupBasis

end
