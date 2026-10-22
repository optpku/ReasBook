/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open scoped commutatorElement

section

variable {F : Type u} [Group F]

namespace FreeGroupBasis

-- Layer triage:
-- `source-facing`: a chosen basis of `F` with `2g` elements grouped into `g` ordered pairs, and
-- an equality between the corresponding product of `g` commutators and a product of `m`
-- commutators built from an arbitrary finite family of pairs of elements.
-- `core/canonical`: the owner abstraction `FreeGroupBasis (Fin g ⊕ Fin g) F` for the basis and
-- the standard commutator-element notation `⁅a, b⁆`.
-- `bridge/view`: the textbook list `x_1, ..., x_{2g}` is represented by the two summands of
-- `Fin g ⊕ Fin g`, so pair `i` is `(basis (Sum.inl i), basis (Sum.inr i))`.
-- Domain sampling:
-- 1. `FreeGroupBasis (Fin g ⊕ Fin g) F` is the mathlib owner abstraction for the chosen basis.
-- 2. `basis.repr : F ≃* FreeGroup (Fin g ⊕ Fin g)` is the canonical transport to the standard
--    free-group model used in commutator-length arguments.
-- 3. `⁅a, b⁆` from `commutatorElement` is the owner notation for group commutators.
-- Primitive vs. derived:
-- the primitive source data are the chosen basis, the finite family `u : Fin m → F × F` of
-- commutator pairs on the right, and the asserted equality; the paired basis elements
-- `basis (.inl i)` and `basis (.inr i)` are derived directly from the owner indexing type
-- `Fin g ⊕ Fin g`.
/-- The source-facing product of the `g` paired commutators attached to a basis indexed by
`Fin g ⊕ Fin g`. -/
def pairedCommutatorProduct {g : ℕ} (basis : FreeGroupBasis (Fin g ⊕ Fin g) F) : F :=
  (List.ofFn fun i : Fin g ↦ ⁅basis (.inl i), basis (.inr i)⁆).prod

/-- Transporting `pairedCommutatorProduct` along `basis.repr` recovers the canonical orientable
surface relator on the free basis `ofFreeGroup (Fin g ⊕ Fin g)`. -/
@[simp] theorem repr_pairedCommutatorProduct {g : ℕ}
    (basis : FreeGroupBasis (Fin g ⊕ Fin g) F) :
    basis.repr basis.pairedCommutatorProduct =
      (ofFreeGroup (Fin g ⊕ Fin g)).pairedCommutatorProduct := by
  rw [pairedCommutatorProduct, pairedCommutatorProduct, map_list_prod, List.map_ofFn]
  refine congrArg List.prod ?_
  rw [List.ofFn_inj]
  ext i
  simp [map_commutatorElement]

/-- Proposition 1-6-8: if `F` has a basis indexed by `Fin g ⊕ Fin g`, so that the basis elements
form `g` ordered pairs, and the product of those `g` commutators equals a product of `m`
commutators, then `m >= g`. -/
-- Proof sketch: transport the given basis to the standard free group of rank `2g`, interpret the
-- left-hand side as the genus-`g` surface relator, and then use the same commutator-length lower
-- bound argument as in Proposition 6.6 after comparing with the right-hand product of `m`
-- commutators.
theorem genus_le_of_commutator_product_eq
    {g m : ℕ}
    (basis : FreeGroupBasis (Fin g ⊕ Fin g) F)
    (u : Fin m → F × F)
    (hrel : basis.pairedCommutatorProduct = (List.ofFn fun j : Fin m ↦ ⁅(u j).1, (u j).2⁆).prod) :
    g ≤ m := sorry

end FreeGroupBasis

end
