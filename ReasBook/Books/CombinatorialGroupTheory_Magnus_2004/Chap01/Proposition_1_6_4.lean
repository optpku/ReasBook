/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib.Data.ENat.Lattice
import Mathlib.GroupTheory.Coprod.Basic
import Mathlib.GroupTheory.CoprodI
import Mathlib.GroupTheory.FreeGroup.Basic

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open scoped Monoid.Coprod

section

variable {G : Type u} [Group G]

-- Layer triage:
-- `source-facing`: the irreducibility rank of a group and its additivity under the free product
-- decomposition `G₁ ∗ G₂`.
-- `core/canonical`: the owner invariant `groupIr`, together with `Monoid.Coprod` for the free
-- product, `FreeGroup (Fin n)` for the rank-`n` free group, and surjective homomorphisms
-- `G →* FreeGroup (Fin n)`.
-- `bridge/view`: a free quotient of `G₁` and a free quotient of `G₂` extend along the universal
-- property of `G₁ ∗ G₂` to a free quotient of the free product, while any free quotient of
-- `G₁ ∗ G₂` restricts to free quotients of the two factors.
-- Domain sampling:
-- 1. `Monoid.Coprod` with notation `G₁ ∗ G₂` is mathlib's owner abstraction for the free product
--    of two groups.
-- 2. `Monoid.Coprod.lift`, `Monoid.Coprod.inl`, and `Monoid.Coprod.inr` are the canonical maps
--    governing homomorphisms out of a free product.
-- 3. `Monoid.Coprod.range_lift` is the canonical range statement for maps out of a free product,
--    so the upper-bound half of Proposition `1-6-4` belongs on the owner abstraction
--    `Monoid.Coprod.lift`.
-- 4. `FreeGroup (Fin n)` is the canonical rank-`n` free group, so finite-rank free quotients
--    should be recorded directly against that owner rather than through an auxiliary wrapper.
-- Primitive vs. derived:
-- the primitive data are only the ambient group and its surjective maps onto finite-rank free
-- groups. The irreducibility rank itself is derived canonically as the supremum of those ranks,
-- so there is no separate public or private wrapper for the set of attainable ranks.

/-- The irreducibility rank `Ir(G)` of a group is the supremum, in `ℕ∞`, of the finite ranks of
free groups that occur as quotients of that group. -/
noncomputable def groupIr (G : Type u) [Group G] : ℕ∞ :=
  sSup (((↑) : ℕ → ℕ∞) '' {m : ℕ | ∃ φ : G →* FreeGroup (Fin m), Function.Surjective φ})

/- The irreducibility rank of a group is written `Ir(G)`, read directly through the canonical
owner invariant `groupIr G`. -/
namespace GroupIr

scoped notation "Ir(" G ")" => groupIr G

end GroupIr

end

section

open scoped GroupIr

variable {G G₁ G₂ : Type u} [Group G] [Group G₁] [Group G₂]

/-- A surjective homomorphism from `G` onto a rank-`m` free group gives the lower bound
`m ≤ Ir(G)`. -/
-- Proof sketch: the witness `(φ, hφ)` shows that `m` belongs to the defining set of finite free
-- quotient ranks, so its image in `ℕ∞` belongs to the set whose supremum defines `Ir(G)`.
theorem le_groupIr_of_surjective (m : ℕ) (φ : G →* FreeGroup (Fin m))
    (hφ : Function.Surjective φ) :
    m ≤ Ir(G) := sorry

/-- The irreducibility rank depends only on the group up to isomorphism. -/
-- Proof sketch: compose free quotients of `G` with `e.symm` and free quotients of `G₁` with `e`.
-- This identifies the attainable finite ranks on the two sides, hence their suprema in `ℕ∞`
-- agree.
theorem groupIr_eq_of_equiv (e : G ≃* G₁) :
    Ir(G) = Ir(G₁) := sorry

/-- Proposition 1-6-4: the irreducibility rank of a free product is the sum of the irreducibility
ranks of the two factors. -/
-- Proof sketch: for the lower bound, combine maximal free quotients of `G₁` and `G₂` using the
-- universal property of the free product to obtain a quotient onto the free product of two free
-- groups, hence onto a free group of rank `Ir(G₁) + Ir(G₂)`. For the upper bound, any
-- surjection from `G₁ ∗ G₂` onto a free group restricts to homomorphisms from the two factors;
-- the subgroup images generate that free group through an induced map from the free product of
-- the images, so the free rank cannot exceed the sum of the irreducibility ranks of the two
-- factors.
theorem groupIr_freeProduct_eq_add :
    Ir(G₁ ∗ G₂) = Ir(G₁) + Ir(G₂) := sorry

end
