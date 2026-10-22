/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib.GroupTheory.Coprod.Basic

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

open scoped Monoid.Coprod

set_option autoImplicit false

section

variable (A : Type u) (B : Type v) [Group A] [Group B]

-- Layer triage:
-- `source-facing`: the textbook definition of the free product of two groups `A` and `B`,
-- presented by adjoining the generators and relators of two disjoint presentations.
-- `core/canonical`: `Monoid.Coprod`, with scoped notation `A ∗ B`, is mathlib's owner
-- abstraction for the coproduct of two groups.
-- `bridge/view`: no extra bridge is needed here, because the textbook item is only recalling the
-- basic owner construction itself rather than asserting a new universal property or comparison
-- theorem.
-- Domain sampling:
-- 1. `Monoid.Coprod` in `Mathlib/GroupTheory/Coprod/Basic` is the canonical free-product
--    construction for monoids and groups.
-- 2. The scoped notation `A ∗ B` is the canonical source-facing notation for that owner
--    construction.
-- 3. `Proposition_1_6_4` and `Proposition_3_12_3` already use `Monoid.Coprod` and the notation
--    `G₁ ∗ G₂` as the project's free-product API for groups.
-- 4. `Definition_4_1_2` immediately derives the factor subgroups from the canonical embeddings
--    `Monoid.Coprod.inl` and `Monoid.Coprod.inr`, so this owner file should expose only the
--    ambient free-product object itself.
-- Primitive vs. derived:
-- the primitive mathematical content of this item is just the ambient free-product object; the
-- universal property maps and later structural lemmas are derived API on top of `Monoid.Coprod`.

/- Definition 4-1-1: for groups `A` and `B` with disjoint chosen presentations, the free product
`A * B` is the group obtained by taking the combined generators and relators of those two
presentations.

This item is a direct recall of mathlib's canonical free-product owner expression for groups, so
the file records the type expression `A ∗ B` itself rather than introducing a redundant alias. -/
#check (A ∗ B)

end
