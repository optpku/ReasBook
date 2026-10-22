/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

open Monoid.Coprod
open scoped Monoid.Coprod

set_option autoImplicit false

section

variable (A : Type u) (B : Type v) [Group A] [Group B]

/-!
Primary domain: free products of groups and their canonical factor subgroups.

Layer triage:
- `source-facing`: the two factor subgroups of the free product `A ∗ B`.
- `core/canonical`: `Monoid.Coprod.inl`, `Monoid.Coprod.inr`, and `MonoidHom.range`.
- `bridge/view`: the textbook factors are expressed as the ranges of the canonical embeddings.

Domain sampling:
1. `Monoid.Coprod` with notation `A ∗ B` is mathlib's owner abstraction for the free product.
2. `Monoid.Coprod.inl` and `Monoid.Coprod.inr` are the canonical embeddings of the two factors.
3. `MonoidHom.range` is the canonical owner for the subgroup image of a homomorphism.

Primitive vs. derived:
- primitive public data: the factor groups `A`, `B`, the free product `A ∗ B`, and the canonical
  embeddings of the factors;
- derived API: the left and right factor subgroups inside `A ∗ B`, obtained as the ranges of those
  embeddings.
-/

/- Definition 4-1-2: inside the free product `A ∗ B`, the two textbook factor subgroups are the
ranges of the canonical embeddings `inl : A →* A ∗ B` and `inr : B →* A ∗ B`.

This item is a direct bridge/view recall of mathlib's canonical range expressions, so the file
records those expressions directly instead of introducing parallel local aliases. -/
#check (((inl : A →* A ∗ B).range) : Subgroup (A ∗ B))
#check (((inr : B →* A ∗ B).range) : Subgroup (A ∗ B))

end
