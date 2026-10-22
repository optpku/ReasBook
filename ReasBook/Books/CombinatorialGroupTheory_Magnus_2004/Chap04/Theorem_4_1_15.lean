/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import CombinatorialGroupTheory_Magnus_2004.Chap03.Proposition_3_3_6

-- Declarations for this item will be appended below by the statement pipeline.

universe u v w

open Monoid
open scoped Pointwise

section

variable {ι : Type u} (G : ι → Type v) [∀ i, Group (G i)]

/-!
Primary domain: subgroup structure of free products.

Layer triage:
- `source-facing`: the Kurosh subgroup theorem for a subgroup `H ≤ CoprodI G`.
- `core/canonical`: `CoprodI` is the owner abstraction for indexed free products, and
  `IsKuroshFactorDecomposition` is the project owner for the corresponding decomposition data.
- `bridge/view`: the ambient-factor description of each Kurosh subgroup factor is expressed using
  `Subgroup.map` and conjugation by `MulAut.conj`; no extra owner is needed here because
  Proposition `3-3-6` already states the theorem at the correct source-facing level.

Domain sampling:
1. `CoprodI` and `CoprodI.of` are the canonical indexed free-product API.
2. `IsKuroshFactorDecomposition` from Chapter 1 is the project owner for the free-product
   decomposition data with one distinguished free factor.
3. `exists_kurosh_freeProduct_decomposition` from Proposition `3-3-6` already has the exact
   Kurosh-subgroup interface in this project.
4. `Subgroup.map` together with `MulAut.conj` is the canonical subgroup-conjugation API used to
   describe the factors.

Primitive vs. derived:
- primitive source-facing data: the subgroup `H` of `CoprodI G`;
- derived API: the free subgroup factor, the family of Kurosh factors, the free-product
  equivalence, and the ambient conjugacy description of each factor.
-/

/- Theorem 4-1-15 (Kurosh Subgroup Theorem): every subgroup of an indexed free product is itself
a free product of one free group together with subgroup factors whose ambient images are conjugate
to subgroups of the original free factors.

This item adds no new source-facing construction beyond Proposition `3-3-6`, so the file keeps a
direct recall of that canonical theorem instead of restating its interface locally. -/
#check exists_kurosh_freeProduct_decomposition

end
