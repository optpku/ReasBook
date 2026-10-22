/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u v w

set_option autoImplicit false

section

open Subgroup

variable {G : Type u} [Group G] [IsMulTorsionFree G]

/-!
Primary domain: subgroup structure of torsion-free groups and free abelian groups.

Layer triage:
- `source-facing`: a torsion-free group `G` together with a subgroup `A ≤ G` that is central, free
  abelian, and of finite index.
- `core/canonical`: `IsMulTorsionFree` for torsion-freeness, `center G` for centrality,
  `Subgroup.FiniteIndex` for the finite-index hypothesis, and `Multiplicative
  (FreeAbelianGroup ι)` for the canonical free abelian group model.
- `bridge/view`: the textbook phrase “`A` is a central free abelian subgroup of finite index” is
  expressed by the conjunction of `A ≤ center G`, `[A.FiniteIndex]`, and the existence datum
  `Nonempty (Σ ι : Type v, A ≃* Multiplicative (FreeAbelianGroup ι))`.

Domain sampling:
1. `IsMulTorsionFree` in `Mathlib/GroupTheory/Torsion` is the canonical owner predicate for a
   torsion-free group.
2. `Subgroup.center G` in `Mathlib/GroupTheory/Subgroup/Center` is the canonical owner for
   central subgroups.
3. `Subgroup.FiniteIndex` in `Mathlib/GroupTheory/Index` is the canonical finite-index owner
   abstraction for subgroup inclusions.
4. `Multiplicative (FreeAbelianGroup ι)` is already the project's source-facing model for free
   abelian groups, as used in Proposition `2-5-23`.

Primitive vs. derived:
- the primitive source data are only the ambient group `G`, the chosen subgroup `A`, and the three
  stated hypotheses on `A`.
- the free-abelian hypothesis and conclusion are recorded as a single existence datum pairing the
  basis type with the multiplicative equivalence, rather than a nested existential/package split.
-/

/-- Proposition 3-7-14: if a torsion-free group contains a central free abelian subgroup of
finite index, then the ambient group is itself free abelian. -/
-- Proof sketch: embed the given free abelian subgroup into its divisible hull and form the
-- central amalgamated extension used in the textbook proof. Because the quotient by that
-- divisible central subgroup is finite, the extension splits. The resulting projection embeds `G`
-- into a divisible free abelian group, identifies `A` with a finite-index subgroup of the image,
-- and shows that adjoining finitely many roots to `A` still yields a free abelian group.
theorem exists_mulEquiv_freeAbelianGroup_of_torsionFree_of_central_freeAbelian_subgroup_finiteIndex
    (A : Subgroup G) [A.FiniteIndex] (hAcentral : A ≤ center G)
    (hAfree : Nonempty (Σ ι : Type v, A ≃* Multiplicative (FreeAbelianGroup ι))) :
    Nonempty (Σ κ : Type w, G ≃* Multiplicative (FreeAbelianGroup κ)) := sorry

end
