/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u

section

variable {G : Type u} [Group G] [Group.FG G]

namespace Subgroup

-- Layer triage:
-- `source-facing`: finite generation of `G`, subgroups of a fixed finite index, and a
-- characteristic finite-index subgroup contained in a given finite-index subgroup.
-- `core/canonical`: `Subgroup.index`, `H.FiniteIndex`, `K.Characteristic`, and finite
-- intersections of finite-index subgroups.
-- `bridge/view`: the first clause packages the textbook "number of subgroups" as finiteness of
-- the set `{H : Subgroup G | H.index = n}`, and the second clause keeps the source-facing
-- existential conclusion with the canonical finite-index owner property instead of introducing an
-- auxiliary bundled wrapper.
-- Domain sampling:
-- 1. `Subgroup.index` is mathlib's owner for subgroup index.
-- 2. `Subgroup.FiniteIndex` is the canonical finite-index hypothesis on a subgroup.
-- 3. `Subgroup.characteristic_iff_map_eq` is the owner criterion for invariance under
--    automorphisms.
-- 4. `Subgroup.finiteIndex_iInf'` is the finite-intersection owner theorem used by the textbook's
--    intersection construction.
-- Primitive vs. derived:
-- the primitive public data are only the ambient finitely generated group `G`, the index `n` in
-- the first clause, and the finite-index subgroup `H` in the second clause. The finite set of
-- index-`n` subgroups and the characteristic finite-index subgroup contained in `H` are derived
-- owner-level conclusions.

-- Proof sketch: encode each subgroup of index `n` by its transitive action on the `n` right
-- cosets, producing a homomorphism into the symmetric group on `n` letters. A finitely generated
-- group has only finitely many homomorphisms into a fixed finite group, so only finitely many
-- index-`n` subgroups can occur.
/-- Theorem 4-4-9 (1): a finitely generated group has only finitely many subgroups of any fixed
positive index `n`. -/
theorem finite_setOf_index_eq (n : ℕ+) :
    Set.Finite {H : Subgroup G | H.index = (n : ℕ)} := sorry

-- Proof sketch: let `n = H.index` and intersect all subgroups of `G` of index `n`. By the first
-- clause this is a finite intersection, hence still of finite index; it lies in `H` because `H`
-- itself has index `n`; and every automorphism of `G` permutes the index-`n` subgroups, so their
-- intersection is characteristic.
/-- Theorem 4-4-9 (2): every finite-index subgroup of a finitely generated group contains a
characteristic subgroup of finite index. -/
theorem exists_characteristic_le_of_finiteIndex (H : Subgroup G) [H.FiniteIndex] :
    ∃ K : Subgroup G, K ≤ H ∧ K.Characteristic ∧ K.FiniteIndex := sorry

end Subgroup

end
