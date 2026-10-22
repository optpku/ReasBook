/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import CombinatorialGroupTheory_Magnus_2004.Chap01.Proposition_1_2_18

-- Declarations for this item will be appended below by the statement pipeline.

universe u

section

variable {F : Type u} [Group F] [IsFreeGroup F]

/-!
Primary domain: finite-index subgroup intersections in torsion-free groups, specialized here to
free groups.

Layer triage:
- `source-facing`: fixed subgroups `H K : Subgroup F`, with `H` of finite index and `K ≠ ⊥`.
- `core/canonical`: `Subgroup.FiniteIndex`, `Subgroup.finite_iff_finite_and_finiteIndex`, and the
  ambient torsion-free owner `IsMulTorsionFree`.
- `bridge/view`: the textbook phrase “has non-trivial intersection with” is expressed as
  `H ⊓ K ≠ ⊥`.

Domain sampling:
1. `Subgroup.FiniteIndex` in `Mathlib/GroupTheory/Index` is the owner predicate for finite index.
2. `Subgroup.instFiniteIndex_subgroupOf` is the canonical finite-index inheritance on
   `H.subgroupOf K`.
3. `Subgroup.finite_iff_finite_and_finiteIndex` is the owner bridge from a finite finite-index
   subgroup to finiteness of the ambient subgroup.
4. Proposition `1-2-18` provides the reused owner instance `IsMulTorsionFree F` for free groups.

Primitive vs. derived:
- primitive public data: the subgroups `H` and `K`, the finite-index structure on `H`, and the
  nontriviality hypothesis `K ≠ ⊥`;
- derived API: finiteness of `K` under the contradiction hypothesis `H ⊓ K = ⊥`, and hence
  triviality of `K` from torsion-freeness.
-/

/-- A finite subgroup of a torsion-free group is trivial. -/
private theorem eq_bot_of_finite_of_isMulTorsionFree {G : Type u} [Group G]
    [IsMulTorsionFree G] (K : Subgroup G) [Finite K] : K = ⊥ := by
  rw [Subgroup.eq_bot_iff_forall]
  intro x hx
  let xK : K := ⟨x, hx⟩
  have hxK : IsOfFinOrder xK := isTorsion_of_finite xK
  simpa [xK] using hxK.eq_one'

/-- A finite-index subgroup of a torsion-free group meets every nontrivial subgroup nontrivially. -/
private theorem inf_ne_bot_of_finiteIndex_of_ne_bot_of_isMulTorsionFree
    {G : Type u} [Group G] [IsMulTorsionFree G] (H K : Subgroup G) [H.FiniteIndex]
    (hK : K ≠ ⊥) :
    H ⊓ K ≠ ⊥ := by
  intro hHK
  have hsub : H.subgroupOf K = ⊥ := by
    rw [Subgroup.subgroupOf_eq_bot, disjoint_iff, hHK]
  letI : Finite (H.subgroupOf K) := by
    simpa [hsub] using (inferInstance : Finite (⊥ : Subgroup K))
  have hK_finite : Finite K :=
    (Subgroup.finite_iff_finite_and_finiteIndex (H.subgroupOf K)).2
      ⟨inferInstance, inferInstance⟩
  letI : Finite K := hK_finite
  exact hK (eq_bot_of_finite_of_isMulTorsionFree K)

/-- Proposition 1-3-19: a finite-index subgroup of a free group has nontrivial intersection with
every nontrivial subgroup. -/
-- Layer triage:
-- `source-facing`: fixed subgroups `H K : Subgroup F`, with `H` of finite index and `K ≠ ⊥`.
-- `core/canonical`: `Subgroup.FiniteIndex`, `IsMulTorsionFree`, and the subgroup lattice infimum
-- `H ⊓ K`.
-- `bridge/view`: the textbook phrase “has non-trivial intersection with” is expressed as
-- `H ⊓ K ≠ ⊥`.
-- Proof sketch: under the contradiction hypothesis `H ⊓ K = ⊥`, the induced subgroup
-- `H.subgroupOf K` is trivial and hence finite; because it still has finite index in `K`, the
-- subgroup `K` itself is finite. Proposition `1-2-18` supplies torsion-freeness of free groups, so
-- every finite subgroup is trivial, contradicting `K ≠ ⊥`.
theorem inf_ne_bot_of_finiteIndex_of_ne_bot (H K : Subgroup F) [H.FiniteIndex] (hK : K ≠ ⊥) :
    H ⊓ K ≠ ⊥ :=
  inf_ne_bot_of_finiteIndex_of_ne_bot_of_isMulTorsionFree H K hK

end
