/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import CombinatorialGroupTheory_Magnus_2004.Chap03.Definition_3_5_3

universe u

set_option autoImplicit false

section

variable {G : Type u} [Group G]

/-!
Primary domain: finite-index subgroups of `F`-groups and torsion-freeness.

Layer triage:
- `source-facing`: an `F`-group `G` together with the existence of a torsion-free subgroup of
  finite index.
- `core/canonical`: `IsFGroup` from Definition `3-5-3`, the bundled owner
  `FiniteIndexNormalSubgroup G` for normal finite-index subgroups, and `IsMulTorsionFree` for
  torsion-freeness.
- `bridge/view`: the source phrase “contains a torsion-free subgroup of finite index” is the
  unbundled existential view obtained by forgetting the normality bundle on a
  `FiniteIndexNormalSubgroup`.

Domain sampling:
1. `IsFGroup` is the chapter owner predicate for the source notion of an `F`-group.
2. `FiniteIndexNormalSubgroup` is mathlib's canonical owner for normal subgroups of finite index.
3. `IsMulTorsionFree` is mathlib's canonical owner predicate for torsion-freeness.
4. Proposition `3-7-12` supplies the upstream residual-finiteness theorem for the finitely
   generated linear groups used in the textbook proof, so this file should only expose the
   torsion-free finite-index consequence rather than a parallel residual-finiteness wrapper.

Primitive vs. derived:
- primitive public data: only the ambient group `G` and the hypothesis `hG : IsFGroup G`;
- derived API: a bundled torsion-free normal finite-index subgroup, and the source-facing weaker
  existential over ordinary subgroups obtained from that bundled owner.
-/

/-- A bundled owner-level form of Proposition 3-7-13: an `F`-group admits a torsion-free normal
subgroup of finite index. -/
-- Proof sketch: choose the standard surface presentation of the `F`-group and use the linearity
-- input from the Section `7` discussion to place `G` in the quotient of a finitely generated
-- subgroup of `SL(2, ℝ)`. Proposition `3-7-12` then gives residual finiteness. Separate the
-- finite set of nontrivial powers of the torsion generators by a finite quotient and take its
-- kernel; the torsion classification from the preceding Fuchsian-complex results forces that
-- kernel to contain no nontrivial finite-order element.
theorem exists_torsionFree_finiteIndexNormalSubgroup_of_isFGroup
    (hG : IsFGroup G) :
    ∃ N : FiniteIndexNormalSubgroup G, IsMulTorsionFree (N : Subgroup G) := sorry

/-- Proposition 3-7-13: every `F`-group contains a torsion-free subgroup of finite index. -/
theorem exists_torsionFree_finiteIndex_subgroup_of_isFGroup
    (hG : IsFGroup G) :
    ∃ H : Subgroup G, H.FiniteIndex ∧ IsMulTorsionFree H := by
  rcases exists_torsionFree_finiteIndexNormalSubgroup_of_isFGroup hG with ⟨N, hN⟩
  exact ⟨(N : Subgroup G), inferInstance, hN⟩

end
