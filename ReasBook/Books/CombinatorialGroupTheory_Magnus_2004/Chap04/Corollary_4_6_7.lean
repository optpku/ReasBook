/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import CombinatorialGroupTheory_Magnus_2004.Chap04.Theorem_4_6_6

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

set_option autoImplicit false

open scoped Pointwise

/-!
Primary domain: subgroup structure of free products with amalgamation and HNN extensions.

Layer triage:
- `source-facing`: a subgroup of an amalgamated product or of an HNN extension, together with the
  hypothesis that it has trivial intersection with every conjugate of the factor subgroups or of
  the embedded base subgroup, and the conclusion that the subgroup is free.
- `core/canonical`: `Subgroup.amalgamatedProductAlong`, `HNNExtension`,
  `IsKuroshFactorDecomposition`, and `IsFreeGroup` are the owner abstractions for the ambient
  groups, the subgroup free-product decomposition, and the freeness conclusion.
- `bridge/view`: the chapter-specific existence theorems from Theorem `4-6-6`
  `exists_kurosh_factor_decomposition_of_disjoint_base_conjugates_amalgamatedProductAlong` and
  `exists_kurosh_factor_decomposition_of_disjoint_associatedSubgroup_conjugates_hnnExtension`
  bridge the present disjointness hypotheses to the canonical decomposition owner. The source
  hypotheses here are stated directly through the canonical conjugation action on the factor ranges
  `(Subgroup.amalgamatedProductAlong.left e).range`,
  `(Subgroup.amalgamatedProductAlong.right e).range`, and the HNN base range `(of).range`; in the
  HNN case the base-range hypothesis is stronger than the associated-subgroup disjointness used by
  Theorem `4-6-6`.

Domain sampling:
1. `IsKuroshFactorDecomposition` from Proposition `1-11-24` is the canonical project owner for
   the free-product decomposition data underlying both corollaries.
2. `exists_kurosh_factor_decomposition_of_disjoint_base_conjugates_amalgamatedProductAlong` from
   Theorem `4-6-6` is the chapter-specialized bridge theorem for the amalgamated-product case.
3. `exists_kurosh_factor_decomposition_of_disjoint_associatedSubgroup_conjugates_hnnExtension`
   from Theorem `4-6-6` is the corresponding HNN-extension bridge theorem.
4. `Subgroup.amalgamatedProductAlong` with `left` and `right`, and `HNNExtension` with `of`, are
   the canonical ambient owners for the two group constructions.

Primitive vs. derived:
- primitive public data: the subgroup and the disjointness hypotheses against conjugates of the
  canonical factor or base subgroups;
- derived API: the Kurosh- or Bass-Serre-type free-product decomposition whose extra factors are
  forced to be trivial, leaving only a free subgroup factor.

The textbook includes finite generation, but for the freeness conclusion that hypothesis is
redundant and is omitted from the canonical statements below.
-/

section AmalgamatedProduct

variable {G1 : Type u} {G2 : Type v} [Group G1] [Group G2]
variable {A : Subgroup G1} {B : Subgroup G2} (e : A ≃* B)

open Subgroup.amalgamatedProductAlong

local notation "P" => Subgroup.amalgamatedProductAlong e

/-- Corollary 4-6-7 (1): in a free product with amalgamation, a subgroup that meets every
conjugate of each factor subgroup trivially is free. -/
-- Proof sketch: apply the chapter owner
-- `exists_kurosh_factor_decomposition_of_disjoint_base_conjugates_amalgamatedProductAlong`. Its
-- subgroup factors are intersections with conjugates of the left or right factor ranges, so the
-- present disjointness hypotheses make those factors trivial. The remaining distinguished factor
-- is free, and the resulting free-product decomposition therefore identifies `K` with a free
-- group.
theorem isFreeGroup_of_disjoint_factor_conjugates_amalgamatedProductAlong
    (K : Subgroup P)
    (hleft : ∀ p : P, Disjoint K (MulAut.conj p⁻¹ • (left e).range))
    (hright : ∀ p : P, Disjoint K (MulAut.conj p⁻¹ • (right e).range)) :
    IsFreeGroup K := sorry

end AmalgamatedProduct

section HNN

variable {G : Type u} [Group G]
variable {A B : Subgroup G} {φ : A ≃* B}

local notation "E" => HNNExtension G A B φ
local notation "of" => (HNNExtension.of : G →* E)

/-- Corollary 4-6-7 (2): in an HNN extension, a subgroup that meets every conjugate of the
embedded base subgroup trivially is free. -/
-- Proof sketch: apply the chapter owner
-- `exists_kurosh_factor_decomposition_of_disjoint_associatedSubgroup_conjugates_hnnExtension`.
-- The present hypothesis on conjugates of `(of).range` is stronger than the owner's hypotheses on
-- conjugates of `A.map of` and `B.map of`, and its subgroup factors are intersections with
-- conjugates of the canonical base range `(of).range`. Hence every such factor is trivial, so only
-- the distinguished free factor remains.
theorem isFreeGroup_of_disjoint_base_conjugates_hnnExtension
    (K : Subgroup E)
    (hbase : ∀ p : E, Disjoint K (MulAut.conj p⁻¹ • (of).range)) :
    IsFreeGroup K := sorry

end HNN
