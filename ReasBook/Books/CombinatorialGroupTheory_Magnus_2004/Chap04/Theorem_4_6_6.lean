/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import CombinatorialGroupTheory_Magnus_2004.Chap01.Proposition_1_11_24
import CombinatorialGroupTheory_Magnus_2004.Chap04.Definition_4_2_9

-- Declarations for this item will be appended below by the statement pipeline.

universe u v w

set_option autoImplicit false

open Monoid
open HNNExtension
open scoped Pointwise

/-!
Primary domain: subgroup decompositions in free products with amalgamation and HNN extensions.

Layer triage:
- `source-facing`: a subgroup of a two-factor amalgamated product or of an HNN extension whose
  intersections with conjugates of the amalgamated subgroup or of the HNN associated subgroups are
  trivial, and the resulting free-product decomposition of that subgroup.
- `core/canonical`: `Subgroup.amalgamatedProductAlong` and `HNNExtension` are the ambient owners,
  while `IsKuroshFactorDecomposition` is the project owner for the resulting free-product
  decomposition with one distinguished free factor.
- `bridge/view`: the amalgamated-product decomposition is obtained internally by specializing the
  Chapter 1 Kurosh theorem to the canonical two-factor pushout, while the public subgroup factors
  are stated directly as intersections with conjugates of `(left e).range` and `(right e).range`.
  In the HNN case the factors are likewise expressed directly as the corresponding
  `Subgroup.comap` intersections inside `H`.

Domain sampling:
1. `Subgroup.amalgamatedProductAlong e`, together with `left`, `right`, and `base`, is the
   chapter owner for two-factor free products with amalgamation.
2. `HNNExtension G A B φ`, together with `of`, is mathlib's canonical owner for HNN extensions and
   the embedded base group.
3. `IsKuroshFactorDecomposition` and `kuroshFactorFamily` from Proposition `1-11-24` are the
   project's canonical owners for the subgroup free-product decomposition data.
4. `MulAut.conj` and `Subgroup.comap` are the canonical APIs for expressing the subgroup factors
   as actual intersections inside the subgroup `H`; the generic Chapter 1
   `conjugateFactorIntersectionSubgroup` remains only an internal bridge.

Primitive vs. derived:
- primitive source-facing data: the subgroup `H` and the hypothesis that it is disjoint from every
  conjugate of the amalgamated subgroup or of the embedded HNN associated subgroups;
- derived API: the free subgroup factor, the family of subgroup factors, the free-product
  equivalence, and the identification of each factor with the corresponding conjugate-intersection
  subgroup.

The finite-generation and nontriviality hypotheses from the textbook are omitted below: the
canonical Kurosh/Bass-Serre decomposition statements do not require them.
-/

section AmalgamatedProduct

variable {G1 : Type u} {G2 : Type v} [Group G1] [Group G2]
variable {A : Subgroup G1} {B : Subgroup G2} (e : A ≃* B)

open Subgroup.amalgamatedProductAlong

local notation "P" => Subgroup.amalgamatedProductAlong e
/-- Theorem 4-6-6 (1): in a two-factor free product with amalgamation, a subgroup that meets
every conjugate of the amalgamated subgroup trivially is a free product of one free factor
together with subgroup factors which are the corresponding conjugate intersections with the left
or right factor subgroups. -/
-- Proof sketch: specialize Proposition `1-11-24` to the canonical two-factor pushout presenting
-- `P`. The resulting Kurosh factors identify with the direct subgroup intersections with
-- conjugates of `(left e).range` and `(right e).range`, viewed as subgroups of `H`, so the
-- theorem surface stays at the owner level `left`/`right` rather than the internal `Bool`-indexed
-- pushout presentation.
theorem exists_kurosh_factor_decomposition_of_disjoint_base_conjugates_amalgamatedProductAlong
    (H : Subgroup P)
    (hbase : ∀ p : P, Disjoint H (MulAut.conj p⁻¹ • (base e).range)) :
    ∃ (κ : Type w) (K : κ → Subgroup H) (F : Subgroup H)
      (ψ : CoprodI (kuroshFactorFamily F K) ≃* H),
      IsKuroshFactorDecomposition H K F ψ ∧
        ∀ j,
          ∃ p : P,
            K j = Subgroup.comap H.subtype (MulAut.conj p⁻¹ • (left e).range) ∨
              K j = Subgroup.comap H.subtype (MulAut.conj p⁻¹ • (right e).range) := sorry

end AmalgamatedProduct

section HNN

variable {G : Type u} [Group G]
variable {A B : Subgroup G} {φ : A ≃* B}

local notation "E" => HNNExtension G A B φ
local notation "of" => (HNNExtension.of : G →* E)

/-- Theorem 4-6-6 (2): in an HNN extension, a subgroup that meets every conjugate of the embedded
associated subgroups trivially is a free product of one free factor together with subgroup factors
which are the corresponding conjugate intersections with conjugates of the embedded base subgroup.
-/
-- Proof sketch: let the subgroup act on the Bass-Serre tree of the HNN extension, or equivalently
-- use the bipolar structure from Section `6`. Trivial intersections with conjugates of the base
-- associated subgroups `A` and `B` force the edge stabilizers to be trivial, so the subgroup is
-- the free product of its vertex stabilizers together with a free group. Those vertex stabilizers
-- are exactly the intersections with conjugates of the embedded base subgroup.
theorem exists_kurosh_factor_decomposition_of_disjoint_associatedSubgroup_conjugates_hnnExtension
    (H : Subgroup E)
    (hA : ∀ p : E, Disjoint H (MulAut.conj p⁻¹ • A.map of))
    (hB : ∀ p : E, Disjoint H (MulAut.conj p⁻¹ • B.map of)) :
    ∃ (κ : Type w) (K : κ → Subgroup H) (F : Subgroup H)
      (ψ : CoprodI (kuroshFactorFamily F K) ≃* H),
      IsKuroshFactorDecomposition H K F ψ ∧
        ∀ j,
          ∃ p : E,
            K j = Subgroup.comap H.subtype (MulAut.conj p⁻¹ • of.range) := sorry

end HNN
