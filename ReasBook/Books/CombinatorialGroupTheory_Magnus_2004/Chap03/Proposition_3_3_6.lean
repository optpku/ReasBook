/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import CombinatorialGroupTheory_Magnus_2004.Chap01.Proposition_1_11_24

-- Declarations for this item will be appended below by the statement pipeline.

universe u v w

open Monoid
open scoped Pointwise

section

variable {ι : Type u} (G : ι → Type v) [∀ i, Group (G i)]

-- Layer triage:
-- `source-facing`: a subgroup `H` of the indexed free product `CoprodI G`, together with a
-- decomposition of `H` as a free product of one free group and subgroup factors of `H` whose
-- ambient images are conjugates of subgroups of the ambient free factors.
-- `core/canonical`: `CoprodI` is mathlib's owner for indexed free products, `IsFreeGroup` is the
-- owner predicate for freeness, and subgroup conjugation is expressed using `MulAut.conj`
-- together with `Subgroup.map`.
-- `bridge/view`: the Chapter 1 owner `IsKuroshFactorDecomposition` packages the distinguished
-- free subgroup together with the subgroup factors into a `CoprodI` decomposition; the extra
-- source-facing content here is only the ambient conjugacy description of the factors.
-- Domain sampling:
-- 1. `CoprodI` and `CoprodI.of` are the canonical indexed free-product owners.
-- 2. `IsFreeGroup` is the canonical owner for the free group factor in the decomposition.
-- 3. `IsKuroshFactorDecomposition` from Proposition `1-11-24` is the project owner for the
--    underlying free-product decomposition data.
-- 4. `Subgroup.map`, `Subgroup.subtype`, and `MulAut.conj` are the standard subgroup and
--    conjugation APIs needed to express the Kurosh factors.

-- Primitive vs. derived:
-- the primitive source-facing data are the subgroup `H`, the distinguished free subgroup factor
-- `F ≤ H`, the subgroup-factor family `K : J → Subgroup H`, and the free-product equivalence
-- `CoprodI (kuroshFactorFamily F K) ≃* H`; the ambient conjugacy description of each `K j` is the
-- extra source-facing property asserted in this proposition.

/-- Proposition 3-3-6: every subgroup of an indexed free product is itself a free product of one
free group together with subgroup factors lying in the subgroup and equal in the ambient free
product to conjugates of subgroups of the original free factors. -/
-- Proof sketch: realize the ambient free product as the fundamental group of a complex obtained by
-- wedging complexes for the factors, then apply the covering-space description of subgroups from
-- Proposition 3-3-4. Decompose the lifted complex using Proposition 3-3-5; the components lying
-- above the original factor complexes contribute the conjugate subgroup factors, and the remaining
-- tree-complement contributes the free factor.
theorem exists_kurosh_freeProduct_decomposition
    (H : Subgroup (CoprodI G)) :
    ∃ (J : Type w) (K : J → Subgroup H) (F : Subgroup H)
      (e : CoprodI (kuroshFactorFamily F K) ≃* H),
      IsKuroshFactorDecomposition H K F e ∧
        ∀ j, ∃ i : ι, ∃ g : CoprodI G, ∃ L : Subgroup (G i),
          Subgroup.map H.subtype (K j) =
            MulAut.conj g • Subgroup.map (CoprodI.of : G i →* CoprodI G) L := sorry

end
