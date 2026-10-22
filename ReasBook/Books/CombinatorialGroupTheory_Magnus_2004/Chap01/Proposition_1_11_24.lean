/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import CombinatorialGroupTheory_Magnus_2004.Chap01.Proposition_1_11_23

-- Declarations for this item will be appended below by the statement pipeline.

universe u v w x y

open Monoid
open scoped Pointwise

section

variable {G : Type y} [Group G]

/-- The `Option`-indexed family of subgroup factors obtained by adjoining one distinguished free
subgroup `F` to an indexed family `K`. -/
abbrev kuroshFactors {κ : Type x} (F : Subgroup G) (K : κ → Subgroup G) :
    Option κ → Subgroup G :=
  fun
    | none => F
    | some j => K j

/-- The carrier family underlying `kuroshFactors F K`, used as the summand family for the indexed
free product `CoprodI`. -/
abbrev kuroshFactorFamily {κ : Type x} (F : Subgroup G) (K : κ → Subgroup G) :
    Option κ → Type _ :=
  fun i ↦ (kuroshFactors F K i : Type _)

/-- Each summand in `kuroshFactorFamily F K` inherits its canonical group structure from the
corresponding subgroup. -/
instance instGroupKuroshFactorFamily {κ : Type x} (F : Subgroup G) (K : κ → Subgroup G)
    (i : Option κ) : Group (kuroshFactorFamily F K i) := by
  simpa [kuroshFactorFamily] using
    (inferInstance : Group ((kuroshFactors F K i : Subgroup G) : Type _))

end

section

variable {G : Type y} [Group G]

/-- A witness that `H` is the free product of the subgroup family `K` together with the free
factor `F`. -/
structure IsKuroshFactorDecomposition {κ : Type x}
    (H : Subgroup G) (K : κ → Subgroup H) (F : Subgroup H)
    (e : CoprodI (kuroshFactorFamily F K) ≃* H) : Prop where
  /-- The distinguished factor `F` is free. -/
  freeFactor_isFree : IsFreeGroup F
  /-- The free-product inclusion of each `Option`-indexed factor identifies with the corresponding
  subgroup inclusion into `H`. -/
  comp_of (i : Option κ) :
      e.toMonoidHom.comp
        (CoprodI.of : kuroshFactorFamily F K i →* CoprodI (kuroshFactorFamily F K)) =
      (kuroshFactors F K i).subtype

namespace IsKuroshFactorDecomposition

variable {κ : Type x} {H : Subgroup G} {K : κ → Subgroup H} {F : Subgroup H}
variable {e : CoprodI (kuroshFactorFamily F K) ≃* H}

/-- The distinguished factor inclusion in a Kurosh decomposition is the subgroup inclusion
`F ↪ H`. -/
theorem freeFactor_comp_of (h : IsKuroshFactorDecomposition H K F e) :
    e.toMonoidHom.comp
        (CoprodI.of : kuroshFactorFamily F K none →* CoprodI (kuroshFactorFamily F K)) =
      F.subtype :=
  by simpa [kuroshFactorFamily, kuroshFactors] using h.comp_of none

/-- Each indexed subgroup factor inclusion in a Kurosh decomposition is the subgroup inclusion
`K j ↪ H`. -/
theorem factor_comp_of (h : IsKuroshFactorDecomposition H K F e) (j : κ) :
    e.toMonoidHom.comp
        (CoprodI.of : kuroshFactorFamily F K (some j) →* CoprodI (kuroshFactorFamily F K)) =
      (K j).subtype :=
  by simpa [kuroshFactorFamily, kuroshFactors] using h.comp_of (some j)

end IsKuroshFactorDecomposition

end

section

variable {ι : Type u} {A : Type v} {H : ι → Type w}
variable [Group A] [∀ i, Group (H i)]
variable (φ : ∀ i, A →* H i)

/- Proposition 1-11-24 lies in Section 11 on subgroups of an amalgamated free product.

Layer triage:
- `source-facing`: the amalgamated product `PushoutI φ`, the subgroup `G*`, the conjugate
  intersections `Hᵢᵖ ∩ G*`, the conjugates of the amalgamated subgroup `A`, and the conclusion that
  `G*` is the free product of certain such intersections together with a free group.
- `core/canonical`: `Monoid.PushoutI` for the ambient amalgamated product,
  `conjugateFactorIntersectionSubgroup` from Proposition `1-11-23` for the subgroup factors,
  `Monoid.CoprodI` for the free product decomposition, and `IsFreeGroup` for the extra free factor.
- `bridge/view`: `kuroshFactorFamily` packages the family of conjugate-intersection factors together
  with one distinguished free subgroup, and `IsKuroshFactorDecomposition` is the resulting
  reusable owner for the free-product decomposition data.

Domain sampling:
1. `Monoid.PushoutI φ` is mathlib's owner abstraction for a free product with the subgroup `A`
   amalgamated across the factors.
2. `conjugateFactorIntersectionSubgroup φ GStar p i` is the canonical subgroup
   `p⁻¹ Hᵢ p ∩ G*` inside `G*`.
3. `Monoid.CoprodI` is mathlib's owner abstraction for free products of an indexed family of
   groups, with canonical inclusions `Monoid.CoprodI.of`.
4. `IsFreeGroup` is mathlib's owner abstraction for the statement that the residual factor is a
   free group.

Primitive vs. derived:
the primitive data are the amalgamating diagram `φ`, the subgroup `G*`, and the hypothesis that
`G*` meets every conjugate of the base subgroup trivially. The asserted Kurosh decomposition uses
the Chapter 1 owner `IsKuroshFactorDecomposition`; the additional source-facing content here is
that each factor `K j` is realized by a conjugate intersection `p⁻¹ Hᵢ p ∩ G*`. -/

/-- Proposition 1-11-24: if `G = PushoutI φ` is the free product of the factors `Hᵢ` with the
subgroup `A` amalgamated and `G*` intersects every conjugate of `A` trivially, then `G*` is the
free product of certain actual conjugate-intersection subgroups `p⁻¹ Hᵢ p ∩ G*` together with one
free subgroup factor. -/
-- Proof sketch: apply Proposition `1-11-23` to the normal subgroup generated by the conjugate
-- intersections. Under the extra hypothesis, the edge groups in the resulting tree-product
-- description are trivial because they lie in conjugates of the amalgamated subgroup. Hence that
-- normal subgroup is an honest free product of the conjugate-intersection factors. Proposition
-- `1-11-22` then splits `G*` over the free quotient, producing a free subgroup factor and the
-- required free-product decomposition of `G*`.
theorem exists_freeProduct_decomposition_of_disjoint_base_conjugates
    (hφ : ∀ i, Function.Injective (φ i))
    (GStar : Subgroup (PushoutI φ))
    (htriv :
      ∀ p : PushoutI φ, Disjoint GStar (MulAut.conj p⁻¹ • (PushoutI.base φ).range)) :
    ∃ (κ : Type x) (K : κ → Subgroup GStar) (F : Subgroup GStar)
      (e : CoprodI (kuroshFactorFamily F K) ≃* GStar),
      IsKuroshFactorDecomposition GStar K F e ∧
        ∀ j, ∃ p : PushoutI φ, ∃ i : ι,
          K j = conjugateFactorIntersectionSubgroup φ GStar p i := sorry

end
