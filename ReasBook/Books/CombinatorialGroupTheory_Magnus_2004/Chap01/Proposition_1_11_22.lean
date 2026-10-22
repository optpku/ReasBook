/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u v w

open GroupExtension

/- Proposition 1-11-22 is the Section `11` conclusion that the ambient group `G*` splits over the
free quotient `F`, with kernel `N`, so `G*` is a semidirect product of `N` by `F`.

Layer triage:
- `source-facing`: the extension `1 → N → G* → F → 1` and the existence of a homomorphic section
  of the quotient map `G* → F`.
- `core/canonical`: `GroupExtension N GStar F`, `GroupExtension.Splitting`, and the canonical
  semidirect-product equivalence attached to a splitting.
- `bridge/view`: the source-facing right inverse to `rightHom` is packaged as a
  `GroupExtension.Splitting`, from which the canonical semidirect-product equivalence is derived.

Domain sampling:
1. `GroupExtension N GStar F` is mathlib's owner abstraction for the short exact sequence
   `1 → N → G* → F → 1`.
2. `GroupExtension.Splitting` is the canonical owner of a split extension.
3. `IsFreeGroup.of`, `IsFreeGroup.lift`, and `IsFreeGroup.ext_hom` are the owner API for building
   and characterizing homomorphisms out of the free quotient `F`.
4. `GroupExtension.Splitting.semidirectProductMulEquiv` is the canonical decomposition of a split
   extension as a semidirect product.

Primitive vs. derived:
the primitive data are the extension `S` and the freeness of the quotient `F`; the source-facing
conclusion is that the extension splits, whose canonical owner is `S.Splitting`. The raw
right-inverse equation for `rightHom` and the semidirect-product equivalence are derived API from
that owner. -/

section

variable {N : Type u} {GStar : Type v} {F : Type w} [Group N] [Group GStar] [Group F]

/-- Proposition 1-11-22: if `1 → N → G* → F → 1` is an extension and the quotient `F` is free,
then the extension splits. Equivalently, the quotient map `G* → F` admits a homomorphic section,
and hence `G*` is canonically identified with a semidirect product via
`s.semidirectProductMulEquiv`. -/
theorem GroupExtension.exists_splitting_of_free_quotient
    (S : GroupExtension N GStar F) [IsFreeGroup F] :
    Nonempty S.Splitting := by
  let s : F →* GStar :=
    IsFreeGroup.lift fun a ↦ Function.surjInv S.rightHom_surjective (IsFreeGroup.of a)
  have hs : S.rightHom.comp s = MonoidHom.id F := by
    apply IsFreeGroup.ext_hom
    intro a
    simp [s, Function.surjInv_eq]
  exact ⟨⟨s, fun g ↦ DFunLike.congr_fun hs g⟩⟩

/-- Bridge/view form of Proposition 1-11-22: the splitting produced by
`exists_splitting_of_free_quotient` yields a homomorphic right inverse to `rightHom`. -/
theorem GroupExtension.exists_rightInverse_rightHom_of_free_quotient
    (S : GroupExtension N GStar F) [IsFreeGroup F] :
    ∃ s : F →* GStar, S.rightHom.comp s = MonoidHom.id F := by
  obtain ⟨s⟩ := S.exists_splitting_of_free_quotient
  exact ⟨s, s.rightHom_comp_splitting⟩

namespace GroupExtension.Splitting

/-- The canonical semidirect-product equivalence sends the copy of `F` in `N ⋊[s.conjAct] F` to
the chosen splitting of the quotient map. -/
theorem semidirectProductMulEquiv_inr {S : GroupExtension N GStar F} (s : S.Splitting) (g : F) :
    s.semidirectProductMulEquiv (SemidirectProduct.inr g) = s g := by
  change S.inl 1 * s g = s g
  simp

end GroupExtension.Splitting

end
