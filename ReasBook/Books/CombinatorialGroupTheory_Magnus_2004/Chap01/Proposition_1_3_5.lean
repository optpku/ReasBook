/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import CombinatorialGroupTheory_Magnus_2004.Chap01.Proposition_1_2_9

-- Declarations for this item will be appended below by the statement pipeline.

universe u

variable {G : Type u} [Group G]

/-- A group is Hopfian when every surjective endomorphism is injective. -/
class IsHopfian (G : Type u) [Group G] : Prop where
  injective_of_surjective (φ : G →* G) (hφ : Function.Surjective φ) : Function.Injective φ

/-- A group is cohopfian when every injective endomorphism is surjective. -/
class IsCohopfian (G : Type u) [Group G] : Prop where
  surjective_of_injective (φ : G →* G) (hφ : Function.Injective φ) : Function.Surjective φ

namespace MonoidHom

/-- A surjective endomorphism of a Hopfian group is injective. -/
theorem injective_of_surjective [IsHopfian G] (φ : G →* G) (hφ : Function.Surjective φ) :
    Function.Injective φ :=
  IsHopfian.injective_of_surjective φ hφ

/-- An injective endomorphism of a cohopfian group is surjective. -/
theorem surjective_of_injective [IsCohopfian G] (φ : G →* G) (hφ : Function.Injective φ) :
    Function.Surjective φ :=
  IsCohopfian.surjective_of_injective φ hφ

end MonoidHom

section

variable {F : Type u} [Group F] [IsFreeGroup F] [Group.FG F]

noncomputable section

namespace IsFreeGroup

/-- A finitely generated free group has a finite canonical generator type. -/
theorem finite_generators (F : Type u) [Group F] [IsFreeGroup F] [Group.FG F] :
    Finite (IsFreeGroup.Generators F) := by
  let α := IsFreeGroup.Generators F
  let e : F ≃* FreeGroup α := IsFreeGroup.toFreeGroup F
  let f : F →* FreeGroup α := e.toMonoidHom
  have hf : Function.Surjective f := e.surjective
  letI : Group.FG (FreeGroup α) := Group.fg_of_surjective hf
  letI : Group.FG (Abelianization (FreeGroup α)) := QuotientGroup.fg (commutator (FreeGroup α))
  letI : AddGroup.FG (Additive (Abelianization (FreeGroup α))) := AddGroup.fg_of_group_fg
  let eab : Additive (Abelianization (FreeGroup α)) ≃+ FreeAbelianGroup α := AddEquiv.refl _
  let fab : Additive (Abelianization (FreeGroup α)) →+ FreeAbelianGroup α := eab.toAddMonoidHom
  have hfab : Function.Surjective fab := eab.surjective
  letI : AddGroup.FG (FreeAbelianGroup α) := AddGroup.fg_of_surjective hfab
  exact Module.Finite.finite_basis (FreeAbelianGroup.basis α)

end IsFreeGroup

-- Primary domain: finitely generated free groups via their canonical free basis and finite
-- generating subsets.
-- `source-facing`: a surjective endomorphism `φ : F →* F` of a finitely generated free group.
-- `core/canonical`: `IsFreeGroup.basis F`, `FreeGroupBasis`, and the owner finite-generator
-- rank/basis lemmas from Proposition `1-2-9`.
-- `bridge/view`: the finite image set of the canonical basis under `φ`.
--
-- Domain sampling:
-- 1. `IsFreeGroup.basis F` is mathlib's owner basis for the ambient free group.
-- 2. `fintype_card_le_card_of_generating_finset` is the chapter owner rank inequality for a
--    finite generating set relative to a chosen free basis.
-- 3. `finset_isFreeGroupBasis_iff_card_and_closure_eq_top` is the owner criterion turning a
--    finite generating set of the correct cardinality into a free basis.
-- 4. `[Group.FG F]` is the owner interface for “finitely generated free group”; finiteness of the
--    canonical generator type is derived internally via abelianization and
--    `FreeAbelianGroup.basis`.
--
-- Primitive vs. derived:
-- the primitive data are the ambient owner basis `IsFreeGroup.basis F` and the surjective
-- endomorphism `φ`. The finiteness of `IsFreeGroup.Generators F`, the finite image set of that
-- basis, its basis property, and the resulting inverse homomorphism are derived API and should be
-- built from those owner declarations rather than from an auxiliary `Fin n` coordinate model.

/-- Proposition 1-3-5: every surjective endomorphism of a finitely generated free group is
bijective, so every finitely generated free group is Hopfian. -/
-- Proof sketch: choose the canonical finite free basis `IsFreeGroup.basis F`. The image of that
-- basis under a surjective endomorphism still generates `F`, so the rank comparison argument from
-- the preceding basis-cardinality results forces the image basis to have the same finite
-- cardinality as the original one. A surjective endomorphism carrying one free basis to another is
-- therefore an automorphism, hence bijective.
theorem surjective_endomorphism_bijective (φ : F →* F) (hφ : Function.Surjective φ) :
    Function.Bijective φ := by
  letI : Finite (IsFreeGroup.Generators F) := IsFreeGroup.finite_generators F
  letI : Fintype (IsFreeGroup.Generators F) := Fintype.ofFinite _
  letI : DecidableEq (IsFreeGroup.Generators F) := Classical.decEq _
  letI : DecidableEq F := Classical.decEq _
  let basis := IsFreeGroup.basis F
  let e := basis.repr.symm
  let f : IsFreeGroup.Generators F → F := fun i ↦ φ (basis i)
  let U : Finset F := Finset.univ.image f
  have hgenU : Subgroup.closure (U : Set F) = ⊤ := by
    have hlift : FreeGroup.lift f = φ.comp e.toMonoidHom := by
      apply FreeGroup.ext_hom
      intro i
      simp only [f, FreeGroup.lift_apply_of, MulEquiv.toMonoidHom_eq_coe,
        MonoidHom.coe_comp, MonoidHom.coe_coe, Function.comp_apply]
      rfl
    have hsurj_lift :
        Function.Surjective (FreeGroup.lift f : FreeGroup (IsFreeGroup.Generators F) →* F) := by
      rw [hlift]
      exact hφ.comp e.surjective
    have htop : (FreeGroup.lift f).range = ⊤ := MonoidHom.range_eq_top.2 hsurj_lift
    simpa [U, Finset.coe_image, Set.image_univ, FreeGroup.range_lift_eq_closure] using htop
  have hrank : Fintype.card (IsFreeGroup.Generators F) ≤ U.card := by
    simpa using fintype_card_le_card_of_generating_finset basis U hgenU
  have hcard_le : U.card ≤ Fintype.card (IsFreeGroup.Generators F) := by
    have h : (Finset.univ.image f).card ≤ (Finset.univ : Finset (IsFreeGroup.Generators F)).card :=
      Finset.card_image_le
    simpa [U] using h
  have hcard : U.card = Fintype.card (IsFreeGroup.Generators F) := le_antisymm hcard_le hrank
  have hInjOn : Set.InjOn f (Finset.univ : Finset (IsFreeGroup.Generators F)) := by
    rw [← Finset.card_image_iff]
    simp [U, hcard]
  have hf_injective : Function.Injective f := by
    intro i j hij
    exact hInjOn (by simp) (by simp) hij
  have hUbasis : IsFreeGroupBasis (↑U : Set F) :=
    (finset_isFreeGroupBasis_iff_card_and_closure_eq_top basis U).2 ⟨hcard, hgenU⟩
  let toU : IsFreeGroup.Generators F → U := fun i ↦ ⟨f i, by
    change f i ∈ Finset.univ.image f
    exact Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩⟩
  have htoU_bijective : Function.Bijective toU := by
    constructor
    · intro i j hij
      apply hf_injective
      exact congrArg Subtype.val hij
    · intro u
      rcases Finset.mem_image.mp u.property with ⟨i, -, hi⟩
      exact ⟨i, Subtype.ext hi⟩
  let eU : IsFreeGroup.Generators F ≃ U := Equiv.ofBijective toU htoU_bijective
  let g : U → F := fun u ↦ basis (eU.symm u)
  obtain ⟨ψ, hψ, -⟩ := hUbasis g
  have hleft : ψ.comp φ = MonoidHom.id F := by
    apply basis.ext_hom
    intro i
    have hψi : ψ (f i) = basis i := by
      have hi : eU.symm (toU i) = i := by
        change eU.symm (eU i) = i
        exact eU.left_inv i
      calc
        ψ (f i) = basis (eU.symm (toU i)) := by
          simpa [g, toU] using hψ (toU i)
        _ = basis i := by rw [hi]
    simpa [f, MonoidHom.comp_apply] using hψi
  have hleftInv : Function.LeftInverse ψ φ := by
    intro x
    simpa [MonoidHom.comp_apply] using congrArg (fun χ : F →* F ↦ χ x) hleft
  exact ⟨hleftInv.injective, hφ⟩

/-- A finitely generated free group is Hopfian. -/
instance isHopfian_of_fg_freeGroup : IsHopfian F where
  injective_of_surjective φ hφ :=
    (surjective_endomorphism_bijective φ hφ).1

end

end
