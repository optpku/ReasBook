/-
Authors: Ze Yuan, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import AlgebraicTopology_May_1999.Chap02.Proposition_2_8_6

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open CategoryTheory
open TopologicalSpace.Opens

noncomputable section

/-- The two standard generators in the usual presentation of the Klein bottle group. -/
inductive KleinBottleGenerator
  | a
  | b
deriving DecidableEq, Fintype

/-- The standard Klein-bottle relator `aba⁻¹b` in the free group on the two generators. -/
abbrev klein_bottle_relator : FreeGroup KleinBottleGenerator :=
  let a := FreeGroup.of KleinBottleGenerator.a
  let b := FreeGroup.of KleinBottleGenerator.b
  a * b * a⁻¹ * b

/-- The standard presentation of the Klein bottle group. -/
abbrev klein_bottle_group :=
  PresentedGroup ({klein_bottle_relator} : Set (FreeGroup KleinBottleGenerator))

/-- The defining relator is trivial in the presented Klein bottle group. -/
-- Proof sketch: `PresentedGroup.mk` kills every element of the chosen relation set, so the unique
-- relator `aba⁻¹b` becomes the identity in the quotient group.
theorem klein_bottle_group_relator_eq_one :
    PresentedGroup.mk ({klein_bottle_relator} : Set (FreeGroup KleinBottleGenerator))
      klein_bottle_relator =
        (1 : klein_bottle_group) := by
  exact PresentedGroup.one_of_mem (by simp)

private theorem klein_bottle_lift_mem_relator_closure (w : FreeGroup Unit) :
    FreeGroup.lift (fun _ : Unit ↦ klein_bottle_relator) w ∈
      Subgroup.closure ({klein_bottle_relator} : Set (FreeGroup KleinBottleGenerator)) := by
  refine FreeGroup.induction_on w ?_ ?_ ?_ ?_
  · exact Subgroup.one_mem _
  · intro _
    exact Subgroup.mem_closure_singleton_self _
  · intro _ h
    simpa using Subgroup.inv_mem _ h
  · intro _ _ hx hy
    simpa using Subgroup.mul_mem _ hx hy

private theorem klein_bottle_relator_normalClosure_range :
    Subgroup.normalClosure
        (Set.range
          (FreeGroup.lift (fun _ : Unit ↦ klein_bottle_relator) :
            FreeGroup Unit →* FreeGroup KleinBottleGenerator)) =
      Subgroup.normalClosure ({klein_bottle_relator} :
        Set (FreeGroup KleinBottleGenerator)) := by
  refine le_antisymm ?_ ?_
  · apply Subgroup.normalClosure_le_normal
    rintro _ ⟨w, rfl⟩
    exact Subgroup.closure_le_normalClosure (klein_bottle_lift_mem_relator_closure w)
  · apply Subgroup.normalClosure_mono
    intro y hy
    rcases Set.mem_singleton_iff.mp hy with rfl
    exact ⟨FreeGroup.of (), by simp⟩

variable {X : Type u} [TopologicalSpace X]

section

variable (U V : TopologicalSpace.Opens (TopCat.of X)) (hcover : U ⊔ V = ⊤)
variable (x : X) (hxU : x ∈ U) (hxV : x ∈ V)
variable
  (pi1_U_equiv :
    FundamentalGroup ↥U ⟨x, hxU⟩ ≃* FreeGroup KleinBottleGenerator)
  (pi1_inter_equiv :
    FundamentalGroup ↥(U ⊓ V) ⟨x, ⟨hxU, hxV⟩⟩ ≃* FreeGroup Unit)
variable [PathConnectedSpace ↥U] [PathConnectedSpace ↥(U ⊓ V)] [SimplyConnectedSpace V]
variable
  (attaching_map_eq :
    (pi1_U_equiv.toMonoidHom.comp (fundamental_group_inf_to_left U V x hxU hxV)).comp
        pi1_inter_equiv.symm.toMonoidHom =
      FreeGroup.lift fun _ : Unit ↦ klein_bottle_relator)

/-- Problem 2.9.2: a based space admitting the standard Klein-bottle decomposition, equivalently
the quotient `(S^1 × I)/(z,0) ∼ (z⁻¹,1)`, has fundamental group
`⟨a, b \mid aba^{-1}b = 1⟩`, equivalently `⟨a, b \mid aba^{-1} = b^{-1}⟩`. -/
-- Proof sketch: apply the two-open-set van Kampen theorem to the decomposition `X = U ∪ V`.
-- Because `V` is simply connected, the resulting pushout identifies `π₁(X,x)` with the quotient
-- of `π₁(U,x)` by the normal closure of the image of `π₁(U ∩ V,x)`. Transport this quotient
-- through `pi1_U_equiv` and `pi1_inter_equiv`, then use `attaching_map_eq` to identify the killed
-- subgroup with the normal closure of the single relator `aba⁻¹b`.
def klein_bottle_fundamental_group :
    FundamentalGroup X x ≃* klein_bottle_group :=
  let φ := pi1_U_equiv.toMonoidHom
  let ψ := pi1_inter_equiv.symm.toMonoidHom
  let ι := fundamental_group_inf_to_left U V x hxU hxV
  let π : FundamentalGroup ↥U ⟨x, hxU⟩ →* FundamentalGroup X x :=
    FundamentalGroup.map (inclusion' U).hom ⟨x, hxU⟩
  let hπ_surj : Function.Surjective π :=
    fundamental_group_left_to_union_surjective U V hcover x hxU hxV
  let hπ_ker :
      π.ker =
        Subgroup.normalClosure (Set.range ι) := by
    simpa [ι] using
      fundamental_group_left_to_union_ker_eq_normal_closure_range
        U V hcover x hxU hxV
  let hrange :
      Set.range (φ.comp ι) =
        Set.range (FreeGroup.lift fun _ : Unit ↦ klein_bottle_relator) := by
    calc
      Set.range (φ.comp ι) = Set.range ((φ.comp ι).comp ψ) := by
          ext y
          constructor
          · rintro ⟨z, rfl⟩
            exact ⟨pi1_inter_equiv z, by simp [φ, ψ]⟩
          · rintro ⟨z, rfl⟩
            exact ⟨pi1_inter_equiv.symm z, by simp [φ, ψ]⟩
      _ = Set.range (FreeGroup.lift fun _ : Unit ↦ klein_bottle_relator) := by
          simpa only [φ, ι, ψ] using
            congrArg
              (fun f : FreeGroup Unit →* FreeGroup KleinBottleGenerator ↦ Set.range f)
              attaching_map_eq
  let hmap_ker :
      π.ker.map φ =
        Subgroup.normalClosure ({klein_bottle_relator} :
          Set (FreeGroup KleinBottleGenerator)) := by
    calc
      π.ker.map φ = (Subgroup.normalClosure (Set.range ι)).map φ := by
            rw [hπ_ker]
      _ =
          Subgroup.normalClosure (φ '' Set.range ι) := by
            rw [Subgroup.map_normalClosure _ _ pi1_U_equiv.surjective]
      _ = Subgroup.normalClosure (Set.range (φ.comp ι)) := by
            congr 1
            ext y
            constructor
            · rintro ⟨z, ⟨w, rfl⟩, rfl⟩
              exact ⟨w, rfl⟩
            · rintro ⟨w, rfl⟩
              exact ⟨_, ⟨w, rfl⟩, rfl⟩
      _ =
          Subgroup.normalClosure
            (Set.range (FreeGroup.lift fun _ : Unit ↦ klein_bottle_relator)) := by
            rw [hrange]
      _ =
          Subgroup.normalClosure ({klein_bottle_relator} :
            Set (FreeGroup KleinBottleGenerator)) := by
            exact klein_bottle_relator_normalClosure_range
  (QuotientGroup.quotientKerEquivOfSurjective π hπ_surj).symm.trans <|
    by
      simpa [klein_bottle_group] using
        QuotientGroup.congr π.ker
          (Subgroup.normalClosure ({klein_bottle_relator} :
            Set (FreeGroup KleinBottleGenerator)))
          pi1_U_equiv hmap_ker

end
