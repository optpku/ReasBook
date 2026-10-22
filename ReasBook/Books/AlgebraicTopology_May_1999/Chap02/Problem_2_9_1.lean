/-
Authors: Ze Yuan, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import AlgebraicTopology_May_1999.Chap02.Proposition_2_8_6

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open scoped commutatorElement

noncomputable section

/-- The four standard generators in the usual presentation of the genus-2 surface group. -/
inductive GenusTwoSurfaceGenerator
  | a1
  | b1
  | a2
  | b2
deriving DecidableEq, Fintype

/-- The standard relator `[a1,b1][a2,b2]` in the free group on the genus-2 generators. -/
abbrev genus_two_surface_relator : FreeGroup GenusTwoSurfaceGenerator :=
  let a1 := FreeGroup.of GenusTwoSurfaceGenerator.a1
  let b1 := FreeGroup.of GenusTwoSurfaceGenerator.b1
  let a2 := FreeGroup.of GenusTwoSurfaceGenerator.a2
  let b2 := FreeGroup.of GenusTwoSurfaceGenerator.b2
  ⁅a1, b1⁆ * ⁅a2, b2⁆

/-- The standard presentation of the genus-2 surface group. -/
abbrev genus_two_surface_group :=
  PresentedGroup ({genus_two_surface_relator} : Set (FreeGroup GenusTwoSurfaceGenerator))

/-- The defining relator is trivial in the presented genus-2 surface group. -/
-- Proof sketch: `PresentedGroup.mk` kills every element of the chosen relation set, so the unique
-- relator `[a1,b1][a2,b2]` becomes the identity in the quotient group.
theorem genus_two_surface_group_relator_eq_one :
    PresentedGroup.mk ({genus_two_surface_relator} : Set (FreeGroup GenusTwoSurfaceGenerator))
      genus_two_surface_relator =
        (1 : genus_two_surface_group) := by
  exact PresentedGroup.one_of_mem (by simp)

private theorem genus_two_surface_lift_mem_relator_closure (w : FreeGroup Unit) :
    FreeGroup.lift (fun _ : Unit ↦ genus_two_surface_relator) w ∈
      Subgroup.closure
        ({genus_two_surface_relator} : Set (FreeGroup GenusTwoSurfaceGenerator)) := by
  refine FreeGroup.induction_on w ?_ ?_ ?_ ?_
  · exact Subgroup.one_mem _
  · intro _
    exact Subgroup.mem_closure_singleton_self _
  · intro _ h
    simpa using Subgroup.inv_mem _ h
  · intro _ _ hx hy
    simpa using Subgroup.mul_mem _ hx hy

private theorem genus_two_surface_relator_normalClosure_range :
    Subgroup.normalClosure
        (Set.range
          (FreeGroup.lift (fun _ : Unit ↦ genus_two_surface_relator) :
            FreeGroup Unit →* FreeGroup GenusTwoSurfaceGenerator)) =
      Subgroup.normalClosure ({genus_two_surface_relator} :
        Set (FreeGroup GenusTwoSurfaceGenerator)) := by
  refine le_antisymm ?_ ?_
  · apply Subgroup.normalClosure_le_normal
    rintro _ ⟨w, rfl⟩
    exact Subgroup.closure_le_normalClosure (genus_two_surface_lift_mem_relator_closure w)
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
    FundamentalGroup ↥U ⟨x, hxU⟩ ≃* FreeGroup GenusTwoSurfaceGenerator)
  (pi1_inter_equiv :
    FundamentalGroup ↥(U ⊓ V) ⟨x, ⟨hxU, hxV⟩⟩ ≃* FreeGroup Unit)
variable [PathConnectedSpace ↥U] [PathConnectedSpace ↥(U ⊓ V)] [SimplyConnectedSpace V]
variable
  (attaching_map_eq :
    (pi1_U_equiv.toMonoidHom.comp (fundamental_group_inf_to_left U V x hxU hxV)).comp
        pi1_inter_equiv.symm.toMonoidHom =
      FreeGroup.lift fun _ : Unit ↦ genus_two_surface_relator)

/-- Problem 2.9.1: a based space admitting the standard genus-2 cell decomposition, equivalently
the compact surface obtained by sewing two punctured tori along their boundary circle, has
fundamental group the presented group `⟨a1, b1, a2, b2 | [a1,b1][a2,b2] = 1⟩`. -/
-- Proof sketch: apply Proposition 2.8.6 to the open cover `X = U ∪ V`. Since `V` is simply
-- connected, that proposition identifies `π₁(X, x)` with the quotient of `π₁(U, x)` by the normal
-- closure of the image of `π₁(U ∩ V, x)`. Transport the quotient through the free-group
-- identifications in `pi1_U_equiv` and `pi1_inter_equiv`, then use `attaching_map_eq` to identify
-- the killed subgroup with the normal closure of the relator `[a1,b1][a2,b2]`.
def genus_two_surface_fundamental_group
    : FundamentalGroup X x ≃* genus_two_surface_group := by
  let φ := pi1_U_equiv.toMonoidHom
  let ψ := pi1_inter_equiv.symm.toMonoidHom
  let ι := fundamental_group_inf_to_left U V x hxU hxV
  let π : FundamentalGroup ↥U ⟨x, hxU⟩ →* FundamentalGroup X x :=
    FundamentalGroup.map (TopologicalSpace.Opens.inclusion' U).hom ⟨x, hxU⟩
  have hπ_surj : Function.Surjective π :=
    fundamental_group_left_to_union_surjective U V hcover x hxU hxV
  have hπ_ker :
      π.ker =
        Subgroup.normalClosure (Set.range ι) := by
    simpa [ι] using
      fundamental_group_left_to_union_ker_eq_normal_closure_range
        U V hcover x hxU hxV
  have hrange :
      Set.range (φ.comp ι) =
        Set.range (FreeGroup.lift fun _ : Unit ↦ genus_two_surface_relator) := by
    calc
      Set.range (φ.comp ι) = Set.range ((φ.comp ι).comp ψ) := by
          ext y
          constructor
          · rintro ⟨z, rfl⟩
            exact ⟨pi1_inter_equiv z, by simp [φ, ψ]⟩
          · rintro ⟨z, rfl⟩
            exact ⟨pi1_inter_equiv.symm z, by simp [φ, ψ]⟩
      _ = Set.range (FreeGroup.lift fun _ : Unit ↦ genus_two_surface_relator) := by
          simpa only [φ, ι, ψ] using
            congrArg
              (fun f : FreeGroup Unit →* FreeGroup GenusTwoSurfaceGenerator ↦ Set.range f)
              attaching_map_eq
  have hmap_ker :
      π.ker.map φ =
        Subgroup.normalClosure ({genus_two_surface_relator} :
          Set (FreeGroup GenusTwoSurfaceGenerator)) := by
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
            (Set.range (FreeGroup.lift fun _ : Unit ↦ genus_two_surface_relator)) := by
            rw [hrange]
      _ =
          Subgroup.normalClosure ({genus_two_surface_relator} :
            Set (FreeGroup GenusTwoSurfaceGenerator)) := by
            exact genus_two_surface_relator_normalClosure_range
  exact
    (QuotientGroup.quotientKerEquivOfSurjective π hπ_surj).symm.trans <|
      by
        simpa [genus_two_surface_group] using
          QuotientGroup.congr π.ker
            (Subgroup.normalClosure ({genus_two_surface_relator} :
              Set (FreeGroup GenusTwoSurfaceGenerator)))
            pi1_U_equiv hmap_ker

end
