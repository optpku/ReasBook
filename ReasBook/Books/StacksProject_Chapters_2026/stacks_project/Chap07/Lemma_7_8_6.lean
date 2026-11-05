module

public import Mathlib.CategoryTheory.Sites.Coverage
public import stacks_project.Chap07.Lemma_7_8_3
public import stacks_project.Chap07.Definition_7_12_1

@[expose] public section

open Opposite
open CategoryTheory.Limits
universe w v u u₁ u₂

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]

namespace SemiRepresentableFamily
namespace Over

/- Domain-style sampling for Lemma 7.8.6:
- primary domain: fixed-target covering families and descent of the sheaf condition along a
  refinement;
- inspected owner declarations:
  `SemiRepresentableFamily.Over.Refines`,
  `SemiRepresentableFamily.Over.toPresieve`,
  `SemiRepresentableFamily.Over.baseChange`,
  `Presieve.isSheafFor_of_factorsThru`;
- best owner abstraction: the source-facing cover data live in `SemiRepresentableFamily.Over U`,
  with `Refines` as the refinement relation and `toPresieve`/`baseChange` as the canonical
  bridge to the sheaf-condition and pullback-cover owners;
- primitive data: a refinement relation `Refines 𝒱 𝒰`, the pullback existence hypotheses needed to
  form `baseChange`, and the injectivity of the pullback restriction maps;
- derived API: the sheaf condition on `𝒰`, obtained from the core owner theorem
  `Presieve.isSheafFor_of_factorsThru`.

Source/core/bridge triage:
- `source-facing`: descent of the sheaf condition along a refinement of fixed-target families;
- `core/canonical`: `Presieve.isSheafFor_of_factorsThru`;
- `bridge/view`: `toPresieve` and `baseChange`, translating the family-level statement into the
  canonical presieve language.
-/

-- Proof sketch: pull a compatible family on `𝒰` back along a refinement of fixed-target families
-- from `𝒱` to obtain a compatible family on `𝒱`. Glue over `𝒱` using the sheaf condition, then
-- restrict the glued section to each member `Uᵢ` of `𝒰` and compare on the pullback family
-- `baseChange 𝒱 (𝒰.obj i).hom`. Injectivity of that restriction map forces the glued
-- section to recover the prescribed component over `Uᵢ`.
/-- Lemma 7.8.6: if a fixed-target family `𝒱` refines `𝒰`, `F` satisfies the sheaf condition for
`𝒱`, and for each `i` the restriction map from `F(U_i)` to the family over the pullbacks
`U_i ×[U] V_j` is injective, then `F` satisfies the sheaf condition for `𝒰`. -/
theorem isSheafFor_of_refinement_and_injective_pullback_restrictions
    {U : C} {𝒰 𝒱 : Over U}
    (hφ : Refines 𝒱 𝒰)
    (F : Cᵒᵖ ⥤ Type w)
    (hpb : ∀ i : 𝒰.index, ∀ j : 𝒱.index, HasPullback (𝒱.obj j).hom (𝒰.obj i).hom)
    (h𝒱 : (toPresieve 𝒱).IsSheafFor F)
    (hsep : ∀ i : 𝒰.index,
      Function.Injective
        (fun s : F.obj (op ((𝒰.obj i).left)) ↦
          fun j : (baseChange 𝒱 (𝒰.obj i).hom).index ↦
            F.map (((baseChange 𝒱 (𝒰.obj i).hom).obj j).hom).op s)) :
    (toPresieve 𝒰).IsSheafFor F := by
  rcases hφ with ⟨φ⟩
  refine Presieve.isSheafFor_of_factorsThru F ?_ h𝒱 ?_
  · intro Y f hf
    obtain ⟨j, rfl, rfl⟩ := Presieve.ofArrows_surj (fun j : 𝒱.index ↦ (𝒱.obj j).hom) f hf
    refine ⟨(𝒰.obj (φ.α j)).left, (φ.f j).left, (𝒰.obj (φ.α j)).hom,
      Presieve.ofArrows.mk (φ.α j), ?_⟩
    simpa using Over.w (φ.f j)
  · intro Y f hf
    obtain ⟨i, rfl, rfl⟩ := Presieve.ofArrows_surj (fun i : 𝒰.index ↦ (𝒰.obj i).hom) f hf
    letI : ∀ j : 𝒱.index, HasPullback (𝒱.obj j).hom (𝒰.obj i).hom := hpb i
    refine ⟨
      toPresieve (baseChange 𝒱 (𝒰.obj i).hom),
      ?_, ?_⟩
    · intro x s t hs ht
      apply hsep i
      funext j
      exact (hs _ (Presieve.ofArrows.mk j)).trans (ht _ (Presieve.ofArrows.mk j)).symm
    · intro Z g hg
      obtain ⟨j, rfl, rfl⟩ := Presieve.ofArrows_surj
        (fun j : (baseChange 𝒱 (𝒰.obj i).hom).index ↦ ((baseChange 𝒱 (𝒰.obj i).hom).obj j).hom)
        g hg
      refine ⟨(𝒱.obj j).left, pullback.fst (𝒱.obj j).hom (𝒰.obj i).hom, (𝒱.obj j).hom,
        Presieve.ofArrows.mk j, ?_⟩
      simpa [baseChange_obj_hom] using
        (pullback.condition :
          pullback.fst (𝒱.obj j).hom (𝒰.obj i).hom ≫ (𝒱.obj j).hom =
            pullback.snd (𝒱.obj j).hom (𝒰.obj i).hom ≫ (𝒰.obj i).hom)

end Over
end SemiRepresentableFamily

open SemiRepresentableFamily.Over

-- Proof sketch: package the indexed arrow families as objects of `SemiRepresentableFamily.Over U`,
-- assemble the refinement data into the canonical relation `Refines 𝒱 𝒰`, rewrite the pullback
-- restriction hypothesis using `SemiRepresentableFamily.Over.baseChange`, and invoke the canonical
-- family-level statement above.
/-- Companion formulation of Lemma 7.8.6 for explicit indexed arrow families. -/
theorem isSheafFor_of_refinement_and_injective_pullback_restrictions
    {U : C} {I : Type u₁} {Ui : I → C} (π : ∀ i : I, Ui i ⟶ U)
    {J : Type u₂} {Vj : J → C} (ψ : ∀ j : J, Vj j ⟶ U)
    (α : J → I) (f : ∀ j : J, Vj j ⟶ Ui (α j))
    (hf : ∀ j : J, f j ≫ π (α j) = ψ j)
    (F : Cᵒᵖ ⥤ Type w)
    (hpb : ∀ i : I, ∀ j : J, HasPullback (ψ j) (π i))
    (hV : Presieve.IsSheafFor F (Presieve.ofArrows Vj ψ))
    (hsep : ∀ i : I,
      Function.Injective
        (fun s : F.obj (op (Ui i)) ↦
          fun j : J ↦ F.map (pullback.snd (ψ j) (π i)).op s)) :
    Presieve.IsSheafFor F (Presieve.ofArrows Ui π) := by
  let 𝒰 :=
    ofArrows
      (fun i : ULift.{max u₁ u₂} I ↦ Ui i.down)
      (fun i : ULift.{max u₁ u₂} I ↦ π i.down)
  let 𝒱 :=
    ofArrows
      (fun j : ULift.{max u₁ u₂} J ↦ Vj j.down)
      (fun j : ULift.{max u₁ u₂} J ↦ ψ j.down)
  have h𝒰 : toPresieve 𝒰 = Presieve.ofArrows Ui π := by
    simpa [𝒰] using (toPresieve_ofArrows_ulift Ui π)
  have h𝒱 : toPresieve 𝒱 = Presieve.ofArrows Vj ψ := by
    simpa [𝒱] using (toPresieve_ofArrows_ulift Vj ψ)
  have hφ : Refines 𝒱 𝒰 := ⟨
    { α := fun j ↦ ⟨α j.down⟩
      f := fun j ↦ Over.homMk (f j.down) (hf j.down) }⟩
  have hpb' : ∀ i : 𝒰.index, ∀ j : 𝒱.index, HasPullback (𝒱.obj j).hom (𝒰.obj i).hom := by
    intro i j
    exact hpb i.down j.down
  have hV' : (toPresieve 𝒱).IsSheafFor F := by
    simpa [h𝒱] using hV
  have hsep' : ∀ i : 𝒰.index,
      Function.Injective
        (fun s : F.obj (op (𝒰.obj i).left) ↦
          fun j : (baseChange 𝒱 (𝒰.obj i).hom).index ↦
            F.map ((baseChange 𝒱 (𝒰.obj i).hom).obj j).hom.op s) := by
    intro i s t hst
    apply hsep i.down
    funext j
    simpa [baseChange_obj_hom] using congrFun hst (ULift.up j)
  simpa [h𝒰] using
    SemiRepresentableFamily.Over.isSheafFor_of_refinement_and_injective_pullback_restrictions
      hφ F hpb' hV' hsep'

end CategoryTheory
