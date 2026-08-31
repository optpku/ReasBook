module

public import Mathlib.CategoryTheory.FiberedCategory.Fiber
public import Mathlib.CategoryTheory.Limits.Final

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits

universe vI vJ vC uI uJ uC

namespace CategoryTheory
namespace Functor

open Fiber IsHomLift

variable {I : Type uI} [Category.{vI} I]
variable {J : Type uJ} [Category.{vJ} J]
variable {C : Type uC} [Category.{vC} C]

variable (F : I ⥤ J)

private def fiberToStructuredArrow {X Y : J} (f : X ⟶ Y) : F.Fiber Y ⥤ StructuredArrow X F where
  obj a := StructuredArrow.mk (f ≫ eqToHom a.2.symm)
  map {a b} φ := StructuredArrow.homMk φ.1 <| by
    let _ : F.IsHomLift (𝟙 Y) φ.1 := by
      simpa using (show F.IsHomLift (𝟙 Y) (Fiber.fiberInclusion.map φ) from inferInstance)
    have hfac : F.map φ.1 = eqToHom a.2 ≫ 𝟙 Y ≫ eqToHom b.2.symm :=
      @IsHomLift.fac' _ _ _ _ F _ _ _ _ (𝟙 Y) φ.1 inferInstance
    simpa [Category.assoc] using
      congrArg (fun k ↦ (StructuredArrow.mk (f ≫ eqToHom a.2.symm)).hom ≫ k) hfac

private def homLiftToStructuredArrow {X Y : J} {a b : I} (f : X ⟶ Y) (g : a ⟶ b)
    [F.IsHomLift f g] :
    (fiberToStructuredArrow F (𝟙 X)).obj (Fiber.mk (IsHomLift.domain_eq F f g)) ⟶
      (fiberToStructuredArrow F f).obj (Fiber.mk (IsHomLift.codomain_eq F f g)) :=
  StructuredArrow.homMk g <| by
    simpa [fiberToStructuredArrow, Category.assoc] using
      congrArg (fun k ↦ eqToHom (IsHomLift.domain_eq F f g).symm ≫ k) (IsHomLift.fac' F f g)

/-
Source/core/bridge triage for Lemma 4.17.5:
- `source-facing`: the Stacks criterion that connected fibers together with arrow-lifting imply
  that `F` is final.
- `core/canonical`: `Functor.Final`, with owner API `Functor.Final.hasColimit_comp_iff` and
  `Functor.Final.colimitIso`.
- `bridge/view`: the anonymous owner-specializations below, which expose the colimit
  consequences directly through the owner API after installing the finality instance.

Primary domain-style sampling:
- project owner recall: `Functor.Final.hasColimit_comp_iff` in `Lemma_4_17_2`;
- project specialization of the same owner API: `Prod.snd` in `Lemma_4_17_6`;
- mathlib owner abstraction: `Functor.Final` in
  `Mathlib/CategoryTheory/Limits/Final.lean`;
- mathlib connected bridge example: `final_snd` in
  `Mathlib/CategoryTheory/Limits/Final/Connected.lean`.

Primitive data are exactly the hypotheses `hfiber` and `hlift`; the colimit-comparison facts
below are derived API once `F.Final` is available. -/
variable
    (hfiber : ∀ j : J, IsConnected (F.Fiber j))
    (hlift : ∀ ⦃X Y : J⦄ (f : X ⟶ Y), ∃ (a b : I) (g : a ⟶ b), F.IsHomLift f g)

include hfiber hlift

/-- Companion bridge for Lemma 4.17.5: the fibre-connectedness and morphism-lifting hypotheses
imply that `F` is final.

Proof sketch: show that each structured-arrow category `StructuredArrow y F` is connected. Use the
connected fibre over `y` to compare objects lying above `y`, and use the hypothesis that every
arrow in `J` lifts through `F` to connect an arbitrary object of `StructuredArrow y F` to one in
the fibre over `y`. -/
theorem final_of_connected_fibers_and_hom_lifts : F.Final := by
  constructor
  intro j
  letI : IsConnected (F.Fiber j) := hfiber j
  letI : Nonempty (StructuredArrow j F) :=
    ⟨(fiberToStructuredArrow F (𝟙 j)).obj (Classical.arbitrary (F.Fiber j))⟩
  apply zigzag_isConnected
  intro A B
  obtain ⟨aA, bA, gA, hgA⟩ := hlift A.hom
  obtain ⟨aB, bB, gB, hgB⟩ := hlift B.hom
  have hdomA : F.obj aA = j :=
    @IsHomLift.domain_eq _ _ _ _ F _ _ _ _ A.hom gA hgA
  have hcodA : F.obj bA = F.obj A.right :=
    @IsHomLift.codomain_eq _ _ _ _ F _ _ _ _ A.hom gA hgA
  have hdomB : F.obj aB = j :=
    @IsHomLift.domain_eq _ _ _ _ F _ _ _ _ B.hom gB hgB
  have hcodB : F.obj bB = F.obj B.right :=
    @IsHomLift.codomain_eq _ _ _ _ F _ _ _ _ B.hom gB hgB
  have hsource :
      Zigzag
        ((fiberToStructuredArrow F (𝟙 j)).obj (Fiber.mk hdomA))
        ((fiberToStructuredArrow F (𝟙 j)).obj (Fiber.mk hdomB)) := by
    simpa [fiberToStructuredArrow] using
      zigzag_obj_of_zigzag (fiberToStructuredArrow F (𝟙 j))
        (isPreconnected_zigzag (Fiber.mk hdomA) (Fiber.mk hdomB))
  have hA :
      Zigzag
        ((fiberToStructuredArrow F (𝟙 j)).obj (Fiber.mk hdomA))
        A := by
    letI : IsConnected (F.Fiber (F.obj A.right)) := hfiber (F.obj A.right)
    let _ : F.IsHomLift A.hom gA := hgA
    let A₁ : F.Fiber (F.obj A.right) := Fiber.mk rfl
    have hA' :
        Zigzag
          ((fiberToStructuredArrow F (𝟙 j)).obj (Fiber.mk hdomA))
          ((fiberToStructuredArrow F A.hom).obj A₁) := by
      refine (Zigzag.of_hom (homLiftToStructuredArrow F A.hom gA)).trans ?_
      simpa [fiberToStructuredArrow] using
        zigzag_obj_of_zigzag (fiberToStructuredArrow F A.hom)
          (isPreconnected_zigzag (Fiber.mk hcodA) A₁)
    have hAend :
        ((fiberToStructuredArrow F A.hom).obj A₁) ⟶
          StructuredArrow.mk A.hom := by
      refine StructuredArrow.homMk (𝟙 A.right) ?_
      dsimp [fiberToStructuredArrow]
      have hp : A₁.2 = rfl :=
        Subsingleton.elim _ _
      have hEq :
          eqToHom A₁.2.symm = 𝟙 (F.obj A.right) := by
        cases hp
        rfl
      have hmap : F.map (𝟙 A.right) = 𝟙 (F.obj A.right) := by
        simpa using F.map_id A.right
      rw [hEq]
      have hmap' :
          A.hom ≫ 𝟙 (F.obj A.right) ≫ F.map (𝟙 A.right) =
            A.hom ≫ 𝟙 (F.obj A.right) ≫ 𝟙 (F.obj A.right) := by
        simpa [Category.assoc] using
          congrArg (fun k ↦ A.hom ≫ 𝟙 (F.obj A.right) ≫ k) hmap
      have hmap'' :
          (A.hom ≫ 𝟙 (F.obj A.right)) ≫ F.map (𝟙 A.right) =
            (A.hom ≫ 𝟙 (F.obj A.right)) ≫ 𝟙 (F.obj A.right) := by
        simpa [Category.assoc] using hmap'
      exact hmap''.trans (by simp)
    rw [StructuredArrow.eq_mk A]
    exact hA'.trans (Zigzag.of_hom hAend)
  have hB :
      Zigzag
        ((fiberToStructuredArrow F (𝟙 j)).obj (Fiber.mk hdomB))
        B := by
    letI : IsConnected (F.Fiber (F.obj B.right)) := hfiber (F.obj B.right)
    let _ : F.IsHomLift B.hom gB := hgB
    let B₁ : F.Fiber (F.obj B.right) := Fiber.mk rfl
    have hB' :
        Zigzag
          ((fiberToStructuredArrow F (𝟙 j)).obj (Fiber.mk hdomB))
          ((fiberToStructuredArrow F B.hom).obj B₁) := by
      refine (Zigzag.of_hom (homLiftToStructuredArrow F B.hom gB)).trans ?_
      simpa [fiberToStructuredArrow] using
        zigzag_obj_of_zigzag (fiberToStructuredArrow F B.hom)
          (isPreconnected_zigzag (Fiber.mk hcodB) B₁)
    have hBend :
        ((fiberToStructuredArrow F B.hom).obj B₁) ⟶
          StructuredArrow.mk B.hom := by
      refine StructuredArrow.homMk (𝟙 B.right) ?_
      dsimp [fiberToStructuredArrow]
      have hp : B₁.2 = rfl :=
        Subsingleton.elim _ _
      have hEq :
          eqToHom B₁.2.symm = 𝟙 (F.obj B.right) := by
        cases hp
        rfl
      have hmap : F.map (𝟙 B.right) = 𝟙 (F.obj B.right) := by
        simpa using F.map_id B.right
      rw [hEq]
      have hmap' :
          B.hom ≫ 𝟙 (F.obj B.right) ≫ F.map (𝟙 B.right) =
            B.hom ≫ 𝟙 (F.obj B.right) ≫ 𝟙 (F.obj B.right) := by
        simpa [Category.assoc] using
          congrArg (fun k ↦ B.hom ≫ 𝟙 (F.obj B.right) ≫ k) hmap
      have hmap'' :
          (B.hom ≫ 𝟙 (F.obj B.right)) ≫ F.map (𝟙 B.right) =
            (B.hom ≫ 𝟙 (F.obj B.right)) ≫ 𝟙 (F.obj B.right) := by
        simpa [Category.assoc] using hmap'
      exact hmap''.trans (by simp)
    rw [StructuredArrow.eq_mk B]
    exact hB'.trans (Zigzag.of_hom hBend)
  exact (hA.symm.trans hsource).trans hB

/-
Under the hypotheses of Lemma 4.17.5, the colimit comparison statements are not new local owners:
they are the direct owner-level consequences of `Functor.Final`.
-/
section

variable (M : J ⥤ C)

/- Lemma 4.17.5 also yields the standard colimit-existence comparison along `F`; this is the
specialization of `Functor.Final.hasColimit_comp_iff` after installing the finality instance from
the source-facing criterion above. -/
#check
  (by
    let _ : F.Final := final_of_connected_fibers_and_hom_lifts F hfiber hlift
    exact (Functor.Final.hasColimit_comp_iff F : HasColimit (F ⋙ M) ↔ HasColimit M))

variable [HasColimit M]

/- Under the same hypotheses, the induced comparison of colimits is exactly the owner isomorphism
`Functor.Final.colimitIso`. -/
#check
  (by
    let _ : F.Final := final_of_connected_fibers_and_hom_lifts F hfiber hlift
    exact (Functor.Final.colimitIso F M : colimit (F ⋙ M) ≅ colimit M))

end

omit hfiber hlift

end Functor
end CategoryTheory
