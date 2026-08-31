module

public import stacks_project.Chap07.Lemma_7_39_1.BranchSystem

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open GrothendieckTopology.Point
open CategoryTheory.SemiRepresentableFamily.Over

universe u v w

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]

attribute [local instance] initiallySmall_of_essentiallySmall

section

variable {J : GrothendieckTopology C}

open GrothendieckTopology.Point.ofIsCofiltered
open CategoryTheory.SemiRepresentableFamily.Over

variable (J)

/-- Helper for Lemma 7.39.1: a common representative at stage `j₁` of the original inverse
system gives two actual tail germs whose images are `s` and `s'`. -/
theorem common_tail_stage_sections
    {ι : Type w} [Preorder ι] (S' : ιᵒᵖ ⥤ C) (j₁ : ι)
    {Fobj : Cᵒᵖ ⥤ Type (max u v w)}
    {s s' : (fiber.{max u v w} S').presheafFiber.obj Fobj}
    {t₁ t₁' : Fobj.obj (op (S'.obj (op j₁)))}
    (hs₁ :
      (fiber.{max u v w} S').toPresheafFiber (S'.obj (op j₁))
        (fiberMk.{max u v w} (𝟙 (S'.obj (op j₁)))) Fobj t₁ = s)
    (hs₁' :
      (fiber.{max u v w} S').toPresheafFiber (S'.obj (op j₁))
        (fiberMk.{max u v w} (𝟙 (S'.obj (op j₁)))) Fobj t₁' = s')
    (hss' : s ≠ s') :
    ∃ ŝ ŝ' : (fiber.{max u v w} (tail_system S' j₁)).presheafFiber.obj Fobj,
      ((refinementFiber (tail_inclusion j₁) S' (Iso.refl _)).presheafFiber).app Fobj ŝ = s ∧
      ((refinementFiber (tail_inclusion j₁) S' (Iso.refl _)).presheafFiber).app Fobj ŝ' = s' ∧
      ŝ ≠ ŝ' := by
  let jTail : Set.Ici j₁ := ⟨j₁, le_rfl⟩
  let xTail : (fiber.{max u v w} (tail_system S' j₁)).obj (S'.obj (op j₁)) :=
    fiberMk.{max u v w} (U := op jTail) (X := S'.obj (op j₁)) (𝟙 (S'.obj (op j₁)))
  let ŝ : (fiber.{max u v w} (tail_system S' j₁)).presheafFiber.obj Fobj :=
    (fiber.{max u v w} (tail_system S' j₁)).toPresheafFiber (S'.obj (op j₁)) xTail Fobj t₁
  let ŝ' : (fiber.{max u v w} (tail_system S' j₁)).presheafFiber.obj Fobj :=
    (fiber.{max u v w} (tail_system S' j₁)).toPresheafFiber (S'.obj (op j₁)) xTail Fobj t₁'
  have hŝ :
      ((refinementFiber (tail_inclusion j₁) S' (Iso.refl _)).presheafFiber).app Fobj ŝ = s := by
    -- Evaluate the tail-to-original refinement on the first canonical tail generator.
    have hrewrite :
        (fiber.{max u v w} S').toPresheafFiber (S'.obj (op j₁))
          ((refinementFiber (tail_inclusion j₁) S' (Iso.refl _)).app
            (S'.obj (op j₁)) xTail) Fobj t₁ =
          (fiber.{max u v w} S').toPresheafFiber (S'.obj (op j₁))
            (fiberMk.{max u v w} (𝟙 (S'.obj (op j₁)))) Fobj t₁ := by
      have hrewrite₀ :
          (fiber.{max u v w} S').toPresheafFiber (S'.obj (op j₁))
            ((refinementFiber (tail_inclusion j₁) S' (Iso.refl _)).app
              (S'.obj (op j₁)) xTail) Fobj t₁ =
            (fiber.{max u v w} S').toPresheafFiber (S'.obj (op j₁))
              (fiberMk.{max u v w}
                ((Iso.refl ((tail_inclusion j₁).toOrderHom.toFunctor.op ⋙ S')).inv.app
                  (op jTail) ≫ 𝟙 (S'.obj (op j₁)))) Fobj t₁ := by
        simpa only [jTail, xTail] using
          congrArg
            (fun x ↦
              (fiber.{max u v w} S').toPresheafFiber (S'.obj (op j₁)) x Fobj t₁)
            (refinementFiber_app_fiberMk (j := tail_inclusion j₁) (T := S') (e := Iso.refl _)
              (U := op jTail) (W := S'.obj (op j₁)) (f := 𝟙 (S'.obj (op j₁))))
      have hrewrite₁ :
          (fiber.{max u v w} S').toPresheafFiber (S'.obj (op j₁))
              (fiberMk.{max u v w}
                ((Iso.refl ((tail_inclusion j₁).toOrderHom.toFunctor.op ⋙ S')).inv.app
                  (op jTail) ≫ 𝟙 (S'.obj (op j₁)))) Fobj t₁ =
            (fiber.{max u v w} S').toPresheafFiber (S'.obj (op j₁))
              (fiberMk.{max u v w} (𝟙 (S'.obj (op j₁)))) Fobj t₁ := by
        have hunit :
            (Iso.refl ((tail_inclusion j₁).toOrderHom.toFunctor.op ⋙ S')).inv.app (op jTail) ≫
              𝟙 (S'.obj (op j₁)) =
            𝟙 (S'.obj (op j₁)) := by
          simp [jTail]
        exact congrArg
          (fun g ↦
            (fiber.{max u v w} S').toPresheafFiber (S'.obj (op j₁))
              (fiberMk.{max u v w} g) Fobj t₁)
          hunit
      exact hrewrite₀.trans hrewrite₁
    calc
      ((refinementFiber (tail_inclusion j₁) S' (Iso.refl _)).presheafFiber).app Fobj ŝ =
          (fiber.{max u v w} S').toPresheafFiber (S'.obj (op j₁))
            ((refinementFiber (tail_inclusion j₁) S' (Iso.refl _)).app
              (S'.obj (op j₁)) xTail) Fobj t₁ := by
              simpa [ŝ, xTail] using
                congrFun
                  (NatTrans.toPresheafFiber_presheafFiber_app
                    (η := refinementFiber (tail_inclusion j₁) S' (Iso.refl _))
                    (F := Fobj) (X := S'.obj (op j₁)) xTail)
                  t₁
      _ = (fiber.{max u v w} S').toPresheafFiber (S'.obj (op j₁))
            (fiberMk.{max u v w} (𝟙 (S'.obj (op j₁)))) Fobj t₁ := hrewrite
      _ = s := hs₁
  have hŝ' :
      ((refinementFiber (tail_inclusion j₁) S' (Iso.refl _)).presheafFiber).app Fobj ŝ' = s' := by
    -- The same normalization identifies the second tail generator with `s'`.
    have hrewrite :
        (fiber.{max u v w} S').toPresheafFiber (S'.obj (op j₁))
          ((refinementFiber (tail_inclusion j₁) S' (Iso.refl _)).app
            (S'.obj (op j₁)) xTail) Fobj t₁' =
          (fiber.{max u v w} S').toPresheafFiber (S'.obj (op j₁))
            (fiberMk.{max u v w} (𝟙 (S'.obj (op j₁)))) Fobj t₁' := by
      have hrewrite₀ :
          (fiber.{max u v w} S').toPresheafFiber (S'.obj (op j₁))
            ((refinementFiber (tail_inclusion j₁) S' (Iso.refl _)).app
              (S'.obj (op j₁)) xTail) Fobj t₁' =
            (fiber.{max u v w} S').toPresheafFiber (S'.obj (op j₁))
              (fiberMk.{max u v w}
                ((Iso.refl ((tail_inclusion j₁).toOrderHom.toFunctor.op ⋙ S')).inv.app
                  (op jTail) ≫ 𝟙 (S'.obj (op j₁)))) Fobj t₁' := by
        simpa only [jTail, xTail] using
          congrArg
            (fun x ↦
              (fiber.{max u v w} S').toPresheafFiber (S'.obj (op j₁)) x Fobj t₁')
            (refinementFiber_app_fiberMk (j := tail_inclusion j₁) (T := S') (e := Iso.refl _)
              (U := op jTail) (W := S'.obj (op j₁)) (f := 𝟙 (S'.obj (op j₁))))
      have hrewrite₁ :
          (fiber.{max u v w} S').toPresheafFiber (S'.obj (op j₁))
              (fiberMk.{max u v w}
                ((Iso.refl ((tail_inclusion j₁).toOrderHom.toFunctor.op ⋙ S')).inv.app
                  (op jTail) ≫ 𝟙 (S'.obj (op j₁)))) Fobj t₁' =
            (fiber.{max u v w} S').toPresheafFiber (S'.obj (op j₁))
              (fiberMk.{max u v w} (𝟙 (S'.obj (op j₁)))) Fobj t₁' := by
        have hunit :
            (Iso.refl ((tail_inclusion j₁).toOrderHom.toFunctor.op ⋙ S')).inv.app (op jTail) ≫
              𝟙 (S'.obj (op j₁)) =
            𝟙 (S'.obj (op j₁)) := by
          simp [jTail]
        exact congrArg
          (fun g ↦
            (fiber.{max u v w} S').toPresheafFiber (S'.obj (op j₁))
              (fiberMk.{max u v w} g) Fobj t₁')
          hunit
      exact hrewrite₀.trans hrewrite₁
    calc
      ((refinementFiber (tail_inclusion j₁) S' (Iso.refl _)).presheafFiber).app Fobj ŝ' =
          (fiber.{max u v w} S').toPresheafFiber (S'.obj (op j₁))
            ((refinementFiber (tail_inclusion j₁) S' (Iso.refl _)).app
              (S'.obj (op j₁)) xTail) Fobj t₁' := by
              simpa [ŝ', xTail] using
                congrFun
                  (NatTrans.toPresheafFiber_presheafFiber_app
                    (η := refinementFiber (tail_inclusion j₁) S' (Iso.refl _))
                    (F := Fobj) (X := S'.obj (op j₁)) xTail)
                  t₁'
      _ = (fiber.{max u v w} S').toPresheafFiber (S'.obj (op j₁))
            (fiberMk.{max u v w} (𝟙 (S'.obj (op j₁)))) Fobj t₁' := hrewrite
      _ = s' := hs₁'
  have hne : ŝ ≠ ŝ' := by
    -- Distinct images in the original raw fiber force the two tail germs to be distinct.
    intro hEq
    apply hss'
    have hImage :
        ((refinementFiber (tail_inclusion j₁) S' (Iso.refl _)).presheafFiber).app Fobj ŝ =
          ((refinementFiber (tail_inclusion j₁) S' (Iso.refl _)).presheafFiber).app Fobj ŝ' := by
      simp [hEq]
    exact hŝ.symm.trans (hImage.trans hŝ')
  exact ⟨ŝ, ŝ', hŝ, hŝ', hne⟩

/-- Helper for Lemma 7.39.1: the explicit canonical tail-stage germs at `j₁` already map back to
`s` and `s'`, and they stay distinct. -/
theorem canonical_tail_stage_sections
    {ι : Type w} [Preorder ι] (S' : ιᵒᵖ ⥤ C) (j₁ : ι)
    {Fobj : Cᵒᵖ ⥤ Type (max u v w)}
    {s s' : (fiber.{max u v w} S').presheafFiber.obj Fobj}
    {t₁ t₁' : Fobj.obj (op (S'.obj (op j₁)))}
    (hs₁ :
      (fiber.{max u v w} S').toPresheafFiber (S'.obj (op j₁))
        (fiberMk.{max u v w} (𝟙 (S'.obj (op j₁)))) Fobj t₁ = s)
    (hs₁' :
      (fiber.{max u v w} S').toPresheafFiber (S'.obj (op j₁))
        (fiberMk.{max u v w} (𝟙 (S'.obj (op j₁)))) Fobj t₁' = s')
    (hss' : s ≠ s') :
    let jTail : Set.Ici j₁ := ⟨j₁, le_rfl⟩
    let xTail : (fiber.{max u v w} (tail_system S' j₁)).obj (S'.obj (op j₁)) :=
      fiberMk.{max u v w} (U := op jTail) (X := S'.obj (op j₁)) (𝟙 (S'.obj (op j₁)))
    let ŝ : (fiber.{max u v w} (tail_system S' j₁)).presheafFiber.obj Fobj :=
      (fiber.{max u v w} (tail_system S' j₁)).toPresheafFiber (S'.obj (op j₁)) xTail Fobj t₁
    let ŝ' : (fiber.{max u v w} (tail_system S' j₁)).presheafFiber.obj Fobj :=
      (fiber.{max u v w} (tail_system S' j₁)).toPresheafFiber (S'.obj (op j₁)) xTail Fobj t₁'
    ((refinementFiber (tail_inclusion j₁) S' (Iso.refl _)).presheafFiber).app Fobj ŝ = s ∧
      ((refinementFiber (tail_inclusion j₁) S' (Iso.refl _)).presheafFiber).app Fobj ŝ' = s' ∧
      ŝ ≠ ŝ' := by
  let jTail : Set.Ici j₁ := ⟨j₁, le_rfl⟩
  let xTail : (fiber.{max u v w} (tail_system S' j₁)).obj (S'.obj (op j₁)) :=
    fiberMk.{max u v w} (U := op jTail) (X := S'.obj (op j₁)) (𝟙 (S'.obj (op j₁)))
  let ŝ : (fiber.{max u v w} (tail_system S' j₁)).presheafFiber.obj Fobj :=
    (fiber.{max u v w} (tail_system S' j₁)).toPresheafFiber (S'.obj (op j₁)) xTail Fobj t₁
  let ŝ' : (fiber.{max u v w} (tail_system S' j₁)).presheafFiber.obj Fobj :=
    (fiber.{max u v w} (tail_system S' j₁)).toPresheafFiber (S'.obj (op j₁)) xTail Fobj t₁'
  have hŝ :
      ((refinementFiber (tail_inclusion j₁) S' (Iso.refl _)).presheafFiber).app Fobj ŝ = s := by
    -- Evaluate the tail-to-original refinement on the first canonical tail generator.
    have hrewrite :
        (fiber.{max u v w} S').toPresheafFiber (S'.obj (op j₁))
          ((refinementFiber (tail_inclusion j₁) S' (Iso.refl _)).app
            (S'.obj (op j₁)) xTail) Fobj t₁ =
        (fiber.{max u v w} S').toPresheafFiber (S'.obj (op j₁))
          (fiberMk.{max u v w} (𝟙 (S'.obj (op j₁)))) Fobj t₁ := by
      have hrewrite₀ :
          (fiber.{max u v w} S').toPresheafFiber (S'.obj (op j₁))
            ((refinementFiber (tail_inclusion j₁) S' (Iso.refl _)).app
              (S'.obj (op j₁)) xTail) Fobj t₁ =
          (fiber.{max u v w} S').toPresheafFiber (S'.obj (op j₁))
            (fiberMk.{max u v w}
              ((Iso.refl ((tail_inclusion j₁).toOrderHom.toFunctor.op ⋙ S')).inv.app
                (op jTail) ≫ 𝟙 (S'.obj (op j₁)))) Fobj t₁ := by
        simpa only [jTail, xTail] using
          congrArg
            (fun x ↦
              (fiber.{max u v w} S').toPresheafFiber (S'.obj (op j₁)) x Fobj t₁)
            (refinementFiber_app_fiberMk (j := tail_inclusion j₁) (T := S') (e := Iso.refl _)
              (U := op jTail) (W := S'.obj (op j₁)) (f := 𝟙 (S'.obj (op j₁))))
      have hrewrite₁ :
          (fiber.{max u v w} S').toPresheafFiber (S'.obj (op j₁))
              (fiberMk.{max u v w}
                ((Iso.refl ((tail_inclusion j₁).toOrderHom.toFunctor.op ⋙ S')).inv.app
                  (op jTail) ≫ 𝟙 (S'.obj (op j₁)))) Fobj t₁ =
            (fiber.{max u v w} S').toPresheafFiber (S'.obj (op j₁))
              (fiberMk.{max u v w} (𝟙 (S'.obj (op j₁)))) Fobj t₁ := by
        have hunit :
            (Iso.refl ((tail_inclusion j₁).toOrderHom.toFunctor.op ⋙ S')).inv.app (op jTail) ≫
              𝟙 (S'.obj (op j₁)) =
            𝟙 (S'.obj (op j₁)) := by
          simp [jTail]
        exact congrArg
          (fun g ↦
            (fiber.{max u v w} S').toPresheafFiber (S'.obj (op j₁))
              (fiberMk.{max u v w} g) Fobj t₁)
          hunit
      exact hrewrite₀.trans hrewrite₁
    calc
      ((refinementFiber (tail_inclusion j₁) S' (Iso.refl _)).presheafFiber).app Fobj ŝ =
          (fiber.{max u v w} S').toPresheafFiber (S'.obj (op j₁))
            ((refinementFiber (tail_inclusion j₁) S' (Iso.refl _)).app
              (S'.obj (op j₁)) xTail) Fobj t₁ := by
              simpa [ŝ, xTail] using
                congrFun
                  (NatTrans.toPresheafFiber_presheafFiber_app
                    (η := refinementFiber (tail_inclusion j₁) S' (Iso.refl _))
                    (F := Fobj) (X := S'.obj (op j₁)) xTail)
                  t₁
      _ = (fiber.{max u v w} S').toPresheafFiber (S'.obj (op j₁))
            (fiberMk.{max u v w} (𝟙 (S'.obj (op j₁)))) Fobj t₁ := hrewrite
      _ = s := hs₁
  have hŝ' :
      ((refinementFiber (tail_inclusion j₁) S' (Iso.refl _)).presheafFiber).app Fobj ŝ' = s' := by
    -- The same normalization identifies the second tail generator with `s'`.
    have hrewrite :
        (fiber.{max u v w} S').toPresheafFiber (S'.obj (op j₁))
          ((refinementFiber (tail_inclusion j₁) S' (Iso.refl _)).app
            (S'.obj (op j₁)) xTail) Fobj t₁' =
        (fiber.{max u v w} S').toPresheafFiber (S'.obj (op j₁))
          (fiberMk.{max u v w} (𝟙 (S'.obj (op j₁)))) Fobj t₁' := by
      have hrewrite₀ :
          (fiber.{max u v w} S').toPresheafFiber (S'.obj (op j₁))
            ((refinementFiber (tail_inclusion j₁) S' (Iso.refl _)).app
              (S'.obj (op j₁)) xTail) Fobj t₁' =
          (fiber.{max u v w} S').toPresheafFiber (S'.obj (op j₁))
            (fiberMk.{max u v w}
              ((Iso.refl ((tail_inclusion j₁).toOrderHom.toFunctor.op ⋙ S')).inv.app
                (op jTail) ≫ 𝟙 (S'.obj (op j₁)))) Fobj t₁' := by
        simpa only [jTail, xTail] using
          congrArg
            (fun x ↦
              (fiber.{max u v w} S').toPresheafFiber (S'.obj (op j₁)) x Fobj t₁')
            (refinementFiber_app_fiberMk (j := tail_inclusion j₁) (T := S') (e := Iso.refl _)
              (U := op jTail) (W := S'.obj (op j₁)) (f := 𝟙 (S'.obj (op j₁))))
      have hrewrite₁ :
          (fiber.{max u v w} S').toPresheafFiber (S'.obj (op j₁))
              (fiberMk.{max u v w}
                ((Iso.refl ((tail_inclusion j₁).toOrderHom.toFunctor.op ⋙ S')).inv.app
                  (op jTail) ≫ 𝟙 (S'.obj (op j₁)))) Fobj t₁' =
            (fiber.{max u v w} S').toPresheafFiber (S'.obj (op j₁))
              (fiberMk.{max u v w} (𝟙 (S'.obj (op j₁)))) Fobj t₁' := by
        have hunit :
            (Iso.refl ((tail_inclusion j₁).toOrderHom.toFunctor.op ⋙ S')).inv.app (op jTail) ≫
              𝟙 (S'.obj (op j₁)) =
            𝟙 (S'.obj (op j₁)) := by
          simp [jTail]
        exact congrArg
          (fun g ↦
            (fiber.{max u v w} S').toPresheafFiber (S'.obj (op j₁))
              (fiberMk.{max u v w} g) Fobj t₁')
          hunit
      exact hrewrite₀.trans hrewrite₁
    calc
      ((refinementFiber (tail_inclusion j₁) S' (Iso.refl _)).presheafFiber).app Fobj ŝ' =
          (fiber.{max u v w} S').toPresheafFiber (S'.obj (op j₁))
            ((refinementFiber (tail_inclusion j₁) S' (Iso.refl _)).app
              (S'.obj (op j₁)) xTail) Fobj t₁' := by
              simpa [ŝ', xTail] using
                congrFun
                  (NatTrans.toPresheafFiber_presheafFiber_app
                    (η := refinementFiber (tail_inclusion j₁) S' (Iso.refl _))
                    (F := Fobj) (X := S'.obj (op j₁)) xTail)
                  t₁'
      _ = (fiber.{max u v w} S').toPresheafFiber (S'.obj (op j₁))
            (fiberMk.{max u v w} (𝟙 (S'.obj (op j₁)))) Fobj t₁' := hrewrite
      _ = s' := hs₁'
  have hne : ŝ ≠ ŝ' := by
    -- Distinct images in the original raw fiber force the two canonical tail germs to differ.
    intro hEq
    apply hss'
    have hImage :
        ((refinementFiber (tail_inclusion j₁) S' (Iso.refl _)).presheafFiber).app Fobj ŝ =
          ((refinementFiber (tail_inclusion j₁) S' (Iso.refl _)).presheafFiber).app Fobj ŝ' := by
      simp [hEq]
    exact hŝ.symm.trans (hImage.trans hŝ')
  exact ⟨hŝ, hŝ', hne⟩

/-- Helper for Lemma 7.39.1: the tail index above `j₁` remains directed. -/
theorem tail_index_isDirected
    {ι : Type w} [Preorder ι] [IsDirected ι (· ≤ ·)] (j₁ : ι) :
    IsDirected (Set.Ici j₁) (· ≤ ·) := by
  refine ⟨?_⟩
  intro a b
  -- Choose a common upper bound in the ambient directed preorder and keep it in the tail.
  obtain ⟨k, hak, hbk⟩ := directed_of (· ≤ ·) a.1 b.1
  exact ⟨⟨k, a.2.trans hak⟩, by simpa using hak, by simpa using hbk⟩

/-- Helper for Lemma 7.39.1: on a fixed branch, the pullback second projections are natural with
respect to the tail transition maps. -/
theorem branch_system_snd_naturality
    {ι : Type w} [Preorder ι] [HasPullbacks C] (S : ιᵒᵖ ⥤ C) (j₁ : ι)
    {W : C} (f₁ : S.obj (op j₁) ⟶ W) (𝒰 : SemiRepresentableFamily.Over W) (k : 𝒰.index)
    {X Y : (Set.Ici j₁)ᵒᵖ} (g : X ⟶ Y) :
    branch_system_map S j₁ f₁ 𝒰 k g ≫
        (show branch_system_obj S j₁ f₁ 𝒰 k Y ⟶ (tail_system S j₁).obj Y from
          pullback.snd (𝒰.obj k).hom (S.map (homOfLE (unop Y).2).op ≫ f₁)) =
      (show branch_system_obj S j₁ f₁ 𝒰 k X ⟶ (tail_system S j₁).obj X from
        pullback.snd (𝒰.obj k).hom (S.map (homOfLE (unop X).2).op ≫ f₁)) ≫
        (tail_system S j₁).map g := by
  -- The tail-system map is exactly the ambient transition map of `S` along the tail preorder.
  simpa [tail_system, Functor.comp_map] using
    branch_system_map_snd_assoc (S := S) (j₁ := j₁) (f₁ := f₁) (𝒰 := 𝒰) (k := k) (g := g)

/-- Helper for Lemma 7.39.1: on a fixed branch, the pullback second projections define a natural
transformation from the branch system to the ambient tail system. -/
noncomputable def branch_system_snd_hom
    {ι : Type w} [Preorder ι] [HasPullbacks C] (S : ιᵒᵖ ⥤ C) (j₁ : ι)
    {W : C} (f₁ : S.obj (op j₁) ⟶ W) (𝒰 : SemiRepresentableFamily.Over W) (k : 𝒰.index) :
    branch_system S j₁ f₁ 𝒰 k ⟶ tail_system S j₁ :=
  { app := fun j ↦ pullback.snd (𝒰.obj k).hom (S.map (homOfLE (unop j).2).op ≫ f₁)
    naturality := fun X Y g ↦
      branch_system_snd_naturality (S := S) (j₁ := j₁) (f₁ := f₁) (𝒰 := 𝒰) (k := k) g }

/-- Helper for Lemma 7.39.1: the stagewise restriction from the tail system to a fixed pullback
branch gives a natural transformation on the corresponding section diagrams. -/
noncomputable def tail_branch_diagram_hom
    {ι : Type w} [Preorder ι] [HasPullbacks C] (S : ιᵒᵖ ⥤ C) (j₁ : ι)
    {W : C} (f₁ : S.obj (op j₁) ⟶ W) (𝒰 : SemiRepresentableFamily.Over W)
    (Fobj : Cᵒᵖ ⥤ Type (max u v w)) (k : 𝒰.index) :
    (tail_system S j₁).op ⋙ Fobj ⟶ (branch_system S j₁ f₁ 𝒰 k).op ⋙ Fobj :=
  -- Route correction: define the branch restriction first on the inverse systems themselves and
  -- then pass to section diagrams by `NatTrans.op` and whiskering with `Fobj`.
  Functor.whiskerRight
    (NatTrans.op (branch_system_snd_hom (S := S) (j₁ := j₁) (f₁ := f₁) (𝒰 := 𝒰) k))
    Fobj

/-- Helper for Lemma 7.39.1: each cover branch induces the canonical map from the tail raw
presheaf fiber to the raw presheaf fiber of that branch system. -/
noncomputable def tail_branch_presheafFiber_map
    {ι : Type w} [Preorder ι] [IsDirected ι (· ≤ ·)] [HasPullbacks C] (S : ιᵒᵖ ⥤ C) (j₁ : ι)
    {W : C} (f₁ : S.obj (op j₁) ⟶ W) (𝒰 : SemiRepresentableFamily.Over W)
    (Fobj : Cᵒᵖ ⥤ Type (max u v w)) (k : 𝒰.index) :
    (fiber.{max u v w} (tail_system S j₁)).presheafFiber.obj Fobj ⟶
      (fiber.{max u v w} (branch_system S j₁ f₁ 𝒰 k)).presheafFiber.obj Fobj :=
  let _ : Nonempty (Set.Ici j₁) := ⟨⟨j₁, le_rfl⟩⟩
  let _ : IsDirected (Set.Ici j₁) (· ≤ ·) := tail_index_isDirected (j₁ := j₁)
  (inverse_system_presheafFiber_colimitIso (tail_system S j₁) Fobj).inv ≫
    colim.map (tail_branch_diagram_hom (S := S) (j₁ := j₁) (f₁ := f₁) (𝒰 := 𝒰)
      (Fobj := Fobj) k) ≫
    (inverse_system_presheafFiber_colimitIso (branch_system S j₁ f₁ 𝒰 k) Fobj).hom

/-- Helper for Lemma 7.39.1: at the base tail stage `j₁`, the branch map on raw presheaf fibers
normalizes to the canonical branch germ built from the pullback second projection. -/
theorem tail_branch_presheafFiber_map_base_generator_eq
    [HasPullbacks C] {ι : Type w} [Preorder ι] [IsDirected ι (· ≤ ·)] (S : ιᵒᵖ ⥤ C) (j₁ : ι)
    {W : C} (f₁ : S.obj (op j₁) ⟶ W) (𝒰 : SemiRepresentableFamily.Over W)
    (Fobj : Cᵒᵖ ⥤ Type (max u v w)) (k : 𝒰.index)
    (t : Fobj.obj (op (S.obj (op j₁)))) :
    let jTail : Set.Ici j₁ := ⟨j₁, le_rfl⟩
    let xTail : (fiber.{max u v w} (tail_system S j₁)).obj (S.obj (op j₁)) :=
      fiberMk.{max u v w} (U := op jTail) (X := S.obj (op j₁)) (𝟙 (S.obj (op j₁)))
    tail_branch_presheafFiber_map (S := S) (j₁ := j₁) (f₁ := f₁) (𝒰 := 𝒰) Fobj k
        ((fiber.{max u v w} (tail_system S j₁)).toPresheafFiber (S.obj (op j₁)) xTail Fobj t) =
      (fiber.{max u v w} (branch_system S j₁ f₁ 𝒰 k)).toPresheafFiber (S.obj (op j₁))
        (fiberMk.{max u v w} (U := op jTail)
          ((branch_system_snd_hom (S := S) (j₁ := j₁) (f₁ := f₁) (𝒰 := 𝒰) k).app
            (op jTail))) Fobj t := by
  let jTail : Set.Ici j₁ := ⟨j₁, le_rfl⟩
  let xTail : (fiber.{max u v w} (tail_system S j₁)).obj (S.obj (op j₁)) :=
    fiberMk.{max u v w} (U := op jTail) (X := S.obj (op j₁)) (𝟙 (S.obj (op j₁)))
  let _ : Nonempty (Set.Ici j₁) := ⟨jTail⟩
  let _ : IsDirected (Set.Ici j₁) (· ≤ ·) := tail_index_isDirected (j₁ := j₁)
  let tailIso := inverse_system_presheafFiber_colimitIso (tail_system S j₁) Fobj
  let branchIso := inverse_system_presheafFiber_colimitIso (branch_system S j₁ f₁ 𝒰 k) Fobj
  let tBranch : Fobj.obj (op ((branch_system S j₁ f₁ 𝒰 k).obj (op jTail))) :=
    Fobj.map
      (((branch_system_snd_hom (S := S) (j₁ := j₁) (f₁ := f₁) (𝒰 := 𝒰) k).app
        (op jTail))).op t
  let xBranch : (fiber.{max u v w} (branch_system S j₁ f₁ 𝒰 k)).obj
      ((branch_system S j₁ f₁ 𝒰 k).obj (op jTail)) :=
    fiberMk.{max u v w} (U := op jTail) (X := (branch_system S j₁ f₁ 𝒰 k).obj (op jTail))
      (𝟙 ((branch_system S j₁ f₁ 𝒰 k).obj (op jTail)))
  have htailHom :
      tailIso.hom (colimit.ι ((tail_system S j₁).op ⋙ Fobj) (op (op jTail)) t) =
        (fiber.{max u v w} (tail_system S j₁)).toPresheafFiber (S.obj (op j₁)) xTail Fobj t := by
    -- The tail colimit generator at `jTail` is the canonical raw fiber generator.
    simpa [tailIso, inverse_system_presheafFiber_colimitIso,
      inverse_system_presheafFiberCocone, jTail, xTail] using
      congrFun
        (colimit.comp_coconePointUniqueUpToIso_hom
          (hc := inverse_system_presheafFiber_isColimit (S := tail_system S j₁) Fobj)
          (op (op jTail)))
        t
  have htailInv :
      tailIso.inv
          ((fiber.{max u v w} (tail_system S j₁)).toPresheafFiber (S.obj (op j₁))
            xTail Fobj t) =
        colimit.ι ((tail_system S j₁).op ⋙ Fobj) (op (op jTail)) t := by
    -- Apply the inverse of the colimit comparison after rewriting by `htailHom`.
    rw [← htailHom]
    simp
  have hmap :
      colim.map (tail_branch_diagram_hom
          (S := S) (j₁ := j₁) (f₁ := f₁) (𝒰 := 𝒰) (Fobj := Fobj) k)
          (colimit.ι ((tail_system S j₁).op ⋙ Fobj) (op (op jTail)) t) =
        colimit.ι ((branch_system S j₁ f₁ 𝒰 k).op ⋙ Fobj) (op (op jTail))
          (((tail_branch_diagram_hom
            (S := S) (j₁ := j₁) (f₁ := f₁) (𝒰 := 𝒰) (Fobj := Fobj) k).app
              (op (op jTail))) t) := by
    -- Mapping a colimit generator along the branch diagram hom stays at the same stage.
    simpa using
      congrFun
        (ι_colimMap
          (tail_branch_diagram_hom
            (S := S) (j₁ := j₁) (f₁ := f₁) (𝒰 := 𝒰) (Fobj := Fobj) k)
          (op (op jTail)))
        t
  have happ :
      ((tail_branch_diagram_hom
          (S := S) (j₁ := j₁) (f₁ := f₁) (𝒰 := 𝒰) (Fobj := Fobj) k).app
          (op (op jTail))) t =
        tBranch := by
    -- At the base tail stage the branch restriction is exactly the pullback second projection.
    simp [tBranch, tail_branch_diagram_hom]
  have hbranchHom :
      branchIso.hom
          (colimit.ι ((branch_system S j₁ f₁ 𝒰 k).op ⋙ Fobj) (op (op jTail)) tBranch) =
        (fiber.{max u v w} (branch_system S j₁ f₁ 𝒰 k)).toPresheafFiber
          ((branch_system S j₁ f₁ 𝒰 k).obj (op jTail)) xBranch Fobj tBranch := by
    -- The branch colimit generator at `jTail` is the identity germ on the pullback object.
    simpa [branchIso, inverse_system_presheafFiber_colimitIso,
      inverse_system_presheafFiberCocone, jTail, xBranch, tBranch] using
      congrFun
        (colimit.comp_coconePointUniqueUpToIso_hom
          (hc := inverse_system_presheafFiber_isColimit
            (S := branch_system S j₁ f₁ 𝒰 k) Fobj)
          (op (op jTail)))
        tBranch
  have hbranchRewrite :
      (fiber.{max u v w} (branch_system S j₁ f₁ 𝒰 k)).toPresheafFiber
          ((branch_system S j₁ f₁ 𝒰 k).obj (op jTail)) xBranch Fobj tBranch =
        (fiber.{max u v w} (branch_system S j₁ f₁ 𝒰 k)).toPresheafFiber (S.obj (op j₁))
          (fiberMk.{max u v w} (U := op jTail)
            ((branch_system_snd_hom (S := S) (j₁ := j₁) (f₁ := f₁) (𝒰 := 𝒰) k).app
              (op jTail))) Fobj t := by
    -- Move the identity germ on the pullback object along `pullback.snd`.
    have hrewrite₀ :
        (fiber.{max u v w} (branch_system S j₁ f₁ 𝒰 k)).toPresheafFiber
            ((branch_system S j₁ f₁ 𝒰 k).obj (op jTail)) xBranch Fobj tBranch =
          (fiber.{max u v w} (branch_system S j₁ f₁ 𝒰 k)).toPresheafFiber
            (S.obj (op ((tail_inclusion j₁) jTail)))
            ((fiber.{max u v w} (branch_system S j₁ f₁ 𝒰 k)).map
              ((branch_system_snd_hom (S := S) (j₁ := j₁) (f₁ := f₁) (𝒰 := 𝒰) k).app
                (op jTail))
              xBranch) Fobj t := by
      simpa [tBranch] using
        congrFun
          ((fiber.{max u v w} (branch_system S j₁ f₁ 𝒰 k)).toPresheafFiber_w
            (F := Fobj)
            ((branch_system_snd_hom (S := S) (j₁ := j₁) (f₁ := f₁) (𝒰 := 𝒰) k).app
              (op jTail))
            xBranch)
          t
    have hrewrite₁ :
        ((fiber.{max u v w} (branch_system S j₁ f₁ 𝒰 k)).map
          ((branch_system_snd_hom (S := S) (j₁ := j₁) (f₁ := f₁) (𝒰 := 𝒰) k).app
            (op jTail))
          xBranch) =
          fiberMk.{max u v w} (U := op jTail)
            ((branch_system_snd_hom (S := S) (j₁ := j₁) (f₁ := f₁) (𝒰 := 𝒰) k).app
              (op jTail)) := by
      simpa [xBranch]
    rw [hrewrite₁] at hrewrite₀
    simpa [jTail] using hrewrite₀
  -- Evaluate the composite definition of `tail_branch_presheafFiber_map` on the base generator
  -- and then normalize the resulting branch germ.
  calc
    tail_branch_presheafFiber_map (S := S) (j₁ := j₁) (f₁ := f₁) (𝒰 := 𝒰) Fobj k
        ((fiber.{max u v w} (tail_system S j₁)).toPresheafFiber (S.obj (op j₁))
          xTail Fobj t) =
      branchIso.hom
        (colim.map (tail_branch_diagram_hom
          (S := S) (j₁ := j₁) (f₁ := f₁) (𝒰 := 𝒰) (Fobj := Fobj) k)
          (tailIso.inv
            ((fiber.{max u v w} (tail_system S j₁)).toPresheafFiber (S.obj (op j₁))
              xTail Fobj t))) := by
          rfl
    _ =
      branchIso.hom
        (colim.map (tail_branch_diagram_hom
          (S := S) (j₁ := j₁) (f₁ := f₁) (𝒰 := 𝒰) (Fobj := Fobj) k)
          (colimit.ι ((tail_system S j₁).op ⋙ Fobj) (op (op jTail)) t)) := by
            rw [htailInv]
    _ =
      branchIso.hom
        (colimit.ι ((branch_system S j₁ f₁ 𝒰 k).op ⋙ Fobj) (op (op jTail))
          (((tail_branch_diagram_hom
            (S := S) (j₁ := j₁) (f₁ := f₁) (𝒰 := 𝒰) (Fobj := Fobj) k).app
              (op (op jTail))) t)) := by
            rw [hmap]
    _ =
      branchIso.hom
        (colimit.ι ((branch_system S j₁ f₁ 𝒰 k).op ⋙ Fobj) (op (op jTail))
          tBranch) := by
            rw [happ]
    _ =
      (fiber.{max u v w} (branch_system S j₁ f₁ 𝒰 k)).toPresheafFiber
        ((branch_system S j₁ f₁ 𝒰 k).obj (op jTail)) xBranch Fobj tBranch := hbranchHom
    _ =
      (fiber.{max u v w} (branch_system S j₁ f₁ 𝒰 k)).toPresheafFiber (S.obj (op j₁))
        (fiberMk.{max u v w} (U := op jTail)
          ((branch_system_snd_hom (S := S) (j₁ := j₁) (f₁ := f₁) (𝒰 := 𝒰) k).app
            (op jTail))) Fobj t :=
          hbranchRewrite

end

end CategoryTheory
