module

public import Mathlib.CategoryTheory.EssentiallySmall
public import Mathlib.CategoryTheory.Sites.Sheafification
public import Mathlib.CategoryTheory.Sites.Sheaf
public import stacks_project.Chap04.Lemma_4_19_2
public import stacks_project.Chap07.«7_32_1_1»
public import stacks_project.Chap07.Definition_7_8_2
public import stacks_project.Chap07.Lemma_7_39_1.Index

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory CategoryTheory.Limits Opposite
open GrothendieckTopology.Point
open CategoryTheory.SemiRepresentableFamily.Over

universe u v w

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]

attribute [local instance] initiallySmall_of_essentiallySmall

/- Domain-style sampling for Lemma 7.39.1:
- primary domain: fibers of cofiltered inverse systems and the induced raw stalk functors on
  sheaves, together with explicit finite covering families on a fixed target;
- sampled owner API:
  `GrothendieckTopology.Point.ofIsCofiltered.fiber`,
  `GrothendieckTopology.Point.ofIsCofiltered.fiberMk`,
  `GrothendieckTopology.Point.ofIsCofiltered.refinementFiber`,
  `Functor.presheafFiber`,
  `GrothendieckTopology.Point.presheafFiber`,
  `GrothendieckTopology.Point.Hom.presheafFiber`,
  `SemiRepresentableFamily.Over`,
  `SemiRepresentableFamily.Over.toSieve`;
- source/core/bridge triage:
  `source-facing`: a directed inverse system `S : ιᵒᵖ ⥤ C`, its associated set-valued functor
  `u`, a fixed-target finite covering family `𝒰 : SemiRepresentableFamily.Over W`, and a
  refinement datum `S ≅ (j.toOrderHom.toFunctor).op ⋙ T`;
  `core/canonical`: `GrothendieckTopology.Point.ofIsCofiltered.fiber`, with raw stalk layer
  `sheafToPresheaf J (Type _) ⋙ (ofIsCofiltered.fiber S).presheafFiber`;
  `bridge/view`: `SemiRepresentableFamily.Over.toSieve` for finite covering families, together
  with the refinement-induced natural transformation `ofIsCofiltered.refinementFiber` between
  these canonical inverse-system fibers and its objectwise/raw-stalk projections.

Primitive data are only the inverse systems and the refinement datum. The covering-surjectivity
data needed to upgrade an inverse system to a site point are absent, so the source-facing theorem
must stay at the inverse-system fiber layer rather than be promoted to `Point.ofIsCofiltered`.
The sheaf-fiber layer is derived API of `Functor.presheafFiber`, and Chapter 7 already packages
explicit fixed-target families by `SemiRepresentableFamily.Over`, so this file should reuse those
owners instead of parallel local inverse-system-fiber or covering-family encodings.
-/

section

variable {J : GrothendieckTopology C}

open GrothendieckTopology.Point.ofIsCofiltered
open CategoryTheory.SemiRepresentableFamily.Over

variable (J)

/-- Helper for Lemma 7.39.1: on the canonical tail-stage generator, the branch-to-glued raw-fiber
comparison agrees with first returning to the original system and then refining to the glued
system. -/
private theorem glued_right_branch_presheafFiber_iso_hom_branch_base_germ_eq
    {ι : Type w} [Preorder ι] [IsDirected ι (· ≤ ·)] [HasPullbacks C] (S : ιᵒᵖ ⥤ C)
    (j₁ : ι) {W : C} (f₁ : S.obj (op j₁) ⟶ W) (𝒰 : SemiRepresentableFamily.Over W)
    (k : 𝒰.index) (Fobj : Cᵒᵖ ⥤ Type (max u v w))
    (t : Fobj.obj (op (S.obj (op j₁)))) :
    let jTail : Set.Ici j₁ := ⟨j₁, le_rfl⟩
    (glued_right_branch_presheafFiber_iso
        (S := S) (j₁ := j₁) (f₁ := f₁) (𝒰 := 𝒰) k Fobj).hom
        ((fiber.{max u v w} (branch_system S j₁ f₁ 𝒰 k)).toPresheafFiber (S.obj (op j₁))
          (fiberMk.{max u v w} (U := op jTail)
            ((branch_system_snd_hom (S := S) (j₁ := j₁) (f₁ := f₁) (𝒰 := 𝒰) k).app
              (op jTail))) Fobj t) =
      (fiber.{max u v w} (glued_refinement_system S j₁ f₁ 𝒰 k)).toPresheafFiber (S.obj (op j₁))
        (fiberMk.{max u v w}
          (U := op (⟨Sum.inr ⟨j₁, le_rfl⟩⟩ : glued_refinement_index j₁))
          (pullback.snd (𝒰.obj k).hom
            (S.map (homOfLE (show j₁ ≤ j₁ from le_rfl)).op ≫ f₁))) Fobj t := by
  let jTail : Set.Ici j₁ := ⟨j₁, le_rfl⟩
  -- Route correction: isolate the remaining blocker to the finality/colimit evaluation on the
  -- single canonical branch generator at `jTail`.
  let i : (Set.Ici j₁)ᵒᵖ ⥤ (glued_refinement_index j₁)ᵒᵖ :=
    ((glued_refinement_tail_inclusion j₁).toOrderHom.toFunctor).op
  let B := branch_system S j₁ f₁ 𝒰 k
  let T := glued_refinement_system S j₁ f₁ 𝒰 k
  let hSections : B.op ⋙ Fobj ≅ i.op ⋙ T.op ⋙ Fobj :=
    (Functor.isoWhiskerRight
        (NatIso.op (glued_refinement_right_restrict_iso
          (S := S) (j₁ := j₁) (f₁ := f₁) (𝒰 := 𝒰) (k := k)).symm)
        Fobj) ≪≫
      (Functor.isoWhiskerRight (Functor.opComp i T) Fobj) ≪≫
      (Functor.associator i.op T.op Fobj)
  let _ : Functor.Final ((glued_refinement_tail_inclusion j₁).toOrderHom.toFunctor) :=
    glued_refinement_tail_inclusion_final (j₁ := j₁)
  let _ : Functor.Final i.op := by infer_instance
  let _ : Nonempty (Set.Ici j₁) := ⟨jTail⟩
  let _ : IsDirected (Set.Ici j₁) (· ≤ ·) := tail_index_isDirected (j₁ := j₁)
  let _ : Nonempty (glued_refinement_index j₁) := ⟨⟨Sum.inl j₁⟩⟩
  let branchIso := inverse_system_presheafFiber_colimitIso B Fobj
  let gluedIso := inverse_system_presheafFiber_colimitIso T Fobj
  let rightIndex : glued_refinement_index j₁ := ⟨Sum.inr jTail⟩
  let branchGerm : (fiber.{max u v w} B).presheafFiber.obj Fobj :=
    (fiber.{max u v w} B).toPresheafFiber (S.obj (op j₁))
      (fiberMk.{max u v w} (U := op jTail)
        ((branch_system_snd_hom (S := S) (j₁ := j₁) (f₁ := f₁) (𝒰 := 𝒰) k).app
          (op jTail))) Fobj t
  let tBranch : Fobj.obj (op (B.obj (op jTail))) :=
    Fobj.map
      (((branch_system_snd_hom (S := S) (j₁ := j₁) (f₁ := f₁) (𝒰 := 𝒰) k).app
        (op jTail))).op t
  let xBranch : (fiber.{max u v w} B).obj (B.obj (op jTail)) :=
    fiberMk.{max u v w} (U := op jTail) (X := B.obj (op jTail))
      (𝟙 (B.obj (op jTail)))
  let rightBaseHom : T.obj (op rightIndex) ⟶ S.obj (op j₁) :=
    pullback.snd (𝒰.obj k).hom
      (S.map (homOfLE (show j₁ ≤ j₁ from le_rfl)).op ≫ f₁)
  let tRight : Fobj.obj (op (T.obj (op rightIndex))) :=
    Fobj.map rightBaseHom.op t
  let xRight : (fiber.{max u v w} T).obj (T.obj (op rightIndex)) :=
    fiberMk.{max u v w} (U := op rightIndex) (X := T.obj (op rightIndex))
      (𝟙 (T.obj (op rightIndex)))
  let gluedGerm : (fiber.{max u v w} T).presheafFiber.obj Fobj :=
    (fiber.{max u v w} T).toPresheafFiber (S.obj (op j₁))
      (fiberMk.{max u v w} (U := op rightIndex) rightBaseHom) Fobj t
  have hbranchHom :
      branchIso.hom
          (colimit.ι (B.op ⋙ Fobj) (op (op jTail)) tBranch) =
        (fiber.{max u v w} B).toPresheafFiber
          (B.obj (op jTail)) xBranch Fobj tBranch := by
    -- The branch colimit generator at `jTail` is the identity raw germ on that stage.
    simpa [branchIso, inverse_system_presheafFiber_colimitIso,
      inverse_system_presheafFiberCocone, B, jTail, xBranch, tBranch] using
      congrFun
        (colimit.comp_coconePointUniqueUpToIso_hom
          (hc := inverse_system_presheafFiber_isColimit (S := B) Fobj)
          (op (op jTail)))
        tBranch
  have hbranchRewrite :
      (fiber.{max u v w} B).toPresheafFiber
          (B.obj (op jTail)) xBranch Fobj tBranch =
        branchGerm := by
    -- Move the branch identity germ along the pullback second projection to the base stage.
    have hrewrite₀ :
        (fiber.{max u v w} B).toPresheafFiber
            (B.obj (op jTail)) xBranch Fobj tBranch =
          (fiber.{max u v w} B).toPresheafFiber
            (S.obj (op ((tail_inclusion j₁) jTail)))
            ((fiber.{max u v w} B).map
              ((branch_system_snd_hom (S := S) (j₁ := j₁) (f₁ := f₁) (𝒰 := 𝒰) k).app
                (op jTail))
              xBranch) Fobj t := by
      simpa [B, tBranch] using
        congrFun
          ((fiber.{max u v w} B).toPresheafFiber_w
            (F := Fobj)
            ((branch_system_snd_hom (S := S) (j₁ := j₁) (f₁ := f₁) (𝒰 := 𝒰) k).app
              (op jTail))
            xBranch)
          t
    have hrewrite₁ :
        ((fiber.{max u v w} B).map
          ((branch_system_snd_hom (S := S) (j₁ := j₁) (f₁ := f₁) (𝒰 := 𝒰) k).app
            (op jTail))
          xBranch) =
          fiberMk.{max u v w} (U := op jTail)
            ((branch_system_snd_hom (S := S) (j₁ := j₁) (f₁ := f₁) (𝒰 := 𝒰) k).app
              (op jTail)) := by
      simpa [xBranch]
    rw [hrewrite₁] at hrewrite₀
    simpa [branchGerm, jTail] using hrewrite₀
  have hbranchInv :
      branchIso.inv branchGerm =
        colimit.ι (B.op ⋙ Fobj) (op (op jTail)) tBranch := by
    -- Invert the branch colimit comparison after identifying its generator with `branchGerm`.
    rw [← hbranchHom.trans hbranchRewrite]
    simp
  have hsectionValue :
      (hSections.hom.app (op (op jTail))) tBranch = tRight := by
    -- The natural isomorphism from the branch diagram to the restricted glued diagram is
    -- componentwise the identity on the right summand.
    simp [hSections, tBranch, tRight, rightBaseHom, rightIndex, i, B, T,
      glued_refinement_right_restrict_iso, branch_system_snd_hom, glued_refinement_tail_inclusion,
      glued_refinement_system, glued_refinement_system_obj, branch_system, branch_system_obj]
    rfl
  have hsections :
      (HasColimit.isoOfNatIso hSections).hom
          (colimit.ι (B.op ⋙ Fobj) (op (op jTail)) tBranch) =
        colimit.ι (i.op ⋙ T.op ⋙ Fobj) (op (op jTail)) tRight := by
    -- Transport the same generator through the natural isomorphism identifying the two section
    -- diagrams.
    calc
      (HasColimit.isoOfNatIso hSections).hom
          (colimit.ι (B.op ⋙ Fobj) (op (op jTail)) tBranch) =
        colimit.ι (i.op ⋙ T.op ⋙ Fobj) (op (op jTail))
          ((hSections.hom.app (op (op jTail))) tBranch) := by
          simpa [CategoryTheory.types_comp_apply] using
            congrFun (HasColimit.isoOfNatIso_ι_hom hSections (op (op jTail))) tBranch
      _ = colimit.ι (i.op ⋙ T.op ⋙ Fobj) (op (op jTail)) tRight := by
          rw [hsectionValue]
  have hfinal :
      (Functor.Final.colimitIso i.op (T.op ⋙ Fobj)).hom
          (colimit.ι (i.op ⋙ T.op ⋙ Fobj) (op (op jTail)) tRight) =
        colimit.ι (T.op ⋙ Fobj) (op (op rightIndex)) tRight := by
    -- Finality of the right summand sends the restricted generator to the corresponding glued
    -- generator.
    simpa [i, rightIndex, CategoryTheory.types_comp_apply] using
      congrFun (Functor.Final.ι_colimitIso_hom i.op (T.op ⋙ Fobj) (op (op jTail))) tRight
  have hgluedHom :
      gluedIso.hom (colimit.ι (T.op ⋙ Fobj) (op (op rightIndex)) tRight) =
        (fiber.{max u v w} T).toPresheafFiber
          (T.obj (op rightIndex)) xRight Fobj tRight := by
    -- The glued colimit generator at the right base is the identity raw germ on that stage.
    simpa [gluedIso, inverse_system_presheafFiber_colimitIso,
      inverse_system_presheafFiberCocone, T, rightIndex, xRight, tRight] using
      congrFun
        (colimit.comp_coconePointUniqueUpToIso_hom
          (hc := inverse_system_presheafFiber_isColimit (S := T) Fobj)
          (op (op rightIndex)))
        tRight
  have hgluedRewrite :
      (fiber.{max u v w} T).toPresheafFiber
          (T.obj (op rightIndex)) xRight Fobj tRight =
        gluedGerm := by
    -- Move the glued identity germ along the right-base projection to the original base stage.
    have hrewrite₀ :
        (fiber.{max u v w} T).toPresheafFiber
            (T.obj (op rightIndex)) xRight Fobj tRight =
          (fiber.{max u v w} T).toPresheafFiber
            (S.obj (op j₁))
            ((fiber.{max u v w} T).map rightBaseHom xRight) Fobj t := by
      simpa [tRight] using
        congrFun
          ((fiber.{max u v w} T).toPresheafFiber_w
            (F := Fobj) rightBaseHom xRight)
          t
    have hrewrite₁ :
        ((fiber.{max u v w} T).map rightBaseHom xRight) =
          fiberMk.{max u v w} (U := op rightIndex) rightBaseHom := by
      simpa [xRight]
    rw [hrewrite₁] at hrewrite₀
    simpa [gluedGerm] using hrewrite₀
  have hmain :
      (glued_right_branch_presheafFiber_iso
          (S := S) (j₁ := j₁) (f₁ := f₁) (𝒰 := 𝒰) k Fobj).hom branchGerm =
        gluedGerm := by
    -- Assemble the four computed legs of the composite isomorphism defining the comparison.
    calc
      (glued_right_branch_presheafFiber_iso
          (S := S) (j₁ := j₁) (f₁ := f₁) (𝒰 := 𝒰) k Fobj).hom branchGerm =
        gluedIso.hom
          ((Functor.Final.colimitIso i.op (T.op ⋙ Fobj)).hom
            ((HasColimit.isoOfNatIso hSections).hom (branchIso.inv branchGerm))) := by
          rfl
      _ =
        gluedIso.hom
          ((Functor.Final.colimitIso i.op (T.op ⋙ Fobj)).hom
            ((HasColimit.isoOfNatIso hSections).hom
              (colimit.ι (B.op ⋙ Fobj) (op (op jTail)) tBranch))) := by
          rw [hbranchInv]
      _ =
        gluedIso.hom
          ((Functor.Final.colimitIso i.op (T.op ⋙ Fobj)).hom
            (colimit.ι (i.op ⋙ T.op ⋙ Fobj) (op (op jTail)) tRight)) := by
          rw [hsections]
      _ =
        gluedIso.hom (colimit.ι (T.op ⋙ Fobj) (op (op rightIndex)) tRight) := by
          rw [hfinal]
      _ = gluedGerm := hgluedHom.trans hgluedRewrite
  simpa [branchGerm, gluedGerm, B, T, rightBaseHom, rightIndex, jTail] using hmain

/-- Helper for Lemma 7.39.1: the explicit glued right-base raw germ is already the refinement
image of the canonical tail-stage germ. -/
private theorem glued_right_base_presheafFiber_germ_eq_refinement_image
    {ι : Type w} [Preorder ι] [HasPullbacks C] (S : ιᵒᵖ ⥤ C)
    (j₁ : ι) {W : C} (f₁ : S.obj (op j₁) ⟶ W) (𝒰 : SemiRepresentableFamily.Over W)
    (k : 𝒰.index) (Fobj : Cᵒᵖ ⥤ Type (max u v w))
    (t : Fobj.obj (op (S.obj (op j₁)))) :
    let jTail : Set.Ici j₁ := ⟨j₁, le_rfl⟩
    let xTail : (fiber.{max u v w} (tail_system S j₁)).obj (S.obj (op j₁)) :=
      fiberMk.{max u v w} (U := op jTail) (X := S.obj (op j₁)) (𝟙 (S.obj (op j₁)))
    let ŝt : (fiber.{max u v w} (tail_system S j₁)).presheafFiber.obj Fobj :=
      (fiber.{max u v w} (tail_system S j₁)).toPresheafFiber (S.obj (op j₁)) xTail Fobj t
    (fiber.{max u v w} (glued_refinement_system S j₁ f₁ 𝒰 k)).toPresheafFiber (S.obj (op j₁))
        (fiberMk.{max u v w}
          (U := op (⟨Sum.inr ⟨j₁, le_rfl⟩⟩ : glued_refinement_index j₁))
          (pullback.snd (𝒰.obj k).hom
            (S.map (homOfLE (show j₁ ≤ j₁ from le_rfl)).op ≫ f₁))) Fobj t =
      ((refinementFiber (glued_refinement_inclusion j₁)
        (glued_refinement_system S j₁ f₁ 𝒰 k)
        (glued_refinement_iso S j₁ f₁ 𝒰 k)).presheafFiber).app Fobj
        (((refinementFiber (tail_inclusion j₁) S (Iso.refl _)).presheafFiber).app Fobj ŝt) := by
  let jTail : Set.Ici j₁ := ⟨j₁, le_rfl⟩
  let xTail : (fiber.{max u v w} (tail_system S j₁)).obj (S.obj (op j₁)) :=
    fiberMk.{max u v w} (U := op jTail) (X := S.obj (op j₁)) (𝟙 (S.obj (op j₁)))
  let ŝt : (fiber.{max u v w} (tail_system S j₁)).presheafFiber.obj Fobj :=
    (fiber.{max u v w} (tail_system S j₁)).toPresheafFiber (S.obj (op j₁)) xTail Fobj t
  let T := glued_refinement_system S j₁ f₁ 𝒰 k
  let ηTail := refinementFiber (tail_inclusion j₁) S (Iso.refl _)
  let ηG := refinementFiber (glued_refinement_inclusion j₁) T (glued_refinement_iso S j₁ f₁ 𝒰 k)
  let rightBaseToLeft :=
    glued_refinement_right_base_to_left_hom (j0 := j₁) (j₁ := j₁) (show j₁ ≤ j₁ from le_rfl)
  let rightBaseHom :
      T.obj (op (⟨Sum.inr ⟨j₁, le_rfl⟩⟩ : glued_refinement_index j₁)) ⟶ (𝒰.obj k).left :=
    pullback.fst (𝒰.obj k).hom
      (S.map (homOfLE (show j₁ ≤ j₁ from le_rfl)).op ≫ f₁)
  have htail :
      ηTail.presheafFiber.app Fobj ŝt =
        (fiber.{max u v w} S).toPresheafFiber (S.obj (op j₁))
          (fiberMk.{max u v w} (𝟙 (S.obj (op j₁)))) Fobj t := by
    -- First identify the tail refinement image of the canonical tail germ with the identity germ.
    have hrewrite :
        (fiber.{max u v w} S).toPresheafFiber (S.obj (op j₁))
          (ηTail.app (S.obj (op j₁)) xTail) Fobj t =
        (fiber.{max u v w} S).toPresheafFiber (S.obj (op j₁))
          (fiberMk.{max u v w} (𝟙 (S.obj (op j₁)))) Fobj t := by
      have hrewrite₀ :
          (fiber.{max u v w} S).toPresheafFiber (S.obj (op j₁))
            (ηTail.app (S.obj (op j₁)) xTail) Fobj t =
          (fiber.{max u v w} S).toPresheafFiber (S.obj (op j₁))
            (fiberMk.{max u v w}
              ((Iso.refl ((tail_inclusion j₁).toOrderHom.toFunctor.op ⋙ S)).inv.app
                (op jTail) ≫ 𝟙 (S.obj (op j₁)))) Fobj t := by
        simpa only [ηTail, jTail, xTail] using
          congrArg
            (fun x ↦
              (fiber.{max u v w} S).toPresheafFiber (S.obj (op j₁)) x Fobj t)
            (refinementFiber_app_fiberMk (j := tail_inclusion j₁) (T := S) (e := Iso.refl _)
              (U := op jTail) (W := S.obj (op j₁)) (f := 𝟙 (S.obj (op j₁))))
      have hrewrite₁ :
          (fiber.{max u v w} S).toPresheafFiber (S.obj (op j₁))
              (fiberMk.{max u v w}
                ((Iso.refl ((tail_inclusion j₁).toOrderHom.toFunctor.op ⋙ S)).inv.app
                  (op jTail) ≫ 𝟙 (S.obj (op j₁)))) Fobj t =
            (fiber.{max u v w} S).toPresheafFiber (S.obj (op j₁))
              (fiberMk.{max u v w} (𝟙 (S.obj (op j₁)))) Fobj t := by
        have hunit :
            (Iso.refl ((tail_inclusion j₁).toOrderHom.toFunctor.op ⋙ S)).inv.app (op jTail) ≫
              𝟙 (S.obj (op j₁)) =
            𝟙 (S.obj (op j₁)) := by
          simp [jTail]
        exact congrArg
          (fun g ↦
            (fiber.{max u v w} S).toPresheafFiber (S.obj (op j₁))
              (fiberMk.{max u v w} g) Fobj t)
          hunit
      exact hrewrite₀.trans hrewrite₁
    calc
      ηTail.presheafFiber.app Fobj ŝt =
          (fiber.{max u v w} S).toPresheafFiber (S.obj (op j₁))
            (ηTail.app (S.obj (op j₁)) xTail) Fobj t := by
              simpa [ηTail, ŝt, xTail] using
                congrFun
                  (NatTrans.toPresheafFiber_presheafFiber_app
                    (η := ηTail) (F := Fobj) (X := S.obj (op j₁)) xTail)
                  t
      _ = (fiber.{max u v w} S).toPresheafFiber (S.obj (op j₁))
            (fiberMk.{max u v w} (𝟙 (S.obj (op j₁)))) Fobj t := hrewrite
  have hrightBaseToLeft :
      T.map rightBaseToLeft =
        pullback.snd (𝒰.obj k).hom
          (S.map (homOfLE (show j₁ ≤ j₁ from le_rfl)).op ≫ f₁) := by
    -- The mixed right-to-left map at the base tail stage is exactly the pullback second projection.
    change pullback.snd (𝒰.obj k).hom
        (S.map (homOfLE (show j₁ ≤ j₁ from le_rfl)).op ≫ f₁) ≫
          S.map (show op j₁ ⟶ op j₁ from (homOfLE (show j₁ ≤ j₁ from le_rfl)).op) =
      pullback.snd (𝒰.obj k).hom
        (S.map (homOfLE (show j₁ ≤ j₁ from le_rfl)).op ≫ f₁)
    simpa using
      Category.comp_id
        (pullback.snd (𝒰.obj k).hom
          (S.map (homOfLE (show j₁ ≤ j₁ from le_rfl)).op ≫ f₁))
  have hleftGenerator :
      ηG.app (S.obj (op j₁))
          (show (fiber.{max u v w} S).obj (S.obj (op j₁)) from
            fiberMk.{max u v w} (𝟙 (S.obj (op j₁)))) =
        (show (fiber.{max u v w} T).obj (S.obj (op j₁)) from
          fiberMk.{max u v w}
            (U := op (⟨Sum.inl j₁⟩ : glued_refinement_index j₁))
            (𝟙 (S.obj (op j₁)))) := by
    -- On the left summand, the refinement map is exactly the identity stage inclusion.
    change (refinementFiber (glued_refinement_inclusion j₁) T
        (glued_refinement_iso S j₁ f₁ 𝒰 k)).app (S.obj (op j₁))
          (show (fiber.{max u v w} S).obj (S.obj (op j₁)) from
            fiberMk.{max u v w} (𝟙 (S.obj (op j₁)))) =
        (show (fiber.{max u v w} T).obj (S.obj (op j₁)) from
          fiberMk.{max u v w}
            (U := op (⟨Sum.inl j₁⟩ : glued_refinement_index j₁))
            (𝟙 (S.obj (op j₁))))
    have hraw :
        (refinementFiber (glued_refinement_inclusion j₁) T
            (glued_refinement_iso S j₁ f₁ 𝒰 k)).app (S.obj (op j₁))
            (show (fiber.{max u v w} S).obj (S.obj (op j₁)) from
              fiberMk.{max u v w} (𝟙 (S.obj (op j₁)))) =
          (show (fiber.{max u v w} T).obj (S.obj (op j₁)) from
            fiberMk.{max u v w}
              (U := op ((glued_refinement_inclusion j₁) j₁))
              ((glued_refinement_iso S j₁ f₁ 𝒰 k).inv.app (op j₁) ≫
                𝟙 (S.obj (op j₁)))) := by
      simpa using
        (refinementFiber_app_fiberMk
          (j := glued_refinement_inclusion j₁) (T := T)
          (e := glued_refinement_iso S j₁ f₁ 𝒰 k)
          (U := op j₁) (W := S.obj (op j₁)) (f := 𝟙 (S.obj (op j₁))))
    have hunit :
        (show (fiber.{max u v w} T).obj (S.obj (op j₁)) from
          fiberMk.{max u v w}
            (U := op ((glued_refinement_inclusion j₁) j₁))
            ((glued_refinement_iso S j₁ f₁ 𝒰 k).inv.app (op j₁) ≫
              𝟙 (S.obj (op j₁)))) =
        (show (fiber.{max u v w} T).obj (S.obj (op j₁)) from
          fiberMk.{max u v w}
            (U := op (⟨Sum.inl j₁⟩ : glued_refinement_index j₁))
            (𝟙 (S.obj (op j₁)))) := by
      refine congrArg
        (fun m ↦ (show (fiber.{max u v w} T).obj (S.obj (op j₁)) from
          fiberMk.{max u v w}
            (U := op (⟨Sum.inl j₁⟩ : glued_refinement_index j₁)) m)) ?_
      simpa using
        glued_refinement_iso_inv_app_eq_id
          (S := S) (j₁ := j₁) (j0 := j₁) (f₁ := f₁) (𝒰 := 𝒰) (k := k)
    exact hraw.trans hunit
  have hrightBase :
      (fiber.{max u v w} T).toPresheafFiber (S.obj (op j₁))
          (fiberMk.{max u v w}
            (U := op (⟨Sum.inr ⟨j₁, le_rfl⟩⟩ : glued_refinement_index j₁))
            (pullback.snd (𝒰.obj k).hom
              (S.map (homOfLE (show j₁ ≤ j₁ from le_rfl)).op ≫ f₁))) Fobj t =
        (fiber.{max u v w} T).toPresheafFiber (S.obj (op j₁))
          (show (fiber.{max u v w} T).obj (S.obj (op j₁)) from
            ηG.app (S.obj (op j₁))
              (show (fiber.{max u v w} S).obj (S.obj (op j₁)) from
                fiberMk.{max u v w} (𝟙 (S.obj (op j₁))))) Fobj t := by
    -- Rewrite the explicit right-base germ by the specialized fiber equality.
    have hcollapse :
        (show (fiber.{max u v w} T).obj (S.obj (op j₁)) from
          fiberMk.{max u v w}
            (T.map rightBaseToLeft ≫ 𝟙 (S.obj (op j₁)))) =
        (show (fiber.{max u v w} T).obj (S.obj (op j₁)) from
          fiberMk.{max u v w}
            (U := op (⟨Sum.inl j₁⟩ : glued_refinement_index j₁))
            (𝟙 (S.obj (op j₁)))) := by
      simpa using
        (fiberMk_map_comp.{max u v w}
          (p := T) (g := rightBaseToLeft) (f := 𝟙 (S.obj (op j₁))) :
            fiberMk.{max u v w} (T.map rightBaseToLeft ≫ 𝟙 (S.obj (op j₁))) =
              fiberMk.{max u v w} (𝟙 (S.obj (op j₁))))
    have hexplicit :
        (show (fiber.{max u v w} T).obj (S.obj (op j₁)) from
          fiberMk.{max u v w}
            (U := op (⟨Sum.inr ⟨j₁, le_rfl⟩⟩ : glued_refinement_index j₁))
            (pullback.snd (𝒰.obj k).hom
              (S.map (homOfLE (show j₁ ≤ j₁ from le_rfl)).op ≫ f₁))) =
        (show (fiber.{max u v w} T).obj (S.obj (op j₁)) from
          fiberMk.{max u v w}
            (T.map rightBaseToLeft ≫ 𝟙 (S.obj (op j₁)))) := by
      refine congrArg
        (fun m ↦ (show (fiber.{max u v w} T).obj (S.obj (op j₁)) from
          fiberMk.{max u v w} m)) ?_
      have hmorph :
          pullback.snd (𝒰.obj k).hom
              (S.map (homOfLE (show j₁ ≤ j₁ from le_rfl)).op ≫ f₁) =
            T.map rightBaseToLeft ≫ 𝟙 (S.obj (op j₁)) := by
        rw [hrightBaseToLeft.symm]
        exact (Category.comp_id (T.map rightBaseToLeft)).symm
      exact hmorph
    exact
      congrArg
          (fun x ↦ (fiber.{max u v w} T).toPresheafFiber (S.obj (op j₁)) x Fobj t)
          hexplicit |>.trans <|
        (congrArg
          (fun x ↦ (fiber.{max u v w} T).toPresheafFiber (S.obj (op j₁)) x Fobj t)
          hcollapse).trans <|
        congrArg
          (fun x ↦ (fiber.{max u v w} T).toPresheafFiber (S.obj (op j₁)) x Fobj t)
          hleftGenerator.symm
  -- Now consume the two refinement maps by first normalizing the tail germ and then applying
  -- `toPresheafFiber_presheafFiber_app` for the glued refinement.
  calc
    (fiber.{max u v w} T).toPresheafFiber (S.obj (op j₁))
        (fiberMk.{max u v w}
          (U := op (⟨Sum.inr ⟨j₁, le_rfl⟩⟩ : glued_refinement_index j₁))
          (pullback.snd (𝒰.obj k).hom
            (S.map (homOfLE (show j₁ ≤ j₁ from le_rfl)).op ≫ f₁))) Fobj t =
      (fiber.{max u v w} T).toPresheafFiber (S.obj (op j₁))
        (ηG.app (S.obj (op j₁))
          (show (fiber.{max u v w} S).obj (S.obj (op j₁)) from
            fiberMk.{max u v w} (𝟙 (S.obj (op j₁))))) Fobj t := hrightBase
    _ =
      ηG.presheafFiber.app Fobj
        ((fiber.{max u v w} S).toPresheafFiber (S.obj (op j₁))
          (fiberMk.{max u v w} (𝟙 (S.obj (op j₁)))) Fobj t) := by
            symm
            simpa [ηG] using
              congrFun
                (NatTrans.toPresheafFiber_presheafFiber_app
                  (η := ηG) (F := Fobj) (X := S.obj (op j₁))
                  (fiberMk.{max u v w} (𝟙 (S.obj (op j₁)))))
                t
    _ = ηG.presheafFiber.app Fobj (ηTail.presheafFiber.app Fobj ŝt) := by
          rw [htail]
    _ =
      ((refinementFiber (glued_refinement_inclusion j₁)
        (glued_refinement_system S j₁ f₁ 𝒰 k)
        (glued_refinement_iso S j₁ f₁ 𝒰 k)).presheafFiber).app Fobj
        (((refinementFiber (tail_inclusion j₁) S (Iso.refl _)).presheafFiber).app Fobj ŝt) := by
          rfl

/-- Helper for Lemma 7.39.1: on the canonical tail-stage generator, the branch-to-glued raw-fiber
comparison agrees with first returning to the original system and then refining to the glued
system. -/
private theorem glued_right_branch_presheafFiber_iso_hom_base_generator_eq
    {ι : Type w} [Preorder ι] [IsDirected ι (· ≤ ·)] [HasPullbacks C] (S : ιᵒᵖ ⥤ C)
    (j₁ : ι) {W : C} (f₁ : S.obj (op j₁) ⟶ W) (𝒰 : SemiRepresentableFamily.Over W)
    (k : 𝒰.index) (Fobj : Cᵒᵖ ⥤ Type (max u v w))
    (t : Fobj.obj (op (S.obj (op j₁)))) :
    let jTail : Set.Ici j₁ := ⟨j₁, le_rfl⟩
    let xTail : (fiber.{max u v w} (tail_system S j₁)).obj (S.obj (op j₁)) :=
      fiberMk.{max u v w} (U := op jTail) (X := S.obj (op j₁)) (𝟙 (S.obj (op j₁)))
    let ŝt : (fiber.{max u v w} (tail_system S j₁)).presheafFiber.obj Fobj :=
      (fiber.{max u v w} (tail_system S j₁)).toPresheafFiber (S.obj (op j₁)) xTail Fobj t
    (glued_right_branch_presheafFiber_iso
        (S := S) (j₁ := j₁) (f₁ := f₁) (𝒰 := 𝒰) k Fobj).hom
        (tail_branch_presheafFiber_map
          (S := S) (j₁ := j₁) (f₁ := f₁) (𝒰 := 𝒰) Fobj k ŝt) =
      ((refinementFiber (glued_refinement_inclusion j₁)
        (glued_refinement_system S j₁ f₁ 𝒰 k)
        (glued_refinement_iso S j₁ f₁ 𝒰 k)).presheafFiber).app Fobj
        (((refinementFiber (tail_inclusion j₁) S (Iso.refl _)).presheafFiber).app Fobj ŝt) := by
  let jTail : Set.Ici j₁ := ⟨j₁, le_rfl⟩
  let xTail : (fiber.{max u v w} (tail_system S j₁)).obj (S.obj (op j₁)) :=
    fiberMk.{max u v w} (U := op jTail) (X := S.obj (op j₁)) (𝟙 (S.obj (op j₁)))
  let ŝt : (fiber.{max u v w} (tail_system S j₁)).presheafFiber.obj Fobj :=
    (fiber.{max u v w} (tail_system S j₁)).toPresheafFiber (S.obj (op j₁)) xTail Fobj t
  -- First normalize the tail-to-branch map on the canonical base generator.
  calc
    (glued_right_branch_presheafFiber_iso
        (S := S) (j₁ := j₁) (f₁ := f₁) (𝒰 := 𝒰) k Fobj).hom
        (tail_branch_presheafFiber_map
          (S := S) (j₁ := j₁) (f₁ := f₁) (𝒰 := 𝒰) Fobj k ŝt) =
      (glued_right_branch_presheafFiber_iso
        (S := S) (j₁ := j₁) (f₁ := f₁) (𝒰 := 𝒰) k Fobj).hom
        ((fiber.{max u v w} (branch_system S j₁ f₁ 𝒰 k)).toPresheafFiber (S.obj (op j₁))
          (fiberMk.{max u v w} (U := op jTail)
            ((branch_system_snd_hom (S := S) (j₁ := j₁) (f₁ := f₁) (𝒰 := 𝒰) k).app
              (op jTail))) Fobj t) := by
            exact congrArg
              ((glued_right_branch_presheafFiber_iso
                (S := S) (j₁ := j₁) (f₁ := f₁) (𝒰 := 𝒰) k Fobj).hom)
              (by
                simpa [jTail, xTail, ŝt] using
                  tail_branch_presheafFiber_map_base_generator_eq
                    (S := S) (j₁ := j₁) (f₁ := f₁) (𝒰 := 𝒰) (Fobj := Fobj) (k := k) t)
    _ =
      (fiber.{max u v w} (glued_refinement_system S j₁ f₁ 𝒰 k)).toPresheafFiber (S.obj (op j₁))
        (fiberMk.{max u v w}
          (U := op (⟨Sum.inr ⟨j₁, le_rfl⟩⟩ : glued_refinement_index j₁))
          (pullback.snd (𝒰.obj k).hom
            (S.map (homOfLE (show j₁ ≤ j₁ from le_rfl)).op ≫ f₁))) Fobj t := by
              simpa [jTail] using
                glued_right_branch_presheafFiber_iso_hom_branch_base_germ_eq
                  (S := S) (j₁ := j₁) (f₁ := f₁) (𝒰 := 𝒰) (k := k)
                  (Fobj := Fobj) (t := t)
    _ =
      ((refinementFiber (glued_refinement_inclusion j₁)
        (glued_refinement_system S j₁ f₁ 𝒰 k)
        (glued_refinement_iso S j₁ f₁ 𝒰 k)).presheafFiber).app Fobj
        (((refinementFiber (tail_inclusion j₁) S (Iso.refl _)).presheafFiber).app Fobj ŝt) := by
          simpa [jTail, xTail, ŝt] using
            glued_right_base_presheafFiber_germ_eq_refinement_image
              (S := S) (j₁ := j₁) (f₁ := f₁) (𝒰 := 𝒰) (k := k)
              (Fobj := Fobj) (t := t)

-- Proof sketch: represent `f` by a map from one stage of the original inverse system to `W`,
-- pull back the finite covering family `𝒰` to that stage, and use the sheaf condition together with
-- filtered-colimit commutation with finite products to find one cover member on which the images
-- of `s` and `s'` are still distinct. Adjoining those pullback stages yields a further directed
-- inverse system refining the original one, and the induced canonical maps on the associated
-- fibers still separate `s` and `s'` while making `f` come from one of the `u(𝒰ᵢ)`.
/-- Lemma 7.39.1: for a directed inverse system on a site whose category has pullbacks, two distinct elements of the canonical
raw sheaf fiber
`(sheafToPresheaf J (Type _) ⋙ (GrothendieckTopology.Point.ofIsCofiltered.fiber S').presheafFiber).obj ℱ`
of a sheaf can be separated after passing to a refinement of the inverse system, and a chosen
element of the source-facing set-valued functor
`(GrothendieckTopology.Point.ofIsCofiltered.fiber S').obj W` can simultaneously be made to come
from one member of a given finite covering family `𝒰 : SemiRepresentableFamily.Over W`. The
refinement data is given directly by a larger directed inverse system together with an order
embedding and an identification of the old system with the restriction of the new one. -/
theorem exists_refined_inverse_system_separating_sections_and_lifting_cover
    {ι : Type w} [Preorder ι] [IsDirected ι (· ≤ ·)] [HasPullbacks C] (S' : ιᵒᵖ ⥤ C)
    {ℱ : Sheaf J (Type (max u v w))}
    {s s' : (sheafToPresheaf J (Type (max u v w)) ⋙
      (fiber.{max u v w} S').presheafFiber).obj ℱ}
    (hss' : s ≠ s')
    {W : C} (𝒰 : SemiRepresentableFamily.Over W) [Finite 𝒰.index]
    (h𝒰 : 𝒰.toSieve ∈ J W)
    (f : (fiber.{max u v w} S').obj W) :
    ∃ (ι' : Type w) (_ : Preorder ι') (_ : IsDirected ι' (· ≤ ·))
      (T : ι'ᵒᵖ ⥤ C) (j : ι ↪o ι') (e : S' ≅ (j.toOrderHom.toFunctor).op ⋙ T),
      ((refinementFiber j T e).presheafFiber).app ((sheafToPresheaf J
        (Type (max u v w))).obj ℱ) s ≠
        ((refinementFiber j T e).presheafFiber).app ((sheafToPresheaf J
          (Type (max u v w))).obj ℱ) s' ∧
        ∃ i : 𝒰.index, ∃ y : (fiber.{max u v w} T).obj (𝒰.obj i).left,
          ((fiber.{max u v w} T).map (𝒰.obj i).hom) y =
            (refinementFiber j T e).app W f := by
  -- Represent the chosen fiber element by a single stage map, exactly as in the source proof.
  rcases fiberMk_jointly_surjective f with ⟨j0, f0, rfl⟩
  let _ : Nonempty ι := ⟨j0.unop⟩
  let Fobj : Cᵒᵖ ⥤ Type (max u v w) :=
    (sheafToPresheaf J (Type (max u v w))).obj ℱ
  -- Route correction: before passing to the tail above `j0`, put `s` and `s'` on one raw
  -- generator of `(fiber S').presheafFiber`.
  obtain ⟨X, x, t, t', hs, hs'⟩ :=
    inverse_system_presheafFiber_jointly_surjective₂ (S := S') (F := Fobj) s s'
  have htt' : t ≠ t' := by
    intro hEq
    have hFiberEq :
        (fiber.{max u v w} S').toPresheafFiber X x Fobj t =
          (fiber.{max u v w} S').toPresheafFiber X x Fobj t' := by
      simp [hEq]
    apply hss'
    exact hs.symm.trans (hFiberEq.trans hs')
  rcases fiberMk_jointly_surjective x with ⟨jx, gx, rfl⟩
  obtain ⟨j₁, hj₀, hjx⟩ := directed_of (· ≤ ·) j0.unop jx.unop
  let g₁ : S'.obj (op j₁) ⟶ X := S'.map (homOfLE hjx).op ≫ gx
  let f₁ : S'.obj (op j₁) ⟶ W := S'.map (homOfLE hj₀).op ≫ f0
  let t₁ : Fobj.obj (op (S'.obj (op j₁))) := Fobj.map g₁.op t
  let t₁' : Fobj.obj (op (S'.obj (op j₁))) := Fobj.map g₁.op t'
  have hs₁ :
      (fiber.{max u v w} S').toPresheafFiber (S'.obj (op j₁))
        (fiberMk (𝟙 (S'.obj (op j₁)))) Fobj t₁ = s := by
    -- Restrict the original common representative along the map from stage `j₁` to stage `jx`.
    calc
      (fiber.{max u v w} S').toPresheafFiber (S'.obj (op j₁))
          (fiberMk (𝟙 (S'.obj (op j₁)))) Fobj t₁ =
        (fiber.{max u v w} S').toPresheafFiber X
          ((fiber.{max u v w} S').map g₁ (fiberMk (𝟙 (S'.obj (op j₁))))) Fobj t := by
            simpa [t₁] using
              congrFun
                ((fiber.{max u v w} S').toPresheafFiber_w (F := Fobj)
                  g₁ (fiberMk (𝟙 (S'.obj (op j₁))))) t
      _ = (fiber.{max u v w} S').toPresheafFiber X (fiberMk g₁) Fobj t := by
            simp
      _ = (fiber.{max u v w} S').toPresheafFiber X (fiberMk gx) Fobj t := by
            simp [g₁]
      _ = s := hs
  have hs₁' :
      (fiber.{max u v w} S').toPresheafFiber (S'.obj (op j₁))
        (fiberMk (𝟙 (S'.obj (op j₁)))) Fobj t₁' = s' := by
    -- The same restriction step transports the second representative to the common tail stage.
    calc
      (fiber.{max u v w} S').toPresheafFiber (S'.obj (op j₁))
          (fiberMk (𝟙 (S'.obj (op j₁)))) Fobj t₁' =
        (fiber.{max u v w} S').toPresheafFiber X
          ((fiber.{max u v w} S').map g₁ (fiberMk (𝟙 (S'.obj (op j₁))))) Fobj t' := by
            simpa [t₁'] using
              congrFun
                ((fiber.{max u v w} S').toPresheafFiber_w (F := Fobj)
                  g₁ (fiberMk (𝟙 (S'.obj (op j₁))))) t'
      _ = (fiber.{max u v w} S').toPresheafFiber X (fiberMk g₁) Fobj t' := by
            simp
      _ = (fiber.{max u v w} S').toPresheafFiber X (fiberMk gx) Fobj t' := by
            simp [g₁]
      _ = s' := hs'
  let jTail : Set.Ici j₁ := ⟨j₁, le_rfl⟩
  let xTail : (fiber.{max u v w} (tail_system S' j₁)).obj (S'.obj (op j₁)) :=
    fiberMk.{max u v w} (U := op jTail) (X := S'.obj (op j₁)) (𝟙 (S'.obj (op j₁)))
  let ŝ : (fiber.{max u v w} (tail_system S' j₁)).presheafFiber.obj Fobj :=
    (fiber.{max u v w} (tail_system S' j₁)).toPresheafFiber (S'.obj (op j₁)) xTail Fobj t₁
  let ŝ' : (fiber.{max u v w} (tail_system S' j₁)).presheafFiber.obj Fobj :=
    (fiber.{max u v w} (tail_system S' j₁)).toPresheafFiber (S'.obj (op j₁)) xTail Fobj t₁'
  have htailSections :
      ((refinementFiber (tail_inclusion j₁) S' (Iso.refl _)).presheafFiber).app Fobj ŝ = s ∧
        ((refinementFiber (tail_inclusion j₁) S' (Iso.refl _)).presheafFiber).app Fobj ŝ' = s' ∧
        ŝ ≠ ŝ' := by
    -- Use the canonical tail-stage generators instead of abstract witnesses, so the final
    -- branch-to-glued comparison applies on the nose.
    simpa [jTail, xTail, ŝ, ŝ'] using
      canonical_tail_stage_sections (S' := S') (j₁ := j₁) (Fobj := Fobj)
        (s := s) (s' := s') (t₁ := t₁) (t₁' := t₁') hs₁ hs₁' hss'
  have hsTail :
      ((refinementFiber (tail_inclusion j₁) S' (Iso.refl _)).presheafFiber).app Fobj ŝ = s :=
    htailSections.1
  have hsTail' :
      ((refinementFiber (tail_inclusion j₁) S' (Iso.refl _)).presheafFiber).app Fobj ŝ' = s' :=
    htailSections.2.1
  have hTailNe : ŝ ≠ ŝ' := htailSections.2.2
  have hbranchRaw :
      ∃ k : 𝒰.index,
        tail_branch_presheafFiber_map (S := S') (j₁ := j₁) (f₁ := f₁) (𝒰 := 𝒰)
            Fobj k ŝ ≠
          tail_branch_presheafFiber_map (S := S') (j₁ := j₁) (f₁ := f₁) (𝒰 := 𝒰)
            Fobj k ŝ' := by
    -- Route correction: choose the branch only after mapping the distinct tail germs into the
    -- finite product of branch raw fibers, matching the textbook proof.
    have hproductInj :
        Function.Injective
          (tail_branch_product_map
            (S := S') (j₁ := j₁) (f₁ := f₁) (𝒰 := 𝒰) Fobj) := by
      -- Factor through the colimit/product comparison and use stagewise separatedness on the
      -- pulled-back cover, exactly as in the source proof.
      simpa [Fobj] using
        tail_branch_product_map_injective
          (J := J) (S := S') (j₁ := j₁) (f₁ := f₁) (𝒰 := 𝒰) h𝒰 ℱ
    exact
      exists_branch_raw_ne_of_tail_ne
        (S := S') (j₁ := j₁) (f₁ := f₁) (𝒰 := 𝒰) Fobj hTailNe hproductInj
  rcases hbranchRaw with ⟨k, hk⟩
  refine ⟨glued_refinement_index j₁, glued_refinement_preorder j₁,
      glued_refinement_isDirected j₁, glued_refinement_system S' j₁ f₁ 𝒰 k,
      glued_refinement_inclusion j₁, glued_refinement_iso S' j₁ f₁ 𝒰 k, ?_, ?_⟩
  · -- Apply the right-branch finality comparison on the explicit canonical tail generators and
    -- cancel it by injectivity to transport the chosen branch inequality into the glued refinement.
    intro hEq
    have hIsoEq :
        (glued_right_branch_presheafFiber_iso
          (S := S') (j₁ := j₁) (f₁ := f₁) (𝒰 := 𝒰) k Fobj).hom
            (tail_branch_presheafFiber_map
              (S := S') (j₁ := j₁) (f₁ := f₁) (𝒰 := 𝒰) Fobj k ŝ) =
          (glued_right_branch_presheafFiber_iso
            (S := S') (j₁ := j₁) (f₁ := f₁) (𝒰 := 𝒰) k Fobj).hom
            (tail_branch_presheafFiber_map
              (S := S') (j₁ := j₁) (f₁ := f₁) (𝒰 := 𝒰) Fobj k ŝ') := by
      calc
        (glued_right_branch_presheafFiber_iso
            (S := S') (j₁ := j₁) (f₁ := f₁) (𝒰 := 𝒰) k Fobj).hom
            (tail_branch_presheafFiber_map
              (S := S') (j₁ := j₁) (f₁ := f₁) (𝒰 := 𝒰) Fobj k ŝ) =
          ((refinementFiber (glued_refinement_inclusion j₁)
              (glued_refinement_system S' j₁ f₁ 𝒰 k)
              (glued_refinement_iso S' j₁ f₁ 𝒰 k)).presheafFiber).app Fobj
            (((refinementFiber (tail_inclusion j₁) S' (Iso.refl _)).presheafFiber).app
              Fobj ŝ) := by
                simpa [jTail, xTail, ŝ] using
                  glued_right_branch_presheafFiber_iso_hom_base_generator_eq
                    (S := S') (j₁ := j₁) (f₁ := f₁) (𝒰 := 𝒰) (k := k)
                    (Fobj := Fobj) (t := t₁)
        _ =
          ((refinementFiber (glued_refinement_inclusion j₁)
              (glued_refinement_system S' j₁ f₁ 𝒰 k)
              (glued_refinement_iso S' j₁ f₁ 𝒰 k)).presheafFiber).app Fobj s := by
                rw [hsTail]
        _ =
          ((refinementFiber (glued_refinement_inclusion j₁)
              (glued_refinement_system S' j₁ f₁ 𝒰 k)
              (glued_refinement_iso S' j₁ f₁ 𝒰 k)).presheafFiber).app Fobj s' := hEq
        _ =
          ((refinementFiber (glued_refinement_inclusion j₁)
              (glued_refinement_system S' j₁ f₁ 𝒰 k)
              (glued_refinement_iso S' j₁ f₁ 𝒰 k)).presheafFiber).app Fobj
            (((refinementFiber (tail_inclusion j₁) S' (Iso.refl _)).presheafFiber).app
              Fobj ŝ') := by
                rw [hsTail']
        _ =
          (glued_right_branch_presheafFiber_iso
            (S := S') (j₁ := j₁) (f₁ := f₁) (𝒰 := 𝒰) k Fobj).hom
            (tail_branch_presheafFiber_map
              (S := S') (j₁ := j₁) (f₁ := f₁) (𝒰 := 𝒰) Fobj k ŝ') := by
                symm
                simpa [jTail, xTail, ŝ'] using
                  glued_right_branch_presheafFiber_iso_hom_base_generator_eq
                    (S := S') (j₁ := j₁) (f₁ := f₁) (𝒰 := 𝒰) (k := k)
                    (Fobj := Fobj) (t := t₁')
    have hIsoInj :
        Function.Injective
          (glued_right_branch_presheafFiber_iso
            (S := S') (j₁ := j₁) (f₁ := f₁) (𝒰 := 𝒰) k Fobj).hom :=
      (ConcreteCategory.bijective_of_isIso
        ((glued_right_branch_presheafFiber_iso
          (S := S') (j₁ := j₁) (f₁ := f₁) (𝒰 := 𝒰) k Fobj).hom)).1
    exact hk (hIsoInj hIsoEq)
  · -- The lift half of the source proof is now realized directly at the right base branch stage.
    refine ⟨k, ?_⟩
    simpa [f₁] using
      glued_refinement_generator_lifts_cover
        (S := S') (hj₀ := hj₀) (f₀ := f0) (𝒰 := 𝒰) (k := k)

end

end CategoryTheory
