module

public import Mathlib.CategoryTheory.EssentiallySmall
public import Mathlib.CategoryTheory.Sites.Sheafification
public import Mathlib.CategoryTheory.Sites.Sheaf
public import stacks_project.Chap07.Definition_7_8_2
public import stacks_project.Chap07.Lemma_7_39_1
public import stacks_project.Chap07.Lemma_7_39_2.DiagramUnionCore

@[expose] public section

open CategoryTheory
open CategoryTheory.SemiRepresentableFamily.Over

universe u v w

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]

attribute [local instance] initiallySmall_of_essentiallySmall

section

variable {J : GrothendieckTopology C}

open GrothendieckTopology.Point.ofIsCofiltered

variable {ι : Type w} [Preorder ι]

/-- Helper for Lemma 7.39.2: package the direct union of a coherent directed diagram of stages as
a new refinement stage, once the original two sections are known to remain separated in that
direct union. -/
noncomputable def refinementStageDiagramLimitStage
    {δ : Type w} [Preorder δ] [IsDirected δ (· ≤ ·)]
    {ℱ : Sheaf J (Type (max u v w))}
    {S' : ιᵒᵖ ⥤ C}
    {s s' : (sheafToPresheaf J (Type (max u v w)) ⋙
      (fiber.{max u v w} S').presheafFiber).obj ℱ}
    (A : δ → refinement_stage (J := J) S' (ℱ := ℱ) s s')
    (hom : ∀ {a b : δ}, a ≤ b → refinement_stage_hom (J := J) (A a) (A b))
    (hom_refl :
      ∀ a : δ, hom (show a ≤ a from le_rfl) = refinement_stage_hom_refl (J := J) (A a))
    (hom_comp :
      ∀ {a b c : δ} (hab : a ≤ b) (hbc : b ≤ c),
        hom (le_trans hab hbc) =
          refinement_stage_hom.comp (J := J) (hom hab) (hom hbc))
    (a0 : δ)
    (hsep :
      letI : Preorder (refinementStageDiagramIndex (J := J) A) :=
        refinementStageDiagramIndexPreorder (J := J) A hom hom_refl hom_comp
      let TΔ := refinementStageDiagramSystem (J := J) A hom hom_refl hom_comp
      let jΔ := refinementStageDiagramSystemOriginalEmbedding
        (J := J) A hom hom_refl hom_comp a0
      let eΔ := refinementStageDiagramSystemOriginalIso (J := J) A hom hom_refl hom_comp a0
      ((refinementFiber jΔ TΔ eΔ).presheafFiber).app ((sheafToPresheaf J
        (Type (max u v w))).obj ℱ) s ≠
        ((refinementFiber jΔ TΔ eΔ).presheafFiber).app ((sheafToPresheaf J
          (Type (max u v w))).obj ℱ) s') :
    refinement_stage (J := J) S' (ℱ := ℱ) s s' := by
  letI : Preorder (refinementStageDiagramIndex (J := J) A) :=
    refinementStageDiagramIndexPreorder (J := J) A hom hom_refl hom_comp
  exact {
    I := refinementStageDiagramIndex (J := J) A
    instPreorder := refinementStageDiagramIndexPreorder (J := J) A hom hom_refl hom_comp
    instDirected := refinementStageDiagramIndexDirected (J := J) A hom
    T := refinementStageDiagramSystem (J := J) A hom hom_refl hom_comp
    j := refinementStageDiagramSystemOriginalEmbedding (J := J) A hom hom_refl hom_comp a0
    e := refinementStageDiagramSystemOriginalIso (J := J) A hom hom_refl hom_comp a0
    separated := hsep
    solved := refinementStageDiagramLimitSolved (J := J) A hom hom_refl hom_comp
    solved_realized := refinementStageDiagramLimitSolved_realized (J := J) A hom hom_refl hom_comp
  }

/-- Helper for Lemma 7.39.2: every stage of a coherent directed diagram maps to the packaged
direct-union stage. -/
noncomputable def refinementStageDiagramStageHomToLimit
    {δ : Type w} [Preorder δ] [IsDirected δ (· ≤ ·)]
    {ℱ : Sheaf J (Type (max u v w))}
    {S' : ιᵒᵖ ⥤ C}
    {s s' : (sheafToPresheaf J (Type (max u v w)) ⋙
      (fiber.{max u v w} S').presheafFiber).obj ℱ}
    (A : δ → refinement_stage (J := J) S' (ℱ := ℱ) s s')
    (hom : ∀ {a b : δ}, a ≤ b → refinement_stage_hom (J := J) (A a) (A b))
    (hom_refl :
      ∀ a : δ, hom (show a ≤ a from le_rfl) = refinement_stage_hom_refl (J := J) (A a))
    (hom_comp :
      ∀ {a b c : δ} (hab : a ≤ b) (hbc : b ≤ c),
        hom (le_trans hab hbc) =
          refinement_stage_hom.comp (J := J) (hom hab) (hom hbc))
    (a0 a : δ)
    (hsep :
      letI : Preorder (refinementStageDiagramIndex (J := J) A) :=
        refinementStageDiagramIndexPreorder (J := J) A hom hom_refl hom_comp
      let TΔ := refinementStageDiagramSystem (J := J) A hom hom_refl hom_comp
      let jΔ := refinementStageDiagramSystemOriginalEmbedding
        (J := J) A hom hom_refl hom_comp a0
      let eΔ := refinementStageDiagramSystemOriginalIso (J := J) A hom hom_refl hom_comp a0
      ((refinementFiber jΔ TΔ eΔ).presheafFiber).app ((sheafToPresheaf J
        (Type (max u v w))).obj ℱ) s ≠
        ((refinementFiber jΔ TΔ eΔ).presheafFiber).app ((sheafToPresheaf J
          (Type (max u v w))).obj ℱ) s') :
    refinement_stage_hom (J := J) (A a)
      (refinementStageDiagramLimitStage (J := J) A hom hom_refl hom_comp a0 hsep) := by
  letI : Preorder (refinementStageDiagramIndex (J := J) A) :=
    refinementStageDiagramIndexPreorder (J := J) A hom hom_refl hom_comp
  exact {
    k := refinementStageDiagramIndexInclusion (J := J) A hom hom_refl hom_comp a
    hT := refinementStageDiagramSystemInclusionIso (J := J) A hom hom_refl hom_comp a
    solved_mono := by
      intro r hr
      exact ⟨a, r, hr, rfl⟩
  }

/-- Helper for Lemma 7.39.2: the direct-union comparison from the image of an index under a
diagram morphism back to that index is exactly the morphism's structure map. -/
theorem refinementStageDiagramSystemMap_hom_self
    {δ : Type w} [Preorder δ]
    {ℱ : Sheaf J (Type (max u v w))}
    {S' : ιᵒᵖ ⥤ C}
    {s s' : (sheafToPresheaf J (Type (max u v w)) ⋙
      (fiber.{max u v w} S').presheafFiber).obj ℱ}
    (A : δ → refinement_stage (J := J) S' (ℱ := ℱ) s s')
    (hom : ∀ {a b : δ}, a ≤ b → refinement_stage_hom (J := J) (A a) (A b))
    (hom_refl :
      ∀ a : δ, hom (show a ≤ a from le_rfl) = refinement_stage_hom_refl (J := J) (A a))
    (hom_comp :
      ∀ {a b c : δ} (hab : a ≤ b) (hbc : b ≤ c),
        hom (le_trans hab hbc) =
          refinement_stage_hom.comp (J := J) (hom hab) (hom hbc))
    {a b : δ} (hab : a ≤ b) (i : (A a).I) :
    letI : Preorder (refinementStageDiagramIndex (J := J) A) :=
      refinementStageDiagramIndexPreorder (J := J) A hom hom_refl hom_comp
    refinementStageDiagramSystemMap (J := J) A hom
        (Opposite.op
          (⟨b, (hom hab).k i⟩ : refinementStageDiagramIndex (J := J) A))
        (Opposite.op (⟨a, i⟩ : refinementStageDiagramIndex (J := J) A))
        (⟨hab, le_rfl⟩) =
      (hom hab).hT.inv.app (Opposite.op i) := by
  letI : Preorder (refinementStageDiagramIndex (J := J) A) :=
    refinementStageDiagramIndexPreorder (J := J) A hom hom_refl hom_comp
  change (A b).T.map (homOfLE (Classical.choose_spec (⟨hab, le_rfl⟩ :
      refinementStageDiagramIndexLE (J := J) A hom
        (⟨a, i⟩ : refinementStageDiagramIndex (J := J) A)
        ⟨b, (hom hab).k i⟩))).op ≫
      (hom (Classical.choose (⟨hab, le_rfl⟩ :
        refinementStageDiagramIndexLE (J := J) A hom
          (⟨a, i⟩ : refinementStageDiagramIndex (J := J) A)
          ⟨b, (hom hab).k i⟩))).hT.inv.app (Opposite.op i) =
    (hom hab).hT.inv.app (Opposite.op i)
  have hchoose : Classical.choose (⟨hab, le_rfl⟩ :
      refinementStageDiagramIndexLE (J := J) A hom
        (⟨a, i⟩ : refinementStageDiagramIndex (J := J) A)
        ⟨b, (hom hab).k i⟩) = hab := Subsingleton.elim _ _
  simp [hchoose]

/-- Helper for Lemma 7.39.2: the map on inverse-system fibers from a diagram stage into the
direct union factors through any later diagram stage. -/
theorem refinementStageDiagramSystemInclusion_refinementFiber_of_le
    {δ : Type w} [Preorder δ]
    {ℱ : Sheaf J (Type (max u v w))}
    {S' : ιᵒᵖ ⥤ C}
    {s s' : (sheafToPresheaf J (Type (max u v w)) ⋙
      (fiber.{max u v w} S').presheafFiber).obj ℱ}
    (A : δ → refinement_stage (J := J) S' (ℱ := ℱ) s s')
    (hom : ∀ {a b : δ}, a ≤ b → refinement_stage_hom (J := J) (A a) (A b))
    (hom_refl :
      ∀ a : δ, hom (show a ≤ a from le_rfl) = refinement_stage_hom_refl (J := J) (A a))
    (hom_comp :
      ∀ {a b c : δ} (hab : a ≤ b) (hbc : b ≤ c),
        hom (le_trans hab hbc) =
          refinement_stage_hom.comp (J := J) (hom hab) (hom hbc))
    {a b : δ} (hab : a ≤ b) :
    letI : Preorder (refinementStageDiagramIndex (J := J) A) :=
      refinementStageDiagramIndexPreorder (J := J) A hom hom_refl hom_comp
    refinementFiber (refinementStageDiagramIndexInclusion
        (J := J) A hom hom_refl hom_comp a)
        (refinementStageDiagramSystem (J := J) A hom hom_refl hom_comp)
        (refinementStageDiagramSystemInclusionIso (J := J) A hom hom_refl hom_comp a) =
      refinementFiber (hom hab).k (A b).T (hom hab).hT ≫
        refinementFiber (refinementStageDiagramIndexInclusion
          (J := J) A hom hom_refl hom_comp b)
          (refinementStageDiagramSystem (J := J) A hom hom_refl hom_comp)
          (refinementStageDiagramSystemInclusionIso (J := J) A hom hom_refl hom_comp b) := by
  letI : Preorder (refinementStageDiagramIndex (J := J) A) :=
    refinementStageDiagramIndexPreorder (J := J) A hom hom_refl hom_comp
  ext W x
  rcases fiberMk_jointly_surjective x with ⟨U, f, rfl⟩
  simp [refinementFiber_app_fiberMk, refinementStageDiagramSystemInclusionIso]
  let i : (A a).I := Opposite.unop U
  let Xa : refinementStageDiagramIndex (J := J) A := ⟨a, i⟩
  let Xb : refinementStageDiagramIndex (J := J) A := ⟨b, (hom hab).k i⟩
  have hle : refinementStageDiagramIndexLE (J := J) A hom Xa Xb := ⟨hab, le_rfl⟩
  have hmap :
      (refinementStageDiagramSystem (J := J) A hom hom_refl hom_comp).map
          ((homOfLE hle).op) =
        (hom hab).hT.inv.app U := by
    have hself :
        refinementStageDiagramSystemMap (J := J) A hom
            (Opposite.op Xb) (Opposite.op Xa) hle =
          (hom hab).hT.inv.app U := by
      simpa [Xa, Xb, i] using
        refinementStageDiagramSystemMap_hom_self
          (J := J) A hom hom_refl hom_comp hab i
    simpa [refinementStageDiagramSystem, Xa, Xb, i] using hself
  let fΔ : (refinementStageDiagramSystem (J := J) A hom hom_refl hom_comp).obj
      (Opposite.op Xa) ⟶ W := f
  have hfiber :
      fiberMk.{max u v w}
          (p := refinementStageDiagramSystem (J := J) A hom hom_refl hom_comp)
          ((refinementStageDiagramSystem (J := J) A hom hom_refl hom_comp).map
              ((homOfLE hle).op) ≫ fΔ) =
        fiberMk.{max u v w}
          (p := refinementStageDiagramSystem (J := J) A hom hom_refl hom_comp) fΔ :=
    fiberMk_map_comp.{max u v w}
      (p := refinementStageDiagramSystem (J := J) A hom hom_refl hom_comp)
      ((homOfLE hle).op) fΔ
  rw [← hmap]
  calc
    fiberMk.{max u v w}
        (p := refinementStageDiagramSystem (J := J) A hom hom_refl hom_comp)
        (𝟙 ((A a).T.obj U) ≫ f) =
      fiberMk.{max u v w}
        (p := refinementStageDiagramSystem (J := J) A hom hom_refl hom_comp) fΔ := by
        simpa only [fΔ, refinementStageDiagramSystem, Xa, i] using
          congrArg
            (fun q =>
              fiberMk.{max u v w}
                (p := refinementStageDiagramSystem (J := J) A hom hom_refl hom_comp) q)
            (Category.id_comp fΔ)
    _ = fiberMk.{max u v w}
        (p := refinementStageDiagramSystem (J := J) A hom hom_refl hom_comp)
        ((refinementStageDiagramSystem (J := J) A hom hom_refl hom_comp).map
            ((homOfLE hle).op) ≫ fΔ) := hfiber.symm
    _ = fiberMk.{max u v w}
        (p := refinementStageDiagramSystem (J := J) A hom hom_refl hom_comp)
        (𝟙 ((A b).T.obj (Opposite.op ((hom hab).k i))) ≫
          (refinementStageDiagramSystem (J := J) A hom hom_refl hom_comp).map
            ((homOfLE hle).op) ≫ f) := by
        simpa only [fΔ, refinementStageDiagramSystem, Xb, i, Category.assoc] using
          (congrArg
            (fun q =>
              fiberMk.{max u v w}
                (p := refinementStageDiagramSystem (J := J) A hom hom_refl hom_comp) q)
            (Category.id_comp
              ((refinementStageDiagramSystem (J := J) A hom hom_refl hom_comp).map
                ((homOfLE hle).op) ≫ fΔ)).symm)

/-- Helper for Lemma 7.39.2: transporting a request from a diagram stage to the direct union is
the same as first transporting it to any later diagram stage and then to the direct union. -/
theorem refinementStageDiagramSystem_transport_request_of_le
    {δ : Type w} [Preorder δ]
    {ℱ : Sheaf J (Type (max u v w))}
    {S' : ιᵒᵖ ⥤ C}
    {s s' : (sheafToPresheaf J (Type (max u v w)) ⋙
      (fiber.{max u v w} S').presheafFiber).obj ℱ}
    (A : δ → refinement_stage (J := J) S' (ℱ := ℱ) s s')
    (hom : ∀ {a b : δ}, a ≤ b → refinement_stage_hom (J := J) (A a) (A b))
    (hom_refl :
      ∀ a : δ, hom (show a ≤ a from le_rfl) = refinement_stage_hom_refl (J := J) (A a))
    (hom_comp :
      ∀ {a b c : δ} (hab : a ≤ b) (hbc : b ≤ c),
        hom (le_trans hab hbc) =
          refinement_stage_hom.comp (J := J) (hom hab) (hom hbc))
    {a b : δ} (hab : a ≤ b) (r : finite_cover_lift_request J (A a).T) :
    letI : Preorder (refinementStageDiagramIndex (J := J) A) :=
      refinementStageDiagramIndexPreorder (J := J) A hom hom_refl hom_comp
    transport_request (J := J)
        (refinementStageDiagramIndexInclusion (J := J) A hom hom_refl hom_comp a)
        (refinementStageDiagramSystem (J := J) A hom hom_refl hom_comp)
        (refinementStageDiagramSystemInclusionIso (J := J) A hom hom_refl hom_comp a) r =
      transport_request (J := J)
        (refinementStageDiagramIndexInclusion (J := J) A hom hom_refl hom_comp b)
        (refinementStageDiagramSystem (J := J) A hom hom_refl hom_comp)
        (refinementStageDiagramSystemInclusionIso (J := J) A hom hom_refl hom_comp b)
        ((hom hab).map_request r) := by
  letI : Preorder (refinementStageDiagramIndex (J := J) A) :=
    refinementStageDiagramIndexPreorder (J := J) A hom hom_refl hom_comp
  cases r
  simp [transport_request, refinement_stage_hom.map_request,
    refinementStageDiagramSystemInclusion_refinementFiber_of_le
      (J := J) A hom hom_refl hom_comp hab]

/-- Helper for Lemma 7.39.2: if a later diagram stage is compatible with the recorded original
refinement data, then the original-to-limit map on presheaf fibers factors through that later
stage. This is the direct-union bridge used to keep the original two sections separated at
chain-limit stages. -/
theorem refinementStageDiagramSystemOriginal_presheafFiber_app_of_le
    {δ : Type w} [Preorder δ]
    {ℱ : Sheaf J (Type (max u v w))}
    {S' : ιᵒᵖ ⥤ C}
    {s s' : (sheafToPresheaf J (Type (max u v w)) ⋙
      (fiber.{max u v w} S').presheafFiber).obj ℱ}
    (A : δ → refinement_stage (J := J) S' (ℱ := ℱ) s s')
    (hom : ∀ {a b : δ}, a ≤ b → refinement_stage_hom (J := J) (A a) (A b))
    (hom_refl :
      ∀ a : δ, hom (show a ≤ a from le_rfl) = refinement_stage_hom_refl (J := J) (A a))
    (hom_comp :
      ∀ {a b c : δ} (hab : a ≤ b) (hbc : b ≤ c),
        hom (le_trans hab hbc) =
          refinement_stage_hom.comp (J := J) (hom hab) (hom hbc))
    (hcompat : ∀ {a b : δ} (hab : a ≤ b), (hom hab).original_compatible)
    {a0 b : δ} (hb : a0 ≤ b) (F : Cᵒᵖ ⥤ Type (max u v w)) :
    letI : Preorder (refinementStageDiagramIndex (J := J) A) :=
      refinementStageDiagramIndexPreorder (J := J) A hom hom_refl hom_comp
    let TΔ := refinementStageDiagramSystem (J := J) A hom hom_refl hom_comp
    ((refinementFiber
        (refinementStageDiagramSystemOriginalEmbedding (J := J) A hom hom_refl hom_comp a0)
        TΔ
        (refinementStageDiagramSystemOriginalIso (J := J) A hom hom_refl hom_comp a0)
      ).presheafFiber).app F =
      ((refinementFiber (A b).j (A b).T (A b).e).presheafFiber).app F ≫
        ((refinementFiber
          (refinementStageDiagramIndexInclusion (J := J) A hom hom_refl hom_comp b)
          TΔ
          (refinementStageDiagramSystemInclusionIso
            (J := J) A hom hom_refl hom_comp b)).presheafFiber).app F := by
  letI : Preorder (refinementStageDiagramIndex (J := J) A) :=
    refinementStageDiagramIndexPreorder (J := J) A hom hom_refl hom_comp
  let TΔ := refinementStageDiagramSystem (J := J) A hom hom_refl hom_comp
  let incl0 := refinementStageDiagramIndexInclusion (J := J) A hom hom_refl hom_comp a0
  let inclb := refinementStageDiagramIndexInclusion (J := J) A hom hom_refl hom_comp b
  have hleft :
      ((refinementFiber
          (refinementStageDiagramSystemOriginalEmbedding (J := J) A hom hom_refl hom_comp a0)
          TΔ
          (refinementStageDiagramSystemOriginalIso (J := J) A hom hom_refl hom_comp a0)
        ).presheafFiber).app F =
        ((refinementFiber (A a0).j (A a0).T (A a0).e).presheafFiber).app F ≫
          ((refinementFiber incl0 TΔ
            (refinementStageDiagramSystemInclusionIso
              (J := J) A hom hom_refl hom_comp a0)).presheafFiber).app F := by
    change
      ((refinementFiber (compose_refinement_embedding (A a0).j incl0) TΔ
        (compose_refinement_iso (A a0).j incl0 (A a0).e
          (refinementStageDiagramSystemInclusionIso
            (J := J) A hom hom_refl hom_comp a0))).presheafFiber).app F =
        ((refinementFiber (A a0).j (A a0).T (A a0).e).presheafFiber).app F ≫
          ((refinementFiber incl0 TΔ
            (refinementStageDiagramSystemInclusionIso
              (J := J) A hom hom_refl hom_comp a0)).presheafFiber).app F
    rw [show refinementFiber (compose_refinement_embedding (A a0).j incl0) TΔ
          (compose_refinement_iso (A a0).j incl0 (A a0).e
            (refinementStageDiagramSystemInclusionIso
              (J := J) A hom hom_refl hom_comp a0)) =
        refinementFiber (A a0).j (A a0).T (A a0).e ≫
          refinementFiber incl0 TΔ
            (refinementStageDiagramSystemInclusionIso
              (J := J) A hom hom_refl hom_comp a0) by
          exact refinementFiber_comp (A a0).j incl0 (A a0).e
            (refinementStageDiagramSystemInclusionIso
              (J := J) A hom hom_refl hom_comp a0)]
    exact refinementFiber_presheafFiber_app_comp
      (j := (A a0).j) (k := incl0) (e := (A a0).e)
      (e' := refinementStageDiagramSystemInclusionIso
        (J := J) A hom hom_refl hom_comp a0) F
  have hincl :
      ((refinementFiber incl0 TΔ
          (refinementStageDiagramSystemInclusionIso
            (J := J) A hom hom_refl hom_comp a0)).presheafFiber).app F =
        ((refinementFiber (hom hb).k (A b).T (hom hb).hT).presheafFiber).app F ≫
          ((refinementFiber inclb TΔ
            (refinementStageDiagramSystemInclusionIso
              (J := J) A hom hom_refl hom_comp b)).presheafFiber).app F := by
    rw [show refinementFiber incl0 TΔ
          (refinementStageDiagramSystemInclusionIso
            (J := J) A hom hom_refl hom_comp a0) =
        refinementFiber (hom hb).k (A b).T (hom hb).hT ≫
          refinementFiber inclb TΔ
            (refinementStageDiagramSystemInclusionIso
              (J := J) A hom hom_refl hom_comp b) by
          exact refinementStageDiagramSystemInclusion_refinementFiber_of_le
            (J := J) A hom hom_refl hom_comp hb]
    exact refinementFiber_presheafFiber_app_comp
      (j := (hom hb).k) (k := inclb) (e := (hom hb).hT)
      (e' := refinementStageDiagramSystemInclusionIso
        (J := J) A hom hom_refl hom_comp b) F
  have hstage :
      ((refinementFiber (A b).j (A b).T (A b).e).presheafFiber).app F =
        ((refinementFiber (A a0).j (A a0).T (A a0).e).presheafFiber).app F ≫
          ((refinementFiber (hom hb).k (A b).T (hom hb).hT).presheafFiber).app F :=
    refinement_stage_hom.original_compatible_presheafFiber_app
      (hom hb) (hcompat hb) F
  calc
    ((refinementFiber
        (refinementStageDiagramSystemOriginalEmbedding (J := J) A hom hom_refl hom_comp a0)
        TΔ
        (refinementStageDiagramSystemOriginalIso (J := J) A hom hom_refl hom_comp a0)
      ).presheafFiber).app F =
        ((refinementFiber (A a0).j (A a0).T (A a0).e).presheafFiber).app F ≫
          ((refinementFiber incl0 TΔ
            (refinementStageDiagramSystemInclusionIso
              (J := J) A hom hom_refl hom_comp a0)).presheafFiber).app F := hleft
    _ =
        ((refinementFiber (A a0).j (A a0).T (A a0).e).presheafFiber).app F ≫
          (((refinementFiber (hom hb).k (A b).T (hom hb).hT).presheafFiber).app F ≫
            ((refinementFiber inclb TΔ
              (refinementStageDiagramSystemInclusionIso
                (J := J) A hom hom_refl hom_comp b)).presheafFiber).app F) := by
          rw [hincl]
    _ =
        (((refinementFiber (A a0).j (A a0).T (A a0).e).presheafFiber).app F ≫
          ((refinementFiber (hom hb).k (A b).T (hom hb).hT).presheafFiber).app F) ≫
            ((refinementFiber inclb TΔ
              (refinementStageDiagramSystemInclusionIso
                (J := J) A hom hom_refl hom_comp b)).presheafFiber).app F := by
          rw [Category.assoc]
    _ =
        ((refinementFiber (A b).j (A b).T (A b).e).presheafFiber).app F ≫
          ((refinementFiber inclb TΔ
            (refinementStageDiagramSystemInclusionIso
              (J := J) A hom hom_refl hom_comp b)).presheafFiber).app F := by
          rw [← hstage]

/-- Helper for Lemma 7.39.2: equality after including one diagram stage into the direct union is
already witnessed after passing to some later diagram stage. -/
theorem refinementStageDiagramSystemInclusion_presheafFiber_eq_of_eq
    {δ : Type w} [Preorder δ] [IsDirected δ (· ≤ ·)]
    {ℱ : Sheaf J (Type (max u v w))}
    {S' : ιᵒᵖ ⥤ C}
    {s s' : (sheafToPresheaf J (Type (max u v w)) ⋙
      (fiber.{max u v w} S').presheafFiber).obj ℱ}
    (A : δ → refinement_stage (J := J) S' (ℱ := ℱ) s s')
    (hom : ∀ {a b : δ}, a ≤ b → refinement_stage_hom (J := J) (A a) (A b))
    (hom_refl :
      ∀ a : δ, hom (show a ≤ a from le_rfl) = refinement_stage_hom_refl (J := J) (A a))
    (hom_comp :
      ∀ {a b c : δ} (hab : a ≤ b) (hbc : b ≤ c),
        hom (le_trans hab hbc) =
          refinement_stage_hom.comp (J := J) (hom hab) (hom hbc))
    (a : δ) (F : Cᵒᵖ ⥤ Type (max u v w))
    {x y : (fiber.{max u v w} (A a).T).presheafFiber.obj F}
    (hxy :
      letI : Preorder (refinementStageDiagramIndex (J := J) A) :=
        refinementStageDiagramIndexPreorder (J := J) A hom hom_refl hom_comp
      let TΔ := refinementStageDiagramSystem (J := J) A hom hom_refl hom_comp
      ((refinementFiber
        (refinementStageDiagramIndexInclusion (J := J) A hom hom_refl hom_comp a)
        TΔ
        (refinementStageDiagramSystemInclusionIso
          (J := J) A hom hom_refl hom_comp a)).presheafFiber).app F x =
      ((refinementFiber
        (refinementStageDiagramIndexInclusion (J := J) A hom hom_refl hom_comp a)
        TΔ
        (refinementStageDiagramSystemInclusionIso
          (J := J) A hom hom_refl hom_comp a)).presheafFiber).app F y) :
    ∃ b, ∃ hab : a ≤ b,
      ((refinementFiber (hom hab).k (A b).T (hom hab).hT).presheafFiber).app F x =
        ((refinementFiber (hom hab).k (A b).T (hom hab).hT).presheafFiber).app F y := by
  classical
  letI : Preorder (refinementStageDiagramIndex (J := J) A) :=
    refinementStageDiagramIndexPreorder (J := J) A hom hom_refl hom_comp
  let TΔ := refinementStageDiagramSystem (J := J) A hom hom_refl hom_comp
  let incla := refinementStageDiagramIndexInclusion (J := J) A hom hom_refl hom_comp a
  let ea := refinementStageDiagramSystemInclusionIso (J := J) A hom hom_refl hom_comp a
  obtain ⟨j₀, z₀, hx₀⟩ :=
    CategoryTheory.Limits.Types.jointly_surjective_of_isColimit
      (CategoryTheory.Limits.colimit.isColimit
        ((CategoryTheory.CategoryOfElements.π (fiber.{max u v w} (A a).T)).op ⋙ F)) x
  rcases fiberMk_jointly_surjective (Opposite.unop j₀).2 with ⟨U₀, f₀, hf₀⟩
  letI : Nonempty (A a).I := ⟨Opposite.unop U₀⟩
  obtain ⟨X, x₁, z, z', hx, hy⟩ :=
    inverse_system_presheafFiber_jointly_surjective₂ (S := (A a).T) (F := F) x y
  rcases fiberMk_jointly_surjective x₁ with ⟨U, f, rfl⟩
  let i : (A a).I := Opposite.unop U
  let Xa : refinementStageDiagramIndex (J := J) A := ⟨a, i⟩
  let UΔ : (refinementStageDiagramIndex (J := J) A)ᵒᵖ := Opposite.op Xa
  let fΔ : TΔ.obj UΔ ⟶ X := ea.inv.app U ≫ f
  let xΔ : (fiber.{max u v w} TΔ).obj X := fiberMk fΔ
  have hlim :
      (fiber.{max u v w} TΔ).toPresheafFiber X xΔ F z =
        (fiber.{max u v w} TΔ).toPresheafFiber X xΔ F z' := by
    calc
      (fiber.{max u v w} TΔ).toPresheafFiber X xΔ F z =
          ((refinementFiber incla TΔ ea).presheafFiber).app F
            ((fiber.{max u v w} (A a).T).toPresheafFiber X (fiberMk f) F z) := by
            symm
            simpa [xΔ, fΔ, incla, ea] using
              congrFun
                (NatTrans.toPresheafFiber_presheafFiber_app
                  (η := refinementFiber incla TΔ ea) (F := F) X (fiberMk f)) z
      _ = ((refinementFiber incla TΔ ea).presheafFiber).app F x := by
            rw [hx]
      _ = ((refinementFiber incla TΔ ea).presheafFiber).app F y := hxy
      _ = ((refinementFiber incla TΔ ea).presheafFiber).app F
            ((fiber.{max u v w} (A a).T).toPresheafFiber X (fiberMk f) F z') := by
            rw [hy]
      _ = (fiber.{max u v w} TΔ).toPresheafFiber X xΔ F z' := by
            simpa [xΔ, fΔ, incla, ea] using
              congrFun
                (NatTrans.toPresheafFiber_presheafFiber_app
                  (η := refinementFiber incla TΔ ea) (F := F) X (fiberMk f)) z'
  have hid :
      (fiber.{max u v w} TΔ).toPresheafFiber (TΔ.obj UΔ)
          (fiberMk (𝟙 (TΔ.obj UΔ))) F (F.map fΔ.op z) =
        (fiber.{max u v w} TΔ).toPresheafFiber (TΔ.obj UΔ)
          (fiberMk (𝟙 (TΔ.obj UΔ))) F (F.map fΔ.op z') := by
    have hz :
        (fiber.{max u v w} TΔ).toPresheafFiber (TΔ.obj UΔ)
            (fiberMk (𝟙 (TΔ.obj UΔ))) F (F.map fΔ.op z) =
          (fiber.{max u v w} TΔ).toPresheafFiber X xΔ F z := by
      calc
        (fiber.{max u v w} TΔ).toPresheafFiber (TΔ.obj UΔ)
            (fiberMk (𝟙 (TΔ.obj UΔ))) F (F.map fΔ.op z) =
            (fiber.{max u v w} TΔ).toPresheafFiber X
              ((fiber.{max u v w} TΔ).map fΔ (fiberMk (𝟙 (TΔ.obj UΔ)))) F z := by
              simpa using
                congrFun
                  ((fiber.{max u v w} TΔ).toPresheafFiber_w
                    (F := F) fΔ (fiberMk (𝟙 (TΔ.obj UΔ)))) z
        _ = (fiber.{max u v w} TΔ).toPresheafFiber X xΔ F z := by
              simp [xΔ, fΔ]
    have hz' :
        (fiber.{max u v w} TΔ).toPresheafFiber (TΔ.obj UΔ)
            (fiberMk (𝟙 (TΔ.obj UΔ))) F (F.map fΔ.op z') =
          (fiber.{max u v w} TΔ).toPresheafFiber X xΔ F z' := by
      calc
        (fiber.{max u v w} TΔ).toPresheafFiber (TΔ.obj UΔ)
            (fiberMk (𝟙 (TΔ.obj UΔ))) F (F.map fΔ.op z') =
            (fiber.{max u v w} TΔ).toPresheafFiber X
              ((fiber.{max u v w} TΔ).map fΔ (fiberMk (𝟙 (TΔ.obj UΔ)))) F z' := by
              simpa using
                congrFun
                  ((fiber.{max u v w} TΔ).toPresheafFiber_w
                    (F := F) fΔ (fiberMk (𝟙 (TΔ.obj UΔ)))) z'
        _ = (fiber.{max u v w} TΔ).toPresheafFiber X xΔ F z' := by
              simp [xΔ, fΔ]
    exact hz.trans (hlim.trans hz'.symm)
  letI : Nonempty (refinementStageDiagramIndex (J := J) A) := ⟨Xa⟩
  letI : IsDirected (refinementStageDiagramIndex (J := J) A) (· ≤ ·) :=
    refinementStageDiagramIndexDirected (J := J) A hom
  have hcol :
      (inverse_system_presheafFiberCocone (S := TΔ) F).ι.app (Opposite.op UΔ)
          (F.map fΔ.op z) =
        (inverse_system_presheafFiberCocone (S := TΔ) F).ι.app (Opposite.op UΔ)
          (F.map fΔ.op z') := by
    simpa [inverse_system_presheafFiberCocone, UΔ] using hid
  rcases (CategoryTheory.Limits.Types.FilteredColimit.isColimit_eq_iff'
      (F := TΔ.op ⋙ F)
      (ht := inverse_system_presheafFiber_isColimit (S := TΔ) F)
      (i := Opposite.op UΔ) (x := F.map fΔ.op z) (y := F.map fΔ.op z')).1 hcol with
    ⟨Zopop, m, hm⟩
  let Z : refinementStageDiagramIndex (J := J) A := Opposite.unop (Opposite.unop Zopop)
  let hXaZ : Xa ≤ Z := leOfHom m.unop.unop
  let hab : a ≤ Z.1 := refinementStageDiagramIndexLE_stageLe (J := J) A hom hXaZ
  let hidx : (hom hab).k i ≤ Z.2 := refinementStageDiagramIndexLE_rel (J := J) A hom hXaZ
  refine ⟨Z.1, hab, ?_⟩
  let gB : (A Z.1).T.obj (Opposite.op Z.2) ⟶ X :=
    (A Z.1).T.map (homOfLE hidx).op ≫ (hom hab).hT.inv.app U ≫ f
  have hidz :
      F.map (𝟙 ((A a).T.obj U)).op (F.map f.op z) = F.map f.op z := by
    simpa [op_id] using
      (FunctorToTypes.map_id_apply (F := F) (X := Opposite.op ((A a).T.obj U))
        (a := F.map f.op z))
  have hidz' :
      F.map (𝟙 ((A a).T.obj U)).op (F.map f.op z') = F.map f.op z' := by
    simpa [op_id] using
      (FunctorToTypes.map_id_apply (F := F) (X := Opposite.op ((A a).T.obj U))
        (a := F.map f.op z'))
  have hm' : F.map gB.op z = F.map gB.op z' := by
    simpa [gB, Functor.comp_map, refinementStageDiagramSystem, refinementStageDiagramSystemMap,
      refinementStageDiagramIndexLE_stageLe, refinementStageDiagramIndexLE_rel,
      refinementStageDiagramSystemInclusionIso, ea, op_id, FunctorToTypes.map_id_apply,
      hidz, hidz', TΔ, UΔ, Xa, Z, hXaZ, hab, hidx, fΔ, Category.assoc] using hm
  letI : Nonempty (A Z.1).I := ⟨Z.2⟩
  have hstage :
      (fiber.{max u v w} (A Z.1).T).toPresheafFiber X
          ((refinementFiber (hom hab).k (A Z.1).T (hom hab).hT).app X (fiberMk f)) F z =
        (fiber.{max u v w} (A Z.1).T).toPresheafFiber X
          ((refinementFiber (hom hab).k (A Z.1).T (hom hab).hT).app X (fiberMk f)) F z' := by
    refine (inverseSystem_toPresheafFiber_eq_iff (A Z.1).T X
      ((refinementFiber (hom hab).k (A Z.1).T (hom hab).hT).app X (fiberMk f)) z z').2 ?_
    refine ⟨(A Z.1).T.obj (Opposite.op Z.2), gB,
      fiberMk (𝟙 ((A Z.1).T.obj (Opposite.op Z.2))), ?_, hm'⟩
    simp [gB, refinementFiber_app_fiberMk]
  calc
    ((refinementFiber (hom hab).k (A Z.1).T (hom hab).hT).presheafFiber).app F x =
        ((refinementFiber (hom hab).k (A Z.1).T (hom hab).hT).presheafFiber).app F
          ((fiber.{max u v w} (A a).T).toPresheafFiber X (fiberMk f) F z) := by
          rw [hx]
    _ = (fiber.{max u v w} (A Z.1).T).toPresheafFiber X
          ((refinementFiber (hom hab).k (A Z.1).T (hom hab).hT).app X (fiberMk f)) F z := by
          simpa using
            congrFun
              (NatTrans.toPresheafFiber_presheafFiber_app
                (η := refinementFiber (hom hab).k (A Z.1).T (hom hab).hT)
                (F := F) X (fiberMk f)) z
    _ = (fiber.{max u v w} (A Z.1).T).toPresheafFiber X
          ((refinementFiber (hom hab).k (A Z.1).T (hom hab).hT).app X (fiberMk f)) F z' :=
          hstage
    _ = ((refinementFiber (hom hab).k (A Z.1).T (hom hab).hT).presheafFiber).app F
          ((fiber.{max u v w} (A a).T).toPresheafFiber X (fiberMk f) F z') := by
          symm
          simpa using
            congrFun
              (NatTrans.toPresheafFiber_presheafFiber_app
                (η := refinementFiber (hom hab).k (A Z.1).T (hom hab).hT)
                (F := F) X (fiberMk f)) z'
    _ = ((refinementFiber (hom hab).k (A Z.1).T (hom hab).hT).presheafFiber).app F y := by
          rw [hy]

/-- Helper for Lemma 7.39.2: a coherent directed diagram of compatible refinement stages keeps
the originally separated sections separated after passing to the direct-union stage. -/
theorem refinementStageDiagramLimitStage_separated_of_compatible
    {δ : Type w} [Preorder δ] [IsDirected δ (· ≤ ·)]
    {ℱ : Sheaf J (Type (max u v w))}
    {S' : ιᵒᵖ ⥤ C}
    {s s' : (sheafToPresheaf J (Type (max u v w)) ⋙
      (fiber.{max u v w} S').presheafFiber).obj ℱ}
    (A : δ → refinement_stage (J := J) S' (ℱ := ℱ) s s')
    (hom : ∀ {a b : δ}, a ≤ b → refinement_stage_hom (J := J) (A a) (A b))
    (hom_refl :
      ∀ a : δ, hom (show a ≤ a from le_rfl) = refinement_stage_hom_refl (J := J) (A a))
    (hom_comp :
      ∀ {a b c : δ} (hab : a ≤ b) (hbc : b ≤ c),
        hom (le_trans hab hbc) =
          refinement_stage_hom.comp (J := J) (hom hab) (hom hbc))
    (hcompat : ∀ {a b : δ} (hab : a ≤ b), (hom hab).original_compatible)
    (a0 : δ) :
    letI : Preorder (refinementStageDiagramIndex (J := J) A) :=
      refinementStageDiagramIndexPreorder (J := J) A hom hom_refl hom_comp
    let TΔ := refinementStageDiagramSystem (J := J) A hom hom_refl hom_comp
    let jΔ := refinementStageDiagramSystemOriginalEmbedding
      (J := J) A hom hom_refl hom_comp a0
    let eΔ := refinementStageDiagramSystemOriginalIso (J := J) A hom hom_refl hom_comp a0
    ((refinementFiber jΔ TΔ eΔ).presheafFiber).app ((sheafToPresheaf J
      (Type (max u v w))).obj ℱ) s ≠
      ((refinementFiber jΔ TΔ eΔ).presheafFiber).app ((sheafToPresheaf J
        (Type (max u v w))).obj ℱ) s' := by
  letI : Preorder (refinementStageDiagramIndex (J := J) A) :=
    refinementStageDiagramIndexPreorder (J := J) A hom hom_refl hom_comp
  let Fobj : Cᵒᵖ ⥤ Type (max u v w) :=
    (sheafToPresheaf J (Type (max u v w))).obj ℱ
  let TΔ := refinementStageDiagramSystem (J := J) A hom hom_refl hom_comp
  let incl0 := refinementStageDiagramIndexInclusion (J := J) A hom hom_refl hom_comp a0
  let eIncl0 := refinementStageDiagramSystemInclusionIso
    (J := J) A hom hom_refl hom_comp a0
  let x := ((refinementFiber (A a0).j (A a0).T (A a0).e).presheafFiber).app Fobj s
  let y := ((refinementFiber (A a0).j (A a0).T (A a0).e).presheafFiber).app Fobj s'
  change ((refinementFiber
      (refinementStageDiagramSystemOriginalEmbedding
        (J := J) A hom hom_refl hom_comp a0)
      TΔ
      (refinementStageDiagramSystemOriginalIso (J := J) A hom hom_refl hom_comp a0)
    ).presheafFiber).app Fobj s ≠
    ((refinementFiber
      (refinementStageDiagramSystemOriginalEmbedding
        (J := J) A hom hom_refl hom_comp a0)
      TΔ
      (refinementStageDiagramSystemOriginalIso (J := J) A hom hom_refl hom_comp a0)
    ).presheafFiber).app Fobj s'
  intro hlim
  have hfactor :
      ((refinementFiber
          (refinementStageDiagramSystemOriginalEmbedding
            (J := J) A hom hom_refl hom_comp a0)
          TΔ
          (refinementStageDiagramSystemOriginalIso (J := J) A hom hom_refl hom_comp a0)
        ).presheafFiber).app Fobj =
        ((refinementFiber (A a0).j (A a0).T (A a0).e).presheafFiber).app Fobj ≫
          ((refinementFiber incl0 TΔ eIncl0).presheafFiber).app Fobj := by
    simpa [Fobj, TΔ, incl0, eIncl0] using
      refinementStageDiagramSystemOriginal_presheafFiber_app_of_le
        (J := J) A hom hom_refl hom_comp hcompat (a0 := a0) (b := a0)
        (show a0 ≤ a0 from le_rfl) Fobj
  have hxy :
      ((refinementFiber incl0 TΔ eIncl0).presheafFiber).app Fobj x =
        ((refinementFiber incl0 TΔ eIncl0).presheafFiber).app Fobj y := by
    calc
      ((refinementFiber incl0 TΔ eIncl0).presheafFiber).app Fobj x =
          (((refinementFiber (A a0).j (A a0).T (A a0).e).presheafFiber).app Fobj ≫
            ((refinementFiber incl0 TΔ eIncl0).presheafFiber).app Fobj) s := by
            rfl
      _ = ((refinementFiber
              (refinementStageDiagramSystemOriginalEmbedding
                (J := J) A hom hom_refl hom_comp a0)
              TΔ
              (refinementStageDiagramSystemOriginalIso (J := J) A hom hom_refl hom_comp a0)
            ).presheafFiber).app Fobj s := by
            rw [← hfactor]
      _ = ((refinementFiber
              (refinementStageDiagramSystemOriginalEmbedding
                (J := J) A hom hom_refl hom_comp a0)
              TΔ
              (refinementStageDiagramSystemOriginalIso (J := J) A hom hom_refl hom_comp a0)
            ).presheafFiber).app Fobj s' := hlim
      _ = (((refinementFiber (A a0).j (A a0).T (A a0).e).presheafFiber).app Fobj ≫
            ((refinementFiber incl0 TΔ eIncl0).presheafFiber).app Fobj) s' := by
            rw [hfactor]
      _ = ((refinementFiber incl0 TΔ eIncl0).presheafFiber).app Fobj y := by
            rfl
  rcases refinementStageDiagramSystemInclusion_presheafFiber_eq_of_eq
      (J := J) A hom hom_refl hom_comp a0 Fobj hxy with
    ⟨b, hb, hbxy⟩
  have hstage :
      ((refinementFiber (A b).j (A b).T (A b).e).presheafFiber).app Fobj =
        ((refinementFiber (A a0).j (A a0).T (A a0).e).presheafFiber).app Fobj ≫
          ((refinementFiber (hom hb).k (A b).T (hom hb).hT).presheafFiber).app Fobj :=
    refinement_stage_hom.original_compatible_presheafFiber_app
      (J := J) (hom hb) (hcompat hb) Fobj
  have hstage_eq :
      ((refinementFiber (A b).j (A b).T (A b).e).presheafFiber).app Fobj s =
        ((refinementFiber (A b).j (A b).T (A b).e).presheafFiber).app Fobj s' := by
    rw [hstage]
    simpa [x, y] using hbxy
  exact (A b).separated hstage_eq

/-- Helper for Lemma 7.39.2: if every request descending to a diagram stage is realized after
passing to a later diagram stage, then the direct-union stage realizes all of its own requests. -/
theorem refinementStageDiagramLimitStage_realizes_all_requests_of_eventually
    {δ : Type w} [Preorder δ] [IsDirected δ (· ≤ ·)]
    {ℱ : Sheaf J (Type (max u v w))}
    {S' : ιᵒᵖ ⥤ C}
    {s s' : (sheafToPresheaf J (Type (max u v w)) ⋙
      (fiber.{max u v w} S').presheafFiber).obj ℱ}
    (A : δ → refinement_stage (J := J) S' (ℱ := ℱ) s s')
    (hom : ∀ {a b : δ}, a ≤ b → refinement_stage_hom (J := J) (A a) (A b))
    (hom_refl :
      ∀ a : δ, hom (show a ≤ a from le_rfl) = refinement_stage_hom_refl (J := J) (A a))
    (hom_comp :
      ∀ {a b c : δ} (hab : a ≤ b) (hbc : b ≤ c),
        hom (le_trans hab hbc) =
          refinement_stage_hom.comp (J := J) (hom hab) (hom hbc))
    (a0 : δ)
    (hsep :
      letI : Preorder (refinementStageDiagramIndex (J := J) A) :=
        refinementStageDiagramIndexPreorder (J := J) A hom hom_refl hom_comp
      let TΔ := refinementStageDiagramSystem (J := J) A hom hom_refl hom_comp
      let jΔ := refinementStageDiagramSystemOriginalEmbedding
        (J := J) A hom hom_refl hom_comp a0
      let eΔ := refinementStageDiagramSystemOriginalIso (J := J) A hom hom_refl hom_comp a0
      ((refinementFiber jΔ TΔ eΔ).presheafFiber).app ((sheafToPresheaf J
        (Type (max u v w))).obj ℱ) s ≠
        ((refinementFiber jΔ TΔ eΔ).presheafFiber).app ((sheafToPresheaf J
          (Type (max u v w))).obj ℱ) s')
    (eventually_realized :
      ∀ a (r : finite_cover_lift_request J (A a).T),
        ∃ b, ∃ hab : a ≤ b,
          request_realized (J := J) ((hom hab).map_request r)) :
    let L := refinementStageDiagramLimitStage (J := J) A hom hom_refl hom_comp a0 hsep
    ∀ r : finite_cover_lift_request J L.T, request_realized (J := J) r := by
  letI : Preorder (refinementStageDiagramIndex (J := J) A) :=
    refinementStageDiagramIndexPreorder (J := J) A hom hom_refl hom_comp
  intro L r
  rcases refinementStageDiagramSystem_request_descends (J := J) A hom hom_refl hom_comp r with
    ⟨a, r0, hr0⟩
  rcases eventually_realized a r0 with ⟨b, hab, hreal⟩
  have hlimit :
      request_realized (J := J)
        (transport_request (J := J)
          (refinementStageDiagramIndexInclusion (J := J) A hom hom_refl hom_comp b)
          (refinementStageDiagramSystem (J := J) A hom hom_refl hom_comp)
          (refinementStageDiagramSystemInclusionIso (J := J) A hom hom_refl hom_comp b)
          ((hom hab).map_request r0)) :=
    request_realized_transport (J := J)
      (refinementStageDiagramIndexInclusion (J := J) A hom hom_refl hom_comp b)
      (refinementStageDiagramSystem (J := J) A hom hom_refl hom_comp)
      (refinementStageDiagramSystemInclusionIso (J := J) A hom hom_refl hom_comp b)
      ((hom hab).map_request r0) hreal
  rwa [← refinementStageDiagramSystem_transport_request_of_le
      (J := J) A hom hom_refl hom_comp hab r0, hr0] at hlimit

/-- Helper for Lemma 7.39.2: if every source request is eventually realized in a coherent
directed diagram of refinement stages, then the direct-union stage realizes all source requests
after transport from the original system. -/
theorem refinementStageDiagramLimitStage_realizes_source_requests_of_eventually
    {δ : Type w} [Preorder δ] [IsDirected δ (· ≤ ·)]
    {ℱ : Sheaf J (Type (max u v w))}
    {S' : ιᵒᵖ ⥤ C}
    {s s' : (sheafToPresheaf J (Type (max u v w)) ⋙
      (fiber.{max u v w} S').presheafFiber).obj ℱ}
    (A : δ → refinement_stage (J := J) S' (ℱ := ℱ) s s')
    (hom : ∀ {a b : δ}, a ≤ b → refinement_stage_hom (J := J) (A a) (A b))
    (hom_refl :
      ∀ a : δ, hom (show a ≤ a from le_rfl) = refinement_stage_hom_refl (J := J) (A a))
    (hom_comp :
      ∀ {a b c : δ} (hab : a ≤ b) (hbc : b ≤ c),
        hom (le_trans hab hbc) =
          refinement_stage_hom.comp (J := J) (hom hab) (hom hbc))
    (a0 : δ)
    (hsep :
      letI : Preorder (refinementStageDiagramIndex (J := J) A) :=
        refinementStageDiagramIndexPreorder (J := J) A hom hom_refl hom_comp
      let TΔ := refinementStageDiagramSystem (J := J) A hom hom_refl hom_comp
      let jΔ := refinementStageDiagramSystemOriginalEmbedding
        (J := J) A hom hom_refl hom_comp a0
      let eΔ := refinementStageDiagramSystemOriginalIso (J := J) A hom hom_refl hom_comp a0
      ((refinementFiber jΔ TΔ eΔ).presheafFiber).app ((sheafToPresheaf J
        (Type (max u v w))).obj ℱ) s ≠
        ((refinementFiber jΔ TΔ eΔ).presheafFiber).app ((sheafToPresheaf J
          (Type (max u v w))).obj ℱ) s')
    (eventually_realized :
      ∀ r : finite_cover_lift_request J S',
        ∃ b, ∃ hb : a0 ≤ b,
          request_realized (J := J)
            ((hom hb).map_request
              (transport_request (J := J) (A a0).j (A a0).T (A a0).e r))) :
    let L := refinementStageDiagramLimitStage (J := J) A hom hom_refl hom_comp a0 hsep
    ∀ r : finite_cover_lift_request J S',
      request_realized (J := J) (transport_request (J := J) L.j L.T L.e r) := by
  letI : Preorder (refinementStageDiagramIndex (J := J) A) :=
    refinementStageDiagramIndexPreorder (J := J) A hom hom_refl hom_comp
  intro L r
  rcases eventually_realized r with ⟨b, hb, hreal⟩
  let r0 : finite_cover_lift_request J (A a0).T :=
    transport_request (J := J) (A a0).j (A a0).T (A a0).e r
  have hlimit :
      request_realized (J := J)
        (transport_request (J := J)
          (refinementStageDiagramIndexInclusion (J := J) A hom hom_refl hom_comp b)
          (refinementStageDiagramSystem (J := J) A hom hom_refl hom_comp)
          (refinementStageDiagramSystemInclusionIso (J := J) A hom hom_refl hom_comp b)
          ((hom hb).map_request r0)) :=
    request_realized_transport (J := J)
      (refinementStageDiagramIndexInclusion (J := J) A hom hom_refl hom_comp b)
      (refinementStageDiagramSystem (J := J) A hom hom_refl hom_comp)
      (refinementStageDiagramSystemInclusionIso (J := J) A hom hom_refl hom_comp b)
      ((hom hb).map_request r0) (by simpa [r0] using hreal)
  have hlimit0 :
      request_realized (J := J)
        (transport_request (J := J)
          (refinementStageDiagramIndexInclusion (J := J) A hom hom_refl hom_comp a0)
          (refinementStageDiagramSystem (J := J) A hom hom_refl hom_comp)
          (refinementStageDiagramSystemInclusionIso (J := J) A hom hom_refl hom_comp a0)
          r0) := by
    have htransport := refinementStageDiagramSystem_transport_request_of_le
      (J := J) A hom hom_refl hom_comp hb r0
    rw [htransport]
    exact hlimit
  change request_realized (J := J)
    (transport_request (J := J)
      (compose_refinement_embedding (A a0).j
        (refinementStageDiagramIndexInclusion (J := J) A hom hom_refl hom_comp a0))
      (refinementStageDiagramSystem (J := J) A hom hom_refl hom_comp)
      (compose_refinement_iso (A a0).j
        (refinementStageDiagramIndexInclusion (J := J) A hom hom_refl hom_comp a0)
        (A a0).e (refinementStageDiagramSystemInclusionIso (J := J) A hom hom_refl hom_comp a0))
      r)
  rw [transport_request_comp]
  exact hlimit0

/-- Helper for Lemma 7.39.2: a coherent directed diagram whose direct union still separates the
two original sections and eventually realizes every source request supplies the source-facing
target of Stacks tag `00YP`. -/
theorem refinementStageDiagram_yields_source_target_of_eventually
    {δ : Type w} [Preorder δ] [IsDirected δ (· ≤ ·)]
    {ℱ : Sheaf J (Type (max u v w))}
    {S' : ιᵒᵖ ⥤ C}
    {s s' : (sheafToPresheaf J (Type (max u v w)) ⋙
      (fiber.{max u v w} S').presheafFiber).obj ℱ}
    (A : δ → refinement_stage (J := J) S' (ℱ := ℱ) s s')
    (hom : ∀ {a b : δ}, a ≤ b → refinement_stage_hom (J := J) (A a) (A b))
    (hom_refl :
      ∀ a : δ, hom (show a ≤ a from le_rfl) = refinement_stage_hom_refl (J := J) (A a))
    (hom_comp :
      ∀ {a b c : δ} (hab : a ≤ b) (hbc : b ≤ c),
        hom (le_trans hab hbc) =
          refinement_stage_hom.comp (J := J) (hom hab) (hom hbc))
    (a0 : δ)
    (hsep :
      letI : Preorder (refinementStageDiagramIndex (J := J) A) :=
        refinementStageDiagramIndexPreorder (J := J) A hom hom_refl hom_comp
      let TΔ := refinementStageDiagramSystem (J := J) A hom hom_refl hom_comp
      let jΔ := refinementStageDiagramSystemOriginalEmbedding
        (J := J) A hom hom_refl hom_comp a0
      let eΔ := refinementStageDiagramSystemOriginalIso (J := J) A hom hom_refl hom_comp a0
      ((refinementFiber jΔ TΔ eΔ).presheafFiber).app ((sheafToPresheaf J
        (Type (max u v w))).obj ℱ) s ≠
        ((refinementFiber jΔ TΔ eΔ).presheafFiber).app ((sheafToPresheaf J
          (Type (max u v w))).obj ℱ) s')
    (eventually_realized :
      ∀ r : finite_cover_lift_request J S',
        ∃ b, ∃ hb : a0 ≤ b,
          request_realized (J := J)
            ((hom hb).map_request
              (transport_request (J := J) (A a0).j (A a0).T (A a0).e r))) :
    ∃ (ι' : Type w) (_ : Preorder ι') (_ : IsDirected ι' (· ≤ ·))
      (T : ι'ᵒᵖ ⥤ C) (j : ι ↪o ι') (e : S' ≅ (j.toOrderHom.toFunctor).op ⋙ T),
      let u := fiber.{max u v w} T
      ((refinementFiber j T e).presheafFiber).app ((sheafToPresheaf J
        (Type (max u v w))).obj ℱ) s ≠
        ((refinementFiber j T e).presheafFiber).app ((sheafToPresheaf J
          (Type (max u v w))).obj ℱ) s' ∧
        ∀ {W : C} (𝒰 : SemiRepresentableFamily.Over.{w} W) [Finite 𝒰.index]
          (h𝒰 : 𝒰.toSieve ∈ J W) (f : (fiber.{max u v w} S').obj W),
            ∃ i : 𝒰.index, ∃ y : u.obj (𝒰.obj i).left,
              u.map (𝒰.obj i).hom y = (refinementFiber j T e).app W f := by
  let L := refinementStageDiagramLimitStage (J := J) A hom hom_refl hom_comp a0 hsep
  have hL : ∀ r : finite_cover_lift_request J S',
      request_realized (J := J) (transport_request (J := J) L.j L.T L.e r) :=
    refinementStageDiagramLimitStage_realizes_source_requests_of_eventually
      (J := J) A hom hom_refl hom_comp a0 hsep eventually_realized
  exact stage_realizing_source_requests_yields_source_target (J := J) (A := L) hL

end

end CategoryTheory
