module

public import stacks_project.Chap04.Remark_4_27_7

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.Limits.Types
open MorphismProperty
open MorphismProperty.RightFraction
open Localization
open Opposite

universe v u

namespace CategoryTheory
namespace MorphismProperty

scoped[MorphismPropertyOver] notation:80 S " / " X => MorphismProperty.Over S ⊤ X

open scoped MorphismPropertyOver

variable {C : Type u} [Category.{v} C]

/- Domain-style sampling for Remark 4.27.15:
- primary domain: right calculus of fractions and localized Hom-sets;
- inspected owner-level declarations:
  `localizationTargetArrows_isFiltered`,
  `MorphismProperty.Over.forget`,
  `uliftYoneda.obj`,
  `Localization.exists_rightFraction`,
  `RightFraction.map_eq_iff`;
- best owner abstraction: the denominator category is already the canonical owner `S / X`,
  i.e. `MorphismProperty.Over S ⊤ X`; its cofilteredness is the opposite-category transport of
  `localizationTargetArrows_isFiltered`, and the Hom-diagram is obtained by pulling back
  `uliftYoneda.obj Y` along `(MorphismProperty.Over.forget S ⊤ X ⋙ Over.forget X).op`.

Primitive-vs-derived split:
- primitive data: the diagram on `(S / X)ᵒᵖ` and its canonical cocone into
  `Hom_{S^{-1}\mathcal C}(X, Y)`;
- derived API: cofilteredness of `S / X`, the `Type`-colimit witness, and the resulting colimit
  comparison isomorphism.

Source/core/bridge triage:
- `source-facing`: `right_localization_hom_colimit`;
- `core/canonical`: `uliftYoneda.obj Y`, `RightFraction.map`, and the `Type`-colimit owner map
  `F.descColimitType c`;
- `bridge/view`: the opposite-category equivalence identifying `S / X` with the left denominator
  category for `S.op`, together with the cocone from the denominator diagram to the localized
  Hom-set. -/

private def sourceArrowsOpEquivUnderOp (S : MorphismProperty C) (X : C) :
    MorphismProperty.Under S.op ⊤ (Opposite.op X) ≌ (S / X)ᵒᵖ where
  functor :=
    { obj := fun U ↦ Opposite.op <| Over.mk (⊤ : MorphismProperty C) U.hom.unop U.prop
      map := fun f ↦
        (Over.homMk f.right.unop
          (by simpa using congrArg Quiver.Hom.unop (Under.w f))).op }
  inverse :=
    { obj := fun U ↦
        let U' := U.unop
        Under.mk (⊤ : MorphismProperty Cᵒᵖ) U'.hom.op U'.prop
      map := fun f ↦
        let f' := f.unop
        Under.homMk f'.left.op
          (by simpa using congrArg Quiver.Hom.op (Over.w f')) }
  unitIso := NatIso.ofComponents
    (fun U ↦ Under.isoMk (Iso.refl _) (by
      change U.hom ≫ 𝟙 U.right = U.hom
      exact Category.comp_id U.hom))
    (by
      intro U V f
      ext
      change f.right ≫ 𝟙 V.right = 𝟙 U.right ≫ f.right
      calc
        f.right ≫ 𝟙 V.right = f.right := Category.comp_id f.right
        _ = 𝟙 U.right ≫ f.right := (Category.id_comp f.right).symm)
  counitIso := NatIso.ofComponents
    (fun U ↦ (Over.isoMk (Iso.refl _) (by
      change 𝟙 (Opposite.unop U).left ≫ (Opposite.unop U).hom = (Opposite.unop U).hom
      exact Category.id_comp (Opposite.unop U).hom)).op)
    (by
      intro U V f
      apply Quiver.Hom.unop_inj
      ext
      change 𝟙 (Opposite.unop V).left ≫ f.unop.left = f.unop.left ≫ 𝟙 (Opposite.unop U).left
      calc
        𝟙 (Opposite.unop V).left ≫ f.unop.left = f.unop.left := Category.id_comp f.unop.left
        _ = f.unop.left ≫ 𝟙 (Opposite.unop U).left := (Category.comp_id f.unop.left).symm)
  functor_unitIso_comp := by
    intro U
    apply Quiver.Hom.unop_inj
    ext
    change 𝟙 (Opposite.unop U.right) ≫ 𝟙 (Opposite.unop U.right) = 𝟙 (Opposite.unop U.right)
    simp

/-- The right-fraction over-category `S/X`, realized as the canonical comma category
`MorphismProperty.Over S ⊤ X`, is cofiltered. -/
-- Proof sketch: this is the right-handed dual of `localizationTargetArrows_isFiltered`. Use the
-- identity denominator for nonemptiness, the right Ore condition to produce a common predecessor
-- of two denominators into `X`, and the right-cancellation axiom to equalize parallel triangles.
instance localizationSourceArrows_isCofiltered
    (S : MorphismProperty C) [S.HasRightCalculusOfFractions] (X : C) :
    IsCofiltered (S / X) := by
  let e := sourceArrowsOpEquivUnderOp S X
  letI : IsFiltered ((S / X)ᵒᵖ) := IsFiltered.of_equivalence e
  letI : IsCofiltered (((S / X)ᵒᵖ)ᵒᵖ) := inferInstance
  exact IsCofiltered.of_equivalence (opOpEquivalence (S / X))

variable (S : MorphismProperty C) [S.HasRightCalculusOfFractions] (X Y : C)

/-- The diagram on `(S / X)ᵒᵖ` whose value at `s : X' ⟶ X` is the Hom-set `Hom_C(X', Y)`. -/
abbrev rightLocalizationHomDiagram :
    (S / X)ᵒᵖ ⥤ Type (max u v) :=
  (Over.forget S ⊤ X ⋙ CategoryTheory.Over.forget X).op ⋙ uliftYoneda.{u}.obj Y

/-- The canonical map from the Hom-set indexed by `s : X' ⟶ X` to the localized Hom-set
`Hom_{S^{-1}\mathcal C}(X, Y)`. -/
noncomputable def rightLocalizationHomCoconeApp (U : (S / X)ᵒᵖ) :
    (rightLocalizationHomDiagram S X Y).obj U → (S.Q.obj X ⟶ S.Q.obj Y) :=
  fun f ↦
    (RightFraction.mk U.unop.hom U.unop.prop f.down).map S.Q (Localization.inverts S.Q S)

/-- Naturality of the canonical maps from the indexed Hom-sets into the localized Hom-set. -/
-- Proof sketch: an arrow in `(S / X)ᵒᵖ` is a commutative triangle refining one denominator by
-- another, and the diagram map is precomposition on numerators. The two resulting right fractions
-- in the localization represent the same morphism by functoriality of `RightFraction.map`.
private theorem rightLocalizationHomCocone_naturality {U V : (S / X)ᵒᵖ} (g : U ⟶ V) :
    (rightLocalizationHomDiagram S X Y).map g ≫
        rightLocalizationHomCoconeApp S X Y V =
      rightLocalizationHomCoconeApp S X Y U :=
  by
    funext f
    let φ : S.RightFraction X Y :=
      RightFraction.mk V.unop.hom V.unop.prop (g.unop.left ≫ f.down)
    let ψ : S.RightFraction X Y :=
      RightFraction.mk U.unop.hom U.unop.prop f.down
    change
      φ.map S.Q (Localization.inverts S.Q S) = ψ.map S.Q (Localization.inverts S.Q S)
    exact (RightFraction.map_eq_iff S.Q S φ ψ).2 <| by
      refine ⟨V.unop.left, 𝟙 _, g.unop.left, ?_, ?_, ?_⟩
      · simpa [φ, ψ] using (Over.w g.unop).symm
      · simp [φ, ψ]
      · simpa [φ] using V.unop.prop

-- The cocone on the right-localization Hom-diagram with point `Hom_{S^{-1}\mathcal C}(X, Y)`.
noncomputable def rightLocalizationHomCocone :
    Cocone (rightLocalizationHomDiagram S X Y) where
  pt := S.Q.obj X ⟶ S.Q.obj Y
  ι :=
    { app := rightLocalizationHomCoconeApp S X Y
      naturality := by
        intro U V g
        simpa using rightLocalizationHomCocone_naturality S X Y g }

-- Proof sketch: surjectivity is Lemma 4.27.13 in the form `Localization.exists_rightFraction`,
-- which writes any morphism in `S⁻¹ C` as a roof over some object of `S / X`. Injectivity is
-- Lemma 4.27.14 encoded by `RightFraction.map_eq_iff`: two roofs become equal in the localization
-- exactly when they agree after refining to a common predecessor in the denominator category.
theorem rightLocalizationHomCoconeTypes_isColimit :
    let F : (S / X)ᵒᵖ ⥤ Type (max u v) :=
      rightLocalizationHomDiagram S X Y
    let c : F.CoconeTypes := F.coconeTypesEquiv.symm (rightLocalizationHomCocone S X Y)
    c.IsColimit := by
  let F : (S / X)ᵒᵖ ⥤ Type (max u v) := rightLocalizationHomDiagram S X Y
  let c : F.CoconeTypes := F.coconeTypesEquiv.symm (rightLocalizationHomCocone S X Y)
  refine ⟨?_⟩
  constructor
  · rw [Functor.CoconeTypes.descColimitType_injective_iff_of_isFiltered]
    intro U V f g hfg
    let φ : S.RightFraction X Y :=
      RightFraction.mk U.unop.hom U.unop.prop f.down
    let ψ : S.RightFraction X Y :=
      RightFraction.mk V.unop.hom V.unop.prop g.down
    have hφψ : φ.map S.Q (Localization.inverts S.Q S) = ψ.map S.Q (Localization.inverts S.Q S) := by
      simpa [F, c, φ, ψ, rightLocalizationHomCocone, rightLocalizationHomCoconeApp,
        RightFraction.map] using hfg
    obtain ⟨Z, a, b, hab, hfg', hS⟩ :=
      (RightFraction.map_eq_iff S.Q S φ ψ).mp hφψ
    let W : S / X := Over.mk (⊤ : MorphismProperty C) (a ≫ U.unop.hom) hS
    refine ⟨Opposite.op W, (Over.homMk a rfl).op, (Over.homMk b hab.symm).op, ?_⟩
    change ULift.up (a ≫ f.down) = ULift.up (b ≫ g.down)
    simpa using hfg'
  · rw [Functor.CoconeTypes.descColimitType_surjective_iff]
    intro z
    obtain ⟨φ, hφ⟩ := Localization.exists_rightFraction S.Q S z
    let U : S / X := Over.mk (⊤ : MorphismProperty C) φ.s φ.hs
    have hφ' : S.Q.map φ.f = S.Q.map φ.s ≫ z := by
      simpa [RightFraction.map, Category.assoc] using
        congrArg (fun k ↦ S.Q.map φ.s ≫ k) hφ.symm
    refine ⟨Opposite.op U, ULift.up φ.f, ?_⟩
    letI := Localization.inverts S.Q S _ φ.hs
    apply (cancel_epi (S.Q.map φ.s)).1
    simpa [F, c, U, rightLocalizationHomCocone, rightLocalizationHomCoconeApp, RightFraction.map,
      Category.assoc] using hφ'

/-- Internal colimit witness for the canonical cocone used to construct
`right_localization_hom_colimit`. -/
noncomputable def rightLocalizationHomCocone_isColimit :
    IsColimit (rightLocalizationHomCocone S X Y) := by
  let F : (S / X)ᵒᵖ ⥤ Type (max u v) := rightLocalizationHomDiagram S X Y
  let c : F.CoconeTypes := F.coconeTypesEquiv.symm (rightLocalizationHomCocone S X Y)
  have hc : c.IsColimit := by
    simpa [F, c] using rightLocalizationHomCoconeTypes_isColimit S X Y
  simpa [c] using ((Functor.CoconeTypes.isColimit_iff c).mp hc).some

/-- Remark 4.27.15: the morphisms in the right-fraction localization `S^{-1}\mathcal C` from
`X` to `Y` are canonically the colimit over `(S / X)ᵒᵖ` of the Hom-sets
`\mathrm{Mor}_{\mathcal C}(X', Y)`, where `s : X' ⟶ X` ranges over arrows of `S`. -/
noncomputable def right_localization_hom_colimit
    (S : MorphismProperty C) [S.HasRightCalculusOfFractions] (X Y : C) :
    let F : (S / X)ᵒᵖ ⥤ Type (max u v) :=
      (Over.forget S ⊤ X ⋙ CategoryTheory.Over.forget X).op ⋙
        uliftYoneda.{u}.obj Y
    colimit F ≅ (S.Q.obj X ⟶ S.Q.obj Y) := by
  let F : (S / X)ᵒᵖ ⥤ Type (max u v) := rightLocalizationHomDiagram S X Y
  let c : ColimitCocone F :=
    ⟨rightLocalizationHomCocone S X Y, rightLocalizationHomCocone_isColimit S X Y⟩
  let _ : HasColimit F := HasColimit.mk c
  simpa [F, rightLocalizationHomDiagram] using colimit.isoColimitCocone c

/-- The colimit comparison sends the coprojection indexed by a denominator `s : X' ⟶ X` and a
numerator `f : X' ⟶ Y` to the corresponding right fraction in the localization. -/
-- Proof sketch: unfold `right_localization_hom_colimit` as the canonical isomorphism from
-- `colimit.isoColimitCocone` for `rightLocalizationHomCocone`, then evaluate its `hom` on the
-- coprojection `colimit.ι`.
theorem right_localization_hom_colimit_hom_ι
    (S : MorphismProperty C) [S.HasRightCalculusOfFractions] (X Y : C)
    (U : (S / X)ᵒᵖ)
    (f : (rightLocalizationHomDiagram S X Y).obj U) :
    (right_localization_hom_colimit S X Y).hom
        (colimit.ι (rightLocalizationHomDiagram S X Y) U f) =
      (RightFraction.mk U.unop.hom U.unop.prop f.down).map S.Q (Localization.inverts S.Q S) :=
  by
    let F : (S / X)ᵒᵖ ⥤ Type (max u v) := rightLocalizationHomDiagram S X Y
    let c : ColimitCocone F :=
      ⟨rightLocalizationHomCocone S X Y, rightLocalizationHomCocone_isColimit S X Y⟩
    let _ : HasColimit F := HasColimit.mk c
    -- Evaluate the standard colimit comparison on the summand indexed by `U`.
    have hι : ((colimit.ι F U) ≫ (colimit.isoColimitCocone c).hom) f =
        (c.cocone.ι.app U) f := by
      exact congrFun (colimit.isoColimitCocone_ι_hom c U) f
    -- Unfold the cocone leg to identify the resulting localized morphism with the roof `(f, U)`.
    simpa [F, c, right_localization_hom_colimit, rightLocalizationHomDiagram,
      rightLocalizationHomCocone, rightLocalizationHomCoconeApp] using hι

end MorphismProperty
end CategoryTheory
