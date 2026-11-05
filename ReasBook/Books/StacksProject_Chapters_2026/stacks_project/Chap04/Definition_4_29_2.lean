module

public import Mathlib.CategoryTheory.Bicategory.Functor.StrictPseudofunctor
public import Mathlib.CategoryTheory.Bicategory.Strict.Basic
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import Mathlib.CategoryTheory.Widesubcategory
public import stacks_project.Chap04.Definition_4_2_10

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

namespace CategoryTheory

open Bicategory
open ObjectProperty
open scoped Bicategory

universe w v u

/- Domain-style sampling for Definition 4.29.2:
- primary domain: strict bicategories and source-facing sub-`2`-categories cut out by chosen
  objects, `1`-morphisms, and `2`-morphisms;
- inspected owner-level declarations:
  `Subcategory`,
  `Subcategory.inclusion`,
  `ObjectProperty.FullSubcategory`,
  `WideSubcategory`,
  `wideSubcategoryInclusion`,
  `Bicategory.InducedBicategory.forget`.
- best owner abstraction: `SubTwoCategory C`, with each chosen hom-category expressed by the
  earlier chapter owner `Subcategory (X.obj ⟶ Y.obj)`;
- primitive data: an object property `obj`, a chosen hom-subcategory `hom X Y` for each pair of
  selected objects, and the closure of the selected `1`-morphisms and `2`-morphisms under
  identities, composition, and whiskering;
- derived API: the bundled object type `Obj`, the derived `1`- and `2`-morphism properties
  `hom₁` and `hom₂`, the hom-categories `Hom`, the induced strict bicategory structure on `Obj`,
  and the canonical inclusion `StrictPseudofunctor`.

Source/core/bridge triage:
- `source-facing`: `SubTwoCategory`;
- `core/canonical`: `Subcategory`, `ObjectProperty.FullSubcategory`, `WideSubcategory`, and
  `StrictPseudofunctor`;
- `bridge/view`: the short owner projections `Obj`, `hom₁`, `hom₂`, `Hom`, `Hom.toHom`, and
  `inclusion`. -/

/-- Definition 4.29.2: a sub 2-category of a strict 2-category `C` consists of a subset of
objects, for each chosen pair of objects a subcategory of the corresponding hom category, and
closure of these chosen cells under composition of `1`-morphisms and horizontal whiskering, so
that the chosen data again form a strict `2`-category. -/
structure SubTwoCategory (C : Type u) [Bicategory.{w, v} C] [Strict C] where
  obj : ObjectProperty C
  hom (X Y : obj.FullSubcategory) : Subcategory (X.obj ⟶ Y.obj)
  id_mem (X : obj.FullSubcategory) : (hom X X).obj (𝟙 X.obj)
  comp_mem {X Y Z : obj.FullSubcategory} {f : X.obj ⟶ Y.obj} {g : Y.obj ⟶ Z.obj}
      (hf : (hom X Y).obj f) (hg : (hom Y Z).obj g) : (hom X Z).obj (f ≫ g)
  whiskerLeft_mem {W X Y : obj.FullSubcategory} {k : W.obj ⟶ X.obj} {f g : X.obj ⟶ Y.obj}
      (hk : (hom W X).obj k) (hf : (hom X Y).obj f) (hg : (hom X Y).obj g)
      {η : (⟨f, hf⟩ : (hom X Y).obj.FullSubcategory) ⟶ ⟨g, hg⟩} :
      (hom W Y).hom
        ((homMk (k ◁ η.hom) :
          (⟨k ≫ f, comp_mem hk hf⟩ : (hom W Y).obj.FullSubcategory) ⟶
            ⟨k ≫ g, comp_mem hk hg⟩))
  whiskerRight_mem {X Y Z : obj.FullSubcategory} {f g : X.obj ⟶ Y.obj} {h : Y.obj ⟶ Z.obj}
      (hf : (hom X Y).obj f) (hg : (hom X Y).obj g)
      {η : (⟨f, hf⟩ : (hom X Y).obj.FullSubcategory) ⟶ ⟨g, hg⟩}
      (hh : (hom Y Z).obj h) :
      (hom X Z).hom
        ((homMk (η.hom ▷ h) :
          (⟨f ≫ h, comp_mem hf hh⟩ : (hom X Z).obj.FullSubcategory) ⟶
            ⟨g ≫ h, comp_mem hg hh⟩))

namespace SubTwoCategory

variable {C : Type u} [Bicategory.{w, v} C] [Strict C]

/-- The chosen object type attached to a sub `2`-category `S`. -/
abbrev Obj (S : SubTwoCategory C) :=
  S.obj.FullSubcategory

/-- The chosen `1`-morphism property on each ambient hom-category. -/
abbrev hom₁ (S : SubTwoCategory C) (X Y : S.Obj) : ObjectProperty (X.obj ⟶ Y.obj) :=
  (S.hom X Y).obj

/-- The chosen `2`-morphism property on each selected hom-category. -/
abbrev hom₂ (S : SubTwoCategory C) (X Y : S.Obj) : MorphismProperty ((S.hom₁ X Y).FullSubcategory) :=
  (S.hom X Y).hom

/-- The chosen hom category `Mor_{C'}(X, Y)` attached to a sub `2`-category `S`. -/
abbrev Hom (S : SubTwoCategory C) (X Y : S.Obj) :=
  @WideSubcategory
    ((S.hom₁ X Y).FullSubcategory)
    inferInstance
    (S.hom₂ X Y)
    (S.hom X Y).hom_isMultiplicative

namespace Hom

variable (S : SubTwoCategory C) (X Y : S.Obj)

variable {S X Y}

/-- Build a selected hom from an ambient `1`-morphism satisfying the selected hom property. -/
abbrev mk (f : X.obj ⟶ Y.obj) (hf : (S.hom X Y).obj f) : S.Hom X Y :=
  { obj := { obj := f, property := hf } }

/-- The ambient `1`-morphism underlying an object of a chosen hom category. -/
abbrev toHom (f : S.Hom X Y) : X.obj ⟶ Y.obj :=
  f.obj.obj

@[simp]
theorem toHom_obj (f : S.Hom X Y) :
    f.toHom = f.obj.obj :=
  rfl

/-- Lift an isomorphism of ambient `1`-morphisms to an isomorphism in a chosen hom category,
provided the two `2`-morphisms lie in the selected wide subcategory. -/
noncomputable def isoMk {f g : S.Hom X Y}
    (e : f.toHom ≅ g.toHom)
    (he : (S.hom X Y).hom (ObjectProperty.homMk e.hom))
    (he_inv : (S.hom X Y).hom (ObjectProperty.homMk e.inv)) :
    f ≅ g :=
  { hom := ⟨ObjectProperty.homMk e.hom, he⟩
    inv := ⟨ObjectProperty.homMk e.inv, he_inv⟩ }

@[simp]
theorem eqToHom_hom {f g : S.Hom X Y} (h : f = g) :
    (eqToHom h).hom.hom = eqToHom (congrArg (fun k : S.Hom X Y ↦ k.toHom) h) := by
  subst h
  simp

end Hom

theorem id_comp_eq {S : SubTwoCategory C} {X Y : S.Obj} (f : S.Hom X Y) :
    (⟨⟨𝟙 X.obj ≫ f.toHom, S.comp_mem (S.id_mem X) f.obj.property⟩⟩ : S.Hom X Y) = f := by
  ext
  exact Strict.id_comp f.toHom

theorem comp_id_eq {S : SubTwoCategory C} {X Y : S.Obj} (f : S.Hom X Y) :
    (⟨⟨f.toHom ≫ 𝟙 Y.obj, S.comp_mem f.obj.property (S.id_mem Y)⟩⟩ : S.Hom X Y) = f := by
  ext
  exact Strict.comp_id f.toHom

theorem assoc_eq {S : SubTwoCategory C} {W X Y Z : S.Obj}
    (f : S.Hom W X) (g : S.Hom X Y) (h : S.Hom Y Z) :
    (⟨⟨(f.toHom ≫ g.toHom) ≫ h.toHom,
        S.comp_mem (S.comp_mem f.obj.property g.obj.property) h.obj.property⟩⟩ : S.Hom W Z) =
      ⟨⟨f.toHom ≫ g.toHom ≫ h.toHom,
        S.comp_mem f.obj.property (S.comp_mem g.obj.property h.obj.property)⟩⟩ := by
  ext
  exact Strict.assoc f.toHom g.toHom h.toHom

instance bicategoryObj (S : SubTwoCategory C) : Bicategory S.Obj where
  Hom X Y := S.Hom X Y
  homCategory X Y :=
    @WideSubcategory.category
      ((S.hom₁ X Y).FullSubcategory)
      inferInstance
      (S.hom₂ X Y)
      (S.hom X Y).hom_isMultiplicative
  id X := ⟨⟨𝟙 X.obj, S.id_mem X⟩⟩
  comp f g := ⟨⟨f.toHom ≫ g.toHom, S.comp_mem f.obj.property g.obj.property⟩⟩
  whiskerLeft := by
    intro X Y Z f g h η
    exact {
      hom := homMk (f.toHom ◁ η.hom.hom)
      property := S.whiskerLeft_mem f.obj.property g.obj.property h.obj.property
    }
  whiskerRight := by
    intro X Y Z f g η h
    exact {
      hom := homMk (η.hom.hom ▷ h.toHom)
      property := S.whiskerRight_mem f.obj.property g.obj.property h.obj.property
    }
  associator f g h := eqToIso (assoc_eq f g h)
  leftUnitor f := eqToIso (id_comp_eq f)
  rightUnitor f := eqToIso (comp_id_eq f)
  whiskerLeft_id := by
    intro a b c f g
    ext
    simp
  whiskerLeft_comp := by
    intro a b c f g h i η θ
    ext
    simp
  id_whiskerRight := by
    intro a b c f g
    ext
    simp
  comp_whiskerRight := by
    intro a b c f g h η θ i
    ext
    simp
  id_whiskerLeft := by
    intro a b f g η
    ext
    simp [Strict.leftUnitor_eqToIso]
  comp_whiskerLeft := by
    intro a b c d f g h h' η
    ext
    simp [Strict.associator_eqToIso]
  whiskerRight_id := by
    intro a b f g η
    ext
    simp [Strict.rightUnitor_eqToIso]
  whiskerRight_comp := by
    intro a b c d f f' η g h
    ext
    simp [Strict.associator_eqToIso]
  whisker_assoc := by
    intro a b c d f g g' η h
    ext
    simp [Strict.associator_eqToIso]
  whisker_exchange := by
    intro a b c f g h i η θ
    ext
    simpa using CategoryTheory.Bicategory.whisker_exchange η.hom.hom θ.hom.hom
  pentagon := by
    intro a b c d e f g h i
    ext
    simp
  triangle := by
    intro a b c f g
    ext
    simp

instance strictObj (S : SubTwoCategory C) : Strict S.Obj where
  id_comp := id_comp_eq
  comp_id := comp_id_eq
  assoc := assoc_eq
  leftUnitor_eqToIso _ := rfl
  rightUnitor_eqToIso _ := rfl
  associator_eqToIso _ _ _ := rfl

/-- The canonical inclusion of a sub `2`-category into the ambient strict `2`-category. -/
@[simps!]
def inclusion (S : SubTwoCategory C) : StrictPseudofunctor S.Obj C :=
  StrictPseudofunctor.mk' {
    obj := fun X ↦ X.obj
    map := fun f ↦ f.toHom
    map_id := by
      intro X
      rfl
    map_comp := by
      intro a b c f g
      rfl
    map₂ := fun η ↦ η.hom.hom
    map₂_whisker_left := by
      intro a b c f g g' η
      change f.toHom ◁ η.hom.hom = eqToHom rfl ≫ (f.toHom ◁ η.hom.hom) ≫ eqToHom rfl
      simp
    map₂_whisker_right := by
      intro a b c f f' η g
      change η.hom.hom ▷ g.toHom = eqToHom rfl ≫ (η.hom.hom ▷ g.toHom) ≫ eqToHom rfl
      simp
    map₂_left_unitor := by
      intro a b f
      rw [Strict.leftUnitor_eqToIso, eqToIso.hom, Hom.eqToHom_hom (id_comp_eq f)]
      simp [Strict.leftUnitor_eqToIso]
    map₂_right_unitor := by
      intro a b f
      rw [Strict.rightUnitor_eqToIso, eqToIso.hom, Hom.eqToHom_hom (comp_id_eq f)]
      simp [Strict.rightUnitor_eqToIso]
    map₂_associator := by
      intro a b c d f g h
      rw [Strict.associator_eqToIso, eqToIso.hom, Hom.eqToHom_hom (assoc_eq f g h)]
      simp [Strict.associator_eqToIso]
  }

end SubTwoCategory

end CategoryTheory
