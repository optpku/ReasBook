module

public import Mathlib.CategoryTheory.Bicategory.Functor.StrictPseudofunctor
public import Mathlib.CategoryTheory.Bicategory.Strict.Basic

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

universe w₁ w₂ v₁ v₂ u₁ u₂

namespace CategoryTheory

open Bicategory
open scoped Bicategory

namespace StrictPseudofunctor

/-- Two strict `2`-functors are inverse when they are mutually inverse on objects,
`1`-morphisms, and `2`-morphisms. The morphism identities are expressed using heterogeneous
equality because the inverse-object equalities need not be definitional. -/
structure IsInverse
    {B : Type u₁} [Bicategory.{w₁, v₁} B] [Bicategory.Strict B]
    {C : Type u₂} [Bicategory.{w₂, v₂} C] [Bicategory.Strict C]
    (F : StrictPseudofunctor B C) (G : StrictPseudofunctor C B) : Prop where
  left_obj : ∀ X : B, G.obj (F.obj X) = X
  left_map : ∀ ⦃X Y : B⦄ (f : X ⟶ Y), G.map (F.map f) ≍ f
  left_map₂ : ∀ ⦃X Y : B⦄ {f g : X ⟶ Y} (η : f ⟶ g), G.map₂ (F.map₂ η) ≍ η
  right_obj : ∀ X : C, F.obj (G.obj X) = X
  right_map : ∀ ⦃X Y : C⦄ (f : X ⟶ Y), F.map (G.map f) ≍ f
  right_map₂ : ∀ ⦃X Y : C⦄ {f g : X ⟶ Y} (η : f ⟶ g), F.map₂ (G.map₂ η) ≍ η

end StrictPseudofunctor

variable {B : Type u₁} [Bicategory.{w₁, v₁} B] [Bicategory.Strict B]

/-- The underlying objects of Definition 4.29.6 are the arrows into a fixed object `X` of the
ambient strict `2`-category `B`. -/
@[ext]
structure SliceTwoCategory (X : B) where
  obj : B
  hom : obj ⟶ X

namespace SliceTwoCategory

variable {X : B}

/-- A `1`-morphism in the slice strict `2`-category over `X`. -/
@[ext]
structure Hom (S T : SliceTwoCategory X) where
  hom : S.obj ⟶ T.obj
  comm : hom ≫ T.hom = S.hom

/-- A `2`-morphism in the slice strict `2`-category over `X`. -/
@[ext]
structure TwoHom {S T : SliceTwoCategory X} (F G : Hom S T) where
  hom : F.hom ⟶ G.hom
  comm : hom ▷ T.hom ≫ eqToHom G.comm = eqToHom F.comm

def idHom (S : SliceTwoCategory X) : Hom S S where
  hom := 𝟙 S.obj
  comm := by simp

def compHom {S T U : SliceTwoCategory X} (F : Hom S T) (G : Hom T U) : Hom S U where
  hom := F.hom ≫ G.hom
  comm := by
    simp [Category.assoc, F.comm, G.comm]

def idTwoHom {S T : SliceTwoCategory X} (F : Hom S T) : TwoHom F F where
  hom := 𝟙 F.hom
  comm := by
    simpa using congrArg (fun α ↦ α ≫ eqToHom F.comm) (id_whiskerRight F.hom T.hom)

/-- Helper for Definition 4.29.6: vertical composition of slice `2`-cells still lies over the
identity on the base object. -/
theorem compTwoHom_comm {S T : SliceTwoCategory X} {F G H : Hom S T}
    (η : TwoHom F G) (θ : TwoHom G H) :
    (η.hom ≫ θ.hom) ▷ T.hom ≫ eqToHom H.comm = eqToHom F.comm := by
  -- Vertical composition in the slice is the ambient vertical composition followed by the two
  -- already-known commutativity squares.
  rw [Bicategory.comp_whiskerRight]
  simp [Category.assoc, θ.comm, η.comm]

def compTwoHom {S T : SliceTwoCategory X} {F G H : Hom S T}
    (η : TwoHom F G) (θ : TwoHom G H) : TwoHom F H where
  hom := η.hom ≫ θ.hom
  comm := compTwoHom_comm η θ

instance (S T : SliceTwoCategory X) : Category (Hom S T) where
  Hom F G := TwoHom F G
  id := idTwoHom
  comp := compTwoHom
  id_comp := by
    intro F G η
    -- Equality of slice `2`-cells is detected on the ambient `2`-cell component.
    ext
    simp [compTwoHom, idTwoHom]
  comp_id := by
    intro F G η
    -- The right identity law is the same ambient categorical identity law.
    ext
    simp [compTwoHom, idTwoHom]
  assoc := by
    intro F G H I η θ μ
    -- Associativity is inherited verbatim from the ambient hom-category.
    ext
    simp [compTwoHom, Category.assoc]

/-- Helper for Definition 4.29.6: left whiskering preserves the slice-over-`X` compatibility
condition for `2`-morphisms. -/
theorem whiskerLeftTwoHom_comm {S T U : SliceTwoCategory X} (F : Hom S T) {G H : Hom T U}
    (η : TwoHom G H) :
    (F.hom ◁ η.hom) ▷ U.hom ≫ eqToHom (compHom F H).comm = eqToHom (compHom F G).comm := by
  -- First rewrite right whiskering of a left whisker using the ambient associator, then transport
  -- the defining relation of `η` through left whiskering by `F.hom`.
  calc
    (F.hom ◁ η.hom) ▷ U.hom ≫ eqToHom (compHom F H).comm
        = (α_ F.hom G.hom U.hom).hom ≫ F.hom ◁ (η.hom ▷ U.hom) ≫
            (α_ F.hom H.hom U.hom).inv ≫ eqToHom (compHom F H).comm := by
              simpa [Category.assoc] using Bicategory.whisker_assoc F.hom η.hom U.hom
    _ = (α_ F.hom G.hom U.hom).hom ≫ (F.hom ◁ (η.hom ▷ U.hom) ≫ F.hom ◁ eqToHom H.comm) ≫
          eqToHom F.comm := by
            simp [Category.assoc, Strict.associator_eqToIso]
    _ = (α_ F.hom G.hom U.hom).hom ≫ F.hom ◁ (η.hom ▷ U.hom ≫ eqToHom H.comm) ≫
          eqToHom F.comm := by
            rw [← Bicategory.whiskerLeft_comp]
    _ = (α_ F.hom G.hom U.hom).hom ≫ F.hom ◁ eqToHom G.comm ≫ eqToHom F.comm := by
          exact congrArg (fun β ↦ (α_ F.hom G.hom U.hom).hom ≫ F.hom ◁ β ≫ eqToHom F.comm) η.comm
    _ = eqToHom (compHom F G).comm := by
          simp [compHom, Strict.associator_eqToIso]

def whiskerLeftTwoHom {S T U : SliceTwoCategory X} (F : Hom S T) {G H : Hom T U}
    (η : TwoHom G H) : TwoHom (compHom F G) (compHom F H) where
  hom := F.hom ◁ η.hom
  comm := whiskerLeftTwoHom_comm F η

/-- Helper for Definition 4.29.6: right whiskering preserves the slice-over-`X` compatibility
condition for `2`-morphisms. -/
theorem whiskerRightTwoHom_comm {S T U : SliceTwoCategory X} {F G : Hom S T}
    (η : TwoHom F G) (H : Hom T U) :
    η.hom ▷ H.hom ▷ U.hom ≫ eqToHom (compHom G H).comm = eqToHom (compHom F H).comm := by
  -- Reassociate to the right-whiskered normal form, use the slice relation for `η`, and then
  -- collapse the ambient associators back to the target slice equality.
  calc
    η.hom ▷ H.hom ▷ U.hom ≫ eqToHom (compHom G H).comm
        = η.hom ▷ H.hom ▷ U.hom ≫ (α_ G.hom H.hom U.hom).hom ≫
            G.hom ◁ eqToHom H.comm ≫ eqToHom G.comm := by
              simp [Strict.associator_eqToIso]
    _ = (α_ F.hom H.hom U.hom).hom ≫ η.hom ▷ (H.hom ≫ U.hom) ≫
          G.hom ◁ eqToHom H.comm ≫ eqToHom G.comm := by
            rw [associator_naturality_left_assoc]
    _ = (α_ F.hom H.hom U.hom).hom ≫ (F.hom ◁ eqToHom H.comm ≫ η.hom ▷ T.hom) ≫
          eqToHom G.comm := by
            rw [← whisker_exchange_assoc]
            simp [Category.assoc]
    _ = (α_ F.hom H.hom U.hom).hom ≫ F.hom ◁ eqToHom H.comm ≫ eqToHom F.comm := by
          simpa [Category.assoc] using
            congrArg (fun α ↦ (α_ F.hom H.hom U.hom).hom ≫ F.hom ◁ eqToHom H.comm ≫ α) η.comm
    _ = eqToHom (compHom F H).comm := by
          simp [compHom, Strict.associator_eqToIso]

def whiskerRightTwoHom {S T U : SliceTwoCategory X} {F G : Hom S T}
    (η : TwoHom F G) (H : Hom T U) : TwoHom (compHom F H) (compHom G H) where
  hom := η.hom ▷ H.hom
  comm := whiskerRightTwoHom_comm η H

/-- Helper for Definition 4.29.6: the ambient associator `2`-cell is compatible with the slice
triangle over `X`. -/
theorem associatorIso_hom_comm {R S T U : SliceTwoCategory X}
    (F : Hom R S) (G : Hom S T) (H : Hom T U) :
    (α_ F.hom G.hom H.hom).hom ▷ U.hom ≫ eqToHom (compHom F (compHom G H)).comm =
      eqToHom (compHom (compHom F G) H).comm := by
  -- The slice associator is exactly the ambient associator on the underlying arrows.
  simp [compHom, Strict.associator_eqToIso]

/-- Helper for Definition 4.29.6: the inverse ambient associator `2`-cell is compatible with the
slice triangle over `X`. -/
theorem associatorIso_inv_comm {R S T U : SliceTwoCategory X}
    (F : Hom R S) (G : Hom S T) (H : Hom T U) :
    (α_ F.hom G.hom H.hom).inv ▷ U.hom ≫ eqToHom (compHom (compHom F G) H).comm =
      eqToHom (compHom F (compHom G H)).comm := by
  -- The inverse associator satisfies the same compatibility relation.
  simp [compHom, Strict.associator_eqToIso]

/-- Helper for Definition 4.29.6: the forward slice associator `2`-cell. -/
def associatorTwoHom {R S T U : SliceTwoCategory X}
    (F : Hom R S) (G : Hom S T) (H : Hom T U) :
    TwoHom (compHom (compHom F G) H) (compHom F (compHom G H)) :=
  { hom := (α_ F.hom G.hom H.hom).hom
    comm := associatorIso_hom_comm F G H }

/-- Helper for Definition 4.29.6: the inverse slice associator `2`-cell. -/
def associatorInvTwoHom {R S T U : SliceTwoCategory X}
    (F : Hom R S) (G : Hom S T) (H : Hom T U) :
    TwoHom (compHom F (compHom G H)) (compHom (compHom F G) H) :=
  { hom := (α_ F.hom G.hom H.hom).inv
    comm := associatorIso_inv_comm F G H }

/-- Helper for Definition 4.29.6: the slice associator has the expected ambient inverse law on
its `hom` component. -/
theorem associatorIso_hom_inv_id {R S T U : SliceTwoCategory X}
    (F : Hom R S) (G : Hom S T) (H : Hom T U) :
    associatorTwoHom F G H ≫ associatorInvTwoHom F G H =
      𝟙 (compHom (compHom F G) H) := by
  -- Equality of slice `2`-cells is detected on the ambient `2`-cell component.
  apply TwoHom.ext
  change (α_ F.hom G.hom H.hom).hom ≫ (α_ F.hom G.hom H.hom).inv =
      𝟙 ((compHom (compHom F G) H).hom)
  simpa [compHom] using Iso.hom_inv_id (α_ F.hom G.hom H.hom)

/-- Helper for Definition 4.29.6: the slice associator has the expected ambient inverse law on
its `inv` component. -/
theorem associatorIso_inv_hom_id {R S T U : SliceTwoCategory X}
    (F : Hom R S) (G : Hom S T) (H : Hom T U) :
    associatorInvTwoHom F G H ≫ associatorTwoHom F G H =
      𝟙 (compHom F (compHom G H)) := by
  -- The opposite inverse law is the same ambient inverse identity.
  apply TwoHom.ext
  change (α_ F.hom G.hom H.hom).inv ≫ (α_ F.hom G.hom H.hom).hom =
      𝟙 ((compHom F (compHom G H)).hom)
  simpa [compHom] using Iso.inv_hom_id (α_ F.hom G.hom H.hom)

def associatorIso {R S T U : SliceTwoCategory X}
    (F : Hom R S) (G : Hom S T) (H : Hom T U) :
    compHom (compHom F G) H ≅ compHom F (compHom G H) where
  hom := associatorTwoHom F G H
  inv := associatorInvTwoHom F G H
  hom_inv_id := associatorIso_hom_inv_id F G H
  inv_hom_id := associatorIso_inv_hom_id F G H

/-- Helper for Definition 4.29.6: the ambient left unitor is compatible with the slice triangle
over `X`. -/
theorem leftUnitorIso_hom_comm {S T : SliceTwoCategory X} (F : Hom S T) :
    (λ_ F.hom).hom ▷ T.hom ≫ eqToHom F.comm = eqToHom (compHom (idHom S) F).comm := by
  -- The slice left unitor is inherited from the ambient left unitor.
  simp [idHom, compHom, Strict.leftUnitor_eqToIso]

/-- Helper for Definition 4.29.6: the inverse ambient left unitor is compatible with the slice
triangle over `X`. -/
theorem leftUnitorIso_inv_comm {S T : SliceTwoCategory X} (F : Hom S T) :
    (λ_ F.hom).inv ▷ T.hom ≫ eqToHom (compHom (idHom S) F).comm = eqToHom F.comm := by
  -- The inverse left unitor satisfies the same compatibility relation.
  simp [Strict.leftUnitor_eqToIso]

/-- Helper for Definition 4.29.6: the forward slice left unitor `2`-cell. -/
def leftUnitorTwoHom {S T : SliceTwoCategory X} (F : Hom S T) :
    TwoHom (compHom (idHom S) F) F :=
  { hom := (λ_ F.hom).hom
    comm := leftUnitorIso_hom_comm F }

/-- Helper for Definition 4.29.6: the inverse slice left unitor `2`-cell. -/
def leftUnitorInvTwoHom {S T : SliceTwoCategory X} (F : Hom S T) :
    TwoHom F (compHom (idHom S) F) :=
  { hom := (λ_ F.hom).inv
    comm := leftUnitorIso_inv_comm F }

/-- Helper for Definition 4.29.6: the slice left unitor satisfies the ambient inverse law on its
`hom` component. -/
theorem leftUnitorIso_hom_inv_id {S T : SliceTwoCategory X} (F : Hom S T) :
    leftUnitorTwoHom F ≫ leftUnitorInvTwoHom F =
      𝟙 (compHom (idHom S) F) := by
  -- Equality of slice `2`-cells is detected on the ambient `2`-cell component.
  apply TwoHom.ext
  change (λ_ F.hom).hom ≫ (λ_ F.hom).inv = 𝟙 ((compHom (idHom S) F).hom)
  simpa [idHom, compHom] using Iso.hom_inv_id (λ_ F.hom)

/-- Helper for Definition 4.29.6: the slice left unitor satisfies the ambient inverse law on its
`inv` component. -/
theorem leftUnitorIso_inv_hom_id {S T : SliceTwoCategory X} (F : Hom S T) :
    leftUnitorInvTwoHom F ≫ leftUnitorTwoHom F =
      𝟙 F := by
  -- The opposite inverse law is the same ambient inverse identity.
  apply TwoHom.ext
  change (λ_ F.hom).inv ≫ (λ_ F.hom).hom = 𝟙 F.hom
  simpa [Strict.leftUnitor_eqToIso] using Iso.inv_hom_id (λ_ F.hom)

def leftUnitorIso {S T : SliceTwoCategory X} (F : Hom S T) :
    compHom (idHom S) F ≅ F where
  hom := leftUnitorTwoHom F
  inv := leftUnitorInvTwoHom F
  hom_inv_id := leftUnitorIso_hom_inv_id F
  inv_hom_id := leftUnitorIso_inv_hom_id F

/-- Helper for Definition 4.29.6: the ambient right unitor is compatible with the slice triangle
over `X`. -/
theorem rightUnitorIso_hom_comm {S T : SliceTwoCategory X} (F : Hom S T) :
    (ρ_ F.hom).hom ▷ T.hom ≫ eqToHom F.comm = eqToHom (compHom F (idHom T)).comm := by
  -- The slice right unitor is inherited from the ambient right unitor.
  simp [idHom, compHom, Strict.rightUnitor_eqToIso]

/-- Helper for Definition 4.29.6: the inverse ambient right unitor is compatible with the slice
triangle over `X`. -/
theorem rightUnitorIso_inv_comm {S T : SliceTwoCategory X} (F : Hom S T) :
    (ρ_ F.hom).inv ▷ T.hom ≫ eqToHom (compHom F (idHom T)).comm = eqToHom F.comm := by
  -- The inverse right unitor satisfies the same compatibility relation.
  simp [Strict.rightUnitor_eqToIso]

/-- Helper for Definition 4.29.6: the forward slice right unitor `2`-cell. -/
def rightUnitorTwoHom {S T : SliceTwoCategory X} (F : Hom S T) :
    TwoHom (compHom F (idHom T)) F :=
  { hom := (ρ_ F.hom).hom
    comm := rightUnitorIso_hom_comm F }

/-- Helper for Definition 4.29.6: the inverse slice right unitor `2`-cell. -/
def rightUnitorInvTwoHom {S T : SliceTwoCategory X} (F : Hom S T) :
    TwoHom F (compHom F (idHom T)) :=
  { hom := (ρ_ F.hom).inv
    comm := rightUnitorIso_inv_comm F }

/-- Helper for Definition 4.29.6: the slice right unitor satisfies the ambient inverse law on its
`hom` component. -/
theorem rightUnitorIso_hom_inv_id {S T : SliceTwoCategory X} (F : Hom S T) :
    rightUnitorTwoHom F ≫ rightUnitorInvTwoHom F =
      𝟙 (compHom F (idHom T)) := by
  -- Equality of slice `2`-cells is detected on the ambient `2`-cell component.
  apply TwoHom.ext
  change (ρ_ F.hom).hom ≫ (ρ_ F.hom).inv = 𝟙 ((compHom F (idHom T)).hom)
  simpa [idHom, compHom] using Iso.hom_inv_id (ρ_ F.hom)

/-- Helper for Definition 4.29.6: the slice right unitor satisfies the ambient inverse law on its
`inv` component. -/
theorem rightUnitorIso_inv_hom_id {S T : SliceTwoCategory X} (F : Hom S T) :
    rightUnitorInvTwoHom F ≫ rightUnitorTwoHom F =
      𝟙 F := by
  -- The opposite inverse law is the same ambient inverse identity.
  apply TwoHom.ext
  change (ρ_ F.hom).inv ≫ (ρ_ F.hom).hom = 𝟙 F.hom
  simpa [Strict.rightUnitor_eqToIso] using Iso.inv_hom_id (ρ_ F.hom)

def rightUnitorIso {S T : SliceTwoCategory X} (F : Hom S T) :
    compHom F (idHom T) ≅ F where
  hom := rightUnitorTwoHom F
  inv := rightUnitorInvTwoHom F
  hom_inv_id := rightUnitorIso_hom_inv_id F
  inv_hom_id := rightUnitorIso_inv_hom_id F

instance instBicategory : Bicategory (SliceTwoCategory X) where
  Hom S T := Hom S T
  homCategory S T := inferInstance
  id := idHom
  comp := compHom
  whiskerLeft := whiskerLeftTwoHom
  whiskerRight := whiskerRightTwoHom
  associator := associatorIso
  leftUnitor := leftUnitorIso
  rightUnitor := rightUnitorIso
  whisker_exchange := by
    intro R S T F G H I η θ
    -- The exchange law is inherited verbatim from the ambient bicategory on underlying arrows.
    apply TwoHom.ext
    change F.hom ◁ θ.hom ≫ η.hom ▷ I.hom = η.hom ▷ H.hom ≫ G.hom ◁ θ.hom
    simpa using CategoryTheory.Bicategory.whisker_exchange η.hom θ.hom
  whiskerLeft_id := by
    intro R S T F G
    -- Left whiskering preserves identity `2`-cells componentwise.
    apply TwoHom.ext
    change F.hom ◁ 𝟙 G.hom = 𝟙 ((compHom F G).hom)
    simpa [whiskerLeftTwoHom, compHom, idTwoHom] using Bicategory.whiskerLeft_id F.hom G.hom
  whiskerLeft_comp := by
    intro R S T F G H I η θ
    -- Left whiskering preserves vertical composition on the underlying ambient `2`-cell.
    apply TwoHom.ext
    change F.hom ◁ (η.hom ≫ θ.hom) = (F.hom ◁ η.hom) ≫ F.hom ◁ θ.hom
    simpa [whiskerLeftTwoHom, compTwoHom] using Bicategory.whiskerLeft_comp F.hom η.hom θ.hom
  id_whiskerLeft := by
    intro S T F G η
    -- The slice left whiskering by an identity reduces to the ambient left-unitor law.
    apply TwoHom.ext
    change (𝟙 S.obj ◁ η.hom) = (λ_ F.hom).hom ≫ η.hom ≫ (λ_ G.hom).inv
    simpa [whiskerLeftTwoHom, idHom, compHom] using Bicategory.id_whiskerLeft η.hom
  comp_whiskerLeft := by
    intro R S T U F G H H' η
    -- Left whiskering by a composite is inherited componentwise from the ambient bicategory.
    apply TwoHom.ext
    change (F.hom ≫ G.hom) ◁ η.hom =
      (α_ F.hom G.hom H.hom).hom ≫ F.hom ◁ (G.hom ◁ η.hom) ≫
        (α_ F.hom G.hom H'.hom).inv
    simpa [whiskerLeftTwoHom, compHom] using Bicategory.comp_whiskerLeft F.hom G.hom η.hom
  id_whiskerRight := by
    intro R S T F G
    -- Right whiskering preserves identity `2`-cells componentwise.
    apply TwoHom.ext
    change 𝟙 F.hom ▷ G.hom = 𝟙 ((compHom F G).hom)
    simpa [whiskerRightTwoHom, compHom, idTwoHom] using Bicategory.id_whiskerRight F.hom G.hom
  comp_whiskerRight := by
    intro R S T F G H η θ I
    -- Right whiskering preserves vertical composition on the underlying ambient `2`-cell.
    apply TwoHom.ext
    change (η.hom ≫ θ.hom) ▷ I.hom = η.hom ▷ I.hom ≫ θ.hom ▷ I.hom
    simpa [whiskerRightTwoHom, compTwoHom] using Bicategory.comp_whiskerRight η.hom θ.hom I.hom
  whiskerRight_id := by
    intro S T F G η
    -- The slice right whiskering by an identity reduces to the ambient right-unitor law.
    apply TwoHom.ext
    change η.hom ▷ 𝟙 T.obj = (ρ_ F.hom).hom ≫ η.hom ≫ (ρ_ G.hom).inv
    simpa [whiskerRightTwoHom, idHom, compHom] using Bicategory.whiskerRight_id η.hom
  whiskerRight_comp := by
    intro R S T U F F' η G H
    -- Right whiskering by a composite is inherited componentwise from the ambient bicategory.
    apply TwoHom.ext
    change η.hom ▷ (G.hom ≫ H.hom) =
      (α_ F.hom G.hom H.hom).inv ≫ (η.hom ▷ G.hom) ▷ H.hom ≫
        (α_ F'.hom G.hom H.hom).hom
    simpa [whiskerRightTwoHom, compHom] using Bicategory.whiskerRight_comp η.hom G.hom H.hom
  whisker_assoc := by
    intro R S T U F G G' η H
    -- Compatibility of left and right whiskering is inherited from the ambient bicategory.
    apply TwoHom.ext
    change (F.hom ◁ η.hom) ▷ H.hom =
      (α_ F.hom G.hom H.hom).hom ≫ F.hom ◁ (η.hom ▷ H.hom) ≫
        (α_ F.hom G'.hom H.hom).inv
    simpa [whiskerLeftTwoHom, whiskerRightTwoHom, compHom] using
      Bicategory.whisker_assoc F.hom η.hom H.hom
  pentagon := by
    intro Q R S T U F G H I
    -- The pentagon coherence law reduces to the ambient one on underlying arrows.
    apply TwoHom.ext
    change (α_ F.hom G.hom H.hom).hom ▷ I.hom ≫
        (α_ F.hom (G.hom ≫ H.hom) I.hom).hom ≫ F.hom ◁ (α_ G.hom H.hom I.hom).hom =
      (α_ (F.hom ≫ G.hom) H.hom I.hom).hom ≫ (α_ F.hom G.hom (H.hom ≫ I.hom)).hom
    simpa [compHom] using Bicategory.pentagon F.hom G.hom H.hom I.hom
  triangle := by
    intro R S T F G
    -- The triangle coherence law is likewise inherited from the ambient bicategory.
    apply TwoHom.ext
    change (α_ F.hom (𝟙 S.obj) G.hom).hom ≫ F.hom ◁ (λ_ G.hom).hom =
      (ρ_ F.hom).hom ▷ G.hom
    simpa [whiskerLeftTwoHom, whiskerRightTwoHom, idHom, compHom] using
      Bicategory.triangle F.hom G.hom

/-- Helper for Definition 4.29.6: the ambient `2`-cell component of `eqToHom` between slice
`1`-morphisms is the `eqToHom` of the induced equality on underlying arrows. -/
private theorem eqToHom_hom_component {S T : SliceTwoCategory X} {F G : Hom S T} (h : F = G) :
    (eqToHom h).hom = eqToHom (congrArg Hom.hom h) := by
  cases h
  rfl

/-- Helper for Definition 4.29.6: slice composition with an identity on the left is strictly
unital. -/
private theorem strict_id_comp_hom {S T : SliceTwoCategory X} (F : Hom S T) :
    𝟙 S ≫ F = F := by
  -- Equality of slice `1`-morphisms is detected on the underlying ambient arrow.
  apply Hom.ext
  change 𝟙 S.obj ≫ F.hom = F.hom
  exact Strict.id_comp F.hom

/-- Helper for Definition 4.29.6: slice composition with an identity on the right is strictly
unital. -/
private theorem strict_comp_id_hom {S T : SliceTwoCategory X} (F : Hom S T) :
    F ≫ 𝟙 T = F := by
  -- Equality of slice `1`-morphisms is detected on the underlying ambient arrow.
  apply Hom.ext
  change F.hom ≫ 𝟙 T.obj = F.hom
  exact Strict.comp_id F.hom

/-- Helper for Definition 4.29.6: slice composition is strictly associative on underlying
arrows. -/
private theorem strict_assoc_hom {R S T U : SliceTwoCategory X}
    (F : Hom R S) (G : Hom S T) (H : Hom T U) :
    compHom (compHom F G) H = compHom F (compHom G H) := by
  -- Equality of slice `1`-morphisms is detected on the underlying ambient arrow.
  apply Hom.ext
  change (F.hom ≫ G.hom) ≫ H.hom = F.hom ≫ G.hom ≫ H.hom
  exact Strict.assoc F.hom G.hom H.hom

/-- The slice over `X` inherits a canonical strict `2`-category structure from the ambient strict
`2`-category `B`. -/
instance instStrict : Bicategory.Strict (SliceTwoCategory X) where
  id_comp := by
    intro S T F
    -- Reuse the strict left-unital slice equality proved just above.
    exact strict_id_comp_hom F
  comp_id := by
    intro S T F
    -- Reuse the strict right-unital slice equality proved just above.
    exact strict_comp_id_hom F
  assoc := by
    intro R S T U F G H
    -- Reuse the strict associativity equality proved just above.
    change compHom (compHom F G) H = compHom F (compHom G H)
    exact strict_assoc_hom F G H
  leftUnitor_eqToIso := by
    intro S T F
    -- Compare the slice isomorphisms on the underlying ambient `2`-cell component.
    apply Iso.ext
    apply TwoHom.ext
    have hhom : congrArg Hom.hom (strict_id_comp_hom F) = Strict.id_comp F.hom := by
      exact Subsingleton.elim _ _
    rw [eqToIso.hom, eqToHom_hom_component, hhom]
    simpa using congrArg Iso.hom (Strict.leftUnitor_eqToIso F.hom)
  rightUnitor_eqToIso := by
    intro S T F
    -- Compare the slice isomorphisms on the underlying ambient `2`-cell component.
    apply Iso.ext
    apply TwoHom.ext
    have hhom : congrArg Hom.hom (strict_comp_id_hom F) = Strict.comp_id F.hom := by
      exact Subsingleton.elim _ _
    rw [eqToIso.hom, eqToHom_hom_component, hhom]
    simpa using congrArg Iso.hom (Strict.rightUnitor_eqToIso F.hom)
  associator_eqToIso := by
    intro Q R S T F G H
    -- Compare the slice isomorphisms on the underlying ambient `2`-cell component.
    apply Iso.ext
    apply TwoHom.ext
    have hhom :
        congrArg Hom.hom (strict_assoc_hom F G H) = Strict.assoc F.hom G.hom H.hom := by
      exact Subsingleton.elim _ _
    rw [eqToIso.hom, eqToHom_hom_component]
    change (α_ F G H).hom.hom = eqToHom (congrArg Hom.hom (strict_assoc_hom F G H))
    rw [hhom]
    simpa using congrArg Iso.hom (Strict.associator_eqToIso F.hom G.hom H.hom)

end SliceTwoCategory

end CategoryTheory
