module

public import stacks_project.Chap04.Definition_4_31_1
public import Mathlib.CategoryTheory.Bicategory.Extension
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Categorical.Basic

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

universe w v u

namespace CategoryTheory

open Bicategory
open scoped Bicategory

variable {B : Type u} [Bicategory.{w, v} B]
variable {x y z : B} (f : x ⟶ z) (g : y ⟶ z)

/- Domain-style sampling for Definition 4.31.2:
- `Bicategory.IsFinal` from Definition `4.31.1` is the canonical owner abstraction for the
  universal property of a `2`-fibre product square.
- `LeftLift` from mathlib is the canonical owner for the lower-triangle data and for the ordinary
  morphism category on the apex maps.
- `Bicategory.IsLocallyGroupoid` from Definition `4.30.1` is only bridge-level input: in the
  source `(2,1)` setting it upgrades those ordinary ambient `2`-morphisms to invertible ones; it
  should not be hardwired into the square owner itself.
- The categorical prototype is `CategoricalPullback.CatCommSqOver`, where the primitive data are a
  commutative square and the pullback universal property is derived API.

Primitive-vs-derived split:
- primitive data: the apex object, the two projection `1`-morphisms, and the invertible
  comparison `2`-morphism.
- derived API: the bicategory structure on squares with ordinary ambient `2`-morphisms in each
  hom-category, the inherited local-groupoid instance, and the
  existence-and-uniqueness reformulation of finality available in the `(2,1)` setting. -/

/- Source/core/bridge triage for Definition 4.31.2:
- `source-facing`: the square data `BicategoricalTwoCommutativeSquare f g`.
- `core/canonical`: for `P : BicategoricalTwoCommutativeSquare f g`, the universal property
  `Bicategory.IsFinal P`.
- `bridge/view`: the inherited `(2,1)`-category specialization, already owned upstream by
  `Bicategory.isFinal_iff_existsUnique_hom₂`. -/

/-- A `2`-commutative square over a bicategorical cospan `x ⟶ z ← y`. -/
@[ext]
structure BicategoricalTwoCommutativeSquare where
  /-- The apex object of the square. -/
  obj : B
  /-- The projection to the left object. -/
  p : obj ⟶ x
  /-- The projection to the right object. -/
  q : obj ⟶ y
  /-- The invertible `2`-morphism witnessing `2`-commutativity. -/
  ψ : p ≫ f ≅ q ≫ g

namespace BicategoricalTwoCommutativeSquare

variable {x y z : B} {f : x ⟶ z} {g : y ⟶ z}

/-- Swap the two legs of a `2`-commutative square. -/
@[simps]
def symm (S : BicategoricalTwoCommutativeSquare f g) :
    BicategoricalTwoCommutativeSquare g f where
  obj := S.obj
  p := S.q
  q := S.p
  ψ := S.ψ.symm

/-- The symmetry operation on `2`-commutative squares is involutive. -/
@[simp] theorem symm_symm (S : BicategoricalTwoCommutativeSquare f g) :
    S.symm.symm = S := by
  cases S
  rfl

/-- The lower triangle of a `2`-commutative square, viewed as the canonical left-lift owner. -/
abbrev toLeftLift (S : BicategoricalTwoCommutativeSquare f g) :
    LeftLift f (S.q ≫ g) :=
  LeftLift.mk S.p S.ψ.inv

noncomputable instance (S : BicategoricalTwoCommutativeSquare f g) :
    IsIso S.toLeftLift.unit := by
  change IsIso S.ψ.inv
  infer_instance

end BicategoricalTwoCommutativeSquare

namespace Limits.CategoricalPullback.CatCommSqOver

universe vCat uCat

variable {X : Type uCat} [Category.{vCat} X]
variable {A : Type uCat} [Category.{vCat} A]
variable {B' : Type uCat} [Category.{vCat} B']
variable {C : Type uCat} [Category.{vCat} C]

/-- A categorical commutative square over `F` and `G`, viewed in the chapter's bicategorical
owner of `2`-commutative squares in `Cat`. -/
abbrev toBicategoricalSquare
    {F : A ⥤ C} {G : B' ⥤ C}
    (P : CatCommSqOver F G X) :
    BicategoricalTwoCommutativeSquare F.toCatHom G.toCatHom where
  obj := Cat.of X
  p := P.fst.toCatHom
  q := P.snd.toCatHom
  ψ := Cat.Hom.isoMk P.iso

end Limits.CategoricalPullback.CatCommSqOver

namespace BicategoricalTwoCommutativeSquare

variable {x y z : B} {f : x ⟶ z} {g : y ⟶ z}

local notation "Square" => BicategoricalTwoCommutativeSquare f g

section

variable {S S₁ S₂ S₃ : Square}

/-- A `1`-morphism between `2`-commutative squares over the fixed cospan `x ⟶ z ← y`.
The leg comparison cells are intentionally oriented toward the source square: this is the
cone-morphism direction used by the final-object universal property of a `2`-fibre product. -/
@[ext]
structure Hom (S₁ S₂ : Square) where
  /-- The map between the apex objects. -/
  hom : S₁.obj ⟶ S₂.obj
  /-- The comparison `2`-morphism on the left leg, oriented toward the source cone. -/
  left : hom ≫ S₂.p ⟶ S₁.p
  /-- The comparison `2`-morphism on the right leg, oriented toward the source cone. -/
  right : hom ≫ S₂.q ⟶ S₁.q
  /-- Compatibility with the chosen `2`-commutativity witnesses. -/
  comm :
    (left ▷ f) ≫ S₁.ψ.hom =
      (α_ hom S₂.p f).hom ≫ hom ◁ S₂.ψ.hom ≫ (α_ hom S₂.q g).inv ≫ (right ▷ g)

/-- A `2`-morphism between morphisms of `2`-commutative squares. -/
@[ext]
structure TwoHom
    {S₁ S₂ : Square}
    (u v : Hom S₁ S₂) where
  /-- The ambient `2`-morphism between the apex maps. -/
  hom : u.hom ⟶ v.hom
  /-- Compatibility with the left-leg comparison `2`-morphisms. -/
  left_comm : (hom ▷ S₂.p) ≫ v.left = u.left
  /-- Compatibility with the right-leg comparison `2`-morphisms. -/
  right_comm : (hom ▷ S₂.q) ≫ v.right = u.right

def idHom (S : Square) :
    Hom S S where
  hom := 𝟙 S.obj
  left := (λ_ S.p).hom
  right := (λ_ S.q).hom
  comm := by
    -- The identity square condition is exactly the ambient left-unitor whiskering formula.
    simpa using (Bicategory.id_whiskerLeft (η := S.ψ.hom)).symm

def compHom
    {S₁ S₂ S₃ : Square}
    (u : Hom S₁ S₂)
    (v : Hom S₂ S₃) :
    Hom S₁ S₃ where
  hom := u.hom ≫ v.hom
  left := (α_ u.hom v.hom S₃.p).hom ≫ u.hom ◁ v.left ≫ u.left
  right := (α_ u.hom v.hom S₃.q).hom ≫ u.hom ◁ v.right ≫ u.right
  comm := by
    -- Route correction: first rewrite the outer square relation `u.comm`, then whisker `v.comm`
    -- through `u.hom`; the remaining associator bookkeeping is pure ambient bicategory coherence.
    simp only [comp_whiskerRight, Category.assoc]
    rw [u.comm]
    have hv :
        (u.hom ◁ v.left) ▷ f ≫ (α_ u.hom S₂.p f).hom ≫ u.hom ◁ S₂.ψ.hom =
          (α_ u.hom (v.hom ≫ S₃.p) f).hom ≫
            u.hom ◁
              ((α_ v.hom S₃.p f).hom ≫ v.hom ◁ S₃.ψ.hom ≫
                (α_ v.hom S₃.q g).inv ≫ v.right ▷ g) := by
      -- Transport the middle square relation through left whiskering by `u.hom`, then align the
      -- resulting source with the displayed composite-leg parenthesization.
      rw [associator_naturality_middle_assoc]
      simpa [Category.assoc] using congrArg (fun β ↦ u.hom ◁ β) v.comm
    have hv' :=
      congrArg
        (fun α ↦
          (α_ u.hom v.hom S₃.p).hom ▷ f ≫ α ≫ (α_ u.hom S₂.q g).inv ≫ u.right ▷ g)
        hv
    simpa [Category.assoc] using hv'

def idHom₂
    {S₁ S₂ : Square}
    (u : Hom S₁ S₂) :
    TwoHom u u where
  hom := 𝟙 u.hom
  left_comm := by
    -- Identity `2`-cells act trivially on the left leg.
    simp
  right_comm := by
    -- Identity `2`-cells act trivially on the right leg.
    simp

def compHom₂
    {S₁ S₂ : Square}
    {u v w : Hom S₁ S₂}
    (η : TwoHom u v)
    (θ : TwoHom v w) :
    TwoHom u w where
  hom := η.hom ≫ θ.hom
  left_comm := by
    -- Vertical composition preserves the left-leg compatibility by associativity.
    simpa [Category.assoc, η.left_comm, θ.left_comm]
  right_comm := by
    -- Vertical composition preserves the right-leg compatibility by associativity.
    simpa [Category.assoc, η.right_comm, θ.right_comm]

def whiskerLeftTwoHom
    {S₁ S₂ S₃ : Square}
    (u : Hom S₁ S₂)
    {v w : Hom S₂ S₃}
    (η : TwoHom v w) :
    TwoHom (compHom u v) (compHom u w) where
  hom := u.hom ◁ η.hom
  left_comm := by
    -- Transport the left leg relation through left whiskering and then reattach `u.left`.
    simpa [compHom, Category.assoc] using
      (show
        ((u.hom ◁ η.hom ▷ S₃.p ≫ u.hom ◁ w.left) ≫ u.left =
          u.hom ◁ v.left ≫ u.left) from
        congrArg (fun α ↦ α ≫ u.left)
          (by
            simpa [Category.assoc] using congrArg (fun β ↦ u.hom ◁ β) η.left_comm))
  right_comm := by
    -- The right leg is the same transport calculation with `q`.
    simpa [compHom, Category.assoc] using
      (show
        ((u.hom ◁ η.hom ▷ S₃.q ≫ u.hom ◁ w.right) ≫ u.right =
          u.hom ◁ v.right ≫ u.right) from
        congrArg (fun α ↦ α ≫ u.right)
          (by
            simpa [Category.assoc] using congrArg (fun β ↦ u.hom ◁ β) η.right_comm))

def whiskerRightTwoHom
    {S₁ S₂ S₃ : Square}
    {u v : Hom S₁ S₂}
    (η : TwoHom u v)
    (w : Hom S₂ S₃) :
    TwoHom (compHom u w) (compHom v w) where
  hom := η.hom ▷ w.hom
  left_comm := by
    -- Reassociate to the final displayed left-leg shape, commute the whiskers, and substitute
    -- the square relation `η.left_comm`.
    calc
      η.hom ▷ w.hom ▷ S₃.p ≫ (compHom v w).left
          = η.hom ▷ w.hom ▷ S₃.p ≫ (α_ v.hom w.hom S₃.p).hom ≫ v.hom ◁ w.left ≫ v.left := by
              simp [compHom, Category.assoc]
      _ = (α_ u.hom w.hom S₃.p).hom ≫ η.hom ▷ (w.hom ≫ S₃.p) ≫ v.hom ◁ w.left ≫ v.left := by
            rw [associator_naturality_left_assoc]
      _ = (α_ u.hom w.hom S₃.p).hom ≫ (u.hom ◁ w.left ≫ η.hom ▷ S₂.p) ≫ v.left := by
            rw [← whisker_exchange_assoc]
            simp [Category.assoc]
      _ = (α_ u.hom w.hom S₃.p).hom ≫ u.hom ◁ w.left ≫ u.left := by
            rw [Category.assoc, η.left_comm]
      _ = (compHom u w).left := by
            simp [compHom, Category.assoc]
  right_comm := by
    -- The right leg follows from the same ambient reassociation with `q`.
    calc
      η.hom ▷ w.hom ▷ S₃.q ≫ (compHom v w).right
          = η.hom ▷ w.hom ▷ S₃.q ≫ (α_ v.hom w.hom S₃.q).hom ≫ v.hom ◁ w.right ≫ v.right := by
              simp [compHom, Category.assoc]
      _ = (α_ u.hom w.hom S₃.q).hom ≫ η.hom ▷ (w.hom ≫ S₃.q) ≫ v.hom ◁ w.right ≫ v.right := by
            rw [associator_naturality_left_assoc]
      _ = (α_ u.hom w.hom S₃.q).hom ≫ (u.hom ◁ w.right ≫ η.hom ▷ S₂.q) ≫ v.right := by
            rw [← whisker_exchange_assoc]
            simp [Category.assoc]
      _ = (α_ u.hom w.hom S₃.q).hom ≫ u.hom ◁ w.right ≫ u.right := by
            rw [Category.assoc, η.right_comm]
      _ = (compHom u w).right := by
            simp [compHom, Category.assoc]

instance (S₁ S₂ : Square) : Category (Hom S₁ S₂) where
  Hom u v := TwoHom u v
  id := idHom₂
  comp := compHom₂
  id_comp := by
    intro u v η
    -- Equality of square `2`-morphisms is detected on the ambient `2`-cell component.
    ext
    simp [compHom₂, idHom₂]
  comp_id := by
    intro u v η
    -- The right identity is the same ambient categorical identity law.
    ext
    simp [compHom₂, idHom₂]
  assoc := by
    intro u v w t η θ μ
    -- Associativity is inherited verbatim from the ambient hom-category.
    ext
    simp [compHom₂, Category.assoc]

noncomputable instance
    [IsLocallyGroupoid B]
    (S₁ S₂ : Square) :
    Groupoid (Hom S₁ S₂) where
  toCategory := inferInstance
  inv η :=
    { hom := inv η.hom
      left_comm := by
        -- Compose the left-leg relation with the inverse whisker to cancel `η.hom`.
        simpa [Category.assoc] using
          congrArg (fun α ↦ inv η.hom ▷ S₂.p ≫ α) (Eq.symm η.left_comm)
      right_comm := by
        -- The right-leg inverse calculation is identical.
        simpa [Category.assoc] using
          congrArg (fun α ↦ inv η.hom ▷ S₂.q ≫ α) (Eq.symm η.right_comm) }
  inv_comp := by
    intro X Y f_1
    -- The inverse law reduces to the ambient groupoid inverse law on `f_1.hom`.
    apply TwoHom.ext
    change inv f_1.hom ≫ f_1.hom = 𝟙 Y.hom
    simpa using Groupoid.inv_comp f_1.hom
  comp_inv := by
    intro X Y f_1
    -- The other inverse law is the same reduction.
    apply TwoHom.ext
    change f_1.hom ≫ inv f_1.hom = 𝟙 X.hom
    simpa using Groupoid.comp_inv f_1.hom

instance : Bicategory (BicategoricalTwoCommutativeSquare f g) where
  Hom S₁ S₂ := Hom S₁ S₂
  homCategory S₁ S₂ := inferInstance
  id := idHom
  comp := compHom
  whiskerLeft := whiskerLeftTwoHom
  whiskerRight := whiskerRightTwoHom
  associator {a b c d} S₁ S₂ S₃ := by
    let _ : Category (Hom a d) := inferInstance
    refine
      { hom :=
          { hom :=
              (α_ S₁.hom S₂.hom S₃.hom).hom
            left_comm := by
              -- The square associator is compatible with the left leg by pure ambient coherence.
              simp [compHom, Category.assoc]
            right_comm := by
              -- The right leg is the same ambient coherence calculation.
              simp [compHom, Category.assoc]
            }
        inv :=
          { hom :=
              (α_ S₁.hom S₂.hom S₃.hom).inv
            left_comm := by
              -- The inverse associator satisfies the same compatibility relation.
              simp [compHom, Category.assoc]
            right_comm := by
              -- The right-leg inverse compatibility is identical.
              simp [compHom, Category.assoc]
            }
        hom_inv_id := by
          -- Equality of square `2`-cells is detected on the ambient apex `2`-cell.
          apply TwoHom.ext
          change (α_ S₁.hom S₂.hom S₃.hom).hom ≫ (α_ S₁.hom S₂.hom S₃.hom).inv =
              𝟙 ((compHom (compHom S₁ S₂) S₃).hom)
          simpa [compHom] using Iso.hom_inv_id (α_ S₁.hom S₂.hom S₃.hom)
        inv_hom_id := by
          -- The opposite inverse law is the same ambient inverse identity.
          apply TwoHom.ext
          change (α_ S₁.hom S₂.hom S₃.hom).inv ≫ (α_ S₁.hom S₂.hom S₃.hom).hom =
              𝟙 ((compHom S₁ (compHom S₂ S₃)).hom)
          simpa [compHom] using Iso.inv_hom_id (α_ S₁.hom S₂.hom S₃.hom) }
  leftUnitor {a b} S := by
    let _ : Category (Hom a b) := inferInstance
    refine
      { hom :=
          { hom := (λ_ S.hom).hom
            left_comm := by
              -- The square left unitor is the ambient left unitor on the apex map.
              simp [idHom, compHom, Category.assoc]
            right_comm := by
              -- The right leg is unchanged by the same left-unitor normalization.
              simp [idHom, compHom, Category.assoc]
            }
        inv :=
          { hom := (λ_ S.hom).inv
            left_comm := by
              -- The inverse left unitor is compatible by the same ambient simplification.
              simp [idHom, compHom, Category.assoc]
            right_comm := by
              -- Likewise for the right leg.
              simp [idHom, compHom, Category.assoc]
            }
        hom_inv_id := by
          -- Reduce the inverse law to the ambient left unitor inverse identity.
          apply TwoHom.ext
          change (λ_ S.hom).hom ≫ (λ_ S.hom).inv = 𝟙 ((compHom (idHom a) S).hom)
          simpa [idHom, compHom] using Iso.hom_inv_id (λ_ S.hom)
        inv_hom_id := by
          -- The opposite inverse law is the same componentwise reduction.
          apply TwoHom.ext
          change (λ_ S.hom).inv ≫ (λ_ S.hom).hom = 𝟙 S.hom
          simpa [idHom, compHom] using Iso.inv_hom_id (λ_ S.hom) }
  rightUnitor {a b} S := by
    let _ : Category (Hom a b) := inferInstance
    refine
      { hom :=
          { hom := (ρ_ S.hom).hom
            left_comm := by
              -- The square right unitor is inherited from the ambient one.
              simp [idHom, compHom, Category.assoc]
            right_comm := by
              -- The right leg is identical after the same normalization.
              simp [idHom, compHom, Category.assoc]
            }
        inv :=
          { hom := (ρ_ S.hom).inv
            left_comm := by
              -- The inverse right unitor satisfies the same compatibility relation.
              simp [idHom, compHom, Category.assoc]
            right_comm := by
              -- Likewise on the right leg.
              simp [idHom, compHom, Category.assoc]
            }
        hom_inv_id := by
          -- Reduce the inverse law to the ambient right unitor inverse identity.
          apply TwoHom.ext
          change (ρ_ S.hom).hom ≫ (ρ_ S.hom).inv = 𝟙 ((compHom S (idHom b)).hom)
          simpa [idHom, compHom] using Iso.hom_inv_id (ρ_ S.hom)
        inv_hom_id := by
          -- The opposite inverse law is identical.
          apply TwoHom.ext
          change (ρ_ S.hom).inv ≫ (ρ_ S.hom).hom = 𝟙 S.hom
          simpa [idHom, compHom] using Iso.inv_hom_id (ρ_ S.hom) }
  whisker_exchange := by
    intro a b c f_1 g_1 h i η θ
    -- The exchange law is inherited verbatim from the ambient bicategory on apex maps.
    apply TwoHom.ext
    change f_1.hom ◁ θ.hom ≫ η.hom ▷ i.hom = η.hom ▷ h.hom ≫ g_1.hom ◁ θ.hom
    simpa using CategoryTheory.Bicategory.whisker_exchange η.hom θ.hom
  whiskerLeft_id := by
    intro a b c f_1 g_1
    -- Once the transport lemmas are exact, this is just the ambient left-whiskering identity law.
    apply TwoHom.ext
    change f_1.hom ◁ 𝟙 g_1.hom = 𝟙 ((compHom f_1 g_1).hom)
    simpa [whiskerLeftTwoHom, compHom, idHom₂] using
      Bicategory.whiskerLeft_id f_1.hom g_1.hom
  whiskerLeft_comp := by
    intro a b c f_1 g_1 h i η θ
    -- The apex `2`-cell component is exactly the ambient left-whiskering composition law.
    apply TwoHom.ext
    change f_1.hom ◁ (η.hom ≫ θ.hom) = (f_1.hom ◁ η.hom) ≫ f_1.hom ◁ θ.hom
    simpa [whiskerLeftTwoHom, compHom₂] using
      Bicategory.whiskerLeft_comp f_1.hom η.hom θ.hom
  id_whiskerLeft := by
    intro a b f_1 g_1 η
    -- After identifying the `.hom` field, the displayed square relation follows automatically.
    apply TwoHom.ext
    change (𝟙 a.obj ◁ η.hom) = (λ_ f_1.hom).hom ≫ η.hom ≫ (λ_ g_1.hom).inv
    simpa [whiskerLeftTwoHom, idHom, compHom] using Bicategory.id_whiskerLeft η.hom
  comp_whiskerLeft := by
    intro a b c d f_1 g_1 h h' η
    -- This is the ambient `comp_whiskerLeft` law on the apex `2`-cell component.
    apply TwoHom.ext
    change (f_1.hom ≫ g_1.hom) ◁ η.hom =
      (α_ f_1.hom g_1.hom h.hom).hom ≫ f_1.hom ◁ (g_1.hom ◁ η.hom) ≫
        (α_ f_1.hom g_1.hom h'.hom).inv
    simpa [whiskerLeftTwoHom, compHom] using
      Bicategory.comp_whiskerLeft f_1.hom g_1.hom η.hom
  id_whiskerRight := by
    intro a b c f_1 g_1
    -- The right-whiskering identity law is inherited from the ambient bicategory.
    apply TwoHom.ext
    change 𝟙 f_1.hom ▷ g_1.hom = 𝟙 ((compHom f_1 g_1).hom)
    simpa [whiskerRightTwoHom, compHom, idHom₂] using
      Bicategory.id_whiskerRight f_1.hom g_1.hom
  comp_whiskerRight := by
    intro a b c f_1 g_1 h η θ i
    -- Vertical composition on the apex `2`-cell is preserved by right whiskering.
    apply TwoHom.ext
    change (η.hom ≫ θ.hom) ▷ i.hom = η.hom ▷ i.hom ≫ θ.hom ▷ i.hom
    simpa [whiskerRightTwoHom, compHom₂] using
      Bicategory.comp_whiskerRight η.hom θ.hom i.hom
  whiskerRight_id := by
    intro a b f_1 g_1 η
    -- This is the ambient right-whiskering identity law transported to square `2`-cells.
    apply TwoHom.ext
    change η.hom ▷ 𝟙 b.obj = (ρ_ f_1.hom).hom ≫ η.hom ≫ (ρ_ g_1.hom).inv
    simpa [whiskerRightTwoHom, idHom, compHom] using Bicategory.whiskerRight_id η.hom
  whiskerRight_comp := by
    intro a b c d f_1 f_1' η g_1 h
    -- This is the ambient right-whiskering associativity law on the `.hom` field.
    apply TwoHom.ext
    change η.hom ▷ (g_1.hom ≫ h.hom) =
      (α_ f_1.hom g_1.hom h.hom).inv ≫ (η.hom ▷ g_1.hom) ▷ h.hom ≫
        (α_ f_1'.hom g_1.hom h.hom).hom
    simpa [whiskerRightTwoHom, compHom] using
      Bicategory.whiskerRight_comp η.hom g_1.hom h.hom
  whisker_assoc := by
    intro a b c d f_1 g_1 g_1' η h
    -- The compatibility of left and right whiskering is inherited componentwise.
    apply TwoHom.ext
    change (f_1.hom ◁ η.hom) ▷ h.hom =
      (α_ f_1.hom g_1.hom h.hom).hom ≫ f_1.hom ◁ (η.hom ▷ h.hom) ≫
        (α_ f_1.hom g_1'.hom h.hom).inv
    simpa [whiskerLeftTwoHom, whiskerRightTwoHom, compHom] using
      Bicategory.whisker_assoc f_1.hom η.hom h.hom
  pentagon := by
    intro a b c d e f_1 g_1 h i
    -- The pentagon coherence law reduces to the ambient one on apex maps.
    apply TwoHom.ext
    change (α_ f_1.hom g_1.hom h.hom).hom ▷ i.hom ≫
        (α_ f_1.hom (g_1.hom ≫ h.hom) i.hom).hom ≫ f_1.hom ◁ (α_ g_1.hom h.hom i.hom).hom =
      (α_ (f_1.hom ≫ g_1.hom) h.hom i.hom).hom ≫ (α_ f_1.hom g_1.hom (h.hom ≫ i.hom)).hom
    simpa [compHom] using Bicategory.pentagon f_1.hom g_1.hom h.hom i.hom
  triangle := by
    intro a b c f_1 g_1
    -- The triangle coherence law is likewise inherited from the ambient bicategory.
    apply TwoHom.ext
    change (α_ f_1.hom (𝟙 b.obj) g_1.hom).hom ≫ f_1.hom ◁ (λ_ g_1.hom).hom =
      (ρ_ f_1.hom).hom ▷ g_1.hom
    simpa [whiskerLeftTwoHom, whiskerRightTwoHom, idHom, compHom] using
      Bicategory.triangle f_1.hom g_1.hom

instance [IsLocallyGroupoid B] :
    IsLocallyGroupoid (BicategoricalTwoCommutativeSquare f g) :=
  fun S₁ S₂ ↦ by
    change IsGroupoid (Hom S₁ S₂)
    infer_instance


/-- Helper for Definition 4.31.2: the ambient `2`-cell component of `eqToHom` between square
`1`-morphisms is the `eqToHom` of the induced apex-map equality. -/
private theorem eqToHom_hom_component {a b : Square} {u v : a ⟶ b} (h : u = v) :
    (eqToHom h).hom = eqToHom (congrArg Hom.hom h) := by
  cases h
  rfl

/-- Helper for Definition 4.31.2: square composition with an identity on the left is strictly
unital. -/
private theorem strict_id_comp_hom [Strict B] {a b : Square} (f_1 : a ⟶ b) :
    𝟙 a ≫ f_1 = f_1 := by
  -- Reduce equality of square morphisms to the apex map and the two dependent leg `2`-cells.
  apply Hom.ext
  · -- The apex map is the ambient strict left identity.
    change 𝟙 a.obj ≫ f_1.hom = f_1.hom
    exact Strict.id_comp f_1.hom
  · -- On the left leg, the strict associator and left unitor collapse the transport to `f_1.left`.
    change ((α_ (𝟙 a.obj) f_1.hom b.p).hom ≫ (𝟙 a.obj ◁ f_1.left) ≫ (λ_ a.p).hom) ≍ f_1.left
    simp [Strict.leftUnitor_eqToIso, Strict.associator_eqToIso]
  · -- The right leg is the same normalization with `q` in place of `p`.
    change ((α_ (𝟙 a.obj) f_1.hom b.q).hom ≫ (𝟙 a.obj ◁ f_1.right) ≫ (λ_ a.q).hom) ≍
        f_1.right
    simp [Strict.leftUnitor_eqToIso, Strict.associator_eqToIso]

/-- Helper for Definition 4.31.2: square composition with an identity on the right is strictly
unital. -/
private theorem strict_comp_id_hom [Strict B] {a b : Square} (f_1 : a ⟶ b) :
    f_1 ≫ 𝟙 b = f_1 := by
  -- Reduce equality of square morphisms to the apex map and the two dependent leg `2`-cells.
  apply Hom.ext
  · -- The apex map is the ambient strict right identity.
    change f_1.hom ≫ 𝟙 b.obj = f_1.hom
    exact Strict.comp_id f_1.hom
  · -- The left leg rewrites to whiskering the ambient left unitor on `b.p`.
    change ((α_ f_1.hom (𝟙 b.obj) b.p).hom ≫ (f_1.hom ◁ (λ_ b.p).hom) ≫ f_1.left) ≍ f_1.left
    simpa [Strict.associator_eqToIso, Strict.leftUnitor_eqToIso] using
      (eqToHom_comp_heq f_1.left (congr_arg (fun k ↦ f_1.hom ≫ k) (Strict.id_comp b.p)))
  · -- The right leg is the same transport calculation for `b.q`.
    change ((α_ f_1.hom (𝟙 b.obj) b.q).hom ≫ (f_1.hom ◁ (λ_ b.q).hom) ≫ f_1.right) ≍ f_1.right
    simpa [Strict.associator_eqToIso, Strict.leftUnitor_eqToIso] using
      (eqToHom_comp_heq f_1.right (congr_arg (fun k ↦ f_1.hom ≫ k) (Strict.id_comp b.q)))

/-- Helper for Definition 4.31.2: square composition is strictly associative. -/
private theorem strict_assoc_left_leg_transport [Strict B] {a b c d : Square}
    (f_1 : a ⟶ b) (g_1 : b ⟶ c) (h : c ⟶ d) :
    ((α_ (f_1.hom ≫ g_1.hom) h.hom d.p).hom ≫ ((f_1.hom ≫ g_1.hom) ◁ h.left) ≫
        ((α_ f_1.hom g_1.hom c.p).hom ≫ f_1.hom ◁ g_1.left ≫ f_1.left)) ≍
      (f_1 ≫ g_1 ≫ h).left := by
  -- Route correction: isolate the dependent left-leg transport as its own theorem so the main
  -- strict associativity proof only has to assemble the three component equalities.
  rw [Bicategory.comp_whiskerLeft]
  -- Strict associators collapse the outer transport to the whiskering-composition normal form
  -- used by the right-associated square leg.
  simp [Category.assoc, Strict.associator_eqToIso]
  -- The remaining comparison is exactly functoriality of left whiskering over the inner
  -- composite leg of `g_1 ≫ h`.
  show
    (f_1.hom ◁ g_1.hom ◁ h.left ≫ f_1.hom ◁ g_1.left ≫ f_1.left) ≍
      ((α_ f_1.hom (g_1.hom ≫ h.hom) d.p).hom ≫
          f_1.hom ◁ ((α_ g_1.hom h.hom d.p).hom ≫ g_1.hom ◁ h.left ≫ g_1.left) ≫
            f_1.left)
  simpa [Category.assoc, Strict.associator_eqToIso] using
    congrArg (fun α ↦ α ≫ f_1.left)
      (Bicategory.whiskerLeft_comp f_1.hom
        ((α_ g_1.hom h.hom d.p).hom ≫ g_1.hom ◁ h.left) g_1.left)

/-- Helper for Definition 4.31.2: the right leg of square composition has the same strict
associativity transport as the left leg. -/
private theorem strict_assoc_right_leg_transport [Strict B] {a b c d : Square}
    (f_1 : a ⟶ b) (g_1 : b ⟶ c) (h : c ⟶ d) :
    ((α_ (f_1.hom ≫ g_1.hom) h.hom d.q).hom ≫ ((f_1.hom ≫ g_1.hom) ◁ h.right) ≫
        ((α_ f_1.hom g_1.hom c.q).hom ≫ f_1.hom ◁ g_1.right ≫ f_1.right)) ≍
      (f_1 ≫ g_1 ≫ h).right := by
  -- The right-leg proof is the same normalization, now postcomposed with `f_1.right`.
  rw [Bicategory.comp_whiskerLeft]
  -- Strict associators again collapse the dependent transport to the right-associated normal form.
  simp [Category.assoc, Strict.associator_eqToIso]
  -- The right leg is the same whiskering-compatibility statement with `q`.
  show
    (f_1.hom ◁ g_1.hom ◁ h.right ≫ f_1.hom ◁ g_1.right ≫ f_1.right) ≍
      ((α_ f_1.hom (g_1.hom ≫ h.hom) d.q).hom ≫
          f_1.hom ◁ ((α_ g_1.hom h.hom d.q).hom ≫ g_1.hom ◁ h.right ≫ g_1.right) ≫
            f_1.right)
  simpa [Category.assoc, Strict.associator_eqToIso] using
    congrArg (fun α ↦ α ≫ f_1.right)
      (Bicategory.whiskerLeft_comp f_1.hom
        ((α_ g_1.hom h.hom d.q).hom ≫ g_1.hom ◁ h.right) g_1.right)

/-- Helper for Definition 4.31.2: square composition is strictly associative. -/
private theorem strict_assoc_hom [Strict B] {a b c d : Square}
    (f_1 : a ⟶ b) (g_1 : b ⟶ c) (h : c ⟶ d) :
    (f_1 ≫ g_1) ≫ h = f_1 ≫ g_1 ≫ h := by
  -- Reduce equality of square morphisms to the apex map and the two dependent leg `2`-cells.
  apply Hom.ext
  · -- The apex map is the ambient strict associativity equality.
    change (f_1.hom ≫ g_1.hom) ≫ h.hom = f_1.hom ≫ g_1.hom ≫ h.hom
    exact Strict.assoc f_1.hom g_1.hom h.hom
  · -- Route correction: reuse the exact left-leg transport lemma so the dependent field proof is
    -- reduced to the already-normalized strict associativity calculation.
    change
      ((α_ (f_1.hom ≫ g_1.hom) h.hom d.p).hom ≫ ((f_1.hom ≫ g_1.hom) ◁ h.left) ≫
          ((α_ f_1.hom g_1.hom c.p).hom ≫ f_1.hom ◁ g_1.left ≫ f_1.left)) ≍
        (f_1 ≫ g_1 ≫ h).left
    exact strict_assoc_left_leg_transport f_1 g_1 h
  · -- The right leg is the same strict transport calculation with `q` in place of `p`.
    change
      ((α_ (f_1.hom ≫ g_1.hom) h.hom d.q).hom ≫ ((f_1.hom ≫ g_1.hom) ◁ h.right) ≫
          ((α_ f_1.hom g_1.hom c.q).hom ≫ f_1.hom ◁ g_1.right ≫ f_1.right)) ≍
        (f_1 ≫ g_1 ≫ h).right
    exact strict_assoc_right_leg_transport f_1 g_1 h

instance [Strict B] : Strict (BicategoricalTwoCommutativeSquare f g) where
  id_comp := by
    intro a b f_1
    -- Reuse the strict left-unital square equality proved just above.
    exact strict_id_comp_hom f_1
  comp_id := by
    intro a b f_1
    -- Reuse the strict right-unital square equality proved just above.
    exact strict_comp_id_hom f_1
  assoc := by
    intro a b c d f_1 g_1 h
    -- Reuse the strict associativity equality proved just above.
    exact strict_assoc_hom f_1 g_1 h
  leftUnitor_eqToIso := by
    intro a b f_1
    -- Compare isomorphisms on the underlying ambient `2`-cell component of their `hom`.
    apply Iso.ext
    apply TwoHom.ext
    -- Rewrite the `eqToIso` side to the `eqToHom` of the apex-map equality proved above.
    have hhom : congrArg Hom.hom (strict_id_comp_hom f_1) = Strict.id_comp f_1.hom := by
      exact Subsingleton.elim _ _
    rw [eqToIso.hom, eqToHom_hom_component, hhom]
    -- The remaining statement is exactly the ambient strict left-unitor compatibility.
    simpa using congrArg Iso.hom (Strict.leftUnitor_eqToIso f_1.hom)
  rightUnitor_eqToIso := by
    intro a b f_1
    -- Compare isomorphisms on the underlying ambient `2`-cell component of their `hom`.
    apply Iso.ext
    apply TwoHom.ext
    -- Rewrite the `eqToIso` side to the `eqToHom` of the apex-map equality proved above.
    have hhom : congrArg Hom.hom (strict_comp_id_hom f_1) = Strict.comp_id f_1.hom := by
      exact Subsingleton.elim _ _
    rw [eqToIso.hom, eqToHom_hom_component, hhom]
    -- The remaining statement is exactly the ambient strict right-unitor compatibility.
    simpa using congrArg Iso.hom (Strict.rightUnitor_eqToIso f_1.hom)
  associator_eqToIso := by
    intro a b c d f_1 g_1 h
    -- Compare isomorphisms on the underlying ambient `2`-cell component of their `hom`.
    apply Iso.ext
    apply TwoHom.ext
    -- Rewrite the `eqToIso` side to the `eqToHom` of the apex-map equality proved above.
    have hhom :
        congrArg Hom.hom (strict_assoc_hom f_1 g_1 h) =
          Strict.assoc f_1.hom g_1.hom h.hom := by
      exact Subsingleton.elim _ _
    rw [eqToIso.hom, eqToHom_hom_component, hhom]
    -- The remaining statement is exactly the ambient strict associator compatibility.
    simpa using congrArg Iso.hom (Strict.associator_eqToIso f_1.hom g_1.hom h.hom)

end

end BicategoricalTwoCommutativeSquare

variable (P : BicategoricalTwoCommutativeSquare f g)

/- Definition 4.31.2: a `2`-fibre product square over `f : x ⟶ z` and `g : y ⟶ z` is a final
object `P` of the bicategory of `2`-commutative squares over that cospan. This core owner
statement is intrinsic to the square bicategory itself. -/
#check (IsFinal P : Prop)

section LocallyGroupoid

variable [IsLocallyGroupoid B]

/- Companion bridge: under the inherited `(2,1)` hypothesis, the textbook
existence-and-uniqueness formulation is the canonical specialization of
`Bicategory.isFinal_iff_existsUnique_hom₂` to the bicategory
`BicategoricalTwoCommutativeSquare f g`. -/
#check Bicategory.isFinal_iff_existsUnique_hom₂ P

end LocallyGroupoid

end CategoryTheory
