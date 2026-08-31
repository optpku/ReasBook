module

public import stacks_project.Chap04.Definition_4_32_1
public import stacks_project.Chap04.Definition_4_33_9
public import stacks_project.Chap04.Lemma_4_32_3
public import stacks_project.Chap04.Lemma_4_33_8
public import stacks_project.Chap04.Lemma_4_33_10
public import stacks_project.Chap04.Lemma_4_35_7
public import stacks_project.Chap04.Lemma_4_35_9

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open CategoryOver
open BasedFunctor
open scoped Bicategory

universe u₁ u₂ u₃ v

namespace CategoryTheory

variable {C : Type u₁} [Category.{v} C]
variable {S : Type u₂} [Category.{v} S]
variable {S' : Type u₃} [Category.{v} S']

/- Domain-style sampling for Lemma 4.34.1:
- primary domain: relative inertia over a fixed base and its comparison with the chapter owner
  `explicitTwoFibreProduct` in `Cat/C`;
- sampled owner-level declarations:
  `CategoryOver.explicitTwoFibreProduct`,
  `CategoryOver.relativeInertiaOver`,
  `BasedFunctor.IsEquivalenceOverBase`,
  `Functor.Fiber`;
- best owner abstraction: the intrinsic source-level data are the relative inertia objects
  `RelativeInertiaObject F`, while the public over-base diagonal and comparison maps should live on
  the bundled morphism owner `X ⥤ᵇ Y` in `Cat/C`, not on a bare functor plus a separate
  commutativity proof;
- primitive data: an object `x : S` together with an automorphism `α : x ≅ x` whose image under
  `F` is the identity;
- derived API: the category structure, projection and structure functors, induced functoriality on
  inertia, and the over-`C` bridge from relative inertia to the diagonal self-`2`-fibre product.

Source/core/bridge triage:
- `source-facing`: `RelativeInertiaObject`, `relativeInertiaProjection`, and the bundled
  over-base theorem `BasedFunctor.relativeInertiaEquivalenceOverBase`;
- `core/canonical`: `CategoryOver.relativeInertiaOver`,
  `CategoryOver.explicitTwoFibreProduct`, and `BasedFunctor.IsEquivalenceOverBase`;
- `bridge/view`: the internal bare-functor constructions used to build the bundled `Cat/C`
  morphisms. -/

/-- An object of the relative inertia of a functor `F : S ⥤ S'` is an object `x` of `S`
together with an automorphism of `x` whose image under `F` is the identity. -/
structure RelativeInertiaObject (F : S ⥤ S') where
  /-- The underlying object of the total category. -/
  x : S
  /-- The automorphism of `x`. -/
  α : x ≅ x
  /-- The automorphism becomes the identity after applying `F`. -/
  map_hom_eq_id : F.map α.hom = 𝟙 (F.obj x)

/-- A morphism in the relative inertia category intertwines the chosen automorphisms. -/
structure RelativeInertiaHom (F : S ⥤ S')
    (X Y : RelativeInertiaObject F) where
  /-- The underlying morphism in `S`. -/
  φ : X.x ⟶ Y.x
  /-- The underlying morphism commutes with the chosen automorphisms. -/
  comm : X.α.hom ≫ φ = φ ≫ Y.α.hom

/-- Relative-inertia morphisms are determined by their underlying morphisms in `S`. -/
@[ext] theorem RelativeInertiaHom.ext {F : S ⥤ S'} {X Y : RelativeInertiaObject F}
    (f g : RelativeInertiaHom F X Y) (h : f.φ = g.φ) :
    f = g := by
  cases f
  cases g
  cases h
  rfl

variable (F : S ⥤ S')

-- Proof sketch: both sides are the same composite with an identity morphism on `X.x`.
/-- The identity morphism of an inertia object commutes with its chosen automorphism. -/
theorem relativeInertiaHom_id_comm
    (X : RelativeInertiaObject F) :
    X.α.hom ≫ 𝟙 X.x = 𝟙 X.x ≫ X.α.hom := by
  -- Both sides reduce to the chosen automorphism of `X`.
  simp

/-- The identity morphism in the relative inertia category. -/
def relativeInertiaHomId
    (X : RelativeInertiaObject F) :
    RelativeInertiaHom F X X :=
  { φ := 𝟙 X.x
    comm := relativeInertiaHom_id_comm F X }

-- Proof sketch: paste the two intertwining squares for `f` and `g` and reassociate.
/-- The composite of two inertia morphisms again commutes with the chosen automorphisms. -/
theorem relativeInertiaHom_comp_comm
    {X Y Z : RelativeInertiaObject F}
    (f : RelativeInertiaHom F X Y)
    (g : RelativeInertiaHom F Y Z) :
    X.α.hom ≫ (f.φ ≫ g.φ) = (f.φ ≫ g.φ) ≫ Z.α.hom := by
  -- Reassociate so the two given intertwining identities can be applied in sequence.
  calc
    X.α.hom ≫ (f.φ ≫ g.φ) = (X.α.hom ≫ f.φ) ≫ g.φ := by
      simp [Category.assoc]
    _ = (f.φ ≫ Y.α.hom) ≫ g.φ := by
      rw [f.comm]
    _ = f.φ ≫ (Y.α.hom ≫ g.φ) := by
      simp [Category.assoc]
    _ = f.φ ≫ (g.φ ≫ Z.α.hom) := by
      rw [g.comm]
    _ = (f.φ ≫ g.φ) ≫ Z.α.hom := by
      simp [Category.assoc]

/-- Composition in the relative inertia category. -/
def relativeInertiaHomComp
    {X Y Z : RelativeInertiaObject F}
    (f : RelativeInertiaHom F X Y)
    (g : RelativeInertiaHom F Y Z) :
    RelativeInertiaHom F X Z :=
  { φ := f.φ ≫ g.φ
    comm := relativeInertiaHom_comp_comm F f g }

-- Proof sketch: both morphisms have the same underlying component `f.φ`.
/-- Left identity for the composition law on relative inertia morphisms. -/
theorem relativeInertiaHom_id_comp
    {X Y : RelativeInertiaObject F}
    (f : RelativeInertiaHom F X Y) :
    relativeInertiaHomComp F (relativeInertiaHomId F X) f = f := by
  -- Equality is detected on the underlying arrow in `S`.
  apply RelativeInertiaHom.ext
  simp [relativeInertiaHomComp, relativeInertiaHomId]

-- Proof sketch: both morphisms have the same underlying component `f.φ`.
/-- Right identity for the composition law on relative inertia morphisms. -/
theorem relativeInertiaHom_comp_id
    {X Y : RelativeInertiaObject F}
    (f : RelativeInertiaHom F X Y) :
    relativeInertiaHomComp F f (relativeInertiaHomId F Y) = f := by
  -- Equality is detected on the underlying arrow in `S`.
  apply RelativeInertiaHom.ext
  simp [relativeInertiaHomComp, relativeInertiaHomId]

-- Proof sketch: all three composites have the same underlying morphism
-- `f.φ ≫ g.φ ≫ h.φ`, and the compatibility proofs are propositions.
/-- Associativity of composition in the relative inertia category. -/
theorem relativeInertiaHom_assoc
    {W X Y Z : RelativeInertiaObject F}
    (f : RelativeInertiaHom F W X)
    (g : RelativeInertiaHom F X Y)
    (h : RelativeInertiaHom F Y Z) :
    relativeInertiaHomComp F (relativeInertiaHomComp F f g) h =
      relativeInertiaHomComp F f (relativeInertiaHomComp F g h) := by
  -- Both composites have the same underlying arrow `(f.φ ≫ g.φ) ≫ h.φ`.
  apply RelativeInertiaHom.ext
  simp [relativeInertiaHomComp, Category.assoc]

/-- The relative inertia objects and intertwining morphisms form a category. -/
instance relativeInertiaCategory :
    Category (RelativeInertiaObject F) where
  Hom X Y := RelativeInertiaHom F X Y
  id := relativeInertiaHomId F
  comp f g := relativeInertiaHomComp F f g
  id_comp := relativeInertiaHom_id_comp F
  comp_id := relativeInertiaHom_comp_id F
  assoc f g h := relativeInertiaHom_assoc F f g h

namespace RelativeInertiaHom

variable {F} {X Y : RelativeInertiaObject F}

/-- A morphism in a relative inertia category is an isomorphism as soon as its underlying
morphism in the source category is an isomorphism. -/
theorem isIso_of_isIso (f : X ⟶ Y) [IsIso f.φ] : IsIso f := by
  let g : RelativeInertiaHom F Y X :=
    { φ := inv f.φ
      comm := by
        apply (cancel_mono f.φ).1
        simp [Category.assoc, f.comm] }
  refine ⟨⟨g, ?_, ?_⟩⟩
  · apply RelativeInertiaHom.ext
    change f.φ ≫ inv f.φ = 𝟙 X.x
    simp
  · apply RelativeInertiaHom.ext
    change inv f.φ ≫ f.φ = 𝟙 Y.x
    simp

end RelativeInertiaHom

/-- The projection from the relative inertia category to the base category `C`. -/
def relativeInertiaProjection
    (p : S ⥤ C) :
    RelativeInertiaObject F ⥤ C where
  obj X := p.obj X.x
  map f := p.map f.φ
  map_id X := p.map_id X.x
  map_comp f g := p.map_comp f.φ g.φ

/-- The canonical forgetful functor from the relative inertia of `F` to the source category
`S`. -/
def relativeInertiaStructureFunctor :
    RelativeInertiaObject F ⥤ S where
  obj X := X.x
  map f := f.φ
  map_id _ := rfl
  map_comp _ _ := rfl

/-- The canonical structure functor from the relative inertia of `F` lies over the base category
`C`. -/
theorem relativeInertiaStructureFunctor_comm
    (p : S ⥤ C) :
    relativeInertiaStructureFunctor F ⋙ p = relativeInertiaProjection F p :=
  rfl

/-- The identity morphisms define the neutral section from the source category to its relative
inertia. -/
def relativeInertiaIdentitySection :
    S ⥤ RelativeInertiaObject F where
  obj X :=
    { x := X
      α := Iso.refl X
      map_hom_eq_id := F.map_id X }
  map f :=
    { φ := f
      comm := by simp }
  map_id X := RelativeInertiaHom.ext _ _ rfl
  map_comp f g := RelativeInertiaHom.ext _ _ rfl

/-- The neutral section is a right inverse to the relative-inertia structure functor. -/
@[simp] theorem relativeInertiaIdentitySection_comp_structureFunctor :
    relativeInertiaIdentitySection F ⋙ relativeInertiaStructureFunctor F = 𝟭 S :=
  rfl

/-- The neutral section picks out the identity automorphism on each source object. -/
@[simp] theorem relativeInertiaIdentitySection_obj_α (X : S) :
    ((relativeInertiaIdentitySection F).obj X).α = Iso.refl X :=
  rfl

theorem relativeInertiaMapObj_map_hom_eq_id
    {S₁ S₁' S₂ S₂' : Type*}
    [Category.{v} S₁] [Category.{v} S₁'] [Category.{v} S₂] [Category.{v} S₂']
    {F₁ : S₁ ⥤ S₁'} {F₂ : S₂ ⥤ S₂'}
    (G : S₁ ⥤ S₂) (G' : S₁' ⥤ S₂')
    (τ : F₁ ⋙ G' ≅ G ⋙ F₂)
    (X : RelativeInertiaObject F₁) :
    F₂.map (G.map X.α.hom) = 𝟙 (F₂.obj (G.obj X.x)) := by
  -- Compare the two ways of transporting `X.α.hom` across the comparison isomorphism `τ`.
  exact (cancel_epi (τ.hom.app X.x)).1 <| by
    simpa [Functor.comp_map, X.map_hom_eq_id, Category.assoc] using
      (τ.hom.naturality X.α.hom).symm

def relativeInertiaMapObj
    {S₁ S₁' S₂ S₂' : Type*}
    [Category.{v} S₁] [Category.{v} S₁'] [Category.{v} S₂] [Category.{v} S₂']
    {F₁ : S₁ ⥤ S₁'} {F₂ : S₂ ⥤ S₂'}
    (G : S₁ ⥤ S₂) (G' : S₁' ⥤ S₂')
    (τ : F₁ ⋙ G' ≅ G ⋙ F₂)
    (X : RelativeInertiaObject F₁) :
    RelativeInertiaObject F₂ :=
  { x := G.obj X.x
    α := G.mapIso X.α
    map_hom_eq_id := relativeInertiaMapObj_map_hom_eq_id G G' τ X }

theorem relativeInertiaMapHom_comm
    {S₁ S₁' S₂ : Type*}
    [Category.{v} S₁] [Category.{v} S₁'] [Category.{v} S₂]
    {F : S₁ ⥤ S₁'} (G : S₁ ⥤ S₂)
    {X Y : RelativeInertiaObject F} (f : X ⟶ Y) :
    G.map X.α.hom ≫ G.map f.φ = G.map f.φ ≫ G.map Y.α.hom := by
  -- Apply `G.map` to the defining intertwining relation of `f`.
  simpa [Functor.map_comp] using congrArg G.map f.comm

def relativeInertiaMapHom
    {S₁ S₁' S₂ S₂' : Type*}
    [Category.{v} S₁] [Category.{v} S₁'] [Category.{v} S₂] [Category.{v} S₂']
    {F₁ : S₁ ⥤ S₁'} {F₂ : S₂ ⥤ S₂'}
    (G : S₁ ⥤ S₂) (G' : S₁' ⥤ S₂')
    (τ : F₁ ⋙ G' ≅ G ⋙ F₂)
    {X Y : RelativeInertiaObject F₁} (f : X ⟶ Y) :
    relativeInertiaMapObj G G' τ X ⟶ relativeInertiaMapObj G G' τ Y :=
  { φ := G.map f.φ
    comm := relativeInertiaMapHom_comm G f }

theorem relativeInertiaMap_map_id
    {S₁ S₁' S₂ S₂' : Type*}
    [Category.{v} S₁] [Category.{v} S₁'] [Category.{v} S₂] [Category.{v} S₂']
    {F₁ : S₁ ⥤ S₁'} {F₂ : S₂ ⥤ S₂'}
    (G : S₁ ⥤ S₂) (G' : S₁' ⥤ S₂')
    (τ : F₁ ⋙ G' ≅ G ⋙ F₂)
    (X : RelativeInertiaObject F₁) :
    relativeInertiaMapHom G G' τ (𝟙 X) = 𝟙 (relativeInertiaMapObj G G' τ X) := by
  -- Equality is detected on the underlying arrow in the target category.
  apply RelativeInertiaHom.ext
  change G.map (𝟙 X.x) = 𝟙 (G.obj X.x)
  simp

theorem relativeInertiaMap_map_comp
    {S₁ S₁' S₂ S₂' : Type*}
    [Category.{v} S₁] [Category.{v} S₁'] [Category.{v} S₂] [Category.{v} S₂']
    {F₁ : S₁ ⥤ S₁'} {F₂ : S₂ ⥤ S₂'}
    (G : S₁ ⥤ S₂) (G' : S₁' ⥤ S₂')
    (τ : F₁ ⋙ G' ≅ G ⋙ F₂)
    {X Y Z : RelativeInertiaObject F₁} (f : X ⟶ Y) (g : Y ⟶ Z) :
    relativeInertiaMapHom G G' τ (f ≫ g) =
      relativeInertiaMapHom G G' τ f ≫ relativeInertiaMapHom G G' τ g := by
  -- Equality is detected on the underlying arrow in the target category.
  apply RelativeInertiaHom.ext
  change G.map (f.φ ≫ g.φ) = G.map f.φ ≫ G.map g.φ
  simp

/-- An invertible comparison square `F₁ ⋙ G' ≅ G ⋙ F₂` induces the canonical functor on relative
inertia categories, sending `(x, α)` to `(G.obj x, G.mapIso α)` and intertwining morphisms by
`G.map`. -/
def relativeInertiaMap
    {S₁ S₁' S₂ S₂' : Type*}
    [Category.{v} S₁] [Category.{v} S₁'] [Category.{v} S₂] [Category.{v} S₂']
    {F₁ : S₁ ⥤ S₁'} {F₂ : S₂ ⥤ S₂'}
    (G : S₁ ⥤ S₂) (G' : S₁' ⥤ S₂')
    (τ : F₁ ⋙ G' ≅ G ⋙ F₂) :
    RelativeInertiaObject F₁ ⥤ RelativeInertiaObject F₂ where
  obj := relativeInertiaMapObj G G' τ
  map := relativeInertiaMapHom G G' τ
  map_id := relativeInertiaMap_map_id G G' τ
  map_comp := relativeInertiaMap_map_comp G G' τ

/-- The canonical functor on relative inertia sends the underlying object `x` to `G.obj x`. -/
@[simp] theorem relativeInertiaMap_obj_x
    {S₁ S₁' S₂ S₂' : Type*}
    [Category.{v} S₁] [Category.{v} S₁'] [Category.{v} S₂] [Category.{v} S₂']
    {F₁ : S₁ ⥤ S₁'} {F₂ : S₂ ⥤ S₂'}
    (G : S₁ ⥤ S₂) (G' : S₁' ⥤ S₂')
    (τ : F₁ ⋙ G' ≅ G ⋙ F₂)
    (X : RelativeInertiaObject F₁) :
    ((relativeInertiaMap G G' τ).obj X).x = G.obj X.x :=
  rfl

/-- The canonical functor on relative inertia sends the chosen automorphism `α` to `G.mapIso α`.
-/
@[simp] theorem relativeInertiaMap_obj_α
    {S₁ S₁' S₂ S₂' : Type*}
    [Category.{v} S₁] [Category.{v} S₁'] [Category.{v} S₂] [Category.{v} S₂']
    {F₁ : S₁ ⥤ S₁'} {F₂ : S₂ ⥤ S₂'}
    (G : S₁ ⥤ S₂) (G' : S₁' ⥤ S₂')
    (τ : F₁ ⋙ G' ≅ G ⋙ F₂)
    (X : RelativeInertiaObject F₁) :
    ((relativeInertiaMap G G' τ).obj X).α = G.mapIso X.α :=
  rfl

/-- The canonical functor on relative inertia sends the underlying arrow `φ` to `G.map φ`. -/
@[simp] theorem relativeInertiaMap_map_hom
    {S₁ S₁' S₂ S₂' : Type*}
    [Category.{v} S₁] [Category.{v} S₁'] [Category.{v} S₂] [Category.{v} S₂']
    {F₁ : S₁ ⥤ S₁'} {F₂ : S₂ ⥤ S₂'}
    (G : S₁ ⥤ S₂) (G' : S₁' ⥤ S₂')
    (τ : F₁ ⋙ G' ≅ G ⋙ F₂)
    {X Y : RelativeInertiaObject F₁} (f : X ⟶ Y) :
    ((relativeInertiaMap G G' τ).map f).φ = G.map f.φ :=
  rfl

variable (p : S ⥤ C)

variable {p}
variable (p' : S' ⥤ C)

-- Proof sketch: apply `p'` to the equality `F.map X.α.hom = 𝟙`, then rewrite both sides using
-- the strict commutativity `F ⋙ p' = p`.
/-- The automorphism in an inertia object is vertical over `C`. -/
theorem relativeInertiaObject_base_eq_id
    (comm : F ⋙ p' = p)
    (X : RelativeInertiaObject F) :
    p.map X.α.hom = 𝟙 (p.obj X.x) := by
  -- Push the defining relation for `X.α` down to the base and rewrite via `comm`.
  cases comm
  simpa [Functor.comp_map] using congrArg p'.map X.map_hom_eq_id

abbrev overFunctor
    (comm : F ⋙ p' = p) :
    BasedCategory.ofFunctor p ⥤ᵇ BasedCategory.ofFunctor p' :=
  { toFunctor := F
    w := comm }

theorem relativeDiagonalObjIso_hom_isLift
    (comm : F ⋙ p' = p)
    (X : S) :
    p'.IsHomLift (𝟙 (p.obj X)) (𝟙 (F.obj X)) := by
  cases comm
  simp

private theorem relativeDiagonalObjIso_hom_inv_id
    (X : S) :
    𝟙 (F.obj X) ≫ 𝟙 (F.obj X) = 𝟙 (F.obj X) := by
  simp

def relativeDiagonalObjIso
    (comm : F ⋙ p' = p)
    (X : S) :
    ((overFunctor F p' comm).fiberFunctor (p.obj X)).obj (Functor.Fiber.mk rfl) ≅
      ((overFunctor F p' comm).fiberFunctor (p.obj X)).obj (Functor.Fiber.mk rfl) where
  hom := ⟨𝟙 (F.obj X), relativeDiagonalObjIso_hom_isLift F p' comm X⟩
  inv := ⟨𝟙 (F.obj X), relativeDiagonalObjIso_hom_isLift F p' comm X⟩
  hom_inv_id := by
    apply Functor.Fiber.hom_ext
    exact relativeDiagonalObjIso_hom_inv_id F X
  inv_hom_id := by
    apply Functor.Fiber.hom_ext
    exact relativeDiagonalObjIso_hom_inv_id F X

theorem relativeDiagonalFunctor_map_comm
    (comm : F ⋙ p' = p)
    {X Y : S}
    (f : X ⟶ Y) :
    CommSq
      (F.map f)
      (relativeDiagonalObjIso F p' comm X).hom.1
      (relativeDiagonalObjIso F p' comm Y).hom.1
      (F.map f) := by
  -- The diagonal comparison is the identity in the relevant fibre, so the square is tautological.
  refine ⟨?_⟩
  change F.map f ≫ 𝟙 (F.obj Y) = 𝟙 (F.obj X) ≫ F.map f
  simp

def relativeDiagonalObject
    (comm : F ⋙ p' = p)
    (X : S) :
    ExplicitTwoFibreProductObject (overFunctor F p' comm) (overFunctor F p' comm) :=
  { U := p.obj X
    obj :=
      { fst := Functor.Fiber.mk rfl
        snd := Functor.Fiber.mk rfl
        iso := relativeDiagonalObjIso F p' comm X } }

def relativeDiagonalFunctorMap
    (comm : F ⋙ p' = p)
    {X Y : S}
    (f : X ⟶ Y) :
    relativeDiagonalObject F p' comm X ⟶ relativeDiagonalObject F p' comm Y :=
  { base := p.map f
    a := f
    a_over := by
      exact IsHomLift.of_fac p (p.map f) f rfl rfl (by simp)
    b := f
    b_over := by
      exact IsHomLift.of_fac p (p.map f) f rfl rfl (by simp)
    comm := relativeDiagonalFunctor_map_comm F p' comm f }

theorem relativeDiagonalFunctor_map_id
    (comm : F ⋙ p' = p)
    (X : S) :
    relativeDiagonalFunctorMap F p' comm (𝟙 X) =
      𝟙 (relativeDiagonalObject F p' comm X) := by
  apply ExplicitTwoFibreProductHom.ext
  · rfl
  · rfl

theorem relativeDiagonalFunctor_map_comp
    (comm : F ⋙ p' = p)
    {X Y Z : S}
    (f : X ⟶ Y)
    (g : Y ⟶ Z) :
    relativeDiagonalFunctorMap F p' comm (f ≫ g) =
      relativeDiagonalFunctorMap F p' comm f ≫
        relativeDiagonalFunctorMap F p' comm g := by
  apply ExplicitTwoFibreProductHom.ext
  · rfl
  · rfl

def relativeDiagonalFunctor
    (comm : F ⋙ p' = p) :
    S ⥤ (explicitTwoFibreProduct (overFunctor F p' comm) (overFunctor F p' comm)).obj where
  obj := relativeDiagonalObject F p' comm
  map := relativeDiagonalFunctorMap F p' comm
  map_id := relativeDiagonalFunctor_map_id F p' comm
  map_comp := relativeDiagonalFunctor_map_comp F p' comm

theorem relativeDiagonalFunctor_comm
    (comm : F ⋙ p' = p) :
    relativeDiagonalFunctor F p' comm ⋙
        (explicitTwoFibreProduct (overFunctor F p' comm) (overFunctor F p' comm)).p =
      p := by
  rfl

/-- Internal bare-functor model for the canonical diagonal morphism in `Cat/C`. The bundled
public owner is `BasedFunctor.relativeDiagonalOver`. -/
def relativeDiagonalOverRaw
    (comm : F ⋙ p' = p) :
    BasedCategory.ofFunctor p ⥤ᵇ
      explicitTwoFibreProduct (overFunctor F p' comm) (overFunctor F p' comm) :=
  { toFunctor := relativeDiagonalFunctor F p' comm
    w := relativeDiagonalFunctor_comm F p' comm }

private theorem relativeInertiaObject_map_inv_eq_id
    (X : RelativeInertiaObject F) :
    F.map X.α.inv = 𝟙 (F.obj X.x) := by
  have h : F.map X.α.inv ≫ F.map X.α.hom = 𝟙 (F.obj X.x) := by
    simp
  simpa [X.map_hom_eq_id] using h

private theorem relativeInertiaObject_base_inv_eq_id
    (comm : F ⋙ p' = p)
    (X : RelativeInertiaObject F) :
    p.map X.α.inv = 𝟙 (p.obj X.x) := by
  have h : p.map X.α.inv ≫ p.map X.α.hom = 𝟙 (p.obj X.x) := by
    simp
  simpa [relativeInertiaObject_base_eq_id F p' comm X] using h

def relativeInertiaComparisonHom
    (comm : F ⋙ p' = p)
    (X : RelativeInertiaObject F) :
    ExplicitTwoFibreProductHom
      (overFunctor F p' comm)
      (overFunctor F p' comm)
      ((relativeDiagonalOverRaw F p' comm).obj X.x)
      ((relativeDiagonalOverRaw F p' comm).obj X.x) where
  base := 𝟙 (p.obj X.x)
  a := X.α.hom
  a_over := by
    change p.IsHomLift (𝟙 (p.obj X.x)) X.α.hom
    simpa [relativeInertiaObject_base_eq_id F p' comm X] using
      (inferInstance : p.IsHomLift (p.map X.α.hom) X.α.hom)
  b := 𝟙 X.x
  b_over := by
    change p.IsHomLift (𝟙 (p.obj X.x)) (𝟙 X.x)
    refine IsHomLift.of_fac p (𝟙 (p.obj X.x)) (𝟙 X.x) rfl rfl ?_
    simp
  comm := by
    -- The comparison isomorphisms in the diagonal object are identities, so only
    -- `F.map X.α.hom = 𝟙` remains.
    refine ⟨?_⟩
    change F.map X.α.hom ≫ 𝟙 (F.obj X.x) = 𝟙 (F.obj X.x) ≫ F.map (𝟙 X.x)
    simp [X.map_hom_eq_id]

theorem relativeInertiaComparisonHom_isHomLift
    (comm : F ⋙ p' = p)
    (X : RelativeInertiaObject F) :
    ((explicitTwoFibreProduct (overFunctor F p' comm) (overFunctor F p' comm)).p).IsHomLift
      (𝟙 (p.obj X.x))
      (relativeInertiaComparisonHom F p' comm X) := by
  -- The projection remembers exactly the stored base arrow of the pullback morphism.
  let q := (explicitTwoFibreProduct (overFunctor F p' comm) (overFunctor F p' comm)).p
  change q.IsHomLift (𝟙 (p.obj X.x)) (relativeInertiaComparisonHom F p' comm X)
  convert (Functor.IsHomLift.map (p := q) (relativeInertiaComparisonHom F p' comm X))

def relativeInertiaComparisonInvHom
    (comm : F ⋙ p' = p)
    (X : RelativeInertiaObject F) :
    ExplicitTwoFibreProductHom
      (overFunctor F p' comm)
      (overFunctor F p' comm)
      ((relativeDiagonalOverRaw F p' comm).obj X.x)
      ((relativeDiagonalOverRaw F p' comm).obj X.x) where
  base := 𝟙 (p.obj X.x)
  a := X.α.inv
  a_over := by
    change p.IsHomLift (𝟙 (p.obj X.x)) X.α.inv
    simpa [relativeInertiaObject_base_inv_eq_id F p' comm X] using
      (inferInstance : p.IsHomLift (p.map X.α.inv) X.α.inv)
  b := 𝟙 X.x
  b_over := by
    change p.IsHomLift (𝟙 (p.obj X.x)) (𝟙 X.x)
    refine IsHomLift.of_fac p (𝟙 (p.obj X.x)) (𝟙 X.x) rfl rfl ?_
    simp
  comm := by
    -- The comparison isomorphisms in the diagonal object are identities, so only
    -- `F.map X.α.inv = 𝟙` remains.
    refine ⟨?_⟩
    change F.map X.α.inv ≫ 𝟙 (F.obj X.x) = 𝟙 (F.obj X.x) ≫ F.map (𝟙 X.x)
    simp [relativeInertiaObject_map_inv_eq_id F X]

theorem relativeInertiaComparisonInvHom_isHomLift
    (comm : F ⋙ p' = p)
    (X : RelativeInertiaObject F) :
    ((explicitTwoFibreProduct (overFunctor F p' comm) (overFunctor F p' comm)).p).IsHomLift
      (𝟙 (p.obj X.x))
      (relativeInertiaComparisonInvHom F p' comm X) := by
  -- The projection remembers exactly the stored base arrow of the pullback morphism.
  let q := (explicitTwoFibreProduct (overFunctor F p' comm) (overFunctor F p' comm)).p
  change q.IsHomLift (𝟙 (p.obj X.x)) (relativeInertiaComparisonInvHom F p' comm X)
  convert (Functor.IsHomLift.map (p := q) (relativeInertiaComparisonInvHom F p' comm X))

private theorem relativeInertiaComparisonIso_hom_inv_id
    (comm : F ⋙ p' = p)
    (X : RelativeInertiaObject F) :
    relativeInertiaComparisonHom F p' comm X ≫
        relativeInertiaComparisonInvHom F p' comm X =
      𝟙 ((relativeDiagonalOverRaw F p' comm).obj X.x) := by
  -- Compare the two composites componentwise in the explicit pullback category.
  apply ExplicitTwoFibreProductHom.ext
  · change X.α.hom ≫ X.α.inv = 𝟙 X.x
    simp
  · change (𝟙 X.x) ≫ 𝟙 X.x = 𝟙 X.x
    simp

private theorem relativeInertiaComparisonIso_inv_hom_id
    (comm : F ⋙ p' = p)
    (X : RelativeInertiaObject F) :
    relativeInertiaComparisonInvHom F p' comm X ≫
        relativeInertiaComparisonHom F p' comm X =
      𝟙 ((relativeDiagonalOverRaw F p' comm).obj X.x) := by
  -- Compare the two composites componentwise in the explicit pullback category.
  apply ExplicitTwoFibreProductHom.ext
  · change X.α.inv ≫ X.α.hom = 𝟙 X.x
    simp
  · change (𝟙 X.x) ≫ 𝟙 X.x = 𝟙 X.x
    simp

def relativeInertiaComparisonIso
    (comm : F ⋙ p' = p)
    (X : RelativeInertiaObject F) :
    ((relativeDiagonalOverRaw F p' comm).fiberFunctor (p.obj X.x)).obj (Functor.Fiber.mk rfl) ≅
      ((relativeDiagonalOverRaw F p' comm).fiberFunctor (p.obj X.x)).obj (Functor.Fiber.mk rfl) where
  hom := ⟨relativeInertiaComparisonHom F p' comm X,
    relativeInertiaComparisonHom_isHomLift F p' comm X⟩
  inv := ⟨relativeInertiaComparisonInvHom F p' comm X,
    relativeInertiaComparisonInvHom_isHomLift F p' comm X⟩
  hom_inv_id := by
    apply Functor.Fiber.hom_ext
    exact relativeInertiaComparisonIso_hom_inv_id F p' comm X
  inv_hom_id := by
    apply Functor.Fiber.hom_ext
    exact relativeInertiaComparisonIso_inv_hom_id F p' comm X

def relativeInertiaToDiagonalPullbackObj
    (comm : F ⋙ p' = p)
    (X : RelativeInertiaObject F) :
    ExplicitTwoFibreProductObject
      (relativeDiagonalOverRaw F p' comm)
      (relativeDiagonalOverRaw F p' comm) :=
  { U := p.obj X.x
    obj :=
      { fst := Functor.Fiber.mk rfl
        snd := Functor.Fiber.mk rfl
        iso := relativeInertiaComparisonIso F p' comm X } }

theorem relativeInertiaToDiagonalPullback_map_comm
    (comm : F ⋙ p' = p)
    {X Y : RelativeInertiaObject F}
    (f : RelativeInertiaHom F X Y) :
    CommSq
      ((relativeDiagonalOverRaw F p' comm).map f.φ)
      (relativeInertiaToDiagonalPullbackObj F p' comm X).obj.iso.hom.1
      (relativeInertiaToDiagonalPullbackObj F p' comm Y).obj.iso.hom.1
      ((relativeDiagonalOverRaw F p' comm).map f.φ) := by
  -- The two composites agree componentwise; the `a`-component is exactly `f.comm`.
  refine ⟨?_⟩
  apply ExplicitTwoFibreProductHom.ext
  · simpa [relativeInertiaToDiagonalPullbackObj, relativeInertiaComparisonIso,
      relativeInertiaComparisonHom, relativeDiagonalOverRaw, relativeDiagonalFunctor,
      relativeDiagonalFunctorMap, Category.assoc] using f.comm.symm
  · change f.φ ≫ 𝟙 Y.x = 𝟙 X.x ≫ f.φ
    simp

def relativeInertiaToDiagonalPullbackMap
    (comm : F ⋙ p' = p)
    {X Y : RelativeInertiaObject F}
    (f : RelativeInertiaHom F X Y) :
    ExplicitTwoFibreProductHom
      (relativeDiagonalOverRaw F p' comm)
      (relativeDiagonalOverRaw F p' comm)
      (relativeInertiaToDiagonalPullbackObj F p' comm X)
      (relativeInertiaToDiagonalPullbackObj F p' comm Y) :=
  { base := p.map f.φ
    a := f.φ
    a_over := by
      exact IsHomLift.of_fac p (p.map f.φ) f.φ rfl rfl (by simp)
    b := f.φ
    b_over := by
      exact IsHomLift.of_fac p (p.map f.φ) f.φ rfl rfl (by simp)
    comm := relativeInertiaToDiagonalPullback_map_comm F p' comm f }

theorem relativeInertiaToDiagonalPullback_map_id
    (comm : F ⋙ p' = p)
    (X : RelativeInertiaObject F) :
    relativeInertiaToDiagonalPullbackMap F p' comm (𝟙 X) =
      𝟙 (relativeInertiaToDiagonalPullbackObj F p' comm X) := by
  apply ExplicitTwoFibreProductHom.ext
  · rfl
  · rfl

def relativeInertiaToDiagonalPullbackFunctor
    (comm : F ⋙ p' = p) :
    RelativeInertiaObject F ⥤
      (explicitTwoFibreProduct
        (relativeDiagonalOverRaw F p' comm)
        (relativeDiagonalOverRaw F p' comm)).obj where
  obj := relativeInertiaToDiagonalPullbackObj F p' comm
  map := relativeInertiaToDiagonalPullbackMap F p' comm
  map_id := relativeInertiaToDiagonalPullback_map_id F p' comm
  map_comp := by
    intro X Y Z f g
    apply ExplicitTwoFibreProductHom.ext
    · rfl
    · rfl

theorem relativeInertiaToDiagonalPullbackFunctor_comm
    (comm : F ⋙ p' = p) :
    relativeInertiaToDiagonalPullbackFunctor F p' comm ⋙
        (explicitTwoFibreProduct
          (relativeDiagonalOverRaw F p' comm)
          (relativeDiagonalOverRaw F p' comm)).p =
      relativeInertiaProjection F p := by
  rfl

/-- Internal bare-functor comparison morphism from relative inertia to the self-pullback of the
raw diagonal. The bundled public owner is `BasedFunctor.relativeInertiaToDiagonalPullback`. -/
def relativeInertiaToDiagonalPullbackRaw
    (comm : F ⋙ p' = p) :
    BasedCategory.ofFunctor (relativeInertiaProjection F p) ⥤ᵇ
      explicitTwoFibreProduct (relativeDiagonalOverRaw F p' comm) (relativeDiagonalOverRaw F p' comm)
    where
  toFunctor := relativeInertiaToDiagonalPullbackFunctor F p' comm
  w := relativeInertiaToDiagonalPullbackFunctor_comm F p' comm

/-- Helper for Lemma 4.34.1: the left component of the comparison morphism of a diagonal
self-pullback object is an isomorphism in the source category. -/
private theorem diagonalPullbackLeft_isIso
    (comm : F ⋙ p' = p)
    (P : (explicitTwoFibreProduct
      (relativeDiagonalOverRaw F p' comm)
      (relativeDiagonalOverRaw F p' comm)).obj) :
    IsIso P.obj.iso.hom.1.a := by
  -- Forget the fiberwise comparison isomorphism to the total diagonal category.
  let e :
      (relativeDiagonalOverRaw F p' comm).obj P.obj.fst.1 ≅
        (relativeDiagonalOverRaw F p' comm).obj P.obj.snd.1 :=
    { hom := P.obj.iso.hom.1
      inv := P.obj.iso.inv.1
      hom_inv_id := congrArg Subtype.val P.obj.iso.hom_inv_id
      inv_hom_id := congrArg Subtype.val P.obj.iso.inv_hom_id }
  -- The left component of an isomorphism in the diagonal category is itself an isomorphism.
  refine ⟨e.inv.a, ?_, ?_⟩
  · exact congrArg ExplicitTwoFibreProductHom.a e.hom_inv_id
  · exact congrArg ExplicitTwoFibreProductHom.a e.inv_hom_id

/-- Helper for Lemma 4.34.1: the right component of the comparison morphism of a diagonal
self-pullback object is an isomorphism in the source category. -/
private theorem diagonalPullbackRight_isIso
    (comm : F ⋙ p' = p)
    (P : (explicitTwoFibreProduct
      (relativeDiagonalOverRaw F p' comm)
      (relativeDiagonalOverRaw F p' comm)).obj) :
    IsIso P.obj.iso.hom.1.b := by
  -- Forget the fiberwise comparison isomorphism to the total diagonal category.
  let e :
      (relativeDiagonalOverRaw F p' comm).obj P.obj.fst.1 ≅
        (relativeDiagonalOverRaw F p' comm).obj P.obj.snd.1 :=
    { hom := P.obj.iso.hom.1
      inv := P.obj.iso.inv.1
      hom_inv_id := congrArg Subtype.val P.obj.iso.hom_inv_id
      inv_hom_id := congrArg Subtype.val P.obj.iso.inv_hom_id }
  -- The right component of an isomorphism in the diagonal category is likewise invertible.
  refine ⟨e.inv.b, ?_, ?_⟩
  · exact congrArg ExplicitTwoFibreProductHom.b e.hom_inv_id
  · exact congrArg ExplicitTwoFibreProductHom.b e.inv_hom_id

attribute [local instance] diagonalPullbackLeft_isIso diagonalPullbackRight_isIso

/-- Helper for Lemma 4.34.1: the left comparison component of a diagonal self-pullback object,
packaged as an isomorphism in the source category. -/
private noncomputable abbrev diagonalPullbackLeftIso
    (comm : F ⋙ p' = p)
    (P : (explicitTwoFibreProduct
      (relativeDiagonalOverRaw F p' comm)
      (relativeDiagonalOverRaw F p' comm)).obj) :
    P.obj.fst.1 ≅ P.obj.snd.1 :=
  @asIso _ _ _ _ P.obj.iso.hom.1.a (diagonalPullbackLeft_isIso F p' comm P)

/-- Helper for Lemma 4.34.1: the right comparison component of a diagonal self-pullback object,
packaged as an isomorphism in the source category. -/
private noncomputable abbrev diagonalPullbackRightIso
    (comm : F ⋙ p' = p)
    (P : (explicitTwoFibreProduct
      (relativeDiagonalOverRaw F p' comm)
      (relativeDiagonalOverRaw F p' comm)).obj) :
    P.obj.fst.1 ≅ P.obj.snd.1 :=
  @asIso _ _ _ _ P.obj.iso.hom.1.b (diagonalPullbackRight_isIso F p' comm P)

/-- Helper for Lemma 4.34.1: the base projection of a morphism in the diagonal self-pullback is
its stored `base` field. -/
private theorem diagonalPullback_base_projection_map
    (comm : F ⋙ p' = p)
    {P Q : (explicitTwoFibreProduct
      (relativeDiagonalOverRaw F p' comm)
      (relativeDiagonalOverRaw F p' comm)).obj}
    (φ : P ⟶ Q) :
    (explicitTwoFibreProduct
      (relativeDiagonalOverRaw F p' comm)
      (relativeDiagonalOverRaw F p' comm)).p.map φ = φ.base := by
  rfl

/-- Helper for Lemma 4.34.1: a lift for the projection of the diagonal self-pullback has base
arrow equal to the stored `base` field of the morphism. -/
private theorem diagonalPullback_isHomLift_base_eq
    (comm : F ⋙ p' = p)
    {P Q : (explicitTwoFibreProduct
      (relativeDiagonalOverRaw F p' comm)
      (relativeDiagonalOverRaw F p' comm)).obj}
    {f : P.U ⟶ Q.U} (φ : P ⟶ Q)
    (hφ : (explicitTwoFibreProduct
      (relativeDiagonalOverRaw F p' comm)
      (relativeDiagonalOverRaw F p' comm)).p.IsHomLift f φ) :
    φ.base = f := by
  let q := (explicitTwoFibreProduct
    (relativeDiagonalOverRaw F p' comm)
    (relativeDiagonalOverRaw F p' comm)).p
  have h : f = q.map φ := @IsHomLift.eq_of_isHomLift _ _ _ _ q _ _ f φ hφ
  simpa [q, diagonalPullback_base_projection_map F p' comm φ] using h.symm

/-- Helper for Lemma 4.34.1: a lift in the diagonal self-pullback induces the corresponding lift
on the left component over the same base arrow. -/
private theorem diagonalPullback_left_isHomLift_of_isHomLift
    (comm : F ⋙ p' = p)
    {P Q : (explicitTwoFibreProduct
      (relativeDiagonalOverRaw F p' comm)
      (relativeDiagonalOverRaw F p' comm)).obj}
    {f : P.U ⟶ Q.U} (φ : P ⟶ Q)
    (hφ : (explicitTwoFibreProduct
      (relativeDiagonalOverRaw F p' comm)
      (relativeDiagonalOverRaw F p' comm)).p.IsHomLift f φ) :
    p.IsHomLift f φ.a := by
  -- Normalize the stored base arrow of `φ` to the chosen external base arrow `f`.
  have hbase : φ.base = f := diagonalPullback_isHomLift_base_eq F p' comm φ hφ
  rw [← hbase]
  -- The left component lift is already part of the explicit pullback morphism data.
  simpa using (φ.a_over : p.IsHomLift φ.base φ.a)

/-- Helper for Lemma 4.34.1: a lift in the diagonal self-pullback induces the corresponding lift
on the right component over the same base arrow. -/
private theorem diagonalPullback_right_isHomLift_of_isHomLift
    (comm : F ⋙ p' = p)
    {P Q : (explicitTwoFibreProduct
      (relativeDiagonalOverRaw F p' comm)
      (relativeDiagonalOverRaw F p' comm)).obj}
    {f : P.U ⟶ Q.U} (φ : P ⟶ Q)
    (hφ : (explicitTwoFibreProduct
      (relativeDiagonalOverRaw F p' comm)
      (relativeDiagonalOverRaw F p' comm)).p.IsHomLift f φ) :
    p.IsHomLift f φ.b := by
  have hbase : φ.base = f := diagonalPullback_isHomLift_base_eq F p' comm φ hφ
  rw [← hbase]
  simpa using (φ.b_over : p.IsHomLift φ.base φ.b)

/-- Helper for Lemma 4.34.1: the two comparison components of a diagonal self-pullback object
have the same image under `F`, because they form a morphism between diagonal objects. -/
private theorem diagonalPullback_component_maps_eq
    (comm : F ⋙ p' = p)
    (P : (explicitTwoFibreProduct
      (relativeDiagonalOverRaw F p' comm)
      (relativeDiagonalOverRaw F p' comm)).obj) :
    F.map (diagonalPullbackLeftIso F p' comm P).hom =
      F.map (diagonalPullbackRightIso F p' comm P).hom := by
  -- Strictify both diagonal comparison maps to identities, so the stored commutative square says
  -- exactly that the two components have the same image under `F`.
  cases P with
  | mk U P =>
      rcases P with ⟨fst, snd, iso⟩
      have hcomm := iso.hom.1.comm.w
      have hfst :
          ((((relativeDiagonalOverRaw F p' comm).fiberFunctor U).obj fst).1).comparison =
            𝟙 (F.obj fst.1) := by
        cases fst
        rfl
      have hsnd :
          ((((relativeDiagonalOverRaw F p' comm).fiberFunctor U).obj snd).1).comparison =
            𝟙 (F.obj snd.1) := by
        cases snd
        rfl
      rw [hsnd, hfst] at hcomm
      have hcomm' : F.map (iso.hom.1.a) = F.map (iso.hom.1.b) := by
        exact (Category.comp_id _).symm.trans <| hcomm.trans (Category.id_comp _)
      simpa [diagonalPullbackLeftIso, diagonalPullbackRightIso] using hcomm'

/-- Helper for Lemma 4.34.1: the automorphism `ι ≫ κ⁻¹` attached to a diagonal self-pullback
object becomes the identity after applying `F`. -/
private theorem diagonalPullbackToRelativeInertiaObj_map_hom_eq_id
    (comm : F ⋙ p' = p)
    (P : (explicitTwoFibreProduct
      (relativeDiagonalOverRaw F p' comm)
      (relativeDiagonalOverRaw F p' comm)).obj) :
    F.map ((diagonalPullbackLeftIso F p' comm P ≪≫
        (diagonalPullbackRightIso F p' comm P).symm).hom) =
      𝟙 (F.obj P.obj.fst.1) := by
  -- Route correction: the source-text automorphism on the first object is `ι ≫ κ⁻¹`,
  -- not the opposite composition.
  calc
    F.map ((diagonalPullbackLeftIso F p' comm P).hom ≫
        (diagonalPullbackRightIso F p' comm P).inv)
        = F.map (diagonalPullbackLeftIso F p' comm P).hom ≫
            F.map (diagonalPullbackRightIso F p' comm P).inv := by
              simpa using
                F.map_comp (diagonalPullbackLeftIso F p' comm P).hom
                  (diagonalPullbackRightIso F p' comm P).inv
    _ = F.map (diagonalPullbackRightIso F p' comm P).hom ≫
          F.map (diagonalPullbackRightIso F p' comm P).inv := by
            rw [diagonalPullback_component_maps_eq F p' comm P]
    _ = 𝟙 (F.obj P.obj.fst.1) := by
          simpa using (F.mapIso (diagonalPullbackRightIso F p' comm P)).hom_inv_id

/-- Helper for Lemma 4.34.1: the reverse functor sends a diagonal self-pullback object to the
corresponding inertia object on its first component with automorphism `ι ≫ κ⁻¹`. -/
private noncomputable def diagonalPullbackToRelativeInertiaObj
    (comm : F ⋙ p' = p)
    (P : (explicitTwoFibreProduct
      (relativeDiagonalOverRaw F p' comm)
      (relativeDiagonalOverRaw F p' comm)).obj) :
    RelativeInertiaObject F :=
  { x := P.obj.fst.1
    α := diagonalPullbackLeftIso F p' comm P ≪≫ (diagonalPullbackRightIso F p' comm P).symm
    map_hom_eq_id := diagonalPullbackToRelativeInertiaObj_map_hom_eq_id F p' comm P }

/-- Helper for Lemma 4.34.1: a morphism in the diagonal self-pullback intertwines the induced
automorphisms `ι ≫ κ⁻¹` on the first components. -/
private theorem diagonalPullbackToRelativeInertia_map_comm
    (comm : F ⋙ p' = p)
    {P Q : (explicitTwoFibreProduct
      (relativeDiagonalOverRaw F p' comm)
      (relativeDiagonalOverRaw F p' comm)).obj}
    (φ : P ⟶ Q) :
    (diagonalPullbackToRelativeInertiaObj F p' comm P).α.hom ≫ φ.a =
      φ.a ≫ (diagonalPullbackToRelativeInertiaObj F p' comm Q).α.hom := by
  -- Read the pullback square componentwise to recover the textbook relations
  -- `ι_P ≫ φ' = φ ≫ ι_Q` and `κ_P ≫ φ' = φ ≫ κ_Q`.
  have hcomm := φ.comm.w
  have hleft :
      (diagonalPullbackLeftIso F p' comm P).hom ≫ φ.b =
        φ.a ≫ (diagonalPullbackLeftIso F p' comm Q).hom := by
    simpa [ExplicitTwoFibreProductObject.comparison, diagonalPullbackLeftIso,
      relativeDiagonalOverRaw, relativeDiagonalFunctor,
      relativeDiagonalFunctorMap, Category.assoc] using
      congrArg ExplicitTwoFibreProductHom.a hcomm.symm
  have hright :
      (diagonalPullbackRightIso F p' comm P).hom ≫ φ.b =
        φ.a ≫ (diagonalPullbackRightIso F p' comm Q).hom := by
    simpa [ExplicitTwoFibreProductObject.comparison, diagonalPullbackRightIso,
      relativeDiagonalOverRaw, relativeDiagonalFunctor,
      relativeDiagonalFunctorMap, Category.assoc] using
      congrArg ExplicitTwoFibreProductHom.b hcomm.symm
  -- Cancel the right comparison isomorphism on the target to reduce to the two component
  -- identities extracted above.
  apply (cancel_mono (diagonalPullbackRightIso F p' comm Q).hom).1
  have hfirst :
      (((diagonalPullbackToRelativeInertiaObj F p' comm P).α.hom ≫ φ.a) ≫
          (diagonalPullbackRightIso F p' comm Q).hom) =
        (diagonalPullbackLeftIso F p' comm P).hom ≫ φ.b := by
    -- Use the right component relation to trade `φ.a ≫ κ_Q` for `κ_P ≫ φ.b`.
    dsimp [diagonalPullbackToRelativeInertiaObj]
    calc
      ((((diagonalPullbackLeftIso F p' comm P).hom ≫
            (diagonalPullbackRightIso F p' comm P).inv) ≫ φ.a) ≫
          (diagonalPullbackRightIso F p' comm Q).hom) =
        (diagonalPullbackLeftIso F p' comm P).hom ≫
          ((diagonalPullbackRightIso F p' comm P).inv ≫
            (φ.a ≫ (diagonalPullbackRightIso F p' comm Q).hom)) := by
              simp [Category.assoc]
      _ = (diagonalPullbackLeftIso F p' comm P).hom ≫
            ((diagonalPullbackRightIso F p' comm P).inv ≫
              ((diagonalPullbackRightIso F p' comm P).hom ≫ φ.b)) := by
                rw [hright.symm]
      _ = (diagonalPullbackLeftIso F p' comm P).hom ≫ φ.b := by
            simp
  have hlast :
      φ.a ≫ (diagonalPullbackLeftIso F p' comm Q).hom =
        ((φ.a ≫ (diagonalPullbackToRelativeInertiaObj F p' comm Q).α.hom) ≫
          (diagonalPullbackRightIso F p' comm Q).hom) := by
    -- Normalize the target-side `ι_Q ≫ κ_Q⁻¹ ≫ κ_Q` tail back to `ι_Q`.
    dsimp [diagonalPullbackToRelativeInertiaObj]
    calc
      φ.a ≫ (diagonalPullbackLeftIso F p' comm Q).hom =
          φ.a ≫ (diagonalPullbackLeftIso F p' comm Q).hom ≫
            𝟙 Q.obj.snd.1 := by
              simp
      _ = φ.a ≫ (diagonalPullbackLeftIso F p' comm Q).hom ≫
            ((diagonalPullbackRightIso F p' comm Q).inv ≫
              (diagonalPullbackRightIso F p' comm Q).hom) := by
              rw [Iso.inv_hom_id]
      _ = ((φ.a ≫ ((diagonalPullbackLeftIso F p' comm Q).hom ≫
              (diagonalPullbackRightIso F p' comm Q).inv)) ≫
            (diagonalPullbackRightIso F p' comm Q).hom) := by
              simp [Category.assoc]
  exact hfirst.trans (hleft.trans hlast)

/-- Helper for Lemma 4.34.1: on morphisms, the reverse functor remembers the left component of a
diagonal self-pullback morphism. -/
private noncomputable def diagonalPullbackToRelativeInertiaMap
    (comm : F ⋙ p' = p)
    {P Q : (explicitTwoFibreProduct
      (relativeDiagonalOverRaw F p' comm)
      (relativeDiagonalOverRaw F p' comm)).obj}
    (φ : P ⟶ Q) :
    diagonalPullbackToRelativeInertiaObj F p' comm P ⟶
      diagonalPullbackToRelativeInertiaObj F p' comm Q :=
  { φ := φ.a
    comm := diagonalPullbackToRelativeInertia_map_comm F p' comm φ }

/-- Helper for Lemma 4.34.1: the explicit diagonal self-pullback admits the textbook reverse
functor to the relative inertia category. -/
private noncomputable def diagonalPullbackToRelativeInertiaFunctor
    (comm : F ⋙ p' = p) :
    (explicitTwoFibreProduct
      (relativeDiagonalOverRaw F p' comm)
      (relativeDiagonalOverRaw F p' comm)).obj ⥤ RelativeInertiaObject F where
  obj := diagonalPullbackToRelativeInertiaObj F p' comm
  map := diagonalPullbackToRelativeInertiaMap F p' comm
  map_id := by
    intro P
    -- The reverse functor keeps only the first component, so identities are immediate.
    apply RelativeInertiaHom.ext
    rfl
  map_comp := by
    intro P Q R φ ψ
    -- Composition is likewise inherited from the first component of the pullback morphism.
    apply RelativeInertiaHom.ext
    rfl

/-- Helper for Lemma 4.34.1: the reverse functor lies over the same base projection as the
diagonal self-pullback. -/
private theorem diagonalPullbackToRelativeInertiaFunctor_comm
    (comm : F ⋙ p' = p) :
    diagonalPullbackToRelativeInertiaFunctor F p' comm ⋙ relativeInertiaProjection F p =
      (explicitTwoFibreProduct
        (relativeDiagonalOverRaw F p' comm)
        (relativeDiagonalOverRaw F p' comm)).p := by
  -- The objectwise base equality comes from the first fiber component, and the morphism equation
  -- is the usual `IsHomLift.fac'` comparison.
  exact Functor.ext (fun P ↦ P.obj.fst.2) (fun P Q φ ↦ by
    have hφa : p.IsHomLift φ.base φ.a := φ.a_over
    letI := hφa
    simpa using (IsHomLift.fac' p φ.base φ.a))

/-- Helper for Lemma 4.34.1: the explicit diagonal self-pullback maps back to the relative
inertia category over the same base category `C`. -/
private noncomputable def diagonalPullbackToRelativeInertiaRaw
    (comm : F ⋙ p' = p) :
    (explicitTwoFibreProduct
      (relativeDiagonalOverRaw F p' comm)
      (relativeDiagonalOverRaw F p' comm)) ⥤ᵇ
        BasedCategory.ofFunctor (relativeInertiaProjection F p) where
  toFunctor := diagonalPullbackToRelativeInertiaFunctor F p' comm
  w := diagonalPullbackToRelativeInertiaFunctor_comm F p' comm

-- Proof sketch: this is the Stacks comparison `(x, α) ↦ (x, x, α, id_x)` into the self-pullback
-- of the relative diagonal `S ⟶ S ×_{S'} S`. A quasi-inverse sends the explicit pullback datum
-- `(x, x, (ι, κ))` to `(x, κ⁻¹ ≫ ι)`, exactly as in the source argument using the canonical
-- explicit `2`-fibre-product model from Lemma `4.33.10`.
/-- Helper for Lemma 4.34.1: the textbook tail
`(ι ≫ κ⁻¹) ≫ κ` in the counit component collapses back to `ι`. -/
private theorem diagonal_pullback_right_iso_cancel_assoc
    (comm : F ⋙ p' = p)
    (P : (explicitTwoFibreProduct
      (relativeDiagonalOverRaw F p' comm)
      (relativeDiagonalOverRaw F p' comm)).obj) :
    (diagonalPullbackToRelativeInertiaObj F p' comm P).α.hom ≫
        (diagonalPullbackRightIso F p' comm P).hom =
      (diagonalPullbackLeftIso F p' comm P).hom := by
  -- Normalize the textbook counit tail `(ι ≫ κ⁻¹) ≫ κ` before building the pullback morphism.
  dsimp [diagonalPullbackToRelativeInertiaObj]
  calc
    ((diagonalPullbackLeftIso F p' comm P).hom ≫
          (diagonalPullbackRightIso F p' comm P).inv) ≫
        (diagonalPullbackRightIso F p' comm P).hom =
      (diagonalPullbackLeftIso F p' comm P).hom ≫
        ((diagonalPullbackRightIso F p' comm P).inv ≫
          (diagonalPullbackRightIso F p' comm P).hom) := by
            simp [Category.assoc]
    _ = (diagonalPullbackLeftIso F p' comm P).hom := by
          simp

/-- Helper for Lemma 4.34.1: the right comparison component of a morphism in the diagonal
self-pullback is the textbook identity `κ_P ≫ φ' = φ ≫ κ_Q`. -/
private theorem diagonal_pullback_right_naturality
    (comm : F ⋙ p' = p)
    {P Q : (explicitTwoFibreProduct
      (relativeDiagonalOverRaw F p' comm)
      (relativeDiagonalOverRaw F p' comm)).obj}
    (φ : P ⟶ Q) :
    (diagonalPullbackRightIso F p' comm P).hom ≫ φ.b =
      φ.a ≫ (diagonalPullbackRightIso F p' comm Q).hom := by
  -- Read the right component of the stored pullback square.
  have hcomm := φ.comm.w
  simpa [ExplicitTwoFibreProductObject.comparison, diagonalPullbackRightIso,
    relativeDiagonalOverRaw, relativeDiagonalFunctor, relativeDiagonalFunctorMap,
    Category.assoc] using congrArg ExplicitTwoFibreProductHom.b hcomm.symm

/-- Helper for Lemma 4.34.1: forgetting a morphism in the diagonal fiber and then taking its
right component recovers the base comparison `eqToHom fst.2 ≫ eqToHom snd.2.symm`. -/
private theorem diagonal_pullback_right_component_base_of_fiber_hom
    (comm : F ⋙ p' = p)
    {U : C} {fst snd : p.Fiber U}
    (η : ((relativeDiagonalOverRaw F p' comm).fiberFunctor U).obj fst ⟶
      ((relativeDiagonalOverRaw F p' comm).fiberFunctor U).obj snd) :
    p.map η.1.b =
      eqToHom fst.2 ≫ eqToHom snd.2.symm := by
  -- Unpack the two fibre objects so the ambient pullback base equation is expressed on `U`.
  cases fst with
  | mk x hx =>
      cases snd with
      | mk y hy =>
          rcases η with ⟨η, hη⟩
          let q :=
            (explicitTwoFibreProduct
              (overFunctor F p' comm)
              (overFunctor F p' comm)).p
          have hbase : η.base = eqToHom hx ≫ 𝟙 U ≫ eqToHom hy.symm := by
            change q.map η = eqToHom hx ≫ 𝟙 U ≫ eqToHom hy.symm
            simpa [q, Category.assoc] using (IsHomLift.fac' q (𝟙 U) η)
          have hηb : p.IsHomLift (eqToHom hx ≫ 𝟙 U ≫ eqToHom hy.symm) η.b := by
            rw [← hbase]
            exact η.b_over
          simpa [Category.assoc] using
            (IsHomLift.fac' p (eqToHom hx ≫ 𝟙 U ≫ eqToHom hy.symm) η.b)

/-- Helper for Lemma 4.34.1: the right comparison map `κ` lies over the source base object of
the counit component. -/
private theorem diagonal_pullback_fiber_iso_right_hom_base_fac
    (comm : F ⋙ p' = p)
    (P : (explicitTwoFibreProduct
      (relativeDiagonalOverRaw F p' comm)
      (relativeDiagonalOverRaw F p' comm)).obj) :
    p.map (diagonalPullbackRightIso F p' comm P).hom =
      eqToHom P.obj.fst.2 ≫ eqToHom P.obj.snd.2.symm := by
  -- The stored fibre isomorphism `P.obj.iso.hom` forgets to the ambient right comparison `κ`.
  change p.map P.obj.iso.hom.1.b = eqToHom P.obj.fst.2 ≫ eqToHom P.obj.snd.2.symm
  exact diagonal_pullback_right_component_base_of_fiber_hom F p' comm
    (fst := P.obj.fst) (snd := P.obj.snd) (η := P.obj.iso.hom)

/-- Helper for Lemma 4.34.1: the inverse right comparison map `κ⁻¹` is vertical over the same
base object, now in the reverse direction. -/
private theorem diagonal_pullback_fiber_iso_right_inv_base_fac
    (comm : F ⋙ p' = p)
    (P : (explicitTwoFibreProduct
      (relativeDiagonalOverRaw F p' comm)
      (relativeDiagonalOverRaw F p' comm)).obj) :
    p.map (diagonalPullbackRightIso F p' comm P).inv =
      eqToHom P.obj.snd.2 ≫ eqToHom P.obj.fst.2.symm := by
  -- The inverse fibre isomorphism forgets to the ambient inverse right comparison `κ⁻¹`.
  let e :
      (relativeDiagonalOverRaw F p' comm).obj P.obj.fst.1 ≅
        (relativeDiagonalOverRaw F p' comm).obj P.obj.snd.1 :=
    { hom := P.obj.iso.hom.1
      inv := P.obj.iso.inv.1
      hom_inv_id := congrArg Subtype.val P.obj.iso.hom_inv_id
      inv_hom_id := congrArg Subtype.val P.obj.iso.inv_hom_id }
  have hright :
      (diagonalPullbackRightIso F p' comm P).inv = P.obj.iso.inv.1.b := by
    have hcomp :
        (diagonalPullbackRightIso F p' comm P).hom ≫ P.obj.iso.inv.1.b = 𝟙 P.obj.fst.1 := by
      simpa [e, diagonalPullbackRightIso] using congrArg ExplicitTwoFibreProductHom.b e.hom_inv_id
    apply IsIso.inv_eq_of_hom_inv_id (f := (diagonalPullbackRightIso F p' comm P).hom)
    exact hcomp
  rw [hright]
  exact diagonal_pullback_right_component_base_of_fiber_hom F p' comm
    (fst := P.obj.snd) (snd := P.obj.fst) (η := P.obj.iso.inv)

/-- Helper for Lemma 4.34.1: the right comparison map `κ` lies over the source base object of
the counit component. -/
private theorem diagonal_pullback_right_component_hom_isHomLift
    (comm : F ⋙ p' = p)
    (P : (explicitTwoFibreProduct
      (relativeDiagonalOverRaw F p' comm)
      (relativeDiagonalOverRaw F p' comm)).obj) :
    p.IsHomLift (eqToHom P.obj.fst.2) (diagonalPullbackRightIso F p' comm P).hom := by
  -- Repackage the explicit vertical formula for `κ` as the source-side transport `eqToHom`.
  refine
    IsHomLift.of_fac' p (eqToHom P.obj.fst.2)
      (diagonalPullbackRightIso F p' comm P).hom rfl P.obj.snd.2 ?_
  simpa [Category.assoc] using
    diagonal_pullback_fiber_iso_right_hom_base_fac F p' comm P

/-- Helper for Lemma 4.34.1: the inverse right comparison map `κ⁻¹` lies over the inverse source
base transport of the counit component. -/
private theorem diagonal_pullback_right_component_inv_isHomLift
    (comm : F ⋙ p' = p)
    (P : (explicitTwoFibreProduct
      (relativeDiagonalOverRaw F p' comm)
      (relativeDiagonalOverRaw F p' comm)).obj) :
    p.IsHomLift (eqToHom P.obj.fst.2.symm) (diagonalPullbackRightIso F p' comm P).inv := by
  -- Repackage the explicit vertical formula for `κ⁻¹` as the inverse source transport.
  refine
    IsHomLift.of_fac' p (eqToHom P.obj.fst.2.symm)
      (diagonalPullbackRightIso F p' comm P).inv P.obj.snd.2 rfl ?_
  simpa [Category.assoc] using
    diagonal_pullback_fiber_iso_right_inv_base_fac F p' comm P

/-- Helper for Lemma 4.34.1: the forward counit component is the morphism `(𝟙, κ)` from the
reverse-then-forward pullback object back to the original pullback object. -/
private theorem diagonal_pullback_counit_hom_comm
    (comm : F ⋙ p' = p)
    (P : (explicitTwoFibreProduct
      (relativeDiagonalOverRaw F p' comm)
      (relativeDiagonalOverRaw F p' comm)).obj) :
    CommSq
      ((relativeDiagonalOverRaw F p' comm).map (𝟙 P.obj.fst.1))
      ((relativeInertiaToDiagonalPullbackRaw F p' comm).obj
        (diagonalPullbackToRelativeInertiaObj F p' comm P)).obj.iso.hom.1
      P.obj.iso.hom.1
      ((relativeDiagonalOverRaw F p' comm).map (diagonalPullbackRightIso F p' comm P).hom) := by
  -- Route correction: isolate the `a`-component `((ι ≫ κ⁻¹) ≫ κ) = ι` before packaging the full
  -- pullback morphism.
  refine ⟨?_⟩
  apply ExplicitTwoFibreProductHom.ext
  · simpa [relativeDiagonalOverRaw, relativeDiagonalFunctor, relativeDiagonalFunctorMap,
      Category.assoc] using (diagonal_pullback_right_iso_cancel_assoc F p' comm P).symm
  · rfl

/-- Helper for Lemma 4.34.1: the inverse counit component is the morphism `(𝟙, κ⁻¹)` from the
original pullback object back to the reverse-then-forward image. -/
private theorem relative_inertia_roundtrip_iso_hom_a
    (comm : F ⋙ p' = p)
    (P : (explicitTwoFibreProduct
      (relativeDiagonalOverRaw F p' comm)
      (relativeDiagonalOverRaw F p' comm)).obj) :
    ((relativeInertiaToDiagonalPullbackRaw F p' comm).obj
      (diagonalPullbackToRelativeInertiaObj F p' comm P)).obj.iso.hom.1.a =
      (diagonalPullbackToRelativeInertiaObj F p' comm P).α.hom := by
  -- Unfold the roundtrip comparison object: its `a`-component is exactly the inertia automorphism.
  rfl

/-- Helper for Lemma 4.34.1: the inverse counit component is the morphism `(𝟙, κ⁻¹)` from the
original pullback object back to the reverse-then-forward image. -/
private theorem diagonal_pullback_counit_inv_comm
    (comm : F ⋙ p' = p)
    (P : (explicitTwoFibreProduct
      (relativeDiagonalOverRaw F p' comm)
      (relativeDiagonalOverRaw F p' comm)).obj) :
    CommSq
      ((relativeDiagonalOverRaw F p' comm).map (𝟙 P.obj.fst.1))
      P.obj.iso.hom.1
      ((relativeInertiaToDiagonalPullbackRaw F p' comm).obj
        (diagonalPullbackToRelativeInertiaObj F p' comm P)).obj.iso.hom.1
      ((relativeDiagonalOverRaw F p' comm).map (diagonalPullbackRightIso F p' comm P).inv) := by
  -- Route correction: verify the inverse textbook square directly on its two pullback components.
  refine ⟨?_⟩
  apply ExplicitTwoFibreProductHom.ext
  · -- The first component is exactly the defining automorphism `α = ι ≫ κ⁻¹`.
    simpa [relativeDiagonalOverRaw, relativeDiagonalFunctor, relativeDiagonalFunctorMap,
      diagonalPullbackToRelativeInertiaObj, diagonalPullbackLeftIso, diagonalPullbackRightIso,
      Category.assoc] using
      (relative_inertia_roundtrip_iso_hom_a F p' comm P)
  · -- The second component is the iso identity `κ ≫ κ⁻¹ = 𝟙`.
    change 𝟙 P.obj.fst.1 ≫ 𝟙 P.obj.fst.1 = (diagonalPullbackRightIso F p' comm P).hom ≫
      (diagonalPullbackRightIso F p' comm P).inv
    simpa using (diagonalPullbackRightIso F p' comm P).hom_inv_id.symm

/-- Helper for Lemma 4.34.1: the forward counit component on a pullback object is the explicit
map `(𝟙, κ)`. -/
private noncomputable def diagonal_pullback_counit_hom
    (comm : F ⋙ p' = p)
    (P : (explicitTwoFibreProduct
      (relativeDiagonalOverRaw F p' comm)
      (relativeDiagonalOverRaw F p' comm)).obj) :
    ((diagonalPullbackToRelativeInertiaRaw F p' comm ⋙
          relativeInertiaToDiagonalPullbackRaw F p' comm).obj P) ⟶
      P :=
  { base := eqToHom P.obj.fst.2
    a := 𝟙 P.obj.fst.1
    a_over := IsHomLift.id_lift_eqToHom_domain (p := p) P.obj.fst.2 rfl
    b := (diagonalPullbackRightIso F p' comm P).hom
    b_over := diagonal_pullback_right_component_hom_isHomLift F p' comm P
    comm := diagonal_pullback_counit_hom_comm F p' comm P }

/-- Helper for Lemma 4.34.1: the inverse counit component on a pullback object is the explicit
map `(𝟙, κ⁻¹)`. -/
private noncomputable def diagonal_pullback_counit_inv
    (comm : F ⋙ p' = p)
    (P : (explicitTwoFibreProduct
      (relativeDiagonalOverRaw F p' comm)
      (relativeDiagonalOverRaw F p' comm)).obj) :
    P ⟶
      ((diagonalPullbackToRelativeInertiaRaw F p' comm ⋙
          relativeInertiaToDiagonalPullbackRaw F p' comm).obj P) :=
  { base := eqToHom P.obj.fst.2.symm
    a := 𝟙 P.obj.fst.1
    a_over := IsHomLift.id_lift_eqToHom_codomain (p := p) P.obj.fst.2.symm rfl
    b := (diagonalPullbackRightIso F p' comm P).inv
    b_over := diagonal_pullback_right_component_inv_isHomLift F p' comm P
    comm := diagonal_pullback_counit_inv_comm F p' comm P }

/-- Helper for Lemma 4.34.1: composing `(𝟙, κ)` with `(𝟙, κ⁻¹)` gives the identity on the
reverse-then-forward pullback object. -/
private theorem diagonal_pullback_counit_hom_inv_id
    (comm : F ⋙ p' = p)
    (P : (explicitTwoFibreProduct
      (relativeDiagonalOverRaw F p' comm)
      (relativeDiagonalOverRaw F p' comm)).obj) :
    diagonal_pullback_counit_hom F p' comm P ≫
        diagonal_pullback_counit_inv F p' comm P =
      𝟙 ((diagonalPullbackToRelativeInertiaRaw F p' comm ⋙
          relativeInertiaToDiagonalPullbackRaw F p' comm).obj P) := by
  -- The two components compose to identities in the source category.
  apply ExplicitTwoFibreProductHom.ext
  · change 𝟙 P.obj.fst.1 ≫ 𝟙 P.obj.fst.1 = 𝟙 P.obj.fst.1
    simp
  · change (diagonalPullbackRightIso F p' comm P).hom ≫
        (diagonalPullbackRightIso F p' comm P).inv = 𝟙 P.obj.fst.1
    simpa using (diagonalPullbackRightIso F p' comm P).hom_inv_id

/-- Helper for Lemma 4.34.1: composing `(𝟙, κ⁻¹)` with `(𝟙, κ)` gives the identity on the
original pullback object. -/
private theorem diagonal_pullback_counit_inv_hom_id
    (comm : F ⋙ p' = p)
    (P : (explicitTwoFibreProduct
      (relativeDiagonalOverRaw F p' comm)
      (relativeDiagonalOverRaw F p' comm)).obj) :
    diagonal_pullback_counit_inv F p' comm P ≫
        diagonal_pullback_counit_hom F p' comm P =
      𝟙 P := by
  -- The two components compose to identities in the target category.
  apply ExplicitTwoFibreProductHom.ext
  · change 𝟙 P.obj.fst.1 ≫ 𝟙 P.obj.fst.1 = 𝟙 P.obj.fst.1
    simp
  · change (diagonalPullbackRightIso F p' comm P).inv ≫
        (diagonalPullbackRightIso F p' comm P).hom = 𝟙 P.obj.snd.1
    simpa using (diagonalPullbackRightIso F p' comm P).inv_hom_id

/-- Helper for Lemma 4.34.1: the objectwise counit component from the reverse-then-forward image
of a diagonal self-pullback object back to the original object is the textbook isomorphism
`(𝟙, κ)`. -/
private noncomputable def diagonal_pullback_counit_component_iso
    (comm : F ⋙ p' = p)
    (P : (explicitTwoFibreProduct
      (relativeDiagonalOverRaw F p' comm)
      (relativeDiagonalOverRaw F p' comm)).obj) :
    ((diagonalPullbackToRelativeInertiaRaw F p' comm ⋙
          relativeInertiaToDiagonalPullbackRaw F p' comm).obj P) ≅
      P :=
  { hom := diagonal_pullback_counit_hom F p' comm P
    inv := diagonal_pullback_counit_inv F p' comm P
    hom_inv_id := diagonal_pullback_counit_hom_inv_id F p' comm P
    inv_hom_id := diagonal_pullback_counit_inv_hom_id F p' comm P }

/-- Helper for Lemma 4.34.1: each counit component is vertical over the identity of the base
object of the pullback. -/
private theorem diagonal_pullback_counit_hom_isHomLift
    (comm : F ⋙ p' = p)
    (P : (explicitTwoFibreProduct
      (relativeDiagonalOverRaw F p' comm)
      (relativeDiagonalOverRaw F p' comm)).obj) :
    ((explicitTwoFibreProduct
      (relativeDiagonalOverRaw F p' comm)
      (relativeDiagonalOverRaw F p' comm)).p).IsHomLift
      (𝟙 P.U)
      (diagonal_pullback_counit_component_iso F p' comm P).hom := by
  -- The counit component has stored base arrow `eqToHom P.obj.fst.2`, which is exactly the
  -- source-side base identification of the composite based functor.
  exact IsHomLift.of_fac' (p := (explicitTwoFibreProduct
      (relativeDiagonalOverRaw F p' comm)
      (relativeDiagonalOverRaw F p' comm)).p)
    (𝟙 P.U)
    (diagonal_pullback_counit_component_iso F p' comm P).hom
    ((BasedFunctor.comp
        (diagonalPullbackToRelativeInertiaRaw F p' comm)
        (relativeInertiaToDiagonalPullbackRaw F p' comm)).w_obj P)
    rfl
    (by
      rw [diagonalPullback_base_projection_map]
      simpa [diagonal_pullback_counit_component_iso] using
        (show
          eqToHom P.obj.fst.2 =
            eqToHom
              ((BasedFunctor.comp
                  (diagonalPullbackToRelativeInertiaRaw F p' comm)
                  (relativeInertiaToDiagonalPullbackRaw F p' comm)).w_obj P) by
          rfl))

/-- Helper for Lemma 4.34.1: the objectwise counit components satisfy the naturality relation. -/
private theorem diagonal_pullback_counit_naturality
    (comm : F ⋙ p' = p)
    {P Q : (explicitTwoFibreProduct
      (relativeDiagonalOverRaw F p' comm)
      (relativeDiagonalOverRaw F p' comm)).obj}
    (φ : P ⟶ Q) :
    (diagonalPullbackToRelativeInertiaRaw F p' comm ⋙
        relativeInertiaToDiagonalPullbackRaw F p' comm).map φ ≫
      (diagonal_pullback_counit_component_iso F p' comm Q).hom =
        (diagonal_pullback_counit_component_iso F p' comm P).hom ≫ φ := by
  -- Naturality is trivial on the first component, and on the second component it is exactly the
  -- stored right comparison relation `κ_P ≫ φ' = φ ≫ κ_Q`.
  apply ExplicitTwoFibreProductHom.ext
  · change φ.a ≫ 𝟙 Q.obj.fst.1 = 𝟙 P.obj.fst.1 ≫ φ.a
    simp
  · change φ.a ≫ (diagonalPullbackRightIso F p' comm Q).hom =
        (diagonalPullbackRightIso F p' comm P).hom ≫ φ.b
    simpa using (diagonal_pullback_right_naturality F p' comm φ).symm

/-- Helper for Lemma 4.34.1: the textbook counit components form an ordinary natural
isomorphism on the diagonal self-pullback. -/
private noncomputable def diagonal_pullback_counit_natIso
    (comm : F ⋙ p' = p) :
    (diagonalPullbackToRelativeInertiaRaw F p' comm ⋙
        relativeInertiaToDiagonalPullbackRaw F p' comm).toFunctor ≅
      𝟭
        (explicitTwoFibreProduct
          (relativeDiagonalOverRaw F p' comm)
          (relativeDiagonalOverRaw F p' comm)).obj :=
  NatIso.ofComponents
    (fun P ↦ diagonal_pullback_counit_component_iso F p' comm P)
    (fun {_ _} φ ↦ diagonal_pullback_counit_naturality F p' comm φ)

/-- Helper for Lemma 4.34.1: the objectwise textbook counit components assemble to a natural
isomorphism on the diagonal self-pullback side. -/
private noncomputable def diagonal_pullback_counit_iso
    (comm : F ⋙ p' = p) :
    diagonalPullbackToRelativeInertiaRaw F p' comm ⋙
        relativeInertiaToDiagonalPullbackRaw F p' comm ≅
      𝟭
        (explicitTwoFibreProduct
          (relativeDiagonalOverRaw F p' comm)
          (relativeDiagonalOverRaw F p' comm)) :=
  BasedNatIso.mkNatIso
    (diagonal_pullback_counit_natIso F p' comm)
    (diagonal_pullback_counit_hom_isHomLift F p' comm)

/-- Helper for Lemma 4.34.1: after passing an inertia object through the forward comparison, the
left comparison component of the resulting diagonal self-pullback is the original automorphism. -/
private theorem relative_inertia_roundtrip_left_hom
    (comm : F ⋙ p' = p)
    (X : RelativeInertiaObject F) :
    (diagonalPullbackLeftIso F p' comm (relativeInertiaToDiagonalPullbackObj F p' comm X)).hom =
      X.α.hom := by
  -- Unfold the forward comparison object: its left component is by construction `X.α`.
  simp [diagonalPullbackLeftIso, relativeInertiaToDiagonalPullbackObj, relativeInertiaComparisonIso,
    relativeInertiaComparisonHom]

/-- Helper for Lemma 4.34.1: after the same roundtrip, the right comparison component is the
identity on the underlying source object. -/
private theorem relative_inertia_roundtrip_right_hom
    (comm : F ⋙ p' = p)
    (X : RelativeInertiaObject F) :
    (diagonalPullbackRightIso F p' comm (relativeInertiaToDiagonalPullbackObj F p' comm X)).hom =
      𝟙 X.x := by
  -- The right component of the forward comparison is the identity by definition.
  simp [diagonalPullbackRightIso, relativeInertiaToDiagonalPullbackObj,
    relativeInertiaComparisonIso, relativeInertiaComparisonHom]

/-- Helper for Lemma 4.34.1: the inverse of the roundtrip right comparison is also the identity
on the underlying source object. -/
private theorem relative_inertia_roundtrip_right_inv_eq_id
    (comm : F ⋙ p' = p)
    (X : RelativeInertiaObject F) :
    (diagonalPullbackRightIso F p' comm (relativeInertiaToDiagonalPullbackObj F p' comm X)).inv =
      𝟙 X.x := by
  -- The inverse comparison is the inverse of the identity comparison on the right component.
  change inv (𝟙 X.x) = 𝟙 X.x
  simp

/-- Helper for Lemma 4.34.1: the source-side roundtrip preserves the inertia automorphism. -/
private theorem relative_inertia_roundtrip_alpha_hom
    (comm : F ⋙ p' = p)
    (X : RelativeInertiaObject F) :
    ((diagonalPullbackToRelativeInertiaRaw F p' comm).obj
        ((relativeInertiaToDiagonalPullbackRaw F p' comm).obj X)).α.hom =
      X.α.hom := by
  -- Unfold the roundtrip automorphism as `left_hom ≫ right_inv`, then collapse the right factor.
  change
      (diagonalPullbackLeftIso F p' comm (relativeInertiaToDiagonalPullbackObj F p' comm X)).hom ≫
        (diagonalPullbackRightIso F p' comm
          (relativeInertiaToDiagonalPullbackObj F p' comm X)).inv =
      X.α.hom
  rw [relative_inertia_roundtrip_left_hom F p' comm X]
  rw [relative_inertia_roundtrip_right_inv_eq_id F p' comm X]
  exact Category.comp_id X.α.hom

/-- Helper for Lemma 4.34.1: the source-side unit morphism has underlying arrow `𝟙` and hence
intertwines the original automorphism with the roundtrip automorphism. -/
private theorem relative_inertia_unit_component_hom_comm
    (comm : F ⋙ p' = p)
    (X : RelativeInertiaObject F) :
    X.α.hom ≫ 𝟙 X.x =
      𝟙 X.x ≫
        ((diagonalPullbackToRelativeInertiaRaw F p' comm).obj
          ((relativeInertiaToDiagonalPullbackRaw F p' comm).obj X)).α.hom := by
  -- Replace the roundtrip automorphism by `X.α`.
  rw [relative_inertia_roundtrip_alpha_hom F p' comm X]
  simp

/-- Helper for Lemma 4.34.1: the inverse source-side unit morphism is also the identity on the
underlying source object. -/
private theorem relative_inertia_unit_component_inv_comm
    (comm : F ⋙ p' = p)
    (X : RelativeInertiaObject F) :
    ((diagonalPullbackToRelativeInertiaRaw F p' comm).obj
        ((relativeInertiaToDiagonalPullbackRaw F p' comm).obj X)).α.hom ≫
        𝟙 X.x =
      𝟙 X.x ≫ X.α.hom := by
  -- The same roundtrip computation identifies the target automorphism with `X.α`.
  rw [relative_inertia_roundtrip_alpha_hom F p' comm X]
  calc
    X.α.hom ≫ 𝟙 X.x = X.α.hom := Category.comp_id X.α.hom
    _ = 𝟙 X.x ≫ X.α.hom := (Category.id_comp X.α.hom).symm

/-- Helper for Lemma 4.34.1: the source-side unit component is the identity morphism of the
underlying source object. -/
private def relative_inertia_unit_component_hom
    (comm : F ⋙ p' = p)
    (X : RelativeInertiaObject F) :
    X ⟶
      (relativeInertiaToDiagonalPullbackRaw F p' comm ⋙
        diagonalPullbackToRelativeInertiaRaw F p' comm).obj X :=
  { φ := 𝟙 X.x
    comm := relative_inertia_unit_component_hom_comm F p' comm X }

/-- Helper for Lemma 4.34.1: the inverse source-side unit component is likewise the identity on
the underlying source object. -/
private def relative_inertia_unit_component_inv
    (comm : F ⋙ p' = p)
    (X : RelativeInertiaObject F) :
    (relativeInertiaToDiagonalPullbackRaw F p' comm ⋙
        diagonalPullbackToRelativeInertiaRaw F p' comm).obj X ⟶
      X :=
  { φ := 𝟙 X.x
    comm := relative_inertia_unit_component_inv_comm F p' comm X }

/-- Helper for Lemma 4.34.1: the two identity-shaped source-side unit components compose to the
identity on the original inertia object. -/
private theorem relative_inertia_unit_component_hom_inv_id
    (comm : F ⋙ p' = p)
    (X : RelativeInertiaObject F) :
    relative_inertia_unit_component_hom F p' comm X ≫
        relative_inertia_unit_component_inv F p' comm X =
      𝟙 X := by
  -- Equality is detected on the underlying source arrow.
  apply RelativeInertiaHom.ext
  change 𝟙 X.x ≫ 𝟙 X.x = 𝟙 X.x
  simp

/-- Helper for Lemma 4.34.1: the opposite composite of the source-side unit components is the
identity on the roundtrip inertia object. -/
private theorem relative_inertia_unit_component_inv_hom_id
    (comm : F ⋙ p' = p)
    (X : RelativeInertiaObject F) :
    relative_inertia_unit_component_inv F p' comm X ≫
        relative_inertia_unit_component_hom F p' comm X =
      𝟙 ((relativeInertiaToDiagonalPullbackRaw F p' comm ⋙
          diagonalPullbackToRelativeInertiaRaw F p' comm).obj X) := by
  -- Equality is again detected on the underlying source arrow.
  apply RelativeInertiaHom.ext
  change 𝟙 X.x ≫ 𝟙 X.x = 𝟙 X.x
  simp

/-- Helper for Lemma 4.34.1: the source-side roundtrip isomorphism is the identity on the
underlying object and automorphism of each inertia object. -/
private noncomputable def relative_inertia_unit_component_iso
    (comm : F ⋙ p' = p)
    (X : RelativeInertiaObject F) :
    X ≅ (relativeInertiaToDiagonalPullbackRaw F p' comm ⋙
      diagonalPullbackToRelativeInertiaRaw F p' comm).obj X :=
  { hom := relative_inertia_unit_component_hom F p' comm X
    inv := relative_inertia_unit_component_inv F p' comm X
    hom_inv_id := relative_inertia_unit_component_hom_inv_id F p' comm X
    inv_hom_id := relative_inertia_unit_component_inv_hom_id F p' comm X }

/-- Helper for Lemma 4.34.1: the source-side unit components are natural because the
forward-then-reverse roundtrip does not change the underlying source arrow. -/
private theorem relative_inertia_unit_naturality
    (comm : F ⋙ p' = p)
    {X Y : RelativeInertiaObject F}
    (f : X ⟶ Y) :
    (𝟭 (BasedCategory.ofFunctor (relativeInertiaProjection F p))).map f ≫
        (relative_inertia_unit_component_iso F p' comm Y).hom =
      (relative_inertia_unit_component_iso F p' comm X).hom ≫
        (relativeInertiaToDiagonalPullbackRaw F p' comm ⋙
          diagonalPullbackToRelativeInertiaRaw F p' comm).map f := by
  -- The roundtrip map keeps the underlying morphism `f.φ`.
  apply RelativeInertiaHom.ext
  change f.φ ≫ 𝟙 Y.x = 𝟙 X.x ≫ f.φ
  simp

/-- Helper for Lemma 4.34.1: the source-side unit is the ordinary identity natural isomorphism
on the relative inertia category. -/
private noncomputable def relative_inertia_unit_natIso
    (comm : F ⋙ p' = p) :
    (𝟭 (BasedCategory.ofFunctor (relativeInertiaProjection F p))).toFunctor ≅
      (relativeInertiaToDiagonalPullbackRaw F p' comm ⋙
        diagonalPullbackToRelativeInertiaRaw F p' comm).toFunctor :=
  NatIso.ofComponents
    (fun X ↦ relative_inertia_unit_component_iso F p' comm X)
    (fun {_ _} f ↦ relative_inertia_unit_naturality F p' comm f)

/-- Helper for Lemma 4.34.1: each source-side unit component is vertical over the identity on
the corresponding base object. -/
private theorem relative_inertia_unit_component_isHomLift
    (comm : F ⋙ p' = p)
    (X : RelativeInertiaObject F) :
    (relativeInertiaProjection F p).IsHomLift (𝟙 (p.obj X.x))
      ((relative_inertia_unit_natIso F p' comm).hom.app X) := by
  -- Each source-side unit component is literally the identity on the underlying source object.
  change (relativeInertiaProjection F p).IsHomLift (𝟙 (p.obj X.x))
    (relative_inertia_unit_component_hom F p' comm X)
  -- Repackage the identity-shaped component over the displayed target base equality of the
  -- source-side roundtrip based functor.
  refine
    IsHomLift.of_fac' (relativeInertiaProjection F p) (𝟙 (p.obj X.x))
      (relative_inertia_unit_component_hom F p' comm X) rfl
      ((BasedFunctor.comp
          (relativeInertiaToDiagonalPullbackRaw F p' comm)
          (diagonalPullbackToRelativeInertiaRaw F p' comm)).w_obj X) ?_
  have hunit : p.IsHomLift (𝟙 (p.obj X.x)) (𝟙 X.x) := by infer_instance
  letI := hunit
  have hdom :
      IsHomLift.domain_eq p (𝟙 (p.obj X.x)) (𝟙 X.x) = rfl := by
    apply Subsingleton.elim
  have hcod :
      IsHomLift.codomain_eq p (𝟙 (p.obj X.x)) (𝟙 X.x) =
        ((BasedFunctor.comp
            (relativeInertiaToDiagonalPullbackRaw F p' comm)
            (diagonalPullbackToRelativeInertiaRaw F p' comm)).w_obj X) := by
    apply Subsingleton.elim
  change p.map (𝟙 X.x) =
    eqToHom rfl ≫ 𝟙 (p.obj X.x) ≫
      eqToHom
        ((BasedFunctor.comp
            (relativeInertiaToDiagonalPullbackRaw F p' comm)
            (diagonalPullbackToRelativeInertiaRaw F p' comm)).w_obj X).symm
  rw [← hdom, ← hcod]
  exact IsHomLift.fac' p (𝟙 (p.obj X.x)) (𝟙 X.x)

/-- Helper for Lemma 4.34.1: the source-side unit is a based natural isomorphism. -/
private noncomputable def relative_inertia_unit_iso
    (comm : F ⋙ p' = p) :
    𝟭 (BasedCategory.ofFunctor (relativeInertiaProjection F p)) ≅
      relativeInertiaToDiagonalPullbackRaw F p' comm ⋙
        diagonalPullbackToRelativeInertiaRaw F p' comm :=
  -- Package the definitional source-side identity as a based natural isomorphism.
  BasedNatIso.mkNatIso
    (relative_inertia_unit_natIso F p' comm)
    (relative_inertia_unit_component_isHomLift F p' comm)

/-- Internal bare-functor form of Lemma 4.34.1. The public over-base statement is the bundled
owner theorem `BasedFunctor.relativeInertiaEquivalenceOverBase`. -/
private theorem relativeInertiaEquivalenceOverBaseRaw
    (comm : F ⋙ p' = p) :
    (relativeInertiaToDiagonalPullbackRaw F p' comm).IsEquivalenceOverBase := by
  -- The source-side unit is definitional, and the pullback-side counit is the packaged textbook
  -- comparison `(𝟙, κ)`.
  refine BasedFunctor.IsEquivalenceOverBase.mkPrime
    (diagonalPullbackToRelativeInertiaRaw F p' comm)
    (relative_inertia_unit_iso F p' comm)
    (diagonal_pullback_counit_iso F p' comm)

namespace BasedFunctor

variable {X Y : CategoryOver C}

/-- The canonical diagonal morphism in `Cat/C` attached to a bundled morphism over `C`. Its target
is the explicit self-`2`-fibre product `X ×_Y X`. -/
def relativeDiagonalOver (F : X ⥤ᵇ Y) :
    X ⥤ᵇ explicitTwoFibreProduct F F :=
  relativeDiagonalOverRaw F.toFunctor Y.p F.w

/-- The canonical comparison morphism in `Cat/C` from the relative inertia over `C` of a bundled
morphism `F` to the explicit self-`2`-fibre product of its diagonal. -/
def relativeInertiaToDiagonalPullback (F : X ⥤ᵇ Y) :
    BasedCategory.ofFunctor (relativeInertiaProjection F.toFunctor X.p) ⥤ᵇ
      explicitTwoFibreProduct (relativeDiagonalOver F) (relativeDiagonalOver F) :=
  relativeInertiaToDiagonalPullbackRaw F.toFunctor Y.p F.w

-- Proof sketch: this is the bundled over-`C` restatement of the internal bare-functor comparison
-- theorem above, with the commutativity proof supplied canonically by `F.w`.
/-- Lemma 4.34.1: for a morphism `F : X ⟶ Y` in `Cat/C`, the relative inertia of `F` over `C` is
equivalent over `C` to the explicit self-`2`-fibre product of the canonical diagonal
`X ⟶ X ×_Y X`. -/
theorem relativeInertiaEquivalenceOverBase (F : X ⥤ᵇ Y) :
    (relativeInertiaToDiagonalPullback F).IsEquivalenceOverBase :=
  relativeInertiaEquivalenceOverBaseRaw F.toFunctor Y.p F.w

end BasedFunctor

namespace FibredInGroupoidsMor

section

variable {C : Type (max u₁ v)} [Category.{v} C]
variable {X Y : FibredInGroupoidsOver.{v, max u₁ v, max u₁ v, v} C}

/-- The canonical self-`2`-fibre-product target of the diagonal of a morphism of categories
fibred in groupoids over `C`, obtained by rebundling the explicit pullback model in `Cat/C`. -/
theorem diagonalTargetProjection_isFibredInGroupoids
    (F : X ⟶ Y) :
    IsFibredInGroupoids
      (explicitTwoFibreProduct
        (FibredInGroupoidsMor.toBasedFunctor F)
        (FibredInGroupoidsMor.toBasedFunctor F)).p := by
  -- Route correction: use the already-imported explicit pullback theorem for fibred-in-groupoids
  -- targets rather than rebuilding the groupoid-fibre argument locally a second time.
  exact explicitTwoFibreProductProjection_isFibredInGroupoids
    (FibredInGroupoidsMor.toBasedFunctor F)
    (FibredInGroupoidsMor.toBasedFunctor F)

/-- The canonical target of the diagonal of a morphism of categories fibred in groupoids over
`C`, obtained by rebundling the explicit self-`2`-fibre product in `Cat/C`. -/
abbrev diagonalTarget (F : X ⟶ Y) : FibredInGroupoidsOver C :=
  letI := diagonalTargetProjection_isFibredInGroupoids F
  FibredInGroupoidsOver.ofFunctor <|
    (explicitTwoFibreProduct
      (FibredInGroupoidsMor.toBasedFunctor F)
      (FibredInGroupoidsMor.toBasedFunctor F)).p

/-- The canonical diagonal morphism attached to a morphism of categories fibred in groupoids over
`C`. -/
abbrev diagonalMor (F : X ⟶ Y) : X ⟶ diagonalTarget F :=
  letI := diagonalTargetProjection_isFibredInGroupoids F
  FibredInGroupoidsMor.ofBasedFunctor <|
    BasedFunctor.relativeDiagonalOver (FibredInGroupoidsMor.toBasedFunctor F)

end

end FibredInGroupoidsMor

namespace FibredInGroupoidsOver

section

variable {C : Type (max u₁ v)} [Category.{v} C]
variable (X : FibredInGroupoidsOver.{v, max u₁ v, max u₁ v, v} C)

/-- The canonical diagonal of the base projection of a bundled category fibred in groupoids over
`C`. This is the object-prefix bridge to the owner morphism `X.baseProjection.diagonalMor`. -/
abbrev baseProjectionDiagonalMor :=
  FibredInGroupoidsMor.diagonalMor X.baseProjection

end

end FibredInGroupoidsOver

/-- Helper for Lemma 4.34.1: a morphism of fibred categories preserves strong cartesianness over
the chosen base arrow, not only over the projected base map. -/
private theorem map_stronglyCartesian_over_base
    {C : Type u₁} [Category.{v} C]
    {X Y : FibredCategoryOver C} (F : X ⟶ Y)
    {U V : C} {a b : X.S} {f : U ⟶ V} {φ : a ⟶ b}
    (hφ : X.p.IsStronglyCartesian f φ) :
    Y.p.IsStronglyCartesian f ((FibredCategoryMor.toFunctor F).map φ) := by
  -- Rebase the source lift to its projected base arrow so the owner preservation theorem applies.
  have hφ' : X.p.IsStronglyCartesian (X.p.map φ) φ := by
    letI : X.p.IsStronglyCartesian f φ := hφ
    subst_hom_lift X.p f φ
    simpa using hφ
  have hmap :
      Y.p.IsStronglyCartesian (Y.p.map ((FibredCategoryMor.toFunctor F).map φ))
        ((FibredCategoryMor.toFunctor F).map φ) :=
    FibredCategoryMor.map_stronglyCartesian F φ hφ'
  -- Then transport the mapped lift back to the original chosen base arrow `f`.
  have hLift : Y.p.IsHomLift f ((FibredCategoryMor.toFunctor F).map φ) := by
    letI : X.p.IsHomLift f φ := hφ.toIsHomLift
    exact show Y.p.IsHomLift f ((FibredCategoryMor.toFunctor F).map φ) from inferInstance
  letI : Y.p.IsHomLift f ((FibredCategoryMor.toFunctor F).map φ) := hLift
  subst_hom_lift Y.p f ((FibredCategoryMor.toFunctor F).map φ)
  simpa using hmap

/-- Helper for Lemma 4.34.1: the projection from the explicit self-pullback of a fibred morphism
reads off the stored `base` field of a morphism. -/
private theorem self_pullback_base_projection_map
    {C : Type u₁} [Category.{v} C]
    {X Y : FibredCategoryOver C} (F : X ⟶ Y)
    {P Q : (explicitTwoFibreProduct
      (FibredCategoryMor.toBasedFunctor F)
      (FibredCategoryMor.toBasedFunctor F)).obj}
    (φ : P ⟶ Q) :
    (explicitTwoFibreProduct
      (FibredCategoryMor.toBasedFunctor F)
      (FibredCategoryMor.toBasedFunctor F)).p.map φ = φ.base := by
  rfl

/-- Helper for Lemma 4.34.1: a lift in the explicit self-pullback has base arrow equal to the
stored `base` field of that pullback morphism. -/
private theorem self_pullback_base_eq_of_isHomLift
    {C : Type u₁} [Category.{v} C]
    {X Y : FibredCategoryOver C} (F : X ⟶ Y)
    {P Q : (explicitTwoFibreProduct
      (FibredCategoryMor.toBasedFunctor F)
      (FibredCategoryMor.toBasedFunctor F)).obj}
    {f : P.U ⟶ Q.U} (φ : P ⟶ Q)
    (hφ : (explicitTwoFibreProduct
      (FibredCategoryMor.toBasedFunctor F)
      (FibredCategoryMor.toBasedFunctor F)).p.IsHomLift f φ) :
    φ.base = f := by
  let q := (explicitTwoFibreProduct
    (FibredCategoryMor.toBasedFunctor F)
    (FibredCategoryMor.toBasedFunctor F)).p
  have h : f = q.map φ := @IsHomLift.eq_of_isHomLift _ _ _ _ q _ _ f φ hφ
  simpa [q, self_pullback_base_projection_map F φ] using h.symm

/-- Helper for Lemma 4.34.1: a lift in the explicit self-pullback induces the corresponding lift
on the left component over the same base arrow. -/
private theorem self_pullback_left_isHomLift_of_isHomLift
    {C : Type u₁} [Category.{v} C]
    {X Y : FibredCategoryOver C} (F : X ⟶ Y)
    {P Q : (explicitTwoFibreProduct
      (FibredCategoryMor.toBasedFunctor F)
      (FibredCategoryMor.toBasedFunctor F)).obj}
    {f : P.U ⟶ Q.U} (φ : P ⟶ Q)
    (hφ : (explicitTwoFibreProduct
      (FibredCategoryMor.toBasedFunctor F)
      (FibredCategoryMor.toBasedFunctor F)).p.IsHomLift f φ) :
    X.p.IsHomLift f φ.a := by
  have hbase : φ.base = f := self_pullback_base_eq_of_isHomLift F φ hφ
  rw [← hbase]
  simpa using (φ.a_over : X.p.IsHomLift φ.base φ.a)

/-- Helper for Lemma 4.34.1: a lift in the explicit self-pullback induces the corresponding lift
on the right component over the same base arrow. -/
private theorem self_pullback_right_isHomLift_of_isHomLift
    {C : Type u₁} [Category.{v} C]
    {X Y : FibredCategoryOver C} (F : X ⟶ Y)
    {P Q : (explicitTwoFibreProduct
      (FibredCategoryMor.toBasedFunctor F)
      (FibredCategoryMor.toBasedFunctor F)).obj}
    {f : P.U ⟶ Q.U} (φ : P ⟶ Q)
    (hφ : (explicitTwoFibreProduct
      (FibredCategoryMor.toBasedFunctor F)
      (FibredCategoryMor.toBasedFunctor F)).p.IsHomLift f φ) :
    X.p.IsHomLift f φ.b := by
  have hbase : φ.base = f := self_pullback_base_eq_of_isHomLift F φ hφ
  rw [← hbase]
  simpa using (φ.b_over : X.p.IsHomLift φ.base φ.b)

/-- Helper for Lemma 4.34.1: a morphism in the explicit self-pullback of a fibred morphism is
strongly cartesian whenever both source components are strongly cartesian over the same base
arrow. -/
private theorem self_pullback_hom_isStronglyCartesian_of_components
    {C : Type u₁} [Category.{v} C]
    {X Y : FibredCategoryOver C} (F : X ⟶ Y)
    {P Q : (explicitTwoFibreProduct
      (FibredCategoryMor.toBasedFunctor F)
      (FibredCategoryMor.toBasedFunctor F)).obj}
    (η : P ⟶ Q)
    (ha : X.p.IsStronglyCartesian η.base η.a)
    (hb : X.p.IsStronglyCartesian η.base η.b) :
    (explicitTwoFibreProduct
      (FibredCategoryMor.toBasedFunctor F)
      (FibredCategoryMor.toBasedFunctor F)).p.IsStronglyCartesian
      η.base η := by
  letI : X.p.IsStronglyCartesian η.base η.a := ha
  letI : X.p.IsStronglyCartesian η.base η.b := hb
  refine
    { toIsHomLift := by
        change (explicitTwoFibreProduct
          (FibredCategoryMor.toBasedFunctor F)
          (FibredCategoryMor.toBasedFunctor F)).p.IsHomLift
          ((explicitTwoFibreProduct
            (FibredCategoryMor.toBasedFunctor F)
            (FibredCategoryMor.toBasedFunctor F)).p.map η) η
        infer_instance
      universal_property' := ?_ }
  intro R g ψ hψ
  letI :
      (explicitTwoFibreProduct
        (FibredCategoryMor.toBasedFunctor F)
        (FibredCategoryMor.toBasedFunctor F)).p.IsHomLift
        (g ≫ η.base) ψ := hψ
  have hψa : X.p.IsHomLift (g ≫ η.base) ψ.a := by
    exact self_pullback_left_isHomLift_of_isHomLift F (f := g ≫ η.base) ψ hψ
  have hψb : X.p.IsHomLift (g ≫ η.base) ψ.b := by
    exact self_pullback_right_isHomLift_of_isHomLift F (f := g ≫ η.base) ψ hψ
  -- Factor each component through the chosen strongly cartesian lift.
  letI : X.p.IsHomLift (g ≫ η.base) ψ.a := hψa
  obtain ⟨χa, hχa, hχa_uniq⟩ :=
    Functor.IsStronglyCartesian.universal_property X.p η.base η.a g (g ≫ η.base) rfl ψ.a
  have hχa_over : X.p.IsHomLift g χa := hχa.1
  have hχa_fac : χa ≫ η.a = ψ.a := hχa.2
  letI : X.p.IsHomLift (g ≫ η.base) ψ.b := hψb
  obtain ⟨χb, hχb, hχb_uniq⟩ :=
    Functor.IsStronglyCartesian.universal_property X.p η.base η.b g (g ≫ η.base) rfl ψ.b
  have hχb_over : X.p.IsHomLift g χb := hχb.1
  have hχb_fac : χb ≫ η.b = ψ.b := hχb.2
  have hmap_b :
      Y.p.IsStronglyCartesian η.base ((FibredCategoryMor.toFunctor F).map η.b) := by
    exact map_stronglyCartesian_over_base F hb
  letI : Y.p.IsStronglyCartesian η.base ((FibredCategoryMor.toFunctor F).map η.b) := hmap_b
  have hleft_over :
      Y.p.IsHomLift g ((FibredCategoryMor.toFunctor F).map χa ≫ P.comparison) := by
    -- Map the left factorization into `Y`, then append the vertical comparison of `P`.
    have hFχa : Y.p.IsHomLift g ((FibredCategoryMor.toFunctor F).map χa) := by
      infer_instance
    letI : Y.p.IsHomLift g ((FibredCategoryMor.toFunctor F).map χa) := hFχa
    letI : Y.p.IsHomLift (𝟙 P.U) P.comparison := P.comparison_over
    exact
      IsHomLift.comp_lift_id_right' (p := Y.p) g
        ((FibredCategoryMor.toFunctor F).map χa) P.U P.comparison
  have hright_over :
      Y.p.IsHomLift g (R.comparison ≫ (FibredCategoryMor.toFunctor F).map χb) := by
    -- Do the same on the right, now precomposing with the vertical comparison of `R`.
    have hFχb : Y.p.IsHomLift g ((FibredCategoryMor.toFunctor F).map χb) := by
      infer_instance
    letI : Y.p.IsHomLift g ((FibredCategoryMor.toFunctor F).map χb) := hFχb
    letI : Y.p.IsHomLift (𝟙 R.U) R.comparison := R.comparison_over
    exact
      IsHomLift.comp_lift_id_left' (p := Y.p) R.U R.comparison g
        ((FibredCategoryMor.toFunctor F).map χb)
  have hcomm_after_comp :
      ((FibredCategoryMor.toFunctor F).map χa ≫ P.comparison) ≫
          (FibredCategoryMor.toFunctor F).map η.b =
        (R.comparison ≫ (FibredCategoryMor.toFunctor F).map χb) ≫
          (FibredCategoryMor.toFunctor F).map η.b := by
    -- Both candidate comparison squares become the same after composing with `F.map η.b`.
    calc
      ((FibredCategoryMor.toFunctor F).map χa ≫ P.comparison) ≫
            (FibredCategoryMor.toFunctor F).map η.b
          = (FibredCategoryMor.toFunctor F).map χa ≫
              ((FibredCategoryMor.toFunctor F).map η.a ≫ Q.comparison) := by
                rw [η.comm.w]
                simp [Category.assoc]
      _ = (FibredCategoryMor.toFunctor F).map (χa ≫ η.a) ≫ Q.comparison := by
            simp [Functor.map_comp, Category.assoc]
      _ = (FibredCategoryMor.toFunctor F).map ψ.a ≫ Q.comparison := by
            rw [hχa_fac]
      _ = R.comparison ≫ (FibredCategoryMor.toFunctor F).map ψ.b := by
            exact ψ.comm.w
      _ = R.comparison ≫ (FibredCategoryMor.toFunctor F).map (χb ≫ η.b) := by
            rw [hχb_fac]
      _ = (R.comparison ≫ (FibredCategoryMor.toFunctor F).map χb) ≫
            (FibredCategoryMor.toFunctor F).map η.b := by
              simp [Functor.map_comp, Category.assoc]
  have hcomm :
      (FibredCategoryMor.toFunctor F).map χa ≫ P.comparison =
        R.comparison ≫ (FibredCategoryMor.toFunctor F).map χb := by
    -- Cancel the mapped strongly cartesian arrow `F.map η.b`.
    apply Functor.IsStronglyCartesian.ext (p := Y.p) (f := η.base)
      ((FibredCategoryMor.toFunctor F).map η.b) g
    simpa [Category.assoc] using hcomm_after_comp
  let χ : R ⟶ P :=
    { base := g
      a := χa
      a_over := hχa_over
      b := χb
      b_over := hχb_over
      comm := ⟨hcomm⟩ }
  refine ⟨χ, ⟨?_, ?_⟩, ?_⟩
  · -- The assembled morphism is itself a lift over `g`.
    change (explicitTwoFibreProduct
      (FibredCategoryMor.toBasedFunctor F)
      (FibredCategoryMor.toBasedFunctor F)).p.IsHomLift
      ((explicitTwoFibreProduct
        (FibredCategoryMor.toBasedFunctor F)
        (FibredCategoryMor.toBasedFunctor F)).p.map χ) χ
    infer_instance
  · -- The chosen left and right factorizations recover the original pullback morphism `ψ`.
    apply ExplicitTwoFibreProductHom.ext
    · simpa [χ] using hχa_fac
    · simpa [χ] using hχb_fac
  · intro χ' hχ'
    rcases hχ' with ⟨hχ'_over, hχ'_fac⟩
    letI :
        (explicitTwoFibreProduct
          (FibredCategoryMor.toBasedFunctor F)
          (FibredCategoryMor.toBasedFunctor F)).p.IsHomLift g χ' := hχ'_over
    have hχ'a : X.p.IsHomLift g χ'.a := by
      exact self_pullback_left_isHomLift_of_isHomLift F (f := g) χ' hχ'_over
    have hχ'b : X.p.IsHomLift g χ'.b := by
      exact self_pullback_right_isHomLift_of_isHomLift F (f := g) χ' hχ'_over
    -- Uniqueness is checked componentwise via the two source strongly cartesian morphisms.
    apply ExplicitTwoFibreProductHom.ext
    · exact hχa_uniq χ'.a ⟨hχ'a, by simpa using congrArg ExplicitTwoFibreProductHom.a hχ'_fac⟩
    · exact hχb_uniq χ'.b ⟨hχ'b, by simpa using congrArg ExplicitTwoFibreProductHom.b hχ'_fac⟩

/-- Helper for Lemma 4.34.1: the comparison stored in an explicit self-pullback object is an
isomorphism in the total category of the target fibred category. -/
private theorem self_pullback_comparison_isIso
    {C : Type u₁} [Category.{v} C]
    {X Y : FibredCategoryOver C} (F : X ⟶ Y)
    (P : (explicitTwoFibreProduct
      (FibredCategoryMor.toBasedFunctor F)
      (FibredCategoryMor.toBasedFunctor F)).obj) :
    IsIso P.comparison := by
  -- Forget the fiberwise comparison isomorphism carried by `P` to the ambient total category.
  let e :
      (FibredCategoryMor.toFunctor F).obj P.obj.fst.1 ≅
        (FibredCategoryMor.toFunctor F).obj P.obj.snd.1 :=
    { hom := P.comparison
      inv := P.obj.iso.inv.1
      hom_inv_id := by
        exact congrArg Subtype.val P.obj.iso.hom_inv_id
      inv_hom_id := by
        exact congrArg Subtype.val P.obj.iso.inv_hom_id }
  exact ⟨e.inv, e.hom_inv_id, e.inv_hom_id⟩

/-- Helper for Lemma 4.34.1: the chosen pullback of the left component of a self-pullback object
along a base arrow, viewed in the fiber over the new source. -/
private noncomputable def self_pullback_left_pullback
    {C : Type u₁} [Category.{v} C]
    {X Y : FibredCategoryOver C} (F : X ⟶ Y)
    (P : (explicitTwoFibreProduct
      (FibredCategoryMor.toBasedFunctor F)
      (FibredCategoryMor.toBasedFunctor F)).obj)
    {V : C} (f : V ⟶ P.U) :
    X.p.Fiber V :=
  let _ : HasFibers X.p := HasFibers.canonical X.p
  let a := HasFibers.pullbackMap (p := X.p) f P.obj.fst.2
  Functor.Fiber.mk (IsHomLift.domain_eq X.p f a)

/-- Helper for Lemma 4.34.1: the canonical pullback map from the left pulled-back component to
the original left component. -/
private noncomputable def self_pullback_left_pullback_map
    {C : Type u₁} [Category.{v} C]
    {X Y : FibredCategoryOver C} (F : X ⟶ Y)
    (P : (explicitTwoFibreProduct
      (FibredCategoryMor.toBasedFunctor F)
      (FibredCategoryMor.toBasedFunctor F)).obj)
    {V : C} (f : V ⟶ P.U) :
    (self_pullback_left_pullback F P f).1 ⟶ P.obj.fst.1 :=
  let _ : HasFibers X.p := HasFibers.canonical X.p
  let a := HasFibers.pullbackMap (p := X.p) f P.obj.fst.2
  show (self_pullback_left_pullback F P f).1 ⟶ P.obj.fst.1 from a

/-- Helper for Lemma 4.34.1: the chosen pullback of the right component of a self-pullback object
along a base arrow, viewed in the fiber over the new source. -/
private noncomputable def self_pullback_right_pullback
    {C : Type u₁} [Category.{v} C]
    {X Y : FibredCategoryOver C} (F : X ⟶ Y)
    (P : (explicitTwoFibreProduct
      (FibredCategoryMor.toBasedFunctor F)
      (FibredCategoryMor.toBasedFunctor F)).obj)
    {V : C} (f : V ⟶ P.U) :
    X.p.Fiber V :=
  let _ : HasFibers X.p := HasFibers.canonical X.p
  let b := HasFibers.pullbackMap (p := X.p) f P.obj.snd.2
  Functor.Fiber.mk (IsHomLift.domain_eq X.p f b)

/-- Helper for Lemma 4.34.1: the canonical pullback map from the right pulled-back component to
the original right component. -/
private noncomputable def self_pullback_right_pullback_map
    {C : Type u₁} [Category.{v} C]
    {X Y : FibredCategoryOver C} (F : X ⟶ Y)
    (P : (explicitTwoFibreProduct
      (FibredCategoryMor.toBasedFunctor F)
      (FibredCategoryMor.toBasedFunctor F)).obj)
    {V : C} (f : V ⟶ P.U) :
    (self_pullback_right_pullback F P f).1 ⟶ P.obj.snd.1 :=
  let _ : HasFibers X.p := HasFibers.canonical X.p
  let b := HasFibers.pullbackMap (p := X.p) f P.obj.snd.2
  show (self_pullback_right_pullback F P f).1 ⟶ P.obj.snd.1 from b

/-- Helper for Lemma 4.34.1: pulling back both components of a self-pullback object along `f`
reconstructs the unique comparison isomorphism in the target fiber over the new base. -/
private noncomputable def self_pullback_pulledback_comparison_iso
    {C : Type u₁} [Category.{v} C]
    {X Y : FibredCategoryOver C} (F : X ⟶ Y)
    (P : (explicitTwoFibreProduct
      (FibredCategoryMor.toBasedFunctor F)
      (FibredCategoryMor.toBasedFunctor F)).obj)
    {V : C} (f : V ⟶ P.U) :
    ((FibredCategoryMor.toBasedFunctor F).fiberFunctor V).obj
        (self_pullback_left_pullback F P f) ≅
      ((FibredCategoryMor.toBasedFunctor F).fiberFunctor V).obj
        (self_pullback_right_pullback F P f) := by
  let _ : HasFibers X.p := HasFibers.canonical X.p
  let a := self_pullback_left_pullback_map F P f
  let b := self_pullback_right_pullback_map F P f
  -- The chosen component pullback maps are strongly cartesian in the source fibred category.
  have ha_cart : X.p.IsCartesian f a := by
    change X.p.IsCartesian f (HasFibers.pullbackMap (p := X.p) f P.obj.fst.2)
    infer_instance
  have hb_cart : X.p.IsCartesian f b := by
    change X.p.IsCartesian f (HasFibers.pullbackMap (p := X.p) f P.obj.snd.2)
    infer_instance
  have ha : X.p.IsStronglyCartesian f a :=
    Functor.IsFibered.isStronglyCartesian_of_isCartesian X.p f a
  have hb : X.p.IsStronglyCartesian f b :=
    Functor.IsFibered.isStronglyCartesian_of_isCartesian X.p f b
  -- Mapping these lifts into `Y` gives the two target-side lifts to compare.
  have hFa : Y.p.IsStronglyCartesian f ((FibredCategoryMor.toFunctor F).map a) :=
    map_stronglyCartesian_over_base F ha
  have hFb : Y.p.IsStronglyCartesian f ((FibredCategoryMor.toFunctor F).map b) :=
    map_stronglyCartesian_over_base F hb
  letI : IsIso P.comparison := self_pullback_comparison_isIso F P
  letI : Y.p.IsHomLift (𝟙 P.U) P.comparison := P.comparison_over
  have hcomparison : Y.p.IsStronglyCartesian (𝟙 P.U) P.comparison :=
    Functor.IsStronglyCartesian.of_isIso Y.p (𝟙 P.U) P.comparison
  have hleft :
      Y.p.IsStronglyCartesian f ((FibredCategoryMor.toFunctor F).map a ≫ P.comparison) := by
    letI : Y.p.IsStronglyCartesian f ((FibredCategoryMor.toFunctor F).map a) := hFa
    letI : Y.p.IsStronglyCartesian (𝟙 P.U) P.comparison := hcomparison
    simpa using
      (show Y.p.IsStronglyCartesian (f ≫ 𝟙 P.U)
          ((FibredCategoryMor.toFunctor F).map a ≫ P.comparison) from inferInstance)
  letI : Y.p.IsStronglyCartesian f ((FibredCategoryMor.toFunctor F).map b) := hFb
  letI : Y.p.IsStronglyCartesian f ((FibredCategoryMor.toFunctor F).map a ≫ P.comparison) :=
    hleft
  let e :=
    Functor.IsStronglyCartesian.domainIsoOfBaseIso
      Y.p
      (g := Iso.refl V)
      (show f = (Iso.refl V).hom ≫ f by simp)
      ((FibredCategoryMor.toFunctor F).map b)
      ((FibredCategoryMor.toFunctor F).map a ≫ P.comparison)
  have hhom : Y.p.IsHomLift (𝟙 V) e.hom := by
    simpa [e] using
      (show Y.p.IsHomLift (Iso.refl V).hom e.hom from inferInstance)
  have hinv : Y.p.IsHomLift (𝟙 V) e.inv := by
    simpa [e] using
      (show Y.p.IsHomLift (Iso.refl V).inv e.inv from inferInstance)
  -- Package the resulting domain comparison back into the standard fiber over `V`.
  refine
    { hom := Functor.Fiber.homMk Y.p V e.hom
      inv := Functor.Fiber.homMk Y.p V e.inv
      hom_inv_id := by
        apply Functor.Fiber.hom_ext
        exact e.hom_inv_id
      inv_hom_id := by
        apply Functor.Fiber.hom_ext
        exact e.inv_hom_id }

/-- Helper for Lemma 4.34.1: every base arrow into the explicit self-pullback of `F` admits the
canonical strongly cartesian pullback morphism obtained by pulling back both source components. -/
private theorem self_pullback_exists_isStronglyCartesian
    {C : Type u₁} [Category.{v} C]
    {X Y : FibredCategoryOver C} (F : X ⟶ Y)
    (P : (explicitTwoFibreProduct
      (FibredCategoryMor.toBasedFunctor F)
      (FibredCategoryMor.toBasedFunctor F)).obj)
    {V : C} (f : V ⟶ P.U) :
    ∃ Q : (explicitTwoFibreProduct
      (FibredCategoryMor.toBasedFunctor F)
      (FibredCategoryMor.toBasedFunctor F)).obj,
      ∃ η : Q ⟶ P,
        (explicitTwoFibreProduct
          (FibredCategoryMor.toBasedFunctor F)
          (FibredCategoryMor.toBasedFunctor F)).p.IsStronglyCartesian f η := by
  let _ : HasFibers X.p := HasFibers.canonical X.p
  let a := self_pullback_left_pullback_map F P f
  let b := self_pullback_right_pullback_map F P f
  -- Pull back the two source components of `P` along `f`.
  let Q : (explicitTwoFibreProduct
      (FibredCategoryMor.toBasedFunctor F)
      (FibredCategoryMor.toBasedFunctor F)).obj :=
    { U := V
      obj :=
        { fst := self_pullback_left_pullback F P f
          snd := self_pullback_right_pullback F P f
          iso := self_pullback_pulledback_comparison_iso F P f } }
  have ha_over : X.p.IsHomLift f a := by
    change X.p.IsHomLift f (HasFibers.pullbackMap (p := X.p) f P.obj.fst.2)
    infer_instance
  have hb_over : X.p.IsHomLift f b := by
    change X.p.IsHomLift f (HasFibers.pullbackMap (p := X.p) f P.obj.snd.2)
    infer_instance
  have ha_cart : X.p.IsCartesian f a := by
    change X.p.IsCartesian f (HasFibers.pullbackMap (p := X.p) f P.obj.fst.2)
    infer_instance
  have hb_cart : X.p.IsCartesian f b := by
    change X.p.IsCartesian f (HasFibers.pullbackMap (p := X.p) f P.obj.snd.2)
    infer_instance
  have ha : X.p.IsStronglyCartesian f a :=
    Functor.IsFibered.isStronglyCartesian_of_isCartesian X.p f a
  have hb : X.p.IsStronglyCartesian f b :=
    Functor.IsFibered.isStronglyCartesian_of_isCartesian X.p f b
  have hFa : Y.p.IsStronglyCartesian f ((FibredCategoryMor.toFunctor F).map a) :=
    map_stronglyCartesian_over_base F ha
  have hFb : Y.p.IsStronglyCartesian f ((FibredCategoryMor.toFunctor F).map b) :=
    map_stronglyCartesian_over_base F hb
  letI : IsIso P.comparison := self_pullback_comparison_isIso F P
  letI : Y.p.IsHomLift (𝟙 P.U) P.comparison := P.comparison_over
  have hcomparison : Y.p.IsStronglyCartesian (𝟙 P.U) P.comparison :=
    Functor.IsStronglyCartesian.of_isIso Y.p (𝟙 P.U) P.comparison
  have hleft :
      Y.p.IsStronglyCartesian f ((FibredCategoryMor.toFunctor F).map a ≫ P.comparison) := by
    letI : Y.p.IsStronglyCartesian f ((FibredCategoryMor.toFunctor F).map a) := hFa
    letI : Y.p.IsStronglyCartesian (𝟙 P.U) P.comparison := hcomparison
    simpa using
      (show Y.p.IsStronglyCartesian (f ≫ 𝟙 P.U)
          ((FibredCategoryMor.toFunctor F).map a ≫ P.comparison) from inferInstance)
  letI : Y.p.IsStronglyCartesian f ((FibredCategoryMor.toFunctor F).map b) := hFb
  letI : Y.p.IsStronglyCartesian f ((FibredCategoryMor.toFunctor F).map a ≫ P.comparison) :=
    hleft
  let e :=
    Functor.IsStronglyCartesian.domainIsoOfBaseIso
      Y.p
      (g := Iso.refl V)
      (show f = (Iso.refl V).hom ≫ f by simp)
      ((FibredCategoryMor.toFunctor F).map b)
      ((FibredCategoryMor.toFunctor F).map a ≫ P.comparison)
  have hfac :
      e.hom ≫ (FibredCategoryMor.toFunctor F).map b =
        (FibredCategoryMor.toFunctor F).map a ≫ P.comparison := by
    simpa [e] using
      (Functor.IsStronglyCartesian.fac
        Y.p
        f
        ((FibredCategoryMor.toFunctor F).map b)
        (show f = (Iso.refl V).hom ≫ f by simp)
        ((FibredCategoryMor.toFunctor F).map a ≫ P.comparison))
  have hcomm :
      CommSq
        ((FibredCategoryMor.toFunctor F).map a)
        Q.comparison
        P.comparison
        ((FibredCategoryMor.toFunctor F).map b) := by
    -- The defining square of the pulled-back comparison is exactly the comparison furnished by `e`.
    refine ⟨?_⟩
    simpa [Q, self_pullback_pulledback_comparison_iso] using hfac.symm
  let η : Q ⟶ P :=
    { base := f
      a := a
      a_over := ha_over
      b := b
      b_over := hb_over
      comm := hcomm }
  have hη :
      (explicitTwoFibreProduct
        (FibredCategoryMor.toBasedFunctor F)
        (FibredCategoryMor.toBasedFunctor F)).p.IsStronglyCartesian f η :=
    self_pullback_hom_isStronglyCartesian_of_components F η ha hb
  -- The two canonical source pullbacks assemble to the desired strongly cartesian morphism.
  exact ⟨Q, η, hη⟩

/-- Helper for Lemma 4.34.1: the projection from the explicit self-pullback of a fibred
morphism is fibred. -/
private theorem self_pullback_projection_isFibered
    {C : Type u₁} [Category.{v} C]
    {X Y : FibredCategoryOver C} (F : X ⟶ Y) :
    (explicitTwoFibreProduct
      (FibredCategoryMor.toBasedFunctor F)
      (FibredCategoryMor.toBasedFunctor F)).p.IsFibered := by
  -- Build strongly cartesian lifts by pulling back both source components simultaneously.
  refine Functor.IsFibered.of_exists_isStronglyCartesian ?_
  intro P V f
  obtain ⟨Q, η, hη⟩ := self_pullback_exists_isStronglyCartesian F P f
  exact ⟨Q, η, hη⟩

/-- Helper for Lemma 4.34.1: the canonical diagonal over the base preserves strongly cartesian
morphisms by assembling the two identical strongly cartesian source components. -/
theorem relativeDiagonalOver_preserves_strongly_cartesian
    {C : Type u₁} [Category.{v} C]
    {X Y : FibredCategoryOver.{u₁, v, max u₁ v, v} C} (F : X ⟶ Y) :
    (BasedFunctor.relativeDiagonalOver (FibredCategoryMor.toBasedFunctor F)).PreservesStronglyCartesian := by
  intro a b φ hφ
  -- The diagonal sends `φ` to `(φ, φ)`, so the pullback assembly theorem applies componentwise.
  simpa [BasedFunctor.relativeDiagonalOver, relativeDiagonalOverRaw, relativeDiagonalFunctor,
      relativeDiagonalFunctorMap] using
    (self_pullback_hom_isStronglyCartesian_of_components (C := C) (X := X) (Y := Y) F
      ((BasedFunctor.relativeDiagonalOver (FibredCategoryMor.toBasedFunctor F)).map φ)
      hφ hφ)

/-- Helper for Lemma 4.34.1: rebundle the canonical based diagonal into the owner morphism whose
target is the chapter-level fibred self-`2`-fibre product. -/
private noncomputable abbrev relative_diagonal_owner_mor
    {C : Type u₁} [Category.{v} C]
    {X Y : FibredCategoryOver.{u₁, v, max u₁ v, v} C} (F : X ⟶ Y) :
    X ⟶ FibredCategoryOver.twoFibreProduct F F :=
  FibredCategoryMor.ofBasedFunctor
    (BasedFunctor.relativeDiagonalOver (FibredCategoryMor.toBasedFunctor F))
    (relativeDiagonalOver_preserves_strongly_cartesian F)

/-- Helper for Lemma 4.34.1: name the owner-level diagonal self-`2`-fibre product once so the
final fibredness transport does not regenerate fresh copies of the same rebundled diagonal. -/
private noncomputable abbrev relative_diagonal_target
    {X Y : FibredCategoryOver.{u₁, v, max u₁ v, v} C} (F : X ⟶ Y) :
    FibredCategoryOver C :=
  FibredCategoryOver.twoFibreProduct
    (relative_diagonal_owner_mor (X := X) (Y := Y) F)
    (relative_diagonal_owner_mor (X := X) (Y := Y) F)

/-- Helper for Lemma 4.34.1: the named diagonal self-`2`-fibre product is fibred by the owner
instance from Lemma 4.33.10. -/
private theorem relative_diagonal_target_isFibered
    {X Y : FibredCategoryOver.{u₁, v, max u₁ v, v} C} (F : X ⟶ Y) :
    (relative_diagonal_target (X := X) (Y := Y) F).p.IsFibered := by
  -- The named target is an ambient fibred category over `C`, so its projection is fibred.
  exact FibredCategoryOver.isFibred
    (X := relative_diagonal_target (X := X) (Y := Y) F)

/-- Helper for Lemma 4.34.1: restate the fibredness of the named owner-level diagonal target in
the explicit pullback type used by the public relative inertia equivalence. -/
private theorem relative_diagonal_explicit_target_isFibered
    {X Y : FibredCategoryOver.{u₁, v, max u₁ v, v} C} (F : X ⟶ Y) :
    (explicitTwoFibreProduct
      (BasedFunctor.relativeDiagonalOver (FibredCategoryMor.toBasedFunctor F))
      (BasedFunctor.relativeDiagonalOver (FibredCategoryMor.toBasedFunctor F))).p.IsFibered := by
  -- Route correction: the public explicit target is definitionally the named owner-level
  -- diagonal target, so the ambient fibredness theorem for that owner target suffices directly.
  change (relative_diagonal_target (C := C) (F := F)).p.IsFibered
  exact FibredCategoryOver.isFibred (X := relative_diagonal_target (C := C) (F := F))

namespace BasedFunctor

/-- Helper for Lemma 4.34.1: forgetting the unit isomorphism from an explicit equivalence-over-base
datum does not change its component morphisms. -/
private theorem forgotten_unit_hom_app_eq
    {X : BasedCategory.{v, u₂} C} {Y : BasedCategory.{v, u₃} C}
    {F : X ⥤ᵇ Y} (e : EquivalenceOverBase F) (x : X.obj) :
    ((BasedNatTrans.forgetful X X).mapIso e.unitIso).hom.app x = e.unitIso.hom.app x := by
  -- Forgetting only removes the base-lift witness, so the underlying component is unchanged.
  rfl

/-- Helper for Lemma 4.34.1: forgetting the unit isomorphism from an explicit equivalence-over-base
datum does not change its inverse component morphisms. -/
private theorem forgotten_unit_inv_app_eq
    {X : BasedCategory.{v, u₂} C} {Y : BasedCategory.{v, u₃} C}
    {F : X ⥤ᵇ Y} (e : EquivalenceOverBase F) (x : X.obj) :
    ((BasedNatTrans.forgetful X X).mapIso e.unitIso).inv.app x = e.unitIso.inv.app x := by
  -- The inverse component is also definitionally unchanged after forgetting the base witness.
  rfl

/-- Helper for Lemma 4.34.1: forgetting the counit isomorphism from an explicit equivalence-over-base
datum does not change its inverse component morphisms. -/
private theorem forgotten_counit_inv_app_eq
    {X : BasedCategory.{v, u₂} C} {Y : BasedCategory.{v, u₃} C}
    {F : X ⥤ᵇ Y} (e : EquivalenceOverBase F) (y : Y.obj) :
    ((BasedNatTrans.forgetful Y Y).mapIso e.counitIso).inv.app y = e.counitIso.inv.app y := by
  -- Forgetting the based data leaves the underlying inverse counit component untouched.
  rfl

/-- Helper for Lemma 4.34.1: after adjointifying the forgotten unit against the forgotten counit,
the ordinary forward triangle holds on the underlying total categories, even in the
heterogeneous-universe setting. -/
private theorem ordinary_equivalence_functor_unitIso_comp
    {X : BasedCategory.{v, u₂} C} {Y : BasedCategory.{v, u₃} C}
    {F : X ⥤ᵇ Y} (e : EquivalenceOverBase F) (x : X.obj) :
    F.map ((CategoryTheory.Equivalence.adjointifyη
        ((BasedNatTrans.forgetful X X).mapIso e.unitIso)
        ((BasedNatTrans.forgetful Y Y).mapIso e.counitIso)).hom.app x) ≫
      e.counitIso.hom.app (F.obj x) = 𝟙 (F.obj x) := by
  -- Forget the based data, adjointify the ordinary unit against the ordinary counit, and apply
  -- the generic ordinary-category triangle theorem.
  simpa using
    (CategoryTheory.Equivalence.adjointify_η_ε
      ((BasedNatTrans.forgetful X X).mapIso e.unitIso)
      ((BasedNatTrans.forgetful Y Y).mapIso e.counitIso) x)

/-- Helper for Lemma 4.34.1: explicit equivalence-over-base data induce an ordinary equivalence of
the underlying total categories, so the triangle identities are available without requiring the
same `BasedCategory` universe on source and target. -/
private noncomputable def ordinary_equivalence_of_equivalence_data
    {X : BasedCategory.{v, u₂} C} {Y : BasedCategory.{v, u₃} C}
    {F : X ⥤ᵇ Y} (e : EquivalenceOverBase F) :
    X.obj ≌ Y.obj :=
  CategoryTheory.Equivalence.mk
    F.toFunctor
    e.inverse.toFunctor
    ((BasedNatTrans.forgetful X X).mapIso e.unitIso)
    ((BasedNatTrans.forgetful Y Y).mapIso e.counitIso)

/-- Helper for Lemma 4.34.1: forgetting the based equivalence-over-base data does not change the
forward object map of the induced ordinary equivalence. -/
private theorem ordinary_equivalence_functor_obj
    {X : BasedCategory.{v, u₂} C} {Y : BasedCategory.{v, u₃} C}
    {F : X ⥤ᵇ Y} (e : EquivalenceOverBase F) (x : X.obj) :
    (ordinary_equivalence_of_equivalence_data (C := C) e).functor.obj x = F.obj x := by
  rfl

/-- Helper for Lemma 4.34.1: the raw forgotten counit cancels the inverse component of the
adjointified unit carried by the induced ordinary equivalence of the total categories. -/
private theorem ordinary_equivalence_counit_adjointified_unit_inverse_comp
    {X : BasedCategory.{v, u₂} C} {Y : BasedCategory.{v, u₃} C}
    {F : X ⥤ᵇ Y} (e : EquivalenceOverBase F) (x : X.obj) :
    e.counitIso.inv.app (F.obj x) ≫
        F.map ((ordinary_equivalence_of_equivalence_data (C := C) e).unitIso.inv.app x) =
      𝟙 (F.obj x) := by
  -- The ordinary equivalence keeps the forgotten counit and adjointifies the forgotten unit.
  exact CategoryTheory.Equivalence.counitIso_functor_comp
    (ordinary_equivalence_of_equivalence_data (C := C) e) x

/-- Helper for Lemma 4.34.1: name the inverse component of the adjointified ordinary unit so the
heterogeneous transport lemmas can use a stable objectwise bridge back to the source category. -/
private noncomputable abbrev adjointified_unit_inv_app
    {X : BasedCategory.{v, u₂} C} {Y : BasedCategory.{v, u₃} C}
    {F : X ⥤ᵇ Y} (e : EquivalenceOverBase F) (x : X.obj) :
    e.inverse.obj (F.obj x) ⟶ x :=
  (ordinary_equivalence_of_equivalence_data (C := C) e).unitIso.inv.app x

/-- Helper for Lemma 4.34.1: the inverse component of the adjointified ordinary unit is still
vertical over the identity on the corresponding source object. -/
private theorem adjointified_unit_inv_isHomLift_heterogeneous
    {X : BasedCategory.{v, u₂} C} {Y : BasedCategory.{v, u₃} C}
    {F : X ⥤ᵇ Y} (e : EquivalenceOverBase F) (x : X.obj) :
    X.p.IsHomLift (𝟙 (X.p.obj x)) (adjointified_unit_inv_app (C := C) e x) := by
  -- Push the adjointified inverse unit component forward along `F`, where it becomes the
  -- ordinary counit component and hence is visibly vertical over the identity.
  have hε :
      Y.p.IsHomLift (𝟙 (Y.p.obj (F.obj x))) (e.counitIso.hom.app (F.obj x)) := by
    simpa using BasedNatTrans.isHomLift e.counitIso.hom
      (rfl : Y.p.obj (F.obj x) = Y.p.obj (F.obj x))
  have hEq :
      F.map (adjointified_unit_inv_app (C := C) e x) = e.counitIso.hom.app (F.obj x) := by
    simpa [adjointified_unit_inv_app] using
      ((ordinary_equivalence_of_equivalence_data (C := C) e).counit_app_functor x).symm
  have hmap :
      Y.p.IsHomLift (𝟙 (Y.p.obj (F.obj x)))
        (F.map (adjointified_unit_inv_app (C := C) e x)) := by
    rw [hEq]
    exact hε
  have hX :
      X.p.IsHomLift (𝟙 (Y.p.obj (F.obj x)))
        (adjointified_unit_inv_app (C := C) e x) := by
    exact
      (F.isHomLift_iff (𝟙 (Y.p.obj (F.obj x)))
        (adjointified_unit_inv_app (C := C) e x)).mp hmap
  rw [← F.w_obj x]
  exact hX

/-- Helper for Lemma 4.34.1: pulling a lifting problem back across the inverse in explicit
equivalence-over-base data preserves the same base morphism in the heterogeneous-universe setting. -/
private theorem inverse_transport_lift_over_base_heterogeneous
    {X : BasedCategory.{v, u₂} C} {Y : BasedCategory.{v, u₃} C}
    {F : X ⥤ᵇ Y} (e : EquivalenceOverBase F)
    {x y : X.obj} (φ : x ⟶ y)
    {z : Y.obj} (g : Y.p.obj z ⟶ Y.p.obj (F.obj x))
    (ψ : z ⟶ F.obj y)
    [Y.p.IsHomLift (g ≫ Y.p.map (F.map φ)) ψ] :
    X.p.IsHomLift (g ≫ eqToHom (F.w_obj x) ≫ X.p.map φ)
      (e.inverse.map ψ ≫ adjointified_unit_inv_app (C := C) e y) := by
  -- Rewrite the target lifting problem into the source base coordinates using the over-base
  -- equation attached to `F`.
  have hψY : Y.p.IsHomLift (g ≫ eqToHom (F.w_obj x) ≫ X.p.map φ) ψ := by
    refine IsHomLift.of_fac Y.p _ ψ rfl (F.w_obj y) ?_
    have hbase :
        g ≫ eqToHom (F.w_obj x) ≫ X.p.map φ =
          Y.p.map ψ ≫ eqToHom (F.w_obj y) := by
      calc
        g ≫ eqToHom (F.w_obj x) ≫ X.p.map φ
            = g ≫ Y.p.map (F.map φ) ≫ eqToHom (F.w_obj y) := by
                simpa [Category.assoc] using
                  (congrArg (fun k ↦ g ≫ k ≫ eqToHom (F.w_obj y))
                    (Functor.congr_hom F.w φ)).symm
        _ = Y.p.map ψ ≫ eqToHom (F.w_obj y) := by
              simpa [Category.assoc] using
                congrArg (fun k ↦ k ≫ eqToHom (F.w_obj y))
                  (IsHomLift.eq_of_isHomLift Y.p (g ≫ Y.p.map (F.map φ)) ψ)
    simpa [Category.assoc] using hbase
  -- Pull the transported lift back across the chosen quasi-inverse and compose with the vertical
  -- adjointified unit inverse.
  have hψX : X.p.IsHomLift (g ≫ eqToHom (F.w_obj x) ≫ X.p.map φ) (e.inverse.map ψ) :=
    (e.inverse.isHomLift_iff _ ψ).2 hψY
  have hη : X.p.IsHomLift (𝟙 (X.p.obj y)) (adjointified_unit_inv_app (C := C) e y) := by
    exact adjointified_unit_inv_isHomLift_heterogeneous (C := C) e y
  exact @IsHomLift.comp_lift_id_right' _ _ _ _ X.p _ _ _ _ _
    (g ≫ eqToHom (F.w_obj x) ≫ X.p.map φ) (e.inverse.map ψ) hψX
    (X.p.obj y) (adjointified_unit_inv_app (C := C) e y) hη

/-- Helper for Lemma 4.34.1: pushing a lifted source morphism forward across the chosen
quasi-inverse preserves the same base morphism in the target. -/
private theorem forward_transport_lift_over_base_heterogeneous
    {X : BasedCategory.{v, u₂} C} {Y : BasedCategory.{v, u₃} C}
    {F : X ⥤ᵇ Y} (e : EquivalenceOverBase F)
    {x : X.obj} {z : Y.obj} (g : Y.p.obj z ⟶ X.p.obj x)
    (ξ : e.inverse.obj z ⟶ x)
    [X.p.IsHomLift g ξ] :
    Y.p.IsHomLift g (e.counitIso.inv.app z ≫ F.map ξ) := by
  -- Push the source lift forward along `F`, then precompose with the vertical counit inverse.
  have hξY : Y.p.IsHomLift g (F.map ξ) :=
    (F.isHomLift_iff g ξ).2 (show X.p.IsHomLift g ξ from inferInstance)
  have hε : Y.p.IsHomLift (𝟙 (Y.p.obj z)) (e.counitIso.inv.app z) := by
    simpa using BasedNatTrans.isHomLift e.counitIso.inv (rfl : Y.p.obj z = Y.p.obj z)
  exact @IsHomLift.comp_lift_id_left' _ _ _ _ Y.p _ _ _
    (Y.p.obj z) (e.counitIso.inv.app z) hε _ _ g (F.map ξ) hξY

/-- Helper for Lemma 4.34.1: appending the canonical base-change isomorphism from `F.w_obj`
does not change whether a target morphism is a lift. -/
private theorem isHomLift_over_target_eq_iff_heterogeneous
    {X : BasedCategory.{v, u₂} C} {Y : BasedCategory.{v, u₃} C}
    {F : X ⥤ᵇ Y} {z : Y.obj} {x : X.obj}
    (g : Y.p.obj z ⟶ Y.p.obj (F.obj x))
    (θ : z ⟶ F.obj x) :
    Y.p.IsHomLift g θ ↔ Y.p.IsHomLift (g ≫ eqToHom (F.w_obj x)) θ := by
  -- The extra `eqToHom` only rewrites the codomain to the source-side base coordinates.
  exact (IsHomLift.lift_comp_eqToHom_iff Y.p g θ (F.w_obj x)).symm

/-- Helper for Lemma 4.34.1: a target-side factorization pulls back along the chosen inverse and
the unit inverse to the corresponding source-side factorization. -/
private theorem pullback_factorization_of_map_factorization_heterogeneous
    {X : BasedCategory.{v, u₂} C} {Y : BasedCategory.{v, u₃} C}
    {F : X ⥤ᵇ Y} (e : EquivalenceOverBase F)
    {x y : X.obj} (φ : x ⟶ y)
    {z : Y.obj} {τ' : z ⟶ F.obj x} {ψ' : z ⟶ F.obj y}
    (hτ' : τ' ≫ F.map φ = ψ') :
    (e.inverse.map τ' ≫ adjointified_unit_inv_app (C := C) e x) ≫ φ =
      e.inverse.map ψ' ≫ adjointified_unit_inv_app (C := C) e y := by
  -- Rewrite the pulled-back `F.map φ` term using naturality of the adjointified unit inverse.
  have hη :
      e.inverse.map (F.map φ) ≫ adjointified_unit_inv_app (C := C) e y =
        adjointified_unit_inv_app (C := C) e x ≫ φ := by
    let E := ordinary_equivalence_of_equivalence_data (C := C) e
    have hη' :
        E.inverse.map (E.functor.map φ) ≫ E.unitInv.app y =
          (E.unitInv.app x ≫ φ ≫ E.unit.app y) ≫ E.unitInv.app y := by
      simpa [Category.assoc] using
        congrArg (fun k ↦ k ≫ E.unitInv.app y) (E.inv_fun_map x y φ)
    have hη'' :
        E.inverse.map (E.functor.map φ) ≫ E.unitInv.app y =
          E.unitInv.app x ≫ φ := by
      rw [hη']
      simpa [Category.assoc]
    change E.inverse.map (E.functor.map φ) ≫ E.unitInv.app y = E.unitInv.app x ≫ φ
    exact hη''
  calc
    (e.inverse.map τ' ≫ adjointified_unit_inv_app (C := C) e x) ≫ φ
        = e.inverse.map τ' ≫ (adjointified_unit_inv_app (C := C) e x ≫ φ) := by
            simp [Category.assoc]
    _ = e.inverse.map τ' ≫
          (e.inverse.map (F.map φ) ≫ adjointified_unit_inv_app (C := C) e y) := by
          rw [← hη]
    _ = e.inverse.map (τ' ≫ F.map φ) ≫ adjointified_unit_inv_app (C := C) e y := by
          simp [Functor.map_comp, Category.assoc]
    _ = e.inverse.map ψ' ≫ adjointified_unit_inv_app (C := C) e y := by
          rw [hτ']

/-- Helper for Lemma 4.34.1: pushing the pulled-back morphism forward with the counit inverse of
the induced ordinary equivalence recovers the original target morphism. -/
private theorem pushforward_pullback_eq_heterogeneous
    {X : BasedCategory.{v, u₂} C} {Y : BasedCategory.{v, u₃} C}
    {F : X ⥤ᵇ Y} (e : EquivalenceOverBase F)
    {x : X.obj} {z : Y.obj} (θ : z ⟶ F.obj x) :
    e.counitIso.inv.app z ≫
        F.map (e.inverse.map θ ≫ adjointified_unit_inv_app (C := C) e x) = θ := by
  -- Move `θ` across the counit inverse, then collapse the remaining counit-unit tail.
  rw [Functor.map_comp]
  have hnat :
      e.counitIso.inv.app z ≫ F.map (e.inverse.map θ) ≫
          F.map (adjointified_unit_inv_app (C := C) e x) =
        θ ≫ e.counitIso.inv.app (F.obj x) ≫
          F.map (adjointified_unit_inv_app (C := C) e x) := by
    simpa [Functor.comp_map, Category.assoc] using
      (congrArg (fun k ↦ k ≫ F.map (adjointified_unit_inv_app (C := C) e x))
        (e.counitIso.inv.naturality θ)).symm
  have htail :
      θ ≫ e.counitIso.inv.app (F.obj x) ≫
          F.map (adjointified_unit_inv_app (C := C) e x) = θ := by
    simpa [adjointified_unit_inv_app, Category.assoc] using
      congrArg (fun k ↦ θ ≫ k)
        (ordinary_equivalence_counit_adjointified_unit_inverse_comp (C := C) (e := e) x)
  exact hnat.trans htail

/-- Helper for Lemma 4.34.1: explicit equivalence-over-base data preserve strongly cartesian
morphisms even when the source and target total categories live in different universes. -/
private theorem preserves_strongly_cartesian_of_equivalence_data
    {X : BasedCategory.{v, u₂} C} {Y : BasedCategory.{v, u₃} C}
    {F : X ⥤ᵇ Y} (e : EquivalenceOverBase F) :
    F.PreservesStronglyCartesian := by
  intro a b φ hφ
  refine
    { toIsHomLift := by
        infer_instance
      universal_property' := ?_ }
  intro z g ψ' hψ'
  -- Pull the problem back to `X` and solve it there using the strong cartesianness of `φ`.
  let ψX : e.inverse.obj z ⟶ b :=
    e.inverse.map ψ' ≫ adjointified_unit_inv_app (C := C) e b
  have hψXlift :
      X.p.IsHomLift ((g ≫ eqToHom (F.w_obj a)) ≫ X.p.map φ) ψX := by
    simpa [ψX] using
      inverse_transport_lift_over_base_heterogeneous (e := e) φ g ψ'
  letI : X.p.IsHomLift ((g ≫ eqToHom (F.w_obj a)) ≫ X.p.map φ) ψX := hψXlift
  obtain ⟨ξ, hξ, hξuniq⟩ :=
    Functor.IsStronglyCartesian.universal_property X.p (X.p.map φ) φ
      (g ≫ eqToHom (F.w_obj a))
      (((g ≫ eqToHom (F.w_obj a)) ≫ X.p.map φ)) rfl ψX
  -- Push the source lift forward along the ordinary counit inverse induced by the equivalence
  -- data.
  letI : X.p.IsHomLift (g ≫ eqToHom (F.w_obj a)) ξ := hξ.1
  let ξ' : z ⟶ F.obj a := e.counitIso.inv.app z ≫ F.map ξ
  have hξ'base :
      Y.p.IsHomLift (g ≫ eqToHom (F.w_obj a)) ξ' :=
    forward_transport_lift_over_base_heterogeneous (e := e)
      (g ≫ eqToHom (F.w_obj a)) ξ
  have hξ' : Y.p.IsHomLift g ξ' :=
    (isHomLift_over_target_eq_iff_heterogeneous (F := F) g ξ').mpr hξ'base
  have hpushψ : e.counitIso.inv.app z ≫ F.map ψX = ψ' := by
    simpa [ψX, Functor.map_comp, Category.assoc] using
      pushforward_pullback_eq_heterogeneous (e := e) ψ'
  refine ⟨ξ', ⟨hξ', ?_⟩, ?_⟩
  · -- The pushed-forward lift factors through `F.map φ` by the pull-push comparison lemma.
    have hstep1 : ξ' ≫ F.map φ = e.counitIso.inv.app z ≫ F.map (ξ ≫ φ) := by
      simp [ξ', Functor.map_comp, Category.assoc]
    have hstep2 :
        e.counitIso.inv.app z ≫ F.map (ξ ≫ φ) = e.counitIso.inv.app z ≫ F.map ψX := by
      simpa using congrArg (fun k ↦ e.counitIso.inv.app z ≫ F.map k) hξ.2
    exact hstep1.trans <| hstep2.trans hpushψ
  · intro η hη
    -- Pull any competing target lift back to `X` and compare there by uniqueness.
    have hηbase :
        Y.p.IsHomLift (g ≫ eqToHom (F.w_obj a)) η :=
      (isHomLift_over_target_eq_iff_heterogeneous (F := F) g η).mp hη.1
    have hηpull :
        X.p.IsHomLift (g ≫ eqToHom (F.w_obj a))
          (e.inverse.map η ≫ adjointified_unit_inv_app (C := C) e a) := by
      have hηpre : X.p.IsHomLift (g ≫ eqToHom (F.w_obj a)) (e.inverse.map η) :=
        (e.inverse.isHomLift_iff (g ≫ eqToHom (F.w_obj a)) η).2 hηbase
      have hηunit :
          X.p.IsHomLift (𝟙 (X.p.obj a)) (adjointified_unit_inv_app (C := C) e a) := by
        exact adjointified_unit_inv_isHomLift_heterogeneous (C := C) e a
      exact @IsHomLift.comp_lift_id_right' _ _ _ _ X.p _ _ _ _ _
        (g ≫ eqToHom (F.w_obj a)) (e.inverse.map η) hηpre
        (X.p.obj a) (adjointified_unit_inv_app (C := C) e a) hηunit
    have hηfac :
        (e.inverse.map η ≫ adjointified_unit_inv_app (C := C) e a) ≫ φ = ψX := by
      simpa [ψX] using
        pullback_factorization_of_map_factorization_heterogeneous (e := e) φ hη.2
    have hηeq : e.inverse.map η ≫ adjointified_unit_inv_app (C := C) e a = ξ :=
      hξuniq _ ⟨hηpull, hηfac⟩
    -- Push the equality back to the target using the same comparison lemma.
    have hpushη :
        η = e.counitIso.inv.app z ≫
          F.map (e.inverse.map η ≫ adjointified_unit_inv_app (C := C) e a) := by
      symm
      simpa [Functor.map_comp, Category.assoc] using
        pushforward_pullback_eq_heterogeneous (e := e) η
    have hstepη :
        e.counitIso.inv.app z ≫
          F.map (e.inverse.map η ≫ adjointified_unit_inv_app (C := C) e a) =
          e.counitIso.inv.app z ≫ F.map ξ := by
      simpa using congrArg (fun k ↦ e.counitIso.inv.app z ≫ F.map k) hηeq
    exact hpushη.trans <| hstepη.trans rfl

/-- Helper for Lemma 4.34.1: explicit equivalence-over-base data transport fibredness forward
between possibly heterogeneous total-category universes. -/
private theorem isFibered_of_equivalence_data
    {X : BasedCategory.{v, u₂} C} {Y : BasedCategory.{v, u₃} C}
    {F : X ⥤ᵇ Y} (e : EquivalenceOverBase F) :
    X.p.IsFibered → Y.p.IsFibered := by
  intro hX
  -- Use the strongly-cartesian lift criterion, transport a chosen source lift across `F`, and
  -- then compose with the vertical counit component to land over the original target object.
  refine Functor.IsFibered.of_exists_isStronglyCartesian ?_
  intro y V f
  letI : X.p.IsFibered := hX
  obtain ⟨x, φ, hφcart⟩ := IsPreFibered.exists_isCartesian X.p (e.inverse.w_obj y) f
  letI : X.p.IsCartesian f φ := hφcart
  have hφstrong : X.p.IsStronglyCartesian f φ :=
    Functor.IsFibered.isStronglyCartesian_of_isCartesian X.p f φ
  have hφowner : X.p.IsStronglyCartesian (X.p.map φ) φ := by
    letI : X.p.IsStronglyCartesian f φ := hφstrong
    exact isStronglyCartesian_rebase_over_target_eq
      (p := X.p) (hb := e.inverse.w_obj y) (f := f) φ
  have hFφstrong_owner :
      Y.p.IsStronglyCartesian (Y.p.map (F.map φ)) (F.map φ) := by
    exact preserves_strongly_cartesian_of_equivalence_data (e := e) φ hφowner
  have hFφlift : Y.p.IsHomLift f (F.map φ) :=
    (F.isHomLift_iff f φ).2 (show X.p.IsHomLift f φ from inferInstance)
  have hFφstrong : Y.p.IsStronglyCartesian f (F.map φ) := by
    -- Rebase the owner-level strong-cartesian structure using the explicit external lift over `f`.
    letI : Y.p.IsStronglyCartesian (Y.p.map (F.map φ)) (F.map φ) := hFφstrong_owner
    letI : Y.p.IsHomLift f (F.map φ) := hFφlift
    exact isStronglyCartesian_of_external_hom_lift (p := Y.p) (f := f) (φ := F.map φ)
  have hεlift : Y.p.IsHomLift (𝟙 (Y.p.obj y)) (e.counitIso.hom.app y) := by
    simpa using BasedNatTrans.isHomLift e.counitIso.hom (rfl : Y.p.obj y = Y.p.obj y)
  have hεstrong : Y.p.IsStronglyCartesian (𝟙 (Y.p.obj y)) (e.counitIso.hom.app y) := by
    let epsIso := (BasedNatTrans.forgetful Y Y).mapIso e.counitIso
    refine
      { toIsHomLift := hεlift
        universal_property' := ?_ }
    intro z g τ hτ
    -- Any lifting problem through the vertical counit is solved by composing with its inverse.
    let χ : z ⟶ F.obj (e.inverse.obj y) := τ ≫ e.counitIso.inv.app y
    have hτ' : Y.p.IsHomLift g τ := by
      simpa using hτ
    have hεinv : Y.p.IsHomLift (𝟙 (Y.p.obj y)) (e.counitIso.inv.app y) := by
      simpa using BasedNatTrans.isHomLift e.counitIso.inv (rfl : Y.p.obj y = Y.p.obj y)
    have hχ : Y.p.IsHomLift g χ := by
      exact @IsHomLift.comp_lift_id_right' _ _ _ _ Y.p _ _ _ _ _
        g τ hτ' (Y.p.obj y) (e.counitIso.inv.app y) hεinv
    refine ⟨χ, ⟨hχ, ?_⟩, ?_⟩
    · simpa [χ, epsIso, Category.assoc] using
        congrArg (fun k ↦ τ ≫ k) (epsIso.inv_hom_id_app y)
    · intro η hη
      have hηcomp :
          η = η ≫ e.counitIso.hom.app y ≫ e.counitIso.inv.app y := by
        rw [← Category.assoc]
        simpa [epsIso] using
          congrArg (fun k ↦ η ≫ k) (epsIso.hom_inv_id_app y).symm
      calc
        η = η ≫ e.counitIso.hom.app y ≫ e.counitIso.inv.app y := hηcomp
        _ = τ ≫ e.counitIso.inv.app y := by
              simpa [Category.assoc] using
                congrArg (fun k ↦ k ≫ e.counitIso.inv.app y) hη.2
        _ = χ := rfl
  let ψ : F.obj x ⟶ y := F.map φ ≫ e.counitIso.hom.app y
  have hψstrong : Y.p.IsStronglyCartesian f ψ := by
    let epsIso := (BasedNatTrans.forgetful Y Y).mapIso e.counitIso
    -- First record that the composite `ψ` still lies over the original external base map `f`.
    have hψlift : Y.p.IsHomLift f ψ := by
      simpa [ψ, Category.assoc] using
        @IsHomLift.comp_lift_id_right' _ _ _ _ Y.p _ _ _ _ _
          f (F.map φ) hFφlift (Y.p.obj y) (e.counitIso.hom.app y) hεlift
    refine
      { toIsHomLift := hψlift
        universal_property' := ?_ }
    intro z g τ hτ
    -- Cancel the vertical counit component on the right and solve the remaining lifting problem
    -- through `F.map φ`.
    let τ' : z ⟶ F.obj (e.inverse.obj y) := τ ≫ e.counitIso.inv.app y
    have hτ' : Y.p.IsHomLift (g ≫ f) τ' := by
      have hτlift : Y.p.IsHomLift (g ≫ f) τ := by
        simpa using hτ
      have hεinv : Y.p.IsHomLift (𝟙 (Y.p.obj y)) (e.counitIso.inv.app y) := by
        simpa using BasedNatTrans.isHomLift e.counitIso.inv (rfl : Y.p.obj y = Y.p.obj y)
      simpa [τ'] using
        @IsHomLift.comp_lift_id_right' _ _ _ _ Y.p _ _ _ _ _
          (g ≫ f) τ hτlift (Y.p.obj y) (e.counitIso.inv.app y) hεinv
    letI : Y.p.IsStronglyCartesian f (F.map φ) := hFφstrong
    letI : Y.p.IsHomLift (g ≫ f) τ' := hτ'
    obtain ⟨χ, hχ, hχuniq⟩ :=
      Functor.IsStronglyCartesian.universal_property Y.p f (F.map φ) g (g ≫ f) rfl τ'
    refine ⟨χ, ⟨hχ.1, ?_⟩, ?_⟩
    · -- Compose the solved factorization back with the counit component to recover `τ`.
      have hτcancel : τ' ≫ e.counitIso.hom.app y = τ := by
        calc
          τ' ≫ e.counitIso.hom.app y
              = τ ≫ (e.counitIso.inv.app y ≫ e.counitIso.hom.app y) := by
                  simp [τ', Category.assoc]
          _ = τ := by
                simpa [Category.assoc] using
                  congrArg (fun k ↦ τ ≫ k) (epsIso.inv_hom_id_app y)
      have hχψ : χ ≫ ψ = τ' ≫ e.counitIso.hom.app y := by
        calc
          χ ≫ ψ = (χ ≫ F.map φ) ≫ e.counitIso.hom.app y := by
              simp [ψ, Category.assoc]
          _ = τ' ≫ e.counitIso.hom.app y := by
                simpa [Category.assoc] using
                  congrArg (fun k ↦ k ≫ e.counitIso.hom.app y) hχ.2
      exact hχψ.trans (by simpa using hτcancel)
    · intro η hη
      have hηcancel : (η ≫ ψ) ≫ e.counitIso.inv.app y = η ≫ F.map φ := by
        calc
          (η ≫ ψ) ≫ e.counitIso.inv.app y
              = η ≫ F.map φ ≫ (e.counitIso.hom.app y ≫ e.counitIso.inv.app y) := by
                  simp [ψ, Category.assoc]
          _ = η ≫ F.map φ := by
                simpa [Category.assoc] using
                  congrArg (fun k ↦ η ≫ F.map φ ≫ k) (epsIso.hom_inv_id_app y)
      have hηfac :
          η ≫ F.map φ = τ' := by
        have hηstep2 : (η ≫ ψ) ≫ e.counitIso.inv.app y = τ ≫ e.counitIso.inv.app y := by
          simpa [Category.assoc] using
            congrArg (fun k ↦ k ≫ e.counitIso.inv.app y) hη.2
        have hηstep3 : τ ≫ e.counitIso.inv.app y = τ' := by
          simpa [τ']
        exact hηcancel.symm.trans (hηstep2.trans hηstep3)
      exact hχuniq _ ⟨hη.1, hηfac⟩
  exact ⟨F.obj x, ψ, hψstrong⟩

/-- Helper for Lemma 4.34.1: the inverse unit component of an equivalence over the base is
vertical over the identity on the corresponding source object. -/
private theorem unit_inv_isHomLift
    {X : BasedCategory.{v, u₂} C} {Y : BasedCategory.{v, u₃} C}
    {F : X ⥤ᵇ Y} (e : EquivalenceOverBase F) (x : X.obj) :
    X.p.IsHomLift (𝟙 (X.p.obj x)) (e.unitIso.inv.app x) := by
  -- This is exactly the over-identity condition carried by the based unit isomorphism.
  simpa using BasedNatTrans.isHomLift e.unitIso.inv (rfl : X.p.obj x = X.p.obj x)

/-- Helper for Lemma 4.34.1: the inverse counit component of an equivalence over the base is
vertical over the identity on the corresponding target object. -/
private theorem counit_inv_isHomLift
    {X : BasedCategory.{v, u₂} C} {Y : BasedCategory.{v, u₃} C}
    {F : X ⥤ᵇ Y} (e : EquivalenceOverBase F) (y : Y.obj) :
    Y.p.IsHomLift (𝟙 (Y.p.obj y)) (e.counitIso.inv.app y) := by
  -- The based counit is also vertical, so its inverse component is a lift of the identity.
  simpa using BasedNatTrans.isHomLift e.counitIso.inv (rfl : Y.p.obj y = Y.p.obj y)

/-- Helper for Lemma 4.34.1: fibredness transports backward along explicit equivalence-over-base
data even when the source and target total categories have different universes. -/
theorem isFibered_of_equivalence_over_base_heterogeneous
    {X : BasedCategory.{v, u₂} C} {Y : BasedCategory.{v, u₃} C}
    {F : X ⥤ᵇ Y} (e : EquivalenceOverBase F) (hY : Y.p.IsFibered) :
    X.p.IsFibered := by
  -- Route correction: rerun the forward transport proof on the explicit inverse equivalence data
  -- instead of coercing to the same-universe theorem from Lemma 4.33.8.
  let e' : EquivalenceOverBase e.inverse :=
    { inverse := F
      unitIso := e.counitIso.symm
      counitIso := e.unitIso.symm }
  exact isFibered_of_equivalence_data (e := e') hY

end BasedFunctor

-- Proof sketch: use the over-`C` equivalence from Lemma `4.34.1` to replace the relative
-- inertia projection by the explicit self-`2`-fibre-product of the diagonal
-- `S ⟶ S ×_{S'} S`, then apply Lemma `4.33.10` to the canonical explicit `2`-fibre-product
-- construction.
/-- The projection from the relative inertia of a morphism of fibred categories over `C` is
fibred. -/
theorem relativeInertiaProjection_isFibered
    {X Y : FibredCategoryOver.{u₁, v, max u₁ v, v} C} (F : X ⟶ Y) :
    (relativeInertiaProjection (FibredCategoryMor.toFunctor F) X.p).IsFibered := by
  -- Route correction: move to the canonical owner `FibredCategoryOver.twoFibreProduct` before
  -- transporting fibredness back across the over-base equivalence from Lemma 4.34.1.
  let G :
      BasedCategory.ofFunctor (relativeInertiaProjection (FibredCategoryMor.toFunctor F) X.p) ⥤ᵇ
        explicitTwoFibreProduct
          (BasedFunctor.relativeDiagonalOver (FibredCategoryMor.toBasedFunctor F))
          (BasedFunctor.relativeDiagonalOver (FibredCategoryMor.toBasedFunctor F)) :=
    BasedFunctor.relativeInertiaToDiagonalPullback (FibredCategoryMor.toBasedFunctor F)
  have hEquiv : G.IsEquivalenceOverBase := by
    -- Freeze the public comparison functor with its explicit source and target before invoking
    -- the imported equivalence-over-base theorem.
    simpa [G] using
      (BasedFunctor.relativeInertiaEquivalenceOverBase (FibredCategoryMor.toBasedFunctor F))
  let e : BasedFunctor.EquivalenceOverBase G := Classical.choice hEquiv.nonempty
  let hTarget := relative_diagonal_explicit_target_isFibered (X := X) (Y := Y) F
  -- Pull the explicit target fibredness back across the chosen equivalence-over-base datum.
  exact BasedFunctor.isFibered_of_equivalence_over_base_heterogeneous e hTarget

instance
    {X Y : FibredCategoryOver.{u₁, v, max u₁ v, v} C} (F : X ⟶ Y) :
    (relativeInertiaProjection (FibredCategoryMor.toFunctor F) X.p).IsFibered :=
  relativeInertiaProjection_isFibered F

end CategoryTheory
