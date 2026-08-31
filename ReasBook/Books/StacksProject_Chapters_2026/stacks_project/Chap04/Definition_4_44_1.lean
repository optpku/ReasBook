module

public import stacks_project.Chap04.Definition_4_31_2

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

universe w v u

namespace CategoryTheory

open Bicategory
open scoped Bicategory

variable {B : Type u} [Bicategory.{w, v} B]

/- Domain-style sampling for Definition 4.44.1:
- primary domain: bicategorical `2`-commutative squares together with left-lift data;
- owner abstractions inspected: `BicategoricalTwoCommutativeSquare`, `LeftLift`,
  `LeftLift.whiskering`, and the canonical morphism category on `LeftLift`;
- triage:
  `source-facing`: the dotted-arrow data attached to a chosen `2`-commutative square,
  `core/canonical`: the square owner `BicategoricalTwoCommutativeSquare` together with the
  whiskered owner category `LeftLift p (sq.p ≫ y)`,
  `bridge/view`: the dotted-arrow category and its locally-groupoidal consequences;
- primitive data: a chosen square `sq : BicategoricalTwoCommutativeSquare y p`, a lift
  `toLeftLift : LeftLift p y` with invertible unit, and an isomorphism from its whiskering along
  `sq.p` to the canonical `LeftLift` encoded by `sq`;
- derived API: the dotted morphism itself, the upper-left and lower-right comparison
  `2`-isomorphisms, the category structure on `DottedArrow sq` with canonical hom type `A ⟶ A'`,
  the postcomposition square/functor for a right square, and the groupoid structure under local
  groupoid hypotheses. -/

/-- Definition 4.44.1: for a chosen `2`-commutative square `sq` over `y : T ⟶ Y` and
`p : X ⟶ Y`, a dotted arrow consists of the canonical bicategorical left-lift datum for the right
triangle, together with an isomorphism in the whiskered owner category identifying the induced
upper-left comparison with the canonical one attached to `sq`. The source-facing Stacks condition
that the right-triangle comparison is invertible remains part of the data. -/
structure DottedArrow
    {T X Y : B} {y : T ⟶ Y} {p : X ⟶ Y}
    (sq : BicategoricalTwoCommutativeSquare y p) where
  /-- The canonical left-lift datum encoding the right triangle `y ⟶ arrow ≫ p`. -/
  toLeftLift : LeftLift p y
  /-- The right-triangle comparison is invertible. -/
  unit_isIso : IsIso toLeftLift.unit
  /-- The induced upper-left comparison, promoted to the whiskered owner category. -/
  comparison : (LeftLift.whiskering sq.p).obj toLeftLift ≅ sq.symm.toLeftLift

attribute [instance] DottedArrow.unit_isIso

namespace DottedArrow

variable {T X Y : B} {y : T ⟶ Y} {p : X ⟶ Y}
variable {sq : BicategoricalTwoCommutativeSquare y p}

/-- Construct the owner-level comparison isomorphism from a source-facing upper-left comparison. -/
noncomputable def comparisonIsoMk
    (t : LeftLift p y) [IsIso t.unit]
    (left : sq.p ≫ t.lift ≅ sq.q)
    (comm :
      sq.p ◁ t.unit ≫ (α_ sq.p t.lift p).inv ≫ left.hom ▷ p =
        sq.ψ.hom) :
    (LeftLift.whiskering sq.p).obj t ≅ sq.symm.toLeftLift :=
  { hom := LeftLift.homMk left.hom <| by
      -- The forward comparison is exactly the source-facing compatibility.
      simpa [LeftLift.whiskering] using comm
    inv := LeftLift.homMk left.inv <| by
      -- Compose the source-facing compatibility with `left.inv` on the right.
      have h := congrArg (fun k ↦ k ≫ left.inv ▷ p) comm
      simpa [LeftLift.whiskering, Category.assoc] using h.symm
    hom_inv_id := by
      apply StructuredArrow.hom_ext
      exact left.hom_inv_id
    inv_hom_id := by
      apply StructuredArrow.hom_ext
      exact left.inv_hom_id }

/-- The dotted morphism `T ⟶ X`. -/
abbrev arrow (A : DottedArrow sq) : T ⟶ X :=
  A.toLeftLift.lift

/-- The comparison `2`-isomorphism for the upper-left triangle. -/
noncomputable def left (A : DottedArrow sq) : sq.p ≫ A.arrow ≅ sq.q :=
  -- The source-facing upper-left comparison is the right component of `A.comparison`.
  Comma.rightIso A.comparison

/-- The comparison `2`-isomorphism for the lower-right triangle. -/
noncomputable def right (A : DottedArrow sq) : y ≅ A.arrow ≫ p :=
  letI := A.unit_isIso
  asIso A.toLeftLift.unit

@[simp]
theorem right_hom (A : DottedArrow sq) :
    A.right.hom = A.toLeftLift.unit := by
  rfl

/-- The two triangular comparison `2`-isomorphisms recover the chosen outer comparison `sq.ψ`. -/
theorem comm (A : DottedArrow sq) :
    whiskerLeftIso sq.p A.right ≪≫
        (α_ sq.p A.arrow p).symm ≪≫
          whiskerRightIso A.left p =
      sq.ψ := by
  ext
  simpa [left, right] using LeftLift.w A.comparison.hom

end DottedArrow

namespace DottedArrow

variable {T X Y : B} {y : T ⟶ Y} {p : X ⟶ Y}
variable {sq : BicategoricalTwoCommutativeSquare y p}

/-- A morphism of dotted arrows is a morphism in the canonical left-lift category together with
compatibility with the upper-left comparison `2`-isomorphisms. The lower-right compatibility is
already owned by the underlying `LeftLift` morphism. -/
abbrev Hom (A A' : DottedArrow sq) :=
  { η : A.toLeftLift ⟶ A'.toLeftLift //
      (LeftLift.whiskering sq.p).map η ≫ A'.comparison.hom = A.comparison.hom }

namespace Hom

variable {A A' : DottedArrow sq}

/-- The underlying morphism in the canonical left-lift category. -/
abbrev toLeftLiftHom (η : Hom A A') : A.toLeftLift ⟶ A'.toLeftLift :=
  η.1

/-- The ambient `2`-morphism between the dotted morphisms. -/
abbrev right (η : Hom A A') : A.arrow ⟶ A'.arrow :=
  η.1.right

/-- Compatibility with the upper-left comparison `2`-isomorphisms. -/
@[reassoc, simp]
theorem left_comm (η : Hom A A') :
    sq.p ◁ η.right ≫ A'.left.hom = A.left.hom :=
  by
    simpa [DottedArrow.left, LeftLift.whiskering] using
      congrArg (fun f ↦ f.right) η.2

/-- Compatibility with the lower-right comparison `2`-isomorphisms. -/
@[reassoc, simp]
theorem right_comm (η : Hom A A') :
    A.right.hom ≫ η.right ▷ p = A'.right.hom := by
  simp [LeftLift.w η.toLeftLiftHom]

@[ext]
theorem ext
    {η θ : Hom A A'}
    (h : η.right = θ.right) :
    η = θ := by
  apply Subtype.ext
  exact StructuredArrow.hom_ext η.1 θ.1 h

end Hom

/-- The identity morphism of a dotted arrow. -/
def idHom (A : DottedArrow sq) : Hom A A :=
  ⟨𝟙 A.toLeftLift, by
    simp
  ⟩

/-- The ambient `2`-morphism of `idHom`. -/
@[simp]
private theorem idHom_right (A : DottedArrow sq) :
    (idHom A).right = 𝟙 A.arrow :=
  rfl

/-- Composition of morphisms of dotted arrows. -/
def compHom
    {A B C : DottedArrow sq}
    (η : Hom A B) (θ : Hom B C) :
    Hom A C :=
  ⟨η.toLeftLiftHom ≫ θ.toLeftLiftHom, by
    rw [Functor.map_comp, Category.assoc, θ.2]
    exact η.2
  ⟩

/-- The ambient `2`-morphism of `compHom`. -/
@[simp]
private theorem compHom_right
    {A B C : DottedArrow sq}
    (η : Hom A B) (θ : Hom B C) :
    (compHom η θ).right = η.right ≫ θ.right :=
  rfl

theorem id_comp
    {A B : DottedArrow sq}
    (η : Hom A B) :
    compHom (idHom A) η = η := by
  apply Hom.ext
  change (𝟙 A.toLeftLift ≫ η.toLeftLiftHom).right = η.right
  simp

theorem comp_id
    {A B : DottedArrow sq}
    (η : Hom A B) :
    compHom η (idHom B) = η := by
  apply Hom.ext
  change (η.toLeftLiftHom ≫ 𝟙 B.toLeftLift).right = η.right
  simp

theorem assoc
    {A B C D : DottedArrow sq}
    (η : Hom A B) (θ : Hom B C) (ι : Hom C D) :
    compHom (compHom η θ) ι = compHom η (compHom θ ι) := by
  apply Hom.ext
  change ((η.toLeftLiftHom ≫ θ.toLeftLiftHom) ≫ ι.toLeftLiftHom).right =
      (η.toLeftLiftHom ≫ (θ.toLeftLiftHom ≫ ι.toLeftLiftHom)).right
  simp

/-- The dotted arrows for a fixed `2`-commutative square form a category. -/
instance : Category (DottedArrow sq) where
  Hom A B := Hom A B
  id := idHom
  comp η θ := compHom η θ
  id_comp := id_comp
  comp_id := comp_id
  assoc η θ ι := assoc η θ ι

@[simp]
theorem id_right (A : DottedArrow sq) :
    (𝟙 A : A ⟶ A).right = 𝟙 A.arrow :=
  idHom_right A

@[simp]
theorem comp_right
    {A B C : DottedArrow sq}
    (η : A ⟶ B) (θ : B ⟶ C) :
    (η ≫ θ).right = η.right ≫ θ.right :=
  compHom_right η θ

section LocallyGroupoid

variable [Bicategory.IsLocallyGroupoid B]

/-- In a locally groupoidal bicategory, a morphism of dotted arrows has the inverse `2`-morphism
in the ambient hom-category as its inverse. -/
private noncomputable def invHom
    {A A' : DottedArrow sq}
    (η : A ⟶ A') :
    A' ⟶ A :=
  ⟨LeftLift.homMk (inv η.right) <| by
      haveI : IsIso η.right := inferInstance
      haveI : IsIso (η.right ▷ p) := inferInstance
      -- The lower-right compatibility is stable under inversion in the hom-category.
      have hunit :
          A.toLeftLift.unit ≫ η.right ▷ p = A'.toLeftLift.unit :=
        LeftLift.w η.toLeftLiftHom
      calc
        A'.toLeftLift.unit ≫ inv η.right ▷ p =
            (A.toLeftLift.unit ≫ η.right ▷ p) ≫ inv η.right ▷ p := by
              rw [← hunit]
        _ = A.toLeftLift.unit ≫
              ((η.right ▷ p) ≫ (inv η.right ▷ p)) := by
              rw [Category.assoc]
        _ = A.toLeftLift.unit ≫ 𝟙 (A.arrow ≫ p) := by
              simp
        _ = A.toLeftLift.unit := by
              simp, by
    -- The upper-left compatibility is obtained by cancelling `η.right` on the left.
    haveI : IsIso η.right := inferInstance
    apply StructuredArrow.hom_ext
    change sq.p ◁ inv η.right ≫ A.left.hom = A'.left.hom
    have h := Hom.left_comm η
    apply (cancel_epi (sq.p ◁ η.right)).1
    simpa [Category.assoc] using h⟩

@[simp]
private theorem invHom_right
    {A A' : DottedArrow sq}
    (η : A ⟶ A') :
    (invHom η).right = inv η.right :=
  rfl

/-- In a locally groupoidal bicategory, every morphism of dotted arrows is invertible. -/
noncomputable instance
    {A A' : DottedArrow sq}
    (η : A ⟶ A') :
    IsIso η where
  out :=
    ⟨invHom η, by
      haveI : IsIso η.right := inferInstance
      apply Hom.ext
      change (η ≫ invHom η).right = (𝟙 A : A ⟶ A).right
      simp, by
      haveI : IsIso η.right := inferInstance
      apply Hom.ext
      change (invHom η ≫ η).right = (𝟙 A' : A' ⟶ A').right
      simp⟩

/-- In a locally groupoidal bicategory, dotted arrows for a fixed square form a groupoid. -/
noncomputable instance : IsGroupoid (DottedArrow sq) where
  all_isIso η := by infer_instance

end LocallyGroupoid

end DottedArrow

namespace BicategoricalTwoCommutativeSquare

variable {T X' Y' X Y : B} {y : T ⟶ Y'} {p : X' ⟶ Y'}
variable (sq : BicategoricalTwoCommutativeSquare y p)
variable {q : X' ⟶ X} {g : Y' ⟶ Y} {f : X ⟶ Y}

/-- Postcomposing a `2`-commutative square with a right square
`p ≫ g ≅ q ≫ f` gives the outer rectangle over `y ≫ g` and `f`. -/
def postcompose (φ : p ≫ g ≅ q ≫ f) :
    BicategoricalTwoCommutativeSquare (y ≫ g) f :=
  { obj := sq.obj
    p := sq.p
    q := sq.q ≫ q
    ψ :=
      (α_ sq.p y g).symm ≪≫
        whiskerRightIso sq.ψ g ≪≫
          α_ sq.q p g ≪≫
            whiskerLeftIso sq.q φ ≪≫
              (α_ sq.q q f).symm }

section

variable {T X' X Y : B} {y : T ⟶ Y} {p : X' ⟶ Y}
variable (sq : BicategoricalTwoCommutativeSquare y p)
variable {q : X' ⟶ X} {f : X ⟶ Y}

/-- Postcomposing a `2`-commutative square with a right triangle `p ≅ q ≫ f` keeps the left edge
fixed and replaces the right edge by `f`. This is the source-facing specialization of
`postcompose` to an identity top edge, with the unitors absorbed into the square itself. -/
def postcomposeRight (φ : p ≅ q ≫ f) :
    BicategoricalTwoCommutativeSquare y f :=
  { obj := sq.obj
    p := sq.p
    q := sq.q ≫ q
    ψ := sq.ψ ≪≫ whiskerLeftIso sq.q φ ≪≫ (α_ sq.q q f).symm }

end

end BicategoricalTwoCommutativeSquare

namespace DottedArrow

section Postcompose

variable {T X' Y' X Y : B} {y : T ⟶ Y'} {p : X' ⟶ Y'}
variable {sq : BicategoricalTwoCommutativeSquare y p}
variable {q : X' ⟶ X} {g : Y' ⟶ Y} {f : X ⟶ Y}

/-- The upper-left comparison induced by postcomposing a dotted arrow with `q`. -/
noncomputable def postcomposeLeft
    (A : DottedArrow sq) :
    sq.p ≫ (A.arrow ≫ q) ≅ sq.q ≫ q :=
  (α_ sq.p A.arrow q).symm ≪≫ whiskerRightIso A.left q

/-- The lower-right comparison induced by postcomposing a dotted arrow with a right square. -/
noncomputable def postcomposeLowerRight
    (φ : p ≫ g ≅ q ≫ f)
    (A : DottedArrow sq) :
    y ≫ g ≅ (A.arrow ≫ q) ≫ f :=
  whiskerRightIso A.right g ≪≫
    α_ A.arrow p g ≪≫
      whiskerLeftIso A.arrow φ ≪≫
        (α_ A.arrow q f).symm

/-- The underlying left lift of the postcomposed dotted arrow. -/
noncomputable abbrev postcomposeToLeftLift
    (φ : p ≫ g ≅ q ≫ f)
    (A : DottedArrow sq) :
    LeftLift f (y ≫ g) :=
  LeftLift.mk (A.arrow ≫ q) (postcomposeLowerRight φ A).hom

theorem postcompose_comm
    (φ : p ≫ g ≅ q ≫ f)
    (A : DottedArrow sq) :
    whiskerLeftIso sq.p (postcomposeLowerRight φ A) ≪≫
        (α_ sq.p (A.arrow ≫ q) f).symm ≪≫
          whiskerRightIso (postcomposeLeft A) f =
      (sq.postcompose φ).ψ := by
  ext
  -- Route correction: transport the original dotted-arrow compatibility through the outer
  -- rectangle shell, and let bicategorical coherence normalize both sides.
  calc
    (whiskerLeftIso sq.p (postcomposeLowerRight φ A) ≪≫
          (α_ sq.p (A.arrow ≫ q) f).symm ≪≫
            whiskerRightIso (postcomposeLeft A) f).hom
        =
          (α_ sq.p y g).inv ≫
            ((sq.p ◁ A.right.hom ≫ (α_ sq.p A.arrow p).inv ≫ A.left.hom ▷ p) ▷ g) ≫
              (α_ sq.q p g).hom ≫
                sq.q ◁ φ.hom ≫
                  (α_ sq.q q f).inv := by
            simp [postcomposeLowerRight, postcomposeLeft, Category.assoc]
            rw [associator_inv_naturality_right_assoc]
            rw [← associator_inv_naturality_left]
            rw [whisker_exchange_assoc]
            bicategory
    _ = (sq.postcompose φ).ψ.hom := by
      simpa [BicategoricalTwoCommutativeSquare.postcompose, Category.assoc] using
        congrArg
          (fun k ↦
            (α_ sq.p y g).inv ≫ (k ▷ g) ≫ (α_ sq.q p g).hom ≫ sq.q ◁ φ.hom ≫
              (α_ sq.q q f).inv)
          (congrArg Iso.hom A.comm)

/-- Postcomposing a dotted arrow with a right square gives a dotted arrow for the outer
rectangle. -/
noncomputable def postcompose
    (φ : p ≫ g ≅ q ≫ f)
    (A : DottedArrow sq) :
    DottedArrow (sq.postcompose φ) := by
  let t : LeftLift f (y ≫ g) := postcomposeToLeftLift φ A
  let _ : IsIso t.unit := by
    change IsIso (postcomposeLowerRight φ A).hom
    infer_instance
  refine
    { toLeftLift := t
      unit_isIso := inferInstance
      comparison := comparisonIsoMk t (postcomposeLeft A) ?_ }
  simpa [t] using congrArg Iso.hom (postcompose_comm φ A)

private theorem postcomposeMap_left_comm
    {A B : DottedArrow sq}
    (θ : A ⟶ B) :
    sq.p ◁ (θ.right ▷ q) ≫ (postcomposeLeft B).hom = (postcomposeLeft A).hom := by
  -- Route correction: package the left-leg compatibility inside the explicit `postcomposeLeft`
  -- shell instead of rewriting in the middle of an associator chain.
  calc
    sq.p ◁ (θ.right ▷ q) ≫ (postcomposeLeft B).hom
        = sq.p ◁ (θ.right ▷ q) ≫ (α_ sq.p B.arrow q).inv ≫ B.left.hom ▷ q := by
            simp [postcomposeLeft, Category.assoc]
    _ = (α_ sq.p A.arrow q).inv ≫ (sq.p ◁ θ.right) ▷ q ≫ B.left.hom ▷ q := by
      rw [associator_inv_naturality_middle_assoc]
    _ = (α_ sq.p A.arrow q).inv ≫ (sq.p ◁ θ.right ≫ B.left.hom) ▷ q := by
      rw [← Category.assoc, comp_whiskerRight]
      simp [Category.assoc]
    _ = (α_ sq.p A.arrow q).inv ≫ A.left.hom ▷ q := by
      rw [Hom.left_comm θ]
    _ = (postcomposeLeft A).hom := by
      simp [postcomposeLeft, Category.assoc]

theorem postcomposeMap_right_comm
    (φ : p ≫ g ≅ q ≫ f)
    {A B : DottedArrow sq}
    (θ : A ⟶ B) :
    (postcomposeLowerRight φ A).hom ≫ (θ.right ▷ q) ▷ f =
      (postcomposeLowerRight φ B).hom := by
  -- Route correction: move the ambient lower-right compatibility through the postcomposition
  -- shell, then use the target-side square data only after the transported term is exposed.
  calc
    (postcomposeLowerRight φ A).hom ≫ (θ.right ▷ q) ▷ f
        = A.right.hom ▷ g ≫
            (α_ A.arrow p g).hom ≫
              A.arrow ◁ φ.hom ≫
                (α_ A.arrow q f).inv ≫
                  θ.right ▷ q ▷ f := by
            simp [postcomposeLowerRight, Category.assoc]
    _ = A.right.hom ▷ g ≫
          (α_ A.arrow p g).hom ≫
            A.arrow ◁ φ.hom ≫
              ((α_ A.arrow q f).inv ≫ θ.right ▷ q ▷ f) := by
          simp [Category.assoc]
    _ = A.right.hom ▷ g ≫
          (α_ A.arrow p g).hom ≫
            A.arrow ◁ φ.hom ≫
              (θ.right ▷ (q ≫ f) ≫
                (α_ B.arrow q f).inv) := by
          rw [← associator_inv_naturality_left]
    _ = A.right.hom ▷ g ≫
          (α_ A.arrow p g).hom ≫
            θ.right ▷ (p ≫ g) ≫
              B.arrow ◁ φ.hom ≫
                (α_ B.arrow q f).inv := by
          rw [whisker_exchange_assoc]
    _ = A.right.hom ▷ g ≫
          θ.right ▷ p ▷ g ≫
            (α_ B.arrow p g).hom ≫
              B.arrow ◁ φ.hom ≫
                (α_ B.arrow q f).inv := by
          rw [← associator_naturality_left_assoc]
    _ = (A.right.hom ≫ θ.right ▷ p) ▷ g ≫
          (α_ B.arrow p g).hom ≫
            B.arrow ◁ φ.hom ≫
              (α_ B.arrow q f).inv := by
          rw [← comp_whiskerRight_assoc]
    _ = B.right.hom ▷ g ≫
          (α_ B.arrow p g).hom ≫
            B.arrow ◁ φ.hom ≫
              (α_ B.arrow q f).inv := by
          simpa [Category.assoc] using
            congrArg
              (fun k ↦ k ▷ g ≫ (α_ B.arrow p g).hom ≫ B.arrow ◁ φ.hom ≫
                (α_ B.arrow q f).inv)
              (Hom.right_comm θ)
    _ = (postcomposeLowerRight φ B).hom := by
      simp [postcomposeLowerRight, Category.assoc]

/-- The induced morphism on postcomposed dotted arrows. -/
noncomputable def postcomposeMap
    (φ : p ≫ g ≅ q ≫ f)
    {A B : DottedArrow sq}
    (θ : A ⟶ B) :
    postcompose φ A ⟶ postcompose φ B :=
  ⟨show postcomposeToLeftLift φ A ⟶ postcomposeToLeftLift φ B from
      LeftLift.homMk (θ.right ▷ q) (postcomposeMap_right_comm φ θ), by
    -- The comparison morphism condition is exactly the already-normalized left compatibility.
    apply StructuredArrow.hom_ext
    change sq.p ◁ (θ.right ▷ q) ≫ (postcomposeLeft B).hom = (postcomposeLeft A).hom
    simpa using postcomposeMap_left_comm (q := q) θ⟩

theorem postcompose_map_id
    (φ : p ≫ g ≅ q ≫ f)
    (A : DottedArrow sq) :
    postcomposeMap φ (𝟙 A) = 𝟙 (postcompose φ A) := by
  -- Equality of dotted-arrow morphisms is detected on the ambient `2`-morphism component.
  apply DottedArrow.Hom.ext
  change (𝟙 A.arrow ▷ q) = 𝟙 (A.arrow ≫ q)
  simp

private theorem postcompose_map_comp
    (φ : p ≫ g ≅ q ≫ f)
    {A B C : DottedArrow sq}
    (η : A ⟶ B) (θ : B ⟶ C) :
    postcomposeMap φ (η ≫ θ) = postcomposeMap φ η ≫ postcomposeMap φ θ := by
  -- The functoriality computation reduces to whiskering a composite `2`-morphism by `q`.
  apply DottedArrow.Hom.ext
  change ((η.right ≫ θ.right) ▷ q) = (η.right ▷ q) ≫ (θ.right ▷ q)
  simp

/-- The canonical functor on dotted-arrow categories induced by postcomposing with a right
square. -/
noncomputable def postcomposeFunctor
    (S : BicategoricalTwoCommutativeSquare y p)
    (φ : p ≫ g ≅ q ≫ f) :
    DottedArrow S ⥤ DottedArrow (S.postcompose φ) where
  obj := postcompose φ
  map := postcomposeMap φ
  map_id := postcompose_map_id φ
  map_comp := by
    intro A B C η θ
    simpa using postcompose_map_comp φ η θ

section PostcomposeRight

variable {T X' X Y : B} {y : T ⟶ Y} {p : X' ⟶ Y}
variable {sq : BicategoricalTwoCommutativeSquare y p}
variable {q : X' ⟶ X} {f : X ⟶ Y}

/-- The lower-right comparison induced by postcomposing a dotted arrow with a right triangle
`p ≅ q ≫ f`. -/
noncomputable def postcomposeRightIso
    (φ : p ≅ q ≫ f)
    (A : DottedArrow sq) :
    y ≅ (A.arrow ≫ q) ≫ f :=
  A.right ≪≫ whiskerLeftIso A.arrow φ ≪≫ (α_ A.arrow q f).symm

theorem postcomposeRight_comm
    (φ : p ≅ q ≫ f)
    (A : DottedArrow sq) :
    whiskerLeftIso sq.p (postcomposeRightIso φ A) ≪≫
        (α_ sq.p (A.arrow ≫ q) f).symm ≪≫
          whiskerRightIso (postcomposeLeft A) f =
      (sq.postcomposeRight φ).ψ := by
  ext
  -- Route correction: specialize the outer-rectangle transport to the case where the top edge is
  -- fixed, so only the right-triangle shell remains around `A.comm`.
  calc
    (whiskerLeftIso sq.p (postcomposeRightIso φ A) ≪≫
          (α_ sq.p (A.arrow ≫ q) f).symm ≪≫
            whiskerRightIso (postcomposeLeft A) f).hom
        =
          (sq.p ◁ A.right.hom ≫ (α_ sq.p A.arrow p).inv ≫ A.left.hom ▷ p) ≫
            sq.q ◁ φ.hom ≫
              (α_ sq.q q f).inv := by
            simp [postcomposeRightIso, postcomposeLeft, Category.assoc]
            rw [associator_inv_naturality_right_assoc]
            rw [← associator_inv_naturality_left]
            rw [whisker_exchange_assoc]
    _ = (sq.postcomposeRight φ).ψ.hom := by
      simpa [BicategoricalTwoCommutativeSquare.postcomposeRight, Category.assoc] using
        congrArg
          (fun k ↦ k ≫ sq.q ◁ φ.hom ≫ (α_ sq.q q f).inv)
          (congrArg Iso.hom A.comm)

/-- Postcomposing a dotted arrow with a right triangle `p ≅ q ≫ f` keeps the left source fixed
and gives a dotted arrow for the resulting source-facing outer square. -/
noncomputable def postcomposeRight
    (φ : p ≅ q ≫ f)
    (A : DottedArrow sq) :
    DottedArrow (sq.postcomposeRight φ) := by
  let t : LeftLift f y := LeftLift.mk (A.arrow ≫ q) (postcomposeRightIso φ A).hom
  let _ : IsIso t.unit := by
    change IsIso (postcomposeRightIso φ A).hom
    infer_instance
  refine
    { toLeftLift := t
      unit_isIso := inferInstance
      comparison := comparisonIsoMk t (postcomposeLeft A) ?_ }
  simpa [t] using congrArg Iso.hom (postcomposeRight_comm φ A)

theorem postcomposeRightMap_right_comm
    (φ : p ≅ q ≫ f)
    {A B : DottedArrow sq}
    (θ : A ⟶ B) :
    (postcomposeRightIso φ A).hom ≫ (θ.right ▷ q) ▷ f = (postcomposeRightIso φ B).hom := by
  -- Route correction: push the lower-right morphism compatibility through the right-triangle
  -- shell in one step, then normalize the coherence data.
  calc
    (postcomposeRightIso φ A).hom ≫ (θ.right ▷ q) ▷ f
        = A.right.hom ≫
            A.arrow ◁ φ.hom ≫
              (α_ A.arrow q f).inv ≫
                θ.right ▷ q ▷ f := by
            simp [postcomposeRightIso, Category.assoc]
    _ = A.right.hom ≫
          A.arrow ◁ φ.hom ≫
            ((α_ A.arrow q f).inv ≫ θ.right ▷ q ▷ f) := by
          simp [Category.assoc]
    _ = A.right.hom ≫
          A.arrow ◁ φ.hom ≫
            (θ.right ▷ (q ≫ f) ≫
              (α_ B.arrow q f).inv) := by
          rw [← associator_inv_naturality_left]
    _ = A.right.hom ≫
          θ.right ▷ p ≫
            B.arrow ◁ φ.hom ≫
              (α_ B.arrow q f).inv := by
          rw [whisker_exchange_assoc]
    _ = B.right.hom ≫ B.arrow ◁ φ.hom ≫ (α_ B.arrow q f).inv := by
          simpa [Category.assoc] using
            congrArg
              (fun k ↦ k ≫ B.arrow ◁ φ.hom ≫ (α_ B.arrow q f).inv)
              (Hom.right_comm θ)
    _ = (postcomposeRightIso φ B).hom := by
      simp [postcomposeRightIso, Category.assoc]

/-- The induced morphism on right-postcomposed dotted arrows. -/
noncomputable def postcomposeRightMap
    (φ : p ≅ q ≫ f)
    {A B : DottedArrow sq}
    (θ : A ⟶ B) :
    postcomposeRight φ A ⟶ postcomposeRight φ B :=
  ⟨show LeftLift.mk (A.arrow ≫ q) (postcomposeRightIso φ A).hom ⟶
        LeftLift.mk (B.arrow ≫ q) (postcomposeRightIso φ B).hom from
      LeftLift.homMk (θ.right ▷ q) (postcomposeRightMap_right_comm φ θ), by
    -- The upper-left comparison is unchanged, so the same left-transport lemma applies.
    apply StructuredArrow.hom_ext
    change sq.p ◁ (θ.right ▷ q) ≫ (postcomposeLeft B).hom = (postcomposeLeft A).hom
    simpa using postcomposeMap_left_comm (q := q) θ⟩

theorem postcomposeRight_map_id
    (φ : p ≅ q ≫ f)
    (A : DottedArrow sq) :
    postcomposeRightMap φ (𝟙 A) = 𝟙 (postcomposeRight φ A) := by
  -- Equality again reduces to the whiskered ambient `2`-morphism.
  apply DottedArrow.Hom.ext
  change (𝟙 A.arrow ▷ q) = 𝟙 (A.arrow ≫ q)
  simp

private theorem postcomposeRight_map_comp
    (φ : p ≅ q ≫ f)
    {A B C : DottedArrow sq}
    (η : A ⟶ B) (θ : B ⟶ C) :
    postcomposeRightMap φ (η ≫ θ) = postcomposeRightMap φ η ≫ postcomposeRightMap φ θ := by
  -- Composition is preserved because right whiskering distributes over vertical composition.
  apply DottedArrow.Hom.ext
  change ((η.right ≫ θ.right) ▷ q) = (η.right ▷ q) ≫ (θ.right ▷ q)
  simp

/-- The canonical functor on dotted-arrow categories induced by postcomposing with a right
triangle `p ≅ q ≫ f`. -/
noncomputable def postcomposeRightFunctor
    (S : BicategoricalTwoCommutativeSquare y p)
    (φ : p ≅ q ≫ f) :
    DottedArrow S ⥤ DottedArrow (S.postcomposeRight φ) where
  obj := postcomposeRight φ
  map := postcomposeRightMap φ
  map_id := postcomposeRight_map_id φ
  map_comp := by
    intro A B C η θ
    simpa using postcomposeRight_map_comp φ η θ

end PostcomposeRight

end Postcompose

end DottedArrow

end CategoryTheory
