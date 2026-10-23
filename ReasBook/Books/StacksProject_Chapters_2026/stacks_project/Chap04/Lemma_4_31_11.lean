module

public import stacks_project.Chap04.Example_4_30_2
public import stacks_project.Chap04.Lemma_4_31_4
public import stacks_project.Chap04.Lemma_4_31_6
public import stacks_project.Chap04.Remark_4_31_5
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Terminal
import Mathlib.CategoryTheory.Adjunction.Limits
import Mathlib.CategoryTheory.Limits.Shapes.Equivalence

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits

namespace CategoryTheory.Limits

open CategoricalPullback
open CategoricalPullback.CatCommSqOver
open scoped CategoricalPullback

universe v u

-- Tag 02XE lives in the `(2,1)` setting: the categories below are groupoids.  (The point-lift
-- machinery forces the object and hom universes of the apexes to coincide, so we use `Type v`.)
variable {A : Type v} [Category.{v} A] [IsGroupoid A]
variable {B : Type v} [Category.{v} B] [IsGroupoid B]
variable {S : Type v} [Category.{v} S] [IsGroupoid S]

/-- Helper for Lemma 4.31.11: the fixed one-point discrete category used to probe point-lifts. -/
abbrev OnePointCat : Type v :=
  Discrete (ULift.{v, 0} Unit)

/-- Helper for Lemma 4.31.11: the unique object of `OnePointCat`. -/
abbrev onePoint : OnePointCat :=
  ⟨⟨()⟩⟩

/- Domain-style sampling for Lemma 4.31.11:
- primary domain: bicategorical `2`-fibre products in `Cat`, presented through categorical
  pullbacks of functors;
- owner abstractions:
  `BicategoricalTwoCommutativeSquare` and `Bicategory.IsFinal` from Definitions `4.31.2`
  and `4.31.1`,
  `CategoricalPullback.CatCommSqOver` with
  `CatCommSqOver.toFunctorToCategoricalPullback` and
  `CatCommSqOver.toBicategoricalSquare` as the categorical bridge/view API, and
  `symmetricTwoFibreProductComparison` from Remark `4.31.5` as the owner-level comparison from
  the diagonal pullback model to the ordinary pullback model.

Primitive-vs-derived split:
- primitive data: a square `P : CatCommSqOver (G₁.prod G₂) (Functor.diag S) X`;
- derived API: the associated bicategorical square in `Cat`, the comparison functor to
  `A ×[S] B`, and the resulting equivalence object obtained from that comparison functor.

Source/core/bridge triage:
- `source-facing`: the displayed `2`-commutative square over `G₁ × G₂` and `Δ_S`;
- `core/canonical`: `Bicategory.IsFinal` of the associated object of
  `BicategoricalTwoCommutativeSquare (G₁.prod G₂).toCatHom (Functor.diag S).toCatHom`;
- `bridge/view`: `CatCommSqOver.toFunctorToCategoricalPullback` and
  `symmetricTwoFibreProductComparison`. -/

noncomputable section

variable (G₁ : A ⥤ S) (G₂ : B ⥤ S)
variable {X : Type v} [Category.{v} X] [IsGroupoid X]
variable (P : CatCommSqOver (G₁.prod G₂) (Functor.diag S) X)

/-- Helper for Lemma 4.31.11: whiskering a fixed square `Q` by a functor `J` produces the source
square used to package universal arrows into `Q`. -/
abbrev whisker_source_square
    {A' : Type u} [Category.{v} A']
    {B' : Type u} [Category.{v} B']
    {C' : Type u} [Category.{v} C']
    {X' : Type u} [Category.{v} X']
    {Y : Type u} [Category.{v} Y]
    {F : A' ⥤ C'} {G : B' ⥤ C'}
    (Q : CatCommSqOver F G X')
    (J : Y ⥤ X') :
    CatCommSqOver F G Y where
  fst := J ⋙ Q.fst
  snd := J ⋙ Q.snd
  iso :=
    Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft J Q.iso ≪≫
      (Functor.associator _ _ _).symm

/-- Helper for Lemma 4.31.11: varying the whiskering functor `J` makes
`whisker_source_square Q J` functorial. -/
abbrev whisker_source_square_functor
    {A' : Type u} [Category.{v} A']
    {B' : Type u} [Category.{v} B']
    {C' : Type u} [Category.{v} C']
    {X' : Type u} [Category.{v} X']
    {Y : Type u} [Category.{v} Y]
    {F : A' ⥤ C'} {G : B' ⥤ C'}
    (Q : CatCommSqOver F G X') :
    (Y ⥤ X') ⥤ CatCommSqOver F G Y where
  obj J := whisker_source_square Q J
  map η := by
    -- A natural transformation between apex functors whiskers the two legs of `Q`.
    refine
      { fst := Functor.whiskerRight η Q.fst
        snd := Functor.whiskerRight η Q.snd
        w := ?_ }
    ext x
    simpa [whisker_source_square, Category.assoc] using Q.iso.hom.naturality (η.app x)
  map_id := by
    -- The whiskered identity transformation is componentwise the identity on both legs.
    intro J
    ext <;> simp
  map_comp := by
    -- Composition of whiskered transformations is computed componentwise.
    intro J K L η θ
    ext <;> simp

/-- Helper for Lemma 4.31.11: from finality of `Q`, the canonical pullback square maps back to
`Q`. This is the source-faithful quasi-inverse square morphism. -/
noncomputable abbrev comparison_inverse_square_hom
    {A' : Type _} [Category.{v} A']
    {B' : Type _} [Category.{v} B']
    {C' : Type _} [Category.{v} C']
    {X' : Type _} [Category.{v} X']
    {F : A' ⥤ C'} {G : B' ⥤ C'}
    (Q : CatCommSqOver F G X')
    [Bicategory.IsFinal Q.toBicategoricalSquare] :
    categoricalPullbackSquare F G ⟶ Q.toBicategoricalSquare :=
  ⊤_ (categoricalPullbackSquare F G ⟶ Q.toBicategoricalSquare)

/-- Helper for Lemma 4.31.11: a square morphism into `Q` is the same data as a costructured arrow
into the whiskered-square functor attached to `Q`. -/
abbrev square_hom_to_costructuredArrow
    {A' : Type _} [Category.{v} A']
    {B' : Type _} [Category.{v} B']
    {C' : Type _} [Category.{v} C']
    {X' : Type _} [Category.{v} X']
    {Y : Type _} [Category.{v} Y]
    {F : A' ⥤ C'} {G : B' ⥤ C'}
    (R : CatCommSqOver F G Y)
    (Q : CatCommSqOver F G X')
    (u : R.toBicategoricalSquare ⟶ Q.toBicategoricalSquare) :
    CostructuredArrow (whisker_source_square_functor Q) R :=
  CostructuredArrow.mk
    ({ fst := u.left.toNatTrans
       snd := u.right.toNatTrans
       w := by
         -- The square-morphism compatibility is exactly the whiskered-square equation after
         -- translating the bicategorical `Cat`-morphism to ordinary natural transformations.
         dsimp [whisker_source_square]
         simpa only [← Category.assoc] using
           congrArg (fun τ ↦ τ.toNatTrans) u.comm } :
      whisker_source_square Q u.hom.toFunctor ⟶ R)

/-- Helper for Lemma 4.31.11: the `CatCommSqOver` compatibility of a costructured arrow is the
bicategorical square-morphism compatibility for the recovered square map. -/
theorem costructuredArrowToSquareHomComm
    {A' : Type _} [Category.{v} A']
    {B' : Type _} [Category.{v} B']
    {C' : Type _} [Category.{v} C']
    {X' : Type _} [Category.{v} X']
    {Y : Type _} [Category.{v} Y]
    {F : A' ⥤ C'} {G : B' ⥤ C'}
    (R : CatCommSqOver F G Y)
    (Q : CatCommSqOver F G X')
    (a : CostructuredArrow (whisker_source_square_functor Q) R) :
    Bicategory.whiskerRight (NatTrans.toCatHom₂ a.hom.fst) F.toCatHom ≫
        R.toBicategoricalSquare.ψ.hom =
      (Bicategory.associator a.left.toCatHom Q.toBicategoricalSquare.p F.toCatHom).hom ≫
        Bicategory.whiskerLeft a.left.toCatHom Q.toBicategoricalSquare.ψ.hom ≫
        (Bicategory.associator a.left.toCatHom Q.toBicategoricalSquare.q G.toCatHom).inv ≫
        Bicategory.whiskerRight (NatTrans.toCatHom₂ a.hom.snd) G.toCatHom := by
  -- Evaluate the bicategorical square equation objectwise; after simplifying the associators and
  -- whiskering, this is exactly the `CatCommSqOver` compatibility of `a.hom`.
  apply Cat.Hom₂.ext
  ext x
  change (Functor.whiskerRight a.hom.fst F ≫ R.iso.hom).app x =
      ((a.left.associator Q.fst F).hom ≫
            a.left.whiskerLeft Q.iso.hom ≫ (a.left.associator Q.snd G).inv ≫
              Functor.whiskerRight a.hom.snd G).app x
  simpa [whisker_source_square] using congrArg (fun τ ↦ τ.app x) a.hom.w

/-- Helper for Lemma 4.31.11: a costructured arrow into the whiskered-square functor recovers the
corresponding square morphism into `Q`. -/
abbrev costructuredArrow_to_square_hom
    {A' : Type _} [Category.{v} A']
    {B' : Type _} [Category.{v} B']
    {C' : Type _} [Category.{v} C']
    {X' : Type _} [Category.{v} X']
    {Y : Type _} [Category.{v} Y]
    {F : A' ⥤ C'} {G : B' ⥤ C'}
    (R : CatCommSqOver F G Y)
    (Q : CatCommSqOver F G X')
    (a : CostructuredArrow (whisker_source_square_functor Q) R) :
    R.toBicategoricalSquare ⟶ Q.toBicategoricalSquare :=
  { hom := a.left.toCatHom
    left := a.hom.fst.toCatHom₂
    right := a.hom.snd.toCatHom₂
    comm := costructuredArrowToSquareHomComm R Q a }

/-- Helper for Lemma 4.31.11: a `2`-morphism of square maps becomes the corresponding morphism in
the comma category of whiskered squares. -/
lemma square_twohom_to_costructuredArrow_hom_eq
    {A' : Type _} [Category.{v} A']
    {B' : Type _} [Category.{v} B']
    {C' : Type _} [Category.{v} C']
    {X' : Type _} [Category.{v} X']
    {Y : Type _} [Category.{v} Y]
    {F : A' ⥤ C'} {G : B' ⥤ C'}
    (R : CatCommSqOver F G Y)
    (Q : CatCommSqOver F G X')
    {u v : R.toBicategoricalSquare ⟶ Q.toBicategoricalSquare}
    (η : u ⟶ v) :
    (whisker_source_square_functor Q).map η.hom.toNatTrans ≫
        (square_hom_to_costructuredArrow R Q v).hom =
      (square_hom_to_costructuredArrow R Q u).hom := by
  -- Equality in the comma category is detected on the two displayed natural-transformation legs.
  apply CatCommSqOver.hom_ext
  · ext x
    simpa [whisker_source_square_functor, whisker_source_square] using
      congrArg (fun τ ↦ τ.app x) (congrArg Cat.Hom₂.toNatTrans η.left_comm)
  · ext x
    simpa [whisker_source_square_functor, whisker_source_square] using
      congrArg (fun τ ↦ τ.app x) (congrArg Cat.Hom₂.toNatTrans η.right_comm)

/-- Helper for Lemma 4.31.11: morphisms in the comma category of whiskered squares recover the
corresponding square `2`-morphisms. -/
abbrev square_hom_equiv_costructuredArrow
    {A' : Type _} [Category.{v} A']
    {B' : Type _} [Category.{v} B']
    {C' : Type _} [Category.{v} C']
    {X' : Type _} [Category.{v} X']
    {Y : Type _} [Category.{v} Y]
    {F : A' ⥤ C'} {G : B' ⥤ C'}
    (R : CatCommSqOver F G Y)
    (Q : CatCommSqOver F G X') :
    (R.toBicategoricalSquare ⟶ Q.toBicategoricalSquare) ≌
      CostructuredArrow (whisker_source_square_functor Q) R :=
  let forward :
      (R.toBicategoricalSquare ⟶ Q.toBicategoricalSquare) ⥤
        CostructuredArrow (whisker_source_square_functor Q) R :=
    { obj := square_hom_to_costructuredArrow R Q
      map := fun η ↦
        CostructuredArrow.homMk
          η.hom.toNatTrans
          (square_twohom_to_costructuredArrow_hom_eq R Q η)
      map_id := by
        -- Identity `2`-morphisms become identity comma morphisms on the whiskered apex functor.
        intro u
        apply CostructuredArrow.hom_ext
        rfl
      map_comp := by
        -- Vertical composition of `2`-morphisms is sent to composition in the comma category.
        intro u v w η θ
        apply CostructuredArrow.hom_ext
        rfl }
  let backward :
      CostructuredArrow (whisker_source_square_functor Q) R ⥤
        (R.toBicategoricalSquare ⟶ Q.toBicategoricalSquare) :=
    { obj := costructuredArrow_to_square_hom R Q
      map := fun η ↦
        { hom := by
            simpa [costructuredArrow_to_square_hom] using η.left.toCatHom₂
          left_comm := by
            -- The left projection of the comma-category relation becomes the left-leg
            -- compatibility.
            apply Cat.Hom₂.ext
            ext x
            simpa [costructuredArrow_to_square_hom, whisker_source_square_functor,
              whisker_source_square] using
              congrArg (fun τ ↦ τ.app x)
                (congrArg CatCommSqOver.Hom.fst (CostructuredArrow.w η))
          right_comm := by
            -- The right projection gives the matching compatibility on the right leg.
            apply Cat.Hom₂.ext
            ext x
            simpa [costructuredArrow_to_square_hom, whisker_source_square_functor,
              whisker_source_square] using
              congrArg (fun τ ↦ τ.app x)
                (congrArg CatCommSqOver.Hom.snd (CostructuredArrow.w η)) }
      map_id := by
        -- Identity comma morphisms translate back to identity `2`-morphisms of square maps.
        intro a
        apply BicategoricalTwoCommutativeSquare.TwoHom.ext
        rfl
      map_comp := by
        -- Composition is preserved because the reconstruction keeps the same apex
        -- natural transformation.
        intro a b c η θ
        apply BicategoricalTwoCommutativeSquare.TwoHom.ext
        rfl }
  let unitIso :
      𝟭 (R.toBicategoricalSquare ⟶ Q.toBicategoricalSquare) ≅ forward ⋙ backward :=
    NatIso.ofComponents
      (fun u ↦
        CategoryTheory.eqToIso <| by
          -- Unpacking the forward-then-backward conversion returns the original square map.
          rcases u with ⟨hom, left, right, comm⟩
          rfl)
      (fun {u v} η ↦ by
        -- After reducing both round-trip equalities, naturality is the identity computation on
        -- the underlying apex `2`-morphism.
        rcases u with ⟨uhom, uleft, uright, ucomm⟩
        rcases v with ⟨vhom, vleft, vright, vcomm⟩
        rcases η with ⟨ηhom, ηleft, ηright⟩
        apply BicategoricalTwoCommutativeSquare.TwoHom.ext
        change ηhom ≫ 𝟙 vhom = 𝟙 uhom ≫ ηhom
        simp)
  let counitIso :
      backward ⋙ forward ≅ 𝟭 (CostructuredArrow (whisker_source_square_functor Q) R) :=
    NatIso.ofComponents
      (fun a ↦
        CategoryTheory.eqToIso <| by
          -- The reverse round-trip preserves the apex functor and the displayed square morphism
          -- into `R`.
          rcases a with ⟨left, hom⟩
          rfl)
      (fun {a b} η ↦ by
        -- The counit naturality is the same identity computation in the comma category.
        rcases a with ⟨aleft, ahom⟩
        rcases b with ⟨bleft, bhom⟩
        rcases η with ⟨ηleft, ηw⟩
        simp [forward, backward])
  CategoryTheory.Equivalence.mk forward backward unitIso counitIso

/-- Helper for Lemma 4.31.11: converting a square map to a costructured arrow and back leaves the
square map unchanged. -/
@[simp] theorem squareHomCostructuredArrowRoundtrip
    {A' : Type _} [Category.{v} A']
    {B' : Type _} [Category.{v} B']
    {C' : Type _} [Category.{v} C']
    {X' : Type _} [Category.{v} X']
    {Y : Type _} [Category.{v} Y]
    {F : A' ⥤ C'} {G : B' ⥤ C'}
    (R : CatCommSqOver F G Y)
    (Q : CatCommSqOver F G X') :
    ∀ u : R.toBicategoricalSquare ⟶ Q.toBicategoricalSquare,
      costructuredArrow_to_square_hom R Q
        (square_hom_to_costructuredArrow R Q u) = u := by
  intro u
  -- Unpacking the forward-then-backward conversion returns the original square map.
  rcases u with ⟨hom, left, right, comm⟩
  rfl

/-- Helper for Lemma 4.31.11: converting a costructured arrow to a square map and back leaves the
costructured arrow unchanged. -/
@[simp] theorem costructuredArrowSquareHomRoundtrip
    {A' : Type _} [Category.{v} A']
    {B' : Type _} [Category.{v} B']
    {C' : Type _} [Category.{v} C']
    {X' : Type _} [Category.{v} X']
    {Y : Type _} [Category.{v} Y]
    {F : A' ⥤ C'} {G : B' ⥤ C'}
    (R : CatCommSqOver F G Y)
    (Q : CatCommSqOver F G X') :
    ∀ a : CostructuredArrow (whisker_source_square_functor Q) R,
      square_hom_to_costructuredArrow R Q
        (costructuredArrow_to_square_hom R Q a) = a := by
  intro a
  -- The reverse round-trip preserves the apex functor and the displayed square morphism into `R`.
  rcases a with ⟨left, hom⟩
  rfl

/-- Helper for Lemma 4.31.11: finality of `Q` transfers to terminal objects in the comma
categories attached to whiskering into `Q`. -/
noncomputable instance costructuredArrow_hasTerminal_of_isFinal
    {A' : Type _} [Category.{v} A']
    {B' : Type _} [Category.{v} B']
    {C' : Type _} [Category.{v} C']
    {X' : Type _} [Category.{v} X']
    {Y : Type _} [Category.{v} Y]
    {F : A' ⥤ C'} {G : B' ⥤ C'}
    (R : CatCommSqOver F G Y)
    (Q : CatCommSqOver F G X')
    [Bicategory.IsFinal Q.toBicategoricalSquare] :
    HasTerminal (CostructuredArrow (whisker_source_square_functor Q) R) := by
  -- Finality of `Q` gives a terminal object in the hom-category, and the equivalence above
  -- transports that terminal object to the corresponding comma category.
  let e := square_hom_equiv_costructuredArrow R Q
  letI : e.inverse.IsEquivalence := e.symm.isEquivalence_functor
  exact CategoryTheory.hasTerminal_of_equivalence e.inverse

/-- Helper for Lemma 4.31.11: the forward comparison square map from `Q` to the canonical
categorical pullback square is the terminal factorization from Lemma `4.31.4`. -/
abbrev comparison_square_hom
    {A' : Type _} [Category.{v} A']
    {B' : Type _} [Category.{v} B']
    {C' : Type _} [Category.{v} C']
    {X' : Type _} [Category.{v} X']
    {F : A' ⥤ C'} {G : B' ⥤ C'}
    (Q : CatCommSqOver F G X') :
    Q.toBicategoricalSquare ⟶ categoricalPullbackSquare F G :=
  terminal_lift F G Q.toBicategoricalSquare

/-- Helper for Lemma 4.31.11: the left comparison component of `comparison_square_hom Q` is
pointwise the identity. -/
@[simp] theorem comparisonSquareHomLeftApp
    {A' : Type _} [Category.{v} A']
    {B' : Type _} [Category.{v} B']
    {C' : Type _} [Category.{v} C']
    {X' : Type _} [Category.{v} X']
    {F : A' ⥤ C'} {G : B' ⥤ C'}
    (Q : CatCommSqOver F G X')
    (x : X') :
    (comparison_square_hom Q).left.toNatTrans.app x = 𝟙 (Q.fst.obj x) := by
  -- The canonical comparison functor is defined using the pullback counit, which is identity on
  -- the first projection.
  rfl

/-- Helper for Lemma 4.31.11: the right comparison component of `comparison_square_hom Q` is
pointwise the identity. -/
@[simp] theorem comparisonSquareHomRightApp
    {A' : Type _} [Category.{v} A']
    {B' : Type _} [Category.{v} B']
    {C' : Type _} [Category.{v} C']
    {X' : Type _} [Category.{v} X']
    {F : A' ⥤ C'} {G : B' ⥤ C'}
    (Q : CatCommSqOver F G X')
    (x : X') :
    (comparison_square_hom Q).right.toNatTrans.app x = 𝟙 (Q.snd.obj x) := by
  -- The second projection is handled symmetrically by the same counit computation.
  rfl

/-- Helper for Lemma 4.31.11: the canonical pullback square over `F` and `G`, viewed as an object
of `CatCommSqOver`, is the target of the comparison-whiskering transport. -/
abbrev canonicalComparisonSquare
    {A' : Type _} [Category.{v} A']
    {B' : Type _} [Category.{v} B']
    {C' : Type _} [Category.{v} C']
    {F : A' ⥤ C'} {G : B' ⥤ C'} :
    CatCommSqOver F G (F ⊡ G) :=
  (toCatCommSqOver F G (F ⊡ G)).obj (𝟭 (F ⊡ G))

/-- Helper for Lemma 4.31.11: the chosen terminal lift from the canonical pullback square back to
`Q` is the quasi-inverse functor candidate for the pullback comparison. -/
abbrev comparisonInverseFunctor
    {A' : Type _} [Category.{v} A']
    {B' : Type _} [Category.{v} B']
    {C' : Type _} [Category.{v} C']
    {X' : Type _} [Category.{v} X']
    {F : A' ⥤ C'} {G : B' ⥤ C'}
    (Q : CatCommSqOver F G X')
    [Bicategory.IsFinal Q.toBicategoricalSquare] :
    F ⊡ G ⥤ X' :=
  (comparison_inverse_square_hom Q).hom.toFunctor

/-- Helper for Lemma 4.31.11: whiskering the canonical pullback square is definitionally the same
as applying `toCatCommSqOver` to the chosen apex functor. -/
abbrev canonicalComparisonWhiskerSourceSquareFunctor
    {A' : Type _} [Category.{v} A']
    {B' : Type _} [Category.{v} B']
    {C' : Type _} [Category.{v} C']
    {Y : Type _} [Category.{v} Y]
    {F : A' ⥤ C'} {G : B' ⥤ C'} :
    whisker_source_square_functor (canonicalComparisonSquare (F := F) (G := G)) ≅
      toCatCommSqOver F G Y :=
  NatIso.ofComponents
    (fun J ↦ by
      -- The canonical pullback square is already the `toCatCommSqOver` image of the identity.
      refine CatCommSqOver.mkIso (Iso.refl _) (Iso.refl _) ?_
      ext y
      simp [whisker_source_square, canonicalComparisonSquare, toCatCommSqOver])
    (fun {_ _} η ↦ by
      -- Both functors act on morphisms by whiskering the same projection transformations.
      apply CatCommSqOver.hom_ext <;> ext y <;>
        simp [whisker_source_square_functor, whisker_source_square, canonicalComparisonSquare,
          toCatCommSqOver])

/-- Helper for Lemma 4.31.11: objectwise, whiskering by the comparison functor identifies the
source square for `Q` with the source square for the canonical pullback square. -/
theorem whiskerSourceSquareFunctorComparisonObjIsoW
    {A' : Type _} [Category.{v} A']
    {B' : Type _} [Category.{v} B']
    {C' : Type _} [Category.{v} C']
    {X' : Type _} [Category.{v} X']
    {Y : Type _} [Category.{v} Y]
    {F : A' ⥤ C'} {G : B' ⥤ C'}
    (Q : CatCommSqOver F G X')
    (J : Y ⥤ X') :
    Functor.whiskerRight
        (Iso.refl ((whisker_source_square Q J).fst)).hom F ≫
        (((Functor.whiskeringRight Y X' (F ⊡ G)).obj
              ((toFunctorToCategoricalPullback F G X').obj Q) ⋙
            whisker_source_square_functor
              (canonicalComparisonSquare (F := F) (G := G))).obj J).iso.hom =
      (whisker_source_square Q J).iso.hom ≫
        Functor.whiskerRight
          (Iso.refl ((whisker_source_square Q J).snd)).hom G := by
  -- Both objectwise square descriptions have identical components after unfolding the comparison
  -- functor into the canonical pullback square.
  ext x
  simp [whisker_source_square, canonicalComparisonSquare]

/-- Helper for Lemma 4.31.11: objectwise, whiskering by the comparison functor identifies the
source square for `Q` with the source square for the canonical pullback square. -/
abbrev whiskerSourceSquareFunctorComparisonObjIso
    {A' : Type _} [Category.{v} A']
    {B' : Type _} [Category.{v} B']
    {C' : Type _} [Category.{v} C']
    {X' : Type _} [Category.{v} X']
    {Y : Type _} [Category.{v} Y]
    {F : A' ⥤ C'} {G : B' ⥤ C'}
    (Q : CatCommSqOver F G X')
    (J : Y ⥤ X') :
    whisker_source_square Q J ≅
      (((Functor.whiskeringRight Y X' (F ⊡ G)).obj
            ((toFunctorToCategoricalPullback F G X').obj Q)) ⋙
          whisker_source_square_functor
            (canonicalComparisonSquare (F := F) (G := G))).obj J :=
  CatCommSqOver.mkIso (Iso.refl _) (Iso.refl _)
    (whiskerSourceSquareFunctorComparisonObjIsoW Q J)

/-- Helper for Lemma 4.31.11: the objectwise comparison above is natural in the whiskering
functor `J`. -/
theorem whiskerSourceSquareFunctorComparisonIsoNaturality
    {A' : Type _} [Category.{v} A']
    {B' : Type _} [Category.{v} B']
    {C' : Type _} [Category.{v} C']
    {X' : Type _} [Category.{v} X']
    {Y : Type _} [Category.{v} Y]
    {F : A' ⥤ C'} {G : B' ⥤ C'}
    (Q : CatCommSqOver F G X') :
    ∀ {J K : Y ⥤ X'} (η : J ⟶ K),
      (whisker_source_square_functor Q).map η ≫
          (whiskerSourceSquareFunctorComparisonObjIso Q K).hom =
        (whiskerSourceSquareFunctorComparisonObjIso Q J).hom ≫
          (((Functor.whiskeringRight Y X' (F ⊡ G)).obj
                ((toFunctorToCategoricalPullback F G X').obj Q) ⋙
              whisker_source_square_functor
                (canonicalComparisonSquare (F := F) (G := G))).map η) := by
  -- The comparison is identity on both displayed components, so naturality is componentwise.
  intro J K η
  apply CatCommSqOver.hom_ext <;> ext x <;>
    simp [whiskerSourceSquareFunctorComparisonObjIso, whisker_source_square,
      canonicalComparisonSquare]

/-- Helper for Lemma 4.31.11: whiskering by the comparison functor turns a source square for `Q`
into the corresponding source square for the canonical pullback square. -/
abbrev whiskerSourceSquareFunctorComparisonIso
    {A' : Type _} [Category.{v} A']
    {B' : Type _} [Category.{v} B']
    {C' : Type _} [Category.{v} C']
    {X' : Type _} [Category.{v} X']
    {Y : Type _} [Category.{v} Y]
    {F : A' ⥤ C'} {G : B' ⥤ C'}
    (Q : CatCommSqOver F G X') :
    whisker_source_square_functor Q ≅
      ((Functor.whiskeringRight Y X' (F ⊡ G)).obj
          ((toFunctorToCategoricalPullback F G X').obj Q)) ⋙
        whisker_source_square_functor
          (canonicalComparisonSquare (F := F) (G := G)) :=
  NatIso.ofComponents
    (whiskerSourceSquareFunctorComparisonObjIso Q)
    (whiskerSourceSquareFunctorComparisonIsoNaturality Q)

/-- Helper for Lemma 4.31.11: the comma categories for source squares over `Q` identify with the
comma categories obtained by whiskering the pullback comparison functor against `toCatCommSqOver`.
-/
abbrev comparisonCostructuredArrowTransport
    {A' : Type _} [Category.{v} A']
    {B' : Type _} [Category.{v} B']
    {C' : Type _} [Category.{v} C']
    {X' : Type _} [Category.{v} X']
    {Y : Type _} [Category.{v} Y]
    {F : A' ⥤ C'} {G : B' ⥤ C'}
    (Q : CatCommSqOver F G X')
    (R : CatCommSqOver F G Y) :
    CostructuredArrow (whisker_source_square_functor Q) R ≌
      CostructuredArrow
        (((Functor.whiskeringRight Y X' (F ⊡ G)).obj
            ((toFunctorToCategoricalPullback F G X').obj Q)) ⋙
          toCatCommSqOver F G Y)
        R :=
  -- First replace source squares for `Q` by whiskering the canonical pullback square, and then
  -- identify the canonical whiskering with `toCatCommSqOver`.
  (CostructuredArrow.mapNatIso (whiskerSourceSquareFunctorComparisonIso (Y := Y) Q)).trans
    (CostructuredArrow.mapNatIso
      (Functor.isoWhiskerLeft
        ((Functor.whiskeringRight Y X' (F ⊡ G)).obj
          ((toFunctorToCategoricalPullback F G X').obj Q))
        (canonicalComparisonWhiskerSourceSquareFunctor (Y := Y) (F := F) (G := G))))

/-- Helper for Lemma 4.31.11: the one-point source square attached to a pullback object `Y`
packages `Y` as a square over `F` and `G`. -/
abbrev pullbackPointSquare
    {A' : Type _} [Category.{v} A']
    {B' : Type _} [Category.{v} B']
    {C' : Type _} [Category.{v} C']
    {F : A' ⥤ C'} {G : B' ⥤ C'}
    (Y : F ⊡ G) :
    CatCommSqOver F G OnePointCat :=
  (toCatCommSqOver F G OnePointCat).obj ((Functor.const OnePointCat).obj Y)

/-- Helper for Lemma 4.31.11: for a point `x : X'`, the corresponding constant functor into `Q`
gives the evident point-lift over the one-point square of `K.obj x`. -/
abbrev pullbackPointLift
    {A' : Type _} [Category.{v} A']
    {B' : Type _} [Category.{v} B']
    {C' : Type _} [Category.{v} C']
    {X' : Type _} [Category.{v} X']
    {F : A' ⥤ C'} {G : B' ⥤ C'}
    (Q : CatCommSqOver F G X')
    (x : X')
    [Bicategory.IsFinal Q.toBicategoricalSquare] :
    CostructuredArrow
      (whisker_source_square_functor Q)
      (pullbackPointSquare (((toFunctorToCategoricalPullback F G X').obj Q).obj x)) :=
  CostructuredArrow.mk
    ({ fst :=
         { app := fun _ ↦ 𝟙 _
           naturality := by
             intro p q f
             simp }
       snd :=
         { app := fun _ ↦ 𝟙 _
           naturality := by
             intro p q f
             simp }
       w := by
         -- The point square of `K.obj x` is definitionally the whiskered square of `Q` at the
         -- constant functor on `x`.
         ext p
         cases p
         simp [pullbackPointSquare, whisker_source_square, toFunctorToCategoricalPullback] } :
      whisker_source_square Q ((Functor.const OnePointCat).obj x) ⟶
        pullbackPointSquare (((toFunctorToCategoricalPullback F G X').obj Q).obj x))

/-- Helper for Lemma 4.31.11: the left leg of `pullbackPointLift Q x` is pointwise the identity. -/
@[simp] theorem pullbackPointLift_fst_app
    {A' : Type _} [Category.{v} A']
    {B' : Type _} [Category.{v} B']
    {C' : Type _} [Category.{v} C']
    {X' : Type _} [Category.{v} X']
    {F : A' ⥤ C'} {G : B' ⥤ C'}
    (Q : CatCommSqOver F G X')
    (x : X')
    [Bicategory.IsFinal Q.toBicategoricalSquare] :
    ∀ p : OnePointCat,
      (pullbackPointLift Q x).hom.fst.app p = 𝟙 (Q.fst.obj x) := by
  -- By construction, the left component of the point-lift is the identity transformation.
  intro p
  rfl

/-- Helper for Lemma 4.31.11: the right leg of `pullbackPointLift Q x` is pointwise the identity. -/
@[simp] theorem pullbackPointLift_snd_app
    {A' : Type _} [Category.{v} A']
    {B' : Type _} [Category.{v} B']
    {C' : Type _} [Category.{v} C']
    {X' : Type _} [Category.{v} X']
    {F : A' ⥤ C'} {G : B' ⥤ C'}
    (Q : CatCommSqOver F G X')
    (x : X')
    [Bicategory.IsFinal Q.toBicategoricalSquare] :
    ∀ p : OnePointCat,
      (pullbackPointLift Q x).hom.snd.app p = 𝟙 (Q.snd.obj x) := by
  -- The right component is built symmetrically from identity arrows.
  intro p
  rfl

/-- Helper for Lemma 4.31.11: in the transported comma category over
`pullbackPointSquare (((toFunctorToCategoricalPullback F G X').obj Q).obj x)`, the explicit
identity point-lift is the object whose source is constantly `x` and whose two displayed
components are identities. -/
abbrev targetIdentityPointLift
    {A' : Type _} [Category.{v} A']
    {B' : Type _} [Category.{v} B']
    {C' : Type _} [Category.{v} C']
    {X' : Type _} [Category.{v} X']
    {F : A' ⥤ C'} {G : B' ⥤ C'}
    (Q : CatCommSqOver F G X')
    (x : X') :
    CostructuredArrow
      (((Functor.whiskeringRight OnePointCat X' (F ⊡ G)).obj
          ((toFunctorToCategoricalPullback F G X').obj Q)) ⋙
        toCatCommSqOver F G OnePointCat)
      (pullbackPointSquare (((toFunctorToCategoricalPullback F G X').obj Q).obj x)) :=
  CostructuredArrow.mk
    ({ fst :=
         { app := fun _ ↦ 𝟙 (Q.fst.obj x)
           naturality := by
             intro p q f
             cases p
             cases q
             simp }
       snd :=
         { app := fun _ ↦ 𝟙 (Q.snd.obj x)
           naturality := by
             intro p q f
             cases p
             cases q
             simp }
       w := by
         -- The explicit identity point-lift satisfies the pullback relation by the defining
         -- commutativity of the object `((toFunctorToCategoricalPullback F G X').obj Q).obj x`.
         ext p
         cases p
         simp [pullbackPointSquare, toFunctorToCategoricalPullback] } :
      (((Functor.whiskeringRight OnePointCat X' (F ⊡ G)).obj
            ((toFunctorToCategoricalPullback F G X').obj Q)) ⋙
          toCatCommSqOver F G OnePointCat).obj
          ((Functor.const OnePointCat).obj x) ⟶
        pullbackPointSquare (((toFunctorToCategoricalPullback F G X').obj Q).obj x))

/-- Helper for Lemma 4.31.11: the left displayed component of the explicit transported
identity point-lift is pointwise the identity on `Q.fst.obj x`. -/
@[simp] theorem targetIdentityPointLift_fst_app
    {A' : Type _} [Category.{v} A']
    {B' : Type _} [Category.{v} B']
    {C' : Type _} [Category.{v} C']
    {X' : Type _} [Category.{v} X']
    {F : A' ⥤ C'} {G : B' ⥤ C'}
    (Q : CatCommSqOver F G X')
    (x : X')
    (p : OnePointCat) :
    (targetIdentityPointLift Q x).hom.fst.app p = 𝟙 (Q.fst.obj x) := by
  cases p
  rfl

/-- Helper for Lemma 4.31.11: the right displayed component of the explicit transported
identity point-lift is pointwise the identity on `Q.snd.obj x`. -/
@[simp] theorem targetIdentityPointLift_snd_app
    {A' : Type _} [Category.{v} A']
    {B' : Type _} [Category.{v} B']
    {C' : Type _} [Category.{v} C']
    {X' : Type _} [Category.{v} X']
    {F : A' ⥤ C'} {G : B' ⥤ C'}
    (Q : CatCommSqOver F G X')
    (x : X')
    (p : OnePointCat) :
    (targetIdentityPointLift Q x).hom.snd.app p = 𝟙 (Q.snd.obj x) := by
  cases p
  rfl

/-- Helper for Lemma 4.31.11: a morphism into `Y` in the ordinary comma category of a functor `K`
induces the corresponding explicit target-side one-point lift over `pullbackPointSquare Y`. -/
abbrev targetPointLiftOfHom
    {A' : Type _} [Category.{v} A']
    {B' : Type _} [Category.{v} B']
    {C' : Type _} [Category.{v} C']
    {X' : Type _} [Category.{v} X']
    {F : A' ⥤ C'} {G : B' ⥤ C'}
    (K : X' ⥤ F ⊡ G)
    {x : X'} {Y : F ⊡ G}
    (φ : K.obj x ⟶ Y) :
    CostructuredArrow
      (((Functor.whiskeringRight OnePointCat X' (F ⊡ G)).obj K) ⋙
        toCatCommSqOver F G OnePointCat)
      (pullbackPointSquare Y) :=
  CostructuredArrow.mk
    ({ fst :=
         { app := fun _ ↦ φ.fst
           naturality := by
             intro p q f
             simp }
       snd :=
         { app := fun _ ↦ φ.snd
           naturality := by
             intro p q f
             simp }
       w := by
         -- Evaluating at the unique point turns the pullback compatibility of `φ` into the
         -- matching target-side one-point compatibility.
         ext p
         cases p
         simpa [pullbackPointSquare] using φ.w } :
      (((Functor.whiskeringRight OnePointCat X' (F ⊡ G)).obj K) ⋙
            toCatCommSqOver F G OnePointCat).obj
          ((Functor.const OnePointCat).obj x) ⟶
        pullbackPointSquare Y)

/-- Helper for Lemma 4.31.11: evaluating a target-side one-point lift at the unique object
recovers the corresponding ordinary comma object into `Y`. -/
abbrev targetPointLiftEvaluationFunctor
    {A' : Type _} [Category.{v} A']
    {B' : Type _} [Category.{v} B']
    {C' : Type _} [Category.{v} C']
    {X' : Type _} [Category.{v} X']
    {F : A' ⥤ C'} {G : B' ⥤ C'}
    (K : X' ⥤ F ⊡ G)
    (Y : F ⊡ G) :
    CostructuredArrow
      (((Functor.whiskeringRight OnePointCat X' (F ⊡ G)).obj K) ⋙
        toCatCommSqOver F G OnePointCat)
      (pullbackPointSquare Y) ⥤
      CostructuredArrow K Y where
  obj a :=
    CostructuredArrow.mk
      { fst := a.hom.fst.app onePoint
        snd := a.hom.snd.app onePoint
        w := by
          -- The target-side comma relation evaluated at the unique point is exactly the ordinary
          -- pullback equation.
          simpa [pullbackPointSquare] using
            (CatCommSqOver.w_app
              (F := F) (G := G) (X := OnePointCat)
              (S := ((((Functor.whiskeringRight OnePointCat X' (F ⊡ G)).obj K) ⋙
                    toCatCommSqOver F G OnePointCat).obj a.left))
              (S' := pullbackPointSquare Y)
              a.hom
              onePoint) }
  map η := by
    -- A target-side one-point-lift morphism is determined by its unique component, which is
    -- exactly the ordinary comma morphism after evaluation.
    refine CostructuredArrow.homMk (η.left.app onePoint) ?_
    apply CategoricalPullback.hom_ext
    · have hfst := congrArg CatCommSqOver.Hom.fst (CostructuredArrow.w η)
      exact congrArg (fun τ ↦ τ.app onePoint) hfst
    · have hsnd := congrArg CatCommSqOver.Hom.snd (CostructuredArrow.w η)
      exact congrArg (fun τ ↦ τ.app onePoint) hsnd
  map_id := by
    -- Identity morphisms stay identities after evaluation at the unique point.
    intro a
    apply CostructuredArrow.hom_ext
    rfl
  map_comp := by
    -- Composition is computed by the same unique component.
    intro a b c η θ
    apply CostructuredArrow.hom_ext
    rfl

/-- Helper for Lemma 4.31.11: evaluating the explicit target-side one-point lift attached to `φ`
recovers `φ` itself. -/
@[simp] theorem targetPointLiftEvaluationFunctor_obj_targetPointLiftOfHom
    {A' : Type _} [Category.{v} A']
    {B' : Type _} [Category.{v} B']
    {C' : Type _} [Category.{v} C']
    {X' : Type _} [Category.{v} X']
    {F : A' ⥤ C'} {G : B' ⥤ C'}
    (K : X' ⥤ F ⊡ G)
    {x : X'} {Y : F ⊡ G}
    (φ : K.obj x ⟶ Y) :
    (targetPointLiftEvaluationFunctor K Y).obj (targetPointLiftOfHom K φ) =
      CostructuredArrow.mk φ := by
  rfl

/-- Helper for Lemma 4.31.11: the explicit transported identity point-lift is the target-side
one-point lift attached to the identity of the pullback object `K.obj x`. -/
@[simp] theorem targetIdentityPointLift_eq_targetPointLiftOfHom_id
    {A' : Type _} [Category.{v} A']
    {B' : Type _} [Category.{v} B']
    {C' : Type _} [Category.{v} C']
    {X' : Type _} [Category.{v} X']
    {F : A' ⥤ C'} {G : B' ⥤ C'}
    (Q : CatCommSqOver F G X')
    (x : X') :
    targetIdentityPointLift Q x =
      targetPointLiftOfHom
        ((toFunctorToCategoricalPullback F G X').obj Q)
        (𝟙 (((toFunctorToCategoricalPullback F G X').obj Q).obj x)) := by
  rfl

/-- Helper for Lemma 4.31.11: evaluating `targetIdentityPointLift Q x` gives the identity comma
object on the pullback object `((toFunctorToCategoricalPullback ...).obj Q).obj x`. -/
@[simp] theorem targetPointLiftEvaluationFunctor_obj_targetIdentityPointLift
    {A' : Type _} [Category.{v} A']
    {B' : Type _} [Category.{v} B']
    {C' : Type _} [Category.{v} C']
    {X' : Type _} [Category.{v} X']
    {F : A' ⥤ C'} {G : B' ⥤ C'}
    (Q : CatCommSqOver F G X')
    (x : X') :
    (targetPointLiftEvaluationFunctor
        ((toFunctorToCategoricalPullback F G X').obj Q)
        (((toFunctorToCategoricalPullback F G X').obj Q).obj x)).obj
        (targetIdentityPointLift Q x) =
      CostructuredArrow.mk
        (𝟙 (((toFunctorToCategoricalPullback F G X').obj Q).obj x)) := by
  rfl

/-- Helper for Lemma 4.31.11: evaluation at the unique point reflects equality of target-side
one-point-lift morphisms. -/
instance targetPointLiftEvaluationFunctor_faithful
    {A' : Type _} [Category.{v} A']
    {B' : Type _} [Category.{v} B']
    {C' : Type _} [Category.{v} C']
    {X' : Type _} [Category.{v} X']
    {F : A' ⥤ C'} {G : B' ⥤ C'}
    (K : X' ⥤ F ⊡ G)
    (Y : F ⊡ G) :
    (targetPointLiftEvaluationFunctor K Y).Faithful where
  map_injective := by
    intro a b η θ hηθ
    apply CostructuredArrow.hom_ext
    ext p
    cases p
    exact congrArg CommaMorphism.left hηθ

/-- Helper for Lemma 4.31.11: every ordinary comma morphism into `Y` lifts uniquely to a
target-side morphism of one-point lifts. -/
instance targetPointLiftEvaluationFunctor_full
    {A' : Type _} [Category.{v} A']
    {B' : Type _} [Category.{v} B']
    {C' : Type _} [Category.{v} C']
    {X' : Type _} [Category.{v} X']
    {F : A' ⥤ C'} {G : B' ⥤ C'}
    (K : X' ⥤ F ⊡ G)
    (Y : F ⊡ G) :
    (targetPointLiftEvaluationFunctor K Y).Full where
  map_surjective := by
    intro a b η
    refine ⟨(CostructuredArrow.homMk
      ({ app := fun _ ↦ η.left
         naturality := by
           intro p q f
           have hpq : p = q := by
             apply Discrete.ext
             apply Subsingleton.elim
           subst hpq
           have hf : f = 𝟙 p := Subsingleton.elim _ _
           simpa [hf] }) ?_), ?_⟩
    · apply CatCommSqOver.hom_ext
      · ext p
        cases p
        have hfst := congrArg CategoricalPullback.Hom.fst (CostructuredArrow.w η)
        simpa [targetPointLiftEvaluationFunctor, pullbackPointSquare] using hfst
      · ext p
        cases p
        have hsnd := congrArg CategoricalPullback.Hom.snd (CostructuredArrow.w η)
        simpa [targetPointLiftEvaluationFunctor, pullbackPointSquare] using hsnd
    · apply CostructuredArrow.hom_ext
      rfl

/-- Helper for Lemma 4.31.11: every ordinary comma object into `Y` lies in the essential image of
target-side one-point evaluation. -/
instance targetPointLiftEvaluationFunctor_essSurj
    {A' : Type _} [Category.{v} A']
    {B' : Type _} [Category.{v} B']
    {C' : Type _} [Category.{v} C']
    {X' : Type _} [Category.{v} X']
    {F : A' ⥤ C'} {G : B' ⥤ C'}
    (K : X' ⥤ F ⊡ G)
    (Y : F ⊡ G) :
    (targetPointLiftEvaluationFunctor K Y).EssSurj where
  mem_essImage := by
    intro a
    refine ⟨targetPointLiftOfHom K a.hom, ?_⟩
    refine ⟨?_⟩
    simpa using (CostructuredArrow.eta a).symm

/-- Helper for Lemma 4.31.11: evaluating a target-side one-point lift at the unique point is an
equivalence with the ordinary comma category into `Y`. -/
noncomputable abbrev targetPointLiftEvaluationFunctor_isEquivalence
    {A' : Type _} [Category.{v} A']
    {B' : Type _} [Category.{v} B']
    {C' : Type _} [Category.{v} C']
    {X' : Type _} [Category.{v} X']
    {F : A' ⥤ C'} {G : B' ⥤ C'}
    (K : X' ⥤ F ⊡ G)
    (Y : F ⊡ G) :
    (targetPointLiftEvaluationFunctor K Y).IsEquivalence := by
  -- The target-side one-point lifts encode exactly the same data as ordinary arrows into `Y`
  -- once we evaluate at the unique point.
  let _ : (targetPointLiftEvaluationFunctor K Y).Faithful :=
    targetPointLiftEvaluationFunctor_faithful K Y
  let _ : (targetPointLiftEvaluationFunctor K Y).Full :=
    targetPointLiftEvaluationFunctor_full K Y
  let _ : (targetPointLiftEvaluationFunctor K Y).EssSurj :=
    targetPointLiftEvaluationFunctor_essSurj K Y
  exact Functor.IsEquivalence.mk (F := targetPointLiftEvaluationFunctor K Y)

/-- Helper for Lemma 4.31.11: finality of `Q` chooses a one-point lift over any pullback object
`Y`. -/
abbrev comparisonPointLift
    {A' : Type _} [Category.{v} A']
    {B' : Type _} [Category.{v} B']
    {C' : Type _} [Category.{v} C']
    {X' : Type _} [Category.{v} X']
    {F : A' ⥤ C'} {G : B' ⥤ C'}
    (Q : CatCommSqOver F G X')
    (Y : F ⊡ G)
    [Bicategory.IsFinal Q.toBicategoricalSquare] :
    CostructuredArrow (whisker_source_square_functor Q) (pullbackPointSquare Y) :=
  square_hom_to_costructuredArrow
    (pullbackPointSquare Y)
    Q
    (⊤_ ((pullbackPointSquare Y).toBicategoricalSquare ⟶ Q.toBicategoricalSquare))

/-- Helper for Lemma 4.31.11: the chosen one-point lift is terminal in the comma category over
`pullbackPointSquare Y`. -/
noncomputable abbrev comparisonPointLift_isTerminal
    {A' : Type _} [Category.{v} A']
    {B' : Type _} [Category.{v} B']
    {C' : Type _} [Category.{v} C']
    {X' : Type _} [Category.{v} X']
    {F : A' ⥤ C'} {G : B' ⥤ C'}
    (Q : CatCommSqOver F G X')
    (Y : F ⊡ G)
    [Bicategory.IsFinal Q.toBicategoricalSquare] :
    Limits.IsTerminal (comparisonPointLift Q Y) := by
  let e := square_hom_equiv_costructuredArrow (pullbackPointSquare Y) Q
  letI : e.functor.IsEquivalence := e.isEquivalence_functor
  letI :
      PreservesLimit
        (Functor.empty ((pullbackPointSquare Y).toBicategoricalSquare ⟶ Q.toBicategoricalSquare))
        e.functor := by
    infer_instance
  let hterminal :
      Limits.IsTerminal
        (⊤_ ((pullbackPointSquare Y).toBicategoricalSquare ⟶ Q.toBicategoricalSquare)) :=
    Limits.terminalIsTerminal
  -- The square/comma equivalence sends the chosen terminal square map to the chosen point-lift.
  simpa [comparisonPointLift, e] using
    (Limits.IsTerminal.isTerminalObj e.functor
      (⊤_ ((pullbackPointSquare Y).toBicategoricalSquare ⟶ Q.toBicategoricalSquare))
      hterminal)

/-- Helper for Lemma 4.31.11: transporting the explicit point-lift `pullbackPointLift Q x`
across `comparisonCostructuredArrowTransport` produces the target-side identity point-lift. -/
theorem comparisonCostructuredArrowTransport_pullbackPointLift_obj
    {A' : Type _} [Category.{v} A']
    {B' : Type _} [Category.{v} B']
    {C' : Type _} [Category.{v} C']
    {X' : Type _} [Category.{v} X']
    {F : A' ⥤ C'} {G : B' ⥤ C'}
    (Q : CatCommSqOver F G X')
    (x : X')
    [Bicategory.IsFinal Q.toBicategoricalSquare] :
    (comparisonCostructuredArrowTransport Q
      (pullbackPointSquare (((toFunctorToCategoricalPullback F G X').obj Q).obj x))).functor.obj
        (pullbackPointLift Q x) =
      targetIdentityPointLift Q x := by
  -- The transport keeps the same constant source object, so it remains only to compare the
  -- displayed morphism into the one-point pullback square.
  refine CostructuredArrow.obj_ext _ _ rfl ?_
  -- Both displayed morphisms are componentwise identities after evaluating at the unique point.
  apply CatCommSqOver.hom_ext
  · ext p
    cases p
    simp [comparisonCostructuredArrowTransport, pullbackPointLift, targetIdentityPointLift,
      canonicalComparisonWhiskerSourceSquareFunctor, whiskerSourceSquareFunctorComparisonIso,
      whisker_source_square, toFunctorToCategoricalPullback, canonicalComparisonSquare,
      pullbackPointSquare]
  · ext p
    cases p
    simp [comparisonCostructuredArrowTransport, pullbackPointLift, targetIdentityPointLift,
      canonicalComparisonWhiskerSourceSquareFunctor, whiskerSourceSquareFunctorComparisonIso,
      whisker_source_square, toFunctorToCategoricalPullback, canonicalComparisonSquare,
      pullbackPointSquare]

/-- Helper for Lemma 4.31.11: recovering the square map from `pullbackPointLift Q x` keeps the
constant apex functor on `x`. -/
@[simp] theorem costructuredArrow_to_square_hom_pullbackPointLift_toFunctor
    {A' : Type _} [Category.{v} A']
    {B' : Type _} [Category.{v} B']
    {C' : Type _} [Category.{v} C']
    {X' : Type _} [Category.{v} X']
    {F : A' ⥤ C'} {G : B' ⥤ C'}
    (Q : CatCommSqOver F G X')
    (x : X')
    [Bicategory.IsFinal Q.toBicategoricalSquare] :
    (costructuredArrow_to_square_hom
        (pullbackPointSquare (((toFunctorToCategoricalPullback F G X').obj Q).obj x))
        Q
        (pullbackPointLift Q x)).hom.toFunctor =
      (Functor.const OnePointCat).obj x := by
  rfl

/-- Helper for Lemma 4.31.11: the left component of the square map recovered from
`pullbackPointLift Q x` is pointwise the identity at `x`. -/
@[simp] theorem costructuredArrow_to_square_hom_pullbackPointLift_left_app
    {A' : Type _} [Category.{v} A']
    {B' : Type _} [Category.{v} B']
    {C' : Type _} [Category.{v} C']
    {X' : Type _} [Category.{v} X']
    {F : A' ⥤ C'} {G : B' ⥤ C'}
    (Q : CatCommSqOver F G X')
    (x : X')
    [Bicategory.IsFinal Q.toBicategoricalSquare]
    (p : OnePointCat) :
    (costructuredArrow_to_square_hom
        (pullbackPointSquare (((toFunctorToCategoricalPullback F G X').obj Q).obj x))
        Q
        (pullbackPointLift Q x)).left.toNatTrans.app p = 𝟙 (Q.fst.obj x) := by
  cases p
  rfl

/-- Helper for Lemma 4.31.11: the right component of the square map recovered from
`pullbackPointLift Q x` is pointwise the identity at `x`. -/
@[simp] theorem costructuredArrow_to_square_hom_pullbackPointLift_right_app
    {A' : Type _} [Category.{v} A']
    {B' : Type _} [Category.{v} B']
    {C' : Type _} [Category.{v} C']
    {X' : Type _} [Category.{v} X']
    {F : A' ⥤ C'} {G : B' ⥤ C'}
    (Q : CatCommSqOver F G X')
    (x : X')
    [Bicategory.IsFinal Q.toBicategoricalSquare]
    (p : OnePointCat) :
    (costructuredArrow_to_square_hom
        (pullbackPointSquare (((toFunctorToCategoricalPullback F G X').obj Q).obj x))
        Q
        (pullbackPointLift Q x)).right.toNatTrans.app p = 𝟙 (Q.snd.obj x) := by
  -- Recovering the square map keeps the right displayed component of the point-lift unchanged.
  cases p
  rfl

/-- Helper for Lemma 4.31.11: recovering the square map from `comparisonPointLift Q Y` returns
the chosen terminal square morphism. -/
@[simp] theorem costructuredArrow_to_square_hom_comparisonPointLift
    {A' : Type _} [Category.{v} A']
    {B' : Type _} [Category.{v} B']
    {C' : Type _} [Category.{v} C']
    {X' : Type _} [Category.{v} X']
    {F : A' ⥤ C'} {G : B' ⥤ C'}
    (Q : CatCommSqOver F G X')
    (Y : F ⊡ G)
    [Bicategory.IsFinal Q.toBicategoricalSquare] :
    costructuredArrow_to_square_hom (pullbackPointSquare Y) Q (comparisonPointLift Q Y) =
      (⊤_ ((pullbackPointSquare Y).toBicategoricalSquare ⟶ Q.toBicategoricalSquare)) := by
  simpa [comparisonPointLift] using
    squareHomCostructuredArrowRoundtrip
      (pullbackPointSquare Y)
      Q
      (⊤_ ((pullbackPointSquare Y).toBicategoricalSquare ⟶ Q.toBicategoricalSquare))

/-- Helper for Lemma 4.31.11: the recovered comparison point-lift square map has the same left
component as the chosen terminal square morphism. -/
@[simp] theorem costructuredArrow_to_square_hom_comparisonPointLift_left_app
    {A' : Type _} [Category.{v} A']
    {B' : Type _} [Category.{v} B']
    {C' : Type _} [Category.{v} C']
    {X' : Type _} [Category.{v} X']
    {F : A' ⥤ C'} {G : B' ⥤ C'}
    (Q : CatCommSqOver F G X')
    (Y : F ⊡ G)
    [Bicategory.IsFinal Q.toBicategoricalSquare]
    (p : OnePointCat) :
    (costructuredArrow_to_square_hom (pullbackPointSquare Y) Q (comparisonPointLift Q Y)).left.toNatTrans.app
        p =
      (⊤_ ((pullbackPointSquare Y).toBicategoricalSquare ⟶ Q.toBicategoricalSquare)).left.toNatTrans.app p := by
  simpa [costructuredArrow_to_square_hom_comparisonPointLift]

/-- Helper for Lemma 4.31.11: the recovered comparison point-lift square map has the same right
component as the chosen terminal square morphism. -/
@[simp] theorem costructuredArrow_to_square_hom_comparisonPointLift_right_app
    {A' : Type _} [Category.{v} A']
    {B' : Type _} [Category.{v} B']
    {C' : Type _} [Category.{v} C']
    {X' : Type _} [Category.{v} X']
    {F : A' ⥤ C'} {G : B' ⥤ C'}
    (Q : CatCommSqOver F G X')
    (Y : F ⊡ G)
    [Bicategory.IsFinal Q.toBicategoricalSquare]
    (p : OnePointCat) :
    (costructuredArrow_to_square_hom (pullbackPointSquare Y) Q (comparisonPointLift Q Y)).right.toNatTrans.app
        p =
      (⊤_ ((pullbackPointSquare Y).toBicategoricalSquare ⟶ Q.toBicategoricalSquare)).right.toNatTrans.app p := by
  simpa [costructuredArrow_to_square_hom_comparisonPointLift]

/-- Helper for Lemma 4.31.11: a morphism in the ordinary pullback into `K.obj y` determines a
corresponding point-lift object over the one-point square of `K.obj y`. -/
abbrev pointLiftOfComparisonHom
    {A' : Type _} [Category.{v} A']
    {B' : Type _} [Category.{v} B']
    {C' : Type _} [Category.{v} C']
    {X' : Type _} [Category.{v} X']
    {F : A' ⥤ C'} {G : B' ⥤ C'}
    (Q : CatCommSqOver F G X')
    {x : X'} {Y : F ⊡ G}
    (φ : (((toFunctorToCategoricalPullback F G X').obj Q).obj x) ⟶ Y) :
    CostructuredArrow
      (whisker_source_square_functor Q)
      (pullbackPointSquare Y) :=
  CostructuredArrow.mk
    ({ fst :=
         { app := fun _ ↦ φ.fst
           naturality := by
             intro p q f
             simp }
       snd :=
         { app := fun _ ↦ φ.snd
           naturality := by
             intro p q f
             simp }
       w := by
         -- Evaluating at the unique point turns the pullback compatibility of `φ` into the
         -- corresponding point-lift compatibility.
         ext p
         cases p
         simpa [pullbackPointSquare, whisker_source_square, toFunctorToCategoricalPullback] using
           φ.w } :
      whisker_source_square Q ((Functor.const OnePointCat).obj x) ⟶
        pullbackPointSquare Y)

/-- Helper for Lemma 4.31.11: evaluating the compatibility of a one-point lift at the unique point
recovers the corresponding pullback equation in `C'`. -/
theorem pointLiftCompatibilityAtUniquePoint
    {A' : Type _} [Category.{v} A']
    {B' : Type _} [Category.{v} B']
    {C' : Type _} [Category.{v} C']
    {X' : Type _} [Category.{v} X']
    {F : A' ⥤ C'} {G : B' ⥤ C'}
    (Q : CatCommSqOver F G X')
    {Y : F ⊡ G}
    (a : CostructuredArrow (whisker_source_square_functor Q) (pullbackPointSquare Y)) :
    (Functor.whiskerRight a.hom.fst F ≫ (pullbackPointSquare Y).iso.hom).app onePoint =
      (((whisker_source_square_functor Q).obj a.left).iso.hom ≫
        Functor.whiskerRight a.hom.snd G).app onePoint := by
  -- This is just the comma-category compatibility evaluated at the unique point.
  exact congrArg (fun τ ↦ τ.app onePoint) a.hom.w

/-- Helper for Lemma 4.31.11: a one-point lift over `Y` evaluates at the unique point to the
corresponding ordinary costructured arrow into `Y`. -/
abbrev pointLiftEvaluationFunctor
    {A' : Type _} [Category.{v} A']
    {B' : Type _} [Category.{v} B']
    {C' : Type _} [Category.{v} C']
    {X' : Type _} [Category.{v} X']
    {F : A' ⥤ C'} {G : B' ⥤ C'}
    (Q : CatCommSqOver F G X')
    (Y : F ⊡ G) :
    CostructuredArrow (whisker_source_square_functor Q) (pullbackPointSquare Y) ⥤
      CostructuredArrow (((toFunctorToCategoricalPullback F G X').obj Q)) Y where
  obj a :=
    CostructuredArrow.mk
      { fst := a.hom.fst.app onePoint
        snd := a.hom.snd.app onePoint
        w := by
          -- The point-lift compatibility at the unique point is exactly the pullback equation.
          simpa [pullbackPointSquare, whisker_source_square, toFunctorToCategoricalPullback] using
            (CatCommSqOver.w_app
              (F := F) (G := G) (X := OnePointCat)
              (S := whisker_source_square Q a.left)
              (S' := pullbackPointSquare Y)
              a.hom
              onePoint) }
  map η := by
    -- A morphism of one-point lifts is determined by its unique component, which is exactly the
    -- ordinary pullback morphism between the evaluated arrows.
    refine CostructuredArrow.homMk (η.left.app onePoint) ?_
    apply CategoricalPullback.hom_ext
    · have hfst := congrArg CatCommSqOver.Hom.fst (CostructuredArrow.w η)
      exact congrArg (fun τ ↦ τ.app onePoint) hfst
    · have hsnd := congrArg CatCommSqOver.Hom.snd (CostructuredArrow.w η)
      exact congrArg (fun τ ↦ τ.app onePoint) hsnd
  map_id := by
    -- Identity morphisms stay identities after evaluation at the unique point.
    intro a
    apply CostructuredArrow.hom_ext
    rfl
  map_comp := by
    -- Composition is again computed by evaluating the unique point component.
    intro a b c η θ
    apply CostructuredArrow.hom_ext
    rfl

/-- Helper for Lemma 4.31.11: evaluating the generalized point-lift reconstructs the original
pullback arrow. -/
@[simp] theorem pointLiftEvaluationFunctor_obj_pointLiftOfComparisonHom
    {A' : Type _} [Category.{v} A']
    {B' : Type _} [Category.{v} B']
    {C' : Type _} [Category.{v} C']
    {X' : Type _} [Category.{v} X']
    {F : A' ⥤ C'} {G : B' ⥤ C'}
    (Q : CatCommSqOver F G X')
    {x : X'} {Y : F ⊡ G}
    (φ : (((toFunctorToCategoricalPullback F G X').obj Q).obj x) ⟶ Y) :
    (pointLiftEvaluationFunctor Q Y).obj (pointLiftOfComparisonHom Q φ) =
      CostructuredArrow.mk φ := by
  rfl

/-- Helper for Lemma 4.31.11: evaluating the explicit point-lift at `x` recovers the identity
arrow of the corresponding pullback object. -/
@[simp] theorem pointLiftEvaluationFunctor_obj_pullbackPointLift
    {A' : Type _} [Category.{v} A']
    {B' : Type _} [Category.{v} B']
    {C' : Type _} [Category.{v} C']
    {X' : Type _} [Category.{v} X']
    {F : A' ⥤ C'} {G : B' ⥤ C'}
    (Q : CatCommSqOver F G X')
    (x : X')
    [Bicategory.IsFinal Q.toBicategoricalSquare] :
    (pointLiftEvaluationFunctor Q
      (((toFunctorToCategoricalPullback F G X').obj Q).obj x)).obj (pullbackPointLift Q x) =
      CostructuredArrow.mk (𝟙 (((toFunctorToCategoricalPullback F G X').obj Q).obj x)) := by
  rfl

/-- Helper for Lemma 4.31.11: a functor out of the one-point discrete category is canonically
isomorphic to the constant functor at its unique value. -/
noncomputable def onePointFunctorIsoConst
    {X' : Type _} [Category.{v} X']
    (J : OnePointCat ⥤ X') :
    J ≅ (Functor.const OnePointCat).obj (J.obj onePoint) :=
  NatIso.ofComponents
    (fun p ↦ by
      cases p
      exact Iso.refl _)
    (by
      intro p q f
      have hpq : p = q := by
        apply Discrete.ext
        apply Subsingleton.elim
      cases hpq
      have hf : f = 𝟙 p := Subsingleton.elim _ _
      simpa [hf])

/-- Helper for Lemma 4.31.11: evaluating a one-point lift and rebuilding it from the resulting
pullback morphism recovers the original lift up to the canonical one-point-source isomorphism. -/
noncomputable def pointLiftEvaluationUnitIso
    {A' : Type _} [Category.{v} A']
    {B' : Type _} [Category.{v} B']
    {C' : Type _} [Category.{v} C']
    {X' : Type _} [Category.{v} X']
    {F : A' ⥤ C'} {G : B' ⥤ C'}
    (Q : CatCommSqOver F G X')
    {Y : F ⊡ G}
    (a : CostructuredArrow (whisker_source_square_functor Q) (pullbackPointSquare Y)) :
    a ≅ pointLiftOfComparisonHom Q ((pointLiftEvaluationFunctor Q Y).obj a).hom := by
  -- Both point-lifts have the same displayed components; only the source functor is rewritten to
  -- the constant functor at its unique object.
  refine CostructuredArrow.isoMk (onePointFunctorIsoConst a.left) ?_
  apply CatCommSqOver.hom_ext
  · ext p
    cases p
    simp [onePointFunctorIsoConst, pointLiftOfComparisonHom, pointLiftEvaluationFunctor,
      whisker_source_square_functor, whisker_source_square]
  · ext p
    cases p
    simp [onePointFunctorIsoConst, pointLiftOfComparisonHom, pointLiftEvaluationFunctor,
      whisker_source_square_functor, whisker_source_square]

/-- Helper for Lemma 4.31.11: ordinary comma morphisms into `Y` lift back to morphisms of
one-point lifts by using the same arrow at the unique point. -/
abbrev pointLiftEvaluationInverseFunctor
    {A' : Type _} [Category.{v} A']
    {B' : Type _} [Category.{v} B']
    {C' : Type _} [Category.{v} C']
    {X' : Type _} [Category.{v} X']
    {F : A' ⥤ C'} {G : B' ⥤ C'}
    (Q : CatCommSqOver F G X')
    (Y : F ⊡ G) :
    CostructuredArrow (((toFunctorToCategoricalPullback F G X').obj Q)) Y ⥤
      CostructuredArrow (whisker_source_square_functor Q) (pullbackPointSquare Y) where
  obj a := pointLiftOfComparisonHom Q a.hom
  map η := by
    -- A morphism in the ordinary comma category is already the unique component of a morphism of
    -- one-point lifts.
    refine CostructuredArrow.homMk
      ({ app := fun _ ↦ η.left
         naturality := by
           intro p q f
           cases p
           cases q
           simp }) ?_
    apply CatCommSqOver.hom_ext
    · ext p
      cases p
      have hfst := congrArg CategoricalPullback.Hom.fst (CostructuredArrow.w η)
      simpa [pointLiftOfComparisonHom, whisker_source_square_functor, whisker_source_square,
        toFunctorToCategoricalPullback] using hfst
    · ext p
      cases p
      have hsnd := congrArg CategoricalPullback.Hom.snd (CostructuredArrow.w η)
      simpa [pointLiftOfComparisonHom, whisker_source_square_functor, whisker_source_square,
        toFunctorToCategoricalPullback] using hsnd
  map_id := by
    -- Identity morphisms lift to identity natural transformations on the one-point source.
    intro a
    apply CostructuredArrow.hom_ext
    ext p
    cases p
    rfl
  map_comp := by
    -- Composition is again computed by the unique component.
    intro a b c η θ
    apply CostructuredArrow.hom_ext
    ext p
    cases p
    rfl

/-- Helper for Lemma 4.31.11: evaluation at the unique point reflects equality of one-point lift
morphisms. -/
instance pointLiftEvaluationFunctor_faithful
    {A' : Type _} [Category.{v} A']
    {B' : Type _} [Category.{v} B']
    {C' : Type _} [Category.{v} C']
    {X' : Type _} [Category.{v} X']
    {F : A' ⥤ C'} {G : B' ⥤ C'}
    (Q : CatCommSqOver F G X')
    (Y : F ⊡ G) :
    (pointLiftEvaluationFunctor Q Y).Faithful where
  map_injective := by
    intro a b η θ hηθ
    apply CostructuredArrow.hom_ext
    ext p
    cases p
    exact congrArg CommaMorphism.left hηθ

/-- Helper for Lemma 4.31.11: every morphism in the ordinary comma category over `Y` comes from a
unique morphism of one-point lifts. -/
instance pointLiftEvaluationFunctor_full
    {A' : Type _} [Category.{v} A']
    {B' : Type _} [Category.{v} B']
    {C' : Type _} [Category.{v} C']
    {X' : Type _} [Category.{v} X']
    {F : A' ⥤ C'} {G : B' ⥤ C'}
    (Q : CatCommSqOver F G X')
    (Y : F ⊡ G) :
    (pointLiftEvaluationFunctor Q Y).Full where
  map_surjective := by
    intro a b η
    refine ⟨(CostructuredArrow.homMk
      ({ app := fun _ ↦ η.left
         naturality := by
           intro p q f
           have hpq : p = q := by
             apply Discrete.ext
             apply Subsingleton.elim
           cases hpq
           have hf : f = 𝟙 p := Subsingleton.elim _ _
           simpa [hf] }) ?_), ?_⟩
    · apply CatCommSqOver.hom_ext
      · ext p
        cases p
        have hfst := congrArg CategoricalPullback.Hom.fst (CostructuredArrow.w η)
        simpa [pointLiftEvaluationFunctor, whisker_source_square_functor, whisker_source_square,
          pullbackPointSquare, toFunctorToCategoricalPullback] using hfst
      · ext p
        cases p
        have hsnd := congrArg CategoricalPullback.Hom.snd (CostructuredArrow.w η)
        simpa [pointLiftEvaluationFunctor, whisker_source_square_functor, whisker_source_square,
          pullbackPointSquare, toFunctorToCategoricalPullback] using hsnd
    · apply CostructuredArrow.hom_ext
      rfl

/-- Helper for Lemma 4.31.11: every ordinary comma object over `Y` is in the essential image of
evaluation at the unique point. -/
instance pointLiftEvaluationFunctor_essSurj
    {A' : Type _} [Category.{v} A']
    {B' : Type _} [Category.{v} B']
    {C' : Type _} [Category.{v} C']
    {X' : Type _} [Category.{v} X']
    {F : A' ⥤ C'} {G : B' ⥤ C'}
    (Q : CatCommSqOver F G X')
    (Y : F ⊡ G) :
    (pointLiftEvaluationFunctor Q Y).EssSurj where
  mem_essImage := by
    intro a
    refine ⟨pointLiftOfComparisonHom Q a.hom, ?_⟩
    refine ⟨?_⟩
    simpa using (CostructuredArrow.eta a).symm

/-- Helper for Lemma 4.31.11: evaluating at the unique point gives an equivalence between
one-point lifts over `Y` and ordinary comma objects into `Y`. -/
noncomputable abbrev pointLiftEvaluationFunctor_isEquivalence
    {A' : Type _} [Category.{v} A']
    {B' : Type _} [Category.{v} B']
    {C' : Type _} [Category.{v} C']
    {X' : Type _} [Category.{v} X']
    {F : A' ⥤ C'} {G : B' ⥤ C'}
    (Q : CatCommSqOver F G X')
    (Y : F ⊡ G) :
    (pointLiftEvaluationFunctor Q Y).IsEquivalence := by
  -- The explicit inverse-on-objects, together with full faithfulness and essential surjectivity,
  -- packages evaluation into an equivalence.
  let _ : (pointLiftEvaluationFunctor Q Y).Faithful := pointLiftEvaluationFunctor_faithful Q Y
  let _ : (pointLiftEvaluationFunctor Q Y).Full := pointLiftEvaluationFunctor_full Q Y
  let _ : (pointLiftEvaluationFunctor Q Y).EssSurj := pointLiftEvaluationFunctor_essSurj Q Y
  exact Functor.IsEquivalence.mk (F := pointLiftEvaluationFunctor Q Y)

/-- Helper for Lemma 4.31.11: a morphism in the ordinary pullback into `K.obj y` determines a
corresponding point-lift object over the one-point square of `K.obj y`. -/
abbrev pointLiftOfPullbackHom
    {A' : Type _} [Category.{v} A']
    {B' : Type _} [Category.{v} B']
    {C' : Type _} [Category.{v} C']
    {X' : Type _} [Category.{v} X']
    {F : A' ⥤ C'} {G : B' ⥤ C'}
    (Q : CatCommSqOver F G X')
    {x y : X'}
    (φ : (((toFunctorToCategoricalPullback F G X').obj Q).obj x) ⟶
      (((toFunctorToCategoricalPullback F G X').obj Q).obj y)) :
    CostructuredArrow
      (whisker_source_square_functor Q)
      (pullbackPointSquare (((toFunctorToCategoricalPullback F G X').obj Q).obj y)) :=
  pointLiftOfComparisonHom Q φ

/-- Helper for Lemma 4.31.11: the left displayed component of `pointLiftOfPullbackHom Q φ` is the
chosen left component of `φ`. -/
@[simp] theorem pointLiftOfPullbackHom_fst_app
    {A' : Type _} [Category.{v} A']
    {B' : Type _} [Category.{v} B']
    {C' : Type _} [Category.{v} C']
    {X' : Type _} [Category.{v} X']
    {F : A' ⥤ C'} {G : B' ⥤ C'}
    (Q : CatCommSqOver F G X')
    {x y : X'}
    (φ : (((toFunctorToCategoricalPullback F G X').obj Q).obj x) ⟶
      (((toFunctorToCategoricalPullback F G X').obj Q).obj y))
    (p : OnePointCat) :
    (pointLiftOfPullbackHom Q φ).hom.fst.app p = φ.fst := by
  rfl

/-- Helper for Lemma 4.31.11: the right displayed component of `pointLiftOfPullbackHom Q φ` is the
chosen right component of `φ`. -/
@[simp] theorem pointLiftOfPullbackHom_snd_app
    {A' : Type _} [Category.{v} A']
    {B' : Type _} [Category.{v} B']
    {C' : Type _} [Category.{v} C']
    {X' : Type _} [Category.{v} X']
    {F : A' ⥤ C'} {G : B' ⥤ C'}
    (Q : CatCommSqOver F G X')
    {x y : X'}
    (φ : (((toFunctorToCategoricalPullback F G X').obj Q).obj x) ⟶
      (((toFunctorToCategoricalPullback F G X').obj Q).obj y))
    (p : OnePointCat) :
    (pointLiftOfPullbackHom Q φ).hom.snd.app p = φ.snd := by
  rfl

/-- Helper for Lemma 4.31.11: evaluating the compatibility of a one-point lift at the unique point
recovers the corresponding square equation in `C'`. -/
theorem pointLiftCompatibilityAtUnit
    {A' : Type _} [Category.{v} A']
    {B' : Type _} [Category.{v} B']
    {C' : Type _} [Category.{v} C']
    {X' : Type _} [Category.{v} X']
    {F : A' ⥤ C'} {G : B' ⥤ C'}
    (Q : CatCommSqOver F G X')
    {Y : F ⊡ G}
    (a : CostructuredArrow (whisker_source_square_functor Q) (pullbackPointSquare Y)) :
    (Functor.whiskerRight a.hom.fst F ≫ (pullbackPointSquare Y).iso.hom).app onePoint =
      (((whisker_source_square_functor Q).obj a.left).iso.hom ≫
        Functor.whiskerRight a.hom.snd G).app onePoint := by
  -- This is just the comma-category compatibility evaluated at the unique point.
  exact congrArg (fun τ ↦ τ.app onePoint) a.hom.w

/-- Helper for Lemma 4.31.11: the explicit point-lift at `x` is the point-lift attached to the
identity morphism of the corresponding pullback object. -/
@[simp] theorem pullbackPointLift_eq_pointLiftOfPullbackHom_id
    {A' : Type _} [Category.{v} A']
    {B' : Type _} [Category.{v} B']
    {C' : Type _} [Category.{v} C']
    {X' : Type _} [Category.{v} X']
    {F : A' ⥤ C'} {G : B' ⥤ C'}
    (Q : CatCommSqOver F G X')
    (x : X')
    [Bicategory.IsFinal Q.toBicategoricalSquare] :
    pullbackPointLift Q x =
      pointLiftOfPullbackHom Q
        (𝟙 (((toFunctorToCategoricalPullback F G X').obj Q).obj x)) := by
  -- Both comma objects are built from the same constant functor and the identity pullback
  -- morphism, so the constructions coincide definitionally.
  rfl

/-- Helper for Lemma 4.31.11: the first component of the comparison functor on morphisms is just
the first leg map of the original square. -/
@[simp] theorem toFunctorToCategoricalPullback_map_fst
    {A' : Type _} [Category.{v} A']
    {B' : Type _} [Category.{v} B']
    {C' : Type _} [Category.{v} C']
    {X' : Type _} [Category.{v} X']
    {F : A' ⥤ C'} {G : B' ⥤ C'}
    (Q : CatCommSqOver F G X')
    {x y : X'}
    (f : x ⟶ y) :
    (((toFunctorToCategoricalPullback F G X').obj Q).map f).fst = Q.fst.map f := by
  rfl

/-- Helper for Lemma 4.31.11: the second component of the comparison functor on morphisms is just
the second leg map of the original square. -/
@[simp] theorem toFunctorToCategoricalPullback_map_snd
    {A' : Type _} [Category.{v} A']
    {B' : Type _} [Category.{v} B']
    {C' : Type _} [Category.{v} C']
    {X' : Type _} [Category.{v} X']
    {F : A' ⥤ C'} {G : B' ⥤ C'}
    (Q : CatCommSqOver F G X')
    {x y : X'}
    (f : x ⟶ y) :
    (((toFunctorToCategoricalPullback F G X').obj Q).map f).snd = Q.snd.map f := by
  rfl

/-- Helper for Lemma 4.31.11: the pullback-side round-trip square has apex functor equal to the
comparison inverse followed by the comparison functor. -/
@[simp] theorem comparisonCounitSquare_toFunctor
    {A' : Type _} [Category.{v} A']
    {B' : Type _} [Category.{v} B']
    {C' : Type _} [Category.{v} C']
    {X' : Type _} [Category.{v} X']
    {F : A' ⥤ C'} {G : B' ⥤ C'}
    (Q : CatCommSqOver F G X')
    [Bicategory.IsFinal Q.toBicategoricalSquare] :
    ((comparison_inverse_square_hom Q ≫ comparison_square_hom Q).hom.toFunctor) =
      comparisonInverseFunctor Q ⋙ ((toFunctorToCategoricalPullback F G X').obj Q) := by
  -- Both sides are the same composite functor by definition of square composition in `Cat`.
  rfl

/-- Helper for Lemma 4.31.11: the source-side round-trip square has apex functor equal to the
comparison functor followed by the comparison inverse. -/
@[simp] theorem comparisonUnitSquare_toFunctor
    {A' : Type _} [Category.{v} A']
    {B' : Type _} [Category.{v} B']
    {C' : Type _} [Category.{v} C']
    {X' : Type _} [Category.{v} X']
    {F : A' ⥤ C'} {G : B' ⥤ C'}
    (Q : CatCommSqOver F G X')
    [Bicategory.IsFinal Q.toBicategoricalSquare] :
    ((comparison_square_hom Q ≫ comparison_inverse_square_hom Q).hom.toFunctor) =
      ((toFunctorToCategoricalPullback F G X').obj Q) ⋙ comparisonInverseFunctor Q := by
  -- The other round-trip square normalizes in the same way.
  rfl

/-- Helper for Lemma 4.31.11: evaluating the square commutativity of
`comparison_inverse_square_hom Q` at a pullback object gives the compatibility needed for the
pullback-side counit isomorphism. -/
theorem comparisonInverseSquareHomCommApp
    {A' : Type _} [Category.{v} A']
    {B' : Type _} [Category.{v} B']
    {C' : Type _} [Category.{v} C']
    {X' : Type _} [Category.{v} X']
    {F : A' ⥤ C'} {G : B' ⥤ C'}
    (Q : CatCommSqOver F G X')
    (Y : F ⊡ G)
    [Bicategory.IsFinal Q.toBicategoricalSquare] :
    F.map ((comparison_inverse_square_hom Q).left.toNatTrans.app Y) ≫ Y.iso.hom =
      Q.iso.hom.app ((comparisonInverseFunctor Q).obj Y) ≫
        G.map ((comparison_inverse_square_hom Q).right.toNatTrans.app Y) := by
  -- Convert the bicategorical square equation to an ordinary natural-transformation equality.
  have h := congrArg Cat.Hom₂.toNatTrans (comparison_inverse_square_hom Q).comm
  have hY := congrArg (fun τ ↦ τ.app Y) h
  have hleft :
      (Functor.whiskerRight (comparison_inverse_square_hom Q).left.toNatTrans F ≫
          (categoricalPullbackSquare F G).ψ.hom.toNatTrans).app Y =
        F.map ((comparison_inverse_square_hom Q).left.toNatTrans.app Y) ≫ Y.iso.hom := by
    change
      F.map ((comparison_inverse_square_hom Q).left.toNatTrans.app Y) ≫
          (((toCatCommSqOver F G (F ⊡ G)).obj (𝟭 (F ⊡ G))).iso.hom.app Y) =
        F.map ((comparison_inverse_square_hom Q).left.toNatTrans.app Y) ≫ Y.iso.hom
    simp [toCatCommSqOver]
  have hright :
      (((comparisonInverseFunctor Q).associator Q.fst F).hom ≫
            (comparisonInverseFunctor Q).whiskerLeft Q.iso.hom ≫
              ((comparisonInverseFunctor Q).associator Q.snd G).inv ≫
                Functor.whiskerRight (comparison_inverse_square_hom Q).right.toNatTrans G).app Y =
        Q.iso.hom.app ((comparisonInverseFunctor Q).obj Y) ≫
          G.map ((comparison_inverse_square_hom Q).right.toNatTrans.app Y) := by
    -- The remaining terms are just the standard associator/whiskering evaluation formulas.
    repeat rw [NatTrans.comp_app]
    simp [comparisonInverseFunctor]
  exact hleft.symm.trans (hY.trans hright)

/-- Helper for Lemma 4.31.11: the inverse square map supplies the forward pullback morphism used
for the counit comparison at `Y`. -/
abbrev comparisonCounitHom
    {A' : Type _} [Category.{v} A']
    {B' : Type _} [Category.{v} B']
    {C' : Type _} [Category.{v} C']
    {X' : Type _} [Category.{v} X']
    {F : A' ⥤ C'} {G : B' ⥤ C'}
    (Q : CatCommSqOver F G X')
    (Y : F ⊡ G)
    [Bicategory.IsFinal Q.toBicategoricalSquare] :
    ((toFunctorToCategoricalPullback F G X').obj Q).obj ((comparisonInverseFunctor Q).obj Y) ⟶ Y :=
  { fst := (comparison_inverse_square_hom Q).left.toNatTrans.app Y
    snd := (comparison_inverse_square_hom Q).right.toNatTrans.app Y
    w := comparisonInverseSquareHomCommApp Q Y }

/-- Helper for Lemma 4.31.11: the left component of `comparisonCounitHom Q Y` is the left
component of `comparison_inverse_square_hom Q` evaluated at `Y`. -/
@[simp] theorem comparisonCounitHom_fst
    {A' : Type _} [Category.{v} A']
    {B' : Type _} [Category.{v} B']
    {C' : Type _} [Category.{v} C']
    {X' : Type _} [Category.{v} X']
    {F : A' ⥤ C'} {G : B' ⥤ C'}
    (Q : CatCommSqOver F G X')
    (Y : F ⊡ G)
    [Bicategory.IsFinal Q.toBicategoricalSquare] :
    (comparisonCounitHom Q Y).fst = (comparison_inverse_square_hom Q).left.toNatTrans.app Y := by
  rfl

/-- Helper for Lemma 4.31.11: the right component of `comparisonCounitHom Q Y` is the right
component of `comparison_inverse_square_hom Q` evaluated at `Y`. -/
@[simp] theorem comparisonCounitHom_snd
    {A' : Type _} [Category.{v} A']
    {B' : Type _} [Category.{v} B']
    {C' : Type _} [Category.{v} C']
    {X' : Type _} [Category.{v} X']
    {F : A' ⥤ C'} {G : B' ⥤ C'}
    (Q : CatCommSqOver F G X')
    (Y : F ⊡ G)
    [Bicategory.IsFinal Q.toBicategoricalSquare] :
    (comparisonCounitHom Q Y).snd = (comparison_inverse_square_hom Q).right.toNatTrans.app Y := by
  rfl

/-- Helper for Lemma 4.31.11: the pullback compatibility field of `comparisonCounitHom Q Y` is
exactly the square commutativity statement extracted from `comparison_inverse_square_hom Q`. -/
@[simp] theorem comparisonCounitHom_w
    {A' : Type _} [Category.{v} A']
    {B' : Type _} [Category.{v} B']
    {C' : Type _} [Category.{v} C']
    {X' : Type _} [Category.{v} X']
    {F : A' ⥤ C'} {G : B' ⥤ C'}
    (Q : CatCommSqOver F G X')
    (Y : F ⊡ G)
    [Bicategory.IsFinal Q.toBicategoricalSquare] :
    (comparisonCounitHom Q Y).w = comparisonInverseSquareHomCommApp Q Y := by
  rfl

/-- Helper for Lemma 4.31.11: in the transported comma category over `pullbackPointSquare Y`,
the explicit counit point-lift is the object whose source is constantly
`(comparisonInverseFunctor Q).obj Y` and whose displayed morphism is `comparisonCounitHom Q Y`. -/
abbrev targetCounitPointLift
    {A' : Type _} [Category.{v} A']
    {B' : Type _} [Category.{v} B']
    {C' : Type _} [Category.{v} C']
    {X' : Type _} [Category.{v} X']
    {F : A' ⥤ C'} {G : B' ⥤ C'}
    (Q : CatCommSqOver F G X')
    (Y : F ⊡ G)
    [Bicategory.IsFinal Q.toBicategoricalSquare] :
    CostructuredArrow
      (((Functor.whiskeringRight OnePointCat X' (F ⊡ G)).obj
          ((toFunctorToCategoricalPullback F G X').obj Q)) ⋙
        toCatCommSqOver F G OnePointCat)
      (pullbackPointSquare Y) :=
  CostructuredArrow.mk
    ({ fst :=
         { app := fun _ ↦ (comparisonCounitHom Q Y).fst
           naturality := by
             intro p q f
             cases p
             cases q
             simp }
       snd :=
         { app := fun _ ↦ (comparisonCounitHom Q Y).snd
           naturality := by
             intro p q f
             cases p
             cases q
             simp }
       w := by
         -- The counit pullback morphism already encodes the compatibility required by the
         -- target comma object.
         ext p
         cases p
         simpa [pullbackPointSquare] using (comparisonCounitHom Q Y).w } :
      (((Functor.whiskeringRight OnePointCat X' (F ⊡ G)).obj
            ((toFunctorToCategoricalPullback F G X').obj Q)) ⋙
          toCatCommSqOver F G OnePointCat).obj
          ((Functor.const OnePointCat).obj ((comparisonInverseFunctor Q).obj Y)) ⟶
        pullbackPointSquare Y)

/-- Helper for Lemma 4.31.11: the left displayed component of the explicit transported
counit point-lift is pointwise `(comparisonCounitHom Q Y).fst`. -/
@[simp] theorem targetCounitPointLift_fst_app
    {A' : Type _} [Category.{v} A']
    {B' : Type _} [Category.{v} B']
    {C' : Type _} [Category.{v} C']
    {X' : Type _} [Category.{v} X']
    {F : A' ⥤ C'} {G : B' ⥤ C'}
    (Q : CatCommSqOver F G X')
    (Y : F ⊡ G)
    [Bicategory.IsFinal Q.toBicategoricalSquare]
    (p : OnePointCat) :
    (targetCounitPointLift Q Y).hom.fst.app p = (comparisonCounitHom Q Y).fst := by
  cases p
  rfl

/-- Helper for Lemma 4.31.11: the right displayed component of the explicit transported
counit point-lift is pointwise `(comparisonCounitHom Q Y).snd`. -/
@[simp] theorem targetCounitPointLift_snd_app
    {A' : Type _} [Category.{v} A']
    {B' : Type _} [Category.{v} B']
    {C' : Type _} [Category.{v} C']
    {X' : Type _} [Category.{v} X']
    {F : A' ⥤ C'} {G : B' ⥤ C'}
    (Q : CatCommSqOver F G X')
    (Y : F ⊡ G)
    [Bicategory.IsFinal Q.toBicategoricalSquare]
    (p : OnePointCat) :
    (targetCounitPointLift Q Y).hom.snd.app p = (comparisonCounitHom Q Y).snd := by
  cases p
  rfl

/-- Helper for Lemma 4.31.11: the source functor of the explicit counit point-lift is the
constant functor at `((comparisonInverseFunctor Q).obj Y)`. -/
@[simp] theorem targetCounitPointLift_left
    {A' : Type _} [Category.{v} A']
    {B' : Type _} [Category.{v} B']
    {C' : Type _} [Category.{v} C']
    {X' : Type _} [Category.{v} X']
    {F : A' ⥤ C'} {G : B' ⥤ C'}
    (Q : CatCommSqOver F G X')
    (Y : F ⊡ G)
    [Bicategory.IsFinal Q.toBicategoricalSquare] :
    (targetCounitPointLift Q Y).left =
      (Functor.const OnePointCat).obj ((comparisonInverseFunctor Q).obj Y) := by
  rfl

/-- Helper for Lemma 4.31.11: evaluating the source functor of `comparisonPointLift Q Y` at the
unique point of `Discrete PUnit` agrees definitionally with the apex object of the recovered
square map. -/
theorem comparisonPointLift_left_obj_eq_recoveredApex
    {A' : Type _} [Category.{v} A']
    {B' : Type _} [Category.{v} B']
    {C' : Type _} [Category.{v} C']
    {X' : Type _} [Category.{v} X']
    {F : A' ⥤ C'} {G : B' ⥤ C'}
    (Q : CatCommSqOver F G X')
    (Y : F ⊡ G)
    [Bicategory.IsFinal Q.toBicategoricalSquare] :
    (comparisonPointLift Q Y).left.obj onePoint =
      (costructuredArrow_to_square_hom (pullbackPointSquare Y) Q (comparisonPointLift Q Y)).hom.toFunctor.obj
        onePoint := by
  -- This is the defining relationship between a costructured arrow and the recovered square map.
  rfl

/-- Helper for Lemma 4.31.11: evaluating the round-trip square functor at `Y` identifies the
canonical composite apex object with the comparison image of `((comparisonInverseFunctor Q).obj Y)`.
-/
@[simp] theorem comparisonCounitSquare_obj
    {A' : Type _} [Category.{v} A']
    {B' : Type _} [Category.{v} B']
    {C' : Type _} [Category.{v} C']
    {X' : Type _} [Category.{v} X']
    {F : A' ⥤ C'} {G : B' ⥤ C'}
    (Q : CatCommSqOver F G X')
    (Y : F ⊡ G)
    [Bicategory.IsFinal Q.toBicategoricalSquare] :
    (comparison_inverse_square_hom Q ≫ comparison_square_hom Q).hom.toFunctor.obj Y =
      ((toFunctorToCategoricalPullback F G X').obj Q).obj ((comparisonInverseFunctor Q).obj Y) := by
  -- Evaluate the already-normalized functor equality at `Y`.
  simpa [Functor.comp_obj] using
    congrArg (fun H ↦ H.obj Y) (comparisonCounitSquare_toFunctor (Q := Q))

/-- Helper for Lemma 4.31.11: the object part of `comparisonInverseFunctor Q` is definitionally the
apex object chosen by `comparison_inverse_square_hom Q`. -/
@[simp] theorem comparisonInverseFunctor_obj
    {A' : Type _} [Category.{v} A']
    {B' : Type _} [Category.{v} B']
    {C' : Type _} [Category.{v} C']
    {X' : Type _} [Category.{v} X']
    {F : A' ⥤ C'} {G : B' ⥤ C'}
    (Q : CatCommSqOver F G X')
    (Y : F ⊡ G)
    [Bicategory.IsFinal Q.toBicategoricalSquare] :
    (comparisonInverseFunctor Q).obj Y = (comparison_inverse_square_hom Q).hom.toFunctor.obj Y := by
  -- The inverse functor is defined as the apex functor of `comparison_inverse_square_hom Q`.
  rfl

/-- Helper for Lemma 4.31.11: evaluating the chosen comparison point-lift at the unique point
records on the left leg the left component of the chosen terminal square morphism from
`pullbackPointSquare Y` to `Q`. -/
@[simp] theorem pointLiftEvaluation_comparisonPointLift_fst
    {A' : Type _} [Category.{v} A']
    {B' : Type _} [Category.{v} B']
    {C' : Type _} [Category.{v} C']
    {X' : Type _} [Category.{v} X']
    {F : A' ⥤ C'} {G : B' ⥤ C'}
    (Q : CatCommSqOver F G X')
    (Y : F ⊡ G)
    [Bicategory.IsFinal Q.toBicategoricalSquare] :
    ((pointLiftEvaluationFunctor Q Y).obj (comparisonPointLift Q Y)).hom.fst =
      (⊤_ ((pullbackPointSquare Y).toBicategoricalSquare ⟶ Q.toBicategoricalSquare)).left.toNatTrans.app
        onePoint := by
  -- The evaluated comparison point-lift reads off the left component of the chosen terminal
  -- square morphism at the unique point.
  rfl

/-- Helper for Lemma 4.31.11: evaluating the chosen comparison point-lift at the unique point
records on the right leg the right component of the chosen terminal square morphism from
`pullbackPointSquare Y` to `Q`. -/
@[simp] theorem pointLiftEvaluation_comparisonPointLift_snd
    {A' : Type _} [Category.{v} A']
    {B' : Type _} [Category.{v} B']
    {C' : Type _} [Category.{v} C']
    {X' : Type _} [Category.{v} X']
    {F : A' ⥤ C'} {G : B' ⥤ C'}
    (Q : CatCommSqOver F G X')
    (Y : F ⊡ G)
    [Bicategory.IsFinal Q.toBicategoricalSquare] :
    ((pointLiftEvaluationFunctor Q Y).obj (comparisonPointLift Q Y)).hom.snd =
      (⊤_ ((pullbackPointSquare Y).toBicategoricalSquare ⟶ Q.toBicategoricalSquare)).right.toNatTrans.app
        onePoint := by
  -- The right component is read off in exactly the same way from the chosen terminal square map.
  rfl

/-- Helper for Lemma 4.31.11: evaluating a square isomorphism over the canonical pullback square at
`Y` produces the corresponding object isomorphism in the pullback category. -/
noncomputable def pullbackSquareIso_objIso
    {A' : Type _} [Category.{v} A']
    {B' : Type _} [Category.{v} B']
    {C' : Type _} [Category.{v} C']
    {F : A' ⥤ C'} {G : B' ⥤ C'}
    {u v : categoricalPullbackSquare F G ⟶ categoricalPullbackSquare F G}
    (e : u ≅ v)
    (Y : F ⊡ G) :
    u.hom.toFunctor.obj Y ≅ v.hom.toFunctor.obj Y :=
  { hom := e.hom.hom.toNatTrans.app Y
    inv := e.inv.hom.toNatTrans.app Y
    hom_inv_id := by
      -- Evaluate the square-level inverse relation on the apex natural transformations.
      have h := congrArg BicategoricalTwoCommutativeSquare.TwoHom.hom e.hom_inv_id
      have h' := congrArg Cat.Hom₂.toNatTrans h
      exact congrArg (fun τ ↦ τ.app Y) h'
    inv_hom_id := by
      -- The same evaluation turns the other inverse relation into the objectwise identity.
      have h := congrArg BicategoricalTwoCommutativeSquare.TwoHom.hom e.inv_hom_id
      have h' := congrArg Cat.Hom₂.toNatTrans h
      exact congrArg (fun τ ↦ τ.app Y) h' }

/-- Helper for Lemma 4.31.11: the comparison square map into the canonical pullback square is the
terminal object in its hom-category. -/
noncomputable abbrev comparisonSquareHom_isTerminal
    {A' : Type _} [Category.{v} A']
    {B' : Type _} [Category.{v} B']
    {C' : Type _} [Category.{v} C']
    {X' : Type _} [Category.{v} X']
    {F : A' ⥤ C'} {G : B' ⥤ C'}
    (Q : CatCommSqOver F G X')
    [Bicategory.IsFinal Q.toBicategoricalSquare] :
    IsTerminal (comparison_square_hom Q) := by
  -- The comparison square is exactly the chosen terminal lift into the categorical pullback
  -- square.
  let _ : ∀ Z : Q.toBicategoricalSquare ⟶ categoricalPullbackSquare F G,
      Unique (Z ⟶ comparison_square_hom Q) := fun Z ↦ by
        simpa [comparison_square_hom] using
          (hom_to_terminal_unique (F := F) (G := G) (S := Q.toBicategoricalSquare) Z)
  exact IsTerminal.ofUnique (comparison_square_hom Q)

/-- Helper for Lemma 4.31.11: a functor that is full, faithful, and essentially surjective is an
equivalence. -/
noncomputable abbrev functorIsEquivalenceOfFullyFaithfulEssSurj
    {A' : Type _} [Category.{v} A']
    {B' : Type _} [Category.{v} B']
    (K : A' ⥤ B')
    [K.Full] [K.Faithful] [K.EssSurj] :
    K.IsEquivalence := by
  -- Once the three standard comparison properties are installed as instances, mathlib packages
  -- them into an equivalence directly.
  exact Functor.IsEquivalence.mk (F := K)

/-- Helper for Lemma 4.31.11: if each explicit point-lift over `Q` is terminal, then the
comparison functor to the categorical pullback is fully faithful. -/
theorem toFunctorToCategoricalPullback_fullyFaithful_of_pointLiftTerminal
    {A' : Type _} [Category.{v} A']
    {B' : Type _} [Category.{v} B']
    {C' : Type _} [Category.{v} C']
    {X' : Type _} [Category.{v} X']
    {F : A' ⥤ C'} {G : B' ⥤ C'}
    (Q : CatCommSqOver F G X')
    [Bicategory.IsFinal Q.toBicategoricalSquare]
    (hterminal : ∀ y : X', Limits.IsTerminal (pullbackPointLift Q y)) :
    Nonempty (((toFunctorToCategoricalPullback F G X').obj Q).FullyFaithful) := by
  let K : X' ⥤ F ⊡ G := (toFunctorToCategoricalPullback F G X').obj Q
  rw [Functor.FullyFaithful.nonempty_iff_map_bijective]
  intro x y
  let preimage : (K.obj x ⟶ K.obj y) → (x ⟶ y) := fun φ ↦
    ((hterminal y).from (pointLiftOfPullbackHom Q φ)).left.app onePoint
  have hmap_preimage : ∀ φ : K.obj x ⟶ K.obj y, K.map (preimage φ) = φ := by
    intro φ
    -- The terminal comparison morphism has the prescribed first and second pullback components,
    -- so it reconstructs `φ`.
    apply CategoricalPullback.hom_ext
    · have hw := congrArg CatCommSqOver.Hom.fst
        (CostructuredArrow.w ((hterminal y).from (pointLiftOfPullbackHom Q φ)))
      have hw' := congrArg (fun τ ↦ τ.app onePoint) hw
      simpa [whisker_source_square_functor, whisker_source_square, K, preimage, pullbackPointLift,
        pointLiftOfPullbackHom, toFunctorToCategoricalPullback] using hw'
    · have hw := congrArg CatCommSqOver.Hom.snd
        (CostructuredArrow.w ((hterminal y).from (pointLiftOfPullbackHom Q φ)))
      have hw' := congrArg (fun τ ↦ τ.app onePoint) hw
      simpa [whisker_source_square_functor, whisker_source_square, K, preimage, pullbackPointLift,
        pointLiftOfPullbackHom, toFunctorToCategoricalPullback] using hw'
  have hpreimage_map : ∀ f : x ⟶ y, preimage (K.map f) = f := by
    intro f
    let η : pointLiftOfPullbackHom Q (K.map f) ⟶ pullbackPointLift Q y :=
      CostructuredArrow.homMk
        (({ app := fun _ ↦ f
            naturality := by
              intro p q g
              cases p
              cases q
              simp } :
          (Functor.const OnePointCat).obj x ⟶ (Functor.const OnePointCat).obj y))
        (by
          -- The obvious constant natural transformation from `x` to `y` is compatible with the
          -- point-lift equations because `K.map f` has the expected pullback components.
          apply CatCommSqOver.hom_ext <;> ext p <;> cases p <;>
            simp [pointLiftOfPullbackHom, pullbackPointLift, K, toFunctorToCategoricalPullback])
    have hη :
        (hterminal y).from (pointLiftOfPullbackHom Q (K.map f)) = η := by
      -- Terminality identifies the chosen lift morphism with the obvious one.
      apply (hterminal y).hom_ext
    simpa [preimage, η] using congrArg (fun τ ↦ τ.left.app onePoint) hη
  refine ⟨?_, ?_⟩
  · intro f g hfg
    -- Apply the terminal-point-lift preimage to both equal images.
    calc
      f = preimage (K.map f) := (hpreimage_map f).symm
      _ = preimage (K.map g) := by rw [hfg]
      _ = g := hpreimage_map g
  · intro φ
    exact ⟨preimage φ, hmap_preimage φ⟩

/-- The source-facing comparison functor of Lemma 4.31.11 from a square over `G₁ × G₂` and `Δ_S`
to the ordinary pullback model `A ×[S] B`. -/
abbrev two_fibre_product_comparison : X ⥤ G₁ ⊡ G₂ :=
  (toFunctorToCategoricalPullback (G₁.prod G₂) (Functor.diag S) X).obj P ⋙
    symmetricTwoFibreProductComparison G₁ G₂

/-- Helper for Lemma 4.31.11 (groupoid setting): when the apex `X'` is a groupoid, finality of `Q`
makes each explicit identity point-lift over `Q` terminal.

This is the `(2,1)`-categorical core of Tag 02XE.  The abstract point-lift `comparisonPointLift`
(built from the chosen terminal square map) is already terminal in the same comma category, and the
unique comparison map to it has underlying source a natural transformation valued in `X'`; since
`X'` is a groupoid that natural transformation is an isomorphism, so `CostructuredArrow.proj`
reflects an isomorphism of comma objects and the explicit point-lift is terminal as well. -/
noncomputable def pullbackPointLift_isTerminal_of_isFinal
    {A' : Type _} [Category.{v} A']
    {B' : Type _} [Category.{v} B']
    {C' : Type _} [Category.{v} C']
    {X' : Type v} [Category.{v} X'] [IsGroupoid X']
    {F : A' ⥤ C'} {G : B' ⥤ C'}
    (Q : CatCommSqOver F G X')
    [Bicategory.IsFinal Q.toBicategoricalSquare]
    (y : X') :
    Limits.IsTerminal (pullbackPointLift Q y) := by
  let K : X' ⥤ F ⊡ G := (toFunctorToCategoricalPullback F G X').obj Q
  -- The abstract point-lift over `K.obj y` is terminal in the same comma category.
  let hcomp : Limits.IsTerminal (comparisonPointLift Q (K.obj y)) :=
    comparisonPointLift_isTerminal Q (K.obj y)
  -- The unique comma map to it; its `.left` is a natural transformation valued in the groupoid `X'`.
  let θ : pullbackPointLift Q y ⟶ comparisonPointLift Q (K.obj y) := hcomp.from _
  haveI : IsIso ((CostructuredArrow.proj (whisker_source_square_functor Q)
      (pullbackPointSquare (K.obj y))).map θ) :=
    NatIso.isIso_of_isIso_app _
  haveI : IsIso θ :=
    isIso_of_reflects_iso θ
      (CostructuredArrow.proj (whisker_source_square_functor Q) (pullbackPointSquare (K.obj y)))
  exact Limits.IsTerminal.ofIso hcomp (asIso θ).symm

/-- Helper for Lemma 4.31.11 (groupoid setting): when the cospan apexes `A'`, `B'` are groupoids,
finality of `Q` makes the canonical comparison functor essentially surjective.  For each pullback
object `Y` the chosen one-point lift provides a source object `x_Y` together with a square map whose
two legs are morphisms in the groupoids `A'`, `B'`, hence isomorphisms; they assemble (via
`CategoricalPullback.mkIso`) to `K.obj x_Y ≅ Y`. -/
theorem toFunctorToCategoricalPullback_essSurj_of_isFinal
    {A' : Type _} [Category.{v} A'] [IsGroupoid A']
    {B' : Type _} [Category.{v} B'] [IsGroupoid B']
    {C' : Type _} [Category.{v} C']
    {X' : Type v} [Category.{v} X']
    {F : A' ⥤ C'} {G : B' ⥤ C'}
    (Q : CatCommSqOver F G X')
    [Bicategory.IsFinal Q.toBicategoricalSquare] :
    ((toFunctorToCategoricalPullback F G X').obj Q).EssSurj := by
  refine ⟨fun Y ↦ ⟨(comparisonInverseFunctor Q).obj Y, ⟨?_⟩⟩⟩
  -- Repackage the chosen terminal square map `categoricalPullbackSquare → Q` as a comma object; its
  -- two displayed legs are `2`-cells valued in the groupoids `A'`, `B'` (hence isomorphisms) and its
  -- `.w` field is the clean compatibility with the pullback witnesses.  They assemble (via
  -- `CategoricalPullback.mkIso`) to the counit isomorphism `K.obj (L.obj Y) ≅ Y`.
  let b := square_hom_to_costructuredArrow canonicalComparisonSquare Q
    (comparison_inverse_square_hom Q)
  refine CategoricalPullback.mkIso (asIso (b.hom.fst.app Y)) (asIso (b.hom.snd.app Y)) ?_
  have hw := congrArg (fun τ ↦ τ.app Y) b.hom.w
  simpa [b, square_hom_to_costructuredArrow, whisker_source_square, canonicalComparisonSquare,
    toCatCommSqOver, toFunctorToCategoricalPullback] using hw

/-- Helper for Lemma 4.31.11: finality of `Q` makes the canonical comparison functor to the
categorical pullback an equivalence.  In the `(2,1)`-categorical setting (apexes `A'`, `B'`, `X'`
groupoids, matching Tag 02XE) this is genuinely true and `sorry`-free. -/
noncomputable abbrev toFunctorToCategoricalPullback_isEquivalence_of_isFinal
    {A' : Type _} [Category.{v} A'] [IsGroupoid A']
    {B' : Type _} [Category.{v} B'] [IsGroupoid B']
    {C' : Type _} [Category.{v} C']
    {X' : Type v} [Category.{v} X'] [IsGroupoid X']
    {F : A' ⥤ C'} {G : B' ⥤ C'}
    (Q : CatCommSqOver F G X')
    [Bicategory.IsFinal Q.toBicategoricalSquare] :
    ((toFunctorToCategoricalPullback F G X').obj Q).IsEquivalence := by
  -- HISTORICAL NOTE.  For a general (non-groupoidal) apex this statement is FALSE: weak finality
  -- (`IsFinal` = each hom-category merely *has* a terminal object) is strictly weaker than
  -- bi-terminality in the `Cat`-based square bicategory.  Counterexample: `A'=B'=C'=𝟙`, `F=G=𝟭`
  -- (so `F ⊡ G ≅ 𝟙`), apex `X' = [0→1]`; then `IsFinal Q` holds but `K : [0→1] ⥤ 𝟙` is not full.
  -- Tag 02XE lives in the `(2,1)` setting, captured here by `[IsGroupoid A'/B'/X']`; there it is
  -- genuinely true, as proved below.
  let _ : ((toFunctorToCategoricalPullback F G X').obj Q).EssSurj :=
    toFunctorToCategoricalPullback_essSurj_of_isFinal (Q := Q)
  -- Each explicit point-lift is terminal (uses `[IsGroupoid X']`), so the comparison is fully
  -- faithful.
  have hterm : ∀ y : X', Limits.IsTerminal (pullbackPointLift Q y) :=
    fun y ↦ pullbackPointLift_isTerminal_of_isFinal (Q := Q) y
  have hff : Nonempty ((toFunctorToCategoricalPullback F G X').obj Q).FullyFaithful :=
    toFunctorToCategoricalPullback_fullyFaithful_of_pointLiftTerminal (Q := Q) hterm
  let _ : ((toFunctorToCategoricalPullback F G X').obj Q).Full := hff.some.full
  let _ : ((toFunctorToCategoricalPullback F G X').obj Q).Faithful := hff.some.faithful
  exact functorIsEquivalenceOfFullyFaithfulEssSurj ((toFunctorToCategoricalPullback F G X').obj Q)

/-- The canonical comparison functor attached to a `2`-fibre product square over `G₁ × G₂` and
`Δ_S`, expressed through the chapter's owner predicate `Bicategory.IsFinal`, is an equivalence.
It is the composite of the owner-level comparison functor from `P` to the diagonal pullback model
with the canonical model comparison `symmetricTwoFibreProductComparison G₁ G₂`. -/
noncomputable instance
    [Bicategory.IsFinal P.toBicategoricalSquare] :
    (two_fibre_product_comparison G₁ G₂ P).IsEquivalence := by
  let _ :
      ((toFunctorToCategoricalPullback (G₁.prod G₂) (Functor.diag S) X).obj P).IsEquivalence :=
    by
      simpa using (toFunctorToCategoricalPullback_isEquivalence_of_isFinal (Q := P))
  let e₁ :
      X ≌ (G₁.prod G₂) ⊡ (Functor.diag S) :=
    ((toFunctorToCategoricalPullback (G₁.prod G₂) (Functor.diag S) X).obj P).asEquivalence
  let e₂ :
      (G₁.prod G₂) ⊡ (Functor.diag S) ≌ G₁ ⊡ G₂ :=
    (symmetricTwoFibreProductComparison G₁ G₂).asEquivalence
  -- The comparison to the ordinary pullback is the composite of the two already constructed
  -- equivalences.
  simpa [two_fibre_product_comparison] using (e₁.trans e₂).isEquivalence_functor

/-- Lemma 4.31.11: if `P` is a `2`-fibre product square over `G₁ × G₂` and `Δ_S`, then `X` is
canonically equivalent to the ordinary pullback category `A ×[S] B`. This formalizes the
canonical isomorphism of the source statement in the bicategorical `Cat` setting. -/
noncomputable def two_fibre_product_square_equivalence
    [Bicategory.IsFinal P.toBicategoricalSquare] :
    X ≌ G₁ ⊡ G₂ :=
  letI : ((toFunctorToCategoricalPullback (G₁.prod G₂) (Functor.diag S) X).obj P).IsEquivalence :=
    toFunctorToCategoricalPullback_isEquivalence_of_isFinal (Q := P)
  let e₁ :
      X ≌ (G₁.prod G₂) ⊡ (Functor.diag S) :=
    ((toFunctorToCategoricalPullback (G₁.prod G₂) (Functor.diag S) X).obj P).asEquivalence
  let e₂ :
      (G₁.prod G₂) ⊡ (Functor.diag S) ≌ G₁ ⊡ G₂ :=
    (symmetricTwoFibreProductComparison G₁ G₂).asEquivalence
  e₁.trans e₂

/-- The functor underlying `two_fibre_product_square_equivalence` is the canonical comparison
functor `two_fibre_product_comparison`. -/
-- Proof sketch: unfold `two_fibre_product_square_equivalence`; it is defined by applying
-- `Functor.asEquivalence` to `two_fibre_product_comparison`.
theorem two_fibre_product_square_equivalence_functor
    [Bicategory.IsFinal P.toBicategoricalSquare] :
    (two_fibre_product_square_equivalence G₁ G₂ P).functor =
      two_fibre_product_comparison G₁ G₂ P := by
  -- Unfolding `Functor.asEquivalence` shows that the forward functor is definitionally the
  -- comparison functor.
  rfl

end

end CategoryTheory.Limits
