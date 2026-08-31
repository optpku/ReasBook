module

public import stacks_project.Chap04.Lemma_4_31_13.Basic
import Mathlib.CategoryTheory.Limits.Shapes.Equivalence
@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open CategoricalPullback
open CategoricalPullback.CatCommSqOver
open scoped CategoricalPullback

namespace CategoryTheory.Limits

universe v₁ v₂ v u₁ u₂ u

variable {C₀ : Type u₁} [Category.{v₁} C₀]
variable {D₀ : Type u₂} [Category.{v₂} D₀]

variable {A : Type (max u v)} [Category.{v} A]
variable {B : Type (max u v)} [Category.{v} B]
variable {C : Type (max u v)} [Category.{v} C]
variable {D : Type (max u v)} [Category.{v} D]

/-- Helper for Lemma 4.31.13: the canonical comparison from `A ×[C] B` to the ordinary pullback
of `A ×[D] B ⥤ C ×[D] C ← C` is an equivalence. -/
private theorem two_fibre_product_diagonal_comparison_isEquivalence
    (F : A ⥤ C) (G : B ⥤ C) (H : C ⥤ D) :
    ((toFunctorToCategoricalPullback
        (two_fibre_product_right_vertical F G H) (Δₚ H) (F ⊡ G)).obj
      (two_fibre_product_diagonal_square_over F G H)).IsEquivalence := by
  -- Route correction: package the explicit inverse directly, rather than rebuilding a fully
  -- faithful/essentially surjective argument through repeated transport.
  let G' := twoFibreProductDiagonalInverse F G H
  let η := twoFibreProductDiagonalUnitIso F G H
  let ε := twoFibreProductDiagonalCounitIso F G H
  exact Functor.IsEquivalence.mk' G' η ε

/-- Helper for Lemma 4.31.13: evaluating the commutativity of a square morphism in `Cat` gives
the expected objectwise compatibility between the two legs and the square isomorphisms. -/
private theorem square_hom_comm_app
    {A₀ : Type (max u v)} [Category.{v} A₀]
    {B₀ : Type (max u v)} [Category.{v} B₀]
    {C₀ : Type (max u v)} [Category.{v} C₀]
    {S₀ : Type (max u v)} [Category.{v} S₀]
    {T₀ : Type (max u v)} [Category.{v} T₀]
    {L : A₀ ⥤ C₀} {R : B₀ ⥤ C₀}
    (S : CatCommSqOver L R S₀)
    (Q : CatCommSqOver L R T₀)
    (u : S.toBicategoricalSquare ⟶ Q.toBicategoricalSquare)
    (x : S₀) :
    L.map (u.left.toNatTrans.app x) ≫ S.iso.hom.app x =
      Q.iso.hom.app (u.hom.toFunctor.obj x) ≫ R.map (u.right.toNatTrans.app x) := by
  -- Convert the bicategorical square equation to an equality of ordinary natural transformations
  -- in `Cat`, then evaluate at `x`.
  have h := congrArg Cat.Hom₂.toNatTrans u.comm
  have hx := congrArg (fun τ ↦ τ.app x) h
  have hleft :
      (Functor.whiskerRight u.left.toNatTrans L ≫ S.iso.hom).app x =
        L.map (u.left.toNatTrans.app x) ≫ S.iso.hom.app x := by
    rfl
  have hright :
      ((u.hom.toFunctor.associator Q.fst L).hom ≫
            u.hom.toFunctor.whiskerLeft Q.iso.hom ≫
              (u.hom.toFunctor.associator Q.snd R).inv ≫
                Functor.whiskerRight u.right.toNatTrans R).app x =
        Q.iso.hom.app (u.hom.toFunctor.obj x) ≫ R.map (u.right.toNatTrans.app x) := by
    repeat rw [NatTrans.comp_app]
    simp
  exact hleft.symm.trans (hx.trans hright)

/-- Helper for Lemma 4.31.13: whiskering a fixed square `Q` by a functor `J` gives the source
square over the same cospan with apex the source of `J`. -/
private abbrev comparison_whisker_source_square
    {A₀ : Type (max u v)} [Category.{v} A₀]
    {B₀ : Type (max u v)} [Category.{v} B₀]
    {C₀ : Type (max u v)} [Category.{v} C₀]
    {Y₀ : Type (max u v)} [Category.{v} Y₀]
    {T₀ : Type (max u v)} [Category.{v} T₀]
    {L : A₀ ⥤ C₀} {R : B₀ ⥤ C₀}
    (Q : CatCommSqOver L R T₀)
    (J : Y₀ ⥤ T₀) :
    CatCommSqOver L R Y₀ :=
  { fst := J ⋙ Q.fst
    snd := J ⋙ Q.snd
    iso := Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft J Q.iso ≪≫
      (Functor.associator _ _ _).symm }

/-- Helper for Lemma 4.31.13: the whiskered square construction is functorial in the apex
functor. -/
private theorem comparison_whisker_source_square_map_w
    {A₀ : Type (max u v)} [Category.{v} A₀]
    {B₀ : Type (max u v)} [Category.{v} B₀]
    {C₀ : Type (max u v)} [Category.{v} C₀]
    {Y₀ : Type (max u v)} [Category.{v} Y₀]
    {T₀ : Type (max u v)} [Category.{v} T₀]
    {L : A₀ ⥤ C₀} {R : B₀ ⥤ C₀}
    (Q : CatCommSqOver L R T₀)
    {J K : Y₀ ⥤ T₀}
    (η : J ⟶ K) :
    Functor.whiskerRight (Functor.whiskerRight η Q.fst) L ≫
        (comparison_whisker_source_square Q K).iso.hom =
      (comparison_whisker_source_square Q J).iso.hom ≫
        Functor.whiskerRight (Functor.whiskerRight η Q.snd) R := by
  -- Naturality of `Q.iso` is exactly the compatibility condition after expanding the whiskering.
  ext x
  simpa [comparison_whisker_source_square, Category.assoc] using
    Q.iso.hom.naturality (η.app x)

/-- Helper for Lemma 4.31.13: the whiskered source squares form a functor out of the apex
functor category. -/
private abbrev comparison_whisker_source_square_functor
    {A₀ : Type (max u v)} [Category.{v} A₀]
    {B₀ : Type (max u v)} [Category.{v} B₀]
    {C₀ : Type (max u v)} [Category.{v} C₀]
    {Y₀ : Type (max u v)} [Category.{v} Y₀]
    {T₀ : Type (max u v)} [Category.{v} T₀]
    {L : A₀ ⥤ C₀} {R : B₀ ⥤ C₀}
    (Q : CatCommSqOver L R T₀) :
    (Y₀ ⥤ T₀) ⥤ CatCommSqOver L R Y₀ :=
  { obj := comparison_whisker_source_square Q
    map := fun η ↦
      { fst := Functor.whiskerRight η Q.fst
        snd := Functor.whiskerRight η Q.snd
        w := comparison_whisker_source_square_map_w Q η }
    map_id := by
      -- The identity transformation whiskers to identities on both legs.
      intro J
      apply CatCommSqOver.hom_ext <;> ext x <;> simp
    map_comp := by
      -- Composition of whiskered transformations is computed componentwise.
      intro J K M η θ
      apply CatCommSqOver.hom_ext <;> ext x <;> simp }

/-- Helper for Lemma 4.31.13: a square morphism into `Q` is equivalently a costructured arrow
into the functor of whiskered source squares attached to `Q`. -/
private abbrev square_hom_to_comparison_costructuredArrow
    {A₀ : Type (max u v)} [Category.{v} A₀]
    {B₀ : Type (max u v)} [Category.{v} B₀]
    {C₀ : Type (max u v)} [Category.{v} C₀]
    {Y₀ : Type (max u v)} [Category.{v} Y₀]
    {T₀ : Type (max u v)} [Category.{v} T₀]
    {L : A₀ ⥤ C₀} {R : B₀ ⥤ C₀}
    (S : CatCommSqOver L R Y₀)
    (Q : CatCommSqOver L R T₀)
    (u : S.toBicategoricalSquare ⟶ Q.toBicategoricalSquare) :
    CostructuredArrow (comparison_whisker_source_square_functor Q) S :=
  CostructuredArrow.mk
    ({ fst := u.left.toNatTrans
       snd := u.right.toNatTrans
       w := by
         -- The square-morphism compatibility is exactly the `CatCommSqOver` compatibility for the
         -- whiskered source square after translating the bicategorical relation to `Cat`.
         dsimp [comparison_whisker_source_square]
         simpa only [← Category.assoc] using
           congrArg CategoryTheory.Cat.Hom₂.toNatTrans u.comm } :
      comparison_whisker_source_square Q u.hom.toFunctor ⟶ S)

/-- Helper for Lemma 4.31.13: the `CatCommSqOver` compatibility of a costructured arrow is the
bicategorical square-morphism compatibility for the recovered square map. -/
private theorem comparison_costructuredArrow_to_square_hom_comm
    {A₀ : Type (max u v)} [Category.{v} A₀]
    {B₀ : Type (max u v)} [Category.{v} B₀]
    {C₀ : Type (max u v)} [Category.{v} C₀]
    {Y₀ : Type (max u v)} [Category.{v} Y₀]
    {T₀ : Type (max u v)} [Category.{v} T₀]
    {L : A₀ ⥤ C₀} {R : B₀ ⥤ C₀}
    (S : CatCommSqOver L R Y₀)
    (Q : CatCommSqOver L R T₀)
    (a : CostructuredArrow (comparison_whisker_source_square_functor Q) S) :
    Bicategory.whiskerRight (NatTrans.toCatHom₂ a.hom.fst) L.toCatHom ≫
        S.toBicategoricalSquare.ψ.hom =
      (Bicategory.associator a.left.toCatHom Q.toBicategoricalSquare.p L.toCatHom).hom ≫
        Bicategory.whiskerLeft a.left.toCatHom Q.toBicategoricalSquare.ψ.hom ≫
        (Bicategory.associator a.left.toCatHom Q.toBicategoricalSquare.q R.toCatHom).inv ≫
        Bicategory.whiskerRight (NatTrans.toCatHom₂ a.hom.snd) R.toCatHom := by
  -- Evaluate the bicategorical square equation objectwise, so both sides can be compared to the
  -- ordinary `CatCommSqOver` midpoint.
  apply Cat.Hom₂.ext
  ext x
  let mid := Q.iso.hom.app (a.left.obj x) ≫ R.map (a.hom.snd.app x)
  have hnorm :
      ((a.left.associator Q.fst L).hom ≫
          (a.left.isoWhiskerLeft Q.iso).hom ≫
          (a.left.associator Q.snd R).inv).app x =
        Q.iso.hom.app (a.left.obj x) := by
    simp
  have hw :
      (Bicategory.whiskerRight (NatTrans.toCatHom₂ a.hom.fst) L.toCatHom ≫
          S.toBicategoricalSquare.ψ.hom).toNatTrans.app x = mid := by
    -- The comma-arrow compatibility is exactly the left-hand comparison with that midpoint.
    change (Functor.whiskerRight a.hom.fst L ≫ S.iso.hom).app x = mid
    simpa [mid] using
      hnorm ▸ (CatCommSqOver.w_app
        (X := Y₀) (S := comparison_whisker_source_square Q a.left) (S' := S) a.hom x)
  have hr :
      ((Bicategory.associator a.left.toCatHom Q.toBicategoricalSquare.p L.toCatHom).hom ≫
          Bicategory.whiskerLeft a.left.toCatHom Q.toBicategoricalSquare.ψ.hom ≫
          (Bicategory.associator a.left.toCatHom Q.toBicategoricalSquare.q R.toCatHom).inv ≫
          Bicategory.whiskerRight (NatTrans.toCatHom₂ a.hom.snd) R.toCatHom).toNatTrans.app x =
        mid := by
    -- The right-hand bicategorical expression expands to the same midpoint.
    change ((a.left.associator Q.fst L).hom ≫ a.left.whiskerLeft Q.iso.hom ≫
        (a.left.associator Q.snd R).inv ≫ Functor.whiskerRight a.hom.snd R).app x = mid
    repeat rw [NatTrans.comp_app]
    simp [mid]
  exact hw.trans hr.symm

/-- Helper for Lemma 4.31.13: a costructured arrow into the whiskered-square functor recovers the
corresponding square morphism into `Q`. -/
private abbrev comparison_costructuredArrow_to_square_hom
    {A₀ : Type (max u v)} [Category.{v} A₀]
    {B₀ : Type (max u v)} [Category.{v} B₀]
    {C₀ : Type (max u v)} [Category.{v} C₀]
    {Y₀ : Type (max u v)} [Category.{v} Y₀]
    {T₀ : Type (max u v)} [Category.{v} T₀]
    {L : A₀ ⥤ C₀} {R : B₀ ⥤ C₀}
    (S : CatCommSqOver L R Y₀)
    (Q : CatCommSqOver L R T₀)
    (a : CostructuredArrow (comparison_whisker_source_square_functor Q) S) :
    S.toBicategoricalSquare ⟶ Q.toBicategoricalSquare :=
  { hom := a.left.toCatHom
    left := a.hom.fst.toCatHom₂
    right := a.hom.snd.toCatHom₂
    comm := comparison_costructuredArrow_to_square_hom_comm S Q a }

/-- Helper for Lemma 4.31.13: a `2`-morphism of square maps becomes the corresponding morphism in
the comma category of whiskered source squares. -/
private theorem square_twohom_to_comparison_costructuredArrow_hom_eq
    {A₀ : Type (max u v)} [Category.{v} A₀]
    {B₀ : Type (max u v)} [Category.{v} B₀]
    {C₀ : Type (max u v)} [Category.{v} C₀]
    {Y₀ : Type (max u v)} [Category.{v} Y₀]
    {T₀ : Type (max u v)} [Category.{v} T₀]
    {L : A₀ ⥤ C₀} {R : B₀ ⥤ C₀}
    (S : CatCommSqOver L R Y₀)
    (Q : CatCommSqOver L R T₀)
    {u v : S.toBicategoricalSquare ⟶ Q.toBicategoricalSquare}
    (η : u ⟶ v) :
    (comparison_whisker_source_square_functor Q).map η.hom.toNatTrans ≫
        (square_hom_to_comparison_costructuredArrow S Q v).hom =
      (square_hom_to_comparison_costructuredArrow S Q u).hom := by
  -- Equality in the comma category is detected on the two displayed natural-transformation legs.
  apply CatCommSqOver.hom_ext
  · ext x
    simpa [comparison_whisker_source_square_functor, comparison_whisker_source_square] using
      congrArg (fun τ ↦ τ.app x) (congrArg Cat.Hom₂.toNatTrans η.left_comm)
  · ext x
    simpa [comparison_whisker_source_square_functor, comparison_whisker_source_square] using
      congrArg (fun τ ↦ τ.app x) (congrArg Cat.Hom₂.toNatTrans η.right_comm)

/-- Helper for Lemma 4.31.13: a morphism in the comma category of whiskered source squares
recovers the corresponding `2`-morphism of square maps. -/
private abbrev comparison_costructuredArrow_hom_to_square_twohom
    {A₀ : Type (max u v)} [Category.{v} A₀]
    {B₀ : Type (max u v)} [Category.{v} B₀]
    {C₀ : Type (max u v)} [Category.{v} C₀]
    {Y₀ : Type (max u v)} [Category.{v} Y₀]
    {T₀ : Type (max u v)} [Category.{v} T₀]
    {L : A₀ ⥤ C₀} {R : B₀ ⥤ C₀}
    (S : CatCommSqOver L R Y₀)
    (Q : CatCommSqOver L R T₀)
    {a b : CostructuredArrow (comparison_whisker_source_square_functor Q) S}
    (η : a ⟶ b) :
    comparison_costructuredArrow_to_square_hom S Q a ⟶
      comparison_costructuredArrow_to_square_hom S Q b :=
  { hom := by
      simpa [comparison_costructuredArrow_to_square_hom] using η.left.toCatHom₂
    left_comm := by
      -- The left projection of the comma-category relation becomes the left-leg compatibility.
      apply Cat.Hom₂.ext
      ext x
      simpa [comparison_costructuredArrow_to_square_hom,
        comparison_whisker_source_square_functor, comparison_whisker_source_square] using
        congrArg (fun τ ↦ τ.app x) (congrArg CatCommSqOver.Hom.fst (CostructuredArrow.w η))
    right_comm := by
      -- The right projection gives the matching compatibility on the right leg.
      apply Cat.Hom₂.ext
      ext x
      simpa [comparison_costructuredArrow_to_square_hom,
        comparison_whisker_source_square_functor, comparison_whisker_source_square] using
        congrArg (fun τ ↦ τ.app x) (congrArg CatCommSqOver.Hom.snd (CostructuredArrow.w η)) }

/-- Helper for Lemma 4.31.13: square maps into `Q` assemble into a functor to costructured
arrows into the whiskered-source-square functor. -/
private abbrev square_hom_to_comparison_costructuredArrow_functor
    {A₀ : Type (max u v)} [Category.{v} A₀]
    {B₀ : Type (max u v)} [Category.{v} B₀]
    {C₀ : Type (max u v)} [Category.{v} C₀]
    {Y₀ : Type (max u v)} [Category.{v} Y₀]
    {T₀ : Type (max u v)} [Category.{v} T₀]
    {L : A₀ ⥤ C₀} {R : B₀ ⥤ C₀}
    (S : CatCommSqOver L R Y₀)
    (Q : CatCommSqOver L R T₀) :
    (S.toBicategoricalSquare ⟶ Q.toBicategoricalSquare) ⥤
      CostructuredArrow (comparison_whisker_source_square_functor Q) S :=
  { obj := square_hom_to_comparison_costructuredArrow S Q
    map := fun η ↦
      CostructuredArrow.homMk
        η.hom.toNatTrans
        (square_twohom_to_comparison_costructuredArrow_hom_eq S Q η)
    map_id := by
      -- Identity `2`-morphisms become identity comma morphisms.
      intro u
      apply CostructuredArrow.hom_ext
      rfl
    map_comp := by
      -- Vertical composition of `2`-morphisms is sent to composition in the comma category.
      intro u v w η θ
      apply CostructuredArrow.hom_ext
      rfl }

/-- Helper for Lemma 4.31.13: costructured arrows into the whiskered-source-square functor
assemble into a functor back to square maps. -/
private abbrev comparison_costructuredArrow_to_square_hom_functor
    {A₀ : Type (max u v)} [Category.{v} A₀]
    {B₀ : Type (max u v)} [Category.{v} B₀]
    {C₀ : Type (max u v)} [Category.{v} C₀]
    {Y₀ : Type (max u v)} [Category.{v} Y₀]
    {T₀ : Type (max u v)} [Category.{v} T₀]
    {L : A₀ ⥤ C₀} {R : B₀ ⥤ C₀}
    (S : CatCommSqOver L R Y₀)
    (Q : CatCommSqOver L R T₀) :
    CostructuredArrow (comparison_whisker_source_square_functor Q) S ⥤
      (S.toBicategoricalSquare ⟶ Q.toBicategoricalSquare) :=
  { obj := comparison_costructuredArrow_to_square_hom S Q
    map := fun η ↦ comparison_costructuredArrow_hom_to_square_twohom S Q η
    map_id := by
      -- Identity comma morphisms translate back to identity `2`-morphisms.
      intro a
      apply BicategoricalTwoCommutativeSquare.TwoHom.ext
      rfl
    map_comp := by
      -- Composition is preserved because the reconstruction keeps the same apex transformation.
      intro a b c η θ
      apply BicategoricalTwoCommutativeSquare.TwoHom.ext
      rfl }

/-- Helper for Lemma 4.31.13: converting a square map to a costructured arrow and back leaves the
square map unchanged. -/
@[simp] private theorem comparison_square_hom_roundtrip
    {A₀ : Type (max u v)} [Category.{v} A₀]
    {B₀ : Type (max u v)} [Category.{v} B₀]
    {C₀ : Type (max u v)} [Category.{v} C₀]
    {Y₀ : Type (max u v)} [Category.{v} Y₀]
    {T₀ : Type (max u v)} [Category.{v} T₀]
    {L : A₀ ⥤ C₀} {R : B₀ ⥤ C₀}
    (S : CatCommSqOver L R Y₀)
    (Q : CatCommSqOver L R T₀) :
    ∀ u : S.toBicategoricalSquare ⟶ Q.toBicategoricalSquare,
      comparison_costructuredArrow_to_square_hom S Q
        (square_hom_to_comparison_costructuredArrow S Q u) = u := by
  intro u
  -- The reconstructed square map is definitionally the same after unpacking the structure.
  rcases u with ⟨hom, left, right, comm⟩
  rfl

/-- Helper for Lemma 4.31.13: converting a costructured arrow to a square map and back leaves the
costructured arrow unchanged. -/
@[simp] private theorem comparison_costructuredArrow_roundtrip
    {A₀ : Type (max u v)} [Category.{v} A₀]
    {B₀ : Type (max u v)} [Category.{v} B₀]
    {C₀ : Type (max u v)} [Category.{v} C₀]
    {Y₀ : Type (max u v)} [Category.{v} Y₀]
    {T₀ : Type (max u v)} [Category.{v} T₀]
    {L : A₀ ⥤ C₀} {R : B₀ ⥤ C₀}
    (S : CatCommSqOver L R Y₀)
    (Q : CatCommSqOver L R T₀) :
    ∀ a : CostructuredArrow (comparison_whisker_source_square_functor Q) S,
      square_hom_to_comparison_costructuredArrow S Q
        (comparison_costructuredArrow_to_square_hom S Q a) = a := by
  intro a
  -- The reverse round-trip preserves the apex functor and the displayed square morphism into `S`.
  rcases a with ⟨left, hom⟩
  rfl

/-- Helper for Lemma 4.31.13: square maps into `Q` are equivalent to costructured arrows into the
whiskered-source-square functor attached to `Q`. -/
private noncomputable abbrev square_hom_equiv_comparison_costructuredArrow
    {A₀ : Type (max u v)} [Category.{v} A₀]
    {B₀ : Type (max u v)} [Category.{v} B₀]
    {C₀ : Type (max u v)} [Category.{v} C₀]
    {Y₀ : Type (max u v)} [Category.{v} Y₀]
    {T₀ : Type (max u v)} [Category.{v} T₀]
    {L : A₀ ⥤ C₀} {R : B₀ ⥤ C₀}
    (S : CatCommSqOver L R Y₀)
    (Q : CatCommSqOver L R T₀) :
    (S.toBicategoricalSquare ⟶ Q.toBicategoricalSquare) ≌
      CostructuredArrow (comparison_whisker_source_square_functor Q) S :=
  let forward := square_hom_to_comparison_costructuredArrow_functor S Q
  let backward := comparison_costructuredArrow_to_square_hom_functor S Q
  let unitIso :
      𝟭 (S.toBicategoricalSquare ⟶ Q.toBicategoricalSquare) ≅ forward ⋙ backward :=
    NatIso.ofComponents
      (fun u ↦ CategoryTheory.eqToIso ((comparison_square_hom_roundtrip S Q) u))
      (fun {u v} η ↦ by
        -- After reducing both round-trip equalities, naturality is the identity computation on
        -- the underlying apex `2`-morphism.
        rcases u with ⟨uhom, uleft, uright, ucomm⟩
        rcases v with ⟨vhom, vleft, vright, vcomm⟩
        rcases η with ⟨ηhom, ηleft, ηright⟩
        cases (comparison_square_hom_roundtrip S Q
          { hom := uhom, left := uleft, right := uright, comm := ucomm })
        cases (comparison_square_hom_roundtrip S Q
          { hom := vhom, left := vleft, right := vright, comm := vcomm })
        apply BicategoricalTwoCommutativeSquare.TwoHom.ext
        change ηhom ≫ 𝟙 vhom = 𝟙 uhom ≫ ηhom
        simp
      )
  let counitIso :
      backward ⋙ forward ≅
        𝟭 (CostructuredArrow (comparison_whisker_source_square_functor Q) S) :=
    NatIso.ofComponents
      (fun a ↦ CategoryTheory.eqToIso ((comparison_costructuredArrow_roundtrip S Q) a))
      (fun {a b} η ↦ by
        -- The counit naturality is the same identity computation in the comma category.
        rcases a with ⟨aleft, aright, ahom⟩
        rcases b with ⟨bleft, bright, bhom⟩
        rcases η with ⟨ηleft, ηw⟩
        cases (comparison_costructuredArrow_roundtrip S Q
          { left := aleft, right := aright, hom := ahom })
        cases (comparison_costructuredArrow_roundtrip S Q
          { left := bleft, right := bright, hom := bhom })
        simp [forward, backward]
      )
  CategoryTheory.Equivalence.mk forward backward unitIso counitIso

/-- Helper for Lemma 4.31.13: finality of `Q` transfers to terminal objects in the comma
categories attached to whiskering into `Q`. -/
private theorem comparison_costructuredArrow_hasTerminal_of_isFinal
    {A₀ : Type (max u v)} [Category.{v} A₀]
    {B₀ : Type (max u v)} [Category.{v} B₀]
    {C₀ : Type (max u v)} [Category.{v} C₀]
    {Y₀ : Type (max u v)} [Category.{v} Y₀]
    {T₀ : Type (max u v)} [Category.{v} T₀]
    {L : A₀ ⥤ C₀} {R : B₀ ⥤ C₀}
    (S : CatCommSqOver L R Y₀)
    (Q : CatCommSqOver L R T₀)
    [Bicategory.IsFinal Q.toBicategoricalSquare] :
    HasTerminal (CostructuredArrow (comparison_whisker_source_square_functor Q) S) := by
  -- Finality of `Q` gives a terminal object in the hom-category, and the generic equivalence
  -- above transports that terminal object to the corresponding comma category.
  let e := square_hom_equiv_comparison_costructuredArrow S Q
  letI : e.inverse.IsEquivalence := e.symm.isEquivalence_functor
  exact CategoryTheory.hasTerminal_of_equivalence e.inverse

/-- Helper for Lemma 4.31.13: the canonical pullback square over `L` and `R`, viewed in
`CatCommSqOver`, is the target of the comparison-whiskering transport. -/
private abbrev canonical_comparison_square
    {A₀ : Type (max u v)} [Category.{v} A₀]
    {B₀ : Type (max u v)} [Category.{v} B₀]
    {C₀ : Type (max u v)} [Category.{v} C₀]
    {L : A₀ ⥤ C₀} {R : B₀ ⥤ C₀} :
    CatCommSqOver L R (L ⊡ R) :=
  (toCatCommSqOver L R (L ⊡ R)).obj (𝟭 (L ⊡ R))

/-- Helper for Lemma 4.31.13: objectwise, whiskering by the comparison functor identifies the
source square for `Q` with the source square for the canonical pullback square. -/
private theorem comparison_whisker_source_square_obj_iso_w
    {A₀ : Type (max u v)} [Category.{v} A₀]
    {B₀ : Type (max u v)} [Category.{v} B₀]
    {C₀ : Type (max u v)} [Category.{v} C₀]
    {Y₀ : Type (max u v)} [Category.{v} Y₀]
    {T₀ : Type (max u v)} [Category.{v} T₀]
    {L : A₀ ⥤ C₀} {R : B₀ ⥤ C₀}
    (Q : CatCommSqOver L R T₀)
    (J : Y₀ ⥤ T₀) :
    Functor.whiskerRight
        (Iso.refl ((comparison_whisker_source_square Q J).fst)).hom L ≫
        (((Functor.whiskeringRight Y₀ T₀ (L ⊡ R)).obj
              ((toFunctorToCategoricalPullback L R T₀).obj Q) ⋙
            comparison_whisker_source_square_functor
              (canonical_comparison_square (L := L) (R := R))).obj J).iso.hom =
      (comparison_whisker_source_square Q J).iso.hom ≫
        Functor.whiskerRight
          (Iso.refl ((comparison_whisker_source_square Q J).snd)).hom R := by
  -- Both objectwise square descriptions have identical components once the comparison functor is
  -- unfolded back to the canonical pullback square.
  ext x
  simp [comparison_whisker_source_square, canonical_comparison_square]

/-- Helper for Lemma 4.31.13: objectwise, whiskering by the comparison functor identifies the
source square for `Q` with the source square for the canonical pullback square. -/
private abbrev comparison_whisker_source_square_obj_iso
    {A₀ : Type (max u v)} [Category.{v} A₀]
    {B₀ : Type (max u v)} [Category.{v} B₀]
    {C₀ : Type (max u v)} [Category.{v} C₀]
    {Y₀ : Type (max u v)} [Category.{v} Y₀]
    {T₀ : Type (max u v)} [Category.{v} T₀]
    {L : A₀ ⥤ C₀} {R : B₀ ⥤ C₀}
    (Q : CatCommSqOver L R T₀)
    (J : Y₀ ⥤ T₀) :
    comparison_whisker_source_square Q J ≅
      (((Functor.whiskeringRight Y₀ T₀ (L ⊡ R)).obj
            ((toFunctorToCategoricalPullback L R T₀).obj Q)) ⋙
          comparison_whisker_source_square_functor
            (canonical_comparison_square (L := L) (R := R))).obj J :=
  CatCommSqOver.mkIso (Iso.refl _) (Iso.refl _)
    (comparison_whisker_source_square_obj_iso_w Q J)

/-- Helper for Lemma 4.31.13: whiskering by the comparison functor turns a source square for `Q`
into the corresponding source square for the canonical pullback square. -/
private theorem comparison_whisker_source_square_iso_naturality
    {A₀ : Type (max u v)} [Category.{v} A₀]
    {B₀ : Type (max u v)} [Category.{v} B₀]
    {C₀ : Type (max u v)} [Category.{v} C₀]
    {Y₀ : Type (max u v)} [Category.{v} Y₀]
    {T₀ : Type (max u v)} [Category.{v} T₀]
    {L : A₀ ⥤ C₀} {R : B₀ ⥤ C₀}
    (Q : CatCommSqOver L R T₀) :
    ∀ {J K : Y₀ ⥤ T₀} (η : J ⟶ K),
      (comparison_whisker_source_square_functor Q).map η ≫
          (comparison_whisker_source_square_obj_iso Q K).hom =
        (comparison_whisker_source_square_obj_iso Q J).hom ≫
          (((Functor.whiskeringRight Y₀ T₀ (L ⊡ R)).obj
                ((toFunctorToCategoricalPullback L R T₀).obj Q) ⋙
              comparison_whisker_source_square_functor
                (canonical_comparison_square (L := L) (R := R))).map η) := by
  -- The transport is identity on both displayed components, so naturality is componentwise.
  intro J K η
  apply CatCommSqOver.hom_ext <;> ext x <;>
    simp [comparison_whisker_source_square_obj_iso, comparison_whisker_source_square,
      canonical_comparison_square]

/-- Helper for Lemma 4.31.13: whiskering by the comparison functor turns a source square for `Q`
into the corresponding source square for the canonical pullback square. -/
private abbrev comparison_whisker_source_square_iso
    {A₀ : Type (max u v)} [Category.{v} A₀]
    {B₀ : Type (max u v)} [Category.{v} B₀]
    {C₀ : Type (max u v)} [Category.{v} C₀]
    {Y₀ : Type (max u v)} [Category.{v} Y₀]
    {T₀ : Type (max u v)} [Category.{v} T₀]
    {L : A₀ ⥤ C₀} {R : B₀ ⥤ C₀}
    (Q : CatCommSqOver L R T₀) :
    comparison_whisker_source_square_functor Q ≅
      ((Functor.whiskeringRight Y₀ T₀ (L ⊡ R)).obj
          ((toFunctorToCategoricalPullback L R T₀).obj Q)) ⋙
        comparison_whisker_source_square_functor
          (canonical_comparison_square (L := L) (R := R)) :=
  NatIso.ofComponents
    (comparison_whisker_source_square_obj_iso Q)
    (comparison_whisker_source_square_iso_naturality Q)

/-- Helper for Lemma 4.31.13: whiskering by the comparison functor induces an equivalence on the
relevant functor categories. -/
private theorem comparison_whiskering_functor_isEquivalence
    {A₀ : Type (max u v)} [Category.{v} A₀]
    {B₀ : Type (max u v)} [Category.{v} B₀]
    {C₀ : Type (max u v)} [Category.{v} C₀]
    {Y₀ : Type (max u v)} [Category.{v} Y₀]
    {T₀ : Type (max u v)} [Category.{v} T₀]
    {L : A₀ ⥤ C₀} {R : B₀ ⥤ C₀}
    (Q : CatCommSqOver L R T₀)
    (hQ : ((toFunctorToCategoricalPullback L R T₀).obj Q).IsEquivalence) :
    (((Functor.whiskeringRight Y₀ T₀ (L ⊡ R)).obj
          ((toFunctorToCategoricalPullback L R T₀).obj Q))).IsEquivalence := by
  let _ : ((toFunctorToCategoricalPullback L R T₀).obj Q).IsEquivalence := hQ
  infer_instance

/-- Helper for Lemma 4.31.13: after whiskering along an equivalence comparison functor, the comma
categories of source squares for `Q` and for the canonical pullback square are equivalent. -/
private noncomputable abbrev comparison_costructuredArrow_equivalence
    {A₀ : Type (max u v)} [Category.{v} A₀]
    {B₀ : Type (max u v)} [Category.{v} B₀]
    {C₀ : Type (max u v)} [Category.{v} C₀]
    {Y₀ : Type (max u v)} [Category.{v} Y₀]
    {T₀ : Type (max u v)} [Category.{v} T₀]
    {L : A₀ ⥤ C₀} {R : B₀ ⥤ C₀}
    (Q : CatCommSqOver L R T₀)
    (S : CatCommSqOver L R Y₀)
    (hQ : ((toFunctorToCategoricalPullback L R T₀).obj Q).IsEquivalence) :
    CostructuredArrow (comparison_whisker_source_square_functor Q) S ≌
      CostructuredArrow
        (comparison_whisker_source_square_functor
          (canonical_comparison_square (L := L) (R := R)))
        S :=
  let W : (Y₀ ⥤ T₀) ⥤ (Y₀ ⥤ L ⊡ R) :=
    (Functor.whiskeringRight Y₀ T₀ (L ⊡ R)).obj
      ((toFunctorToCategoricalPullback L R T₀).obj Q)
  letI : W.IsEquivalence := comparison_whiskering_functor_isEquivalence (Y₀ := Y₀) Q hQ
  (CostructuredArrow.mapNatIso (comparison_whisker_source_square_iso (Y₀ := Y₀) Q)).trans
    (Functor.asEquivalence (CostructuredArrow.pre W _ S))

/-- Helper for Lemma 4.31.13: if the canonical comparison functor of a commutative square to the
ordinary categorical pullback is an equivalence, then the associated bicategorical square is
final. -/
private theorem isFinal_of_toFunctorToCategoricalPullback_isEquivalence
    {A₀ : Type (max u v)} [Category.{v} A₀]
    {B₀ : Type (max u v)} [Category.{v} B₀]
    {C₀ : Type (max u v)} [Category.{v} C₀]
    {X₀ : Type (max u v)} [Category.{v} X₀]
    {L : A₀ ⥤ C₀} {R : B₀ ⥤ C₀}
    (Q : CatCommSqOver L R X₀)
    (hQ : ((toFunctorToCategoricalPullback L R X₀).obj Q).IsEquivalence) :
    Bicategory.IsFinal Q.toBicategoricalSquare := by
  -- Route correction: transport terminal objects from the canonical categorical pullback square
  -- through the comparison functor, then back across the square-hom/comma equivalence.
  let _ : ((toFunctorToCategoricalPullback L R X₀).obj Q).IsEquivalence := hQ
  refine ⟨fun S ↦ ?_⟩
  let R₀ : CatCommSqOver L R S.obj := as_catCommSqOver L R S
  let e₁ := square_hom_equiv_comparison_costructuredArrow R₀ Q
  let e₂ := comparison_costructuredArrow_equivalence Q R₀ hQ
  let _ :
      Bicategory.IsFinal
        (canonical_comparison_square (L := L) (R := R)).toBicategoricalSquare := by
    simpa [canonical_comparison_square, categoricalPullbackSquare] using
      (categoricalPullback_isTwoFibreProduct (F := L) (G := R))
  let _ :
      HasTerminal
        (CostructuredArrow
          (comparison_whisker_source_square_functor
            (canonical_comparison_square (L := L) (R := R)))
          R₀) :=
    comparison_costructuredArrow_hasTerminal_of_isFinal
      R₀
      (canonical_comparison_square (L := L) (R := R))
  let _ :
      HasTerminal
        (CostructuredArrow (comparison_whisker_source_square_functor Q) R₀) := by
    letI : e₂.functor.IsEquivalence := e₂.isEquivalence_functor
    exact CategoryTheory.hasTerminal_of_equivalence e₂.functor
  letI : e₁.functor.IsEquivalence := e₁.isEquivalence_functor
  exact CategoryTheory.hasTerminal_of_equivalence e₁.functor

open scoped Bicategory

/-- The square
`A ×[C] B ⥤ A ×[D] B`, `A ×[C] B ⥤ C`, `A ×[D] B ⥤ C ×[D] C`, `C ⥤ C ×[D] C`
with bottom map the diagonal `Δₚ H`, viewed as the chapter's bicategorical square in `Cat`. -/
abbrev two_fibre_product_diagonal_square
    (F : A ⥤ C) (G : B ⥤ C) (H : C ⥤ D) :
    BicategoricalTwoCommutativeSquare
      (two_fibre_product_right_vertical F G H).toCatHom
      (Δₚ H).toCatHom :=
  (two_fibre_product_diagonal_square_over F G H).toBicategoricalSquare

/-- Lemma 4.31.13: the displayed square with bottom map the diagonal `Δ_{C/D}` is a
`2`-fibre product diagram, expressed through the chapter's owner predicate
`Bicategory.IsFinal`. -/
theorem two_fibre_product_diagonal_isTwoFibreProduct
    (F : A ⥤ C) (G : B ⥤ C) (H : C ⥤ D) :
    Bicategory.IsFinal (two_fibre_product_diagonal_square F G H) := by
  -- The explicit comparison equivalence feeds directly into the generic finality-transfer bridge.
  refine isFinal_of_toFunctorToCategoricalPullback_isEquivalence
    (Q := two_fibre_product_diagonal_square_over F G H) ?_
  have hcomp := two_fibre_product_diagonal_comparison_isEquivalence F G H
  exact hcomp

/-- Lemma 4.31.13, restated as the canonical `IsFinal` instance on the public square
`two_fibre_product_diagonal_square F G H`. -/
noncomputable instance
    (F : A ⥤ C) (G : B ⥤ C) (H : C ⥤ D) :
    Bicategory.IsFinal (two_fibre_product_diagonal_square F G H) :=
  two_fibre_product_diagonal_isTwoFibreProduct F G H

end CategoryTheory.Limits
