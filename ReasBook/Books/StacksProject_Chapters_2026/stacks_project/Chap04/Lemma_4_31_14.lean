module

public import stacks_project.Chap04.Lemma_4_31_13.Basic
public import stacks_project.Chap04.Lemma_4_31_6
public import stacks_project.Chap04.Lemma_4_31_8
public import stacks_project.Chap04.Lemma_4_31_10
public import stacks_project.Chap04.Lemma_4_31_11
import Mathlib.CategoryTheory.Limits.Shapes.Equivalence

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open CategoricalPullback
open CategoricalPullback.CatCommSqOver
open scoped CategoricalPullback

namespace CategoryTheory.Limits

universe v u

noncomputable section

variable {U : Type v} [Category.{v} U] [IsGroupoid U]
variable {X : Type v} [Category.{v} X] [IsGroupoid X]
variable {V : Type v} [Category.{v} V] [IsGroupoid V]
variable {Y : Type v} [Category.{v} Y] [IsGroupoid Y]

/- Domain-style sampling for Lemma 4.31.14:
- primary domain: bicategorical `2`-fibre products in `Cat`, now kept at the source-facing level
  of an arbitrary square `P : CatCommSqOver F G U` over `F : X ⥤ Y` and `G : V ⥤ Y`;
- sampled owner abstractions in this chapter/project:
  `CatCommSqOver`,
  `CatCommSqOver.toBicategoricalSquare`,
  `BicategoricalTwoCommutativeSquare`,
  `Bicategory.IsFinal`,
  the specialized comparison-equivalence instance from Lemma `4.31.11` for the
  `G₁ × G₂` / `Δ_S` model,
  and `categorical_pullback_diagonal`;
- best owner abstraction: the source-facing input is `P` together with
  `[Bicategory.IsFinal P.toBicategoricalSquare]`; the standard pullback model
  `U = X ×[Y] V` is only a bridge specialization, and the conversion from a categorical square to
  the chapter bicategorical owner is now reused directly from the `CatCommSqOver` owner layer;
- primitive data here: the original square `P`, the induced right-vertical functor on the
  self-pullback over `P.snd`, and the resulting `2`-commutative square with bottom map
  `Δ_F : X ⥤ X ×[Y] X`;
- derived API here: finality of that induced square; any comparison-equivalence statement to the
  categorical pullback model is obtained by direct reuse of
  `CatCommSqOver.toFunctorToCategoricalPullback` together with the generic owner-level bridge from
  Lemma `4.31.11`, rather than by a second local wrapper; the canonical model `U = X ×[Y] V` is
  accessed by specializing the same statements to the canonical square.

Source/core/bridge triage:
- `source-facing`: the induced square attached to an arbitrary `2`-fibre product square `P`;
- `core/canonical`: `Bicategory.IsFinal` of that induced square;
- `bridge/view`: the categorical-pullback comparison functor; the pullback model is obtained by
  taking `P` to be the canonical square on `X ×[Y] V`, not by introducing a second public owner. -/

variable {F : X ⥤ Y} {G : V ⥤ Y}

/-- For a square `U ⥤ V`, `U ⥤ X`, `V ⥤ Y`, `X ⥤ Y`, the left leg `U ⥤ X` induces the right
vertical functor `U ×[V] U ⥤ X ×[Y] X`. -/
abbrev two_fibre_product_left_leg_right_vertical
    (P : CatCommSqOver F G U) :
    P.snd ⊡ P.snd ⥤ F ⊡ F :=
  two_fibre_product_map P.iso P.iso.symm

/- The first projected component of the induced square is the identity on the left leg `U ⥤ X`. -/
abbrev left_leg_diagonal_square_first_iso
    (P : CatCommSqOver F G U) :
    Δₚ P.snd ⋙
        two_fibre_product_left_leg_right_vertical P ⋙
        π₁ F F ≅
      P.fst ⋙ Δₚ F ⋙ π₁ F F :=
  Iso.refl _

/- The second projected component of the same square is also the identity on `U ⥤ X`. -/
abbrev left_leg_diagonal_square_second_iso
    (P : CatCommSqOver F G U) :
    Δₚ P.snd ⋙
        two_fibre_product_left_leg_right_vertical P ⋙
        π₂ F F ≅
      P.fst ⋙ Δₚ F ⋙ π₂ F F :=
  Iso.refl _

/- Coherence of the projected isomorphisms for the diagonal square attached to the left leg of
`P`. After projecting to `Y`, both sides reduce to the structural `2`-commutativity of `P`. -/
theorem left_leg_diagonal_square_coherence
    (P : CatCommSqOver F G U) :
    Functor.whiskerRight
        (left_leg_diagonal_square_first_iso P).hom F ≫
        (Functor.associator _ _ _).hom ≫
        Functor.whiskerLeft
          (P.fst ⋙ Δₚ F)
          (CatCommSq.iso (π₁ F F) (π₂ F F) F F).hom ≫
        (Functor.associator _ _ _).inv =
      (Functor.associator _ _ _).hom ≫
        Functor.whiskerLeft
          (Δₚ P.snd ⋙
            two_fibre_product_left_leg_right_vertical P)
          (CatCommSq.iso (π₁ F F) (π₂ F F) F F).hom ≫
        (Functor.associator _ _ _).inv ≫
        Functor.whiskerRight
          (left_leg_diagonal_square_second_iso P).hom F := by
  -- The first component is definitional, while the second is the inverse-hom identity of
  -- the structural pullback isomorphism.
  ext X
  simpa [two_fibre_product_left_leg_right_vertical] using
    (Iso.hom_inv_id_app P.iso X).symm

/- The square
`U ⥤ U ×[V] U`, `U ⥤ X`, `U ×[V] U ⥤ X ×[Y] X`, `X ⥤ X ×[Y] X`
induced by the left leg of `P` is `2`-commutative. -/
abbrev two_fibre_product_left_leg_diagonal_iso
    (P : CatCommSqOver F G U) :
    Δₚ P.snd ⋙
        two_fibre_product_left_leg_right_vertical P ≅
      P.fst ⋙ Δₚ F :=
  mkNatIso
    (left_leg_diagonal_square_first_iso P)
    (left_leg_diagonal_square_second_iso P)
    (left_leg_diagonal_square_coherence P)

/- The diagonal square over the cospan
`U ×[V] U ⥤ X ×[Y] X ← X`
attached to the left leg of `P`. -/
abbrev two_fibre_product_left_leg_diagonal_square_over
    (P : CatCommSqOver F G U) :
    CatCommSqOver
      (two_fibre_product_left_leg_right_vertical P)
      (Δₚ F)
      U :=
  { fst := Δₚ P.snd
    snd := P.fst
    iso := two_fibre_product_left_leg_diagonal_iso P }

/-- Helper for Lemma 4.31.14: the canonical comparison functor from `U` to the categorical
pullback of the induced cospan `U ×[V] U ⥤ X ×[Y] X ← X`. -/
private abbrev two_fibre_product_left_leg_diagonal_comparison
    (P : CatCommSqOver F G U) :
    U ⥤ (two_fibre_product_left_leg_right_vertical P) ⊡ (Δₚ F) :=
  (toFunctorToCategoricalPullback
    (two_fibre_product_left_leg_right_vertical P)
    (Δₚ F)
    U).obj (two_fibre_product_left_leg_diagonal_square_over P)

/-- Helper for Lemma 4.31.14: the second projection of the diagonal comparison functor is exactly
the original left leg `P.fst`. -/
private theorem two_fibre_product_left_leg_diagonal_comparison_obj_snd
    (P : CatCommSqOver F G U) (x : U) :
    ((two_fibre_product_left_leg_diagonal_comparison P).obj x).snd = P.fst.obj x := by
  -- The comparison functor packages the diagonal square into the categorical pullback, so its
  -- second component is definitionally the second leg of that square.
  rfl

/-- Helper for Lemma 4.31.14: evaluating the commutativity of a square morphism in `Cat` gives the
expected objectwise compatibility between the two legs and the square isomorphisms. -/
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
  -- in `Cat`, then evaluate at `x` and simplify the whiskering/associator terms.
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

/-- Helper for Lemma 4.31.14: whiskering a fixed square `Q` by a functor `J` gives the source
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

/-- Helper for Lemma 4.31.14: the whiskered square construction is functorial in the apex functor.
-/
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

/-- Helper for Lemma 4.31.14: the whiskered source squares form a functor out of the apex functor
category. -/
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

/-- Helper for Lemma 4.31.14: a square morphism into `Q` is equivalently a costructured arrow into
the functor of whiskered source squares attached to `Q`. -/
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

/-- Helper for Lemma 4.31.14: the `CatCommSqOver` compatibility of a costructured arrow is the
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
  -- ordinary `CatCommSqOver` midpoint `Q.iso.hom.app (a.left.obj x) ≫ R.map (a.hom.snd.app x)`.
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
    -- The right-hand bicategorical expression expands to the same midpoint after evaluating at
    -- `x` and simplifying the whiskered square isomorphism.
    change ((a.left.associator Q.fst L).hom ≫ a.left.whiskerLeft Q.iso.hom ≫
        (a.left.associator Q.snd R).inv ≫ Functor.whiskerRight a.hom.snd R).app x = mid
    repeat rw [NatTrans.comp_app]
    simp [mid]
  exact hw.trans hr.symm

/-- Helper for Lemma 4.31.14: a costructured arrow into the whiskered-square functor recovers the
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

/-- Helper for Lemma 4.31.14: a `2`-morphism of square maps becomes the corresponding morphism in
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

/-- Helper for Lemma 4.31.14: a morphism in the comma category of whiskered source squares
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

/-- Helper for Lemma 4.31.14: square maps into `Q` assemble into a functor to costructured
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
      -- Identity `2`-morphisms become identity comma morphisms on the whiskered apex functor.
      intro u
      apply CostructuredArrow.hom_ext
      rfl
    map_comp := by
      -- Vertical composition of `2`-morphisms is sent to composition in the comma category.
      intro u v w η θ
      apply CostructuredArrow.hom_ext
      rfl }

/-- Helper for Lemma 4.31.14: costructured arrows into the whiskered-source-square functor
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

/-- Helper for Lemma 4.31.14: converting a square map to a costructured arrow and back leaves the
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

/-- Helper for Lemma 4.31.14: converting a costructured arrow to a square map and back leaves the
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

/-- Helper for Lemma 4.31.14: square maps into `Q` are equivalent to costructured arrows into the
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

/-- Helper for Lemma 4.31.14: finality of `Q` transfers to terminal objects in the comma
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

/-- Helper for Lemma 4.31.14: the canonical pullback square over `L` and `R`, viewed in
`CatCommSqOver`, is the target of the comparison-whiskering transport. -/
private abbrev canonical_comparison_square
    {A₀ : Type (max u v)} [Category.{v} A₀]
    {B₀ : Type (max u v)} [Category.{v} B₀]
    {C₀ : Type (max u v)} [Category.{v} C₀]
    {L : A₀ ⥤ C₀} {R : B₀ ⥤ C₀} :
    CatCommSqOver L R (L ⊡ R) :=
  (toCatCommSqOver L R (L ⊡ R)).obj (𝟭 (L ⊡ R))

/-- Helper for Lemma 4.31.14: objectwise, whiskering by the comparison functor identifies the
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

/-- Helper for Lemma 4.31.14: objectwise, whiskering by the comparison functor identifies the
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

/-- Helper for Lemma 4.31.14: whiskering by the comparison functor turns a source square for `Q`
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

/-- Helper for Lemma 4.31.14: whiskering by the comparison functor turns a source square for `Q`
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

/-- Helper for Lemma 4.31.14: whiskering by the comparison functor induces an equivalence on the
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

/-- Helper for Lemma 4.31.14: after whiskering along an equivalence comparison functor, the comma
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

/-- Helper for Lemma 4.31.14: if the comparison functor from a commutative square to the
categorical pullback model is an equivalence, then the associated bicategorical square is final. -/
private theorem isFinal_of_comparison_isEquivalence
    {A₀ : Type (max u v)} [Category.{v} A₀]
    {B₀ : Type (max u v)} [Category.{v} B₀]
    {C₀ : Type (max u v)} [Category.{v} C₀]
    {T₀ : Type (max u v)} [Category.{v} T₀]
    {L : A₀ ⥤ C₀} {R : B₀ ⥤ C₀}
    (Q : CatCommSqOver L R T₀)
    (hQ : ((toFunctorToCategoricalPullback L R T₀).obj Q).IsEquivalence) :
    Bicategory.IsFinal Q.toBicategoricalSquare := by
  -- Route correction: the generic hom/comma bridge is now available, so finality is obtained by
  -- transporting terminal objects from the canonical pullback square along the comparison
  -- functor and then back across the hom/comma equivalence.
  let _ : ((toFunctorToCategoricalPullback L R T₀).obj Q).IsEquivalence := hQ
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

/-- Helper for Lemma 4.31.14: the comparison functor for the induced left-leg diagonal square is an
equivalence. -/
private theorem two_fibre_product_left_leg_diagonal_comparison_isEquivalence
    (P : CatCommSqOver F G U)
    [Bicategory.IsFinal P.toBicategoricalSquare] :
    (two_fibre_product_left_leg_diagonal_comparison P).IsEquivalence := by
  -- Route correction: rather than packaging another large transport equivalence, prove directly
  -- that the diagonal comparison is fully faithful, and then construct chosen objectwise
  -- preimages by pulling the target object back through the original comparison
  -- `U ⥤ X ×[Y] V`, which is already an equivalence by the `2`-fibre product hypothesis.
  let c : U ⥤ F ⊡ G := (toFunctorToCategoricalPullback F G U).obj P
  let d : U ⥤ (two_fibre_product_left_leg_right_vertical P) ⊡ (Δₚ F) :=
    two_fibre_product_left_leg_diagonal_comparison P
  let hc : c.IsEquivalence := toFunctorToCategoricalPullback_isEquivalence_of_isFinal P
  letI : c.IsEquivalence := hc
  letI : c.Faithful := inferInstance
  letI : c.Full := inferInstance
  have hff : Nonempty d.FullyFaithful := by
    -- A morphism between diagonal-comparison objects is determined by its first `U`-component.
    rw [Functor.FullyFaithful.nonempty_iff_map_bijective]
    intro X₀ Y₀
    refine ⟨?_, ?_⟩
    · intro f g hfg
      have hfst := congrArg (fun k ↦ k.fst.fst) hfg
      simpa [d, two_fibre_product_left_leg_diagonal_comparison] using hfst
    · intro φ
      refine ⟨φ.fst.fst, ?_⟩
      have hsnd_eq :
          φ.fst.snd = φ.fst.fst := by
        have hπ₂ :
            P.snd.map φ.fst.snd = P.snd.map φ.fst.fst := by
          simpa [d, two_fibre_product_left_leg_diagonal_comparison] using φ.fst.w.symm
        have hπ₁_left :
            P.fst.map φ.fst.snd = φ.snd := by
          simpa [d, two_fibre_product_left_leg_diagonal_comparison,
            two_fibre_product_left_leg_right_vertical] using
            congrArg CategoricalPullback.Hom.snd φ.w
        have hπ₁_right :
            P.fst.map φ.fst.fst = φ.snd := by
          simpa [d, two_fibre_product_left_leg_diagonal_comparison,
            two_fibre_product_left_leg_right_vertical] using
            congrArg CategoricalPullback.Hom.fst φ.w
        have hcmap :
            c.map φ.fst.snd = c.map φ.fst.fst := by
          apply CategoricalPullback.hom_ext
          · simpa [c] using hπ₁_left.trans hπ₁_right.symm
          · simpa [c] using hπ₂
        exact c.map_injective hcmap
      apply CategoricalPullback.hom_ext
      · apply CategoricalPullback.hom_ext
        · simp [d, two_fibre_product_left_leg_diagonal_comparison]
        · simpa [d, two_fibre_product_left_leg_diagonal_comparison] using hsnd_eq.symm
      · simpa [d, two_fibre_product_left_leg_diagonal_comparison] using
          congrArg CategoricalPullback.Hom.fst φ.w
  classical
  let hdFF : d.FullyFaithful := Classical.choice hff
  let hcFF : c.FullyFaithful := Functor.FullyFaithful.ofFullyFaithful c
  letI : d.Faithful := hdFF.faithful
  letI : d.Full := hdFF.full
  letI : d.EssSurj := by
    refine ⟨fun T ↦ ?_⟩
    let e₁ : P.fst.obj T.fst.fst ≅ T.snd :=
      { hom := T.iso.hom.fst
        inv := T.iso.inv.fst
        hom_inv_id := by
          exact congrArg CategoricalPullback.Hom.fst T.iso.hom_inv_id
        inv_hom_id := by
          exact congrArg CategoricalPullback.Hom.fst T.iso.inv_hom_id }
    let e₂ : P.fst.obj T.fst.snd ≅ T.snd :=
      { hom := T.iso.hom.snd
        inv := T.iso.inv.snd
        hom_inv_id := by
          exact congrArg CategoricalPullback.Hom.snd T.iso.hom_inv_id
        inv_hom_id := by
          exact congrArg CategoricalPullback.Hom.snd T.iso.inv_hom_id }
    -- The inverse-side compatibility of `T.iso` identifies the two `U`-legs after projecting
    -- through the original comparison functor `c : U ⥤ X ×[Y] V`.
    have hcompat :
        F.map (e₂ ≪≫ e₁.symm).hom ≫ P.iso.hom.app T.fst.fst =
          P.iso.hom.app T.fst.snd ≫ G.map T.fst.iso.symm.hom := by
      have hraw :
          F.map T.iso.hom.snd =
            P.iso.hom.app T.fst.snd ≫
              G.map T.fst.iso.symm.hom ≫
                P.iso.inv.app T.fst.fst ≫
                  F.map T.iso.hom.fst := by
        simpa [two_fibre_product_left_leg_right_vertical, Category.assoc] using T.iso.hom.w'
      have hleft :
          F.map (e₂ ≪≫ e₁.symm).hom ≫ P.iso.hom.app T.fst.fst =
            F.map T.iso.hom.snd ≫ F.map T.iso.inv.fst ≫ P.iso.hom.app T.fst.fst := by
        simp [e₁, e₂, Functor.map_comp, Category.assoc]
      have hmid :
          F.map T.iso.hom.snd ≫ F.map T.iso.inv.fst ≫ P.iso.hom.app T.fst.fst =
            P.iso.hom.app T.fst.snd ≫
              G.map T.fst.iso.symm.hom ≫
                P.iso.inv.app T.fst.fst ≫
                  F.map T.iso.hom.fst ≫
                    F.map T.iso.inv.fst ≫
                      P.iso.hom.app T.fst.fst := by
        simpa [Category.assoc] using congrArg
          (fun k ↦ k ≫ F.map T.iso.inv.fst ≫ P.iso.hom.app T.fst.fst) hraw
      have hright :
          P.iso.hom.app T.fst.snd ≫
              G.map T.fst.iso.symm.hom ≫
                P.iso.inv.app T.fst.fst ≫
                  F.map T.iso.hom.fst ≫
                    F.map T.iso.inv.fst ≫
                      P.iso.hom.app T.fst.fst =
            P.iso.hom.app T.fst.snd ≫ G.map T.fst.iso.symm.hom := by
        have hmap :
            F.map T.iso.hom.fst ≫ F.map T.iso.inv.fst =
              𝟙 (F.obj (P.fst.obj T.fst.fst)) := by
          simpa [e₁, Functor.map_comp] using congrArg F.map e₁.hom_inv_id
        have hcancel :
            P.iso.inv.app T.fst.fst ≫
                F.map T.iso.hom.fst ≫
                  F.map T.iso.inv.fst ≫
                    P.iso.hom.app T.fst.fst =
              𝟙 (G.obj (P.snd.obj T.fst.fst)) := by
          have hcancel₁ :
              P.iso.inv.app T.fst.fst ≫
                  F.map T.iso.hom.fst ≫
                    F.map T.iso.inv.fst ≫
                      P.iso.hom.app T.fst.fst =
                P.iso.inv.app T.fst.fst ≫ P.iso.hom.app T.fst.fst := by
            simpa [Category.assoc] using congrArg
              (fun k ↦ P.iso.inv.app T.fst.fst ≫ k ≫ P.iso.hom.app T.fst.fst) hmap
          exact hcancel₁.trans (Iso.inv_hom_id (P.iso.app T.fst.fst))
        simpa [Category.assoc] using congrArg
          (fun k ↦ P.iso.hom.app T.fst.snd ≫ G.map T.fst.iso.symm.hom ≫ k) hcancel
      exact hleft.trans (hmid.trans hright)
    let ez : c.obj T.fst.snd ≅ c.obj T.fst.fst :=
      CategoricalPullback.mkIso (e₂ ≪≫ e₁.symm) T.fst.iso.symm hcompat
    let eu : T.fst.snd ≅ T.fst.fst := hcFF.preimageIso ez
    have heu_map : c.mapIso eu = ez := by
      simpa [eu] using (hcFF.isoEquiv.right_inv ez)
    have heu_fst :
        P.fst.map eu.hom = (e₂ ≪≫ e₁.symm).hom := by
      simpa [c] using congrArg (fun i ↦ i.hom.fst) heu_map
    have heu_snd :
        P.snd.map eu.hom = T.fst.iso.symm.hom := by
      simpa [c] using congrArg (fun i ↦ i.hom.snd) heu_map
    have heu_fst_inv :
        P.fst.map eu.symm.hom = (e₂ ≪≫ e₁.symm).symm.hom := by
      simpa [c] using congrArg (fun i ↦ i.inv.fst) heu_map
    have heu_snd_inv :
        P.snd.map eu.symm.hom = T.fst.iso.hom := by
      simpa [c] using congrArg (fun i ↦ i.inv.snd) heu_map
    -- The first pullback component becomes diagonal after replacing the second leg by the
    -- lifted isomorphism in `U`.
    let ep : (Δₚ P.snd).obj T.fst.fst ≅ T.fst :=
      CategoricalPullback.mkIso (Iso.refl _) eu.symm (by
        change
          P.snd.map (𝟙 T.fst.fst) ≫ T.fst.iso.hom =
            ((Δₚ P.snd).obj T.fst.fst).iso.hom ≫ P.snd.map eu.symm.hom
        simpa using heu_snd_inv.symm )
    refine ⟨T.fst.fst, ⟨?_⟩⟩
    -- The remaining `X`-component is exactly the first leg of `T.iso`, so together these two
    -- component isomorphisms identify `T` with a diagonal-comparison object.
    refine CategoricalPullback.mkIso ep e₁ ?_
    apply CategoricalPullback.hom_ext
    · simp [d, two_fibre_product_left_leg_diagonal_comparison,
        two_fibre_product_left_leg_right_vertical, e₁, ep, categorical_pullback_diagonal]
    · have hcomp := congrArg (fun k ↦ k ≫ T.iso.hom.snd) heu_fst_inv
      have hstep₁ :
          P.fst.map eu.inv ≫ T.iso.hom.snd =
            ((e₂ ≪≫ e₁.symm).symm).hom ≫ T.iso.hom.snd :=
        hcomp
      have hstep₂ :
          ((e₂ ≪≫ e₁.symm).symm).hom ≫ T.iso.hom.snd =
            T.iso.hom.fst ≫ T.iso.inv.snd ≫ T.iso.hom.snd := by
        simp [e₁, e₂, Category.assoc]
      have hstep₃ :
          T.iso.hom.fst ≫ T.iso.inv.snd ≫ T.iso.hom.snd = T.iso.hom.fst := by
        simpa [e₂, Category.assoc] using
          congrArg (fun k ↦ T.iso.hom.fst ≫ k) e₂.inv_hom_id
      have hstep₄ :
          ((d.obj T.fst.fst).iso.hom ≫ (Δₚ F).map e₁.hom).snd = T.iso.hom.fst := by
        simp [d, two_fibre_product_left_leg_diagonal_comparison,
          two_fibre_product_left_leg_right_vertical, e₁, categorical_pullback_diagonal]
      exact hstep₁.trans (hstep₂.trans (hstep₃.trans hstep₄.symm))
  exact
    { faithful := inferInstance
      full := inferInstance
      essSurj := inferInstance }

/-- For a square `U ⥤ V`, `U ⥤ X`, `V ⥤ Y`, `X ⥤ Y`, the induced square
`U ⥤ U ×[V] U`, `U ⥤ X`, `U ×[V] U ⥤ X ×[Y] X`, `X ⥤ X ×[Y] X`
viewed as the chapter's bicategorical square in `Cat`. -/
abbrev two_fibre_product_left_leg_diagonal_square
    (P : CatCommSqOver F G U) :
    BicategoricalTwoCommutativeSquare
      (two_fibre_product_left_leg_right_vertical P).toCatHom
      (Δₚ F).toCatHom :=
  (two_fibre_product_left_leg_diagonal_square_over P).toBicategoricalSquare

/-- Lemma 4.31.14: if `P` is a `2`-fibre product square over `F : X ⥤ Y` and `G : V ⥤ Y`, then
the induced square
`U ⥤ U ×[V] U`, `U ⥤ X`, `U ×[V] U ⥤ X ×[Y] X`, `X ⥤ X ×[Y] X`
is again a `2`-fibre product square. This is the source-facing main entry. -/
theorem two_fibre_product_left_leg_diagonal_isTwoFibreProduct
    (P : CatCommSqOver F G U)
    [Bicategory.IsFinal P.toBicategoricalSquare] :
    Bicategory.IsFinal (two_fibre_product_left_leg_diagonal_square P) := by
  -- Once the diagonal comparison functor is known to be an equivalence, the generic reverse
  -- bridge upgrades that comparison equivalence to finality of the induced square.
  let Q := two_fibre_product_left_leg_diagonal_square_over P
  change Bicategory.IsFinal Q.toBicategoricalSquare
  let hcomparison :
      (two_fibre_product_left_leg_diagonal_comparison P).IsEquivalence :=
    two_fibre_product_left_leg_diagonal_comparison_isEquivalence P
  exact
    isFinal_of_comparison_isEquivalence Q hcomparison

/-- Lemma 4.31.14, restated as the canonical `IsFinal` instance on the induced square. -/
noncomputable instance
    (P : CatCommSqOver F G U)
    [Bicategory.IsFinal P.toBicategoricalSquare] :
    Bicategory.IsFinal (two_fibre_product_left_leg_diagonal_square P) :=
  two_fibre_product_left_leg_diagonal_isTwoFibreProduct P

end

end CategoryTheory.Limits
