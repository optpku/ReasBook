module

public import Mathlib.CategoryTheory.Sites.Sheafification
public import Mathlib.CategoryTheory.Sites.Sheaf
public import stacks_project.Chap07.Lemma_7_25_9
public import stacks_project.Chap07.Lemma_7_28_6

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Opposite
open CategoryTheory.Limits
open CategoryTheory.GrothendieckTopology
open scoped SheafifiedRepresentable

universe u v w

noncomputable section

section

variable {C : Type u} [Category.{v} C]
variable (J : GrothendieckTopology C)
variable {U' U V' V : C}
variable (i : U' ⟶ U) (p : U' ⟶ V') (f : U ⟶ V) (g : V' ⟶ V)

/-
Domain-style sampling for Lemma 7.27.5:
- primary domain: relocalization for slice sites and the induced inverse-image and direct-image functors on
  sheaves;
- sampled owner API:
  `Over.mapComp_eq`,
  `GrothendieckTopology.overMapPullbackComp`,
  `GrothendieckTopology.overMapPullbackCongr`,
  `site_square_direct_image_inverse_image_iso`;
- source-facing layer: the commutative square and base-change statements for relocalization along a
  commutative square in `C`;
- core/canonical layer: the slice functors `Over.map _`, the localized inverse-image owner
  `J.overMapPullback _ _`, and the site-square Beck-Chevalley owner
  `site_square_direct_image_inverse_image_iso`;
- bridge/view layer: clause `(1)` should be organized around the functor-square owner
  `CatCommSq`, with the strict slice-functor equality only as a companion; clauses `(2)` and `(3)`
  are the canonical comparison isomorphisms specialized from those owners rather than any
  strictified local copies.

Primitive data are just the commutative square `i ≫ f = p ≫ g` and, for the base-change part, the
cartesian hypothesis. The source-facing owner for clause `(1)` is the induced `CatCommSq` on slice
functors, while the strict equality of composites is a derived companion. The sheaf-level
comparisons are derived API and should remain at the canonical isomorphism level owned upstream.
-/

/-- The two composites of slice relocalization functors agree for a commutative square. -/
-- Proof sketch: use `Over.mapComp_eq` to identify each composite with the relocalization functor
-- attached to the composite morphism, then rewrite along `hcomm`.
theorem over_map_square_eq
    (hcomm : i ≫ f = p ≫ g) :
    Over.map i ⋙ Over.map f = Over.map p ⋙ Over.map g := by
  -- Normalize both composites to the relocalization functor of the corresponding composite.
  rw [← Over.mapComp_eq, ← Over.mapComp_eq]
  -- The commutative square identifies the two composite arrows.
  simp [hcomm]

/-! The file keeps the three clauses of Lemma 7.27.5 as separate atomic declarations. -/

/-- First assertion of Lemma 7.27.5: the relocalization functors attached to a commutative square
`U' ⟶ U ⟶ V` and `U' ⟶ V' ⟶ V` form a commutative square of continuous and cocontinuous functors
between the localized sites. -/
abbrev relocalization_over_map_square
    (hcomm : i ≫ f = p ≫ g) :
    CatCommSq (Over.map i) (Over.map p) (Over.map f) (Over.map g) where
  iso := eqToIso (over_map_square_eq i p f g hcomm)

/-- Equality form of Lemma 7.27.5 (1), derived from the canonical `CatCommSq` owner. -/
theorem relocalization_over_map_square_eq
    (hcomm : i ≫ f = p ≫ g) :
    Over.map i ⋙ Over.map f = Over.map p ⋙ Over.map g :=
  over_map_square_eq i p f g hcomm

/-- Helper for Lemma 7.27.5: the square isomorphism on over-map functors is identity on
underlying slice objects. -/
theorem relocalization_over_map_square_iso_hom_app_left
    (hcomm : i ≫ f = p ≫ g) (X : Over U') :
    ((relocalization_over_map_square i p f g hcomm).iso.hom.app X).left = 𝟙 X.left := by
  -- The owner square was built from an equality of `Over.map` composites, whose components are
  -- identity maps on the slice source objects.
  change ((eqToIso (over_map_square_eq i p f g hcomm)).hom.app X).left = 𝟙 X.left
  simp

/-- Helper for Lemma 7.27.5: a cartesian square of base objects gives a Guitart-exact square
of slice relocalization functors. -/
theorem relocalization_over_map_square_guitartExact
    (hcart : IsPullback i p f g) :
    TwoSquare.GuitartExact (relocalization_over_map_square i p f g hcart.w).iso.hom := by
  -- It is enough to connect each structured-arrow category over an object of the target comma
  -- category; the cartesian lift gives a canonical central object.
  rw [TwoSquare.guitartExact_iff_isConnected_rightwards]
  intro X A α
  let hsquare : CatCommSq (Over.map i) (Over.map p) (Over.map f) (Over.map g) :=
    relocalization_over_map_square i p f g hcart.w
  let sq := hsquare.iso.hom
  let hα : X.hom ≫ f = (α.left ≫ A.hom) ≫ g := by
    simpa [Category.assoc] using α.w.symm
  let Y : Over U' := Over.mk (hcart.lift X.hom (α.left ≫ A.hom) hα)
  let a : X ⟶ (Over.map i).obj Y := Over.homMk (𝟙 X.left) (by
    dsimp [Y]
    simpa [Category.assoc] using (hcart.lift_fst X.hom (α.left ≫ A.hom) hα))
  let b : (Over.map p).obj Y ⟶ A := Over.homMk α.left (by
    dsimp [Y]
    simpa [Category.assoc] using (hcart.lift_snd X.hom (α.left ≫ A.hom) hα).symm)
  let P : TwoSquare.StructuredArrowRightwards sq α :=
    TwoSquare.StructuredArrowRightwards.mk sq α Y a b (by
      ext
      have hsq_left : (sq.app Y).left = 𝟙 Y.left := by
        simpa [sq] using
          (relocalization_over_map_square_iso_hom_app_left
            (i := i) (p := p) (f := f) (g := g) hcart.w Y)
      simp only [Over.map_obj_left, Functor.comp_obj, Over.comp_left, Over.map_map_left,
        hsq_left]
      rw [show a.left = 𝟙 X.left by rfl, show b.left = α.left by rfl]
      simp [Y])
  have connect_mk (YQ : Over U') (aQ : X ⟶ (Over.map i).obj YQ)
      (bQ : (Over.map p).obj YQ ⟶ A)
      (hQ : (Over.map f).map aQ ≫ sq.app YQ ≫ (Over.map g).map bQ = α) :
      P ⟶ TwoSquare.StructuredArrowRightwards.mk sq α YQ aQ bQ hQ := by
    have hsq_leftQ : (sq.app YQ).left = 𝟙 YQ.left := by
      simpa [sq] using
        (relocalization_over_map_square_iso_hom_app_left
          (i := i) (p := p) (f := f) (g := g) hcart.w YQ)
    have hQ_left : aQ.left ≫ bQ.left = α.left := by
      simpa [Over.comp_left, Over.map_map_left, hsq_leftQ, Category.assoc] using
        congrArg (fun η ↦ η.left) hQ
    have hc_left : aQ.left ≫ YQ.hom = Y.hom := by
      apply hcart.hom_ext
      · have haQi : aQ.left ≫ (YQ.hom ≫ i) = X.hom := by
          simpa using aQ.w
        simpa [Category.assoc, Y] using
          haQi.trans (hcart.lift_fst X.hom (α.left ≫ A.hom) hα).symm
      · have hp : (aQ.left ≫ YQ.hom) ≫ p = α.left ≫ A.hom := by
          have hbQ : YQ.hom ≫ p = bQ.left ≫ A.hom := by
            simpa using bQ.w.symm
          have hassoc : (aQ.left ≫ YQ.hom) ≫ p = aQ.left ≫ (YQ.hom ≫ p) := by
            simp [Category.assoc]
          have hreplace :
              aQ.left ≫ (YQ.hom ≫ p) = aQ.left ≫ (bQ.left ≫ A.hom) :=
            congrArg (fun k ↦ aQ.left ≫ k) hbQ
          have htarget : aQ.left ≫ (bQ.left ≫ A.hom) = α.left ≫ A.hom := by
            simpa [Category.assoc] using congrArg (fun k ↦ k ≫ A.hom) hQ_left
          exact hassoc.trans (hreplace.trans htarget)
        exact by
          dsimp [Y]
          exact hp.trans (hcart.lift_snd X.hom (α.left ≫ A.hom) hα).symm
    let c : Y ⟶ YQ := Over.homMk aQ.left hc_left
    have hP_right_hom_left : P.right.hom.left = α.left := by
      simp [P, b]
    have hP_hom_left_left : P.hom.left.left = 𝟙 X.left := by
      simp [P, a]
    let d :
        P.right ⟶ (CostructuredArrow.mk bQ : CostructuredArrow (Over.map p) A) :=
      CostructuredArrow.homMk c (by
        ext
        rw [hP_right_hom_left]
        exact hQ_left)
    exact StructuredArrow.homMk d (by
      ext
      simp only [Functor.const_obj_obj, CostructuredArrow.mk_left, StructuredArrow.mk_right,
        TwoSquare.costructuredArrowRightwards_obj, CostructuredArrow.mk_hom_eq_self,
        CostructuredArrow.pre_obj_left, Comma.mapLeft_obj_left, Over.map_obj_left,
        TwoSquare.costructuredArrowRightwards_map, CostructuredArrow.comp_left,
        CostructuredArrow.pre_map_left, Comma.mapLeft_map_left, CostructuredArrow.homMk_left,
        Over.comp_left, Over.map_map_left, StructuredArrow.mk_hom_eq_self,
        hP_hom_left_left]
      exact Category.id_comp aQ.left)
  -- Every other object maps to the same cartesian lift, giving the connecting zigzags.
  have hnonempty : Nonempty (TwoSquare.StructuredArrowRightwards sq α) := ⟨P⟩
  change IsConnected (TwoSquare.StructuredArrowRightwards sq α)
  refine @zigzag_isConnected _ _ hnonempty ?_
  intro Q R
  obtain ⟨YQ, aQ, bQ, hQ, rfl⟩ := TwoSquare.StructuredArrowRightwards.mk_surjective Q
  obtain ⟨YR, aR, bR, hR, rfl⟩ := TwoSquare.StructuredArrowRightwards.mk_surjective R
  refine Zigzag.of_inv_hom (j₂ := P) ?_ ?_
  · exact connect_mk YQ aQ bQ hQ
  · exact connect_mk YR aR bR hR

/-- Helper for Lemma 7.27.5: the rightwards costructured-arrow functor for the cartesian
relocalization square is final. -/
theorem relocalization_over_map_square_costructuredArrowRightwards_final
    (hcart : IsPullback i p f g) (A : Over V') :
    (TwoSquare.costructuredArrowRightwards
      (relocalization_over_map_square i p f g hcart.w).iso.hom A).Final := by
  -- Convert the cartesian-square Guitart-exactness into the finality form needed by the generic
  -- site-square Beck-Chevalley comparison.
  exact (TwoSquare.guitartExact_iff_final
    (relocalization_over_map_square i p f g hcart.w).iso.hom).1
      (relocalization_over_map_square_guitartExact
        (i := i) (p := p) (f := f) (g := g) hcart) A

-- Proof sketch: compose the canonical owner isomorphisms
-- `J.overMapPullbackComp` for the two routes around the square and insert
-- `J.overMapPullbackCongr` for the equality `i ≫ f = p ≫ g`.
/-- Second assertion of Lemma 7.27.5: the commutative square of relocalization functors induces a commutative
square of localized topoi, expressed by the canonical comparison isomorphism of inverse-image
functors on sheaves. -/
noncomputable def relocalization_inverse_image_square_iso
    (hcomm : i ≫ f = p ≫ g) :
    J.overMapPullback (Type w) f ⋙ J.overMapPullback (Type w) i ≅
      J.overMapPullback (Type w) g ⋙ J.overMapPullback (Type w) p :=
  J.overMapPullbackComp (Type w) i f ≪≫
    J.overMapPullbackCongr (Type w) hcomm ≪≫
      (J.overMapPullbackComp (Type w) p g).symm

/-- Helper for Lemma 7.27.5: a cartesian square in `C` remains cartesian after applying the
sheafified-representable functor. -/
theorem sheafified_representable_square_isPullback
    (hcart : IsPullback i p f g) :
    IsPullback (J.sheafifiedRepresentableMap i) (J.sheafifiedRepresentableMap p)
      (J.sheafifiedRepresentableMap f) (J.sheafifiedRepresentableMap g) := by
  -- The sheafified-representable functor preserves pullbacks, so the source cartesian square
  -- transports directly to the sheaf topos.
  simpa [GrothendieckTopology.sheafifiedRepresentableMap,
    GrothendieckTopology.sheafifiedRepresentableFunctor,
    GrothendieckTopology.uliftSheafifiedRepresentableFunctor] using
    hcart.map (CategoryTheory.uliftYoneda.{max u v} ⋙
      presheafToSheaf J (Type (max u v)))

/-- Helper for Lemma 7.27.5: the left-hand base-change object is the canonical pullback over
`h[U]^#[J]`. -/
theorem sheafified_representable_base_change_source_isPullback
    (A : Over h[V']^#[J]) :
    IsPullback
      (pullback.snd (A.hom ≫ J.sheafifiedRepresentableMap g) (J.sheafifiedRepresentableMap f))
      (pullback.fst (A.hom ≫ J.sheafifiedRepresentableMap g) (J.sheafifiedRepresentableMap f))
      (J.sheafifiedRepresentableMap f)
      (A.hom ≫ J.sheafifiedRepresentableMap g) := by
  -- The source object is defined by the ordinary pullback in the ambient slice category.
  exact
    (IsPullback.of_hasPullback
      (A.hom ≫ J.sheafifiedRepresentableMap g) (J.sheafifiedRepresentableMap f)).flip

/-- Helper for Lemma 7.27.5: the right-hand base-change object is the pullback obtained by pasting
the cartesian square of sheafified representables with the canonical pullback over `h[V']^#[J]`. -/
theorem sheafified_representable_base_change_target_isPullback
    (hcart : IsPullback i p f g) (A : Over h[V']^#[J]) :
    IsPullback
      ((pullback.snd A.hom (J.sheafifiedRepresentableMap p)) ≫
        J.sheafifiedRepresentableMap i)
      (pullback.fst A.hom (J.sheafifiedRepresentableMap p))
      (J.sheafifiedRepresentableMap f)
      (A.hom ≫ J.sheafifiedRepresentableMap g) := by
  let hsheaf := sheafified_representable_square_isPullback (J := J) i p f g hcart
  -- Pasting with the sheafified cartesian square identifies the target object with the same
  -- ambient pullback cospan as the source object.
  exact
    (IsPullback.of_hasPullback A.hom (J.sheafifiedRepresentableMap p)).flip.paste_horiz hsheaf

/-- Helper for Lemma 7.27.5: objectwise, the two slice-level base-change constructions are
canonically isomorphic because they are pullbacks of the same cospan. -/
noncomputable def sheafified_representable_base_change_obj_iso
    (hcart : IsPullback i p f g) (A : Over h[V']^#[J]) :
    ((Over.map (J.sheafifiedRepresentableMap g) ⋙
          Over.pullback (J.sheafifiedRepresentableMap f)).obj A) ≅
      ((Over.pullback (J.sheafifiedRepresentableMap p) ⋙
          Over.map (J.sheafifiedRepresentableMap i)).obj A) := by
  let hleft :=
    sheafified_representable_base_change_source_isPullback (J := J) (f := f) (g := g) A
  let hright :=
    sheafified_representable_base_change_target_isPullback
      (J := J) (i := i) (p := p) (f := f) (g := g) hcart A
  let e :
      pullback (A.hom ≫ J.sheafifiedRepresentableMap g) (J.sheafifiedRepresentableMap f) ≅
        pullback A.hom (J.sheafifiedRepresentableMap p) :=
    hleft.flip.isoPullback ≪≫ (hright.flip.isoPullback).symm
  -- The slice-object isomorphism is just the ambient pullback isomorphism with the structure map
  -- compatibility recorded separately.
  exact Over.isoMk e <| by
    simp [e, Category.assoc]

/-- Helper for Lemma 7.27.5: the component isomorphism matches the second pullback projection. -/
theorem sheafified_representable_base_change_obj_iso_hom_comp_snd
    (hcart : IsPullback i p f g) (A : Over h[V']^#[J]) :
    (sheafified_representable_base_change_obj_iso
          (J := J) (i := i) (p := p) (f := f) (g := g) hcart A).hom.left ≫
        pullback.snd A.hom (J.sheafifiedRepresentableMap p) ≫
          J.sheafifiedRepresentableMap i =
      pullback.snd (A.hom ≫ J.sheafifiedRepresentableMap g)
        (J.sheafifiedRepresentableMap f) := by
  -- Unfolding the objectwise pullback comparison reveals the defining second-projection formula.
  simp [sheafified_representable_base_change_obj_iso, Category.assoc]

/-- Helper for Lemma 7.27.5: the component isomorphism matches the first pullback projection. -/
theorem sheafified_representable_base_change_obj_iso_hom_comp_fst
    (hcart : IsPullback i p f g) (A : Over h[V']^#[J]) :
    (sheafified_representable_base_change_obj_iso
          (J := J) (i := i) (p := p) (f := f) (g := g) hcart A).hom.left ≫
        pullback.fst A.hom (J.sheafifiedRepresentableMap p) =
      pullback.fst (A.hom ≫ J.sheafifiedRepresentableMap g)
        (J.sheafifiedRepresentableMap f) := by
  -- Unfolding the objectwise pullback comparison reveals the defining first-projection formula.
  simp [sheafified_representable_base_change_obj_iso, Category.assoc]

/-- Helper for Lemma 7.27.5: the objectwise pullback comparison is natural in the slice object over
`h[V']^#[J]`. -/
theorem sheafified_representable_base_change_obj_iso_naturality
    (hcart : IsPullback i p f g) {A B : Over h[V']^#[J]} (η : A ⟶ B) :
    ((Over.map (J.sheafifiedRepresentableMap g) ⋙
          Over.pullback (J.sheafifiedRepresentableMap f)).map η) ≫
        (sheafified_representable_base_change_obj_iso
          (J := J) (i := i) (p := p) (f := f) (g := g) hcart B).hom =
      (sheafified_representable_base_change_obj_iso
          (J := J) (i := i) (p := p) (f := f) (g := g) hcart A).hom ≫
    ((Over.pullback (J.sheafifiedRepresentableMap p) ⋙
            Over.map (J.sheafifiedRepresentableMap i)).map η) := by
  -- Reduce equality in the slice to equality of the underlying maps, then use the pasted
  -- pullback square on the target object to compare the two projections.
  apply Over.OverMorphism.ext
  apply (sheafified_representable_base_change_target_isPullback
    (J := J) (i := i) (p := p) (f := f) (g := g) hcart B).hom_ext
  · -- The second projection is transported through the component comparison and the pullback map.
    have hB :=
      sheafified_representable_base_change_obj_iso_hom_comp_snd
        (J := J) (i := i) (p := p) (f := f) (g := g) hcart B
    have hA :=
      sheafified_representable_base_change_obj_iso_hom_comp_snd
        (J := J) (i := i) (p := p) (f := f) (g := g) hcart A
    simp only [Over.comp_left, Functor.comp_map]
    have hleft :
        (((Over.pullback (J.sheafifiedRepresentableMap f)).map
                ((Over.map (J.sheafifiedRepresentableMap g)).map η)).left ≫
              (sheafified_representable_base_change_obj_iso
                (J := J) (i := i) (p := p) (f := f) (g := g) hcart B).hom.left) ≫
            pullback.snd B.hom (J.sheafifiedRepresentableMap p) ≫
              J.sheafifiedRepresentableMap i =
          pullback.snd (A.hom ≫ J.sheafifiedRepresentableMap g)
            (J.sheafifiedRepresentableMap f) := by
      calc
        (((Over.pullback (J.sheafifiedRepresentableMap f)).map
                ((Over.map (J.sheafifiedRepresentableMap g)).map η)).left ≫
              (sheafified_representable_base_change_obj_iso
                (J := J) (i := i) (p := p) (f := f) (g := g) hcart B).hom.left) ≫
            pullback.snd B.hom (J.sheafifiedRepresentableMap p) ≫
              J.sheafifiedRepresentableMap i =
          ((Over.pullback (J.sheafifiedRepresentableMap f)).map
                ((Over.map (J.sheafifiedRepresentableMap g)).map η)).left ≫
            pullback.snd (B.hom ≫ J.sheafifiedRepresentableMap g)
              (J.sheafifiedRepresentableMap f) := by
            simpa [Category.assoc] using
              congrArg
                (fun k ↦
                  (((Over.pullback (J.sheafifiedRepresentableMap f)).map
                      ((Over.map (J.sheafifiedRepresentableMap g)).map η)).left) ≫ k) hB
        _ =
          pullback.snd (A.hom ≫ J.sheafifiedRepresentableMap g)
            (J.sheafifiedRepresentableMap f) := by
            simp [Over.pullback_map_left, pullback.lift_snd]
    have hright :
        ((sheafified_representable_base_change_obj_iso
              (J := J) (i := i) (p := p) (f := f) (g := g) hcart A).hom.left ≫
            ((Over.map (J.sheafifiedRepresentableMap i)).map
              ((Over.pullback (J.sheafifiedRepresentableMap p)).map η)).left) ≫
          pullback.snd B.hom (J.sheafifiedRepresentableMap p) ≫
            J.sheafifiedRepresentableMap i =
          pullback.snd (A.hom ≫ J.sheafifiedRepresentableMap g)
            (J.sheafifiedRepresentableMap f) := by
      have hη :
          ((Over.map (J.sheafifiedRepresentableMap i)).map
                ((Over.pullback (J.sheafifiedRepresentableMap p)).map η)).left ≫
              pullback.snd B.hom (J.sheafifiedRepresentableMap p) =
            pullback.snd A.hom (J.sheafifiedRepresentableMap p) := by
        simpa [Over.pullback_map_left, pullback.lift_snd]
      have hproj :
          ((sheafified_representable_base_change_obj_iso
                (J := J) (i := i) (p := p) (f := f) (g := g) hcart A).hom.left ≫
              ((Over.map (J.sheafifiedRepresentableMap i)).map
                ((Over.pullback (J.sheafifiedRepresentableMap p)).map η)).left) ≫
            pullback.snd B.hom (J.sheafifiedRepresentableMap p) ≫
              J.sheafifiedRepresentableMap i =
            (sheafified_representable_base_change_obj_iso
                  (J := J) (i := i) (p := p) (f := f) (g := g) hcart A).hom.left ≫
              pullback.snd A.hom (J.sheafifiedRepresentableMap p) ≫
                J.sheafifiedRepresentableMap i := by
        simpa [Category.assoc] using
          congrArg
            (fun k ↦
              (sheafified_representable_base_change_obj_iso
                  (J := J) (i := i) (p := p) (f := f) (g := g) hcart A).hom.left ≫
                k ≫ J.sheafifiedRepresentableMap i) hη
      exact hproj.trans (by simpa [Category.assoc] using hA)
    exact hleft.trans hright.symm
  · -- The first projection is handled in the same way, using `pullback.lift_fst`.
    have hB :=
      sheafified_representable_base_change_obj_iso_hom_comp_fst
        (J := J) (i := i) (p := p) (f := f) (g := g) hcart B
    have hA :=
      sheafified_representable_base_change_obj_iso_hom_comp_fst
        (J := J) (i := i) (p := p) (f := f) (g := g) hcart A
    simp only [Over.comp_left, Functor.comp_map]
    have hleft :
        (((Over.pullback (J.sheafifiedRepresentableMap f)).map
                ((Over.map (J.sheafifiedRepresentableMap g)).map η)).left ≫
              (sheafified_representable_base_change_obj_iso
                (J := J) (i := i) (p := p) (f := f) (g := g) hcart B).hom.left) ≫
            pullback.fst B.hom (J.sheafifiedRepresentableMap p) =
          pullback.fst (A.hom ≫ J.sheafifiedRepresentableMap g)
              (J.sheafifiedRepresentableMap f) ≫ η.left := by
      calc
        (((Over.pullback (J.sheafifiedRepresentableMap f)).map
                ((Over.map (J.sheafifiedRepresentableMap g)).map η)).left ≫
              (sheafified_representable_base_change_obj_iso
                (J := J) (i := i) (p := p) (f := f) (g := g) hcart B).hom.left) ≫
            pullback.fst B.hom (J.sheafifiedRepresentableMap p) =
          ((Over.pullback (J.sheafifiedRepresentableMap f)).map
                ((Over.map (J.sheafifiedRepresentableMap g)).map η)).left ≫
            pullback.fst (B.hom ≫ J.sheafifiedRepresentableMap g)
              (J.sheafifiedRepresentableMap f) := by
            simpa [Category.assoc] using
              congrArg
                (fun k ↦
                  (((Over.pullback (J.sheafifiedRepresentableMap f)).map
                      ((Over.map (J.sheafifiedRepresentableMap g)).map η)).left) ≫ k) hB
        _ =
          pullback.fst (A.hom ≫ J.sheafifiedRepresentableMap g)
              (J.sheafifiedRepresentableMap f) ≫ η.left := by
            simp [Over.pullback_map_left, pullback.lift_fst]
    have hright :
        ((sheafified_representable_base_change_obj_iso
              (J := J) (i := i) (p := p) (f := f) (g := g) hcart A).hom.left ≫
            ((Over.map (J.sheafifiedRepresentableMap i)).map
              ((Over.pullback (J.sheafifiedRepresentableMap p)).map η)).left) ≫
          pullback.fst B.hom (J.sheafifiedRepresentableMap p) =
          pullback.fst (A.hom ≫ J.sheafifiedRepresentableMap g)
              (J.sheafifiedRepresentableMap f) ≫ η.left := by
      have hη :
          ((Over.map (J.sheafifiedRepresentableMap i)).map
                ((Over.pullback (J.sheafifiedRepresentableMap p)).map η)).left ≫
              pullback.fst B.hom (J.sheafifiedRepresentableMap p) =
            pullback.fst A.hom (J.sheafifiedRepresentableMap p) ≫ η.left := by
        simp [Over.pullback_map_left, pullback.lift_fst]
      have hproj :
          ((sheafified_representable_base_change_obj_iso
                (J := J) (i := i) (p := p) (f := f) (g := g) hcart A).hom.left ≫
              ((Over.map (J.sheafifiedRepresentableMap i)).map
                ((Over.pullback (J.sheafifiedRepresentableMap p)).map η)).left) ≫
            pullback.fst B.hom (J.sheafifiedRepresentableMap p) =
            (sheafified_representable_base_change_obj_iso
                  (J := J) (i := i) (p := p) (f := f) (g := g) hcart A).hom.left ≫
              pullback.fst A.hom (J.sheafifiedRepresentableMap p) ≫ η.left := by
        simpa [Category.assoc] using
          congrArg
            (fun k ↦
              (sheafified_representable_base_change_obj_iso
                  (J := J) (i := i) (p := p) (f := f) (g := g) hcart A).hom.left ≫ k) hη
      exact hproj.trans (by
        simpa [Category.assoc] using congrArg (fun k ↦ k ≫ η.left) hA)
    exact hleft.trans hright.symm

/-- Helper for Lemma 7.27.5: the pullback square of sheafified representables induces the usual
base-change isomorphism between slice postcomposition and pullback functors. -/
noncomputable def sheafified_representable_base_change_iso
    (hcart : IsPullback i p f g) :
    Over.map (J.sheafifiedRepresentableMap g) ⋙
        Over.pullback (J.sheafifiedRepresentableMap f) ≅
      Over.pullback (J.sheafifiedRepresentableMap p) ⋙
        Over.map (J.sheafifiedRepresentableMap i) :=
  NatIso.ofComponents
    (fun A ↦ sheafified_representable_base_change_obj_iso
      (J := J) (i := i) (p := p) (f := f) (g := g) hcart A)
    (fun η ↦ sheafified_representable_base_change_obj_iso_naturality
      (J := J) (i := i) (p := p) (f := f) (g := g) hcart η)

/-- Lemma 7.27.5: if the square
`U' ⟶ U ⟶ V` and `U' ⟶ V' ⟶ V` is cartesian, then inverse image along `V' ⟶ V` commutes with
direct image along `U ⟶ V` after relocalization via the canonical Beck-Chevalley comparison
isomorphism. -/
noncomputable def relocalization_pushforward_inverse_image_iso
    (hcart : IsPullback i p f g)
    [HasWeakSheafify (J.over U') (Type w)]
    [HasWeakSheafify (J.over U) (Type w)]
    [∀ F : (Over U)ᵒᵖ ⥤ Type w, (Over.map f).op.HasPointwiseRightKanExtension F]
    [∀ F : (Over U')ᵒᵖ ⥤ Type w, (Over.map p).op.HasPointwiseRightKanExtension F] :
    (Over.map f).sheafPushforwardCocontinuous (Type w) (J.over U) (J.over V) ⋙
        J.overMapPullback (Type w) g ≅
      J.overMapPullback (Type w) i ⋙
        (Over.map p).sheafPushforwardCocontinuous (Type w) (J.over U') (J.over V') :=
  -- The cartesian square of slice relocalization functors is Guitart-exact, so the generic
  -- site-level Beck-Chevalley theorem gives the desired direct-image/inverse-image comparison.
  (site_square_direct_image_inverse_image_iso
      (J.over U') (J.over U) (J.over V') (J.over V)
      (relocalization_over_map_square i p f g hcart.w)
      (fun A ↦ relocalization_over_map_square_costructuredArrowRightwards_final
        (i := i) (p := p) (f := f) (g := g) hcart A)).symm

-- Proof sketch: expand `relocalization_inverse_image_square_iso` as a composite of canonical
-- isomorphisms and use the triangle identities for isomorphisms.
/-- The forward and inverse comparison morphisms of
`relocalization_inverse_image_square_iso` compose to the identity. -/
theorem relocalization_inverse_image_square_iso_hom_inv_id
    (hcomm : i ≫ f = p ≫ g) :
    (relocalization_inverse_image_square_iso J i p f g hcomm).hom ≫
        (relocalization_inverse_image_square_iso J i p f g hcomm).inv =
      𝟙 _ := by
  -- This is the defining `Iso.hom_inv_id` identity for the comparison isomorphism.
  exact (relocalization_inverse_image_square_iso J i p f g hcomm).hom_inv_id

-- Proof sketch: any isomorphism satisfies `hom ≫ inv = 𝟙`; apply this to
-- `relocalization_pushforward_inverse_image_iso`.
/-- The forward and inverse comparison morphisms of
`relocalization_pushforward_inverse_image_iso` compose to the identity. -/
theorem relocalization_pushforward_inverse_image_iso_hom_inv_id
    (hcart : IsPullback i p f g)
    [HasWeakSheafify (J.over U') (Type w)]
    [HasWeakSheafify (J.over U) (Type w)]
    [∀ F : (Over U)ᵒᵖ ⥤ Type w, (Over.map f).op.HasPointwiseRightKanExtension F]
    [∀ F : (Over U')ᵒᵖ ⥤ Type w, (Over.map p).op.HasPointwiseRightKanExtension F] :
    (relocalization_pushforward_inverse_image_iso J i p f g hcart).hom ≫
        (relocalization_pushforward_inverse_image_iso J i p f g hcart).inv =
      𝟙 _ := by
  -- This is the defining `Iso.hom_inv_id` identity for the Beck-Chevalley comparison.
  exact (relocalization_pushforward_inverse_image_iso J i p f g hcart).hom_inv_id

end
