module

public import stacks_project.Chap04.Lemma_4_32_5
public import stacks_project.Chap04.Definition_4_35_1
public import stacks_project.Chap04.Definition_4_35_6
public import stacks_project.Chap04.Lemma_4_35_14
public import stacks_project.Chap04.Lemma_4_35_7
public import stacks_project.Chap04.Lemma_4_35_9

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

universe u v uX uY

namespace CategoryTheory

open CategoryOver

variable {C : Type u} [Category.{v} C]
variable {X : BasedCategory.{v, uX} C}
variable {Y : BasedCategory.{v, uY} C}

/- Domain-style sampling for Lemma 4.35.16:
- primary domain: factorization of a morphism of categories fibred in groupoids through the
  explicit `2`-fibre product with the identity of the target;
- sampled owner-level declarations:
  `FibredInGroupoidsOver.twoFibreProduct`,
  `explicitTwoFibreProduct`,
  `explicitTwoFibreProductRightProjection`,
  `ExplicitTwoFibreProductHom.ext`,
  `BasedFunctor.IsEquivalenceOverBase.mkPrime`;
- best owner abstraction: the source-facing factorization object is the explicit `2`-fibre
  product specialized to `(F, id Y)` because that specialization is definable without fibredness
  assumptions and is stable across the heterogeneous universes of `X` and `Y`; the fibred-in-
  groupoids closure should therefore reuse the existing explicit-pullback theorem directly rather
  than rebuilding a parallel bundled owner specialization inside this file.

Primitive-vs-derived split:
- primitive data: only the based functor `F : X ⥤ᵇ Y`;
- derived API: the factorization object `X ×_{F,Y,\mathrm{id}} Y`, the canonical source map
  `x ↦ (x, F(x), 𝟙)`, the target projection, the fibred-in-groupoids specialization of the
  pullback projection theorem, and the equivalence-over-base upgrade from the underlying
  categorical equivalence.

Source/core/bridge triage:
- `source-facing`: `fibredInGroupoidsFactorizationFromSource` and the numbered specializations in
  Lemma 4.35.16;
- `core/canonical`: `explicitTwoFibreProduct`, `explicitTwoFibreProductRightProjection`,
  `explicitTwoFibreProductProjection_isFibredInGroupoids`, and
  `BasedFunctor.IsEquivalenceOverBase`;
- `bridge/view`: the specialization of the generic explicit `2`-fibre product to `(F, id Y)`,
  together with the left-projection quasi-inverse data used in the over-base equivalence proof. -/

/-- The textbook factorization object `X' = X ×_{F,Y,\mathrm{id}} Y`, realized by the canonical
explicit `2`-fibre-product model from Lemma 4.35.7. -/
abbrev fibredInGroupoidsFactorization
    (F : X ⥤ᵇ Y) :
    BasedCategory C :=
  explicitTwoFibreProduct F (BasedFunctor.id Y)

-- Proof sketch: for each `x : X`, the comma object `(x, F(x), 𝟙_{F(x)})` has invertible
-- comparison arrow lying over the identity of `X.p.obj x`, so it belongs to the defining full
-- subcategory of the explicit `2`-fibre-product model.
/-- The canonical object `(x, F(x), id)` in the explicit factorization. -/
abbrev fibredInGroupoidsFactorizationFromSourceObj
    (F : X ⥤ᵇ Y) (x : X.obj) :
    (fibredInGroupoidsFactorization F).obj :=
  { U := X.p.obj x
    obj :=
      { fst := ⟨x, rfl⟩
        snd := ⟨F.obj x, F.w_obj x⟩
        iso := Iso.refl _ } }

/-- The morphism of source objects induced by a morphism in `X`. -/
def fibredInGroupoidsFactorizationFromSourceMap
    (F : X ⥤ᵇ Y) {x x' : X.obj} (a : x ⟶ x') :
    fibredInGroupoidsFactorizationFromSourceObj F x ⟶
      fibredInGroupoidsFactorizationFromSourceObj F x' where
  base := X.p.map a
  a := a
  a_over := by infer_instance
  b := F.map a
  b_over := by infer_instance
  comm := by
    change CommSq (F.map a) (𝟙 (F.obj x)) (𝟙 (F.obj x')) (F.map a)
    simp

/-- The source functor into the explicit factorization satisfies the identity law. -/
theorem fibredInGroupoidsFactorizationFromSource_map_id
    (F : X ⥤ᵇ Y) (x : X.obj) :
    fibredInGroupoidsFactorizationFromSourceMap F (𝟙 x) =
      𝟙 (fibredInGroupoidsFactorizationFromSourceObj F x) := by
  apply ExplicitTwoFibreProductHom.ext
  · rfl
  · have hb :
        (((𝟙 (fibredInGroupoidsFactorizationFromSourceObj F x)) :
            fibredInGroupoidsFactorizationFromSourceObj F x ⟶
              fibredInGroupoidsFactorizationFromSourceObj F x)).b =
          𝟙 (F.obj x) := rfl
    have hmap := F.toFunctor.map_id x
    dsimp [fibredInGroupoidsFactorizationFromSourceMap] at hmap ⊢
    simp [hb] at hmap ⊢

-- Proof sketch: the left component is `a ≫ b` and the right component is `F.map (a ≫ b)`, which
-- agrees with `F.map a ≫ F.map b` by functoriality of `F`.
/-- The source functor into the explicit factorization satisfies the composition law. -/
theorem fibredInGroupoidsFactorizationFromSource_map_comp
    (F : X ⥤ᵇ Y) {x y z : X.obj} (a : x ⟶ y) (b : y ⟶ z) :
    fibredInGroupoidsFactorizationFromSourceMap F (a ≫ b) =
      fibredInGroupoidsFactorizationFromSourceMap F a ≫
        fibredInGroupoidsFactorizationFromSourceMap F b := by
  apply ExplicitTwoFibreProductHom.ext
  · rfl
  · change F.map (a ≫ b) = F.map a ≫ F.map b
    simp

def fibredInGroupoidsFactorizationFromSourceFunctor
    (F : X ⥤ᵇ Y) :
    X.obj ⥤ (fibredInGroupoidsFactorization F).obj where
  obj := fibredInGroupoidsFactorizationFromSourceObj F
  map := fun a ↦ fibredInGroupoidsFactorizationFromSourceMap F a
  map_id := fibredInGroupoidsFactorizationFromSource_map_id F
  map_comp := fun a b ↦ fibredInGroupoidsFactorizationFromSource_map_comp F a b

theorem fibredInGroupoidsFactorizationFromSourceFunctor_comm
    (F : X ⥤ᵇ Y) :
    fibredInGroupoidsFactorizationFromSourceFunctor F ⋙
        (fibredInGroupoidsFactorization F).p =
      X.p := by
  rfl

/-- The canonical map `X ⟶ X'` given by `x ↦ (x, F(x), id)`. -/
abbrev fibredInGroupoidsFactorizationFromSource
    (F : X ⥤ᵇ Y) :
    X ⥤ᵇ fibredInGroupoidsFactorization F :=
  { toFunctor :=
      fibredInGroupoidsFactorizationFromSourceFunctor F
    w := fibredInGroupoidsFactorizationFromSourceFunctor_comm F }

/-- The projection `X' ⟶ Y` from the explicit factorization, forgetting the `X`-component. -/
abbrev fibredInGroupoidsFactorizationToTarget
    (F : X ⥤ᵇ Y) :
    fibredInGroupoidsFactorization F ⥤ᵇ Y :=
  explicitTwoFibreProductRightProjection F (BasedFunctor.id Y)

section

variable [IsFibredInGroupoids X.p] [IsFibredInGroupoids Y.p]

/-- Helper for Lemma 4.35.16: the categorical pullback of two groupoids is a groupoid. -/
private theorem fibredInGroupoidsFactorization_categorical_pullback_isGroupoid
    {A B T : Type*} [Category A] [Category B] [Category T]
    (L : A ⥤ T) (R : B ⥤ T) [IsGroupoid A] [IsGroupoid B] :
    IsGroupoid (Limits.CategoricalPullback L R) where
  all_isIso := fun f ↦
    (Limits.CategoricalPullback.isIso_iff (F := L) (G := R) f).2
      ⟨inferInstance, inferInstance⟩

end

-- Proof sketch: the quasi-inverse is the left projection `(x, y, f) ↦ x`, and the only
-- nontrivial coherence is the counit whose component is the stored comparison isomorphism.
/-- Helper for Lemma 4.35.16: the left projection from the explicit factorization to `X`. -/
private abbrev fibredInGroupoidsFactorizationLeftProjection
    (F : X ⥤ᵇ Y) :
    fibredInGroupoidsFactorization F ⥤ᵇ X :=
  explicitTwoFibreProductLeftProjection F (BasedFunctor.id Y)

/-- Helper for Lemma 4.35.16: the base projection of a morphism in the explicit factorization is
its stored `base` field. -/
private theorem fibredInGroupoidsFactorization_base_projection_map
    (F : X ⥤ᵇ Y)
    {P Q : (fibredInGroupoidsFactorization F).obj} (φ : P ⟶ Q) :
    (fibredInGroupoidsFactorization F).p.map φ = φ.base := by
  rfl

/-- Helper for Lemma 4.35.16: the counit isomorphism from the left projection followed by the
canonical source map to the identity on the explicit factorization. -/
private noncomputable def fibredInGroupoidsFactorization_counit_component_iso
    (F : X ⥤ᵇ Y) (P : (fibredInGroupoidsFactorization F).obj) :
    fibredInGroupoidsFactorizationFromSourceObj F P.obj.fst.1 ≅ P := by
  -- The source comparison object maps to `P` by the stored comparison arrow `P.comparison`.
  refine
    { hom :=
        { base := eqToHom P.obj.fst.2
          a := 𝟙 P.obj.fst.1
          a_over := by
            refine IsHomLift.of_fac' X.p (eqToHom P.obj.fst.2) (𝟙 P.obj.fst.1) rfl P.obj.fst.2 ?_
            simp
          b := P.comparison
          b_over := by
            have hcomparison : Y.p.IsHomLift (𝟙 P.U) P.comparison := P.comparison_over
            letI : Y.p.IsHomLift (𝟙 P.U) P.comparison := hcomparison
            refine
              IsHomLift.of_fac' Y.p (eqToHom P.obj.fst.2) P.comparison
                (F.w_obj P.obj.fst.1) P.obj.snd.2 ?_
            simpa [Category.assoc] using IsHomLift.fac' Y.p (𝟙 P.U) P.comparison
          comm := ?_ }
      inv :=
        { base := eqToHom P.obj.fst.2.symm
          a := 𝟙 P.obj.fst.1
          a_over := by
            refine
              IsHomLift.of_fac' X.p (eqToHom P.obj.fst.2.symm) (𝟙 P.obj.fst.1)
                P.obj.fst.2 rfl ?_
            simp
          b := P.obj.iso.inv.1
          b_over := by
            have hinv : Y.p.IsHomLift (𝟙 P.U) P.obj.iso.inv.1 := P.obj.iso.inv.2
            letI : Y.p.IsHomLift (𝟙 P.U) P.obj.iso.inv.1 := hinv
            refine
              IsHomLift.of_fac' Y.p (eqToHom P.obj.fst.2.symm) P.obj.iso.inv.1
                P.obj.snd.2 (F.w_obj P.obj.fst.1) ?_
            have hfac :
                Y.p.map P.obj.iso.inv.1 =
                  eqToHom P.obj.snd.2 ≫ 𝟙 P.U ≫
                    eqToHom ((F.w_obj P.obj.fst.1).trans P.obj.fst.2).symm := by
              simpa using IsHomLift.fac' Y.p (𝟙 P.U) P.obj.iso.inv.1
            simpa [Category.assoc] using hfac
          comm := ?_ }
      hom_inv_id := ?_
      inv_hom_id := ?_ }
  · -- The forward square is the defining comparison square of `P`.
    change CommSq (F.map (𝟙 P.obj.fst.1)) (𝟙 (F.obj P.obj.fst.1)) P.comparison P.comparison
    refine ⟨?_⟩
    simp
  · -- The inverse square uses the inverse of the stored comparison isomorphism.
    change CommSq (F.map (𝟙 P.obj.fst.1)) P.comparison (𝟙 (F.obj P.obj.fst.1)) P.obj.iso.inv.1
    refine ⟨?_⟩
    calc
      F.map (𝟙 P.obj.fst.1) ≫ 𝟙 (F.obj P.obj.fst.1) = 𝟙 (F.obj P.obj.fst.1) := by simp
      _ = P.comparison ≫ P.obj.iso.inv.1 := by
            exact (congrArg (fun f ↦ f.1) P.obj.iso.hom_inv_id).symm
  · -- Route correction: compare the two composites componentwise in the explicit pullback model.
    apply ExplicitTwoFibreProductHom.ext
    · change 𝟙 P.obj.fst.1 ≫ 𝟙 P.obj.fst.1 = 𝟙 P.obj.fst.1
      simp
    · change P.comparison ≫ P.obj.iso.inv.1 = 𝟙 ((F.fiberFunctor P.U).obj P.obj.fst).1
      exact congrArg (fun f ↦ f.1) P.obj.iso.hom_inv_id
  · -- The opposite composite is checked in the same way.
    apply ExplicitTwoFibreProductHom.ext
    · change 𝟙 P.obj.fst.1 ≫ 𝟙 P.obj.fst.1 = 𝟙 P.obj.fst.1
      simp
    · change P.obj.iso.inv.1 ≫ P.comparison = 𝟙 P.obj.snd.1
      exact congrArg (fun f ↦ f.1) P.obj.iso.inv_hom_id

/-- Helper for Lemma 4.35.16: the counit comparison is the stored objectwise pullback
isomorphism. -/
private noncomputable def fibredInGroupoidsFactorizationLeftProjection_counitIso
    (F : X ⥤ᵇ Y) :
    BasedFunctor.comp
        (fibredInGroupoidsFactorizationLeftProjection F)
        (fibredInGroupoidsFactorizationFromSource F) ≅
      𝟙 (fibredInGroupoidsFactorization F) := by
  -- Package the textbook component `(𝟙_x, f)` into a based natural isomorphism.
  refine BasedNatIso.mkNatIso ?_ ?_
  · refine NatIso.ofComponents
      (fun P ↦ fibredInGroupoidsFactorization_counit_component_iso F P) ?_
    intro P Q φ
    -- Naturality is the pullback compatibility square of `φ`.
    apply ExplicitTwoFibreProductHom.ext
    · change φ.a ≫ 𝟙 Q.obj.fst.1 = 𝟙 P.obj.fst.1 ≫ φ.a
      simp
    · change F.map φ.a ≫ Q.comparison = P.comparison ≫ φ.b
      exact φ.comm.w
  · intro P
    -- Each component is vertical over the base object of `P`.
    exact IsHomLift.of_fac' (fibredInGroupoidsFactorization F).p
      (𝟙 P.U)
      (fibredInGroupoidsFactorization_counit_component_iso F P).hom
      ((BasedFunctor.comp
          (fibredInGroupoidsFactorizationLeftProjection F)
          (fibredInGroupoidsFactorizationFromSource F)).w_obj P)
      rfl
      (by
        rw [fibredInGroupoidsFactorization_base_projection_map]
        simpa [fibredInGroupoidsFactorization_counit_component_iso] using
          (show
            eqToHom P.obj.fst.2 =
              eqToHom
                ((BasedFunctor.comp
                    (fibredInGroupoidsFactorizationLeftProjection F)
                    (fibredInGroupoidsFactorizationFromSource F)).w_obj P) by
            rfl))

-- Proof sketch: the unit is definitional, while the counit is the comparison isomorphism
-- packaged above.
/-- Helper for Lemma 4.35.16: the source map into the factorization is an equivalence over `C`. -/
private theorem fibredInGroupoidsFactorizationFromSource_isEquivalenceOverBase_aux
    (F : X ⥤ᵇ Y) :
    (fibredInGroupoidsFactorizationFromSource F).IsEquivalenceOverBase := by
  -- The left projection is the based quasi-inverse from the textbook construction.
  refine BasedFunctor.IsEquivalenceOverBase.mkPrime
    (fibredInGroupoidsFactorizationLeftProjection F) ?_ ?_
  · -- The source map followed by the left projection is literally the identity on `X`.
    exact eqToIso rfl
  · -- The counit is induced by the stored comparison isomorphism of the pullback object.
    exact fibredInGroupoidsFactorizationLeftProjection_counitIso F

-- Proof sketch: specialize the explicit `2`-fibre-product owner to `(F, 𝟭 Y)` and use the left
-- projection `(x, y, f) ↦ x` as a based quasi-inverse. The unit is the tautological identity on
-- `X`, while the counit at `(x, y, f)` is induced by the stored comparison isomorphism
-- `f : F(x) ≅ y`, so no fibred-in-groupoids hypotheses on `X` or `Y` are needed.
/-- Lemma 4.35.16 (2): the canonical map `X ⟶ X'` is an equivalence over the base category `C`. -/
theorem fibredInGroupoidsFactorizationFromSource_isEquivalenceOverBase
    (F : X ⥤ᵇ Y) :
    (fibredInGroupoidsFactorizationFromSource F).IsEquivalenceOverBase := by
  -- Reuse the packaged quasi-inverse and counit helper above.
  exact fibredInGroupoidsFactorizationFromSource_isEquivalenceOverBase_aux F

-- Proof sketch: the canonical map `X ⟶ X ×_{F,Y,\mathrm{id}} Y` is an equivalence of categories,
-- with quasi-inverse given by the left projection of the explicit `2`-fibre product.
/-- The canonical comparison `X ⟶ X'` is an equivalence of categories. -/
theorem fibredInGroupoidsFactorizationFromSource_isEquivalence
    (F : X ⥤ᵇ Y) :
    (fibredInGroupoidsFactorizationFromSource F).IsEquivalence := by
  -- Forgetting the base data turns an equivalence over `C` into an ordinary equivalence.
  exact BasedFunctor.isEquivalence_of_isEquivalenceOverBase _ <|
    fibredInGroupoidsFactorizationFromSource_isEquivalenceOverBase F

-- Proof sketch: the target projection from the explicit `2`-fibre-product model is the right
-- projection `(x, y, f) ↦ y`; the textbook argument shows it satisfies the fibred-in-groupoids
-- lifting and uniqueness conditions over `Y`.
-- Proof sketch: forgetting the `Y`-component after inserting `(x, F(x), id)` recovers the
-- original functor `F` by construction.
/-- Lemma 4.35.16 (3): the explicit factorization maps compose to the original functor `F`. -/
theorem fibredInGroupoidsFactorization_comp
    (F : X ⥤ᵇ Y) :
    BasedFunctor.comp
        (fibredInGroupoidsFactorizationFromSource F)
        (fibredInGroupoidsFactorizationToTarget F) =
      F :=
  rfl

section

variable [IsFibredInGroupoids X.p] [IsFibredInGroupoids Y.p]

/-- Helper for Lemma 4.35.16: the stored comparison of an object in the explicit factorization is
an isomorphism in the total category of `Y`. -/
theorem fibredInGroupoidsFactorization_comparison_isIso
    (F : X ⥤ᵇ Y)
    (P : (fibredInGroupoidsFactorization F).obj) :
    IsIso P.comparison := by
  -- Forget the fiberwise isomorphism carried by `P` to the total category `Y`.
  let e : F.obj P.obj.fst.1 ≅ P.obj.snd.1 :=
    { hom := P.comparison
      inv := P.obj.iso.inv.1
      hom_inv_id := by
        exact congrArg Subtype.val P.obj.iso.hom_inv_id
      inv_hom_id := by
        exact congrArg Subtype.val P.obj.iso.inv_hom_id }
  exact ⟨e.inv, e.hom_inv_id, e.inv_hom_id⟩

/-- Helper for Lemma 4.35.16: the base arrow in `C` underlying a morphism in `Y` between two
objects in the image of the right projection. -/
private abbrev fibredInGroupoidsFactorizationToTarget_base
    (F : X ⥤ᵇ Y)
    {P Q : (fibredInGroupoidsFactorization F).obj}
    (g : (fibredInGroupoidsFactorizationToTarget F).toFunctor.obj P ⟶
      (fibredInGroupoidsFactorizationToTarget F).toFunctor.obj Q) :
    P.U ⟶ Q.U :=
  eqToHom ((fibredInGroupoidsFactorizationToTarget F).w_obj P).symm ≫
    Y.p.map g ≫
      eqToHom ((fibredInGroupoidsFactorizationToTarget F).w_obj Q)

/-- Helper for Lemma 4.35.16: the base arrow in `C` underlying a morphism in `Y` whose codomain
lies in the image of the right projection. -/
abbrev fibredInGroupoidsFactorizationToTarget_pullbackBase
    (F : X ⥤ᵇ Y)
    {P : (fibredInGroupoidsFactorization F).obj}
    {y' : Y.obj}
    (b : y' ⟶ (fibredInGroupoidsFactorizationToTarget F).toFunctor.obj P) :
    Y.p.obj y' ⟶ P.U :=
  Y.p.map b ≫ eqToHom ((fibredInGroupoidsFactorizationToTarget F).w_obj P)

/-- Helper for Lemma 4.35.16: the transported base arrow attached to a morphism in the image of
the right projection is indeed the base arrow that the morphism lifts in `Y`. -/
private theorem fibredInGroupoidsFactorizationToTarget_base_isHomLift
    (F : X ⥤ᵇ Y)
    {P Q : (fibredInGroupoidsFactorization F).obj}
    (g : (fibredInGroupoidsFactorizationToTarget F).toFunctor.obj P ⟶
      (fibredInGroupoidsFactorizationToTarget F).toFunctor.obj Q) :
    Y.p.IsHomLift (fibredInGroupoidsFactorizationToTarget_base F g) g := by
  -- Normalize first the codomain transport coming from `Q`, then the domain transport from `P`.
  have hg' :
      Y.p.IsHomLift
        (Y.p.map g ≫ eqToHom ((fibredInGroupoidsFactorizationToTarget F).w_obj Q)) g := by
    simpa using
      (IsHomLift.lift_comp_eqToHom_iff
        Y.p
        (Y.p.map g)
        g
        ((fibredInGroupoidsFactorizationToTarget F).w_obj Q)).2
        (show Y.p.IsHomLift (Y.p.map g) g from inferInstance)
  simpa [fibredInGroupoidsFactorizationToTarget_base, Category.assoc] using
    (IsHomLift.lift_eqToHom_comp_iff
      Y.p
      (Y.p.map g ≫ eqToHom ((fibredInGroupoidsFactorizationToTarget F).w_obj Q))
      g
      ((fibredInGroupoidsFactorizationToTarget F).w_obj P).symm).2
      hg'

/-- Helper for Lemma 4.35.16: transporting the base of a composite in `Y` through the right
projection agrees with composing the transported base arrows in `C`. -/
private theorem fibredInGroupoidsFactorizationToTarget_base_comp
    (F : X ⥤ᵇ Y)
    {P Q R : (fibredInGroupoidsFactorization F).obj}
    (g : (fibredInGroupoidsFactorizationToTarget F).toFunctor.obj R ⟶
      (fibredInGroupoidsFactorizationToTarget F).toFunctor.obj P)
    (h : (fibredInGroupoidsFactorizationToTarget F).toFunctor.obj P ⟶
      (fibredInGroupoidsFactorizationToTarget F).toFunctor.obj Q) :
    fibredInGroupoidsFactorizationToTarget_base F (g ≫ h) =
      fibredInGroupoidsFactorizationToTarget_base F g ≫
        fibredInGroupoidsFactorizationToTarget_base F h := by
  -- The middle transport cancels because both arrows land in the same image object `P`.
  dsimp [fibredInGroupoidsFactorizationToTarget_base]
  simp [Category.assoc]

/-- Helper for Lemma 4.35.16: for an actual morphism in the explicit factorization, the
transported base of its right component is exactly the stored base field. -/
private theorem fibredInGroupoidsFactorizationToTarget_base_eq
    (F : X ⥤ᵇ Y)
    {P Q : (fibredInGroupoidsFactorization F).obj}
    (φ : P ⟶ Q) :
    fibredInGroupoidsFactorizationToTarget_base F φ.b = φ.base := by
  -- Expand the transported base and then rewrite `Y.p.map φ.b` using the lifting property of the
  -- right component.
  dsimp [fibredInGroupoidsFactorizationToTarget_base]
  rw [IsHomLift.fac' Y.p φ.base φ.b]
  simp [Category.assoc]

/-- Helper for Lemma 4.35.16: the base arrow attached to a morphism into the image of the right
projection is the one that the morphism itself lifts in `Y`. -/
theorem fibredInGroupoidsFactorizationToTarget_pullbackBase_isHomLift
    (F : X ⥤ᵇ Y)
    {P : (fibredInGroupoidsFactorization F).obj}
    {y' : Y.obj}
    (b : y' ⟶ (fibredInGroupoidsFactorizationToTarget F).toFunctor.obj P) :
    Y.p.IsHomLift (fibredInGroupoidsFactorizationToTarget_pullbackBase F b) b := by
  -- Only the codomain transport from the chosen object `P` needs to be normalized.
  simpa [fibredInGroupoidsFactorizationToTarget_pullbackBase] using
    (IsHomLift.lift_comp_eqToHom_iff
      Y.p
      (Y.p.map b)
      b
      ((fibredInGroupoidsFactorizationToTarget F).w_obj P)).2
      (show Y.p.IsHomLift (Y.p.map b) b from inferInstance)

/-- Helper for Lemma 4.35.16: pull back the `X`-component of a factorization object along a
target morphism `b : y' ⟶ P.y`, viewed in the standard fiber of `X` over `Y.p.obj y'`. -/
noncomputable def fibredInGroupoidsFactorizationToTarget_left_pullback
    (F : X ⥤ᵇ Y)
    (P : (fibredInGroupoidsFactorization F).obj)
    {y' : Y.obj}
    (b : y' ⟶ (fibredInGroupoidsFactorizationToTarget F).toFunctor.obj P) :
    X.p.Fiber (Y.p.obj y') :=
  let f := fibredInGroupoidsFactorizationToTarget_pullbackBase F b
  let _ : HasFibers X.p := HasFibers.canonical X.p
  let a := HasFibers.pullbackMap (p := X.p) f P.obj.fst.2
  Functor.Fiber.mk (IsHomLift.domain_eq X.p f a)

/-- Helper for Lemma 4.35.16: the chosen pullback map of the `X`-component along a target
morphism `b : y' ⟶ P.y`. -/
noncomputable def fibredInGroupoidsFactorizationToTarget_left_pullback_map
    (F : X ⥤ᵇ Y)
    (P : (fibredInGroupoidsFactorization F).obj)
    {y' : Y.obj}
    (b : y' ⟶ (fibredInGroupoidsFactorizationToTarget F).toFunctor.obj P) :
    (fibredInGroupoidsFactorizationToTarget_left_pullback F P b).1 ⟶ P.obj.fst.1 :=
  let f := fibredInGroupoidsFactorizationToTarget_pullbackBase F b
  let _ : HasFibers X.p := HasFibers.canonical X.p
  let a := HasFibers.pullbackMap (p := X.p) f P.obj.fst.2
  show (fibredInGroupoidsFactorizationToTarget_left_pullback F P b).1 ⟶ P.obj.fst.1 from a

/-- Helper for Lemma 4.35.16: the chosen pullback map of the left component is strongly
cartesian over the transported base arrow attached to `b`. -/
theorem fibredInGroupoidsFactorizationToTarget_left_pullback_map_isStronglyCartesian
    (F : X ⥤ᵇ Y)
    (P : (fibredInGroupoidsFactorization F).obj)
    {y' : Y.obj}
    (b : y' ⟶ (fibredInGroupoidsFactorizationToTarget F).toFunctor.obj P) :
    X.p.IsStronglyCartesian
      (fibredInGroupoidsFactorizationToTarget_pullbackBase F b)
      (fibredInGroupoidsFactorizationToTarget_left_pullback_map F P b) := by
  let f := fibredInGroupoidsFactorizationToTarget_pullbackBase F b
  let _ : HasFibers X.p := HasFibers.canonical X.p
  let a := fibredInGroupoidsFactorizationToTarget_left_pullback_map F P b
  have ha_cart : X.p.IsCartesian f a := by
    -- The canonical pullback map in `X` is cartesian by construction.
    change X.p.IsCartesian f (HasFibers.pullbackMap (p := X.p) f P.obj.fst.2)
    infer_instance
  exact Functor.IsFibered.isStronglyCartesian_of_isCartesian X.p f a

/-- Helper for Lemma 4.35.16: if a morphism is strongly cartesian for one chosen lift of its base
arrow, then it is strongly cartesian for any other chosen lift of the same morphism. -/
private theorem isStronglyCartesian_rebase_of_same_lift
    {𝒮 : Type u} {𝒳 : Type v} [Category 𝒮] [Category 𝒳]
    (p : 𝒳 ⥤ 𝒮)
    {a b : 𝒳} {f f' : p.obj a ⟶ p.obj b} (φ : a ⟶ b)
    [p.IsStronglyCartesian f φ] [p.IsHomLift f' φ] :
    p.IsStronglyCartesian f' φ := by
  -- Both lift structures identify their base arrows with the owner base map `p.map φ`.
  have hf : f = p.map φ := IsHomLift.eq_of_isHomLift p f φ
  have hf' : f' = p.map φ := IsHomLift.eq_of_isHomLift p f' φ
  subst hf
  subst hf'
  infer_instance

/-- Helper for Lemma 4.35.16: an external lift witness upgrades strong cartesianness back to the
owner-level base map of the same morphism. -/
theorem isStronglyCartesian_of_external_hom_lift
    {𝒮 : Type u} {𝒳 : Type v} [Category 𝒮] [Category 𝒳]
    (p : 𝒳 ⥤ 𝒮)
    {R S : 𝒮} {a b : 𝒳} {f : R ⟶ S} (φ : a ⟶ b)
    [p.IsStronglyCartesian (p.map φ) φ] [p.IsHomLift f φ] :
    p.IsStronglyCartesian f φ := by
  -- Normalize the chosen external source and target to the actual owner source and target.
  have ha : p.obj a = R := IsHomLift.domain_eq p f φ
  have hb : p.obj b = S := IsHomLift.codomain_eq p f φ
  subst ha
  subst hb
  exact isStronglyCartesian_rebase_of_same_lift (p := p) (f := p.map φ) (f' := f) φ

/-- Helper for Lemma 4.35.16: once the `X`-component of a morphism in the explicit factorization
is strongly cartesian over its base arrow in `C`, the whole morphism is strongly cartesian for the
right projection to `Y`. -/
theorem fibredInGroupoidsFactorizationToTarget_hom_isStronglyCartesian_of_left
    (F : X ⥤ᵇ Y)
    {P Q : (fibredInGroupoidsFactorization F).obj}
    (φ : P ⟶ Q)
    (ha : X.p.IsStronglyCartesian φ.base φ.a) :
    (fibredInGroupoidsFactorizationToTarget F).toFunctor.IsStronglyCartesian φ.b φ := by
  letI : X.p.IsStronglyCartesian φ.base φ.a := ha
  refine
    { toIsHomLift := by
        refine
          IsHomLift.of_fac'
            ((fibredInGroupoidsFactorizationToTarget F).toFunctor)
            φ.b
            φ
            rfl
            rfl
            ?_
        simp [fibredInGroupoidsFactorizationToTarget]
      universal_property' := ?_ }
  intro R g ψ hψ
  letI :
      (fibredInGroupoidsFactorizationToTarget F).toFunctor.IsHomLift (g ≫ φ.b) ψ := hψ
  have hψb : g ≫ φ.b = ψ.b := by
    simpa using
      (IsHomLift.eq_of_isHomLift
        ((fibredInGroupoidsFactorizationToTarget F).toFunctor) (g ≫ φ.b) ψ)
  have hψa :
      X.p.IsHomLift
        (fibredInGroupoidsFactorizationToTarget_base F g ≫ φ.base)
        ψ.a := by
    have hbase :
        fibredInGroupoidsFactorizationToTarget_base F g ≫ φ.base = ψ.base := by
      calc
        fibredInGroupoidsFactorizationToTarget_base F g ≫ φ.base
            = fibredInGroupoidsFactorizationToTarget_base F g ≫
                fibredInGroupoidsFactorizationToTarget_base F φ.b := by
                  rw [fibredInGroupoidsFactorizationToTarget_base_eq F φ]
        _ = fibredInGroupoidsFactorizationToTarget_base F (g ≫ φ.b) := by
              symm
              exact fibredInGroupoidsFactorizationToTarget_base_comp F g φ.b
        _ = fibredInGroupoidsFactorizationToTarget_base F ψ.b := by
              simpa [hψb]
        _ = ψ.base := by
              exact fibredInGroupoidsFactorizationToTarget_base_eq F ψ
    refine
      IsHomLift.of_fac'
        X.p
        (fibredInGroupoidsFactorizationToTarget_base F g ≫ φ.base)
        ψ.a
        R.obj.fst.2
        Q.obj.fst.2
        ?_
    simpa [hbase, Category.assoc] using IsHomLift.fac' X.p ψ.base ψ.a
  letI :
      X.p.IsHomLift
        (fibredInGroupoidsFactorizationToTarget_base F g ≫ φ.base)
        ψ.a := hψa
  -- Factor the `X`-component through the chosen strongly cartesian lift `φ.a`.
  obtain ⟨χa, hχa, hχa_uniq⟩ :=
    Functor.IsStronglyCartesian.universal_property
      X.p
      φ.base
      φ.a
      (fibredInGroupoidsFactorizationToTarget_base F g)
      (fibredInGroupoidsFactorizationToTarget_base F g ≫ φ.base)
      rfl
      ψ.a
  have hχa_over :
      X.p.IsHomLift (fibredInGroupoidsFactorizationToTarget_base F g) χa := hχa.1
  have hχa_fac : χa ≫ φ.a = ψ.a := hχa.2
  have hφb :
      Y.p.IsStronglyCartesian φ.base φ.b := by
    letI : Y.p.IsHomLift φ.base φ.b := by
      rw [← fibredInGroupoidsFactorizationToTarget_base_eq F φ]
      exact fibredInGroupoidsFactorizationToTarget_base_isHomLift F φ.b
    exact isStronglyCartesian_of_external_hom_lift (p := Y.p) (f := φ.base) φ.b
  letI : Y.p.IsStronglyCartesian φ.base φ.b := hφb
  have hleft_over :
      Y.p.IsHomLift
        (fibredInGroupoidsFactorizationToTarget_base F g)
        (F.map χa ≫ P.comparison) := by
    -- Map the left factor through `F`, then append the vertical comparison of `P`.
    have hFχa :
        Y.p.IsHomLift
          (fibredInGroupoidsFactorizationToTarget_base F g)
          (F.map χa) := by
      infer_instance
    letI :
        Y.p.IsHomLift
          (fibredInGroupoidsFactorizationToTarget_base F g)
          (F.map χa) := hFχa
    letI : Y.p.IsHomLift (𝟙 P.U) P.comparison := P.comparison_over
    exact
      @IsHomLift.comp_lift_id_right' _ _ _ _ Y.p _ _ _ _ _
        (fibredInGroupoidsFactorizationToTarget_base F g)
        (F.map χa)
        hFχa
        P.U
        P.comparison
        P.comparison_over
  have hright_over :
      Y.p.IsHomLift
        (fibredInGroupoidsFactorizationToTarget_base F g)
        (R.comparison ≫ g) := by
    -- Precompose the target arrow `g` with the vertical comparison of `R`.
    have hg :
        Y.p.IsHomLift
          (fibredInGroupoidsFactorizationToTarget_base F g)
          g := fibredInGroupoidsFactorizationToTarget_base_isHomLift F g
    letI :
        Y.p.IsHomLift
          (fibredInGroupoidsFactorizationToTarget_base F g)
          g := hg
    letI : Y.p.IsHomLift (𝟙 R.U) R.comparison := R.comparison_over
    exact
      @IsHomLift.comp_lift_id_left' _ _ _ _ Y.p _ _ _
        R.U
        R.comparison
        R.comparison_over
        _ _
        (fibredInGroupoidsFactorizationToTarget_base F g)
        g
        hg
  have hcomm_after_comp :
      (F.map χa ≫ P.comparison) ≫ φ.b =
        (R.comparison ≫ g) ≫ φ.b := by
    have hφcomm : P.comparison ≫ φ.b = F.map φ.a ≫ Q.comparison := by
      simpa using φ.comm.w.symm
    have hψcomm : F.map ψ.a ≫ Q.comparison = R.comparison ≫ ψ.b := by
      simpa using ψ.comm.w
    have hψcomm_post :
        F.map ψ.a ≫ Q.comparison =
          (R.comparison ≫ g) ≫ φ.b := by
      simpa [Category.assoc, hψb] using hψcomm
    have hχa_map :
        F.map (χa ≫ φ.a) ≫ Q.comparison = F.map ψ.a ≫ Q.comparison := by
      simpa using congrArg (fun k ↦ F.map k ≫ Q.comparison) hχa_fac
    have hmain :
        (F.map χa ≫ P.comparison) ≫ φ.b = F.map ψ.a ≫ Q.comparison := by
      calc
        (F.map χa ≫ P.comparison) ≫ φ.b = F.map χa ≫ (P.comparison ≫ φ.b) := by
          simp [Category.assoc]
        _ = F.map χa ≫ (F.map φ.a ≫ Q.comparison) := by
          simpa using congrArg (fun k ↦ F.map χa ≫ k) hφcomm
        _ = (F.map χa ≫ F.map φ.a) ≫ Q.comparison := by
          simp [Category.assoc]
        _ = F.map (χa ≫ φ.a) ≫ Q.comparison := by
          simp [Functor.map_comp, Category.assoc]
        _ = F.map ψ.a ≫ Q.comparison := hχa_map
    -- Both candidate comparison arrows become equal after postcomposition with `φ.b`.
    exact hmain.trans hψcomm_post
  have hcomm :
      F.map χa ≫ P.comparison = R.comparison ≫ g := by
    letI :
        Y.p.IsHomLift
          (fibredInGroupoidsFactorizationToTarget_base F g)
          (F.map χa ≫ P.comparison) := hleft_over
    letI :
        Y.p.IsHomLift
          (fibredInGroupoidsFactorizationToTarget_base F g)
          (R.comparison ≫ g) := hright_over
    exact
      @Functor.IsStronglyCartesian.ext _ _ _ _ Y.p _ _ _ _
        φ.base φ.b inferInstance _ _
        (fibredInGroupoidsFactorizationToTarget_base F g)
        (F.map χa ≫ P.comparison)
        (R.comparison ≫ g)
        hleft_over hright_over
        (by simpa [Category.assoc] using hcomm_after_comp)
  let χ : R ⟶ P :=
    { base := fibredInGroupoidsFactorizationToTarget_base F g
      a := χa
      a_over := hχa_over
      b := g
      b_over := fibredInGroupoidsFactorizationToTarget_base_isHomLift F g
      comm := ⟨hcomm⟩ }
  refine ⟨χ, ⟨?_, ?_⟩, ?_⟩
  · -- The assembled morphism lifts the prescribed `Y`-morphism `g`.
    refine
      IsHomLift.of_fac'
        ((fibredInGroupoidsFactorizationToTarget F).toFunctor)
        g
        χ
        rfl
        rfl
        ?_
    simp [χ, fibredInGroupoidsFactorizationToTarget]
  · -- Factorization follows from the chosen left factor and the lift equation on the right.
    apply ExplicitTwoFibreProductHom.ext
    · simpa [χ] using hχa_fac
    · simpa [χ] using hψb
  · intro χ' hχ'
    rcases hχ' with ⟨hχ'_over, hχ'_fac⟩
    letI :
        (fibredInGroupoidsFactorizationToTarget F).toFunctor.IsHomLift
          g χ' := hχ'_over
    have hχ'a_base :
        χ'.base = fibredInGroupoidsFactorizationToTarget_base F g := by
      calc
        χ'.base = fibredInGroupoidsFactorizationToTarget_base F χ'.b := by
                    symm
                    exact fibredInGroupoidsFactorizationToTarget_base_eq F χ'
        _ = fibredInGroupoidsFactorizationToTarget_base F g := by
              have hχ'b : g = χ'.b := by
                simpa using
                  (IsHomLift.eq_of_isHomLift
                    ((fibredInGroupoidsFactorizationToTarget F).toFunctor) g χ')
              simpa [hχ'b]
    have hχ'a :
        X.p.IsHomLift
          (fibredInGroupoidsFactorizationToTarget_base F g)
          χ'.a := by
      rw [← hχ'a_base]
      simpa using (χ'.a_over : X.p.IsHomLift χ'.base χ'.a)
    apply ExplicitTwoFibreProductHom.ext
    · exact
        hχa_uniq χ'.a
          ⟨hχ'a, by simpa using congrArg ExplicitTwoFibreProductHom.a hχ'_fac⟩
    · simpa [χ] using
        (IsHomLift.eq_of_isHomLift
          ((fibredInGroupoidsFactorizationToTarget F).toFunctor) g χ').symm

/-- Helper for Lemma 4.35.16: the pulled-back left component of a factorization object carries a
vertical comparison isomorphism to the chosen source object in `Y`. -/
noncomputable def fibredInGroupoidsFactorizationToTarget_pulledback_comparison_iso
    (F : X ⥤ᵇ Y)
    (P : (fibredInGroupoidsFactorization F).obj)
    {y' : Y.obj}
    (b : y' ⟶ (fibredInGroupoidsFactorizationToTarget F).toFunctor.obj P) :
    (F.fiberFunctor (Y.p.obj y')).obj (fibredInGroupoidsFactorizationToTarget_left_pullback F P b) ≅
      Functor.Fiber.mk rfl := by
  let f := fibredInGroupoidsFactorizationToTarget_pullbackBase F b
  let _ : HasFibers X.p := HasFibers.canonical X.p
  let a := fibredInGroupoidsFactorizationToTarget_left_pullback_map F P b
  have ha_cart : X.p.IsCartesian f a := by
    change X.p.IsCartesian f (HasFibers.pullbackMap (p := X.p) f P.obj.fst.2)
    infer_instance
  have ha : X.p.IsStronglyCartesian f a :=
    Functor.IsFibered.isStronglyCartesian_of_isCartesian X.p f a
  have hFa :
      Y.p.IsStronglyCartesian f (F.map a) := by
    have hmap :
        Y.p.IsStronglyCartesian (Y.p.map (F.map a)) (F.map a) :=
      inferInstance
    letI : Y.p.IsStronglyCartesian (Y.p.map (F.map a)) (F.map a) := hmap
    letI : Y.p.IsHomLift f (F.map a) := by
      infer_instance
    exact isStronglyCartesian_of_external_hom_lift (p := Y.p) (f := f) (F.map a)
  have hb :
      Y.p.IsStronglyCartesian f b := by
    letI : Y.p.IsHomLift f b := fibredInGroupoidsFactorizationToTarget_pullbackBase_isHomLift F b
    exact isStronglyCartesian_of_external_hom_lift (p := Y.p) (f := f) b
  letI : IsIso P.comparison := fibredInGroupoidsFactorization_comparison_isIso F P
  have hleft_over :
      Y.p.IsHomLift f (F.map a ≫ P.comparison) := by
    have hFa_over : Y.p.IsHomLift f (F.map a) := by
      infer_instance
    letI : Y.p.IsHomLift f (F.map a) := hFa_over
    letI : Y.p.IsHomLift (𝟙 P.U) P.comparison := P.comparison_over
    exact IsHomLift.comp_lift_id_right' (p := Y.p) f (F.map a) P.U P.comparison
  have hleft :
      Y.p.IsStronglyCartesian f (F.map a ≫ P.comparison) := by
    letI : Y.p.IsStronglyCartesian f (F.map a) := hFa
    letI : Y.p.IsHomLift (𝟙 P.U) P.comparison := P.comparison_over
    have hcomparison : Y.p.IsStronglyCartesian (𝟙 P.U) P.comparison :=
      Functor.IsStronglyCartesian.of_isIso Y.p (𝟙 P.U) P.comparison
    letI : Y.p.IsStronglyCartesian (𝟙 P.U) P.comparison := hcomparison
    simpa using
      (show Y.p.IsStronglyCartesian (f ≫ 𝟙 P.U) (F.map a ≫ P.comparison) from inferInstance)
  let e : F.obj ((fibredInGroupoidsFactorizationToTarget_left_pullback F P b).1) ≅ y' := by
    exact
      @Functor.IsStronglyCartesian.domainIsoOfBaseIso _ _ _ _ Y.p
        _ _ _ _ _ _ _ _ _
        (show f = (Iso.refl (Y.p.obj y')).hom ≫ f by simp)
        b
        (F.map a ≫ P.comparison)
        hb
        hleft
  have hhom : Y.p.IsHomLift (𝟙 (Y.p.obj y')) e.hom := by
    simpa [e] using
      (@Functor.IsStronglyCartesian.domainUniqueUpToIso_inv_isHomLift _ _ _ _ Y.p
        _ _ _ _ _ _ _ _ _
        (show f = (Iso.refl (Y.p.obj y')).hom ≫ f by simp)
        b
        (F.map a ≫ P.comparison)
        hb
        hleft)
  have hinv : Y.p.IsHomLift (𝟙 (Y.p.obj y')) e.inv := by
    simpa [e] using
      (@Functor.IsStronglyCartesian.domainUniqueUpToIso_hom_isHomLift _ _ _ _ Y.p
        _ _ _ _ _ _ _ _ _
        (show f = (Iso.refl (Y.p.obj y')).hom ≫ f by simp)
        b
        (F.map a ≫ P.comparison)
        hb
        hleft)
  -- Package the domain comparison back into the standard fiber over `Y.p.obj y'`.
  refine
    { hom := Functor.Fiber.homMk Y.p (Y.p.obj y') e.hom
      inv := Functor.Fiber.homMk Y.p (Y.p.obj y') e.inv
      hom_inv_id := by
        apply Functor.Fiber.hom_ext
        exact e.hom_inv_id
      inv_hom_id := by
        apply Functor.Fiber.hom_ext
        exact e.inv_hom_id }

/-- Helper for Lemma 4.35.16: every arrow into the target component of a factorization object has
an explicit strongly cartesian lift obtained by pulling back the `X`-component and transporting
the comparison isomorphism across the resulting lift in `Y`. -/
theorem fibredInGroupoidsFactorizationToTarget_exists_isStronglyCartesian
    (F : X ⥤ᵇ Y)
    (P : (fibredInGroupoidsFactorization F).obj)
    {y' : Y.obj}
    (b : y' ⟶ (fibredInGroupoidsFactorizationToTarget F).toFunctor.obj P) :
    ∃ Q : (fibredInGroupoidsFactorization F).obj,
      ∃ η : Q ⟶ P,
        (fibredInGroupoidsFactorizationToTarget F).toFunctor.IsStronglyCartesian b η := by
  let f := fibredInGroupoidsFactorizationToTarget_pullbackBase F b
  let _ : HasFibers X.p := HasFibers.canonical X.p
  let a := fibredInGroupoidsFactorizationToTarget_left_pullback_map F P b
  have ha_over : X.p.IsHomLift f a := by
    change X.p.IsHomLift f (HasFibers.pullbackMap (p := X.p) f P.obj.fst.2)
    infer_instance
  have ha_cart : X.p.IsCartesian f a := by
    change X.p.IsCartesian f (HasFibers.pullbackMap (p := X.p) f P.obj.fst.2)
    infer_instance
  have ha : X.p.IsStronglyCartesian f a :=
    Functor.IsFibered.isStronglyCartesian_of_isCartesian X.p f a
  have hFa :
      Y.p.IsStronglyCartesian f (F.map a) := by
    have hmap :
        Y.p.IsStronglyCartesian (Y.p.map (F.map a)) (F.map a) :=
      inferInstance
    letI : Y.p.IsStronglyCartesian (Y.p.map (F.map a)) (F.map a) := hmap
    letI : Y.p.IsHomLift f (F.map a) := by
      infer_instance
    exact isStronglyCartesian_of_external_hom_lift (p := Y.p) (f := f) (F.map a)
  have hb :
      Y.p.IsStronglyCartesian f b := by
    letI : Y.p.IsHomLift f b := fibredInGroupoidsFactorizationToTarget_pullbackBase_isHomLift F b
    exact isStronglyCartesian_of_external_hom_lift (p := Y.p) (f := f) b
  letI : IsIso P.comparison := fibredInGroupoidsFactorization_comparison_isIso F P
  have hleft_over :
      Y.p.IsHomLift f (F.map a ≫ P.comparison) := by
    have hFa_over : Y.p.IsHomLift f (F.map a) := by
      infer_instance
    letI : Y.p.IsHomLift f (F.map a) := hFa_over
    letI : Y.p.IsHomLift (𝟙 P.U) P.comparison := P.comparison_over
    exact IsHomLift.comp_lift_id_right' (p := Y.p) f (F.map a) P.U P.comparison
  have hleft :
      Y.p.IsStronglyCartesian f (F.map a ≫ P.comparison) := by
    letI : Y.p.IsStronglyCartesian f (F.map a) := hFa
    letI : Y.p.IsHomLift (𝟙 P.U) P.comparison := P.comparison_over
    have hcomparison : Y.p.IsStronglyCartesian (𝟙 P.U) P.comparison :=
      Functor.IsStronglyCartesian.of_isIso Y.p (𝟙 P.U) P.comparison
    letI : Y.p.IsStronglyCartesian (𝟙 P.U) P.comparison := hcomparison
    simpa using
      (show Y.p.IsStronglyCartesian (f ≫ 𝟙 P.U) (F.map a ≫ P.comparison) from inferInstance)
  let e : F.obj ((fibredInGroupoidsFactorizationToTarget_left_pullback F P b).1) ≅ y' := by
    exact
      @Functor.IsStronglyCartesian.domainIsoOfBaseIso _ _ _ _ Y.p
        _ _ _ _ _ _ _ _ _
        (show f = (Iso.refl (Y.p.obj y')).hom ≫ f by simp)
        b
        (F.map a ≫ P.comparison)
        hb
        hleft
  have hhom : Y.p.IsHomLift (𝟙 (Y.p.obj y')) e.hom := by
    simpa [e] using
      (@Functor.IsStronglyCartesian.domainUniqueUpToIso_inv_isHomLift _ _ _ _ Y.p
        _ _ _ _ _ _ _ _ _
        (show f = (Iso.refl (Y.p.obj y')).hom ≫ f by simp)
        b
        (F.map a ≫ P.comparison)
        hb
        hleft)
  have hinv : Y.p.IsHomLift (𝟙 (Y.p.obj y')) e.inv := by
    simpa [e] using
      (@Functor.IsStronglyCartesian.domainUniqueUpToIso_hom_isHomLift _ _ _ _ Y.p
        _ _ _ _ _ _ _ _ _
        (show f = (Iso.refl (Y.p.obj y')).hom ≫ f by simp)
        b
        (F.map a ≫ P.comparison)
        hb
        hleft)
  let Q : (fibredInGroupoidsFactorization F).obj :=
    { U := Y.p.obj y'
      obj :=
        { fst := fibredInGroupoidsFactorizationToTarget_left_pullback F P b
          snd := Functor.Fiber.mk rfl
          iso :=
            { hom := Functor.Fiber.homMk Y.p (Y.p.obj y') e.hom
              inv := Functor.Fiber.homMk Y.p (Y.p.obj y') e.inv
              hom_inv_id := by
                apply Functor.Fiber.hom_ext
                exact e.hom_inv_id
              inv_hom_id := by
                apply Functor.Fiber.hom_ext
                exact e.inv_hom_id } } }
  have hfac :
      e.hom ≫ b = F.map a ≫ P.comparison := by
    simpa [e] using
      (@Functor.IsStronglyCartesian.fac _ _ _ _ Y.p
        _ _ _ _ f b hb
        _ _
        (Iso.refl (Y.p.obj y')).hom
        f
        (show f = (Iso.refl (Y.p.obj y')).hom ≫ f by simp)
        (F.map a ≫ P.comparison)
        hleft_over)
  have hcomm :
      CommSq (F.map a) Q.comparison P.comparison b := by
    -- The comparison of `Q` is exactly the vertical arrow produced by the strong-cartesian
    -- comparison in `Y`.
    refine ⟨?_⟩
    simpa [Q, fibredInGroupoidsFactorizationToTarget_left_pullback_map] using hfac.symm
  let η : Q ⟶ P :=
    { base := f
      a := a
      a_over := ha_over
      b := b
      b_over := fibredInGroupoidsFactorizationToTarget_pullbackBase_isHomLift F b
      comm := hcomm }
  have hη :
      (fibredInGroupoidsFactorizationToTarget F).toFunctor.IsStronglyCartesian b η := by
    -- The direct universal-property proof now applies because the left component is the chosen
    -- strongly cartesian pullback of `P.x`.
    simpa [η] using
      fibredInGroupoidsFactorizationToTarget_hom_isStronglyCartesian_of_left F η ha
  exact ⟨Q, η, hη⟩

-- Proof sketch: the target projection from the explicit `2`-fibre-product model is the right
-- projection `(x, y, f) ↦ y`; the textbook argument shows it satisfies the fibred-in-groupoids
-- lifting and uniqueness conditions over `Y`, using the `Y`-side fibred-in-groupoids structure
-- over `C` to produce the needed comparison isomorphism over the identity.
/-- Lemma 4.35.16 (4): the projection `X' ⟶ Y` is fibred in groupoids over `Y`. -/
theorem fibredInGroupoidsFactorizationToTarget_isFibredInGroupoids
    (F : X ⥤ᵇ Y) :
    IsFibredInGroupoids (fibredInGroupoidsFactorizationToTarget F).toFunctor := by
  refine
    { toIsFibered := ?_
      isStronglyCartesian_map := ?_ }
  · -- Build explicit strongly cartesian lifts over arbitrary arrows of `Y`.
    refine Functor.IsFibered.of_exists_isStronglyCartesian ?_
    intro P y' b
    obtain ⟨Q, η, hη⟩ :=
      fibredInGroupoidsFactorizationToTarget_exists_isStronglyCartesian F P b
    exact ⟨Q, η, hη⟩
  · intro P Q φ
    -- Route correction: prove map-strong-cartesianness directly from the universal property in
    -- the `X`-component instead of transporting a separate owner-level theorem.
    have hφa : X.p.IsStronglyCartesian φ.base φ.a := by
      letI : X.p.IsStronglyCartesian (X.p.map φ.a) φ.a :=
        (inferInstance : X.p.IsStronglyCartesian (X.p.map φ.a) φ.a)
      letI : X.p.IsHomLift φ.base φ.a := φ.a_over
      exact isStronglyCartesian_of_external_hom_lift (p := X.p) (f := φ.base) φ.a
    simpa using
      fibredInGroupoidsFactorizationToTarget_hom_isStronglyCartesian_of_left F φ hφa

-- Proof sketch: the factorization projection to `C` is the composite of the right projection
-- `X' ⟶ Y` with the original projection `Y ⥤ C`, so Lemma 4.35.14 closes the proof once the
-- right projection is known to be fibred in groupoids.
/-- Lemma 4.35.16 (1): the explicit factorization object `X' = X ×_{F, Y, id} Y` is fibred in
groupoids over `C`. -/
theorem fibredInGroupoidsFactorization_isFibredInGroupoids
    (F : X ⥤ᵇ Y) :
    IsFibredInGroupoids (fibredInGroupoidsFactorization F).p := by
  -- Route correction: compose the already-proved projection `X' ⟶ Y` with `Y ⥤ C` instead of
  -- reusing the homogeneous-universe specialization of Lemma 4.35.7.
  letI : IsFibredInGroupoids (fibredInGroupoidsFactorizationToTarget F).toFunctor :=
    fibredInGroupoidsFactorizationToTarget_isFibredInGroupoids F
  have hw :
      ((fibredInGroupoidsFactorizationToTarget F).toFunctor ⋙ Y.p) =
        (fibredInGroupoidsFactorization F).p :=
    (fibredInGroupoidsFactorizationToTarget F).w
  simpa [hw] using
    (show IsFibredInGroupoids (((fibredInGroupoidsFactorizationToTarget F).toFunctor) ⋙ Y.p) from
      inferInstance)

end

end CategoryTheory
