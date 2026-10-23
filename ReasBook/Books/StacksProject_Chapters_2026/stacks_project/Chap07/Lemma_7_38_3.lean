module

public import Mathlib.CategoryTheory.EssentiallySmall
public import Mathlib.CategoryTheory.Sites.LocallySurjective
public import Mathlib.Topology.Sheaves.LocallySurjective
public import Mathlib.CategoryTheory.Sites.Sheafification
public import Mathlib.CategoryTheory.Sites.Sheaf
public import stacks_project.Chap07.Lemma_7_11_2
public import stacks_project.Chap07.Lemma_7_12_4
public import stacks_project.Chap07.Lemma_7_38_2
public import stacks_project.Chap07.Lemma_7_38_3.Index

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Opposite
open CategoryTheory.Limits
open CategoryTheory.ObjectProperty

universe w v u w' w''

namespace CategoryTheory

namespace GrothendieckTopology

attribute [local instance] Types.instFunLike Types.instConcreteCategory

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}

/- Layering for Lemma 7.38.3:
- primary domain: conservative families of points of a site and their detection of equality of
  sections through point fibers;
- sampled owner declarations:
  `ObjectProperty.IsConservativeFamilyOfPoints`,
  `isConservativePointFamily_iff`,
  `JointlyFaithful.jointlyReflectsIsomorphisms`,
  `GrothendieckTopology.uliftSheafifiedRepresentableHomEquiv`;
- source/core/bridge triage:
  `source-facing`: the textbook criterion that distinct local sections are separated by some germ
    at a point of the family;
  `core/canonical`: `(ofObj p).IsConservativeFamilyOfPoints`;
  `bridge/view`: the indexed-family recall `isConservativePointFamily_iff`, together with the
    sheafified-representable Yoneda equivalence used to compare sections with morphisms out of
    `h[U]^#[J]`.
- primitive data: only the indexed family of points `p`;
- derived API here: the source-facing separation criterion.

The owner abstraction remains `(ofObj p).IsConservativeFamilyOfPoints`; this file should stay a
thin source-facing bridge, not a second owner for conservative point families.
-/

-- Proof sketch: for the forward implication, if two sections have the same germ at every point of
-- the family, the induced equalizer sieve has surjective maps on all point fibers; the
-- conservative-family local-surjectivity criterion makes it covering, and separatedness of the
-- sheaf identifies the sections. For the converse, use the separation hypothesis to show the stalk
-- family is jointly faithful on sheaves of sets; then the generic owner theorem
-- `JointlyFaithful.jointlyReflectsIsomorphisms`, combined with `isConservativePointFamily_iff`,
-- upgrades that joint faithfulness to conservativity.

/-- Helper for Lemma 7.38.3: if every lifted point-fiber element lifts through a sieve, that
forces the sieve to be covering by the conservative-family `W`-criterion. -/
private lemma covering_of_ulift_family_lifts_core
    {ι : Type w} (p : ι → Point.{w'} J)
    (hp : (ofObj p).IsConservativeFamilyOfPoints)
    [LocallySmall.{w'} C] [HasSheafify J (Type w')] [J.WEqualsLocallyBijective (Type w')]
    {X : C} (S : Sieve X)
    (hS :
      ∀ i (x : ULift.{max u v, w'} ((p i).fiber.obj X)),
        ∃ (Y : C) (g : Y ⟶ X) (_ : S g) (y : ULift.{max u v, w'} ((p i).fiber.obj Y)),
          ULift.up ((p i).fiber.map g y.down) = x) :
    S ∈ J X := by
  have hsurj :
      ∀ Φ : (ofObj p).FullSubcategory,
        Function.Surjective
          (Φ.obj.presheafFiber.map (Sieve.shrinkFunctor.{w'} S).ι) :=
    shrinkFunctor_surjective_fullSubcategory_of_ulift_lifts (p := p) S hS
  have hloc : Presheaf.IsLocallySurjective J (Sieve.shrinkFunctor.{w'} S).ι :=
    hp.jointly_reflect_isLocallySurjective (Sieve.shrinkFunctor.{w'} S).ι hsurj
  let x : (shrinkYoneda.{w'}.obj X).obj (op X) :=
    shrinkYonedaObjObjEquiv.symm (𝟙 X)
  have hmem : Presheaf.imageSieve (Sieve.shrinkFunctor.{w'} S).ι x ∈ J X :=
    hloc.imageSieve_mem x
  rw [show Presheaf.imageSieve (Sieve.shrinkFunctor.{w'} S).ι x = S by
    simpa [x] using imageSieve_shrinkFunctor_ι_id (S := S)] at hmem
  exact hmem

/-- Helper for Lemma 7.38.3: pointwise equality of germs along a conservative family makes the
equalizer sieve of the two sections covering. -/
private lemma covering_equalizerSieve_of_pointwise_germ_eq
    [LocallySmall.{w'} C]
    [HasSheafify J (Type w')] [J.WEqualsLocallyBijective (Type w')]
    {ι : Type w} (p : ι → Point.{w'} J)
    (hp : (ofObj p).IsConservativeFamilyOfPoints)
    {ℱ : Sheaf J (Type (max u v w'))} (U : C)
    (s s' : ℱ.obj.obj (op U))
    (hss :
      ∀ i (x : (p i).fiber.obj U),
        (p i).toPresheafFiber U x ℱ.obj s =
          (p i).toPresheafFiber U x ℱ.obj s') :
    Presheaf.equalizerSieve (F := ℱ.obj) s s' ∈ J U := by
  let S : Sieve U := Presheaf.equalizerSieve (F := ℱ.obj) s s'
  -- Keep the source proof's controlling object fixed: prove the equalizer sieve is covering from
  -- the pointwise germ equalities and the conservative family.
  exact covering_of_ulift_family_lifts_core (p := p) hp (S := S) <| by
    intro i x
    obtain ⟨Y, g, hg, y, hy⟩ :=
      pointwise_germ_eq_gives_equalizer_lift (q := p i) U s s' (hx := hss i x.down)
    refine ⟨Y, g, hg, ULift.up.{max u v, w'} y, ?_⟩
    cases x
    simpa using
      congrArg (ULift.up.{max u v, w'} : (p i).fiber.obj U → ULift.{max u v, w'} ((p i).fiber.obj U)) hy

/-- Helper for Lemma 7.38.3: a covering equalizer sieve forces two sections of a sheaf to agree. -/
private lemma sections_eq_of_covering_equalizerSieve
    {ℱ : Sheaf J (Type (max u v w'))} (U : C) (s s' : ℱ.obj.obj (op U))
    (hcover : Presheaf.equalizerSieve (F := ℱ.obj) s s' ∈ J U) :
    s = s' := by
  -- Use separatedness of the sheaf on the covering equalizer sieve.
  exact (((isSheaf_iff_isSheaf_of_type J ℱ.obj).1 ℱ.property).isSeparated _ hcover).ext
    (fun _ _ hf ↦ hf)

/-- Helper for Lemma 7.38.3: pointwise equality of germs along the family identifies the induced
stalk maps on `h_U^#` at every point of the family. -/
private lemma sheafifiedRepresentable_stalkwise_eq_of_pointwise_germ_eq
    {ι : Type w} (p : ι → Point.{w'} J)
    [LocallySmall.{w'} C]
    [HasWeakSheafify J (Type (max u v w'))]
    {ℱ : Sheaf J (Type (max u v w'))} (U : C)
    (α β :
      CategoryTheory.GrothendieckTopology.uliftSheafifiedRepresentable.{max u v w', u, v}
        J U ⟶ ℱ)
    (hαβ :
      ∀ i (x : (p i).fiber.obj U),
        (p i).toPresheafFiber U x ℱ.obj
            (J.uliftSheafifiedRepresentableHomEquiv ℱ U α) =
          (p i).toPresheafFiber U x ℱ.obj
            (J.uliftSheafifiedRepresentableHomEquiv ℱ U β)) :
    ∀ i, (p i).sheafFiber.map α = (p i).sheafFiber.map β := by
  intro i
  -- Apply the single-point stalk extensionality lemma pointwise across the family.
  exact sheafifiedRepresentable_stalk_map_ext_of_pointwise_germ_eq
    (q := p i) U α β (hαβ i)

/-- Helper for Lemma 7.38.3: after applying `ULift` to the fibers of a point, covering witnesses
for a sieve are still produced by the original point axiom. -/
private lemma ulift_cover_lift_of_point
    (q : Point.{w'} J) {X : C} (S : Sieve X) (hS : S ∈ J X)
    (x : ULift.{max u v, w'} (q.fiber.obj X)) :
    ∃ (Y : C) (f : Y ⟶ X) (_ : S f) (y : ULift.{max u v, w'} (q.fiber.obj Y)),
      ULift.up (q.fiber.map f y.down) = x := by
  -- This is exactly the forward direction of the previously established `ULift` cover-lift
  -- equivalence, applied to the original point axiom.
  exact (point_cover_lift_ulift_iff (q := q) (U := X) S).2
    (q.jointly_surjective S hS) x

/-- Helper for Lemma 7.38.3: the original and `ULift`-enlarged fibers of a point have equivalent
categories of elements. -/
private noncomputable def ulift_point_elements_equivalence
    (q : Point.{w'} J) :
    q.fiber.Elements ≌ (uliftPointFiberFunctor q).Elements where
  functor :=
    { obj := fun x ↦ ⟨x.1, ULift.up x.2⟩
      map := fun {X Y} f ↦
        CategoryOfElements.homMk _ _ f.1 (by
          -- The forward map keeps the base morphism and lifts only the element component.
          rcases X with ⟨X, x⟩
          rcases Y with ⟨Y, y⟩
          rcases f with ⟨f, hf⟩
          simpa [uliftPointFiberFunctor] using
            congrArg (ULift.up : q.fiber.obj Y → ULift.{max u v, w'} (q.fiber.obj Y)) hf) }
  inverse :=
    { obj := fun x ↦ ⟨x.1, x.2.down⟩
      map := fun {X Y} f ↦
        CategoryOfElements.homMk _ _ f.1 (by
          -- The inverse map keeps the base morphism and removes the `ULift` wrapper.
          rcases X with ⟨X, x⟩
          rcases Y with ⟨Y, y⟩
          rcases f with ⟨f, hf⟩
          simpa [uliftPointFiberFunctor] using
            congrArg (ULift.down : ULift.{max u v, w'} (q.fiber.obj Y) → q.fiber.obj Y) hf) }
  unitIso :=
    NatIso.ofComponents
      (fun x ↦
        CategoryOfElements.isoMk _ _ (Iso.refl _) (by
          -- Route correction: use the explicit `ULift` fiber isomorphism rather than reducing
          -- sigma objects in `Functor.Elements` by hand.
          simp))
      (fun f ↦ by
        -- Morphisms in the category of elements are determined by their base arrow.
        apply CategoryOfElements.ext
        simp)
  counitIso :=
    NatIso.ofComponents
      (fun x ↦
        CategoryOfElements.isoMk _ _ (Iso.refl _) (by
          -- The `ULift` wrapper is removed objectwise, so the element component is unchanged.
          simpa [uliftPointFiberFunctor] using ULift.up_down x.2))
      (fun f ↦ by
        -- Again, the objectwise `ULift` comparison leaves the underlying arrow unchanged.
        apply CategoryOfElements.ext
        simp)
  functor_unitIso_comp x := by
    -- The triangle identity is objectwise reflexive on the underlying base arrow.
    apply CategoryOfElements.ext
    simp

/-- Helper for Lemma 7.38.3: the enlarged point inherits cofilteredness from the original point by
transporting across the explicit equivalence of element categories. -/
private lemma ulift_point_isCofiltered
    (q : Point.{w'} J) :
    IsCofiltered (uliftPointFiberFunctor q).Elements := by
  -- Transfer the global cofilteredness invariant across the explicit `ULift` equivalence.
  exact IsCofiltered.of_equivalence (ulift_point_elements_equivalence (q := q))

/-- Helper for Lemma 7.38.3: the enlarged point still has an initially small category of elements,
again via the explicit `ULift` equivalence. -/
private lemma ulift_point_initiallySmall
    (q : Point.{w'} J) :
    InitiallySmall.{max u v w'} (uliftPointFiberFunctor q).Elements := by
  -- Transfer the existing small indexing category for `q` along the explicit equivalence functor.
  letI : EssentiallySmall.{max u v w'} q.fiber.Elements :=
    CategoryTheory.essentiallySmallSelf (C := q.fiber.Elements)
  letI : InitiallySmall.{max u v w'} q.fiber.Elements :=
    CategoryTheory.initiallySmall_of_essentiallySmall (J := q.fiber.Elements)
  exact initiallySmall_of_initial_of_initiallySmall
    (ulift_point_elements_equivalence (q := q)).functor

/-- Helper for Lemma 7.38.3: the enlarged point satisfies the covering-lift axiom because the
original point does and the `ULift` bookkeeping is explicit. -/
private lemma ulift_point_jointly_surjective
    (q : Point.{w'} J) {X : C} (S : Sieve X) (hS : S ∈ J X)
    (x : (uliftPointFiberFunctor q).obj X) :
    ∃ (Y : C) (f : Y ⟶ X) (_ : S f) (y : (uliftPointFiberFunctor q).obj Y),
      (uliftPointFiberFunctor q).map f y = x := by
  -- Reuse the original point axiom and then rewrite the transported fiber map into its canonical
  -- `ULift` form.
  obtain ⟨Y, f, hf, y, hy⟩ := ulift_cover_lift_of_point (q := q) S hS x
  refine ⟨Y, f, hf, y, ?_⟩
  simpa [uliftTypeFunctor, CategoryTheory.uliftFunctor_map] using hy

/-- Helper for Lemma 7.38.3: enlarge a point to the ambient universe by `ULift` on all fibers. -/
private noncomputable def ulift_point
    (q : Point.{w'} J) : Point.{max u v w'} J :=
  { fiber := uliftPointFiberFunctor q
    isCofiltered := ulift_point_isCofiltered (q := q)
    initiallySmall := ulift_point_initiallySmall (q := q)
    jointly_surjective := ulift_point_jointly_surjective (q := q) }

/-- Helper for Lemma 7.38.3: the family-wise `ULift` lifting package immediately descends to the
ordinary point fibers. -/
private lemma family_point_cover_lift_of_ulift
    {ι : Type w} (p : ι → Point.{w'} J) {X : C} (S : Sieve X)
    (hS :
      ∀ i (x : ULift.{max u v, w'} ((p i).fiber.obj X)),
        ∃ (Y : C) (g : Y ⟶ X) (_ : S g) (y : ULift.{max u v, w'} ((p i).fiber.obj Y)),
          ULift.up ((p i).fiber.map g y.down) = x) :
    ∀ i (x : (p i).fiber.obj X),
      ∃ (Y : C) (g : Y ⟶ X) (_ : S g) (y : (p i).fiber.obj Y),
        (p i).fiber.map g y = x := by
  intro i
  -- Remove the auxiliary `ULift` wrapper pointwise, using the single-point equivalence already
  -- proved earlier in the file.
  exact (point_cover_lift_ulift_iff (q := p i) (U := X) S).1 (hS i)

/-- Helper for Lemma 7.38.3: lifted point-fiber witnesses for an arbitrary sieve already reflect
covering because the original family reflects coverings for sieves of arrows. -/
private lemma covering_of_ulift_family_lifts
    {ι : Type w} (p : ι → Point.{w'} J)
    (hp : (ofObj p).IsConservativeFamilyOfPoints)
    [LocallySmall.{w'} C] [HasSheafify J (Type w')] [J.WEqualsLocallyBijective (Type w')]
    {X : C} (S : Sieve X)
    (hS :
      ∀ i (x : ULift.{max u v, w'} ((p i).fiber.obj X)),
        ∃ (Y : C) (g : Y ⟶ X) (_ : S g) (y : ULift.{max u v, w'} ((p i).fiber.obj Y)),
          ULift.up ((p i).fiber.map g y.down) = x) :
    S ∈ J X := by
  exact covering_of_ulift_family_lifts_core (p := p) hp (S := S) hS

/-- Helper for Lemma 7.38.3: if the original family is conservative, then the `ULift`-enlarged
family is conservative in the ambient point universe. -/
private lemma ulift_point_family_conservative
    {ι : Type w} (p : ι → Point.{w'} J)
    (hp : (ofObj p).IsConservativeFamilyOfPoints)
    [LocallySmall.{w'} C] [HasSheafify J (Type w')] [J.WEqualsLocallyBijective (Type w')] :
    (ofObj (fun i => ulift_point (p i))).IsConservativeFamilyOfPoints := by
  -- Route correction: use the owner constructor `mk'` directly and reflect covering of an
  -- arbitrary sieve via the explicit `ofArrows` reduction proved just above.
  refine ObjectProperty.IsConservativeFamilyOfPoints.mk' ?_
  intro X S hS
  exact covering_of_ulift_family_lifts (p := p) hp S (fun i x ↦
    hS ⟨ulift_point (p i), ofObj_apply (fun i ↦ ulift_point (p i)) i⟩ x)

/-- Helper for Lemma 7.38.3: the original point and its `ULift` enlargement induce canonically
isomorphic fiber functors on large type-valued presheaves. -/
private lemma ulift_point_presheafFiberHom_compatible
    (q : Point.{w'} J) (P : Cᵒᵖ ⥤ Type (max u v w')) :
    ∀ ⦃X Y : C⦄ (f : X ⟶ Y) (x : (ulift_point q).fiber.obj X),
      P.map f.op ≫ q.toPresheafFiber X x.down P =
        q.toPresheafFiber Y ((ulift_point q).fiber.map f x).down P := by
  intro X Y f x
  -- Remove the lifted point fiber back to the original point fiber before using `toPresheafFiber_w`.
  simpa [ulift_point, uliftPointFiberFunctor] using
    (q.toPresheafFiber_w (P := P) f x.down)

/-- Helper for Lemma 7.38.3: the forward comparison map on presheaf fibers removes the `ULift`
wrapper from point-fiber generators. -/
private noncomputable def ulift_point_presheafFiberHom
    (q : Point.{w'} J) (P : Cᵒᵖ ⥤ Type (max u v w')) :
    (ulift_point q).presheafFiber.obj P ⟶ q.presheafFiber.obj P :=
  (ulift_point q).presheafFiberDesc
    (fun X x ↦ q.toPresheafFiber X x.down P)
    (ulift_point_presheafFiberHom_compatible (q := q) P)

/-- Helper for Lemma 7.38.3: the forward comparison map evaluates on a lifted generator by simply
forgetting `ULift`. -/
private lemma ulift_point_toPresheafFiber_presheafFiberHom
    (q : Point.{w'} J) (P : Cᵒᵖ ⥤ Type (max u v w')) (X : C)
    (x : (ulift_point q).fiber.obj X) :
    (ulift_point q).toPresheafFiber X x P ≫ ulift_point_presheafFiberHom (q := q) P =
      q.toPresheafFiber X x.down P := by
  -- Evaluate the descent map on the canonical colimit generator for the lifted point.
  simpa [ulift_point_presheafFiberHom] using
    ((ulift_point q).toPresheafFiber_presheafFiberDesc
      (fun X x ↦ q.toPresheafFiber X x.down P)
      (ulift_point_presheafFiberHom_compatible (q := q) P) X x)

/-- Helper for Lemma 7.38.3: the reverse comparison from the original presheaf fiber to the
lifted one is compatible with pullback along arrows. -/
private lemma ulift_point_presheafFiberInv_compatible
    (q : Point.{w'} J) (P : Cᵒᵖ ⥤ Type (max u v w')) :
    ∀ ⦃X Y : C⦄ (f : X ⟶ Y) (x : q.fiber.obj X),
      P.map f.op ≫ (ulift_point q).toPresheafFiber X (ULift.up x) P =
        (ulift_point q).toPresheafFiber Y (ULift.up (q.fiber.map f x)) P := by
  intro X Y f x
  -- The lifted point applies `ULift.up` after the original fiber map, so the compatibility is
  -- exactly `toPresheafFiber_w` for `ulift_point q`.
  simpa [ulift_point, uliftPointFiberFunctor] using
    ((ulift_point q).toPresheafFiber_w (P := P) f (ULift.up x))

/-- Helper for Lemma 7.38.3: the reverse comparison map on presheaf fibers adds the `ULift`
wrapper back to point-fiber generators. -/
private noncomputable def ulift_point_presheafFiberInv
    (q : Point.{w'} J) (P : Cᵒᵖ ⥤ Type (max u v w')) :
    q.presheafFiber.obj P ⟶ (ulift_point q).presheafFiber.obj P :=
  q.presheafFiberDesc
    (fun X x ↦ (ulift_point q).toPresheafFiber X (ULift.up x) P)
    (ulift_point_presheafFiberInv_compatible (q := q) P)

/-- Helper for Lemma 7.38.3: the reverse comparison map evaluates on an original generator by
reintroducing `ULift`. -/
private lemma point_toPresheafFiber_presheafFiberInv
    (q : Point.{w'} J) (P : Cᵒᵖ ⥤ Type (max u v w')) (X : C) (x : q.fiber.obj X) :
    q.toPresheafFiber X x P ≫ ulift_point_presheafFiberInv (q := q) P =
      (ulift_point q).toPresheafFiber X (ULift.up x) P := by
  -- Evaluate the descent map on the canonical colimit generator for the original point.
  simpa [ulift_point_presheafFiberInv] using
    (q.toPresheafFiber_presheafFiberDesc
      (fun X x ↦ (ulift_point q).toPresheafFiber X (ULift.up x) P)
      (ulift_point_presheafFiberInv_compatible (q := q) P) X x)

/-- Helper for Lemma 7.38.3: the forward and reverse comparison maps on a presheaf fiber are
inverse after testing on lifted generators. -/
private lemma ulift_point_presheafFiberHom_inv
    (q : Point.{w'} J) (P : Cᵒᵖ ⥤ Type (max u v w')) :
    ulift_point_presheafFiberHom (q := q) P ≫ ulift_point_presheafFiberInv (q := q) P = 𝟙 _ := by
  -- The comparison is determined on colimit generators, where `ULift.up` then `ULift.down`
  -- returns the original lifted element.
  apply (ulift_point q).presheafFiber_hom_ext
  intro X x
  repeat rw [← Category.assoc]
  rw [ulift_point_toPresheafFiber_presheafFiberHom]
  rw [point_toPresheafFiber_presheafFiberInv]
  cases x
  rfl

/-- Helper for Lemma 7.38.3: the reverse and forward comparison maps on a presheaf fiber are
inverse after testing on original generators. -/
private lemma ulift_point_presheafFiberInv_hom
    (q : Point.{w'} J) (P : Cᵒᵖ ⥤ Type (max u v w')) :
    ulift_point_presheafFiberInv (q := q) P ≫ ulift_point_presheafFiberHom (q := q) P = 𝟙 _ := by
  -- The same generator test removes `ULift` immediately after it was introduced.
  apply q.presheafFiber_hom_ext
  intro X x
  repeat rw [← Category.assoc]
  rw [point_toPresheafFiber_presheafFiberInv]
  rw [ulift_point_toPresheafFiber_presheafFiberHom]
  rfl

/-- Helper for Lemma 7.38.3: the componentwise presheaf-fiber comparison is natural in the
presheaf argument. -/
private lemma ulift_point_presheafFiberObjIso_hom_naturality
    (q : Point.{w'} J) {P Q : Cᵒᵖ ⥤ Type (max u v w')} (f : P ⟶ Q) :
    (ulift_point q).presheafFiber.map f ≫
        ulift_point_presheafFiberHom (q := q) Q =
      ulift_point_presheafFiberHom (q := q) P ≫ q.presheafFiber.map f := by
  -- Compare both composites on lifted generators and reduce to naturality of the original point
  -- fiber maps.
  apply (ulift_point q).presheafFiber_hom_ext
  intro X x
  rw [← Category.assoc, ← Category.assoc]
  rw [(ulift_point q).toPresheafFiber_naturality f X x]
  rw [Category.assoc]
  rw [ulift_point_toPresheafFiber_presheafFiberHom]
  rw [ulift_point_toPresheafFiber_presheafFiberHom]
  simpa [ulift_point, uliftPointFiberFunctor] using
    (q.toPresheafFiber_naturality f X x.down).symm

/-- Helper for Lemma 7.38.3: for a fixed presheaf, the original point and its `ULift`
enlargement have canonically isomorphic fibers. -/
private noncomputable def ulift_point_presheafFiberObjIso
    (q : Point.{w'} J) (P : Cᵒᵖ ⥤ Type (max u v w')) :
    (ulift_point q).presheafFiber.obj P ≅ q.presheafFiber.obj P :=
  { hom := ulift_point_presheafFiberHom (q := q) P
    inv := ulift_point_presheafFiberInv (q := q) P
    hom_inv_id := ulift_point_presheafFiberHom_inv (q := q) P
    inv_hom_id := ulift_point_presheafFiberInv_hom (q := q) P }

/-- Helper for Lemma 7.38.3: the objectwise comparison isomorphisms assemble naturally into a
presheaf-fiber isomorphism. -/
private lemma ulift_point_presheafFiberObjIso_naturality
    (q : Point.{w'} J) {P Q : Cᵒᵖ ⥤ Type (max u v w')} (f : P ⟶ Q) :
    (ulift_point q).presheafFiber.map f ≫
        (ulift_point_presheafFiberObjIso (q := q) Q).hom =
      (ulift_point_presheafFiberObjIso (q := q) P).hom ≫ q.presheafFiber.map f := by
  -- This is the generatorwise naturality already proved for the underlying forward comparison.
  simpa [ulift_point_presheafFiberObjIso] using
    (ulift_point_presheafFiberObjIso_hom_naturality (q := q) f)

/-- Helper for Lemma 7.38.3: the original point and its `ULift` enlargement induce canonically
isomorphic fiber functors on large type-valued presheaves. -/
private noncomputable def ulift_point_presheafFiberIso
    (q : Point.{w'} J) :
    ((ulift_point q).presheafFiber :
      (Cᵒᵖ ⥤ Type (max u v w')) ⥤ Type (max u v w')) ≅ q.presheafFiber :=
  NatIso.ofComponents
    (ulift_point_presheafFiberObjIso (q := q))
    (ulift_point_presheafFiberObjIso_naturality (q := q))

/-- Helper for Lemma 7.38.3: equality of sheaf-fiber maps for the `ULift`-enlarged point should
be equivalent to equality for the original point. -/
private lemma ulift_point_sheafFiber_map_eq_iff
    (q : Point.{w'} J)
    {ℱ 𝒢 : Sheaf J (Type (max u v w'))} {φ ψ : ℱ ⟶ 𝒢} :
    (ulift_point q).sheafFiber.map φ = (ulift_point q).sheafFiber.map ψ ↔
      q.sheafFiber.map φ = q.sheafFiber.map ψ := by
  let e : (ulift_point q).sheafFiber ≅ q.sheafFiber :=
    Functor.isoWhiskerLeft (sheafToPresheaf J (Type (max u v w')))
      (ulift_point_presheafFiberIso (q := q))
  constructor
  · intro h
    ext z
    obtain ⟨z', rfl⟩ := ((e.app ℱ).toEquiv).surjective z
    have hz :
        e.hom.app 𝒢 ((ulift_point q).sheafFiber.map φ z') =
          e.hom.app 𝒢 ((ulift_point q).sheafFiber.map ψ z') := by
      simpa using congrArg (e.hom.app 𝒢) (congrFun h z')
    -- Transport equality across the comparison isomorphism by naturality of the comparison map.
    exact (NatTrans.naturality_apply e.hom φ z').symm.trans <|
      hz.trans (NatTrans.naturality_apply e.hom ψ z')
  · intro h
    ext z
    obtain ⟨z', rfl⟩ := ((e.symm.app ℱ).toEquiv).surjective z
    have hz :
        e.inv.app 𝒢 (q.sheafFiber.map φ z') =
          e.inv.app 𝒢 (q.sheafFiber.map ψ z') := by
      simpa using congrArg (e.inv.app 𝒢) (congrFun h z')
    -- The inverse comparison map transports equality in the reverse direction.
    exact (NatTrans.naturality_apply e.inv φ z').symm.trans <|
      hz.trans (NatTrans.naturality_apply e.inv ψ z')

/-- Helper for Lemma 7.38.3: the conservative family should be jointly faithful on large
type-valued sheaves once the small-to-large universe bridge is supplied. -/
private lemma sheaf_hom_ext_of_stalkwise_large_type
    {ι : Type w} (p : ι → Point.{w'} J)
    (hp : (ofObj p).IsConservativeFamilyOfPoints)
    [LocallySmall.{w'} C] [HasSheafify J (Type w')] [J.WEqualsLocallyBijective (Type w')]
    {ℱ 𝒢 : Sheaf J (Type (max u v w'))} {φ ψ : ℱ ⟶ 𝒢}
    (hφ : ∀ i, (p i).sheafFiber.map φ = (p i).sheafFiber.map ψ) :
    φ = ψ := by
  letI : LocallySmall.{max u v w'} C := by infer_instance
  let p' : ι → Point.{max u v w'} J := fun i ↦ ulift_point (p i)
  have hp' : (ofObj p').IsConservativeFamilyOfPoints :=
    ulift_point_family_conservative (p := p) hp
  have hφ' : ∀ i, (p' i).sheafFiber.map φ = (p' i).sheafFiber.map ψ := by
    intro i
    -- Transport the original stalkwise equality to the lifted family through the comparison iso.
    exact (ulift_point_sheafFiber_map_eq_iff (q := p i)).2 (hφ i)
  -- Apply Lemma 7.38.2 to the lifted conservative family, which lives in the ambient universe.
  exact sheaf_hom_ext_of_stalkwise (p := p') hp' hφ'

/-- Helper for Lemma 7.38.3: distinct maps out of `h_U^#` are detected on the stalk of some
point in a conservative family. -/
private lemma stalkwise_ne_of_ne_sheafifiedRepresentable_hom
    {ι : Type w} (p : ι → Point.{w'} J)
    (hp : (ofObj p).IsConservativeFamilyOfPoints)
    [LocallySmall.{w'} C] [HasSheafify J (Type w')] [J.WEqualsLocallyBijective (Type w')]
    {ℱ : Sheaf J (Type (max u v w'))} (U : C)
    (α β :
      CategoryTheory.GrothendieckTopology.uliftSheafifiedRepresentable.{max u v w', u, v}
        J U ⟶ ℱ)
    (hαβ : α ≠ β) :
    ∃ i, (p i).sheafFiber.map α ≠ (p i).sheafFiber.map β := by
  classical
  by_contra hstalk
  push Not at hstalk
  -- If every stalk map were equal, joint faithfulness of the conservative family would force
  -- `α = β`.
  exact hαβ <|
    sheaf_hom_ext_of_stalkwise_large_type (p := p) hp hstalk

/-- Helper for Lemma 7.38.3: a stalk-level difference between two maps out of `h_U^#` comes from
some actual point-fiber element `x ∈ u_i(U)` separating the corresponding germs. -/
private lemma exists_point_separating_germ_of_ne_sheafifiedRepresentable_hom
    {ι : Type w} (p : ι → Point.{w'} J)
    (hp : (ofObj p).IsConservativeFamilyOfPoints)
    [LocallySmall.{w'} C] [HasSheafify J (Type w')] [J.WEqualsLocallyBijective (Type w')]
    [HasWeakSheafify J (Type (max u v w'))]
    {ℱ : Sheaf J (Type (max u v w'))} (U : C)
    (α β :
      CategoryTheory.GrothendieckTopology.uliftSheafifiedRepresentable.{max u v w', u, v}
        J U ⟶ ℱ)
    (hαβ : α ≠ β) :
    ∃ i, ∃ x : (p i).fiber.obj U,
      (p i).toPresheafFiber U x ℱ.obj
          (J.uliftSheafifiedRepresentableHomEquiv ℱ U α) ≠
        (p i).toPresheafFiber U x ℱ.obj
          (J.uliftSheafifiedRepresentableHomEquiv ℱ U β) := by
  classical
  obtain ⟨i, hi⟩ :=
    stalkwise_ne_of_ne_sheafifiedRepresentable_hom (p := p) hp U α β hαβ
  have hz :
      ∃ z,
        (p i).sheafFiber.map α z ≠
          (p i).sheafFiber.map β z := by
    by_contra hz
    push Not at hz
    exact hi <| by
      funext z
      exact hz z
  obtain ⟨z, hz⟩ := hz
  obtain ⟨x, rfl⟩ := point_sheafifiedRepresentable_stalkElem_surjective (q := p i) U z
  refine ⟨i, x, ?_⟩
  -- Unwind the chosen stalk generator back to the germ of the corresponding section at `x`.
  intro hEq
  exact hz <|
    (sheafifiedRepresentable_stalk_map_eq_iff (q := p i) U α β x).2 hEq

/-- Helper for Lemma 7.38.3: pointwise equality of germs forces equality of the two associated
morphisms out of `h_U^#`. -/
private lemma sheafifiedRepresentable_hom_eq_of_pointwise_germ_eq
    {ι : Type w} (p : ι → Point.{w'} J)
    (hp : (ofObj p).IsConservativeFamilyOfPoints)
    [LocallySmall.{w'} C] [HasSheafify J (Type w')] [J.WEqualsLocallyBijective (Type w')]
    [HasWeakSheafify J (Type (max u v w'))]
    {ℱ : Sheaf J (Type (max u v w'))} (U : C)
    (α β :
      CategoryTheory.GrothendieckTopology.uliftSheafifiedRepresentable.{max u v w', u, v}
        J U ⟶ ℱ)
    (hαβ :
      ∀ i (x : (p i).fiber.obj U),
        (p i).toPresheafFiber U x ℱ.obj
            (J.uliftSheafifiedRepresentableHomEquiv ℱ U α) =
        (p i).toPresheafFiber U x ℱ.obj
            (J.uliftSheafifiedRepresentableHomEquiv ℱ U β)) :
    α = β := by
  let eU := J.uliftSheafifiedRepresentableHomEquiv ℱ U
  let s : ℱ.obj.obj (op U) := eU α
  let s' : ℱ.obj.obj (op U) := eU β
  -- Route correction: follow the source proof and make the equalizer sieve covering from
  -- pointwise germ equality, then use sheaf separatedness on that covering.
  have hcover :
      Presheaf.equalizerSieve (F := ℱ.obj) s s' ∈ J U := by
    simpa [s, s'] using
      covering_equalizerSieve_of_pointwise_germ_eq (p := p) hp U s s'
        (by simpa [s, s'] using hαβ)
  have hs : s = s' :=
    sections_eq_of_covering_equalizerSieve (ℱ := ℱ) U s s' hcover
  exact eU.injective <| by simpa [s, s'] using hs

/-- Helper for Lemma 7.38.3: the large separating-sections criterion implies conservativity for the
original small family of point stalk functors. -/
lemma small_conservative_of_large_separating_sections
    {ι : Type w} (p : ι → Point.{w'} J)
    [LocallySmall.{w'} C]
    (hsep :
      ∀ ⦃ℱ : Sheaf J (Type (max u v w'))⦄ (U : C) (s s' : ℱ.obj.obj (op U)),
        s ≠ s' →
          ∃ i : ι, ∃ x : (p i).fiber.obj U,
            (p i).toPresheafFiber U x ℱ.obj s ≠ (p i).toPresheafFiber U x ℱ.obj s') :
    ∀ ⦃ℱ 𝒢 : Sheaf J (Type w')⦄ (φ : ℱ ⟶ 𝒢),
      (∀ i : ι, IsIso ((p i).sheafFiber.map φ)) → IsIso φ := by
  intro ℱ 𝒢 φ hφ
  let Fup : Sheaf J (Type w') ⥤ Sheaf J (Type (max u v w')) :=
    sheafCompose J
      (CategoryTheory.uliftFunctor.{max u v, w'} :
        Type w' ⥤ Type (max u v w'))
  have hFup :
      ∀ i : ι, IsIso ((p i).sheafFiber.map (Fup.map φ)) := by
    intro i
    let _ : IsIso ((p i).sheafFiber.map φ) := hφ i
    exact
      ((MorphismProperty.isomorphisms _).arrow_mk_iso_iff
        (((Functor.mapArrowFunctor _ _).mapIso
          ((p i).sheafFiberCompIso
            (CategoryTheory.uliftFunctor.{max u v, w'} :
              Type w' ⥤ Type (max u v w')))).app (Arrow.mk φ))).2
        (inferInstanceAs
          (IsIso
            ((CategoryTheory.uliftFunctor.{max u v, w'} :
              Type w' ⥤ Type (max u v w')).map ((p i).sheafFiber.map φ))))
  let _ : ∀ i : ι, IsIso ((p i).sheafFiber.map (Fup.map φ)) := hFup
  let _ : IsIso (Fup.map φ) :=
    (stalkFamily_jointlyReflectsIsomorphisms_of_separating_sections_large
      (p := p) hsep).isIso (Fup.map φ)
  -- Reflect the lifted isomorphism back through the `ULift`-whiskering functor on sheaves.
  exact isIso_of_reflects_iso φ Fup

/-- Helper for Lemma 7.38.3: for small set-valued sheaves, equality of two germs in a point
fiber is witnessed after pulling back to an arrow in the equalizer sieve. -/
private lemma pointwise_germ_eq_gives_equalizer_lift_small
    (q : Point.{w'} J) {ℱ : Sheaf J (Type w')} (U : C)
    (s s' : ℱ.obj.obj (op U)) {x : q.fiber.obj U}
    (hx : q.toPresheafFiber U x ℱ.obj s = q.toPresheafFiber U x ℱ.obj s') :
    ∃ (Y : C) (g : Y ⟶ U) (_ : Presheaf.equalizerSieve (F := ℱ.obj) s s' g)
      (y : q.fiber.obj Y), q.fiber.map g y = x := by
  obtain ⟨Y, g, y, hy, hEq⟩ :=
    (point_fiber_eq_iff_of_type (q := q) (P := ℱ.obj) U x s s').1 hx
  exact ⟨Y, g, hEq, y, hy⟩

/-- Helper for Lemma 7.38.3: a covering equalizer sieve forces equality of two sections of a
small set-valued sheaf. -/
private lemma sections_eq_of_covering_equalizerSieve_small
    {ℱ : Sheaf J (Type w')} (U : C) (s s' : ℱ.obj.obj (op U))
    (hcover : Presheaf.equalizerSieve (F := ℱ.obj) s s' ∈ J U) :
    s = s' := by
  exact (((isSheaf_iff_isSheaf_of_type J ℱ.obj).1 ℱ.property).isSeparated _ hcover).ext
    (fun _ _ hf ↦ hf)

/-- Helper for Lemma 7.38.3: the section-separation criterion makes the small stalk family
jointly faithful on set-valued sheaves. -/
private lemma stalkFamily_jointlyFaithful_of_separating_sections_small
    {ι : Type w} (p : ι → Point.{w'} J)
    (hsep :
      ∀ ⦃ℱ : Sheaf J (Type w')⦄ (U : C) (s s' : ℱ.obj.obj (op U)),
        s ≠ s' →
          ∃ i : ι, ∃ x : (p i).fiber.obj U,
            (p i).toPresheafFiber U x ℱ.obj s ≠ (p i).toPresheafFiber U x ℱ.obj s') :
    JointlyFaithful
      (fun i : ι ↦ ((p i).sheafFiber : Sheaf J (Type w') ⥤ Type w')) := by
  refine ⟨?_⟩
  intro ℱ 𝒢 φ ψ hφ
  ext U s
  by_contra hs
  obtain ⟨i, x, hx⟩ := hsep U.unop ((φ.hom.app U) s) ((ψ.hom.app U) s) hs
  have hEqStalk :
      ((p i).sheafFiber.map φ) ((p i).toPresheafFiber U.unop x ℱ.obj s) =
        ((p i).sheafFiber.map ψ) ((p i).toPresheafFiber U.unop x ℱ.obj s) := by
    exact congr_fun (hφ i) ((p i).toPresheafFiber U.unop x ℱ.obj s)
  have hLeft :
      ((p i).sheafFiber.map φ) ((p i).toPresheafFiber U.unop x ℱ.obj s) =
        (p i).toPresheafFiber U.unop x 𝒢.obj ((φ.hom.app U) s) := by
    simpa using congrFun ((p i).toPresheafFiber_naturality φ.hom U.unop x) s
  have hRight :
      ((p i).sheafFiber.map ψ) ((p i).toPresheafFiber U.unop x ℱ.obj s) =
        (p i).toPresheafFiber U.unop x 𝒢.obj ((ψ.hom.app U) s) := by
    simpa using congrFun ((p i).toPresheafFiber_naturality ψ.hom U.unop x) s
  exact hx (hLeft.symm.trans (hEqStalk.trans hRight))

/-- Lemma 7.38.3: a family of points of a site is conservative if and only if every pair of
distinct local sections of a set-valued sheaf is separated by their germs at some point of one of
the fibers `u_i(U)`.

The source statement is set-valued in the point universe. The small sheafification and
`W =` local-bijectivity assumptions are the canonical owner-side bridge used to turn the
pointwise lifting condition for a sieve into a covering proof. -/
theorem isConservativePointFamily_iff_exists_point_separating_sections
    {ι : Type w} (p : ι → Point.{w'} J)
    [LocallySmall.{w'} C] [HasSheafify J (Type w')] [J.WEqualsLocallyBijective (Type w')] :
    (ofObj p).IsConservativeFamilyOfPoints ↔
      ∀ ⦃ℱ : Sheaf J (Type w')⦄ (U : C) (s s' : ℱ.obj.obj (op U)),
        s ≠ s' →
          ∃ i : ι, ∃ x : (p i).fiber.obj U,
            (p i).toPresheafFiber U x ℱ.obj s ≠ (p i).toPresheafFiber U x ℱ.obj s' := by
  constructor
  · intro hp
    -- Source route: compare the two maps `h_U^# ⟶ ℱ` corresponding to `s` and `s'`; if every
    -- point has equal germs, the equalizer sieve is covering by conservativity, hence the two
    -- sheaf sections are equal.
    intro ℱ U s s' hs
    by_contra hnone
    push Not at hnone
    have hcover : Presheaf.equalizerSieve (F := ℱ.obj) s s' ∈ J U := by
      exact covering_of_ulift_family_lifts_core (p := p) hp
          (S := Presheaf.equalizerSieve (F := ℱ.obj) s s') <| by
        intro i x
        obtain ⟨Y, g, hg, y, hy⟩ :=
          pointwise_germ_eq_gives_equalizer_lift_small (q := p i) U s s'
            (x := x.down) (hnone i x.down)
        refine ⟨Y, g, hg, ULift.up.{max u v, w'} y, ?_⟩
        cases x
        simpa using
          congrArg
            (ULift.up.{max u v, w'} :
              (p i).fiber.obj U → ULift.{max u v, w'} ((p i).fiber.obj U)) hy
    exact hs (sections_eq_of_covering_equalizerSieve_small (ℱ := ℱ) U s s' hcover)
  · intro hsep
    -- Source route: convert the section-separation criterion into the owner criterion that every
    -- sheaf morphism inducing isomorphisms on all point stalks is itself an isomorphism.
    rw [isConservativePointFamily_iff]
    intro ℱ 𝒢 φ hφ
    let jf := stalkFamily_jointlyFaithful_of_separating_sections_small (p := p) hsep
    let _ : ∀ i : ι, IsIso ((p i).sheafFiber.map φ) := hφ
    exact (CategoryTheory.JointlyFaithful.jointlyReflectsIsomorphisms jf).isIso φ

end GrothendieckTopology

end CategoryTheory
