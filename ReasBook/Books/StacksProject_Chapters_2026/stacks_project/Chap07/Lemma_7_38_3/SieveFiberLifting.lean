module

public import stacks_project.Chap07.Lemma_7_38_3.SeparatingSections

@[expose] public section

open CategoryTheory Opposite
open CategoryTheory.Limits
open CategoryTheory.ObjectProperty

universe w v u w' w''

namespace CategoryTheory

namespace GrothendieckTopology

attribute [local instance] Types.instFunLike Types.instConcreteCategory

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}

/-- Helper for Lemma 7.38.3: the image sieve of the canonical universe-lifted sieve inclusion at
the identity section is the original sieve. -/
lemma imageSieve_uliftFunctorInclusion_id
    {U : C} (S : Sieve U) :
    Presheaf.imageSieve S.uliftFunctorInclusion
        (show (CategoryTheory.uliftYoneda.obj.{max u v w'} U).obj (op U) from
          ULift.up (𝟙 U)) =
      S := by
  -- Unpack the image-sieve definition: the lifted generator at the identity sees exactly the
  -- original arrows of `S`.
  ext V g
  constructor
  · rintro ⟨t, ht⟩
    change ULift.up t.down.1 = ULift.up (g ≫ 𝟙 U) at ht
    have ht' : t.down.1 = g := by
      simpa using congrArg ULift.down ht
    simpa [ht'] using t.down.2
  · intro hg
    refine ⟨ULift.up ⟨g, by simpa using hg⟩, ?_⟩
    change ULift.up g = ULift.up (g ≫ 𝟙 U)
    simp

/-- Helper for Lemma 7.38.3: every element of a type-valued point fiber is represented by some
section at some stage of the filtered colimit. -/
lemma point_presheafFiber_jointly_surjective_of_type
    (q : Point.{w'} J) {P : Cᵒᵖ ⥤ Type w''}
    [Limits.HasColimitsOfSize.{w', w'} (Type w'')]
    (p : q.presheafFiber.obj P) :
    ∃ (X : C) (x : q.fiber.obj X) (z : P.obj (op X)),
      q.toPresheafFiber X x P z = p := by
  -- Unpack the concrete colimit defining the point fiber in `Type`.
  obtain ⟨⟨X, x⟩, z, h⟩ :=
    Types.jointly_surjective_of_isColimit (q.isColimitPresheafFiberCocone P) p
  exact ⟨X, x, z, h⟩

/-- Helper for Lemma 7.38.3: two elements of a type-valued point fiber can be represented at a
common stage of the filtered colimit. -/
lemma point_presheafFiber_jointly_surjective₂_of_type
    (q : Point.{w'} J) {P : Cᵒᵖ ⥤ Type w''}
    [Limits.HasColimitsOfSize.{w', w'} (Type w'')]
    (p₁ p₂ : q.presheafFiber.obj P) :
    ∃ (X : C) (x : q.fiber.obj X) (z₁ z₂ : P.obj (op X)),
      q.toPresheafFiber X x P z₁ = p₁ ∧ q.toPresheafFiber X x P z₂ = p₂ := by
  -- Use the filtered-colimit description to choose simultaneous representatives.
  obtain ⟨⟨X, x⟩, z₁, z₂, h₁, h₂⟩ :=
    Types.FilteredColimit.jointly_surjective_of_isColimit₂
      (q.isColimitPresheafFiberCocone P) p₁ p₂
  exact ⟨X, x, z₁, z₂, h₁, h₂⟩

/-- Helper for Lemma 7.38.3: if every point of `u(U)` lifts through a sieve `S`, then the map on
point fibers induced by `S.uliftFunctorInclusion` is surjective. -/
lemma point_uliftFunctorInclusion_presheafFiber_surjective_of_lifts
    (q : Point.{w'} J) {U : C} (S : Sieve U)
    (hlift :
      ∀ x : q.fiber.obj U,
        ∃ (Y : C) (g : Y ⟶ U) (_ : S g) (y : q.fiber.obj Y), q.fiber.map g y = x) :
    Function.Surjective
      (q.presheafFiber.map (Sieve.uliftFunctorInclusion.{max u v w'} S)) := by
  intro p
  -- First reduce the target fiber element to the canonical generator coming from some `x ∈ u(U)`.
  obtain ⟨x, rfl⟩ := point_uliftYoneda_generator_surjective (q := q) U p
  obtain ⟨Y, g, hg, y, hy⟩ := hlift x
  refine ⟨q.toPresheafFiber Y y (Sieve.uliftFunctor.{max u v w'} S)
      (ULift.up ⟨g, hg⟩), ?_⟩
  -- Naturality computes the image of the lifted arrow under the sieve inclusion.
  have hη :
      q.presheafFiber.map (Sieve.uliftFunctorInclusion.{max u v w'} S)
          (q.toPresheafFiber Y y (Sieve.uliftFunctor.{max u v w'} S)
            (ULift.up ⟨g, hg⟩)) =
        q.toPresheafFiber Y y (CategoryTheory.uliftYoneda.{max u v w'}.obj U)
          (ULift.up g) := by
    simpa using
      congrFun
        (q.toPresheafFiber_naturality
          (Sieve.uliftFunctorInclusion.{max u v w'} S) Y y)
        (ULift.up ⟨g, hg⟩)
  -- The represented arrow `g` lands at the chosen element `x`, so this is exactly the canonical
  -- generator at `x`.
  have hgerm :
      q.toPresheafFiber Y y (CategoryTheory.uliftYoneda.{max u v w'}.obj U)
          (ULift.up g) =
        point_uliftYoneda_generator (q := q) U x := by
    have hw :=
      congrFun
        (q.toPresheafFiber_w g y
          (CategoryTheory.uliftYoneda.{max u v w'}.obj U))
        (show (CategoryTheory.uliftYoneda.{max u v w'}.obj U).obj (op U) from
          ULift.up (𝟙 U))
    simpa [point_uliftYoneda_generator, CategoryTheory.uliftYoneda, hy] using hw
  exact hη.trans hgerm

/-- Helper for Lemma 7.38.3: the universe-lifted inclusion of a sieve is objectwise injective. -/
lemma uliftFunctorInclusion_app_injective
    {U : C} (S : Sieve U) (X : Cᵒᵖ) :
    Function.Injective ((Sieve.uliftFunctorInclusion.{max u v w'} S).app X) := by
  intro a b h
  cases a with
  | up a =>
    cases b with
    | up b =>
      -- Forget the outer `ULift`; the inclusion only remembers the underlying arrow of the sieve.
      have hab : a.1 = b.1 := by
        simpa using congrArg ULift.down h
      have hab' : a = b := Subtype.ext hab
      subst hab'
      rfl

/-- Helper for Lemma 7.38.3: pointwise lift witnesses through `S` make the induced map on point
fibers bijective. -/
lemma point_uliftFunctorInclusion_presheafFiber_bijective_of_lifts
    (q : Point.{w'} J) {U : C} (S : Sieve U)
    [LocallySmall.{w'} C]
    (hlift :
      ∀ x : q.fiber.obj U,
        ∃ (Y : C) (g : Y ⟶ U) (_ : S g) (y : q.fiber.obj Y), q.fiber.map g y = x) :
    Function.Bijective
      (q.presheafFiber.map (Sieve.uliftFunctorInclusion.{max u v w'} S)) := by
  let _ : Presheaf.IsLocallyInjective J (Sieve.uliftFunctorInclusion.{max u v w'} S) :=
    -- Local injectivity is immediate because the lifted sieve inclusion is objectwise injective.
    Presheaf.isLocallyInjective_of_injective J
      (Sieve.uliftFunctorInclusion.{max u v w'} S)
      (uliftFunctorInclusion_app_injective (S := S))
  constructor
  · -- Once local injectivity is available, the owner theorem upgrades it to injectivity on fibers.
    exact q.toPresheafFiber_map_injective (Sieve.uliftFunctorInclusion.{max u v w'} S)
  · -- Surjectivity is the concrete part: every generator `x ∈ u(U)` already lifts through `S`.
    exact point_uliftFunctorInclusion_presheafFiber_surjective_of_lifts (q := q) S hlift

/-- Helper for Lemma 7.38.3: the image sieve of the lifted sieve inclusion on the section
represented by `g` is the pullback of the original sieve along `g`. -/
lemma imageSieve_uliftFunctorInclusion_eq_pullback
    {U : C} (S : Sieve U) {V : C} (g : V ⟶ U) :
    Presheaf.imageSieve S.uliftFunctorInclusion
        (show (CategoryTheory.uliftYoneda.obj.{max u v w'} U).obj (op V) from ULift.up g) =
      S.pullback g := by
  let s : (CategoryTheory.uliftYoneda.obj.{max u v w'} U).obj (op U) := ULift.up (𝟙 U)
  have hpull := Presheaf.pullback_imageSieve S.uliftFunctorInclusion s g
  rw [imageSieve_uliftFunctorInclusion_id (S := S)] at hpull
  have hmap :
      Presheaf.imageSieve S.uliftFunctorInclusion
          (show (CategoryTheory.uliftYoneda.obj.{max u v w'} U).obj (op V) from ULift.up g) =
      Presheaf.imageSieve S.uliftFunctorInclusion
          ((CategoryTheory.uliftYoneda.obj.{max u v w'} U).map g.op s) := by
    ext W h
    simp [Presheaf.imageSieve, s]
  exact hmap.trans hpull.symm

/-- Helper for Lemma 7.38.3: the image sieve of the small shrink-functor inclusion at the
identity section is exactly the original sieve. -/
lemma imageSieve_shrinkFunctor_ι_id
    [LocallySmall.{w'} C] {U : C} (S : Sieve U) :
    Presheaf.imageSieve (Sieve.shrinkFunctor.{w'} S).ι
        (show (shrinkYoneda.{w'}.obj U).obj (op U) from
          shrinkYonedaObjObjEquiv.symm (𝟙 U)) =
      S := by
  -- Unpack the image-sieve definition: the shrink-functor generator at the identity sees exactly
  -- the arrows already lying in `S`.
  ext V g
  constructor
  · rintro ⟨t, ht⟩
    have ht' :
        t.1 = shrinkYonedaObjObjEquiv.symm g := by
      calc
        t.1 = ((Sieve.shrinkFunctor.{w'} S).ι.app (op V)) t := rfl
        _ =
            (shrinkYoneda.{w'}.obj U).map g.op
              (show (shrinkYoneda.{w'}.obj U).obj (op U) from
                shrinkYonedaObjObjEquiv.symm (𝟙 U)) := ht
        _ = shrinkYonedaObjObjEquiv.symm g := by
            simpa using shrinkYoneda_obj_map_shrinkYonedaObjObjEquiv_symm g.op (𝟙 U)
    have htg : shrinkYonedaObjObjEquiv t.1 = g := by
      simpa using congrArg shrinkYonedaObjObjEquiv ht'
    simpa [htg] using (show S (shrinkYonedaObjObjEquiv t.1) from t.2)
  · intro hg
    refine ⟨⟨shrinkYonedaObjObjEquiv.symm g, by simpa using hg⟩, ?_⟩
    simpa using (shrinkYoneda_obj_map_shrinkYonedaObjObjEquiv_symm g.op (𝟙 U)).symm

/-- Helper for Lemma 7.38.3: if every point of `u(U)` lifts through a sieve `S`, then the map on
point fibers induced by `S.shrinkFunctor.ι` is surjective. -/
lemma point_shrinkFunctor_presheafFiber_surjective_of_lifts
    [LocallySmall.{w'} C]
    (q : Point.{w'} J) {U : C} (S : Sieve U)
    (hlift :
      ∀ x : q.fiber.obj U,
        ∃ (Y : C) (g : Y ⟶ U) (_ : S g) (y : q.fiber.obj Y), q.fiber.map g y = x) :
    Function.Surjective
      (q.presheafFiber.map (Sieve.shrinkFunctor.{w'} S).ι) := by
  intro p
  obtain ⟨x, rfl⟩ := (q.shrinkYonedaCompPresheafFiberIso.app U).toEquiv.symm.surjective p
  obtain ⟨Y, g, hg, y, hy⟩ := hlift x
  refine ⟨q.toPresheafFiber Y y (Sieve.shrinkFunctor.{w'} S).toFunctor
      ⟨shrinkYonedaObjObjEquiv.symm g, by simpa using hg⟩, ?_⟩
  -- Compute the image of the chosen representative under the sieve inclusion.
  have hmap :
      q.presheafFiber.map (Sieve.shrinkFunctor.{w'} S).ι
          (q.toPresheafFiber Y y (Sieve.shrinkFunctor.{w'} S).toFunctor
            ⟨shrinkYonedaObjObjEquiv.symm g, by simpa using hg⟩) =
        q.toPresheafFiber Y y (shrinkYoneda.{w'}.obj U)
          (shrinkYonedaObjObjEquiv.symm g) := by
    simpa using
      congrFun
        (q.toPresheafFiber_naturality ((Sieve.shrinkFunctor.{w'} S).ι) Y y)
        ⟨shrinkYonedaObjObjEquiv.symm g, by simpa using hg⟩
  have hshrink :
      q.toPresheafFiber Y y (shrinkYoneda.{w'}.obj U)
          (shrinkYonedaObjObjEquiv.symm g) =
        (q.shrinkYonedaCompPresheafFiberIso.app U).toEquiv.symm (q.fiber.map g y) := by
    calc
      q.toPresheafFiber Y y (shrinkYoneda.{w'}.obj U)
          (shrinkYonedaObjObjEquiv.symm g) =
        q.presheafFiber.map (shrinkYoneda.{w'}.map g)
          ((q.shrinkYonedaCompPresheafFiberIso.app Y).toEquiv.symm y) := by
            simpa using
              (q.presheafFiber_map_shrinkYoneda_map_shrinkYonedaCompPresheafFiberIso_inv_app
                (f := g) (x := y)).symm
      _ = (q.shrinkYonedaCompPresheafFiberIso.app U).toEquiv.symm (q.fiber.map g y) := by
            simpa using (congrFun (q.shrinkYonedaCompPresheafFiberIso.inv.naturality g) y).symm
  exact hmap.trans (hshrink.trans (by rw [hy]))

/-- Helper for Lemma 7.38.3: the small shrink-functor inclusion is objectwise injective. -/
lemma shrinkFunctor_ι_app_injective
    [LocallySmall.{w'} C] {U : C} (S : Sieve U) (X : Cᵒᵖ) :
    Function.Injective ((Sieve.shrinkFunctor.{w'} S).ι.app X) := by
  intro a b h
  exact Subtype.ext h

/-- Helper for Lemma 7.38.3: pointwise lift witnesses through `S` make the induced map on point
fibers of `S.shrinkFunctor.ι` bijective. -/
lemma point_shrinkFunctor_presheafFiber_bijective_of_lifts
    [LocallySmall.{w'} C]
    (q : Point.{w'} J) {U : C} (S : Sieve U)
    (hlift :
      ∀ x : q.fiber.obj U,
        ∃ (Y : C) (g : Y ⟶ U) (_ : S g) (y : q.fiber.obj Y), q.fiber.map g y = x) :
    Function.Bijective
      (q.presheafFiber.map (Sieve.shrinkFunctor.{w'} S).ι) := by
  let _ : Presheaf.IsLocallyInjective J (Sieve.shrinkFunctor.{w'} S).ι :=
    -- Local injectivity is immediate because `S.shrinkFunctor.ι` is objectwise injective.
    Presheaf.isLocallyInjective_of_injective J
      (Sieve.shrinkFunctor.{w'} S).ι
      (shrinkFunctor_ι_app_injective (S := S))
  constructor
  · -- Local injectivity upgrades objectwise injectivity to injectivity on the point fiber.
    exact q.toPresheafFiber_map_injective (Sieve.shrinkFunctor.{w'} S).ι
  · -- Surjectivity comes from lifting every generator `x ∈ u(U)` through the sieve.
    exact point_shrinkFunctor_presheafFiber_surjective_of_lifts (q := q) (S := S) hlift

/-- Helper for Lemma 7.38.3: lifted witness packages descend to surjectivity on the point fiber
of the small shrink-functor inclusion. -/
lemma point_shrinkFunctor_presheafFiber_surjective_of_ulift_lifts
    [LocallySmall.{w'} C]
    (q : Point.{w'} J) {U : C} (S : Sieve U)
    (hlift :
      ∀ x : ULift.{max u v, w'} (q.fiber.obj U),
        ∃ (Y : C) (g : Y ⟶ U) (_ : S g) (y : ULift.{max u v, w'} (q.fiber.obj Y)),
          ULift.up (q.fiber.map g y.down) = x) :
    Function.Surjective
      (q.presheafFiber.map (Sieve.shrinkFunctor.{w'} S).ι) := by
  -- First remove the `ULift` wrapper from the witness package, then apply the small shrink-fiber
  -- surjectivity lemma.
  refine point_shrinkFunctor_presheafFiber_surjective_of_lifts (q := q) (S := S) ?_
  exact (point_cover_lift_ulift_iff (q := q) (U := U) S).1 hlift

/-- Helper for Lemma 7.38.3: the `ULift`-based shrink-functor surjectivity package reindexes from
the original family index type to the owner full subcategory. -/
lemma shrinkFunctor_surjective_fullSubcategory_of_ulift_lifts
    [LocallySmall.{w'} C]
    {ι : Type w} (p : ι → Point.{w'} J) {U : C} (S : Sieve U)
    (hS :
      ∀ i (x : ULift.{max u v, w'} ((p i).fiber.obj U)),
        ∃ (Y : C) (g : Y ⟶ U) (_ : S g) (y : ULift.{max u v, w'} ((p i).fiber.obj Y)),
          ULift.up ((p i).fiber.map g y.down) = x) :
    ∀ Φ : (ofObj p).FullSubcategory,
      Function.Surjective
        (Φ.obj.presheafFiber.map (Sieve.shrinkFunctor.{w'} S).ι) := by
  intro Φ
  rcases Φ with ⟨q, hq⟩
  -- Reindex the owner theorem's point back to one of the original `p i`.
  rcases (ofObj_iff p q).1 hq with ⟨i, rfl⟩
  exact point_shrinkFunctor_presheafFiber_surjective_of_ulift_lifts
    (q := p i) (S := S) (hS i)

/-- Helper for Lemma 7.38.3: the `ULift`-based lift package reindexes from the original family
index type to bijectivity of the universe-lifted sieve inclusion on the owner full subcategory. -/
lemma uliftFunctorInclusion_bijective_fullSubcategory_of_ulift_lifts
    [LocallySmall.{w'} C]
    {ι : Type w} (p : ι → Point.{w'} J) {U : C} (S : Sieve U)
    (hS :
      ∀ i (x : ULift.{max u v, w'} ((p i).fiber.obj U)),
        ∃ (Y : C) (g : Y ⟶ U) (_ : S g) (y : ULift.{max u v, w'} ((p i).fiber.obj Y)),
          ULift.up ((p i).fiber.map g y.down) = x) :
    ∀ Φ : (ofObj p).FullSubcategory,
      Function.Bijective
        (Φ.obj.presheafFiber.map (Sieve.uliftFunctorInclusion.{max u v w'} S)) := by
  intro Φ
  rcases Φ with ⟨q, hq⟩
  -- Reindex the owner theorem's point back to one of the original `p i`.
  rcases (ofObj_iff p q).1 hq with ⟨i, rfl⟩
  -- Remove the `ULift` wrapper from the given witness package, then apply the pointwise
  -- bijectivity lemma for `S.uliftFunctorInclusion`.
  refine point_uliftFunctorInclusion_presheafFiber_bijective_of_lifts
    (q := p i) (S := S) ?_
  exact (point_cover_lift_ulift_iff (q := p i) (U := U) S).1 (hS i)

/-- Helper for Lemma 7.38.3: pointwise equality of germs along a family of points makes the
equalizer sieve act surjectively on each corresponding point fiber of `shrinkYoneda`. -/
lemma pointwise_germ_eq_shrinkFunctor_surjective
    [LocallySmall.{w'} C]
    {ι : Type w} (p : ι → Point.{w'} J)
    {ℱ : Sheaf J (Type (max u v w'))} (U : C)
    (s s' : ℱ.obj.obj (op U))
    (hss :
      ∀ i (x : (p i).fiber.obj U),
        (p i).toPresheafFiber U x ℱ.obj s =
          (p i).toPresheafFiber U x ℱ.obj s') :
    ∀ i,
      Function.Surjective
        ((p i).presheafFiber.map
          (Sieve.shrinkFunctor.{w'} (Presheaf.equalizerSieve (F := ℱ.obj) s s')).ι) := by
  intro i
  -- Every `x ∈ u_i(U)` lifts through the equalizer sieve, so the induced map on the point fiber
  -- of `shrinkYoneda` is surjective.
  refine point_shrinkFunctor_presheafFiber_surjective_of_lifts
    (q := p i) (S := Presheaf.equalizerSieve (F := ℱ.obj) s s') ?_
  intro x
  obtain ⟨Y, g, hg, y, hy⟩ :=
    pointwise_germ_eq_gives_equalizer_lift (q := p i) U s s' (hx := hss i x)
  exact ⟨Y, g, hg, y, hy⟩

/-- Helper for Lemma 7.38.3: reindex the pointwise surjectivity package from `i : ι` to the
owner theorem's full subcategory `(ofObj p).FullSubcategory`. -/
lemma pointwise_germ_eq_shrinkFunctor_surjective_fullSubcategory
    [LocallySmall.{w'} C]
    {ι : Type w} (p : ι → Point.{w'} J)
    {ℱ : Sheaf J (Type (max u v w'))} (U : C)
    (s s' : ℱ.obj.obj (op U))
    (hss :
      ∀ i (x : (p i).fiber.obj U),
        (p i).toPresheafFiber U x ℱ.obj s =
          (p i).toPresheafFiber U x ℱ.obj s') :
    ∀ Φ : (ofObj p).FullSubcategory,
      Function.Surjective
        (Φ.obj.presheafFiber.map
          (Sieve.shrinkFunctor.{w'} (Presheaf.equalizerSieve (F := ℱ.obj) s s')).ι) := by
  intro Φ
  rcases Φ with ⟨q, hq⟩
  -- Reindex the owner theorem's object `q` back to one of the original points `p i`.
  rcases (ofObj_iff p q).1 hq with ⟨i, rfl⟩
  exact pointwise_germ_eq_shrinkFunctor_surjective (p := p) U s s' hss i

/-- Helper for Lemma 7.38.3: pointwise equality of germs makes the equalizer sieve act
bijectively on each corresponding point fiber of `shrinkYoneda`. -/
lemma pointwise_germ_eq_shrinkFunctor_bijective
    [LocallySmall.{w'} C]
    {ι : Type w} (p : ι → Point.{w'} J)
    {ℱ : Sheaf J (Type (max u v w'))} (U : C)
    (s s' : ℱ.obj.obj (op U))
    (hss :
      ∀ i (x : (p i).fiber.obj U),
        (p i).toPresheafFiber U x ℱ.obj s =
          (p i).toPresheafFiber U x ℱ.obj s') :
    ∀ i,
      Function.Bijective
        ((p i).presheafFiber.map
          (Sieve.shrinkFunctor.{w'} (Presheaf.equalizerSieve (F := ℱ.obj) s s')).ι) := by
  intro i
  -- The equalizer-lift witnesses already built above give the full bijectivity package.
  refine point_shrinkFunctor_presheafFiber_bijective_of_lifts
    (q := p i) (S := Presheaf.equalizerSieve (F := ℱ.obj) s s') ?_
  intro x
  exact pointwise_germ_eq_gives_equalizer_lift (q := p i) U s s' (hx := hss i x)

end GrothendieckTopology

end CategoryTheory
