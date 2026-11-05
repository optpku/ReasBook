module

public import stacks_project.Chap04.«4_34_2_4»
@[expose] public section

universe u v u₁ u₁' u₂ u₂'

namespace CategoryTheory
namespace CategoryOver

open BasedCategory BasedFunctor BasedNatIso BasedNatTrans

variable {C : Type u} [Category.{v} C]

/- Domain-style sampling for `4.34.2.3`:
- primary domain: the bicategory `Cat/C`, modeled chapter-wide by `BasedCategory`, `BasedFunctor`,
  and `BasedNatTrans`;
- inspected owner declarations: the generic `CategoryTheory.relativeInertiaMap`, the chapter owner
  objects `relativeInertiaOver` and `absoluteInertiaOver`, the chapter comparison map
  `relativeInertiaToAbsoluteInertia`, and the bicategorical
  constructor `BasedNatIso.mkNatIso`;
- best owner abstraction: the generic relative-inertia functor on underlying categories, packaged
  over `C` by the bridge/view map `relativeInertiaOverMap` and its absolute specialization
  `absoluteInertiaOverMap`;
- layer classification here: `bridge/view`;
- primitive data: an invertible `2`-commutative square in `Cat/C`;
- derived API: the induced map on relative inertia over `C`, its absolute specialization, and the
  naturality isomorphism for the comparison map from relative to absolute inertia. -/

variable
    {S₁ : BasedCategory.{v, u₁} C} {S₁' : BasedCategory.{v, u₁'} C}
    {S₂ : BasedCategory.{v, u₂} C} {S₂' : BasedCategory.{v, u₂'} C}

@[simp] private theorem relativeInertiaEqToHom_φ
    {A B : Type*} [Category.{v} A] [Category.{v} B]
    {F : A ⥤ B} {X Y : RelativeInertiaObject F} (h : X = Y) :
    (eqToHom h : X ⟶ Y).φ = eqToHom (by cases h; rfl) := by
  cases h
  rfl

/-- The induced morphism on relative inertia over `C` attached to an invertible
`2`-commutative square in `Cat/C`. -/
noncomputable abbrev relativeInertiaOverMap
    (F₁ : S₁ ⥤ᵇ S₁') (F₂ : S₂ ⥤ᵇ S₂')
    (G : S₁ ⥤ᵇ S₂) (G' : S₁' ⥤ᵇ S₂')
    (comm : F₁ ⋙ G' ≅ G ⋙ F₂) :
    relativeInertiaOver F₁ ⥤ᵇ relativeInertiaOver F₂ :=
  { toFunctor := CategoryTheory.relativeInertiaMap G.toFunctor G'.toFunctor
      ((BasedNatTrans.forgetful S₁ S₂').mapIso comm)
    w := by
      refine Functor.ext ?_ ?_
      · intro X
        exact G.w_obj X.x
      · intro X Y f
        simpa [relativeInertiaProjection, relativeInertiaMap_map_hom] using
          Functor.congr_hom G.w f.φ }

/-- The induced morphism on absolute inertia over `C` attached to a morphism in `Cat/C`,
specialized from `relativeInertiaOverMap` along the structure functors. -/
noncomputable abbrev absoluteInertiaOverMap
    (G : S₁ ⥤ᵇ S₂) :
    absoluteInertiaOver S₁ ⥤ᵇ absoluteInertiaOver S₂ :=
  { toFunctor := CategoryTheory.relativeInertiaMap G.toFunctor (𝟭 C)
      (eqToIso <| by simpa using G.w.symm)
    w := by
      refine Functor.ext ?_ ?_
      · intro X
        exact G.w_obj X.x
      · intro X Y f
        simpa [absoluteInertiaOver, relativeInertiaProjection, relativeInertiaMap_map_hom] using
          Functor.congr_hom G.w f.φ }

section Naturality

variable
    (F₁ : S₁ ⥤ᵇ S₁') (F₂ : S₂ ⥤ᵇ S₂')
    (G : S₁ ⥤ᵇ S₂) (G' : S₁' ⥤ᵇ S₂')
    (comm : F₁ ⋙ G' ≅ G ⋙ F₂)

theorem naturality_app_obj_eq
    (X : RelativeInertiaObject F₁.toFunctor) :
    (relativeInertiaOverMap F₁ F₂ G G' comm ⋙ relativeInertiaToAbsoluteInertia F₂).obj X =
      (relativeInertiaToAbsoluteInertia F₁ ⋙ absoluteInertiaOverMap G).obj X := by
  cases X
  simp [relativeInertiaOverMap, absoluteInertiaOverMap, relativeInertiaToAbsoluteInertia]
  aesop

private theorem naturality_hom
    {X Y : RelativeInertiaObject F₁.toFunctor} (f : X ⟶ Y) :
    (relativeInertiaOverMap F₁ F₂ G G' comm ⋙ relativeInertiaToAbsoluteInertia F₂).map f ≫
      eqToHom (naturality_app_obj_eq F₁ F₂ G G' comm Y) =
      eqToHom (naturality_app_obj_eq F₁ F₂ G G' comm X) ≫
        (relativeInertiaToAbsoluteInertia F₁ ⋙ absoluteInertiaOverMap G).map f := by
  -- Compare the naturality square on the underlying objects in `S₂`.
  have hx := congrArg RelativeInertiaObject.x (naturality_app_obj_eq F₁ F₂ G G' comm X)
  have hy := congrArg RelativeInertiaObject.x (naturality_app_obj_eq F₁ F₂ G G' comm Y)
  cases X
  cases Y
  apply RelativeInertiaHom.ext
  -- After projecting to `x`, both routes transport along the same arrow `G.map f.φ`.
  change ((relativeInertiaOverMap F₁ F₂ G G' comm ⋙ relativeInertiaToAbsoluteInertia F₂).map f).φ ≫
      eqToHom hy =
    eqToHom hx ≫
      ((relativeInertiaToAbsoluteInertia F₁ ⋙ absoluteInertiaOverMap G).map f).φ
  simp [relativeInertiaOverMap, absoluteInertiaOverMap, relativeInertiaToAbsoluteInertia,
    relativeInertiaMap_map_hom]

noncomputable def naturalityNatIso :
    (relativeInertiaOverMap F₁ F₂ G G' comm).toFunctor ⋙
        (relativeInertiaToAbsoluteInertia F₂).toFunctor ≅
      (relativeInertiaToAbsoluteInertia F₁).toFunctor ⋙
        (absoluteInertiaOverMap G).toFunctor :=
  NatIso.ofComponents
    (fun X ↦ eqToIso (naturality_app_obj_eq F₁ F₂ G G' comm X))
    (fun {_ _} f ↦ by
      simpa using naturality_hom F₁ F₂ G G' comm f)

private theorem naturality_over_id :
    eqToHom (relativeInertiaOverMap F₁ F₂ G G' comm ⋙ relativeInertiaToAbsoluteInertia F₂).w.symm ≫
        Functor.whiskerRight
          (naturalityNatIso F₁ F₂ G G' comm).hom
          (absoluteInertiaOver S₂).p ≫
      eqToHom (relativeInertiaToAbsoluteInertia F₁ ⋙ absoluteInertiaOverMap G).w =
        𝟙 (relativeInertiaOver F₁).p := by
  ext X
  cases X
  simp [naturalityNatIso, absoluteInertiaOverMap, relativeInertiaOverMap,
    relativeInertiaToAbsoluteInertia]
  simp only [eqToHom_map, eqToHom_trans, eqToHom_refl]

/-- 4.34.2.3: the canonical comparison
`\mathcal I_{\mathcal S_1/\mathcal S_1'} \to \mathcal I_{\mathcal S_1}` of `4.34.2.4`
is natural for an invertible `2`-commutative square in `Cat/C`. -/
noncomputable def relativeInertiaToAbsoluteInertiaNaturality :
    relativeInertiaOverMap F₁ F₂ G G' comm ⋙ relativeInertiaToAbsoluteInertia F₂ ≅
      relativeInertiaToAbsoluteInertia F₁ ⋙ absoluteInertiaOverMap G := by
  let H₁ := relativeInertiaOverMap F₁ F₂ G G' comm ⋙ relativeInertiaToAbsoluteInertia F₂
  let H₂ := relativeInertiaToAbsoluteInertia F₁ ⋙ absoluteInertiaOverMap G
  let η : H₁ ⟶ H₂ :=
    of_over_id
      (naturalityNatIso F₁ F₂ G G' comm).hom
      (by simpa [H₁, H₂] using naturality_over_id F₁ F₂ G G' comm)
  exact mkNatIso (naturalityNatIso F₁ F₂ G G' comm) η.isHomLift'

/-- The naturality isomorphism for relative-to-absolute inertia is a morphism over the identity
of the base category. -/
-- Proof sketch: apply `BasedNatTrans.over_id` to the hom of
-- `relativeInertiaToAbsoluteInertiaNaturality`.
theorem relativeInertiaToAbsoluteInertiaNaturality_hom_over_id :
    eqToHom
          (relativeInertiaOverMap F₁ F₂ G G' comm ⋙
            relativeInertiaToAbsoluteInertia F₂).w.symm ≫
        Functor.whiskerRight
          (relativeInertiaToAbsoluteInertiaNaturality F₁ F₂ G G' comm).hom.toNatTrans
          (absoluteInertiaOver S₂).p ≫
      eqToHom (relativeInertiaToAbsoluteInertia F₁ ⋙ absoluteInertiaOverMap G).w =
        𝟙 (relativeInertiaOver F₁).p := by
  -- This is the standard over-identity equation for the based natural transformation `hom`.
  simpa using
    BasedNatTrans.over_id ((relativeInertiaToAbsoluteInertiaNaturality F₁ F₂ G G' comm).hom)

end Naturality

end CategoryOver
end CategoryTheory
