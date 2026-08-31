module

public import Mathlib.CategoryTheory.FiberedCategory.Cartesian
public import Mathlib.CategoryTheory.FiberedCategory.Fibered
public import Mathlib.CategoryTheory.Widesubcategory
public import stacks_project.Chap04.Definition_4_35_1

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

universe v₁ v₂ u₁ u₂

namespace CategoryTheory

open Functor IsStronglyCartesian

/-
Domain-style sampling for Lemma 4.35.3:
- primary domain: fibred categories, strongly cartesian morphisms, and the associated category
  fibred in groupoids;
- sampled owner-level declarations:
  `Functor.IsStronglyCartesian`,
  `Functor.IsFibered.of_exists_isStronglyCartesian`,
  `CategoryTheory.WideSubcategory`,
  `CategoryTheory.IsFibredInGroupoids`.
- best owner abstraction: the core owner is `Functor.IsStronglyCartesian`; this file should stay at
  the bridge/view layer, building only the associated projection to `C` from the canonical
  `WideSubcategory` owner, without introducing a parallel owner for fibred-in-groupoids data.

Source/core/bridge triage:
- `source-facing`: `stronglyCartesianProjection_isFibredInGroupoids`;
- `core/canonical`: `Functor.IsStronglyCartesian`, `Functor.IsFibered`,
  `CategoryTheory.IsFibredInGroupoids`;
- `bridge/view`: `stronglyCartesianProjection`.

Primitive-vs-derived split:
- primitive data: the functor `p : S ⥤ C` and the owner-level predicate
  `p.IsStronglyCartesian (p.map φ) φ` on morphisms of `S`;
- derived API: the multiplicative wide subcategory cut out by that predicate, the restricted
  projection to `C`, and the induced fibred-in-groupoids structure when `p` is fibred.
-/

variable {C : Type u₁} {S : Type u₂} [Category.{v₁} C] [Category.{v₂} S]

/-- The morphism property on `S` consisting of the arrows that are strongly cartesian over their
image under `p`. -/
abbrev stronglyCartesianProperty (p : S ⥤ C) : MorphismProperty S :=
  fun {_ _} φ ↦ p.IsStronglyCartesian (p.map φ) φ

/-- The strongly cartesian morphisms over `p` form a multiplicative morphism property. -/
instance (p : S ⥤ C) :
    MorphismProperty.IsMultiplicative (stronglyCartesianProperty p) where
  id_mem x := by
    simpa [stronglyCartesianProperty] using
      (inferInstance : p.IsStronglyCartesian (𝟙 (p.obj x)) (𝟙 x))
  comp_mem φ ψ hφ hψ := by
    haveI : p.IsStronglyCartesian (p.map φ) φ := hφ
    haveI : p.IsStronglyCartesian (p.map ψ) ψ := hψ
    change p.IsStronglyCartesian (p.map (φ ≫ ψ)) (φ ≫ ψ)
    simpa using
      (inferInstance : p.IsStronglyCartesian (p.map φ ≫ p.map ψ) (φ ≫ ψ))

/-- The wide subcategory of `S` whose morphisms are exactly the strongly cartesian morphisms
over `p`. -/
abbrev stronglyCartesianSubcategory (p : S ⥤ C) :=
  WideSubcategory (stronglyCartesianProperty p)

/-- The restriction of `p` to its strongly cartesian wide subcategory. -/
abbrev stronglyCartesianProjection (p : S ⥤ C) :
    stronglyCartesianSubcategory p ⥤ C :=
  wideSubcategoryInclusion (stronglyCartesianProperty p) ⋙ p

private theorem isHomLift_of_stronglyCartesianProjection
    (p : S ⥤ C) {x y : stronglyCartesianSubcategory p}
    {f : p.obj x.obj ⟶ p.obj y.obj} {φ : x ⟶ y}
    [(stronglyCartesianProjection p).IsHomLift f φ] :
    p.IsHomLift f φ.hom := by
  refine IsHomLift.of_fac p f φ.hom rfl rfl ?_
  simpa [stronglyCartesianProjection] using
    (IsHomLift.fac (stronglyCartesianProjection p) f φ)

private theorem isHomLift_stronglyCartesianProjection
    (p : S ⥤ C) {x y : stronglyCartesianSubcategory p}
    {f : p.obj x.obj ⟶ p.obj y.obj} {φ : x ⟶ y}
    [p.IsHomLift f φ.hom] :
    (stronglyCartesianProjection p).IsHomLift f φ := by
  refine IsHomLift.of_fac (stronglyCartesianProjection p) f φ rfl rfl ?_
  simpa [stronglyCartesianProjection] using (IsHomLift.fac p f φ.hom)

-- Any morphism of the strongly cartesian wide subcategory remains strongly cartesian for the
-- restricted projection.
private theorem stronglyCartesianProjection_map_isStronglyCartesian
    (p : S ⥤ C) {x y : stronglyCartesianSubcategory p} (φ : x ⟶ y) :
    (stronglyCartesianProjection p).IsStronglyCartesian ((stronglyCartesianProjection p).map φ) φ := by
  constructor
  intro z g ψ hψ
  change p.obj z.obj ⟶ p.obj x.obj at g
  haveI : p.IsStronglyCartesian (p.map φ.hom) φ.hom :=
    φ.2
  letI : (stronglyCartesianProjection p).IsHomLift (g ≫ p.map φ.hom) ψ := by
    simpa [stronglyCartesianProjection, Functor.comp_map] using hψ
  letI : p.IsHomLift (g ≫ p.map φ.hom) ψ.hom :=
    isHomLift_of_stronglyCartesianProjection p
  obtain ⟨χ, hχlift, hχuniq⟩ :=
    IsStronglyCartesian.universal_property p (p.map φ.hom) φ.hom g
      (g ≫ p.map φ.hom) rfl ψ.hom
  letI : p.IsHomLift g χ :=
    hχlift.1
  have hχfac : χ ≫ φ.hom = ψ.hom :=
    hχlift.2
  have hψStrong : p.IsStronglyCartesian (g ≫ p.map φ.hom) ψ.hom := by
    haveI : p.IsStronglyCartesian (p.map ψ.hom) ψ.hom :=
      ψ.2
    have hψeq : g ≫ p.map φ.hom = p.map ψ.hom := IsHomLift.eq_of_isHomLift p _ ψ.hom
    simpa [hψeq] using (show p.IsStronglyCartesian (p.map ψ.hom) ψ.hom from inferInstance)
  have hχcomp : p.IsStronglyCartesian (g ≫ p.map φ.hom) (χ ≫ φ.hom) := by
    simpa [hχfac] using hψStrong
  letI : p.IsStronglyCartesian (g ≫ p.map φ.hom) (χ ≫ φ.hom) := hχcomp
  have hχStrong : p.IsStronglyCartesian g χ := by
    let hφStrong : p.IsStronglyCartesian (p.map φ.hom) φ.hom := φ.2
    exact
      @Functor.IsStronglyCartesian.of_comp
        _ _ _ _ p _ _ _ _ _ _ _ _ _ _ hφStrong hχcomp hχlift.1
  -- Package the ambient lift `χ` into the wide subcategory once we know it is strongly cartesian.
  have hχ_mem : stronglyCartesianProperty p χ := by
    have hχeq : g = p.map χ := IsHomLift.eq_of_isHomLift p g χ
    simpa [stronglyCartesianProperty, hχeq] using hχStrong
  let χ' : z ⟶ x :=
    ⟨χ, hχ_mem⟩
  refine ⟨χ', ⟨?_, ?_⟩, ?_⟩
  · exact isHomLift_stronglyCartesianProjection p
  · apply WideSubcategory.hom_ext
    exact hχfac
  · intro τ hτ
    apply WideSubcategory.hom_ext
    letI : (stronglyCartesianProjection p).IsHomLift g τ := hτ.1
    letI : p.IsHomLift g τ.hom := isHomLift_of_stronglyCartesianProjection p
    exact hχuniq τ.hom ⟨inferInstance, congrArg (fun k ↦ k.hom) hτ.2⟩

-- Proof sketch: for existence of lifts, use that `p` is fibered and choose strongly cartesian
-- lifts, which already lie in the wide subcategory. For uniqueness, compare two composable lifts as
-- in Diagram `4.35.1.1`; since every morphism in the wide subcategory is strongly cartesian, the
-- comparison is an isomorphism, and isomorphisms remain strongly cartesian there.
/-- The strongly cartesian restriction of a fibred functor is fibred in groupoids. -/
instance (p : S ⥤ C) [p.IsFibered] :
    IsFibredInGroupoids (stronglyCartesianProjection p) := by
  refine
    { toIsFibered := Functor.IsFibered.of_exists_isStronglyCartesian ?_
      isStronglyCartesian_map := fun φ ↦
        stronglyCartesianProjection_map_isStronglyCartesian p φ }
  intro y R f
  change R ⟶ p.obj y.obj at f
  obtain ⟨x, φ, hφ⟩ := IsPreFibered.exists_isCartesian p rfl f
  letI : p.IsCartesian f φ := hφ
  letI : p.IsStronglyCartesian f φ :=
    IsFibered.isStronglyCartesian_of_isCartesian p f φ
  have hx : p.obj x = R := IsHomLift.domain_eq p f φ
  subst R
  have hfeq : f = p.map φ := IsHomLift.eq_of_isHomLift p f φ
  -- The chosen ambient lift is already strongly cartesian, so it defines a morphism downstairs.
  have hφ'_mem : stronglyCartesianProperty p φ := by
    simpa [stronglyCartesianProperty, hfeq] using
      (show p.IsStronglyCartesian f φ from inferInstance)
  let φ' : (⟨x⟩ : stronglyCartesianSubcategory p) ⟶ y :=
    ⟨φ, hφ'_mem⟩
  change (stronglyCartesianProjection p).obj (⟨x⟩ : stronglyCartesianSubcategory p) ⟶
      (stronglyCartesianProjection p).obj y at f
  have hφ'eq : f = (stronglyCartesianProjection p).map φ' := by
    simpa [stronglyCartesianProjection, Functor.comp_map] using hfeq
  have hφ'_lift : (stronglyCartesianProjection p).IsHomLift f φ' := by
    refine IsHomLift.of_fac' (stronglyCartesianProjection p) f φ' rfl rfl ?_
    simpa using hφ'eq.symm
  letI : (stronglyCartesianProjection p).IsHomLift f φ' :=
    hφ'_lift
  have hφ' : (stronglyCartesianProjection p).IsStronglyCartesian f φ' := by
    simpa [hφ'eq] using stronglyCartesianProjection_map_isStronglyCartesian p φ'
  refine ⟨⟨x⟩, φ', ?_⟩
  exact hφ'

/-- Lemma 4.35.3: if `p : S ⥤ C` is fibred, then its restriction to the wide subcategory whose
morphisms are the strongly cartesian morphisms of `S` is fibred in groupoids. -/
theorem stronglyCartesianProjection_isFibredInGroupoids
    (p : S ⥤ C) [p.IsFibered] :
    IsFibredInGroupoids (stronglyCartesianProjection p) :=
  inferInstance

end CategoryTheory
