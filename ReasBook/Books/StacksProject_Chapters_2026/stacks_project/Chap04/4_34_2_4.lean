module

public import stacks_project.Chap04.«4_34_2_1»

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

universe u v uS uS'

namespace CategoryTheory

namespace CategoryOver

open BasedCategory
open FibredCategoryMor
open Functor IsHomLift

variable {C : Type u} [Category.{v} C]
variable {S : BasedCategory.{v, uS} C} {S' : BasedCategory.{v, uS'} C}

private theorem idFunctor_isStronglyCartesian {R T : C} (f : R ⟶ T) :
    Functor.IsStronglyCartesian (𝟭 C) f f where
  toIsHomLift := by
    simpa using
      (show Functor.IsHomLift (𝟭 C) ((𝟭 C).map f) f from inferInstance)
  universal_property' := by
    intro a g φ hφ
    subst_hom_lift (𝟭 C) (g ≫ f) φ
    refine ⟨g, ?_, ?_⟩
    · constructor
      · simpa using
          (show Functor.IsHomLift (𝟭 C) ((𝟭 C).map g) g from inferInstance)
      · rfl
    · intro π hπ
      let _ := hπ.1
      subst_hom_lift (𝟭 C) g π
      rfl

private theorem idFunctor_isFibered : (𝟭 C).IsFibered := by
  apply Functor.IsFibered.of_exists_isStronglyCartesian
  intro a R f
  exact ⟨R, f, idFunctor_isStronglyCartesian f⟩

/- Domain-style sampling for `4.34.2.4`:
- primary domain: categories over a fixed base `C`, extending the owner objects
  `relativeInertiaOver F` and `absoluteInertiaOver S` introduced in `4.34.2.1`.
- owner abstraction: the chapter owner objects already live upstream; this file adds only the
  further bridge data built from them, namely fibredness of the absolute projection and the
  comparison map to absolute inertia.
- refinement target: reuse the owner declarations from `4.34.2.1` directly and keep this file in
  the `bridge/view` layer. -/

section AbsoluteInertiaFibered

variable {T : Type uS} [Category.{v} T]
variable (p : T ⥤ C) [p.IsFibered]

omit [p.IsFibered] in
/-- Helper for Lemma 4.35.12: a vertical automorphism of an inertia object pulls back along a
strongly cartesian lift of its source object. -/
private theorem pullback_automorphism_hom
    {X : RelativeInertiaObject p} {R : C} {y : T} {f : R ⟶ p.obj X.x}
    (a : y ⟶ X.x) [p.IsStronglyCartesian f a] :
    ∃ αy : y ⟶ y, p.IsHomLift (𝟙 R) αy ∧ αy ≫ a = a ≫ X.α.hom := by
  haveI : p.IsHomLift (𝟙 (p.obj X.x)) X.α.hom := by
    simpa [X.map_hom_eq_id] using
      (inferInstance : p.IsHomLift (p.map X.α.hom) X.α.hom)
  haveI : p.IsHomLift f (a ≫ X.α.hom) := by
    simpa using
      (inferInstance : p.IsHomLift (f ≫ 𝟙 (p.obj X.x)) (a ≫ X.α.hom))
  -- Factor `a ≫ X.α.hom` uniquely through the chosen strongly cartesian lift `a`.
  obtain ⟨αy, hαy, -⟩ :=
    Functor.IsStronglyCartesian.universal_property p f a (𝟙 R) f (Category.id_comp f).symm
      (a ≫ X.α.hom)
  exact ⟨αy, hαy.1, hαy.2⟩

omit [p.IsFibered] in
/-- Helper for Lemma 4.35.12: the pulled-back vertical endomorphism is again an automorphism. -/
private theorem pullback_automorphism_iso
    {X : RelativeInertiaObject p} {R : C} {y : T} {f : R ⟶ p.obj X.x}
    (a : y ⟶ X.x) [p.IsStronglyCartesian f a] :
    ∃ e : y ≅ y, p.IsHomLift (𝟙 R) e.hom ∧ e.hom ≫ a = a ≫ X.α.hom := by
  obtain ⟨αh, hαh_lift, hαh_eq⟩ :=
    pullback_automorphism_hom (p := p) (X := X) (R := R) (y := y) (f := f) a
  let Xinv : RelativeInertiaObject p :=
    { x := X.x
      α := X.α.symm
      map_hom_eq_id := by
        simpa [X.map_hom_eq_id] using Functor.map_inv p X.α.hom }
  obtain ⟨αi, hαi_lift, hαi_eq⟩ :=
    pullback_automorphism_hom (p := p) (X := Xinv) (R := R) (y := y) (f := f) a
  have hαi_eq' : αi ≫ a = a ≫ X.α.inv := by
    simpa [Xinv] using hαi_eq
  have hαhαi : αh ≫ αi = 𝟙 y := by
    letI : p.IsHomLift (𝟙 R) αh := hαh_lift
    letI : p.IsHomLift (𝟙 R) αi := hαi_lift
    haveI : p.IsHomLift (𝟙 R) (𝟙 y) := by
      exact IsHomLift.id (IsHomLift.domain_eq p f a)
    -- Compare the two candidate vertical factorizations after postcomposing with `a`.
    apply Functor.IsStronglyCartesian.ext (p := p) (f := f) (φ := a) (g := 𝟙 R)
    calc
      (αh ≫ αi) ≫ a = αh ≫ (αi ≫ a) := by simp [Category.assoc]
      _ = αh ≫ (a ≫ X.α.inv) := by rw [hαi_eq']
      _ = (αh ≫ a) ≫ X.α.inv := by simp [Category.assoc]
      _ = (a ≫ X.α.hom) ≫ X.α.inv := by rw [hαh_eq]
      _ = a := by simp [Category.assoc]
      _ = (𝟙 y) ≫ a := by simp
  have hαiαh : αi ≫ αh = 𝟙 y := by
    letI : p.IsHomLift (𝟙 R) αh := hαh_lift
    letI : p.IsHomLift (𝟙 R) αi := hαi_lift
    haveI : p.IsHomLift (𝟙 R) (𝟙 y) := by
      exact IsHomLift.id (IsHomLift.domain_eq p f a)
    -- The inverse relation is proved by the same uniqueness argument through `a`.
    apply Functor.IsStronglyCartesian.ext (p := p) (f := f) (φ := a) (g := 𝟙 R)
    calc
      (αi ≫ αh) ≫ a = αi ≫ (αh ≫ a) := by simp [Category.assoc]
      _ = αi ≫ (a ≫ X.α.hom) := by rw [hαh_eq]
      _ = (αi ≫ a) ≫ X.α.hom := by simp [Category.assoc]
      _ = (a ≫ X.α.inv) ≫ X.α.hom := by rw [hαi_eq']
      _ = a := by simp [Category.assoc]
      _ = (𝟙 y) ≫ a := by simp
  exact ⟨⟨αh, αi, hαhαi, hαiαh⟩, hαh_lift, hαh_eq⟩

/-- Helper for Lemma 4.35.12: every base arrow into an inertia object admits a strongly
cartesian lift in the inertia projection. -/
private theorem relative_inertia_lift_isStronglyCartesian
    {X : RelativeInertiaObject p} {R : C} (f : R ⟶ p.obj X.x) :
    ∃ Y : RelativeInertiaObject p, ∃ φ : Y ⟶ X,
      (relativeInertiaProjection p p).IsStronglyCartesian f φ := by
  obtain ⟨y, a, ha_cart⟩ := IsPreFibered.exists_isCartesian p rfl f
  letI : p.IsCartesian f a := ha_cart
  letI : p.IsStronglyCartesian f a :=
    Functor.IsFibered.isStronglyCartesian_of_isCartesian p f a
  have hy : p.obj y = R := IsHomLift.domain_eq p f a
  obtain ⟨e, he_lift, he_eq⟩ :=
    pullback_automorphism_iso (p := p) (X := X) (R := R) (y := y) (f := f) a
  let Y : RelativeInertiaObject p :=
    { x := y
      α := e
      map_hom_eq_id := by
        letI : p.IsHomLift (𝟙 R) e.hom := he_lift
        subst hy
        simpa using (IsHomLift.eq_of_isHomLift p (𝟙 (p.obj y)) e.hom).symm }
  let φ : Y ⟶ X :=
    { φ := a
      comm := by
        simpa [Y] using he_eq }
  refine ⟨Y, φ, ?_⟩
  refine
    { toIsHomLift := by
        refine IsHomLift.of_fac' (relativeInertiaProjection p p) f φ ?_ rfl ?_
        · simpa [relativeInertiaProjection, Y] using hy
        · simpa [relativeInertiaProjection, φ, Y] using (IsHomLift.fac' p f a)
      universal_property' := ?_ }
  intro Z g ψ hψ
  have hψlift : p.IsHomLift (g ≫ f) ψ.φ := by
    letI : (relativeInertiaProjection p p).IsHomLift (g ≫ f) ψ := hψ
    refine IsHomLift.of_fac' p (g ≫ f) ψ.φ rfl rfl ?_
    simpa [relativeInertiaProjection] using
      (IsHomLift.fac' (p := relativeInertiaProjection p p) (f := g ≫ f) (φ := ψ))
  letI : p.IsHomLift (g ≫ f) ψ.φ := hψlift
  obtain ⟨χ0, hχ0, hχ0_uniq⟩ :=
    Functor.IsStronglyCartesian.universal_property p f a g (g ≫ f) rfl ψ.φ
  have hχ0_fac : χ0 ≫ a = ψ.φ := hχ0.2
  letI : p.IsHomLift g χ0 := hχ0.1
  have hχ0_comm : Z.α.hom ≫ χ0 = χ0 ≫ e.hom := by
    haveI : p.IsHomLift (𝟙 (p.obj Z.x)) Z.α.hom := by
      simpa [Z.map_hom_eq_id] using
        (inferInstance : p.IsHomLift (p.map Z.α.hom) Z.α.hom)
    haveI : p.IsHomLift g (Z.α.hom ≫ χ0) := by
      exact IsHomLift.comp_lift_id_left' (p := p) (p.obj Z.x) Z.α.hom g χ0
    haveI : p.IsHomLift (𝟙 R) e.hom := he_lift
    haveI : p.IsHomLift g (χ0 ≫ e.hom) := by
      exact IsHomLift.comp_lift_id_right' (p := p) g χ0 R e.hom
    -- Recover the inertia commutation relation by comparing both candidates after `a`.
    apply Functor.IsStronglyCartesian.ext (p := p) (f := f) (φ := a) (g := g)
    calc
      (Z.α.hom ≫ χ0) ≫ a = Z.α.hom ≫ (χ0 ≫ a) := by simp [Category.assoc]
      _ = Z.α.hom ≫ ψ.φ := by rw [hχ0_fac]
      _ = ψ.φ ≫ X.α.hom := by simpa using ψ.comm
      _ = (χ0 ≫ a) ≫ X.α.hom := by rw [hχ0_fac]
      _ = χ0 ≫ (a ≫ X.α.hom) := by simp [Category.assoc]
      _ = χ0 ≫ (e.hom ≫ a) := by rw [← he_eq]
      _ = (χ0 ≫ e.hom) ≫ a := by simp [Category.assoc]
  let χ : Z ⟶ Y :=
    { φ := χ0
      comm := by
        simpa [Y] using hχ0_comm }
  refine ⟨χ, ⟨?_, ?_⟩, ?_⟩
  · refine IsHomLift.of_fac' (relativeInertiaProjection p p) g χ rfl ?_ ?_
    · simpa [relativeInertiaProjection, Y] using hy
    · simpa [relativeInertiaProjection, χ, Y] using (IsHomLift.fac' p g χ0)
  · apply RelativeInertiaHom.ext
    exact hχ0_fac
  · intro π hπ
    apply RelativeInertiaHom.ext
    have hπlift : p.IsHomLift g π.φ := by
      letI : (relativeInertiaProjection p p).IsHomLift g π := hπ.1
      refine IsHomLift.of_fac' p g π.φ rfl ?_ ?_
      · simpa [relativeInertiaProjection, Y] using hy
      · simpa [relativeInertiaProjection, Y] using
          (IsHomLift.fac' (relativeInertiaProjection p p) g π)
    have hπfac : π.φ ≫ a = ψ.φ := by
      simpa using congrArg RelativeInertiaHom.φ hπ.2
    exact hχ0_uniq π.φ ⟨hπlift, hπfac⟩

/-- Helper for Lemma 4.35.12: the raw absolute inertia projection `relativeInertiaProjection p p`
is fibered. -/
theorem relativeInertiaProjection_self_isFibered :
    (relativeInertiaProjection p p).IsFibered := by
  -- Route correction: build the strongly cartesian lift directly in the inertia category, rather
  -- than passing through a homogeneous owner theorem that fixes the total-category universe.
  refine Functor.IsFibered.of_exists_isStronglyCartesian ?_
  intro X R f
  obtain ⟨Y, φ, hφ⟩ :=
    relative_inertia_lift_isStronglyCartesian (p := p) (X := X) (R := R) f
  exact ⟨Y, φ, hφ⟩


end AbsoluteInertiaFibered

/-- The projection from the absolute inertia of a fibred category over `C` is fibred. -/
theorem absoluteInertiaProjection_isFibered
    (X : FibredCategoryOver.{u, v, u, v} C) :
    (CategoryOver.absoluteInertiaOver X.toCategoryOver).p.IsFibered := by
  simpa [CategoryOver.absoluteInertiaOver, CategoryOver.relativeInertiaOver, BasedCategory.toBase]
    using relativeInertiaProjection_self_isFibered (p := X.p)

instance (X : FibredCategoryOver.{u, v, u, v} C) :
    (CategoryOver.absoluteInertiaOver X.toCategoryOver).p.IsFibered :=
  absoluteInertiaProjection_isFibered X

/-- 4.34.2.4: forgetting the condition that the automorphism becomes the identity in `S'` defines
the canonical comparison morphism `\mathcal{I}_{\mathcal{S}/\mathcal{S}'} \to
\mathcal{I}_{\mathcal{S}}`. -/
abbrev relativeInertiaToAbsoluteInertia (F : S ⥤ᵇ S') :
    relativeInertiaOver F ⥤ᵇ CategoryOver.absoluteInertiaOver S :=
  { toFunctor := relativeInertiaMap (𝟭 S.obj) S'.p (eqToIso F.w)
    w := rfl }

-- Proof sketch: unfold the based functor defining the comparison morphism.
/-- The comparison morphism has the expected underlying relative inertia functor. -/
theorem relativeInertiaToAbsoluteInertia_toFunctor (F : S ⥤ᵇ S') :
    (relativeInertiaToAbsoluteInertia F).toFunctor =
      relativeInertiaMap (𝟭 S.obj) S'.p (eqToIso F.w) := by
  -- Unfolding the packaged comparison morphism exposes the defining relative inertia functor.
  rfl

end CategoryOver
end CategoryTheory
