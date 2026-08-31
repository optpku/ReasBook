module

public import stacks_project.Chap04.«4_34_2_4»
public import stacks_project.Chap04.Definition_4_35_1
public import stacks_project.Chap04.Lemma_4_35_2

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

universe v₁ u₁ u₂

namespace CategoryTheory

open CategoryOver Functor Functor.Fiber IsHomLift

variable {C : Type u₁} [Category.{v₁} C]

/- Domain-style sampling for Lemma 4.35.12:
- primary domain: relative/absolute inertia projections over a fixed base and the owner predicate
  `IsFibredInGroupoids`;
- inspected owner-level declarations:
  `relativeInertiaProjection`,
  `CategoryOver.absoluteInertiaOver`,
  `CategoryOver.absoluteInertiaProjection_isFibered`,
  `IsFibredInGroupoids`,
  `isFibredInGroupoids_of_isFibered_and_fiber_groupoid`,
  `RelativeInertiaHom.isIso_of_isIso`;
- best owner abstraction: the core theorem should live on the raw projection
  `relativeInertiaProjection p p`; the `Cat/C` theorem for `absoluteInertiaOver 𝒮` is only the
  source-facing bridge obtained by packaging the same owner;
- primitive data: only a functor `p : S ⥤ C` together with the existing
  `IsFibredInGroupoids p` structure;
- derived API: the bridge theorem and bundled instance for `absoluteInertiaOver`, obtained by
  reusing the existing fibredness owner theorem and checking that each inertia fiber is again a
  groupoid.

Source/core/bridge triage:
- `source-facing`: `absoluteInertiaProjection_isFibredInGroupoids`;
- `core/canonical`: `relativeInertiaProjection`, `Functor.Fiber`, and
  `IsFibredInGroupoids`;
- `bridge/view`: the definitional identification
  `(absoluteInertiaOver (BasedCategory.ofFunctor p)).p = relativeInertiaProjection p p`. -/

variable {S : Type u₂} [Category.{v₁} S]

section

variable (p : S ⥤ C) [IsFibredInGroupoids p]

/-- Helper for Lemma 4.35.12: every arrow of the identity functor on the base category is
strongly cartesian over itself. -/
private theorem idFunctor_isStronglyCartesian {R T : C} (f : R ⟶ T) :
    Functor.IsStronglyCartesian (𝟭 C) f f where
  -- The identity functor turns the displayed arrow into a tautological lift of itself.
  toIsHomLift := by
    simpa using
      (show Functor.IsHomLift (𝟭 C) ((𝟭 C).map f) f from inferInstance)
  universal_property' := by
    intro a g φ hφ
    -- Any competing lift over `g ≫ f` is definitionally the same composite.
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

/-- Helper for Lemma 4.35.12: the identity functor on the base category is fibered. -/
private theorem idFunctor_isFibered : (𝟭 C).IsFibered := by
  -- For a base arrow `f`, choose `f` itself as a strongly cartesian lift.
  apply Functor.IsFibered.of_exists_isStronglyCartesian
  intro a R f
  exact ⟨R, f, idFunctor_isStronglyCartesian (C := C) f⟩

omit [IsFibredInGroupoids p] in
/-- Helper for Lemma 4.35.12: a vertical automorphism of an inertia object pulls back along a
strongly cartesian lift of its source object. -/
private theorem pullback_automorphism_hom
    {X : RelativeInertiaObject p} {R : C} {y : S} {f : R ⟶ p.obj X.x}
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

omit [IsFibredInGroupoids p] in
/-- Helper for Lemma 4.35.12: the pulled-back vertical endomorphism is again an automorphism. -/
private theorem pullback_automorphism_iso
    {X : RelativeInertiaObject p} {R : C} {y : S} {f : R ⟶ p.obj X.x}
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
private theorem relativeInertiaProjection_isFibered_self :
    (relativeInertiaProjection p p).IsFibered := by
  -- Route correction: build the strongly cartesian lift directly in the inertia category, rather
  -- than passing through a homogeneous owner theorem that fixes the total-category universe.
  refine Functor.IsFibered.of_exists_isStronglyCartesian ?_
  intro X R f
  obtain ⟨Y, φ, hφ⟩ :=
    relative_inertia_lift_isStronglyCartesian (p := p) (X := X) (R := R) f
  exact ⟨Y, φ, hφ⟩

/-- Helper for Lemma 4.35.12: every morphism in a standard fiber of the absolute inertia
projection is an isomorphism. -/
private theorem relativeInertiaProjection_fiber_hom_isIso
    (U : C) {X Y : (relativeInertiaProjection p p).Fiber U} (φ : X ⟶ Y) :
    IsIso φ := by
  let q := relativeInertiaProjection p p
  letI : q.IsHomLift (𝟙 U) φ.1 := φ.2
  -- Forgetting the inertia structure shows that the underlying morphism lies in the fiber of `p`.
  letI : p.IsHomLift (𝟙 U) φ.1.φ := by
    refine of_fac' p (𝟙 U) φ.1.φ ?_ ?_ ?_
    · simpa [q, relativeInertiaProjection] using domain_eq q (𝟙 U) φ.1
    · simpa [q, relativeInertiaProjection] using codomain_eq q (𝟙 U) φ.1
    · simpa [q, relativeInertiaProjection] using fac' q (𝟙 U) φ.1
  -- The underlying vertical morphism is invertible in the fiber of `p`, hence also in `S`.
  letI : IsIso (homMk p U φ.1.φ) :=
    IsFibredInGroupoids.hom_isIso U (homMk p U φ.1.φ)
  letI : IsIso φ.1.φ := by
    simpa using
      (inferInstance : IsIso ((fiberInclusion : p.Fiber U ⥤ _).map (homMk p U φ.1.φ)))
  letI : IsIso φ.1 := RelativeInertiaHom.isIso_of_isIso φ.1
  -- The inverse of a vertical isomorphism still lies over the identity, so it defines the
  -- inverse in the inertia fiber.
  letI : q.IsHomLift (𝟙 U) (inv φ.1) := by
    simpa [q] using lift_id_inv_isIso q U φ.1
  refine ⟨?_⟩
  use ⟨inv φ.1, inferInstance⟩
  constructor
  · apply Fiber.hom_ext
    change φ.1 ≫ inv φ.1 = 𝟙 X.1
    simp
  · apply Fiber.hom_ext
    change inv φ.1 ≫ φ.1 = 𝟙 Y.1
    simp

/-- Helper for Lemma 4.35.12: each standard fiber of the absolute inertia projection is a
groupoid. -/
private instance relativeInertiaProjection_fiber_isGroupoid
    (U : C) :
    IsGroupoid ((relativeInertiaProjection p p).Fiber U) where
  all_isIso := relativeInertiaProjection_fiber_hom_isIso p U

-- Proof sketch: reuse the canonical owner theorem
-- `CategoryOver.absoluteInertiaProjection_isFibered` for the projection part, then apply
-- Lemma `4.35.2` and check directly that each inertia fiber is a groupoid because a morphism in
-- the inertia fiber is a vertical morphism in `S`, hence an isomorphism.
/-- Owner-level form of Lemma 4.35.12: if `p : S ⥤ C` is fibred in groupoids, then its absolute
inertia projection `relativeInertiaProjection p p : I_S ⥤ C` is again fibred in groupoids. The
source-facing `Cat/C` packaging is the companion theorem
`CategoryOver.absoluteInertiaProjection_isFibredInGroupoids`. -/
theorem relativeInertiaProjection_isFibredInGroupoids :
    IsFibredInGroupoids (relativeInertiaProjection p p) := by
  refine
    isFibredInGroupoids_of_isFibered_and_fiber_groupoid
      (relativeInertiaProjection p p)
      ?_
      ?_
  · simpa using
      relativeInertiaProjection_isFibered_self (p := p)
  · intro U
    infer_instance

end

-- Proof sketch: this is only the `Cat/C` bridge form of
-- `relativeInertiaProjection_isFibredInGroupoids`, since `(absoluteInertiaOver 𝒮).p` is
-- definitionally `relativeInertiaProjection 𝒮.p 𝒮.p`.
namespace CategoryOver

/-- Lemma 4.35.12: if `p : S ⥤ C` is fibred in groupoids, then the inertia fibred category
`I_S → C` is again fibred in groupoids over `C`. -/
theorem absoluteInertiaProjection_isFibredInGroupoids
    (𝒮 : BasedCategory.{v₁, u₁} C) [IsFibredInGroupoids 𝒮.p] :
    IsFibredInGroupoids (absoluteInertiaOver 𝒮).p := by
  simpa [absoluteInertiaOver] using relativeInertiaProjection_isFibredInGroupoids 𝒮.p

/-- The absolute inertia projection inherits the canonical `IsFibredInGroupoids` instance from
Lemma 4.35.12. -/
instance (𝒮 : BasedCategory.{v₁, u₁} C) [IsFibredInGroupoids 𝒮.p] :
    IsFibredInGroupoids (absoluteInertiaOver 𝒮).p :=
  absoluteInertiaProjection_isFibredInGroupoids 𝒮

end CategoryOver

end CategoryTheory
