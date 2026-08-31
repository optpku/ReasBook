module

public import Mathlib.CategoryTheory.Sites.CoverLifting
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Sites.Grothendieck
public import Mathlib.CategoryTheory.Sites.LocallyBijective
public import Mathlib.CategoryTheory.Adjunction.Comma
public import Mathlib.CategoryTheory.Limits.Shapes.Terminal
public import Mathlib.CategoryTheory.Limits.Preserves.Ulift
public import Mathlib.CategoryTheory.Limits.Types.Multiequalizer
public import Mathlib.CategoryTheory.UnivLE
public import Mathlib.Logic.Small.Basic
import Mathlib.Tactic.Recall
public import stacks_project.Chap07.Definition_7_42_3
public import stacks_project.Chap07.Lemma_7_42_4.Index
@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Opposite CategoryTheory.GrothendieckTopology.Plus

universe u₁ u₂ u₃ v₁ v₂ v₃ w r

namespace CategoryTheory.Functor

variable {C : Type u₁} [Category.{v₁} C]
variable {D : Type u₂} [Category.{v₂} D]

section

variable (u : C ⥤ D) (J : GrothendieckTopology C) (K : GrothendieckTopology D)
variable [HasWeakSheafify J (Type w)] [HasWeakSheafify K (Type w)]
variable [K.WEqualsLocallyBijective (Type w)]
variable [u.IsContinuous J K] [u.IsAlmostCocontinuous J K]

/- Domain-style sampling for Lemma 7.42.4:
- primary domain: sheafification comparison for inverse image along continuous, almost
  cocontinuous functors of sites;
- sampled owner declarations:
  `Functor.IsAlmostCocontinuous`,
  `GrothendieckTopology.IsSheafTheoreticallyEmpty`,
  `GrothendieckTopology.sheafTheoreticallyEmpty_iff_forall_unique_sections`,
  `Functor.pushforwardContinuousSheafificationCompatibility_hom_app_hom`;
- best owner abstraction: the canonical comparison morphism
  `sheafifyLift J (whiskerLeft u.op <| toSheafify K G) ...`, determined directly by the weak
  sheafification universal property;
- primitive data: the site functor `u`, the topologies `J` and `K`, weak sheafification on both
  sites, the formal `W =` local-bijectivity package for `Type w` on `K`, the continuity and
  almost-cocontinuity hypotheses, the presheaf `G`, and the singleton-over-sheaf-theoretically-empty
  hypothesis on `G`;
- derived API: under the stronger cocontinuity hypothesis, the identification of the source
  comparison morphism with the `hom` of the `G`-component of the canonical mathlib
  compatibility isomorphism.

Source/core/bridge triage:
- `source-facing`: the Stacks Project theorem that the comparison morphism
  `(uᵖ G)^# ⟶ uᵖ (G^#)` is an isomorphism under continuity, almost cocontinuity, and the
  singleton condition on sheaf-theoretically empty objects;
- `core/canonical`: the canonical comparison morphism produced by `sheafifyLift`; the extra
  `K.WEqualsLocallyBijective (Type w)` assumption is the Lean-side package that makes the
  sheafification unit locally injective in the target site;
- `bridge/view`: when `u` is cocontinuous, the theorem
  `pushforwardContinuousSheafificationCompatibility_hom_app_hom` identifies that source-facing
  comparison morphism with the component of the canonical mathlib compatibility isomorphism.

The previous refinement failed by rebuilding the proof through a global
`WEqualsLocallyBijective` universe bridge. The source-faithful route below only needs local
surjectivity of the sheafification unit and local bijectivity of the whiskered comparison map,
which are proved directly from cover lifting and the empty-image uniqueness hypothesis. -/

/-- Helper for Lemma 7.42.4: under a universe inequality, a function between small type
carriers transports to their `Shrink` models. -/
@[implicit_reducible] private noncomputable def typeShrinkMap
    [UnivLE.{w, r}] {X Y : Type w} (f : X ⟶ Y) :
    Shrink.{r} X → Shrink.{r} Y :=
  fun x ↦ equivShrink Y (f ((equivShrink X).symm x))

/-- Helper for Lemma 7.42.4: shrink transport respects identity maps. -/
private theorem typeShrinkMap_id
    [UnivLE.{w, r}] (X : Type w) :
    typeShrinkMap (𝟙 X) = id := by
  funext x
  change equivShrink X ((𝟙 X) ((equivShrink X).symm x)) = x
  simp

/-- Helper for Lemma 7.42.4: shrink transport respects composition of maps. -/
private theorem typeShrinkMap_comp
    [UnivLE.{w, r}] {X Y Z : Type w} (f : X ⟶ Y) (g : Y ⟶ Z) :
    typeShrinkMap (f ≫ g) = typeShrinkMap g ∘ typeShrinkMap f := by
  funext x
  change equivShrink Z (g (f ((equivShrink X).symm x))) =
    equivShrink Z (g ((equivShrink Y).symm (equivShrink Y (f ((equivShrink X).symm x)))))
  simp

/-- Helper for Lemma 7.42.4: shrink-transported functions can be unshrunk to ordinary maps. -/
@[implicit_reducible] private noncomputable def shrinkHom
    [UnivLE.{w, r}] (X Y : Type w) : Type r :=
  Shrink.{r} X → Shrink.{r} Y

/-- Helper for Lemma 7.42.4: shrink-transported maps are function-like. -/
private instance shrinkHomFunLike [UnivLE.{w, r}] (X Y : Type w) :
    FunLike (shrinkHom.{w, r} X Y) (Shrink.{r} X) (Shrink.{r} Y) where
  coe f := f
  coe_injective' := by
    intro f g h
    funext x
    exact congrFun h x

/-- Helper for Lemma 7.42.4: unshrinking a map of shrink carriers gives an ordinary function. -/
@[implicit_reducible] private noncomputable def shrinkHomToFunction
    [UnivLE.{w, r}] {X Y : Type w} (f : shrinkHom.{w, r} X Y) : X ⟶ Y :=
  fun x ↦ (equivShrink Y).symm (f (equivShrink X x))

/-- Helper for Lemma 7.42.4: shrinking after unshrinking recovers a shrink-carrier map. -/
private theorem typeShrinkMap_shrinkHomToFunction
    [UnivLE.{w, r}] {X Y : Type w} (f : shrinkHom.{w, r} X Y) :
    typeShrinkMap (shrinkHomToFunction f) = f := by
  funext x
  simp [typeShrinkMap, shrinkHomToFunction]

/-- Helper for Lemma 7.42.4: unshrinking after shrinking recovers the original function. -/
private theorem shrinkHomToFunction_typeShrinkMap
    [UnivLE.{w, r}] {X Y : Type w} (f : X ⟶ Y) :
    shrinkHomToFunction (typeShrinkMap f) = f := by
  funext x
  simp [typeShrinkMap, shrinkHomToFunction]

/-- Helper for Lemma 7.42.4: shrink transport fixes identity maps pointwise. -/
private theorem typeShrinkMap_id_apply [UnivLE.{w, r}] {X : Type w}
    (x : Shrink.{r} X) :
    typeShrinkMap (𝟙 X) x = x := by
  simpa using congrFun (typeShrinkMap_id (X := X)) x

/-- Helper for Lemma 7.42.4: shrink transport computes on composites pointwise. -/
private theorem typeShrinkMap_comp_apply
    [UnivLE.{w, r}] {X Y Z : Type w} (f : X ⟶ Y) (g : Y ⟶ Z)
    (x : Shrink.{r} X) :
    typeShrinkMap (f ≫ g) x = typeShrinkMap g (typeShrinkMap f x) := by
  simpa using congrFun (typeShrinkMap_comp (f := f) (g := g)) x

/-- Helper for Lemma 7.42.4: `Type w` is concrete over resized `Shrink` carriers. -/
@[implicit_reducible]
private noncomputable def shrinkConcreteCategory [UnivLE.{w, r}] :
    ConcreteCategory.{r} (Type w) (shrinkHom.{w, r}) where
  hom f := typeShrinkMap f
  ofHom f := shrinkHomToFunction f
  hom_ofHom f := typeShrinkMap_shrinkHomToFunction f
  ofHom_hom f := shrinkHomToFunction_typeShrinkMap f
  id_apply x := typeShrinkMap_id_apply x
  comp_apply f g x := typeShrinkMap_comp_apply f g x

/-- Helper for Lemma 7.42.4: local injectivity for ordinary `Type w` sections remains local
injectivity after replacing carriers by their resized `Shrink` models. -/
private theorem isLocallyInjective_shrink
    [UnivLE.{w, r}] {E : Type u₃} [Category.{v₃} E] {L : GrothendieckTopology E}
    {P Q : Eᵒᵖ ⥤ Type w} (η : P ⟶ Q)
    (hη : Presheaf.IsLocallyInjective L η) :
    letI : ConcreteCategory.{r} (Type w) (shrinkHom.{w, r}) := shrinkConcreteCategory
    Presheaf.IsLocallyInjective L η := by
  letI : ConcreteCategory.{r} (Type w) (shrinkHom.{w, r}) := shrinkConcreteCategory
  refine ⟨fun {X} xs ys hxy ↦ ?_⟩
  -- Unshrink the equal pair, apply ordinary local injectivity, and then shrink the local
  -- equalizer relation back to the resized carrier.
  change typeShrinkMap (η.app X) xs = typeShrinkMap (η.app X) ys at hxy
  let x : P.obj X := (equivShrink (P.obj X)).symm xs
  let y : P.obj X := (equivShrink (P.obj X)).symm ys
  have hxyOrd : η.app X x = η.app X y := by
    apply (equivShrink (Q.obj X)).injective
    simpa [typeShrinkMap, x, y] using hxy
  let SOrd : Sieve X.unop :=
    { arrows := fun Y f ↦ P.map f.op x = P.map f.op y
      downward_closed := by
        intro Y Z f hf g
        simpa [op_comp] using congrArg (P.map g.op) hf }
  have hSOrd : SOrd ∈ L X.unop := by
    letI : ConcreteCategory (Type w) (fun X Y : Type w ↦ X ⟶ Y) :=
      Types.instConcreteCategory
    let _ : Presheaf.IsLocallyInjective L η := hη
    simpa [SOrd, Presheaf.equalizerSieve] using
      (Presheaf.equalizerSieve_mem L η x y hxyOrd)
  refine L.superset_covering ?_ hSOrd
  intro Y f hf
  dsimp [SOrd] at hf
  change typeShrinkMap (P.map f.op) xs = typeShrinkMap (P.map f.op) ys
  simpa [typeShrinkMap, x, y] using congrArg (equivShrink (P.obj (op Y))) hf

/-- Helper for Lemma 7.42.4: local surjectivity for ordinary `Type w` sections remains local
surjectivity after replacing carriers by their resized `Shrink` models. -/
private theorem isLocallySurjective_shrink
    [UnivLE.{w, r}] {E : Type u₃} [Category.{v₃} E] {L : GrothendieckTopology E}
    {P Q : Eᵒᵖ ⥤ Type w} (η : P ⟶ Q)
    (hη : Presheaf.IsLocallySurjective L η) :
    letI : ConcreteCategory.{r} (Type w) (shrinkHom.{w, r}) := shrinkConcreteCategory
    Presheaf.IsLocallySurjective L η := by
  letI : ConcreteCategory.{r} (Type w) (shrinkHom.{w, r}) := shrinkConcreteCategory
  refine ⟨fun {X} xs ↦ ?_⟩
  -- Unshrink the target section, use ordinary local surjectivity, then shrink the local
  -- preimages back to the resized carrier.
  let x : Q.obj (op X) := (equivShrink (Q.obj (op X))).symm xs
  have hSOrd_downward :
      ∀ {Y Z : E} {f : Y ⟶ X}, (∃ y : P.obj (op Y), η.app (op Y) y = Q.map f.op x) →
        (g : Z ⟶ Y) → ∃ y : P.obj (op Z), η.app (op Z) y = Q.map (g ≫ f).op x := by
    intro Y Z f hf g
    rcases hf with ⟨y, hy⟩
    refine ⟨P.map g.op y, ?_⟩
    calc
      η.app (op Z) (P.map g.op y)
          = Q.map g.op (η.app (op Y) y) := FunctorToTypes.naturality _ _ η g.op y
      _ = Q.map g.op (Q.map f.op x) := by rw [hy]
      _ = (Q.map f.op ≫ Q.map g.op) x := rfl
      _ = Q.map (f.op ≫ g.op) x := by rw [Q.map_comp]
      _ = Q.map (g ≫ f).op x := by rw [op_comp]
  let SOrd : Sieve X :=
    { arrows := fun Y f ↦ ∃ y : P.obj (op Y), η.app (op Y) y = Q.map f.op x
      downward_closed := hSOrd_downward }
  have hSOrd : SOrd ∈ L X := by
    letI : ConcreteCategory (Type w) (fun X Y : Type w ↦ X ⟶ Y) :=
      Types.instConcreteCategory
    let _ : Presheaf.IsLocallySurjective L η := hη
    simpa [SOrd, Presheaf.imageSieve] using
      (Presheaf.imageSieve_mem L η x)
  refine L.superset_covering ?_ hSOrd
  intro Y f hf
  dsimp [SOrd] at hf
  rcases hf with ⟨y, hy⟩
  refine ⟨equivShrink (P.obj (op Y)) y, ?_⟩
  change typeShrinkMap (η.app (op Y)) (equivShrink (P.obj (op Y)) y) =
    typeShrinkMap (Q.map f.op) xs
  simpa [typeShrinkMap, x] using congrArg (equivShrink (Q.obj (op Y))) hy

/-- Helper for Lemma 7.42.4: local injectivity computed on resized carriers reflects to the
ordinary type-valued concrete structure. -/
private theorem locallyInjective_of_shrink
    [UnivLE.{w, r}] {E : Type u₃} [Category.{v₃} E] {L : GrothendieckTopology E}
    {P Q : Eᵒᵖ ⥤ Type w} (η : P ⟶ Q)
    (hη :
      letI : ConcreteCategory.{r} (Type w) (shrinkHom.{w, r}) := shrinkConcreteCategory
      Presheaf.IsLocallyInjective L η) :
    Presheaf.IsLocallyInjective L η where
  equalizerSieve_mem {X} x y hxy := by
    let xs : Shrink.{r} (P.obj X) := equivShrink (P.obj X) x
    let ys : Shrink.{r} (P.obj X) := equivShrink (P.obj X) y
    have hxyShrink : typeShrinkMap (η.app X) xs = typeShrinkMap (η.app X) ys := by
      simpa [typeShrinkMap, xs, ys] using hxy
    letI : ConcreteCategory.{r} (Type w) (shrinkHom.{w, r}) := shrinkConcreteCategory
    have hS : Presheaf.equalizerSieve (F := P) xs ys ∈ L X.unop :=
      Presheaf.equalizerSieve_mem L η xs ys hxyShrink
    -- Unshrink the local equalizer relation back to the ordinary carrier.
    refine L.superset_covering ?_ hS
    intro Y f hf
    change typeShrinkMap (P.map f.op) xs = typeShrinkMap (P.map f.op) ys at hf
    change P.map f.op x = P.map f.op y
    apply (equivShrink (P.obj (op Y))).injective
    simpa [typeShrinkMap, xs, ys] using hf

/-- Helper for Lemma 7.42.4: the shrink-valued forgetful functor for `Type w`. -/
@[implicit_reducible] private noncomputable def shrinkForget [UnivLE.{w, r}] :
    Type w ⥤ Type r :=
  letI : ConcreteCategory.{r} (Type w) (shrinkHom.{w, r}) := shrinkConcreteCategory
  CategoryTheory.forget (Type w)

/-- Helper for Lemma 7.42.4: the shrink forgetful functor computes by `typeShrinkMap`. -/
private theorem shrinkForget_map_apply [UnivLE.{w, r}] {X Y : Type w}
    (f : X ⟶ Y) (x : Shrink.{r} X) :
    (shrinkForget.{w, r}).map f x = typeShrinkMap f x := by
  -- The concrete `forget` functor is defined through `ConcreteCategory.hom`.
  rfl

/-- Helper for Lemma 7.42.4: the shrink-valued forgetful functor reflects isomorphisms. -/
private theorem shrinkForget_reflectsIsomorphisms [UnivLE.{w, r}] :
    (shrinkForget.{w, r}).ReflectsIsomorphisms where
  reflects {X Y} f hf := by
    -- A bijection after shrinking transfers across the objectwise `equivShrink` equivalences.
    rw [CategoryTheory.isIso_iff_bijective]
    have hfBij : Function.Bijective (typeShrinkMap f : Shrink.{r} X → Shrink.{r} Y) := by
      rw [← CategoryTheory.isIso_iff_bijective]
      simpa [shrinkForget_map_apply] using hf
    constructor
    · intro x y hxy
      apply (equivShrink X).injective
      apply hfBij.1
      simpa [typeShrinkMap] using congrArg (equivShrink Y) hxy
    · intro y
      obtain ⟨sx, hsx⟩ := hfBij.2 (equivShrink Y y)
      refine ⟨(equivShrink X).symm sx, ?_⟩
      apply (equivShrink Y).injective
      simpa [typeShrinkMap] using hsx

/-- Helper for Lemma 7.42.4: the shrink concrete-category forgetful functor preserves sheaves. -/
private theorem shrinkForget_isSheaf
    [UnivLE.{w, r}] {E : Type u₃} [Category.{v₃} E]
    {L : GrothendieckTopology E} {P : Eᵒᵖ ⥤ Type w}
    (hP : Presheaf.IsSheaf L P) :
    Presheaf.IsSheaf L (P ⋙ shrinkForget.{w, r}) := by
  -- Convert sheafness to type-valued sheafness and transport it across `equivShrink`.
  rw [isSheaf_iff_isSheaf_of_type]
  refine Presieve.isSheaf_of_nat_equiv
    (e := fun X ↦ equivShrink (P.obj (op X))) (he := ?_) ?_
  · intro X Y f x
    -- Naturality is exactly the computation rule for the shrink-valued forgetful functor.
    change equivShrink (P.obj (op X)) (P.map f.op x) =
      (shrinkForget.{w, r}).map (P.map f.op) (equivShrink (P.obj (op Y)) x)
    rw [shrinkForget_map_apply]
    simp [typeShrinkMap]
  · exact (isSheaf_iff_isSheaf_of_type L P).1 hP

/-- Helper for Lemma 7.42.4: sheaves remain sheaves after the shrink forgetful functor. -/
private theorem shrinkForget_hasSheafCompose
    [UnivLE.{w, r}] {E : Type u₃} [Category.{v₃} E] (L : GrothendieckTopology E) :
    L.HasSheafCompose (shrinkForget.{w, r}) where
  isSheaf P hP := by
    -- Package the objectwise shrink equivalence as the sheaf-compose owner.
    exact shrinkForget_isSheaf (L := L) hP

/-- Helper for Lemma 7.42.4: local injectivity survives whiskering by the resized shrink-valued
forgetful functor. -/
private theorem isLocallyInjective_whisker_shrinkForget
    [UnivLE.{w, r}] {E : Type u₃} [Category.{v₃} E] {L : GrothendieckTopology E}
    {P Q : Eᵒᵖ ⥤ Type w} (η : P ⟶ Q)
    (hη : Presheaf.IsLocallyInjective L η) :
    Presheaf.IsLocallyInjective L (Functor.whiskerRight η (shrinkForget.{w, r})) where
  equalizerSieve_mem {X} xs ys hxy := by
    -- Translate equality after the shrink-valued map back to equality of ordinary sections.
    change (shrinkForget.{w, r}).map (η.app X) xs =
      (shrinkForget.{w, r}).map (η.app X) ys at hxy
    rw [shrinkForget_map_apply, shrinkForget_map_apply] at hxy
    let x : P.obj X := (equivShrink (P.obj X)).symm xs
    let y : P.obj X := (equivShrink (P.obj X)).symm ys
    have hxyOrd : η.app X x = η.app X y := by
      have hxyShrink :
          (equivShrink.{r, w} (Q.obj X)) (η.app X x) =
            (equivShrink.{r, w} (Q.obj X)) (η.app X y) := by
        simpa only [typeShrinkMap, x, y] using hxy
      exact (Equiv.apply_eq_iff_eq (equivShrink.{r, w} (Q.obj X))).1 hxyShrink
    have hSOrd_downward :
        ∀ {Y Z : E} {f : Y ⟶ X.unop}, P.map f.op x = P.map f.op y →
          (g : Z ⟶ Y) → P.map (g ≫ f).op x = P.map (g ≫ f).op y := by
      intro Y Z f hf g
      simpa [op_comp] using congrArg (P.map g.op) hf
    let SOrd : Sieve X.unop :=
      { arrows := fun Y f ↦ P.map f.op x = P.map f.op y
        downward_closed := hSOrd_downward }
    have hSOrd : SOrd ∈ L X.unop := by
      let _ : Presheaf.IsLocallyInjective L η := hη
      simpa [SOrd, Presheaf.equalizerSieve] using
        (Presheaf.equalizerSieve_mem L η x y hxyOrd)
    refine L.superset_covering ?_ hSOrd
    intro Y f hf
    dsimp [SOrd] at hf
    -- Shrink the ordinary local equalizer relation back to the whiskered equalizer sieve.
    change (shrinkForget.{w, r}).map (P.map f.op) xs =
      (shrinkForget.{w, r}).map (P.map f.op) ys
    rw [shrinkForget_map_apply, shrinkForget_map_apply]
    change typeShrinkMap (P.map f.op) xs = typeShrinkMap (P.map f.op) ys
    simpa [typeShrinkMap, x, y] using congrArg (equivShrink (P.obj (op Y))) hf

/-- Helper for Lemma 7.42.4: local surjectivity survives whiskering by the resized shrink-valued
forgetful functor. -/
private theorem isLocallySurjective_whisker_shrinkForget
    [UnivLE.{w, r}] {E : Type u₃} [Category.{v₃} E] {L : GrothendieckTopology E}
    {P Q : Eᵒᵖ ⥤ Type w} (η : P ⟶ Q)
    (hη : Presheaf.IsLocallySurjective L η) :
    Presheaf.IsLocallySurjective L (Functor.whiskerRight η (shrinkForget.{w, r})) where
  imageSieve_mem {X} xs := by
    -- Unshrink the target section, use ordinary local surjectivity, then shrink the chosen
    -- local preimages back to the whiskered morphism.
    let x : Q.obj (op X) := (equivShrink (Q.obj (op X))).symm xs
    have hSOrd_downward :
        ∀ {Y Z : E} {f : Y ⟶ X}, (∃ y : P.obj (op Y), η.app (op Y) y = Q.map f.op x) →
          (g : Z ⟶ Y) → ∃ y : P.obj (op Z), η.app (op Z) y = Q.map (g ≫ f).op x := by
      intro Y Z f hf g
      rcases hf with ⟨y, hy⟩
      refine ⟨P.map g.op y, ?_⟩
      calc
        η.app (op Z) (P.map g.op y)
            = Q.map g.op (η.app (op Y) y) := FunctorToTypes.naturality _ _ η g.op y
        _ = Q.map g.op (Q.map f.op x) := by rw [hy]
        _ = (Q.map f.op ≫ Q.map g.op) x := rfl
        _ = Q.map (f.op ≫ g.op) x := by rw [Q.map_comp]
        _ = Q.map (g ≫ f).op x := by rw [op_comp]
    let SOrd : Sieve X :=
      { arrows := fun Y f ↦ ∃ y : P.obj (op Y), η.app (op Y) y = Q.map f.op x
        downward_closed := hSOrd_downward }
    have hSOrd : SOrd ∈ L X := by
      let _ : Presheaf.IsLocallySurjective L η := hη
      simpa [SOrd, Presheaf.imageSieve] using
        (Presheaf.imageSieve_mem L η x)
    refine L.superset_covering ?_ hSOrd
    intro Y f hf
    dsimp [SOrd] at hf
    rcases hf with ⟨y, hy⟩
    refine ⟨equivShrink (P.obj (op Y)) y, ?_⟩
    change (shrinkForget.{w, r}).map (η.app (op Y)) (equivShrink (P.obj (op Y)) y) =
      (shrinkForget.{w, r}).map (Q.map f.op) xs
    rw [shrinkForget_map_apply, shrinkForget_map_apply]
    change typeShrinkMap (η.app (op Y)) (equivShrink (P.obj (op Y)) y) =
      typeShrinkMap (Q.map f.op) xs
    simpa [typeShrinkMap, x] using congrArg (equivShrink (Q.obj (op Y))) hy

/-- Helper for Lemma 7.42.4: if `W` already agrees with local bijectivity in the source and
resized target universes, the shrink-valued forgetful functor preserves sheafification. -/
private theorem shrinkForget_preservesSheafification_of_WEqualsLocallyBijective
    [UnivLE.{w, r}] {E : Type u₃} [Category.{v₃} E] (L : GrothendieckTopology E)
    [HasWeakSheafify L (Type w)] [HasWeakSheafify L (Type r)]
    [L.WEqualsLocallyBijective (Type w)] [L.WEqualsLocallyBijective (Type r)] :
    L.PreservesSheafification (shrinkForget.{w, r}) where
  le P Q η hη := by
    -- Convert the source `W`-hypothesis to local bijectivity and transport both halves through
    -- the shrink-valued forgetful functor.
    let hBij := (L.W_iff_isLocallyBijective η).1 hη
    let _ : Presheaf.IsLocallyInjective L
        (Functor.whiskerRight η (shrinkForget.{w, r})) :=
      isLocallyInjective_whisker_shrinkForget (L := L) η hBij.1
    let _ : Presheaf.IsLocallySurjective L
        (Functor.whiskerRight η (shrinkForget.{w, r})) :=
      isLocallySurjective_whisker_shrinkForget (L := L) η hBij.2
    -- The target `W =` locally-bijective package turns the transported local data back into `W`.
    exact
      GrothendieckTopology.W_of_isLocallyBijective
        (J := L) (f := Functor.whiskerRight η (shrinkForget.{w, r}))

/-- Helper for Lemma 7.42.4: the image sieve of the identity section under a shrink-functor
inclusion is the original sieve. -/
private theorem imageSieve_shrinkFunctor_ι_identity
    {E : Type u₃} [Category.{v₃} E] [LocallySmall.{r} E] {X : E} (S : Sieve X) :
    Presheaf.imageSieve (Sieve.shrinkFunctor.{r} S).ι
        (show (shrinkYoneda.{r}.obj X).obj (op X) from
          shrinkYonedaObjObjEquiv.symm (𝟙 X)) =
      S := by
  -- Unpack image-sieve membership; a local preimage is exactly an arrow lying in `S`.
  ext Y g
  constructor
  · rintro ⟨t, ht⟩
    have ht' : t.1 = shrinkYonedaObjObjEquiv.symm g := by
      calc
        t.1 = ((Sieve.shrinkFunctor.{r} S).ι.app (op Y)) t := rfl
        _ =
            (shrinkYoneda.{r}.obj X).map g.op
              (show (shrinkYoneda.{r}.obj X).obj (op X) from
                shrinkYonedaObjObjEquiv.symm (𝟙 X)) := ht
        _ = shrinkYonedaObjObjEquiv.symm g := by
          simpa using shrinkYoneda_obj_map_shrinkYonedaObjObjEquiv_symm g.op (𝟙 X)
    have htg : shrinkYonedaObjObjEquiv t.1 = g := by
      simpa using congrArg shrinkYonedaObjObjEquiv ht'
    simpa [htg] using (show S (shrinkYonedaObjObjEquiv t.1) from t.2)
  · intro hg
    refine ⟨⟨shrinkYonedaObjObjEquiv.symm g, by simpa using hg⟩, ?_⟩
    simpa using (shrinkYoneda_obj_map_shrinkYonedaObjObjEquiv_symm g.op (𝟙 X)).symm

/-- Helper for Lemma 7.42.4: if a shrink-functor inclusion is a `W`-morphism in a universe
where `W` is local bijectivity, then the original sieve is covering. -/
private theorem covering_of_W_shrinkFunctor_ι
    {E : Type u₃} [Category.{v₃} E] [LocallySmall.{r} E]
    {L : GrothendieckTopology E} [L.WEqualsLocallyBijective (Type r)]
    {X : E} {S : Sieve X}
    (hW : L.W ((Sieve.shrinkFunctor.{r} S).ι)) :
    S ∈ L X := by
  -- Convert `W` to local surjectivity and evaluate it on the identity section.
  have hSurj : Presheaf.IsLocallySurjective L ((Sieve.shrinkFunctor.{r} S).ι) :=
    hW.isLocallySurjective
  let x : (shrinkYoneda.{r}.obj X).obj (op X) :=
    shrinkYonedaObjObjEquiv.symm (𝟙 X)
  have hmem : Presheaf.imageSieve (Sieve.shrinkFunctor.{r} S).ι x ∈ L X :=
    hSurj.imageSieve_mem x
  rw [show Presheaf.imageSieve (Sieve.shrinkFunctor.{r} S).ι x = S by
    simpa [x] using imageSieve_shrinkFunctor_ι_identity (S := S)] at hmem
  exact hmem

/-- Helper for Lemma 7.42.4: in a universe where `W` is local bijectivity, a shrink-functor
inclusion is a `W`-morphism exactly when the original sieve is covering. -/
private theorem W_shrinkFunctor_ι_iff_mem
    {E : Type u₃} [Category.{v₃} E] [LocallySmall.{r} E]
    {L : GrothendieckTopology E} [L.WEqualsLocallyBijective (Type r)]
    {X : E} {S : Sieve X} :
    L.W ((Sieve.shrinkFunctor.{r} S).ι) ↔ S ∈ L X := by
  constructor
  · intro hW
    -- Evaluate local surjectivity of the shrink inclusion at the identity section.
    exact covering_of_W_shrinkFunctor_ι (L := L) (S := S) hW
  · intro hS
    -- A covering sieve is inverted by sheafification via the canonical shrink-sieve API.
    exact Sieve.W_shrinkFunctor_ι_of_mem.{r} L S hS

/-- Helper for Lemma 7.42.4: local injectivity of the sheafification unit gives the large
shrink-functor `W` statement for its pointwise equalizer sieve. -/
private theorem W_shrinkFunctor_ι_equalizerSieve_of_toSheafify_eq_of_locallyInjective
    {E : Type u₃} [Category.{v₃} E] [LocallySmall.{r} E]
    (L : GrothendieckTopology E) [HasWeakSheafify L (Type w)]
    {P : Eᵒᵖ ⥤ Type w} {X : Eᵒᵖ} (x y : P.obj X)
    (h : (toSheafify L P).app X x = (toSheafify L P).app X y)
    [Presheaf.IsLocallyInjective L (toSheafify L P)] :
    L.W ((Sieve.shrinkFunctor.{r} (Presheaf.equalizerSieve (F := P) x y)).ι) := by
  -- First read local injectivity as covering of the ordinary equalizer sieve.
  have hS : Presheaf.equalizerSieve (F := P) x y ∈ L X.unop :=
    Presheaf.equalizerSieve_mem L (toSheafify L P) x y h
  -- Then move that cover to the shrink-Yoneda inclusion used by the `W` API.
  exact Sieve.W_shrinkFunctor_ι_of_mem.{r} L (Presheaf.equalizerSieve (F := P) x y) hS

/-- Helper for Lemma 7.42.4: a large-universe `W` statement for the shrink inclusion of a
pointwise equalizer sieve recovers the ordinary covering equalizer sieve. -/
private theorem equalizerSieve_mem_of_W_shrinkFunctor_ι
    {E : Type u₃} [Category.{v₃} E] [LocallySmall.{r} E]
    {L : GrothendieckTopology E} [L.WEqualsLocallyBijective (Type r)]
    {P : Eᵒᵖ ⥤ Type w} {X : Eᵒᵖ} (x y : P.obj X)
    (hW : L.W ((Sieve.shrinkFunctor.{r} (Presheaf.equalizerSieve (F := P) x y)).ι)) :
    Presheaf.equalizerSieve (F := P) x y ∈ L X.unop := by
  -- Convert the shrink-Yoneda `W` statement back through the proved sieve bridge.
  exact
    (W_shrinkFunctor_ι_iff_mem (L := L)
      (S := Presheaf.equalizerSieve (F := P) x y)).1 hW

/-- Helper for Lemma 7.42.4: a `W =` locally-bijective package for `Type w` turns the
sheafification unit's universal `W`-property into local injectivity. -/
private theorem toSheafify_isLocallyInjective_type_of_WEqualsLocallyBijective
    {E : Type u₃} [Category.{v₃} E] (L : GrothendieckTopology E)
    [HasWeakSheafify L (Type w)] [L.WEqualsLocallyBijective (Type w)]
    (P : Eᵒᵖ ⥤ Type w) :
    Presheaf.IsLocallyInjective L (toSheafify L P) := by
  -- Read the canonical `W`-morphism from the unit through the local-bijective comparison.
  exact (L.W_toSheafify P).isLocallyInjective

/-- Helper for Lemma 7.42.4: equality after the sheafification unit is equivalent to equality
after every map from the presheaf into a `Type w`-valued sheaf. -/
private theorem toSheafify_app_eq_iff_forall_sheaf_maps_eq
    {E : Type u₃} [Category.{v₃} E] (L : GrothendieckTopology E)
    [HasWeakSheafify L (Type w)] {P : Eᵒᵖ ⥤ Type w} {X : Eᵒᵖ}
    (x y : P.obj X) :
    (toSheafify L P).app X x = (toSheafify L P).app X y ↔
      ∀ (Q : Eᵒᵖ ⥤ Type w), Presheaf.IsSheaf L Q →
        ∀ f : P ⟶ Q, f.app X x = f.app X y := by
  constructor
  · intro h Q hQ f
    have hf : toSheafify L P ≫ sheafifyLift L f hQ = f :=
      toSheafify_sheafifyLift (J := L) f hQ
    have hmap :
        (sheafifyLift L f hQ).app X ((toSheafify L P).app X x) =
          (sheafifyLift L f hQ).app X ((toSheafify L P).app X y) :=
      congrArg ((sheafifyLift L f hQ).app X) h
    -- Factor `f` through the reflector unit and transport the given equality through the lift.
    have hcomp :
        (toSheafify L P ≫ sheafifyLift L f hQ).app X x =
          (toSheafify L P ≫ sheafifyLift L f hQ).app X y := by
      change
        (sheafifyLift L f hQ).app X ((toSheafify L P).app X x) =
          (sheafifyLift L f hQ).app X ((toSheafify L P).app X y)
      exact hmap
    simpa [hf] using hcomp
  · intro h
    -- Test against the sheafification target itself to recover the original unit equality.
    exact h (sheafify L P) (((presheafToSheaf L (Type w)).obj P).property) (toSheafify L P)

/-- Helper for Lemma 7.42.4: `ULift` does not change the equalizer sieve of two ordinary
sections. -/
private theorem equalizerSieve_whisker_ulift_up
    {E : Type u₃} [Category.{v₃} E]
    {P : Eᵒᵖ ⥤ Type w} {X : Eᵒᵖ} (x y : P.obj X) :
    Presheaf.equalizerSieve
        (F := P ⋙
          (CategoryTheory.uliftFunctor.{max u₃ v₃, w} :
            Type w ⥤ Type (max w (max u₃ v₃))))
        (show
          (P ⋙
            (CategoryTheory.uliftFunctor.{max u₃ v₃, w} :
              Type w ⥤ Type (max w (max u₃ v₃)))).obj X from ULift.up x)
        (show
          (P ⋙
            (CategoryTheory.uliftFunctor.{max u₃ v₃, w} :
              Type w ⥤ Type (max w (max u₃ v₃)))).obj X from ULift.up y) =
      Presheaf.equalizerSieve (F := P) x y := by
  -- Compare membership arrow-by-arrow; `ULift.up` is injective on the resulting section
  -- equality.
  ext Y f
  constructor
  · intro hf
    change ULift.up (P.map f.op x) = ULift.up (P.map f.op y) at hf
    exact ULift.up.inj hf
  · intro hf
    change ULift.up (P.map f.op x) = ULift.up (P.map f.op y)
    exact congrArg ULift.up hf

/-- Helper for Lemma 7.42.4: a large-universe `W` proof for the `ULift`-whiskered
sheafification unit gives the desired small equalizer-sieve cover. -/
private theorem equalizerSieve_mem_of_whiskered_toSheafify_W
    {E : Type u₃} [Category.{v₃} E] (L : GrothendieckTopology E)
    [HasWeakSheafify L (Type w)]
    [HasWeakSheafify L (Type (max w (max u₃ v₃)))]
    {P : Eᵒᵖ ⥤ Type w} {X : Eᵒᵖ} (x y : P.obj X)
    (hW :
      L.W
        (Functor.whiskerRight (toSheafify L P)
          (CategoryTheory.uliftFunctor.{max u₃ v₃, w} :
            Type w ⥤ Type (max w (max u₃ v₃)))))
    (h : (toSheafify L P).app X x = (toSheafify L P).app X y) :
    Presheaf.equalizerSieve (F := P) x y ∈ L X.unop := by
  let F : Type w ⥤ Type (max w (max u₃ v₃)) :=
    CategoryTheory.uliftFunctor.{max u₃ v₃, w}
  let _ : L.WEqualsLocallyBijective (Type (max w (max u₃ v₃))) :=
    large_type_WEqualsLocallyBijective (L := L)
  let _ :
      Presheaf.IsLocallyInjective L (Functor.whiskerRight (toSheafify L P) F) :=
    hW.isLocallyInjective
  let x' : (P ⋙ F).obj X := ULift.up x
  let y' : (P ⋙ F).obj X := ULift.up y
  have hUp :
      (Functor.whiskerRight (toSheafify L P) F).app X x' =
        (Functor.whiskerRight (toSheafify L P) F).app X y' := by
    -- Lift the given equality of small sheafification sections into the ambient universe.
    change ULift.up ((toSheafify L P).app X x) =
      ULift.up ((toSheafify L P).app X y)
    exact congrArg ULift.up h
  have hS :
      Presheaf.equalizerSieve (F := P ⋙ F) x' y' ∈ L X.unop :=
    Presheaf.equalizerSieve_mem L (Functor.whiskerRight (toSheafify L P) F) x' y' hUp
  -- Descend the lifted equalizer sieve back to the original one.
  simpa [F, x', y'] using
    (by
      rw [equalizerSieve_whisker_ulift_up (P := P) (x := x) (y := y)] at hS
      exact hS)

/-- Helper for Lemma 7.42.4: if the opposite of a functor is right adjoint, then every
structured-arrow category over it has `Type w`-valued limits. -/
private theorem rightAdjointOpStructuredArrowHasLimitsType
    {A : Type u₁} [Category.{v₁} A] {B : Type u₂} [Category.{v₂} B]
    (G : A ⥤ B) [G.op.IsRightAdjoint] (X : Bᵒᵖ) :
    Limits.HasLimitsOfShape (StructuredArrow X G.op) (Type w) := by
  -- A right adjoint supplies an initial object in the structured-arrow category.
  let _ : Limits.HasInitial (StructuredArrow X G.op) := by
    exact (CategoryTheory.mkInitialOfLeftAdjoint G.op
      (Adjunction.ofIsRightAdjoint G.op) X).hasInitial
  -- Limits of type-valued diagrams over a category with an initial object are computed there.
  exact ⟨fun _ ↦ by infer_instance⟩

/-- Helper for Lemma 7.42.4: the inverse of the canonical small-model equivalence has the
structured-arrow limit owner required by small-model transport. -/
private theorem smallModelStructuredArrowHasLimitsType
    {E : Type u₃} [Category.{v₃} E] (X : Eᵒᵖ) :
    Limits.HasLimitsOfShape
      (StructuredArrow X (CategoryTheory.equivSmallModel.{max u₃ v₃} E).inverse.op)
      (Type w) := by
  -- The inverse equivalence is right adjoint after taking opposites.
  exact rightAdjointOpStructuredArrowHasLimitsType
    ((CategoryTheory.equivSmallModel.{max u₃ v₃} E).inverse) X

/-- Helper for Lemma 7.42.4: weak sheafification on `Type w` transports from a site to the
induced topology on its canonical small model. -/
private theorem smallModelInducedTopologyHasWeakSheafifyType
    {E : Type u₃} [Category.{v₃} E] (L : GrothendieckTopology E)
    [HasWeakSheafify L (Type w)] :
    HasWeakSheafify
      (((CategoryTheory.equivSmallModel.{max u₃ v₃} E).inverse.inducedTopology L)) (Type w) := by
  let e := CategoryTheory.equivSmallModel.{max u₃ v₃} E
  let _ : ∀ X : (SmallModel.{max u₃ v₃, v₃, u₃} E)ᵒᵖ,
      Limits.HasLimitsOfShape (StructuredArrow X e.functor.op) (Type w) := by
    intro X
    exact rightAdjointOpStructuredArrowHasLimitsType e.functor X
  let _ :
      (e.functor.sheafPushforwardContinuous (Type w) L (e.inverse.inducedTopology L)).IsEquivalence := by
    infer_instance
  -- Dense-subsite equivalence transports the weak reflector to the small model.
  exact Functor.IsDenseSubsite.hasWeakSheafify_of_isEquivalence
    L (e.inverse.inducedTopology L) e.functor (Type w)

/-- Helper for Lemma 7.42.4: a `W =` locally-bijective package on the canonical small model
transports back to the original site. -/
private theorem smallTypeWEqualsLocallyBijectiveOfSmallModelTransport
    {E : Type u₃} [Category.{v₃} E] (L : GrothendieckTopology E)
    [∀ X : Eᵒᵖ,
      Limits.HasLimitsOfShape
        (StructuredArrow X (CategoryTheory.equivSmallModel.{max u₃ v₃} E).inverse.op) (Type w)]
    [GrothendieckTopology.WEqualsLocallyBijective
      ((CategoryTheory.equivSmallModel.{max u₃ v₃} E).inverse.inducedTopology L) (Type w)] :
    L.WEqualsLocallyBijective (Type w) := by
  let _ : CategoryTheory.EssentiallySmall.{max u₃ v₃} E :=
    CategoryTheory.essentiallySmallSelf (C := E)
  -- Apply mathlib's transport theorem for `W =` local bijectivity along the small-model
  -- dense-subsite equivalence.
  simpa using
    (GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall
      (J := L) (A := Type w) :
        L.WEqualsLocallyBijective (Type w))

/-- Helper for Lemma 7.42.4: the abstract type-valued sheafification unit is locally injective
when the topology's `W`-morphisms are exactly the locally bijective morphisms. -/
private theorem toSheafify_isLocallyInjective_type_of_WEquals
    {E : Type u₃} [Category.{v₃} E] (L : GrothendieckTopology E)
    [HasWeakSheafify L (Type w)] [L.WEqualsLocallyBijective (Type w)]
    (P : Eᵒᵖ ⥤ Type w) :
    Presheaf.IsLocallyInjective L (toSheafify L P) := by
  exact toSheafify_isLocallyInjective_type_of_WEqualsLocallyBijective (L := L) P

/-- Helper for Lemma 7.42.4: for `Type w`-valued presheaves, the sheafification unit is
locally injective under the formal `W =` local-bijectivity package. -/
private lemma toSheafify_isLocallyInjective_type
    {E : Type u₃} [Category.{v₃} E] (L : GrothendieckTopology E)
    [HasWeakSheafify L (Type w)] [L.WEqualsLocallyBijective (Type w)]
    (P : Eᵒᵖ ⥤ Type w) :
    Presheaf.IsLocallyInjective L (toSheafify L P) := by
  exact toSheafify_isLocallyInjective_type_of_WEquals (L := L) P

/-- Helper for Lemma 7.42.4: for `Type w`-valued presheaves, the concrete `plus-plus`
sheafification model already gives local surjectivity of the sheafification unit. -/
private lemma toSheafify_isLocallySurjective_type
    {E : Type u₃} [Category.{v₃} E] (L : GrothendieckTopology E)
    [HasWeakSheafify L (Type w)] (P : Eᵒᵖ ⥤ Type w) :
    Presheaf.IsLocallySurjective L (toSheafify L P) := by
  -- Use the reflector/range argument, which does not enter the unresolved `ULift` branch.
  exact toSheafify_isLocallySurjective_type_of_hasWeakSheafify (L := L) P

omit [HasWeakSheafify K (Type w)] [K.WEqualsLocallyBijective (Type w)] in
/-- Helper for Lemma 7.42.4: the singleton-on-empty hypothesis survives one application of
the `plus` construction. -/
private lemma plus_preserves_singleton_on_sheaf_theoretically_empty
    (G : Dᵒᵖ ⥤ Type w)
    [∀ X : D, Limits.HasColimitsOfShape (K.Cover X)ᵒᵖ (Type w)]
    [∀ P' : Dᵒᵖ ⥤ Type w, ∀ X : D, ∀ S : K.Cover X,
      Limits.HasMultiequalizer (S.index P')]
    (hG : ∀ V : D, K.IsSheafTheoreticallyEmpty V → Nonempty (Unique (G.obj (op V)))) :
    ∀ V : D, K.IsSheafTheoreticallyEmpty V →
      Nonempty (Unique ((K.plusObj G).obj (op V))) := by
  intro V hV
  obtain ⟨hUniqueG⟩ := hG V hV
  rw [GrothendieckTopology.isSheafTheoreticallyEmpty_iff_bot_mem] at hV
  refine ⟨{
    default := (K.toPlus G).app (op V) hUniqueG.default
    uniq := ?_
  }⟩
  intro s
  let S : K.Cover V := ⟨⊥, hV⟩
  -- The empty cover gives a vacuous separatedness witness, so every `Plus` section is equal to
  -- the one induced from the unique original section.
  exact
    GrothendieckTopology.Plus.sep (J := K) G S _ _
      (fun I ↦ False.elim (by simpa using I.hf))

omit [K.WEqualsLocallyBijective (Type w)] in
/-- Helper for Lemma 7.42.4: on a sheaf-theoretically empty object, every section of the
sheafification of `G` has a preimage in `G`. -/
private lemma empty_branch_has_preimage
    (G : Dᵒᵖ ⥤ Type w)
    (hG : ∀ V : D, K.IsSheafTheoreticallyEmpty V → Nonempty (Unique (G.obj (op V))))
    (V : D) (hV : K.IsSheafTheoreticallyEmpty V) (s : (sheafify K G).obj (op V)) :
    ∃ t : G.obj (op V), (toSheafify K G).app (op V) t = s := by
  -- Rewrite emptiness as the covering condition for the bottom sieve so the sheaf target applies.
  obtain ⟨hUniqueG⟩ := hG V hV
  rw [GrothendieckTopology.isSheafTheoreticallyEmpty_iff_bot_mem] at hV
  have hUniqueSh : Unique ((sheafify K G).obj (op V)) :=
    CategoryTheory.Limits.Types.isTerminalEquivUnique _
      (((presheafToSheaf K (Type w)).obj G).isTerminalOfBotCover V hV)
  refine ⟨hUniqueG.default, ?_⟩
  -- Compare both sections with the unique section of the sheafification.
  calc
    (toSheafify K G).app (op V) hUniqueG.default = hUniqueSh.default := hUniqueSh.uniq _
    _ = s := (hUniqueSh.uniq s).symm

/-
The next helper only uses the almost-cocontinuity lifting statement on `u`; the weak sheafify
data on `J` and continuity of `u` are not needed in its proof.
-/
omit [HasWeakSheafify J (Type w)] [u.IsContinuous J K] in
/-- Helper for Lemma 7.42.4: the whiskered sheafification unit is locally injective along an
almost cocontinuous functor once the empty-image branch is singleton-valued. -/
private lemma whisker_toSheafify_isLocallyInjective
    (G : Dᵒᵖ ⥤ Type w)
    (hG : ∀ V : D, K.IsSheafTheoreticallyEmpty V → Nonempty (Unique (G.obj (op V)))) :
    Presheaf.IsLocallyInjective J (Functor.whiskerLeft u.op (toSheafify K G)) where
  equalizerSieve_mem {X} x y h := by
    letI instWhiskerBaseInjective : Presheaf.IsLocallyInjective K (toSheafify K G) :=
      toSheafify_isLocallyInjective_type (L := K) G
    let T : K.Cover (u.obj X.unop) :=
      ⟨Presheaf.equalizerSieve (F := G) x y,
        Presheaf.equalizerSieve_mem K (toSheafify K G) x y h⟩
    obtain ⟨S, hS⟩ := Functor.cover_lift_factors u J K T
    -- Lift the equalizer cover and split into the empty-image branch or the factorization branch.
    refine J.superset_covering ?_ S.condition
    intro Y f hf
    let I : S.Arrow := ⟨Y, f, hf⟩
    rcases hS I with hEmpty | ⟨j, g, hg⟩
    · obtain ⟨hUnique⟩ := hG (u.obj Y) hEmpty
      -- On the empty branch, every section over `u.obj Y` is equal.
      exact
        (hUnique.uniq (G.map (u.map f).op x)).trans
          (hUnique.uniq (G.map (u.map f).op y)).symm
    · -- On the factorization branch, pull the equalizer relation back along the factorization.
      have hj : G.map j.f.op x = G.map j.f.op y := by
        simpa [T] using j.hf
      calc
        G.map (u.map f).op x = G.map g.op (G.map j.f.op x) := by
          rw [← hg]
          simp [op_comp]
        _ = G.map g.op (G.map j.f.op y) := by rw [hj]
        _ = G.map (u.map f).op y := by
          rw [← hg]
          simp [op_comp]

omit [HasWeakSheafify J (Type w)] [K.WEqualsLocallyBijective (Type w)] [u.IsContinuous J K] in
/-- Helper for Lemma 7.42.4: the whiskered sheafification unit is locally surjective along an
almost cocontinuous functor once empty-image branches have preimages. -/
private lemma whisker_toSheafify_isLocallySurjective
    (G : Dᵒᵖ ⥤ Type w)
    (hG : ∀ V : D, K.IsSheafTheoreticallyEmpty V → Nonempty (Unique (G.obj (op V)))) :
    Presheaf.IsLocallySurjective J (Functor.whiskerLeft u.op (toSheafify K G)) where
  imageSieve_mem {U} s := by
    letI instWhiskerBaseSurjective : Presheaf.IsLocallySurjective K (toSheafify K G) :=
      toSheafify_isLocallySurjective_type (L := K) G
    let T : K.Cover (u.obj U) :=
      ⟨Presheaf.imageSieve (toSheafify K G) s,
        Presheaf.imageSieve_mem K (toSheafify K G) s⟩
    obtain ⟨S, hS⟩ := Functor.cover_lift_factors u J K T
    -- Lift the image cover and again split into the empty-image branch or a genuine refinement.
    refine J.superset_covering ?_ S.condition
    intro Y f hf
    let I : S.Arrow := ⟨Y, f, hf⟩
    rcases hS I with hEmpty | ⟨j, g, hg⟩
    · -- On the empty branch, the pulled-back target section has a preimage by uniqueness.
      simpa using
        empty_branch_has_preimage (K := K) G hG (u.obj Y) hEmpty
          ((sheafify K G).map (u.map f).op s)
    · rcases (show Presheaf.imageSieve (toSheafify K G) s j.f from by simpa [T] using j.hf) with
        ⟨t, ht⟩
      refine ⟨G.map g.op t, ?_⟩
      -- On the factorization branch, pull back a chosen local preimage along the factorization.
      calc
        (toSheafify K G).app (op (u.obj Y)) (G.map g.op t) =
            (sheafify K G).map g.op ((toSheafify K G).app (op j.Y) t) := by
              exact FunctorToTypes.naturality _ _ (toSheafify K G) g.op t
        _ = (sheafify K G).map g.op ((sheafify K G).map j.f.op s) := by
          simpa using congrArg ((sheafify K G).map g.op) ht
        _ = (sheafify K G).map (u.map f).op s := by
          rw [← hg]
          simp [op_comp]

/-- Helper for Lemma 7.42.4: a locally bijective map into a sheaf induces an isomorphism after
`J`-sheafification once the source sheafification unit is locally surjective. -/
private theorem sheafifyLift_isIso_of_locallyBijective
    {E : Type u₃} [Category.{v₃} E] (L : GrothendieckTopology E)
    [HasWeakSheafify L (Type w)]
    {P Q : Eᵒᵖ ⥤ Type w} (η : P ⟶ Q) (hQ : Presheaf.IsSheaf L Q)
    [Presheaf.IsLocallySurjective L (toSheafify L P)]
    [Presheaf.IsLocallyInjective L η] [Presheaf.IsLocallySurjective L η] :
    IsIso (sheafifyLift L η hQ) := by
  let α : P ⟶ sheafify L P := toSheafify L P
  let β : sheafify L P ⟶ Q := sheafifyLift L η hQ
  have hfac : α ≫ β = η := by
    -- The defining equation of `sheafifyLift` identifies the composite with `η`.
    simpa [α, β] using (toSheafify_sheafifyLift (J := L) η hQ)
  letI instBetaInjective : Presheaf.IsLocallyInjective L β := by
    -- Local injectivity of `β` follows from that of `η`, using local surjectivity of `α`.
    exact Presheaf.isLocallyInjective_of_isLocallyInjective_of_isLocallySurjective_fac
      L η hfac
  letI instBetaSurjective : Presheaf.IsLocallySurjective L β := by
    -- Local surjectivity cancels the locally surjective source unit from the same factorization.
    exact (Presheaf.comp_isLocallySurjective_iff L α β).1 (by simpa [hfac])
  let Fsheaf : Sheaf L (Type w) :=
    ⟨sheafify L P, ((presheafToSheaf L (Type w)).obj P).property⟩
  let Gsheaf : Sheaf L (Type w) := ⟨Q, hQ⟩
  let βsheaf : Fsheaf ⟶ Gsheaf := ⟨β⟩
  have hIsoSheaf : IsIso βsheaf := by
    -- A locally bijective morphism of sheaves of types is an isomorphism.
    exact (Sheaf.isLocallyBijective_iff_isIso (J := L) (A := Type w) βsheaf).1
      ⟨inferInstance, inferInstance⟩
  letI instIsoSheaf : IsIso βsheaf := hIsoSheaf
  -- Forgetting from sheaves to presheaves preserves the isomorphism just constructed.
  change IsIso ((sheafToPresheaf L (Type w)).map βsheaf)
  infer_instance

/-- Lemma 7.42.4: if `u : (C, J) ⥤ (D, K)` is continuous and almost cocontinuous, and if the
presheaf `G` is singleton-valued on every sheaf-theoretically empty object of `(D, K)`, then the
canonical comparison morphism `(uᵖ G)^# ⟶ uᵖ (G^#)` is an isomorphism. -/
theorem pushforwardContinuousSheafificationComparison_isIso_of_isAlmostCocontinuous
    (G : Dᵒᵖ ⥤ Type w)
    (hG : ∀ V : D, K.IsSheafTheoreticallyEmpty V → Nonempty (Unique (G.obj (op V)))) :
    IsIso
      (sheafifyLift J (whiskerLeft u.op <| toSheafify K G)
        ((presheafToSheaf K (Type w) ⋙ u.sheafPushforwardContinuous (Type w) J K).obj G).property) := by
  letI instToSheafifySurjective : ∀ P : Cᵒᵖ ⥤ Type w, Presheaf.IsLocallySurjective J (toSheafify J P) :=
    fun P ↦ toSheafify_isLocallySurjective_type (L := J) P
  let η : u.op ⋙ G ⟶ u.op ⋙ sheafify K G := Functor.whiskerLeft u.op (toSheafify K G)
  let hQ :
      Presheaf.IsSheaf J (u.op ⋙ sheafify K G) :=
    ((presheafToSheaf K (Type w) ⋙ u.sheafPushforwardContinuous (Type w) J K).obj G).property
  letI instEtaInjective : Presheaf.IsLocallyInjective J η :=
    whisker_toSheafify_isLocallyInjective
      (u := u) (J := J) (K := K) G hG
  letI instEtaSurjective : Presheaf.IsLocallySurjective J η :=
    whisker_toSheafify_isLocallySurjective
      (u := u) (J := J) (K := K) G hG
  -- Route correction: the main theorem now uses the sheaf-level local-bijectivity criterion
  -- directly, avoiding a global `J.WEqualsLocallyBijective (Type w)` package.
  simpa [η, hQ] using
    (sheafifyLift_isIso_of_locallyBijective (L := J) (η := η) hQ :
      IsIso (sheafifyLift J η hQ))

section CocontinuousBridge

variable [u.IsCocontinuous J K]
variable [∀ F : Cᵒᵖ ⥤ Type w, u.op.HasPointwiseRightKanExtension F]

/- Companion bridge: under the stronger cocontinuity hypothesis, the source comparison morphism is
exactly the `hom` of the `G`-component of the canonical mathlib compatibility isomorphism
`u.pushforwardContinuousSheafificationCompatibility (Type w) J K`. -/
recall pushforwardContinuousSheafificationCompatibility_hom_app_hom

omit [K.WEqualsLocallyBijective (Type w)] [u.IsAlmostCocontinuous J K] in
/-
The cocontinuous bridge does not use the almost-cocontinuity hypothesis or the target-site
`W =` package from the surrounding section.
-/
/-- Helper for Lemma 7.42.4: under the stronger cocontinuous and right-Kan-extension hypotheses,
the source comparison map is an isomorphism because it is the underlying morphism of mathlib's
compatibility isomorphism. -/
private theorem pushforwardContinuousSheafificationComparison_isIso_of_isCocontinuous
    (G : Dᵒᵖ ⥤ Type w) :
    IsIso
      (sheafifyLift J (whiskerLeft u.op <| toSheafify K G)
        ((presheafToSheaf K (Type w) ⋙ u.sheafPushforwardContinuous (Type w) J K).obj G).property) := by
  let e :
      ((whiskeringLeft Cᵒᵖ Dᵒᵖ (Type w)).obj u.op ⋙ presheafToSheaf J (Type w)).obj G ≅
        (presheafToSheaf K (Type w) ⋙ u.sheafPushforwardContinuous (Type w) J K).obj G :=
    asIso ((u.pushforwardContinuousSheafificationCompatibility (Type w) J K).hom.app G)
  have hcomp :
      sheafifyLift J (whiskerLeft u.op <| toSheafify K G)
          ((presheafToSheaf K (Type w) ⋙ u.sheafPushforwardContinuous (Type w) J K).obj G).property =
        e.hom.hom := by
    -- Rewrite the source-facing comparison morphism as the underlying morphism of `e.hom`.
    exact (u.pushforwardContinuousSheafificationCompatibility_hom_app_hom (Type w) J K G).symm
  -- Use the inverse of the sheaf-level isomorphism to build an inverse on underlying presheaves.
  refine ⟨⟨e.inv.hom, ?_, ?_⟩⟩
  · rw [hcomp]
    exact ObjectProperty.isoHom_inv_id_hom e
  · rw [hcomp]
    exact ObjectProperty.isoInv_hom_id_hom e
end CocontinuousBridge

end

end CategoryTheory.Functor
