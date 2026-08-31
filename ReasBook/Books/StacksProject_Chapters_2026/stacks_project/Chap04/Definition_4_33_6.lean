module

public import Mathlib.CategoryTheory.FiberedCategory.Cartesian
public import Mathlib.CategoryTheory.FiberedCategory.Fiber
public import Mathlib.CategoryTheory.FiberedCategory.Fibered

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

universe v₁ v₂ u₁ u₂

namespace CategoryTheory

open Category Functor Fiber

variable {C : Type u₁} [Category.{v₁} C]
variable {S : Type u₂} [Category.{v₂} S]

/- Domain-style sampling for Definition 4.33.6:
- primary domain: fibered categories and chosen strongly cartesian pullbacks in standard fibers.
- inspected owner-level declarations:
  `Functor.IsStronglyCartesian.map`,
  `Functor.IsStronglyCartesian.map_self`,
  `Functor.IsStronglyCartesian.map_comp_map`,
  `Functor.IsStronglyCartesian.ext`,
  `Functor.IsFibered`,
  `Functor.IsFibered.isStronglyCartesian_of_isCartesian`.
- best owner abstraction for the derived standard-fiber action: `Functor.IsStronglyCartesian`.
- primitive data: the source-facing explicit pullback-choice package `PullbackChoice p`.
- derived API: `PullbackChoice.isFibered` and the induced pullback functors on standard fibers,
  with the action on morphisms read directly from the strong-cartesian universal property.

Source/core/bridge triage:
- `source-facing`: `PullbackChoice p`, matching the textbook's explicit chosen pullbacks.
- `core/canonical`: `Functor.IsFibered`.
- `bridge/view`: the constructions deriving fibredness and pullback functors from a given
  `PullbackChoice`.

This file keeps the explicit choice data as the source-facing parameter and does not expose a
public global witness built from mathlib's noncanonical `pullbackObj`/`pullbackMap` choices. -/

/-- Definition 4.33.6: a choice of pullbacks for `p : S ⥤ C` consists of, for
every morphism `f : V ⟶ U` and every object `x` of the standard fiber over `U`, a chosen strongly
cartesian morphism `f^*x ⟶ x` lying over `f`. -/
structure PullbackChoice (p : S ⥤ C) where
  /-- The chosen pullback object `f^*x` in the fiber over the domain of `f`. -/
  obj {U V : C} (f : V ⟶ U) (x : Fiber p U) : Fiber p V
  /-- The chosen strongly cartesian morphism `f^*x ⟶ x` lying over `f`. -/
  map {U V : C} (f : V ⟶ U) (x : Fiber p U) : (obj f x).1 ⟶ x.1
  /-- The chosen comparison morphism is strongly cartesian over `f`. -/
  isStronglyCartesian {U V : C} (f : V ⟶ U) (x : Fiber p U) :
    p.IsStronglyCartesian f (map f x)

attribute [instance] PullbackChoice.isStronglyCartesian

end CategoryTheory

/- The chosen pullback object of `x` along `f` for the pullback choice `hc`. -/
notation:90 f:90 " ^*[" hc "] " x:91 => CategoryTheory.PullbackChoice.obj hc f x

namespace CategoryTheory

open Category Functor Fiber

variable {C : Type u₁} [Category.{v₁} C]
variable {S : Type u₂} [Category.{v₂} S]

namespace PullbackChoice

variable {p : S ⥤ C}

/-- A pullback choice already exhibits `p` as a fibred category. -/
theorem isFibered (hc : PullbackChoice p) : p.IsFibered :=
  IsFibered.of_exists_isStronglyCartesian fun x _ f ↦
    let x' : Fiber p (p.obj x) := .mk rfl
    ⟨(f ^*[hc] x').1, hc.map f x', hc.isStronglyCartesian f x'⟩

/-- A chosen pullback system induces the canonical fibred-category structure on `p`. -/
instance (hc : PullbackChoice p) : p.IsFibered :=
  hc.isFibered

variable (hc : PullbackChoice p)

/-- The map on morphisms induced by a chosen pullback system on a fibred category. -/
noncomputable def pullbackMap
    {U V : C} (f : V ⟶ U) {x y : Fiber p U} (φ : x ⟶ y) :
    f ^*[hc] x ⟶ f ^*[hc] y :=
  let ψ : (f ^*[hc] x).1 ⟶ y.1 := hc.map f x ≫ φ.1
  letI : p.IsHomLift (𝟙 U) φ.1 := φ.2
  letI : p.IsHomLift f ψ := IsHomLift.comp_lift_id_right' p f (hc.map f x) U φ.1
  ⟨IsStronglyCartesian.map p f (hc.map f y) (id_comp f).symm ψ, inferInstance⟩

@[reassoc]
private theorem pullbackMap_fac
    {U V : C} (f : V ⟶ U) {x y : Fiber p U} (φ : x ⟶ y) :
    (hc.pullbackMap f φ).1 ≫ hc.map f y = hc.map f x ≫ φ.1 := by
  -- Unfold the chosen lift and read off its defining factorization through `hc.map f y`.
  simp [pullbackMap]

/-- The chosen pullback construction sends identity morphisms in a fiber to identity morphisms. -/
theorem pullbackMap_id
    {U V : C} (f : V ⟶ U) (x : Fiber p U) :
    hc.pullbackMap f (𝟙 x) = 𝟙 (f ^*[hc] x) := by
  let η : f ^*[hc] x ⟶ f ^*[hc] x := 𝟙 (f ^*[hc] x)
  -- It is enough to compare the underlying arrows in the ambient category.
  apply Fiber.hom_ext
  change (hc.pullbackMap f (𝟙 x)).1 = η.1
  -- Both candidates are lifts over `𝟙 V` into the same strongly cartesian arrow `hc.map f x`.
  letI : p.IsHomLift (𝟙 V) (hc.pullbackMap f (𝟙 x)).1 := (hc.pullbackMap f (𝟙 x)).2
  letI : p.IsHomLift (𝟙 V) η.1 := η.2
  apply IsStronglyCartesian.ext p f (hc.map f x) (𝟙 V)
  -- After postcomposition with `hc.map f x`, both arrows become `hc.map f x`.
  calc
    (hc.pullbackMap f (𝟙 x)).1 ≫ hc.map f x
        = hc.map f x ≫ (𝟙 x : x ⟶ x).1 := by
            rw [pullbackMap_fac]
    _ = hc.map f x := by
          change hc.map f x ≫ 𝟙 x.1 = hc.map f x
          simp
    _ = η.1 ≫ hc.map f x := by
          change hc.map f x = 𝟙 (f ^*[hc] x).1 ≫ hc.map f x
          simp

/-- The chosen pullback construction respects composition in each fiber. -/
theorem pullbackMap_comp
    {U V : C} (f : V ⟶ U) {x y z : Fiber p U} (φ : x ⟶ y) (ψ : y ⟶ z) :
    hc.pullbackMap f (φ ≫ ψ) =
      hc.pullbackMap f φ ≫ hc.pullbackMap f ψ := by
  -- It is enough to compare the underlying lifts in the ambient category.
  apply Fiber.hom_ext
  -- Reduce from equality in the fiber to equality of the ambient arrows.
  change (hc.pullbackMap f (φ ≫ ψ)).1 = (hc.pullbackMap f φ ≫ hc.pullbackMap f ψ).1
  -- The uniqueness lemma needs the projected fiber morphisms as explicit ambient lifts.
  letI : p.IsHomLift (𝟙 V) (hc.pullbackMap f (φ ≫ ψ)).1 := (hc.pullbackMap f (φ ≫ ψ)).2
  letI : p.IsHomLift (𝟙 V) (hc.pullbackMap f φ ≫ hc.pullbackMap f ψ).1 :=
    (hc.pullbackMap f φ ≫ hc.pullbackMap f ψ).2
  -- Both arrows are lifts over `𝟙 V` into the same strongly cartesian morphism `hc.map f z`.
  apply IsStronglyCartesian.ext p f (hc.map f z) (𝟙 V)
  -- After postcomposition with `hc.map f z`, both sides become the same composite.
  calc
    (hc.pullbackMap f (φ ≫ ψ)).1 ≫ hc.map f z
        = hc.map f x ≫ (φ ≫ ψ).1 := by
            rw [pullbackMap_fac]
    _ = (hc.map f x ≫ φ.1) ≫ ψ.1 := by
          change hc.map f x ≫ (φ.1 ≫ ψ.1) = (hc.map f x ≫ φ.1) ≫ ψ.1
          simp [Category.assoc]
    _ = ((hc.pullbackMap f φ).1 ≫ hc.map f y) ≫ ψ.1 := by
          rw [pullbackMap_fac]
    _ = (hc.pullbackMap f φ).1 ≫ (hc.map f y ≫ ψ.1) := by
          simp [Category.assoc]
    _ = (hc.pullbackMap f φ).1 ≫ ((hc.pullbackMap f ψ).1 ≫ hc.map f z) := by
          rw [← pullbackMap_fac]
    _ = (hc.pullbackMap f φ ≫ hc.pullbackMap f ψ).1 ≫ hc.map f z := by
          change
            (hc.pullbackMap f φ).1 ≫ ((hc.pullbackMap f ψ).1 ≫ hc.map f z) =
              ((hc.pullbackMap f φ).1 ≫ (hc.pullbackMap f ψ).1) ≫ hc.map f z
          simp [Category.assoc]

/-- The pullback functor on standard fibers associated to a chosen pullback system. -/
noncomputable def pullbackFunctor
    {U V : C} (f : V ⟶ U) :
    Fiber p U ⥤ Fiber p V where
  obj := fun x ↦ f ^*[hc] x
  map := hc.pullbackMap f
  map_id := hc.pullbackMap_id f
  map_comp := hc.pullbackMap_comp f

end PullbackChoice

end CategoryTheory
