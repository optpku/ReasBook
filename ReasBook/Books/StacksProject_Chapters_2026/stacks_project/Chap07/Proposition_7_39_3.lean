module

public import Mathlib.CategoryTheory.EssentiallySmall
public import Mathlib.Topology.Sheaves.SheafCondition.Sites
public import Mathlib.Topology.Sheaves.PUnit
public import Mathlib.CategoryTheory.Sites.Sheafification
public import Mathlib.CategoryTheory.Sites.Sheaf
public import stacks_project.Chap07.«7_32_1_1»
public import stacks_project.Chap07.Definition_7_38_1
public import stacks_project.Chap07.Lemma_7_38_3.SeparatingSections
public import stacks_project.Chap07.Lemma_7_17_2
public import stacks_project.Chap07.Lemma_7_39_2
public import stacks_project.Chap07.Proposition_7_33_3

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

universe u v w

namespace CategoryTheory

open Opposite
open CategoryTheory.Limits
open GrothendieckTopology
open GrothendieckTopology.Point.ofIsCofiltered

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}

attribute [local instance] initiallySmall_of_essentiallySmall

/-- Helper for Proposition 7.39.3: equality of two inverse-system presheaf-fiber generators over
the same object is witnessed after moving to a common later element of the fiber functor. -/
lemma proposition_7_39_3_inverseSystem_toPresheafFiber_eq_iff
    {ι : Type _} [Preorder ι] [IsDirected ι (· ≤ ·)] [Nonempty ι]
    [InitiallySmall ιᵒᵖ] (S : ιᵒᵖ ⥤ C) {F : Cᵒᵖ ⥤ Type (max u v)}
    (X : C) (x : (fiber.{max u v} S).obj X) (z₁ z₂ : F.obj (op X)) :
    (fiber.{max u v} S).toPresheafFiber X x F z₁ =
        (fiber.{max u v} S).toPresheafFiber X x F z₂ ↔
      ∃ (Y : C) (f : Y ⟶ X) (y : (fiber.{max u v} S).obj Y),
        (fiber.{max u v} S).map f y = x ∧ F.map f.op z₁ = F.map f.op z₂ := by
  constructor
  · intro h
    -- Read equality in the filtered colimit defining the presheaf fiber.
    obtain ⟨j, f, hf⟩ :=
      (Types.FilteredColimit.isColimit_eq_iff'
        (ht := colimit.isColimit ((CategoryOfElements.π (fiber.{max u v} S)).op ⋙ F))
        (i := op ⟨X, x⟩) z₁ z₂).1 h
    exact ⟨j.unop.1, f.unop.val, j.unop.2, f.unop.property, hf⟩
  · rintro ⟨Y, f, y, hy, hEq⟩
    -- Conversely, any such common refinement identifies the two colimit representatives.
    exact
      (Types.FilteredColimit.isColimit_eq_iff'
        (ht := colimit.isColimit ((CategoryOfElements.π (fiber.{max u v} S)).op ⋙ F))
        (i := op ⟨X, x⟩) z₁ z₂).2
        ⟨op ⟨Y, y⟩, op (CategoryOfElements.homMk ⟨Y, y⟩ ⟨X, x⟩ f hy), hEq⟩

/- Domain-style sampling for Proposition 7.39.3:
- primary domain: enough points on a Grothendieck site, built from point fibers of cofiltered
  inverse systems and the canonical conservative-family criterion;
- sampled owner API:
  `GrothendieckTopology.HasEnoughPoints`,
  `GrothendieckTopology.hasEnoughPoints_iff_exists_conservativePointFamily`,
  `GrothendieckTopology.isConservativePointFamily_iff_exists_point_separating_sections`,
  `GrothendieckTopology.Point.ofIsCofiltered.fiber`,
  `HasFiniteRefinementProperty`;
- source/core/bridge triage:
  `source-facing`: the site-level theorem that the finite-refinement hypothesis implies enough
    points;
  `core/canonical`: `J.HasEnoughPoints` and the owner notion `GrothendieckTopology.Point`;
  `bridge/view`: the separation criterion for conservative families of points and the
    inverse-system fiber construction used to manufacture the required points.

Primitive data are only the finite-limit hypothesis on `C` and the source-facing finite-refinement
assumption `∀ X, J.HasFiniteRefinementProperty X`. Conservative-family packaging and the passage
from a cofiltered inverse system to a point are derived API from the owner layer above, so this
file should stay a thin theorem at the `HasEnoughPoints` owner rather than introducing any local
wrapper around conservative point families or point data.
-/
/-- Helper for Proposition 7.39.3: the raw presheaf fiber map attached to the trivial one-object
inverse system is injective, so distinct sections remain distinct before applying
Lemma 7.39.2. -/
lemma trivial_inverse_system_toPresheafFiber_injective
    {ℱ : Sheaf J (Type (max u v))} (U : C) :
    let I₀ := ULift.{max u v} PUnit
    let S₀ : I₀ᵒᵖ ⥤ C := (Functor.const I₀ᵒᵖ).obj U
    let x₀ : (fiber.{max u v} S₀).obj U :=
      fiberMk (show S₀.obj (op (ULift.up PUnit.unit)) ⟶ U from 𝟙 U)
    Function.Injective ((fiber.{max u v} S₀).toPresheafFiber U x₀ ℱ.obj) := by
  let I₀ := ULift.{max u v} PUnit
  let S₀ : I₀ᵒᵖ ⥤ C := (Functor.const I₀ᵒᵖ).obj U
  let x₀ : (fiber.{max u v} S₀).obj U :=
    fiberMk (show S₀.obj (op (ULift.up PUnit.unit)) ⟶ U from 𝟙 U)
  change Function.Injective ((fiber.{max u v} S₀).toPresheafFiber U x₀ ℱ.obj)
  intro s s' hss
  let u₀ : C ⥤ Type (max u v) := fiber.{max u v} S₀
  have hpullback :
      ∃ (Y : C) (f : Y ⟶ U) (y : u₀.obj Y), u₀.map f y = x₀ ∧
        ℱ.obj.map f.op s = ℱ.obj.map f.op s' := by
    -- Compare the two germs by the canonical point-fiber equality criterion.
    simpa [u₀] using
      (proposition_7_39_3_inverseSystem_toPresheafFiber_eq_iff S₀ U x₀ s s').1 hss
  obtain ⟨Y, f, y, hy, hpullback⟩ := hpullback
  -- Represent the witness `y` by an actual stage map in the one-object inverse system.
  obtain ⟨V, g, rfl⟩ := fiberMk_jointly_surjective y
  have hfiberMk :
      fiberMk.{max u v} (g ≫ f) =
        fiberMk.{max u v} (show S₀.obj (op (ULift.up PUnit.unit)) ⟶ U from 𝟙 U) := by
    simpa [x₀, u₀] using hy
  -- Since the indexing category has one object, that pullback arrow has a section.
  obtain ⟨W, q, hq⟩ := exists_of_fiberMk_eq_fiberMk (p := S₀) hfiberMk
  have hsection : g ≫ f = 𝟙 U := by
    simpa [S₀] using hq
  -- Apply the section to the pullback equality to recover equality of the original sections.
  have hmap :
      ℱ.obj.map (g ≫ f).op s = ℱ.obj.map (g ≫ f).op s' := by
    simpa using congrArg (ℱ.obj.map g.op) hpullback
  have hmap_id : ℱ.obj.map (𝟙 U).op s = ℱ.obj.map (𝟙 U).op s' := by
    rw [← hsection]
    exact hmap
  simpa using hmap_id

/-- Helper for Proposition 7.39.3: once every finite covering family lifts elements of the fiber
functor, the finite-refinement hypothesis upgrades that to the covering-sieve lifting condition
needed in Proposition 7.33.3. -/
lemma coversLiftToFunctorFibers_of_finite_family_lifting
    (hfinite : ∀ X : C, J.HasFiniteRefinementProperty X)
    {ι : Type _} [Preorder ι] [IsDirected ι (· ≤ ·)] [InitiallySmall ιᵒᵖ] (T : ιᵒᵖ ⥤ C)
    (hlift :
      ∀ {W : C} (𝒰 : SemiRepresentableFamily.Over.{max u v} W) [Finite 𝒰.index],
        𝒰.toSieve ∈ J W →
          ∀ f : (fiber.{max u v} T).obj W,
            ∃ i : 𝒰.index, ∃ y : (fiber.{max u v} T).obj (𝒰.obj i).left,
              (fiber.{max u v} T).map (𝒰.obj i).hom y = f) :
    CoversLiftToFunctorFibers J (fiber.{max u v} T) := by
  intro W R hR f
  -- Refine the arbitrary covering sieve by a finite covering family.
  obtain ⟨𝒱, h𝒱fin, h𝒱, hle⟩ :=
    (hfinite W).finite_refinement (R : Presieve W) (by simpa using hR)
  have hle' : 𝒱.toSieve ≤ R := by
    simpa using hle
  let _ : Finite 𝒱.index := h𝒱fin
  -- The assumed finite-family lifting produces a lift through one member of that refinement.
  obtain ⟨i, y, hy⟩ := hlift (W := W) 𝒱 h𝒱 f
  refine ⟨(𝒱.obj i).left, (𝒱.obj i).hom, ?_, y, hy⟩
  have hi : 𝒱.toSieve (𝒱.obj i).hom := by
    exact (Sieve.le_generate 𝒱.toPresieve) _ _ (Presieve.ofArrows.mk i)
  exact hle' _ hi

/-- Helper for Proposition 7.39.3: the covering-lift predicate supplies the joint-surjectivity
field required to make an inverse-system fiber into a point. -/
lemma inverseSystemFiber_jointlySurjective_of_coversLiftToFunctorFibers
    {ι : Type _} [Preorder ι] [IsDirected ι (· ≤ ·)] [InitiallySmall ιᵒᵖ] (T : ιᵒᵖ ⥤ C)
    (hcover : CoversLiftToFunctorFibers J (fiber.{max u v} T))
    {X : C} (R : Sieve X) (hR : R ∈ J X) (x : (fiber.{max u v} T).obj X) :
    ∃ (Y : C) (f : Y ⟶ X) (_ : R f) (y : (fiber.{max u v} T).obj Y),
      (fiber.{max u v} T).map f y = x := by
  -- Unpack the covering-lift witness and repack it in the field shape used by `Point`.
  obtain ⟨Y, f, hf, y, hy⟩ := hcover R hR x
  exact ⟨Y, f, hf, y, hy⟩

/-- Helper for Proposition 7.39.3: every unequal pair of sections of a set-valued sheaf is
separated by the germs at some point obtained from the refinement construction of Lemma 7.39.2. -/
lemma exists_point_separating_sections_of_finite_cover_refinement
    [Limits.HasFiniteLimits C]
    (hfinite : ∀ X : C, J.HasFiniteRefinementProperty X)
  {ℱ : Sheaf J (Type (max u v))} (U : C) (s s' : ℱ.obj.obj (op U))
    (hs : s ≠ s') :
    ∃ p : GrothendieckTopology.Point.{max u v} J, ∃ x : p.fiber.obj U,
      p.toPresheafFiber U x ℱ.obj s ≠ p.toPresheafFiber U x ℱ.obj s' := by
  let I₀ := ULift.{max u v} PUnit
  letI : IsDirected I₀ (· ≤ ·) := ⟨fun _ _ ↦ ⟨ULift.up PUnit.unit, trivial, trivial⟩⟩
  let S₀ : I₀ᵒᵖ ⥤ C := (Functor.const I₀ᵒᵖ).obj U
  let x₀ : (fiber.{max u v} S₀).obj U :=
    fiberMk (show S₀.obj (op (ULift.up PUnit.unit)) ⟶ U from 𝟙 U)
  let a : (sheafToPresheaf J (Type (max u v)) ⋙ (fiber.{max u v} S₀).presheafFiber).obj ℱ :=
    (fiber.{max u v} S₀).toPresheafFiber U x₀ ℱ.obj s
  let a' : (sheafToPresheaf J (Type (max u v)) ⋙ (fiber.{max u v} S₀).presheafFiber).obj ℱ :=
    (fiber.{max u v} S₀).toPresheafFiber U x₀ ℱ.obj s'
  have hraw : a ≠ a' := by
    -- The trivial inverse system records the original sections faithfully.
    intro haa'
    exact hs ((trivial_inverse_system_toPresheafFiber_injective (J := J) (ℱ := ℱ) U) haa')
  -- Route correction: keep the source proof's trivial-system-to-refinement architecture rather
  -- than replacing it with a direct conservative-family argument.
  obtain ⟨ι', _, _, T, j, e, hsep, hlift⟩ :=
    exists_refined_inverse_system_separating_sections_and_lifting_all_final_finite_covers
      (J := J) (S' := S₀) (ℱ := ℱ) (s := a) (s' := a') hraw
  have hcover : CoversLiftToFunctorFibers J (fiber.{max u v} T) := by
    -- Upgrade the finite-cover lifting output of Lemma 7.39.2 to arbitrary coverings.
    exact coversLiftToFunctorFibers_of_finite_family_lifting (J := J) hfinite T hlift
  letI : Nonempty ι' := ⟨j (ULift.up PUnit.unit)⟩
  let p : GrothendieckTopology.Point.{max u v} J :=
    { fiber := fiber.{max u v} T
      jointly_surjective :=
        inverseSystemFiber_jointlySurjective_of_coversLiftToFunctorFibers
          (J := J) T hcover }
  refine ⟨p, (refinementFiber j T e).app U x₀, ?_⟩
  -- The separating raw-fiber inequality is exactly the inequality of germs at the refined point.
  have hleft :
      (refinementFiber j T e).presheafFiber.app ℱ.obj
          ((fiber.{max u v} S₀).toPresheafFiber U x₀ ℱ.obj s) =
        p.toPresheafFiber U ((refinementFiber j T e).app U x₀) ℱ.obj s := by
    simpa [p] using
      congrFun
        (NatTrans.toPresheafFiber_presheafFiber_app (refinementFiber j T e) U x₀
          (F := ℱ.obj)) s
  have hright :
      (refinementFiber j T e).presheafFiber.app ℱ.obj
          ((fiber.{max u v} S₀).toPresheafFiber U x₀ ℱ.obj s') =
        p.toPresheafFiber U ((refinementFiber j T e).app U x₀) ℱ.obj s' := by
    simpa [p] using
      congrFun
        (NatTrans.toPresheafFiber_presheafFiber_app (refinementFiber j T e) U x₀
          (F := ℱ.obj)) s'
  simpa [a, a', hleft, hright] using hsep

/-- Helper for Proposition 7.39.3: once a family of points separates every unequal pair of
sections, Lemma 7.38.3 identifies that family as conservative. -/
lemma section_separating_family_isConservative
    {ι : Type _}
    (p : ι → GrothendieckTopology.Point.{max u v} J)
    (hsep :
      ∀ ⦃ℱ : Sheaf J (Type (max u v))⦄ (U : C) (s s' : ℱ.obj.obj (op U)),
        s ≠ s' →
          ∃ i : ι, ∃ x : (p i).fiber.obj U,
            (p i).toPresheafFiber U x ℱ.obj s ≠
              (p i).toPresheafFiber U x ℱ.obj s') :
    (ObjectProperty.ofObj p).IsConservativeFamilyOfPoints := by
  -- Translate the owner predicate into the indexed stalkwise-isomorphism criterion.
  rw [GrothendieckTopology.isConservativePointFamily_iff]
  intro ℱ 𝒢 φ hφ
  -- The split Lemma 7.38.3 bridge turns separation of sections into joint reflection of
  -- isomorphisms by the corresponding stalk functors.
  exact
    (GrothendieckTopology.stalkFamily_jointlyReflectsIsomorphisms_of_separating_sections_large
      (p := p) hsep).isIso_iff φ |>.2 hφ

/-- Helper for Proposition 7.39.3: enlarge the fiber functor of a small point to an arbitrary
target point universe by applying `ULift` objectwise. -/
def pointTargetUniverseFiber (q : GrothendieckTopology.Point.{max u v} J) :
    C ⥤ Type (max (u + 1) (v + 1)) :=
  { obj := fun X ↦ ULift.{max (u + 1) (v + 1), max u v} (q.fiber.obj X)
    map := fun {X Y} f x ↦ ULift.up (q.fiber.map f x.down) }

/-- Helper for Proposition 7.39.3: removing `ULift` from target-universe fibers preserves the
covering-lift condition for a sieve. -/
lemma pointTargetUniverseCoverLift_iff
    (q : GrothendieckTopology.Point.{max u v} J) {X : C} (S : Sieve X) :
    (∀ x : (pointTargetUniverseFiber (C := C) (J := J) q).obj X,
      ∃ (Y : C) (g : Y ⟶ X) (_ : S g)
        (y : (pointTargetUniverseFiber (C := C) (J := J) q).obj Y),
          (pointTargetUniverseFiber (C := C) (J := J) q).map g y = x) ↔
      ∀ x : q.fiber.obj X,
        ∃ (Y : C) (g : Y ⟶ X) (_ : S g) (y : q.fiber.obj Y),
          q.fiber.map g y = x := by
  constructor
  · intro h x
    -- Lower a target-universe lift witness back to the original point fiber.
    obtain ⟨Y, g, hg, y, hy⟩ :=
      h (show (pointTargetUniverseFiber (C := C) (J := J) q).obj X from ULift.up x)
    refine ⟨Y, g, hg, y.down, ?_⟩
    exact congrArg ULift.down hy
  · intro h x
    -- Lift an original witness objectwise by `ULift`.
    obtain ⟨Y, g, hg, y, hy⟩ := h x.down
    refine ⟨Y, g, hg,
      (show (pointTargetUniverseFiber (C := C) (J := J) q).obj Y from ULift.up y), ?_⟩
    cases x
    exact congrArg
      (show q.fiber.obj X → (pointTargetUniverseFiber (C := C) (J := J) q).obj X from
        ULift.up) hy

/-- Helper for Proposition 7.39.3: the original and target-universe point fibers have equivalent
categories of elements. -/
noncomputable def pointTargetUniverseFiberElementsEquivalence
    (q : GrothendieckTopology.Point.{max u v} J) :
    q.fiber.Elements ≌ (pointTargetUniverseFiber (C := C) (J := J) q).Elements where
  functor :=
    { obj := fun x ↦
        ⟨x.1, (show (pointTargetUniverseFiber (C := C) (J := J) q).obj x.1 from
          ULift.up x.2)⟩
      map := fun {X Y} f ↦
        CategoryOfElements.homMk _ _ f.1 (by
          -- The forward comparison keeps the base arrow and lifts the element equation.
          rcases X with ⟨X, x⟩
          rcases Y with ⟨Y, y⟩
          rcases f with ⟨f, hf⟩
          simpa [pointTargetUniverseFiber] using
            congrArg
              (show q.fiber.obj Y →
                  (pointTargetUniverseFiber (C := C) (J := J) q).obj Y from ULift.up) hf) }
  inverse :=
    { obj := fun x ↦ ⟨x.1, x.2.down⟩
      map := fun {X Y} f ↦
        CategoryOfElements.homMk _ _ f.1 (by
          -- The inverse comparison keeps the base arrow and lowers the element equation.
          rcases X with ⟨X, x⟩
          rcases Y with ⟨Y, y⟩
          rcases f with ⟨f, hf⟩
          simpa [pointTargetUniverseFiber] using congrArg ULift.down hf) }
  unitIso :=
    NatIso.ofComponents
      (fun x ↦
        CategoryOfElements.isoMk _ _ (Iso.refl _) (by
          -- Objectwise, lifting and lowering the original element is the identity.
          simp))
      (fun f ↦ by
        -- Morphisms in element categories are determined by their base arrow.
        apply CategoryOfElements.ext
        simp)
  counitIso :=
    NatIso.ofComponents
      (fun x ↦
        CategoryOfElements.isoMk _ _ (Iso.refl _) (by
          -- The lowered-then-lifted target element is definitionally the same `ULift` value.
          simpa [pointTargetUniverseFiber] using ULift.up_down x.2))
      (fun f ↦ by
        -- The comparison leaves the underlying base arrow unchanged.
        apply CategoryOfElements.ext
        simp)
  functor_unitIso_comp x := by
    -- The triangle identity is reflexive on the base arrow of the element-category morphism.
    apply CategoryOfElements.ext
    simp

/-- Helper for Proposition 7.39.3: the target-universe point fiber remains cofiltered. -/
lemma pointTargetUniverseFiber_isCofiltered
    (q : GrothendieckTopology.Point.{max u v} J) :
    IsCofiltered (pointTargetUniverseFiber (C := C) (J := J) q).Elements := by
  -- Transfer cofilteredness across the explicit element-category equivalence.
  exact IsCofiltered.of_equivalence
    (pointTargetUniverseFiberElementsEquivalence (C := C) (J := J) q)

/-- Helper for Proposition 7.39.3: the target-universe point fiber has an initially small
category of elements. -/
lemma pointTargetUniverseFiber_initiallySmall
    (q : GrothendieckTopology.Point.{max u v} J) :
    InitiallySmall.{max (u + 1) (v + 1)}
      (pointTargetUniverseFiber (C := C) (J := J) q).Elements := by
  -- Use a self small model for the original element category in the target universe, then
  -- transport it along the target-universe fiber equivalence.
  letI : EssentiallySmall.{max (u + 1) (v + 1)} q.fiber.Elements :=
    CategoryTheory.essentiallySmallSelf.{max (u + 1) (v + 1), v, max u v}
      (C := q.fiber.Elements)
  letI : InitiallySmall.{max (u + 1) (v + 1)} q.fiber.Elements :=
    CategoryTheory.initiallySmall_of_essentiallySmall (J := q.fiber.Elements)
  exact initiallySmall_of_initial_of_initiallySmall
    (pointTargetUniverseFiberElementsEquivalence (C := C) (J := J) q).functor

/-- Helper for Proposition 7.39.3: the target-universe point fiber satisfies the point covering
axiom. -/
lemma pointTargetUniverseFiber_jointlySurjective
    (q : GrothendieckTopology.Point.{max u v} J)
    {X : C} (S : Sieve X) (hS : S ∈ J X)
    (x : (pointTargetUniverseFiber (C := C) (J := J) q).obj X) :
    ∃ (Y : C) (g : Y ⟶ X) (_ : S g)
      (y : (pointTargetUniverseFiber (C := C) (J := J) q).obj Y),
        (pointTargetUniverseFiber (C := C) (J := J) q).map g y = x := by
  -- Lift the original point's covering witness to the target universe.
  exact (pointTargetUniverseCoverLift_iff (C := C) (J := J) q S).2
    (q.jointly_surjective S hS) x

/-- Helper for Proposition 7.39.3: enlarge a point to a chosen target universe. -/
noncomputable def pointTargetUniverseLift
    (q : GrothendieckTopology.Point.{max u v} J) :
    GrothendieckTopology.Point.{max (u + 1) (v + 1)} J :=
  { fiber := pointTargetUniverseFiber (C := C) (J := J) q
    isCofiltered := pointTargetUniverseFiber_isCofiltered (C := C) (J := J) q
    initiallySmall := pointTargetUniverseFiber_initiallySmall (C := C) (J := J) q
    jointly_surjective := pointTargetUniverseFiber_jointlySurjective (C := C) (J := J) q }

/-- Helper for Proposition 7.39.3: ordinary lift data for every point in a conservative family
forces the sieve to be covering. -/
lemma sieve_mem_of_family_fiber_lifts
    {ι : Type w} (p : ι → GrothendieckTopology.Point.{max u v} J)
    (hp : (ObjectProperty.ofObj p).IsConservativeFamilyOfPoints)
    {X : C} (S : Sieve X)
    (hS :
      ∀ i (x : (p i).fiber.obj X),
        ∃ (Y : C) (g : Y ⟶ X) (_ : S g) (y : (p i).fiber.obj Y),
          (p i).fiber.map g y = x) :
    S ∈ J X := by
  -- Rewrite an arbitrary sieve as the sieve generated by its own arrow category and apply the
  -- owner conservative-family criterion for generated sieves.
  rw [← Sieve.ofArrows_category S]
  rw [hp.jointly_reflect_ofArrows_mem]
  intro Φ x
  rcases Φ with ⟨q, hq⟩
  rcases (ObjectProperty.ofObj_iff p q).1 hq with ⟨i, rfl⟩
  obtain ⟨Y, g, hg, y, hy⟩ := hS i x
  let j : S.arrows.category := Presieve.categoryMk S.arrows g hg
  refine ⟨j, y, ?_⟩
  simpa [j] using hy

/-- Helper for Proposition 7.39.3: conservativity survives objectwise target-universe lifting of
the family of points. -/
lemma pointTargetUniverseLift_family_conservative
    {ι : Type w} (p : ι → GrothendieckTopology.Point.{max u v} J)
    (hp : (ObjectProperty.ofObj p).IsConservativeFamilyOfPoints)
    [HasSheafify J (Type (max (u + 1) (v + 1)))] :
    ObjectProperty.IsConservativeFamilyOfPoints
      (P := (ObjectProperty.ofObj
        (fun i ↦ pointTargetUniverseLift (C := C) (J := J) (p i)) :
          ObjectProperty (GrothendieckTopology.Point.{max (u + 1) (v + 1)} J))) := by
  -- Apply the owner constructor and lower all `ULift` witnesses to the original conservative
  -- family, where the previous sieve-reflection lemma applies.
  refine ObjectProperty.IsConservativeFamilyOfPoints.mk' ?_
  intro X S hS
  exact sieve_mem_of_family_fiber_lifts (J := J) p hp S (fun i ↦
    (pointTargetUniverseCoverLift_iff (C := C) (J := J) (p i) S).1
      (hS ⟨pointTargetUniverseLift (C := C) (J := J) (p i),
        ObjectProperty.ofObj_apply
          (fun i ↦ pointTargetUniverseLift (C := C) (J := J) (p i)) i⟩))

-- Proof sketch: for any two distinct sections of a sheaf, start with the trivial one-object
-- inverse system at the ambient object and apply Lemma 7.39.2 to obtain a refined inverse system
-- that still separates the sections and whose associated fiber functor is jointly surjective for
-- every finite covering family. The finite-refinement hypothesis upgrades this to all covering
-- families, so Proposition 7.33.3 turns the resulting functor into a point; Lemma 7.38.3 then
-- shows that the resulting family of points is conservative.
/-- Proposition 7.39.3: if finite limits exist in `C` and every covering family in `(C, J)`
admits a finite covering refinement, then `(C, J)` has enough points. -/
theorem hasEnoughPoints_of_finite_cover_refinement
    [Limits.HasFiniteLimits C]
    (hfinite : ∀ X : C, J.HasFiniteRefinementProperty X) :
    HasEnoughPoints.{max (u + 1) (v + 1)} J := by
  classical
  let ι : Type (max (u + 1) (v + 1)) :=
    Σ (ℱ : Sheaf J (Type (max u v))) (U : C),
      { ss : ℱ.obj.obj (op U) × ℱ.obj.obj (op U) // ss.1 ≠ ss.2 }
  let p : ι → GrothendieckTopology.Point.{max u v} J
    | ⟨ℱ, U, ⟨⟨s, s'⟩, hs⟩⟩ =>
        Classical.choose <|
          exists_point_separating_sections_of_finite_cover_refinement
            (J := J) (ℱ := ℱ) hfinite U s s' hs
  have hsep :
      ∀ ⦃ℱ : Sheaf J (Type (max u v))⦄ (U : C) (s s' : ℱ.obj.obj (op U)),
        s ≠ s' →
          ∃ i : ι, ∃ x : (p i).fiber.obj U,
            (p i).toPresheafFiber U x ℱ.obj s ≠
              (p i).toPresheafFiber U x ℱ.obj s' := by
    intro ℱ U s s' hs
    let i : ι := ⟨ℱ, U, ⟨⟨s, s'⟩, hs⟩⟩
    refine ⟨i, ?_⟩
    -- Index the conservative family by all unequal pairs of sections and use the chosen witness.
    simpa [p, i] using
      (Classical.choose_spec <|
        exists_point_separating_sections_of_finite_cover_refinement
          (J := J) (ℱ := ℱ) hfinite U s s' hs)
  have hconservative : (ObjectProperty.ofObj p).IsConservativeFamilyOfPoints := by
    -- First record the verified source-faithful frontier: the chosen family is conservative.
    exact section_separating_family_isConservative (J := J) p hsep
  let pLarge : ι → GrothendieckTopology.Point.{max (u + 1) (v + 1)} J :=
    fun i ↦ pointTargetUniverseLift (C := C) (J := J) (p i)
  have hlarge : (ObjectProperty.ofObj pLarge).IsConservativeFamilyOfPoints := by
    -- Lift the conservative family pointwise to the theorem's target universe.
    letI : HasSheafify J (Type (max (u + 1) (v + 1))) :=
      CategoryTheory.GrothendieckTopology.hasSheafify_ulift_type.{v, u, max (u + 1) (v + 1)}
        (J := J)
    simpa [pLarge] using
      pointTargetUniverseLift_family_conservative (J := J) p hconservative
  -- Package the lifted conservative family as the required enough-points witness.
  exact
    { exists_objectProperty := by
        exact ⟨ObjectProperty.ofObj pLarge, inferInstance, hlarge⟩ }

end CategoryTheory
