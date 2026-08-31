module

public import stacks_project.Chap04.CanonicalFiberPseudofunctor.ComparisonIso
public import Mathlib.CategoryTheory.Bicategory.Functor.LocallyDiscrete
@[expose] public section

/-!
# Canonical fiber pseudofunctor coherence package

This slim owner keeps the source-text part (5) of Lemma 4.33.7: the coherence proofs showing that
the chosen pullback functors and comparison isomorphisms assemble into the pseudofunctor of fibers.
-/

universe v₁ v₂ u₁ u₂

namespace CategoryTheory

open Functor
open Opposite
open scoped Bicategory

variable {C : Type u₁} [Category.{v₁} C]
variable {S : Type u₂} [Category.{v₂} S]

namespace PullbackChoice

variable {p : S ⥤ C} (hc : PullbackChoice p)

/-- Helper for Lemma 4.33.7: after transporting between equal pullback functors, the component at
`x` still postcomposes with the chosen pullback arrow to the expected map in the total category. -/
private theorem pullback_eqToHom_component_postcompose_eq
    {U V : C} {f g : V ⟶ U} (e : f = g) (x : Fiber p U) :
    Fiber.fiberInclusion.map ((eqToHom (congrArg (fun k ↦ hc.pullbackFunctor k) e)).app x) ≫
        hc.map g x =
      hc.map f x := by
  -- Reduce to the reflexive case, where the transported component is the identity.
  cases e
  simp

/-- Helper for Lemma 4.33.7: a morphism into a chosen pullback object is determined by its
postcomposition with the chosen strongly cartesian pullback arrow. -/
private theorem pullback_hom_ext
    {U V : C} (f : V ⟶ U) {x : Fiber p U} {y : Fiber p V}
    {ψ ψ' : y ⟶ f ^*[hc] x}
    (h : ψ.1 ≫ hc.map f x = ψ'.1 ≫ hc.map f x) :
    ψ = ψ' := by
  -- Forget to the ambient category and use uniqueness for the chosen strongly cartesian lift.
  apply Fiber.hom_ext
  change ψ.1 = ψ'.1
  letI : p.IsHomLift (𝟙 V) ψ.1 := ψ.2
  letI : p.IsHomLift (𝟙 V) ψ'.1 := ψ'.2
  exact
    @IsStronglyCartesian.ext _ _ _ _ p _ _ _ _
      f (hc.map f x) inferInstance _ _ (𝟙 V) ψ.1 ψ'.1 inferInstance inferInstance h

-- Proof sketch: after evaluating the associator coherence chain at `x`, every nontrivial factor
-- is a comparison component between chosen pullbacks, so postcomposing with the final chosen
-- pullback arrow lets the defining factorization equalities collapse the whole chain to the single
-- chosen pullback map for the composite `h.unop ≫ g.unop ≫ f.unop`.
/-- Helper for Lemma 4.33.7: the objectwise associator coherence chain postcomposes with the chosen
pullback map `hc.map ((h.unop ≫ g.unop) ≫ f.unop) x` to the expected triple-composite pullback
arrow. -/
private theorem fiberPseudofunctor_associator_component_postcompose_eq
    {U V W X : Cᵒᵖ} (f : U ⟶ V) (g : V ⟶ W) (h : W ⟶ X) (x : Fiber p (unop U)) :
    Fiber.fiberInclusion.map
        (((hc.pullbackCompIso (g.unop ≫ f.unop) h.unop).hom ≫
            whiskerRight (hc.pullbackCompIso f.unop g.unop).hom (hc.pullbackFunctor h.unop) ≫
            ((hc.pullbackFunctor f.unop).associator (hc.pullbackFunctor g.unop)
              (hc.pullbackFunctor h.unop)).hom ≫
            (hc.pullbackFunctor f.unop).whiskerLeft (hc.pullbackCompIso g.unop h.unop).inv ≫
            (hc.pullbackCompIso f.unop (h.unop ≫ g.unop)).inv).app x) ≫
        hc.map ((h.unop ≫ g.unop) ≫ f.unop) x =
      hc.map (h.unop ≫ g.unop ≫ f.unop) x := by
  -- Expand the Cat-valued composite to an ordinary composite in `S`, then collapse it by the
  -- defining factorization laws of the pullback comparison components.
  have h4 :
      Fiber.fiberInclusion.map ((hc.pullbackCompIso f.unop (h.unop ≫ g.unop)).inv.app x) ≫
        hc.map ((h.unop ≫ g.unop) ≫ f.unop) x =
      hc.map (h.unop ≫ g.unop) (f.unop ^*[hc] x) ≫ hc.map f.unop x := by
    simpa [pullbackCompIso] using
      hc.pullbackCompComponentIso_inv_fac (f := f.unop) (g := h.unop ≫ g.unop) x
  have h3 :
      Fiber.fiberInclusion.map ((hc.pullbackCompIso g.unop h.unop).inv.app
          ((hc.pullbackFunctor f.unop).obj x)) ≫
        hc.map (h.unop ≫ g.unop) (f.unop ^*[hc] x) =
      hc.map h.unop (g.unop ^*[hc] (f.unop ^*[hc] x)) ≫ hc.map g.unop (f.unop ^*[hc] x) := by
    simpa [pullbackCompIso] using
      hc.pullbackCompComponentIso_inv_fac (f := g.unop) (g := h.unop)
        ((hc.pullbackFunctor f.unop).obj x)
  have h2 :
      Fiber.fiberInclusion.map ((hc.pullbackFunctor h.unop).map
          ((hc.pullbackCompIso f.unop g.unop).hom.app x)) ≫
        hc.map h.unop (g.unop ^*[hc] (f.unop ^*[hc] x)) =
      hc.map h.unop ((g.unop ≫ f.unop) ^*[hc] x) ≫
        Fiber.fiberInclusion.map ((hc.pullbackCompIso f.unop g.unop).hom.app x) := by
    simpa [pullbackCompIso] using
      hc.pullbackFunctor_map_fac h.unop ((hc.pullbackCompIso f.unop g.unop).hom.app x)
  have hcomp :
      Fiber.fiberInclusion.map ((hc.pullbackCompIso f.unop g.unop).hom.app x) ≫
        hc.map g.unop (f.unop ^*[hc] x) ≫ hc.map f.unop x =
      hc.map (g.unop ≫ f.unop) x := by
    simpa [pullbackCompIso] using
      hc.pullbackCompComponentIso_fac (f := f.unop) (g := g.unop) x
  have h1 :
      Fiber.fiberInclusion.map ((hc.pullbackCompIso (g.unop ≫ f.unop) h.unop).hom.app x) ≫
        hc.map h.unop ((g.unop ≫ f.unop) ^*[hc] x) ≫ hc.map (g.unop ≫ f.unop) x =
      hc.map (h.unop ≫ g.unop ≫ f.unop) x := by
    simpa [Category.assoc, pullbackCompIso] using
      hc.pullbackCompComponentIso_fac (f := g.unop ≫ f.unop) (g := h.unop) x
  let α₁ := Fiber.fiberInclusion.map ((hc.pullbackCompIso (g.unop ≫ f.unop) h.unop).hom.app x)
  let α₂ := Fiber.fiberInclusion.map
    ((hc.pullbackFunctor h.unop).map ((hc.pullbackCompIso f.unop g.unop).hom.app x))
  let α₃ := Fiber.fiberInclusion.map
    ((hc.pullbackCompIso g.unop h.unop).inv.app ((hc.pullbackFunctor f.unop).obj x))
  let α₄ := Fiber.fiberInclusion.map ((hc.pullbackCompIso f.unop (h.unop ≫ g.unop)).inv.app x)
  have hmain :
      α₁ ≫ α₂ ≫ α₃ ≫ α₄ ≫ hc.map ((h.unop ≫ g.unop) ≫ f.unop) x =
        hc.map (h.unop ≫ g.unop ≫ f.unop) x := by
    calc
      α₁ ≫ α₂ ≫ α₃ ≫ α₄ ≫ hc.map ((h.unop ≫ g.unop) ≫ f.unop) x
          = α₁ ≫ α₂ ≫ α₃ ≫ (α₄ ≫ hc.map ((h.unop ≫ g.unop) ≫ f.unop) x) := by
              simp
      _ = α₁ ≫ α₂ ≫ α₃ ≫ (hc.map (h.unop ≫ g.unop) (f.unop ^*[hc] x) ≫ hc.map f.unop x) := by
            exact congrArg (fun k ↦ α₁ ≫ α₂ ≫ α₃ ≫ k) h4
      _ = α₁ ≫ α₂ ≫ α₃ ≫ hc.map (h.unop ≫ g.unop) (f.unop ^*[hc] x) ≫ hc.map f.unop x := by
            simp
      _ = α₁ ≫ α₂ ≫ (α₃ ≫ hc.map (h.unop ≫ g.unop) (f.unop ^*[hc] x)) ≫ hc.map f.unop x := by
            simp [Category.assoc]
      _ = α₁ ≫ α₂ ≫ (hc.map h.unop (g.unop ^*[hc] (f.unop ^*[hc] x)) ≫
            hc.map g.unop (f.unop ^*[hc] x)) ≫ hc.map f.unop x := by
            exact congrArg (fun k ↦ α₁ ≫ α₂ ≫ k ≫ hc.map f.unop x) h3
      _ = α₁ ≫ (α₂ ≫ hc.map h.unop (g.unop ^*[hc] (f.unop ^*[hc] x))) ≫
            hc.map g.unop (f.unop ^*[hc] x) ≫ hc.map f.unop x := by
            simp [Category.assoc]
      _ = α₁ ≫ (hc.map h.unop ((g.unop ≫ f.unop) ^*[hc] x) ≫
            Fiber.fiberInclusion.map ((hc.pullbackCompIso f.unop g.unop).hom.app x)) ≫
            hc.map g.unop (f.unop ^*[hc] x) ≫ hc.map f.unop x := by
            exact congrArg
              (fun k ↦ α₁ ≫ k ≫ hc.map g.unop (f.unop ^*[hc] x) ≫ hc.map f.unop x) h2
      _ = α₁ ≫ hc.map h.unop ((g.unop ≫ f.unop) ^*[hc] x) ≫
            Fiber.fiberInclusion.map ((hc.pullbackCompIso f.unop g.unop).hom.app x) ≫
            hc.map g.unop (f.unop ^*[hc] x) ≫ hc.map f.unop x := by
            simp [Category.assoc]
      _ = α₁ ≫ hc.map h.unop ((g.unop ≫ f.unop) ^*[hc] x) ≫
            (Fiber.fiberInclusion.map ((hc.pullbackCompIso f.unop g.unop).hom.app x) ≫
              hc.map g.unop (f.unop ^*[hc] x) ≫ hc.map f.unop x) := by
            simp
      _ = α₁ ≫ hc.map h.unop ((g.unop ≫ f.unop) ^*[hc] x) ≫ hc.map (g.unop ≫ f.unop) x := by
            exact congrArg
              (fun k ↦ α₁ ≫ hc.map h.unop ((g.unop ≫ f.unop) ^*[hc] x) ≫ k) hcomp
      _ = hc.map (h.unop ≫ g.unop ≫ f.unop) x := h1
  simpa [α₁, α₂, α₃, α₄, NatTrans.comp_app, Functor.whiskerLeft_app,
    Functor.whiskerRight_app, Category.assoc] using hmain

-- Proof sketch: this is exactly the associativity coherence required in Lemma 4.33.7 (3) for the
-- comparison isomorphisms from part (1), expressed in mathlib's pseudofunctor orientation.
theorem fiberPseudofunctor_map₂_associator
    {U V W X : Cᵒᵖ} (f : U ⟶ V) (g : V ⟶ W) (h : W ⟶ X) :
    (Cat.Hom.isoMk (hc.pullbackCompIso (f ≫ g).unop h.unop)).hom ≫
        (Cat.Hom.isoMk (hc.pullbackCompIso f.unop g.unop)).hom ▷
            (hc.pullbackFunctor h.unop).toCatHom ≫
          (α_ ((hc.pullbackFunctor f.unop).toCatHom) ((hc.pullbackFunctor g.unop).toCatHom)
            ((hc.pullbackFunctor h.unop).toCatHom)).hom ≫
            (hc.pullbackFunctor f.unop).toCatHom ◁
              (Cat.Hom.isoMk (hc.pullbackCompIso g.unop h.unop)).inv ≫
              (Cat.Hom.isoMk (hc.pullbackCompIso f.unop (g ≫ h).unop)).inv =
      eqToHom (by
        exact congrArg (fun k ↦ (hc.pullbackFunctor k.unop).toCatHom) (Category.assoc f g h)) :=
  by
    -- Route correction: reduce the Cat-valued coherence law to an objectwise equality in the
    -- ambient category, then compare both sides by postcomposition with the chosen pullback map.
    apply Cat.Hom₂.ext
    ext x
    apply hc.pullback_hom_ext (((h.unop ≫ g.unop) ≫ f.unop))
    -- The associator comparison chain and the transported identity both recover the same chosen
    -- pullback arrow to `x`, so uniqueness of maps into the chosen pullback object applies.
    have hleft := fiberPseudofunctor_associator_component_postcompose_eq (hc := hc) f g h x
    have eAssoc : h.unop ≫ g.unop ≫ f.unop = ((h.unop ≫ g.unop) ≫ f.unop) := by
      simpa [Category.assoc] using congrArg (fun k ↦ k.unop) (Category.assoc f g h)
    have hright :
        Fiber.fiberInclusion.map
            (((eqToHom (congrArg (fun k ↦ hc.pullbackFunctor k) eAssoc)).app x)) ≫
          hc.map ((h.unop ≫ g.unop) ≫ f.unop) x =
        hc.map (h.unop ≫ g.unop ≫ f.unop) x := by
      simpa [Category.assoc] using
        hc.pullback_eqToHom_component_postcompose_eq
          (f := h.unop ≫ g.unop ≫ f.unop) (g := (h.unop ≫ g.unop) ≫ f.unop)
          (e := eAssoc) x
    refine hleft.trans ?_
    rw [Cat.Hom₂.eqToHom_toNatTrans]
    change
      hc.map (h.unop ≫ g.unop ≫ f.unop) x =
        Fiber.fiberInclusion.map
            (((eqToHom (congrArg (fun k ↦ hc.pullbackFunctor k) eAssoc)).app x)) ≫
          hc.map ((h.unop ≫ g.unop) ≫ f.unop) x
    exact hright.symm

-- Proof sketch: after evaluating the left-unit coherence chain at an object, the functorial
-- whiskering contributes the pullback of the inverse unit component, and the defining factorization
-- lemmas for the comparison and unit components recover the chosen pullback map for `f`.
/-- Helper for Lemma 4.33.7: the objectwise left-unit coherence component postcomposes with the
chosen pullback map `hc.map f.unop x` to the expected composite pullback arrow. -/
private theorem fiberPseudofunctor_left_unitor_component_postcompose_eq
    {U V : Cᵒᵖ} (f : U ⟶ V) (x : Fiber p (unop U)) :
    Fiber.fiberInclusion.map
        (((hc.pullbackCompIso (𝟙 (unop U)) f.unop).hom ≫
            Functor.whiskerRight (hc.pullbackIdIso (unop U)).inv (hc.pullbackFunctor f.unop) ≫
            (hc.pullbackFunctor f.unop).leftUnitor.hom).app x) ≫
        hc.map f.unop x =
      hc.map (f.unop ≫ 𝟙 (unop U)) x := by
  -- Evaluate the whiskered unit component and then read off the two defining factorization laws.
  have hstep1 :
      Fiber.fiberInclusion.map
          (((hc.pullbackCompIso (𝟙 (unop U)) f.unop).hom ≫
              Functor.whiskerRight (hc.pullbackIdIso (unop U)).inv (hc.pullbackFunctor f.unop) ≫
              (hc.pullbackFunctor f.unop).leftUnitor.hom).app x) ≫
          hc.map f.unop x =
        Fiber.fiberInclusion.map
            ((hc.pullbackCompIso (𝟙 (unop U)) f.unop).hom.app x) ≫
          hc.map f.unop (((𝟙 (unop U)) ^*[hc] x)) ≫
          ((hc.pullbackIdIso (unop U)).inv.app x).1 := by
    calc
      Fiber.fiberInclusion.map
          (((hc.pullbackCompIso (𝟙 (unop U)) f.unop).hom ≫
              Functor.whiskerRight (hc.pullbackIdIso (unop U)).inv (hc.pullbackFunctor f.unop) ≫
              (hc.pullbackFunctor f.unop).leftUnitor.hom).app x) ≫
          hc.map f.unop x
          =
        Fiber.fiberInclusion.map
            ((hc.pullbackCompIso (𝟙 (unop U)) f.unop).hom.app x) ≫
          Fiber.fiberInclusion.map
            ((hc.pullbackFunctor f.unop).map ((hc.pullbackIdIso (unop U)).inv.app x)) ≫
          hc.map f.unop x := by
            simp [NatTrans.comp_app, Functor.whiskerRight_app, Category.assoc]
      _ =
        Fiber.fiberInclusion.map
            ((hc.pullbackCompIso (𝟙 (unop U)) f.unop).hom.app x) ≫
          hc.map f.unop (((𝟙 (unop U)) ^*[hc] x)) ≫
          ((hc.pullbackIdIso (unop U)).inv.app x).1 := by
            simpa [Category.assoc] using
              congrArg
                (fun k ↦ Fiber.fiberInclusion.map
                  ((hc.pullbackCompIso (𝟙 (unop U)) f.unop).hom.app x) ≫ k)
                (hc.pullbackFunctor_map_fac f.unop ((hc.pullbackIdIso (unop U)).inv.app x))
  have hstep2 :
      Fiber.fiberInclusion.map
          ((hc.pullbackCompIso (𝟙 (unop U)) f.unop).hom.app x) ≫
        hc.map f.unop (((𝟙 (unop U)) ^*[hc] x)) ≫
        ((hc.pullbackIdIso (unop U)).inv.app x).1 =
      Fiber.fiberInclusion.map
          ((hc.pullbackCompIso (𝟙 (unop U)) f.unop).hom.app x) ≫
        hc.map f.unop (((𝟙 (unop U)) ^*[hc] x)) ≫
        hc.map (𝟙 (unop U)) x := by
    simpa using
      congrArg
        (fun k ↦ Fiber.fiberInclusion.map
          ((hc.pullbackCompIso (𝟙 (unop U)) f.unop).hom.app x) ≫
            hc.map f.unop (((𝟙 (unop U)) ^*[hc] x)) ≫ k)
        (hc.pullbackIdComponentIso_inv_eq (unop U) x)
  have hstep3 :
      Fiber.fiberInclusion.map
          ((hc.pullbackCompIso (𝟙 (unop U)) f.unop).hom.app x) ≫
        hc.map f.unop (((𝟙 (unop U)) ^*[hc] x)) ≫
        hc.map (𝟙 (unop U)) x =
      hc.map (f.unop ≫ 𝟙 (unop U)) x := by
    simpa [Category.assoc] using
      hc.pullbackCompComponentIso_fac (f := 𝟙 (unop U)) (g := f.unop) x
  exact hstep1.trans (hstep2.trans hstep3)

-- Proof sketch: this is the left unit coherence for the pseudofunctor determined by the chosen
-- pullback system, using the unit comparison isomorphisms from part (2).
theorem fiberPseudofunctor_map₂_left_unitor
    {U V : Cᵒᵖ} (f : U ⟶ V) :
    (Cat.Hom.isoMk (hc.pullbackCompIso (𝟙 U).unop f.unop)).hom ≫
        (Cat.Hom.isoMk ((hc.pullbackIdIso (unop U)).symm)).hom ▷
            (hc.pullbackFunctor f.unop).toCatHom ≫
          (λ_ ((hc.pullbackFunctor f.unop).toCatHom)).hom =
      eqToHom (by
        exact congrArg (fun k ↦ (hc.pullbackFunctor k.unop).toCatHom) (Category.id_comp f)) :=
  by
    -- Route correction: compare the two endomorphisms of `f.unop ^*[hc] x` by postcomposing with
    -- the chosen strongly cartesian arrow to `x`.
    apply Cat.Hom₂.ext
    ext x
    apply hc.pullback_hom_ext f.unop
    -- The comparison chain and the transport morphism both recover the chosen map `hc.map f.unop x`.
    have hleft := hc.fiberPseudofunctor_left_unitor_component_postcompose_eq f x
    have hright :
        Fiber.fiberInclusion.map
            ((eqToHom
              (congrArg (fun k ↦ hc.pullbackFunctor k)
                (by simpa using congrArg (fun k ↦ k.unop) (Category.id_comp f)))).app x) ≫
          hc.map f.unop x =
        hc.map (f.unop ≫ 𝟙 (unop U)) x := by
      simpa using
        hc.pullback_eqToHom_component_postcompose_eq
          (f := f.unop ≫ 𝟙 (unop U)) (g := f.unop)
          (e := by simpa using congrArg (fun k ↦ k.unop) (Category.id_comp f)) x
    refine hleft.trans ?_
    rw [Cat.Hom₂.eqToHom_toNatTrans]
    change
      hc.map (f.unop ≫ 𝟙 (unop U)) x =
        Fiber.fiberInclusion.map
            ((eqToHom
              (congrArg (fun k ↦ hc.pullbackFunctor k)
                (by simpa using congrArg (fun k ↦ k.unop) (Category.id_comp f)))).app x) ≫
          hc.map f.unop x
    exact hright.symm

-- Proof sketch: this is the right unit coherence for the same pseudofunctor data.
/-- Helper for Lemma 4.33.7: the objectwise right-unit coherence component postcomposes with the
chosen pullback map `hc.map f.unop x` to the expected composite pullback arrow. -/
private theorem fiberPseudofunctor_right_unitor_component_postcompose_eq
    {U V : Cᵒᵖ} (f : U ⟶ V) (x : Fiber p (unop U)) :
    Fiber.fiberInclusion.map
        (((hc.pullbackCompIso f.unop (𝟙 (unop V))).hom ≫
            (hc.pullbackFunctor f.unop).whiskerLeft (hc.pullbackIdIso (unop V)).inv ≫
            (hc.pullbackFunctor f.unop).rightUnitor.hom).app x) ≫
        hc.map f.unop x =
      hc.map (𝟙 (unop V) ≫ f.unop) x := by
  -- Evaluate the left-whiskered unit component and then apply the comparison factorization laws.
  calc
    Fiber.fiberInclusion.map
        (((hc.pullbackCompIso f.unop (𝟙 (unop V))).hom ≫
            (hc.pullbackFunctor f.unop).whiskerLeft (hc.pullbackIdIso (unop V)).inv ≫
            (hc.pullbackFunctor f.unop).rightUnitor.hom).app x) ≫
        hc.map f.unop x
        =
      Fiber.fiberInclusion.map ((hc.pullbackCompIso f.unop (𝟙 (unop V))).hom.app x) ≫
        Fiber.fiberInclusion.map
          (((hc.pullbackIdIso (unop V)).inv).app ((hc.pullbackFunctor f.unop).obj x)) ≫
        hc.map f.unop x := by
          simp [NatTrans.comp_app, Functor.whiskerLeft_app, Category.assoc]
    _ =
      Fiber.fiberInclusion.map ((hc.pullbackCompIso f.unop (𝟙 (unop V))).hom.app x) ≫
        hc.map (𝟙 (unop V)) ((hc.pullbackFunctor f.unop).obj x) ≫
        hc.map f.unop x := by
          simpa using
            congrArg
              (fun k ↦ Fiber.fiberInclusion.map
                ((hc.pullbackCompIso f.unop (𝟙 (unop V))).hom.app x) ≫ k ≫ hc.map f.unop x)
              (hc.pullbackIdComponentIso_inv_eq (unop V) ((hc.pullbackFunctor f.unop).obj x))
    _ = hc.map (𝟙 (unop V) ≫ f.unop) x := by
          simpa [Category.assoc] using
            hc.pullbackCompComponentIso_fac (f := f.unop) (g := 𝟙 (unop V)) x

theorem fiberPseudofunctor_map₂_right_unitor
    {U V : Cᵒᵖ} (f : U ⟶ V) :
    (Cat.Hom.isoMk (hc.pullbackCompIso f.unop (𝟙 V).unop)).hom ≫
        (hc.pullbackFunctor f.unop).toCatHom ◁
          (Cat.Hom.isoMk ((hc.pullbackIdIso (unop V)).symm)).hom ≫
          (ρ_ ((hc.pullbackFunctor f.unop).toCatHom)).hom =
      eqToHom (by
        exact congrArg (fun k ↦ (hc.pullbackFunctor k.unop).toCatHom) (Category.comp_id f)) :=
  by
    -- Route correction: compare the two endomorphisms by the same postcomposition uniqueness used
    -- for the left unit law, now with the unit component whiskered on the left.
    apply Cat.Hom₂.ext
    ext x
    apply hc.pullback_hom_ext f.unop
    -- The comparison chain and the transport morphism both recover the same chosen map `hc.map f.unop x`.
    have hleft := hc.fiberPseudofunctor_right_unitor_component_postcompose_eq f x
    have hright :
        Fiber.fiberInclusion.map
            ((eqToHom
              (congrArg (fun k ↦ hc.pullbackFunctor k)
                (by simpa using congrArg (fun k ↦ k.unop) (Category.comp_id f)))).app x) ≫
          hc.map f.unop x =
        hc.map (𝟙 (unop V) ≫ f.unop) x := by
      simpa using
        hc.pullback_eqToHom_component_postcompose_eq
          (f := 𝟙 (unop V) ≫ f.unop) (g := f.unop)
          (e := by simpa using congrArg (fun k ↦ k.unop) (Category.comp_id f)) x
    refine hleft.trans ?_
    rw [Cat.Hom₂.eqToHom_toNatTrans]
    change
      hc.map (𝟙 (unop V) ≫ f.unop) x =
        Fiber.fiberInclusion.map
            ((eqToHom
              (congrArg (fun k ↦ hc.pullbackFunctor k)
                (by simpa using congrArg (fun k ↦ k.unop) (Category.comp_id f)))).app x) ≫
          hc.map f.unop x
    exact hright.symm

/-- Lemma 4.33.7 (3): the fiber categories, pullback functors, composition comparisons
`α_{g,f}`, and unit comparisons `α_U` assemble into a pseudofunctor `Cᵒᵖ ⥤ᵖ Cat`, i.e. into the
canonical mathlib model of a pseudofunctor to the source text's `(2,1)`-category of categories. -/
noncomputable def fiberPseudofunctor :
    LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat :=
  LocallyDiscrete.mkPseudofunctor
    (fun U ↦ Cat.of (Fiber p (unop U)))
    (fun f ↦ (hc.pullbackFunctor f.unop).toCatHom)
    (fun U ↦ Cat.Hom.isoMk ((hc.pullbackIdIso (unop U)).symm))
    (fun f g ↦ Cat.Hom.isoMk (hc.pullbackCompIso f.unop g.unop))
    (fun f g h ↦ hc.fiberPseudofunctor_map₂_associator f g h)
    (fun f ↦ hc.fiberPseudofunctor_map₂_left_unitor f)
    (fun f ↦ hc.fiberPseudofunctor_map₂_right_unitor f)

end PullbackChoice

end CategoryTheory
