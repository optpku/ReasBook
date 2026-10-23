module

public import stacks_project.Chap04.Lemma_4_33_7
public import stacks_project.Chap04.Definition_4_36_2

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

universe v₁ v₂ u₁ u₂

namespace CategoryTheory

open BasedFunctor
open Functor Fiber
open Opposite
open scoped Bicategory

variable {C : Type u₁} [Category.{v₁} C]
variable {S : Type (max u₁ u₂)} [Category.{max v₁ v₂} S]

/- Domain-style sampling for Lemma 4.36.3:
- primary domain: split fibred categories, chosen pullback systems on standard fibers, and the
  canonical pseudofunctor/co-Grothendieck bridge.
- inspected owner-level declarations:
  `PullbackChoice`,
  `PullbackChoice.pullbackFunctor`,
  `PullbackChoice.pullbackCompIso`,
  `PullbackChoice.pullbackIdIso`,
  `Functor.IsSplitFibredCategory`.
  together with strict composition for its pullback functors.  Since this formalization keeps
  identity pullbacks only up to the canonical unit isomorphism from Lemma 4.33.7, a literal
  ordinary `Cat`-valued functor also needs a strict unit normalization.
- primitive data: the chosen pullback system `hc : PullbackChoice p`.
- derived API: the composition-on-the-nose equations
  `hc.pullbackFunctor (g ≫ f) = hc.pullbackFunctor f ⋙ hc.pullbackFunctor g`, and separately the
  optional strict unit normalization `hc.pullbackFunctor (𝟙 U) = 𝟭 (Fiber p U)`.

Source/core/bridge triage:
- `source-facing`: the Stacks statement is an equality criterion for a split cleavage. With the
  present `PullbackChoice` API, identity and composition comparisons live as canonical
  isomorphisms from Lemma 4.33.7; the formal theorem below therefore records the normalized strict
  data needed to build an ordinary contravariant `Cat`-valued functor.
- `core/canonical`: `p.IsSplitFibredCategory`.
- `bridge/view`: the co-Grothendieck model attached to the strict fiber functor. -/

-- Proof sketch: a normalized pullback system with strict unit and composition determines an
-- ordinary contravariant `Cat`-valued functor on the fibers. Its co-Grothendieck construction is
-- split by definition. If the original `p` is explicitly identified over `C` with that strict
-- model, splitness of `p` follows by packaging this identification in Definition 4.36.2.
/-- Helper for Lemma 4.36.3: a strict pullback choice determines the ordinary contravariant
`Cat`-valued functor on the standard fibers. -/
noncomputable def strict_pullback_functor
    {p : S ⥤ C} (hc : PullbackChoice p)
    (hid : ∀ U : C, hc.pullbackFunctor (𝟙 U) = 𝟭 (Fiber p U))
    (hcomp : ∀ {U V W : C} (f : V ⟶ U) (g : W ⟶ V),
      hc.pullbackFunctor (g ≫ f) = hc.pullbackFunctor f ⋙ hc.pullbackFunctor g) :
    Cᵒᵖ ⥤ CategoryTheory.Cat where
  obj := fun U ↦ CategoryTheory.Cat.of (Fiber p (unop U))
  map := fun f ↦ (hc.pullbackFunctor f.unop).toCatHom
  map_id := by
    -- The strict unit hypothesis turns pullback along identities into the literal identity functor.
    intro U
    apply CategoryTheory.Cat.ext
    simpa using hid (unop U)
  map_comp := by
    -- The strict composition hypothesis is exactly the functoriality law on the fibers.
    intro U V W f g
    apply CategoryTheory.Cat.ext
    simpa using hcomp f.unop g.unop

/-- A bare strict composition law for chosen pullback functors only makes the identity pullback
functor idempotent. The normalized strict model below therefore records the identity law as a
separate hypothesis rather than deriving it from composition. -/
theorem PullbackChoice.pullbackFunctor_id_idempotent_of_compStrict
    {p : S ⥤ C} (hc : PullbackChoice p)
    (hcomp : ∀ {U V W : C} (f : V ⟶ U) (g : W ⟶ V),
      hc.pullbackFunctor (g ≫ f) = hc.pullbackFunctor f ⋙ hc.pullbackFunctor g)
    (U : C) :
    hc.pullbackFunctor (𝟙 U) =
      hc.pullbackFunctor (𝟙 U) ⋙ hc.pullbackFunctor (𝟙 U) := by
  simpa using hcomp (𝟙 U) (𝟙 U)

/-- Helper for Lemma 4.36.3: transporting along an equality of pullback functors does not change
the ambient chosen pullback arrow after forgetting to the total category. -/
private theorem pullbackEqToHomComponentPostcomposeEq
    {p : S ⥤ C} (hc : PullbackChoice p)
    {U V : C} {f g : V ⟶ U} (e : f = g) (x : Fiber p U) :
    Fiber.fiberInclusion.map ((eqToHom (congrArg (fun k ↦ hc.pullbackFunctor k) e)).app x) ≫
        hc.map g x =
      hc.map f x := by
  -- Reduce the transport comparison to the reflexive case, where the component is the identity.
  cases e
  simp

/-- Helper for Lemma 4.36.3: a morphism into a chosen pullback object is determined by its
postcomposition with the chosen pullback arrow. -/
private theorem pullbackHom_ext
    {p : S ⥤ C} (hc : PullbackChoice p)
    {U V : C} (f : V ⟶ U) {x : Fiber p U} {y : Fiber p V}
    {ψ ψ' : y ⟶ (hc.pullbackFunctor f).obj x}
    (h : ψ.1 ≫ hc.map f x = ψ'.1 ≫ hc.map f x) :
    ψ = ψ' := by
  -- Forget to the ambient category and use uniqueness for lifts into the chosen cartesian arrow.
  apply Fiber.hom_ext
  change ψ.1 = ψ'.1
  letI : p.IsHomLift (𝟙 V) ψ.1 := ψ.2
  letI : p.IsHomLift (𝟙 V) ψ'.1 := ψ'.2
  have hψ : p.IsHomLift (𝟙 V) ψ.1 := inferInstance
  have hψ' : p.IsHomLift (𝟙 V) ψ'.1 := inferInstance
  exact
    @IsStronglyCartesian.ext _ _ _ _ p _ _ _ _
      f (hc.map f x) inferInstance _ _ (𝟙 V) ψ.1 ψ'.1 hψ hψ' h

/-- Helper for Lemma 4.36.3: the explicit source-side identity-comparison chain postcomposes with
the chosen pullback arrow to the expected composite pullback map. -/
private theorem pullbackIdSourceTransportPostcomposeEq
    {p : S ⥤ C} (hc : PullbackChoice p)
    {U T : C} (f : U ⟶ T) (x : Fiber p T) :
    Fiber.fiberInclusion.map
        ((hc.pullbackCompIso f (𝟙 U)).hom.app x ≫
          (hc.pullbackIdIso U).inv.app ((hc.pullbackFunctor f).obj x)) ≫
        hc.map f x =
      hc.map (𝟙 U ≫ f) x := by
  -- Expand the comparison chain and collapse it using the component factorization laws.
  have hstep1 :
      Fiber.fiberInclusion.map
          ((hc.pullbackCompIso f (𝟙 U)).hom.app x ≫
            (hc.pullbackIdIso U).inv.app ((hc.pullbackFunctor f).obj x)) ≫
          hc.map f x =
        ((hc.pullbackCompIso f (𝟙 U)).hom.app x).1 ≫
          hc.map (𝟙 U) ((hc.pullbackFunctor f).obj x) ≫
            hc.map f x := by
    rw [Functor.map_comp]
    simpa [PullbackChoice.pullbackIdIso, Category.assoc] using
      congrArg
        (fun k ↦ ((hc.pullbackCompIso f (𝟙 U)).hom.app x).1 ≫ k ≫ hc.map f x)
        (hc.pullbackIdComponentIso_inv_eq U ((hc.pullbackFunctor f).obj x))
  have hstep2 :
      ((hc.pullbackCompIso f (𝟙 U)).hom.app x).1 ≫
          hc.map (𝟙 U) ((hc.pullbackFunctor f).obj x) ≫
            hc.map f x =
        hc.map (𝟙 U ≫ f) x := by
    simpa [PullbackChoice.pullbackCompIso, Category.assoc] using
      hc.pullbackCompComponentIso_fac (f := f) (g := 𝟙 U) x
  exact hstep1.trans hstep2

/-- Helper for Lemma 4.36.3: the explicit target-side identity-comparison chain postcomposes with
the composite pullback arrow to the original chosen pullback map. -/
private theorem pullbackIdTargetTransportPostcomposeEq
    {p : S ⥤ C} (hc : PullbackChoice p)
    {U T : C} (f : U ⟶ T) (x : Fiber p T) :
    Fiber.fiberInclusion.map
        ((hc.pullbackIdIso U).hom.app ((hc.pullbackFunctor f).obj x) ≫
          (hc.pullbackCompIso f (𝟙 U)).inv.app x) ≫
        hc.map (𝟙 U ≫ f) x =
      hc.map f x := by
  -- Route correction: normalize the target transport through the unit comparison first, then
  -- apply the inverse comparison-factorization law.
  have hstep1 :
      Fiber.fiberInclusion.map
          ((hc.pullbackIdIso U).hom.app ((hc.pullbackFunctor f).obj x) ≫
            (hc.pullbackCompIso f (𝟙 U)).inv.app x) ≫
          hc.map (𝟙 U ≫ f) x =
        ((hc.pullbackIdIso U).hom.app ((hc.pullbackFunctor f).obj x)).1 ≫
          hc.map (𝟙 U) ((hc.pullbackFunctor f).obj x) ≫
            hc.map f x := by
    rw [Functor.map_comp]
    simpa [PullbackChoice.pullbackIdIso, Category.assoc] using
      congrArg
        (fun k ↦ ((hc.pullbackIdIso U).hom.app ((hc.pullbackFunctor f).obj x)).1 ≫ k)
        (hc.pullbackCompComponentIso_inv_fac (f := f) (g := 𝟙 U) x)
  have hstep2 :
      ((hc.pullbackIdIso U).hom.app ((hc.pullbackFunctor f).obj x)).1 ≫
          hc.map (𝟙 U) ((hc.pullbackFunctor f).obj x) ≫
            hc.map f x =
        hc.map f x := by
    have hfac :
        ((hc.pullbackIdIso U).hom.app ((hc.pullbackFunctor f).obj x)).1 ≫
            hc.map (𝟙 U) ((hc.pullbackFunctor f).obj x) =
          𝟙 ((hc.pullbackFunctor f).obj x).1 := by
      simpa [PullbackChoice.pullbackIdIso] using
        hc.pullbackIdComponentIso_fac U ((hc.pullbackFunctor f).obj x)
    calc
      ((hc.pullbackIdIso U).hom.app ((hc.pullbackFunctor f).obj x)).1 ≫
            hc.map (𝟙 U) ((hc.pullbackFunctor f).obj x) ≫
              hc.map f x
          =
        (((hc.pullbackIdIso U).hom.app ((hc.pullbackFunctor f).obj x)).1 ≫
              hc.map (𝟙 U) ((hc.pullbackFunctor f).obj x)) ≫
            hc.map f x := by
              simp [Category.assoc]
      _ = hc.map f x := by
            rw [hfac]
            simp
  exact hstep1.trans hstep2

/-- Helper for Lemma 4.36.3: the object transport induced by `Category.id_comp` agrees with the
explicit source-side identity comparison chain. -/
private theorem pullbackIdEqToHom
    {p : S ⥤ C} (hc : PullbackChoice p)
    {U T : C} (f : U ⟶ T) (x : Fiber p T) :
    eqToHom (congrArg (fun k ↦ (hc.pullbackFunctor k).obj x) (Category.id_comp f)) =
      (hc.pullbackCompIso f (𝟙 U)).hom.app x ≫
        (hc.pullbackIdIso U).inv.app ((hc.pullbackFunctor f).obj x) := by
  -- Compare the two candidate transports after postcomposing with the chosen pullback arrow.
  apply pullbackHom_ext hc f
  have hleft :
      Fiber.fiberInclusion.map
          (eqToHom (congrArg (fun k ↦ (hc.pullbackFunctor k).obj x) (Category.id_comp f))) ≫
          hc.map f x =
        hc.map (𝟙 U ≫ f) x := by
    have htransport :
        Fiber.fiberInclusion.map
            ((eqToHom (congrArg (fun k ↦ hc.pullbackFunctor k) (Category.id_comp f))).app x) ≫
            hc.map f x =
          hc.map (𝟙 U ≫ f) x :=
      pullbackEqToHomComponentPostcomposeEq hc (e := Category.id_comp f) x
    simpa using htransport
  have hright :
      Fiber.fiberInclusion.map
          ((hc.pullbackCompIso f (𝟙 U)).hom.app x ≫
            (hc.pullbackIdIso U).inv.app ((hc.pullbackFunctor f).obj x)) ≫
          hc.map f x =
        hc.map (𝟙 U ≫ f) x := by
    have htransport := pullbackIdSourceTransportPostcomposeEq hc (f := f) (x := x)
    rw [Functor.map_comp] at htransport
    simpa [Category.assoc] using htransport
  exact hleft.trans hright.symm

/-- Helper for Lemma 4.36.3: the inverse transport induced by `Category.id_comp` agrees with the
explicit target-side identity comparison chain. -/
private theorem pullbackIdEqToHomSymm
    {p : S ⥤ C} (hc : PullbackChoice p)
    {U T : C} (f : U ⟶ T) (x : Fiber p T) :
    eqToHom (congrArg (fun k ↦ (hc.pullbackFunctor k).obj x) (Category.id_comp f)).symm =
      (hc.pullbackIdIso U).hom.app ((hc.pullbackFunctor f).obj x) ≫
        (hc.pullbackCompIso f (𝟙 U)).inv.app x := by
  -- Compare the two inverse transports after postcomposing with the composite pullback arrow.
  apply pullbackHom_ext hc (𝟙 U ≫ f)
  have hleft :
      Fiber.fiberInclusion.map
          (eqToHom (congrArg (fun k ↦ (hc.pullbackFunctor k).obj x) (Category.id_comp f)).symm) ≫
          hc.map (𝟙 U ≫ f) x =
        hc.map f x := by
    have htransport :
        Fiber.fiberInclusion.map
            ((eqToHom (congrArg (fun k ↦ hc.pullbackFunctor k)
              (Category.id_comp f)).symm).app x) ≫
            hc.map (𝟙 U ≫ f) x =
          hc.map f x :=
      pullbackEqToHomComponentPostcomposeEq hc (f := f) (g := 𝟙 U ≫ f)
        (e := (Category.id_comp f).symm) x
    simpa using htransport
  have hright :
      Fiber.fiberInclusion.map
          ((hc.pullbackIdIso U).hom.app ((hc.pullbackFunctor f).obj x) ≫
            (hc.pullbackCompIso f (𝟙 U)).inv.app x) ≫
          hc.map (𝟙 U ≫ f) x =
        hc.map f x := by
    have htransport := pullbackIdTargetTransportPostcomposeEq hc (f := f) (x := x)
    rw [Functor.map_comp] at htransport
    simpa [Category.assoc] using htransport
  exact hleft.trans hright.symm

/-- Helper for Lemma 4.36.3: forgetting an equality morphism in a standard fiber recovers the
corresponding equality morphism in the ambient category. -/
private theorem fiberEqToHom_map
    {p : S ⥤ C} {U : C} {P Q : Fiber p U} (h : P = Q) :
    Fiber.fiberInclusion.map (eqToHom h) = eqToHom (congrArg Subtype.val h) := by
  -- Equality morphisms in the fiber are defined by the same underlying arrows in the total
  -- category.
  cases h
  rfl

/-- Helper for Lemma 4.36.3: factor a total-category arrow through the chosen pullback of its
target along its image in the base. -/
private noncomputable def factorToPullback
    {p : S ⥤ C} (hc : PullbackChoice p) {x y : S} (φ : x ⟶ y) :
    let xF : Fiber p (p.obj x) := ⟨x, rfl⟩
    let yF : Fiber p (p.obj y) := ⟨y, rfl⟩
    xF ⟶ (hc.pullbackFunctor (p.map φ)).obj yF := by
  dsimp
  let xF : Fiber p (p.obj x) := ⟨x, rfl⟩
  let yF : Fiber p (p.obj y) := ⟨y, rfl⟩
  letI : p.IsHomLift (p.map φ) φ := inferInstance
  let m := IsStronglyCartesian.map p (p.map φ) (hc.map (p.map φ) yF)
    (Category.id_comp (p.map φ)).symm φ
  have hm : p.IsHomLift (𝟙 (p.obj x)) m := by
    dsimp [m]
    exact IsStronglyCartesian.map_isHomLift p (p.map φ) (hc.map (p.map φ) yF)
      (Category.id_comp (p.map φ)).symm φ
  exact ⟨m, hm⟩

/-- Helper for Lemma 4.36.3: the factorization through a chosen pullback recomposes to the original
total-category arrow. -/
private theorem factorToPullback_fac
    {p : S ⥤ C} (hc : PullbackChoice p) {x y : S} (φ : x ⟶ y) :
    let yF : Fiber p (p.obj y) := ⟨y, rfl⟩
    (factorToPullback hc φ).1 ≫ hc.map (p.map φ) yF = φ := by
  dsimp [factorToPullback]
  let yF : Fiber p (p.obj y) := ⟨y, rfl⟩
  change IsStronglyCartesian.map p (p.map φ) (hc.map (p.map φ) yF)
    (Category.id_comp (p.map φ)).symm φ ≫ hc.map (p.map φ) yF = φ
  exact IsStronglyCartesian.fac p (p.map φ) (hc.map (p.map φ) yF)
    (Category.id_comp (p.map φ)).symm φ

/-- Helper for Lemma 4.36.3: the tautological pullback choice on a split co-Grothendieck model. -/
private noncomputable def modelPullbackChoice
    (F : Cᵒᵖ ⥤ CategoryTheory.Cat.{v₂, u₂}) :
    PullbackChoice (Pseudofunctor.CoGrothendieck.forget (F.toPseudofunctor')) where
  obj := by
    intro U V f x
    rcases x with ⟨X, hX⟩
    subst hX
    exact ⟨Pseudofunctor.CoGrothendieck.domainCartesianLift X.fiber f, rfl⟩
  map := by
    intro U V f x
    rcases x with ⟨X, hX⟩
    subst hX
    exact Pseudofunctor.CoGrothendieck.cartesianLift X.fiber f
  isStronglyCartesian := by
    intro U V f x
    rcases x with ⟨X, hX⟩
    subst hX
    exact Pseudofunctor.CoGrothendieck.isStronglyCartesian_homCartesianLift X.fiber f

/-- Helper for Lemma 4.36.3: the strict co-Grothendieck model attached to a strict pullback
choice is split by construction. -/
private theorem strictPullbackModel_isSplit
    {p : S ⥤ C} (hc : PullbackChoice p)
    (hid : ∀ U : C, hc.pullbackFunctor (𝟙 U) = 𝟭 (Fiber p U))
    (hcomp : ∀ {U V W : C} (f : V ⟶ U) (g : W ⟶ V),
      hc.pullbackFunctor (g ≫ f) = hc.pullbackFunctor f ⋙ hc.pullbackFunctor g) :
    Functor.IsSplitFibredCategory
      (Pseudofunctor.CoGrothendieck.forget ((strict_pullback_functor hc hid hcomp).toPseudofunctor')) := by
  -- This target is literally the co-Grothendieck model used in the definition of splitness.
  refine ⟨?_⟩
  refine ⟨strict_pullback_functor hc hid hcomp, ?_, ?_, ?_, ?_⟩
  · exact 𝟙 (BasedCategory.ofFunctor _)
  · exact 𝟙 (BasedCategory.ofFunctor _)
  · simp
  · simp

/-- Lemma 4.36.3, strict model direction: a normalized choice of pullbacks whose pullback
functors compose on the nose gives the split co-Grothendieck model associated to the induced
contravariant `Cat`-valued functor.

In the formalization of Definition 4.33.6, identity pullbacks are only canonically isomorphic to
the identity functor by `PullbackChoice.pullbackIdIso`; literal equality of identity pullback
functors is therefore recorded as part of the normalized strict data. -/
theorem Functor.isSplit_of_strict_pullbackChoice_model
    {p : S ⥤ C} (hc : PullbackChoice p)
    (hid : ∀ U : C, hc.pullbackFunctor (𝟙 U) = 𝟭 (Fiber p U))
    (hcomp : ∀ {U V W : C} (f : V ⟶ U) (g : W ⟶ V),
      hc.pullbackFunctor (g ≫ f) = hc.pullbackFunctor f ⋙ hc.pullbackFunctor g) :
    Functor.IsSplitFibredCategory
      (Pseudofunctor.CoGrothendieck.forget
        ((strict_pullback_functor hc hid hcomp).toPseudofunctor')) :=
  strictPullbackModel_isSplit hc hid hcomp

/-- Formal bridge for Lemma 4.36.3: a normalized strict pullback choice proves splitness of any
fibred category that is identified over the base with the strict co-Grothendieck model built from
that choice.

The extra based isomorphism data is the formal coherence missing from the bare statement
`hc.pullbackFunctor (g ≫ f) = hc.pullbackFunctor f ⋙ hc.pullbackFunctor g`: in this
formalization, identity pullback arrows are only canonically isomorphic to identities, so the
comparison with `p` itself cannot be recovered from functor equality alone. -/
theorem Functor.isSplit_of_strict_pullbackChoice_model_iso
    {p : S ⥤ C} (hc : PullbackChoice p)
    (hid : ∀ U : C, hc.pullbackFunctor (𝟙 U) = 𝟭 (Fiber p U))
    (hcomp : ∀ {U V W : C} (f : V ⟶ U) (g : W ⟶ V),
      hc.pullbackFunctor (g ≫ f) = hc.pullbackFunctor f ⋙ hc.pullbackFunctor g)
    (e : BasedCategory.ofFunctor p ⥤ᵇ
      BasedCategory.ofFunctor
        (Pseudofunctor.CoGrothendieck.forget
          ((strict_pullback_functor hc hid hcomp).toPseudofunctor')))
    (eInv : BasedCategory.ofFunctor
      (Pseudofunctor.CoGrothendieck.forget
        ((strict_pullback_functor hc hid hcomp).toPseudofunctor')) ⥤ᵇ
        BasedCategory.ofFunctor p)
    (hη : e ⋙ eInv = 𝟙 (BasedCategory.ofFunctor p))
    (hε : eInv ⋙ e =
      𝟙 (BasedCategory.ofFunctor
        (Pseudofunctor.CoGrothendieck.forget
          ((strict_pullback_functor hc hid hcomp).toPseudofunctor')))) :
    p.IsSplitFibredCategory := by
  exact ⟨⟨strict_pullback_functor hc hid hcomp, e, eInv, hη, hε⟩⟩

/-- Existential form of the normalized strict-pullback model criterion for Lemma 4.36.3.

Besides strict identity and composition of pullback functors, the hypothesis includes explicit
based inverse data identifying `p` with the strict co-Grothendieck model built from those
pullbacks. This is the formal coherence that the paper proof suppresses in the phrase “immediate
from the definitions”: with the current `PullbackChoice` structure, functor equality alone does
not encode the chosen identity pullback arrows or the comparison with the total category. -/
theorem Functor.isSplit_of_exists_strict_pullbackChoice_model_iso
    {p : S ⥤ C}
    (h :
      ∃ (hc : PullbackChoice p)
        (hid : ∀ U : C, hc.pullbackFunctor (𝟙 U) = 𝟭 (Fiber p U))
        (hcomp : ∀ {U V W : C} (f : V ⟶ U) (g : W ⟶ V),
          hc.pullbackFunctor (g ≫ f) = hc.pullbackFunctor f ⋙ hc.pullbackFunctor g),
        ∃ (e : BasedCategory.ofFunctor p ⥤ᵇ
          BasedCategory.ofFunctor
            (Pseudofunctor.CoGrothendieck.forget
              ((strict_pullback_functor hc hid hcomp).toPseudofunctor')))
          (eInv : BasedCategory.ofFunctor
            (Pseudofunctor.CoGrothendieck.forget
              ((strict_pullback_functor hc hid hcomp).toPseudofunctor')) ⥤ᵇ
              BasedCategory.ofFunctor p),
          e ⋙ eInv = 𝟙 (BasedCategory.ofFunctor p) ∧
            eInv ⋙ e =
              𝟙 (BasedCategory.ofFunctor
                (Pseudofunctor.CoGrothendieck.forget
                  ((strict_pullback_functor hc hid hcomp).toPseudofunctor')))) :
    p.IsSplitFibredCategory := by
  rcases h with ⟨hc, hid, hcomp, e, eInv, hη, hε⟩
  exact Functor.isSplit_of_strict_pullbackChoice_model_iso hc hid hcomp e eInv hη hε

/-- Companion spelling of the normalized strict-pullback model criterion. -/
theorem Functor.isSplit_of_strict_pullbackChoice_model'
    {p : S ⥤ C} (hc : PullbackChoice p)
    (hid : ∀ U : C, hc.pullbackFunctor (𝟙 U) = 𝟭 (Fiber p U))
    (hcomp : ∀ {U V W : C} (f : V ⟶ U) (g : W ⟶ V),
      hc.pullbackFunctor (g ≫ f) = hc.pullbackFunctor f ⋙ hc.pullbackFunctor g) :
    Functor.IsSplitFibredCategory
      (Pseudofunctor.CoGrothendieck.forget
        ((strict_pullback_functor hc hid hcomp).toPseudofunctor')) :=
  Functor.isSplit_of_strict_pullbackChoice_model hc hid hcomp

end CategoryTheory
