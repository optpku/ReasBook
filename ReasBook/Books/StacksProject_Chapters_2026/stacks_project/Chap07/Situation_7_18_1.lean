module

public import Mathlib.CategoryTheory.Adjunction.CompositionIso
public import Mathlib.CategoryTheory.Sites.Sheafification
public import Mathlib.CategoryTheory.Sites.Sheaf
public import Mathlib.CategoryTheory.Sites.Finite
public import stacks_project.Chap07.Definition_7_13_1
public import stacks_project.Chap07.Definition_7_14_1
public import stacks_project.Chap07.Lemma_7_17_2

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.GrothendieckTopology
open CategoryTheory.Limits
open CategoryTheory.SemiRepresentableFamily.Over
open Opposite

universe w u v uI uC vC

/-
Domain-style sampling for Situation 7.18.1 (refactored):
- primary domain: cofiltered inverse systems of Stacks sites with finite covering families and
  their stage morphisms of sites;
- sampled owner API:
  `CategoryTheory.Precoverage`,
  `CategoryTheory.Precoverage.HasIsos`,
  `CategoryTheory.Precoverage.HasPullbacks`,
  `CategoryTheory.Precoverage.finite`,
  `CategoryTheory.Functor.IsContinuousSiteFunctor`,
  `CategoryTheory.RepresentablyFlat`,
  `IsMorphismOfSites`;
- source/core/bridge triage:
  `source-facing`: the chosen covering families `Cov(C_i)` of each stage site, their three site
  axioms in the literal Stacks Definition 7.6.2 form, the finiteness of covering index sets, and
  the continuity (Definition 7.13.1) plus exactness data of the transition functors;
  `core/canonical`: `Precoverage` together with `HasIsos`/`HasPullbacks` and the per-arrow
  (`Presieve.bind`) and chosen-pullback (`Presieve.pullbackArrows`) stability axioms below;
  `bridge/view`: the generated stage Grothendieck topologies and the topology-level
  `Functor.IsContinuous`/`IsMorphismOfSites` instances.

Primitive data are the index category, its cofilteredness, the contravariant category diagram,
the chosen stage covering families with the literal Stacks site axioms, the finiteness of those
families, and the transition continuity/flatness. The stage Grothendieck topologies and all
topology-level statements are derived API.

Design note (route correction relative to the previous encoding): the mathlib classes
`Precoverage.IsStableUnderComposition` and `Precoverage.IsStableUnderBaseChange` quantify over
arbitrary index types with repetitions carrying independent inner data, so they are *false* for
any precoverage all of whose coverings are finite. The Stacks axioms (2) and (3) of
Definition 7.6.2 are therefore encoded in `Presieve.bind` and `Presieve.pullbackArrows` form,
which match the source text exactly. Likewise, the previous hypothesis that every presieve
generating a covering sieve is finite forces all hom-sets into an object to be finite (the
maximal sieve generates a covering sieve); finiteness is now imposed only on the chosen
covering families, as in the source.
-/

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]

/-- Stacks Project Definition 7.6.2, axiom (2), stated for a precoverage in per-arrow
(`Presieve.bind`) form: refining each arrow of a covering family by a covering family of its
source yields a covering family. This is the literal transitivity axiom for sites whose covering
families are not closed under arbitrary re-indexing (for example, sites all of whose covering
families are finite). -/
class Precoverage.IsStableUnderBind (J : Precoverage C) : Prop where
  bind_mem ⦃X : C⦄ ⦃R : Presieve X⦄ (hR : R ∈ J X)
      (T : ∀ ⦃Y : C⦄ ⦃f : Y ⟶ X⦄, R f → Presieve Y)
      (hT : ∀ ⦃Y : C⦄ ⦃f : Y ⟶ X⦄ (hf : R f), T hf ∈ J Y) :
      R.bind T ∈ J X

alias Precoverage.bind_mem := Precoverage.IsStableUnderBind.bind_mem

/-- Stacks Project Definition 7.6.2, axiom (3), covering part, stated for the chosen pullbacks:
pulling back a covering family along an arbitrary morphism yields a covering family. The
existence part of axiom (3) is the separate owner `Precoverage.HasPullbacks`. -/
class Precoverage.IsStableUnderPullbackArrows (J : Precoverage C) : Prop where
  pullbackArrows_mem ⦃X V : C⦄ (f : V ⟶ X) ⦃R : Presieve X⦄ (hR : R ∈ J X)
      [R.HasPullbacks f] : R.pullbackArrows f ∈ J V

alias Precoverage.pullbackArrows_mem' := Precoverage.IsStableUnderPullbackArrows.pullbackArrows_mem

/-- Stacks Project Definition 7.6.2, axiom (3), covering part, in choice-free form: pulling a
covering family back along a morphism is possible up to a covering family that factors through
it. This is the `Coverage`-compatibility condition and is the faithful reading of axiom (3) for
sites whose fiber products are only specified up to isomorphism (such as the colimit site of
Lemma 7.18.2). -/
class Precoverage.HasFactoringPullbacks (J : Precoverage C) : Prop where
  exists_factors : ∀ ⦃X Y : C⦄ (f : Y ⟶ X) ⦃S : Presieve X⦄, S ∈ J X →
    ∃ T ∈ J Y, T.FactorsThruAlong S f

alias Precoverage.exists_factors := Precoverage.HasFactoringPullbacks.exists_factors

/-- Chosen covering pullbacks provide factoring pullbacks. -/
instance (J : Precoverage C) [J.HasPullbacks] [J.IsStableUnderPullbackArrows] :
    J.HasFactoringPullbacks where
  exists_factors {X Y} f S hS := by
    haveI : S.HasPullbacks f := J.hasPullbacks_of_mem f hS
    exact ⟨S.pullbackArrows f, Precoverage.pullbackArrows_mem' f hS,
      Presieve.FactorsThruAlong.pullbackArrows f S⟩

/-- Every sieve of the Grothendieck topology generated by a precoverage satisfying the literal
Stacks site axioms contains the sieve generated by a single covering family. This is the
refinement workhorse replacing
`Precoverage.mem_toGrothendieck_iff_of_isStableUnderComposition`, whose hypothesis class is
false for finite-covering sites. -/
theorem Precoverage.exists_mem_generate_le_of_mem_toGrothendieck
    {J : Precoverage C} [J.HasIsos]
    [J.IsStableUnderBind] [J.HasFactoringPullbacks]
    {X : C} {S : Sieve X} (hS : S ∈ J.toGrothendieck X) :
    ∃ R ∈ J X, Sieve.generate R ≤ S := by
  rw [Precoverage.mem_toGrothendieck_iff] at hS
  induction hS with
  | of X R hR =>
    exact ⟨R, hR, le_refl _⟩
  | top X =>
    exact ⟨Presieve.singleton (𝟙 X), Precoverage.mem_coverings_of_isIso _, le_top⟩
  | pullback X S hS Y f ih =>
    obtain ⟨R, hR, hle⟩ := ih
    obtain ⟨T, hT, hfac⟩ := Precoverage.exists_factors f hR
    refine ⟨T, hT, ?_⟩
    rw [Sieve.generate_le_iff]
    intro Z t ht
    obtain ⟨W, q, e, he, hqe⟩ := hfac ht
    -- The factored composite lies in the pulled-back sieve.
    have hSe : S e := hle _ ⟨W, 𝟙 W, e, he, Category.id_comp e⟩
    change S.arrows (t ≫ f)
    rw [← hqe]
    exact S.downward_closed hSe q
  | transitive X S R hS hR ihS ihR =>
    obtain ⟨R₀, hR₀, hle₀⟩ := ihS
    -- Choose one covering refinement of each pulled-back sieve along an arrow of `R₀`.
    have hmem : ∀ ⦃Y : C⦄ ⦃f : Y ⟶ X⦄, R₀ f → S f := fun Y f hf =>
      hle₀ _ ⟨Y, 𝟙 Y, f, hf, Category.id_comp f⟩
    have ih' : ∀ (Y : C) (f : Y ⟶ X), R₀ f →
        ∃ T, T ∈ J Y ∧ Sieve.generate T ≤ R.pullback f := by
      intro Y f hf
      obtain ⟨T, hT, hle⟩ := ihR (hmem hf)
      exact ⟨T, hT, hle⟩
    choose T hT hleT using ih'
    refine ⟨R₀.bind (fun Y f hf => T Y f hf),
      Precoverage.bind_mem hR₀ _ (fun Y f hf => hT Y f hf), ?_⟩
    rw [Sieve.generate_le_iff]
    rintro Z g ⟨Y, t, f, hf, ht, rfl⟩
    -- Each two-step arrow lies in the pulled-back sieve, hence in `R` after composition.
    have : (R.pullback f).arrows t :=
      hleT Y f hf _ ⟨_, 𝟙 _, t, ht, Category.id_comp t⟩
    simpa using this

/-- The coverage induced by a precoverage that satisfies the Stacks pullback axiom: the
existential pullback-compatibility condition of `Coverage` is witnessed by the chosen pullback
families. -/
def Precoverage.toCoverageOfIsStableUnderPullbackArrows (J : Precoverage C)
    [J.HasFactoringPullbacks] : Coverage C where
  toPrecoverage := J
  pullback _X _Y f S hS := Precoverage.exists_factors f hS

/-- The coverage induced by a Stacks-axioms precoverage generates the same Grothendieck topology
as the precoverage itself. -/
theorem Precoverage.toCoverageOfIsStableUnderPullbackArrows_toGrothendieck
    (J : Precoverage C) [J.HasFactoringPullbacks] :
    (J.toCoverageOfIsStableUnderPullbackArrows).toGrothendieck = J.toGrothendieck :=
  GrothendieckTopology.copy_eq

/-- For a precoverage satisfying the Stacks site axioms, a presheaf of types is a sheaf for the
generated Grothendieck topology if and only if it satisfies the sheaf condition for every chosen
covering family. -/
theorem Precoverage.isSheaf_toGrothendieck_iff_of_isStableUnderPullbackArrows
    (J : Precoverage C) [J.HasFactoringPullbacks]
    (P : Cᵒᵖ ⥤ Type w) :
    Presieve.IsSheaf J.toGrothendieck P ↔
      ∀ {X : C} (R : Presieve X), R ∈ J X → Presieve.IsSheafFor P R := by
  rw [← Precoverage.toCoverageOfIsStableUnderPullbackArrows_toGrothendieck J,
    Presieve.isSheaf_coverage]
  exact Iff.rfl

variable {D : Type uC} [Category.{vC} D]

/-- A functor that is continuous in the Stacks Project sense (Definition 7.13.1) between sites
satisfying the literal Stacks site axioms is continuous for the generated Grothendieck
topologies. This replaces `Functor.isContinuous_toGrothendieck_of_pullbacksPreservedBy`, whose
`IsStableUnderBaseChange` hypotheses fail for finite-covering sites. -/
theorem Functor.isContinuous_toGrothendieck_of_isContinuousSiteFunctor
    (u : C ⥤ D) (J : Precoverage C) (K : Precoverage D)
    [J.HasPullbacks] [J.HasFactoringPullbacks] [K.HasFactoringPullbacks]
    [h : u.IsContinuousSiteFunctor J K] :
    Functor.IsContinuous u J.toGrothendieck K.toGrothendieck := by
  constructor
  intro G
  have hG : Presieve.IsSheaf K.toGrothendieck G.obj := by
    have := G.property
    rwa [isSheaf_iff_isSheaf_of_type] at this
  rw [Precoverage.isSheaf_toGrothendieck_iff_of_isStableUnderPullbackArrows]
  intro X R hR
  haveI : R.HasPairwisePullbacks := J.hasPairwisePullbacks_of_mem hR
  haveI : u.PreservesPairwisePullbacks R := by
    refine ⟨fun Y Z f g hf hg => ?_⟩
    haveI : HasPullback f g := Presieve.HasPairwisePullbacks.has_pullbacks hf hg
    exact h.preservesPullback hR hg f
  rw [Presieve.IsSheafFor.comp_iff_of_preservesPairwisePullbacks]
  exact (Precoverage.isSheaf_toGrothendieck_iff_of_isStableUnderPullbackArrows K G.obj).1 hG _
    (h.toLeComap _ hR)

end CategoryTheory

/-- A precoverage all of whose covering families are finite and which satisfies the literal
Stacks site axioms generates a Grothendieck topology with the finite-refinement property on
every object. This is the corrected bridge from the source-facing finite-covering hypothesis to
the downstream owner used later in the chapter. -/
theorem GrothendieckTopology.hasFiniteRefinementProperty_of_covering_mem_finite
    {C : Type uC} [Category.{vC} C] {J : Precoverage C}
    [J.HasIsos] [J.IsStableUnderBind] [J.HasFactoringPullbacks]
    (hfinite :
      ∀ ⦃U : C⦄ ⦃R : Presieve U⦄,
        R ∈ J U → R ∈ Precoverage.finite C U)
    (U : C) :
    HasFiniteRefinementProperty J.toGrothendieck U := by
  refine { finite_refinement := fun S hS ↦ ?_ }
  obtain ⟨R, hR, hle⟩ := Precoverage.exists_mem_generate_le_of_mem_toGrothendieck hS
  have hRfinite : R.uncurry.Finite :=
    (Precoverage.mem_finite_iff.1 (hfinite hR))
  let 𝒱 : SemiRepresentableFamily.Over U :=
    ofArrows
      (fun i : R.uncurry ↦ i.1.1)
      (fun i : R.uncurry ↦ i.1.2)
  -- The family indexed by `R.uncurry` presents the chosen covering family and hence its sieve.
  have h𝒱toPresieve : 𝒱.toPresieve = R := by
    simpa [𝒱, toPresieve] using presieve_of_uncurry_eq R
  have h𝒱toSieve : 𝒱.toSieve = Sieve.generate R := by
    simpa [toSieve] using congrArg Sieve.generate h𝒱toPresieve
  have h𝒱 : 𝒱.toSieve ∈ J.toGrothendieck U := by
    rw [h𝒱toSieve]
    exact Precoverage.generate_mem_toGrothendieck hR
  refine ⟨𝒱, hRfinite.to_subtype, h𝒱, ?_⟩
  rw [h𝒱toSieve]
  exact hle

/-- Situation 7.18.1: a cofiltered inverse system of sites, encoded by a contravariant diagram of
the underlying categories together with, on each stage, the chosen covering families of a site in
the literal sense of Definition 7.6.2 whose coverings all have finite index sets, and whose
transition functors are continuous (Definition 7.13.1) with representably flat (exact inverse
image, Definition 7.14.1) site morphisms. -/
structure CofilteredSiteDiagram.{uI', uC', vC'} where
  /-- The cofiltered index category `\mathcal I`. -/
  I : Type uI'
  /-- The category structure on the index category. -/
  [smallCategoryI : SmallCategory I]
  /-- The cofilteredness hypothesis on the index category. -/
  [cofilteredI : IsCofiltered I]
  /-- The contravariant diagram of underlying categories `i ↦ \mathcal C_i`. -/
  diagram : Iᵒᵖ ⥤ Cat.{vC', uC'}
  /-- The chosen covering families `\text{Cov}(\mathcal C_i)` of the stage site. -/
  stageCov (i : I) : Precoverage (diagram.obj (op i))
  /-- Every chosen covering family of each stage site is finite (Situation 7.18.1). -/
  stageCov_finite {i : I} ⦃X : diagram.obj (op i)⦄ ⦃R : Presieve X⦄ :
      R ∈ stageCov i X → R ∈ Precoverage.finite (diagram.obj (op i)) X
  /-- Stage site axiom (1) of Definition 7.6.2: singleton isomorphisms are coverings. -/
  stageCov_hasIsos (i : I) : (stageCov i).HasIsos
  /-- Stage site axiom (3) of Definition 7.6.2, existence part: covering members admit pullbacks
  along arbitrary morphisms. -/
  stageCov_hasPullbacks (i : I) : (stageCov i).HasPullbacks
  /-- Stage site axiom (2) of Definition 7.6.2 in per-arrow form. -/
  stageCov_isStableUnderBind (i : I) : (stageCov i).IsStableUnderBind
  /-- Stage site axiom (3) of Definition 7.6.2, covering part. -/
  stageCov_isStableUnderPullbackArrows (i : I) : (stageCov i).IsStableUnderPullbackArrows
  /-- Each transition functor `u_a : \mathcal C_i \to \mathcal C_j` is continuous in the Stacks
  Project sense (Definition 7.13.1) on the chosen covering families. -/
  transition_isContinuousSiteFunctor {i j : I} (a : j ⟶ i) :
      Functor.IsContinuousSiteFunctor (diagram.map a.op).toFunctor (stageCov i) (stageCov j)
  /-- Each transition functor has exact inverse image on sheaves, encoded through the canonical
  mathlib owner `RepresentablyFlat` as in Definition 7.14.1. -/
  transition_representablyFlat {i j : I} (a : j ⟶ i) :
      RepresentablyFlat (diagram.map a.op).toFunctor

/-- The index type of a cofiltered site diagram carries its stored small-category structure. -/
instance (S : CofilteredSiteDiagram.{uI, uC, vC}) : SmallCategory S.I :=
  S.smallCategoryI

/-- The index category of a cofiltered site diagram is cofiltered by the stored primitive data. -/
instance (S : CofilteredSiteDiagram.{uI, uC, vC}) : IsCofiltered S.I :=
  S.cofilteredI

namespace CofilteredSiteDiagram

variable (S : CofilteredSiteDiagram.{uI, uC, vC})

/-- The stage category `\mathcal C_i` of the inverse system. This is a short owner-level name for
the repeatedly used object of the underlying `Cat`-valued diagram. -/
abbrev stage (i : S.I) := S.diagram.obj (op i)

/-- The stage category `\mathcal C_i` carries its canonical category structure from the
`Cat`-valued inverse-system diagram. -/
instance stageCategory (i : S.I) : Category (S.stage i) := inferInstance

/-- The stage transition functor `u_a : \mathcal C_i \to \mathcal C_j` attached to
`a : j ⟶ i`. This is the owner-level derived map underlying the later pullback functors on
sheaves. -/
abbrev stageFunctor {i j : S.I} (a : j ⟶ i) :
    S.stage i ⥤ S.stage j :=
  (S.diagram.map a.op).toFunctor

/-- The identity transition functor is the identity functor. -/
theorem stageFunctor_id_eq (i : S.I) :
    S.stageFunctor (𝟙 i) = 𝟭 _ :=
  congrArg Cat.Hom.toFunctor (S.diagram.map_id (op i))

/-- Two successive transition functors compose to the transition functor of the composite. -/
theorem stageFunctor_comp_eq {i j k : S.I} (a : j ⟶ i) (b : k ⟶ j) :
    S.stageFunctor (b ≫ a) = S.stageFunctor a ⋙ S.stageFunctor b :=
  congrArg Cat.Hom.toFunctor (S.diagram.map_comp a.op b.op)

instance instStageCovHasIsos (i : S.I) : (S.stageCov i).HasIsos :=
  S.stageCov_hasIsos i

instance instStageCovHasPullbacks (i : S.I) : (S.stageCov i).HasPullbacks :=
  S.stageCov_hasPullbacks i

instance instStageCovIsStableUnderBind (i : S.I) : (S.stageCov i).IsStableUnderBind :=
  S.stageCov_isStableUnderBind i

instance instStageCovIsStableUnderPullbackArrows (i : S.I) :
    (S.stageCov i).IsStableUnderPullbackArrows :=
  S.stageCov_isStableUnderPullbackArrows i

/-- The stage Grothendieck topology generated by the chosen covering families of the stage site.
This was a primitive field in the previous encoding and is now derived API. -/
abbrev stageTopology (i : S.I) : GrothendieckTopology (S.stage i) :=
  (S.stageCov i).toGrothendieck

/-- The source-facing finiteness of stage covering families induces the downstream
finite-refinement owner used later in the chapter. -/
instance stageTopology_hasFiniteRefinementProperty (i : S.I) (X : S.stage i) :
    (S.stageTopology i).HasFiniteRefinementProperty X :=
  GrothendieckTopology.hasFiniteRefinementProperty_of_covering_mem_finite
    (fun _ _ hR => S.stageCov_finite hR) X

/-- The owner-level stage functor inherits the primitive transition continuity data stored in
the situation. -/
instance stageFunctor_isContinuousSiteFunctor {i j : S.I} (a : j ⟶ i) :
    Functor.IsContinuousSiteFunctor (S.stageFunctor a) (S.stageCov i) (S.stageCov j) :=
  S.transition_isContinuousSiteFunctor a

/-- The owner-level stage functor inherits the primitive representable flatness stored in the
situation. -/
instance stageFunctor_representablyFlat {i j : S.I} (a : j ⟶ i) :
    RepresentablyFlat (S.stageFunctor a) :=
  S.transition_representablyFlat a

/-- Every stage transition functor is continuous for the stage Grothendieck topologies. -/
instance stageFunctor_isContinuous {i j : S.I} (a : j ⟶ i) :
    Functor.IsContinuous (S.stageFunctor a) (S.stageTopology i) (S.stageTopology j) :=
  Functor.isContinuous_toGrothendieck_of_isContinuousSiteFunctor
    (S.stageFunctor a) (S.stageCov i) (S.stageCov j)

/-- Every stage transition functor defines a morphism of sites between the generated stage
topologies in the sense of Definition 7.14.1. -/
instance stageFunctor_isMorphismOfSites {i j : S.I} (a : j ⟶ i) :
    IsMorphismOfSites (S.stageTopology i) (S.stageTopology j) (S.stageFunctor a) where
  toIsContinuous := inferInstance
  toRepresentablyFlat := inferInstance

/-- The identity transition pullback is canonically the identity functor on stage sheaves. -/
noncomputable def stageSheafPullbackIdIso
    (A : Type*) [Category A] (i : S.I)
    [HasWeakSheafify (S.stageTopology i) A]
    [∀ F : (S.stage i)ᵒᵖ ⥤ A, (S.stageFunctor (𝟙 i)).op.HasLeftKanExtension F] :
    (S.stageFunctor (𝟙 i)).sheafPullback A (S.stageTopology i) (S.stageTopology i) ≅ 𝟭 _ :=
  let e := eqToIso (stageFunctor_id_eq S i)
  Adjunction.leftAdjointIdIso
    ((S.stageFunctor (𝟙 i)).sheafAdjunctionContinuous A
      (S.stageTopology i) (S.stageTopology i))
    (Functor.sheafPushforwardContinuousId' e A (S.stageTopology i))

/-- Transition pullbacks compose in the canonical way. -/
noncomputable def stageSheafPullbackCompIso
    (A : Type*) [Category A]
    {i j k : S.I} (a : j ⟶ i) (b : k ⟶ j)
    [HasWeakSheafify (S.stageTopology j) A]
    [HasWeakSheafify (S.stageTopology k) A]
    [∀ F : (S.stage i)ᵒᵖ ⥤ A, (S.stageFunctor a).op.HasLeftKanExtension F]
    [∀ F : (S.stage j)ᵒᵖ ⥤ A, (S.stageFunctor b).op.HasLeftKanExtension F]
    [∀ F : (S.stage i)ᵒᵖ ⥤ A, (S.stageFunctor (b ≫ a)).op.HasLeftKanExtension F] :
    (S.stageFunctor a).sheafPullback A (S.stageTopology i) (S.stageTopology j) ⋙
        (S.stageFunctor b).sheafPullback A (S.stageTopology j) (S.stageTopology k) ≅
      (S.stageFunctor (b ≫ a)).sheafPullback A (S.stageTopology i) (S.stageTopology k) :=
  let e := eqToIso (stageFunctor_comp_eq S a b)
  Adjunction.leftAdjointCompIso
    ((S.stageFunctor a).sheafAdjunctionContinuous A
      (S.stageTopology i) (S.stageTopology j))
    ((S.stageFunctor b).sheafAdjunctionContinuous A
      (S.stageTopology j) (S.stageTopology k))
    ((S.stageFunctor (b ≫ a)).sheafAdjunctionContinuous A
      (S.stageTopology i) (S.stageTopology k))
    (Functor.sheafPushforwardContinuousComp' e.symm
      A (S.stageTopology i) (S.stageTopology j) (S.stageTopology k))

/-- For an arrow `a : j ⟶ i`, the object `X ∈ \mathcal C_i` maps to `u_a(X) ∈ \mathcal C_j`. -/
abbrev overImage {i : S.I} (X : S.stage i) (A : (Over i)ᵒᵖ) :
    S.stage A.unop.left :=
  (S.stageFunctor A.unop.hom).obj X

end CofilteredSiteDiagram
