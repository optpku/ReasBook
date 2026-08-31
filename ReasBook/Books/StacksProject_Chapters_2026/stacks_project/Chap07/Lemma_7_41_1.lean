module

public import Mathlib.CategoryTheory.Adjunction.FullyFaithful
public import Mathlib.CategoryTheory.Adjunction.Limits
public import Mathlib.CategoryTheory.Functor.EpiMono
public import Mathlib.CategoryTheory.Functor.ReflectsIso.Basic
public import Mathlib.CategoryTheory.Functor.ReflectsIso.Balanced
public import Mathlib.CategoryTheory.Sites.Whiskering
public import Mathlib.CategoryTheory.UnivLE
public import Mathlib.CategoryTheory.Whiskering
public import Mathlib.CategoryTheory.Limits.Constructions.EpiMono
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Shapes.Pullbacks
public import Mathlib.CategoryTheory.Sites.LocallyBijective
public import Mathlib.CategoryTheory.Sites.CoverLifting
public import Mathlib.CategoryTheory.Sites.LeftExact
public import Mathlib.CategoryTheory.Sites.RegularEpi
public import Mathlib.CategoryTheory.Sites.Adjunction
public import Mathlib.CategoryTheory.Sites.Equivalence
import Mathlib.Tactic.Recall
public import stacks_project.Chap07.Lemma_7_12_4
public import stacks_project.Chap07.Lemma_7_11_2
public import stacks_project.Chap07.Lemma_7_11_3
public import stacks_project.Chap07.Lemma_7_17_6
public import stacks_project.Chap07.Lemma_7_38_3.LargeTypeLocalBijective
public import stacks_project.Chap07.Definition_7_15_1_Topoi
@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open Opposite
open scoped MorphismOfTopoiIn

universe u₁ u₂ v₁ v₂ w

namespace CategoryTheory

namespace MorphismOfTopoiIn

section

variable {C : Type u₁} [Category.{v₁} C]
variable {D : Type u₂} [Category.{v₂} D]
variable {J : GrothendieckTopology C} {K : GrothendieckTopology D}
variable (f : MorphismOfTopoiIn J K)

/-
Domain-style sampling for Lemma 7.41.1:
- primary domain: adjunction criteria for faithful and fully faithful right adjoints, together
  with the chapter's source-facing surjectivity predicate for sheaf morphisms and the standard
  functor classes for preserving and reflecting epis, monos, and isomorphisms;
- sampled owner API:
  `Sheaf.IsLocallySurjective`,
  `Sheaf.isLocallySurjective_iff_epi`,
  `Adjunction.faithful_R_of_epi_counit_app`,
  `Adjunction.counit_isIso_of_R_fully_faithful`,
  `Adjunction.fullyFaithfulROfIsIsoCounit`,
  `Functor.ReflectsMonomorphisms`,
  `Functor.ReflectsEpimorphisms`,
  `Functor.FullyFaithful.reflectsIsomorphisms`;
- source/core/bridge triage:
  `source-facing`: the numbered Stacks surjectivity clauses for a morphism of topoi, expressed
  by `Sheaf.IsLocallySurjective`;
  `core/canonical`: the owner properties on `(f _*)`, the inverse-image functor `f⁻¹`, and the
  counit of `f.adjunction`;
  `bridge/view`: the extra source-level lifting predicate
  `surjectionLiftingAlongInverseImage`.

Primitive data are only the morphism of topoi `f` and its adjunction. Faithfulness, full
faithfulness, and reflection of monos, epis, and isomorphisms are derived owner-level API of
`f _*`, so the declarations below should reuse that notation layer directly rather than rebuild
parallel local interfaces. For the textbook surjectivity clauses, the source-facing owner is
already `Sheaf.IsLocallySurjective`, with `Sheaf.isLocallySurjective_iff_epi` providing the
bridge to categorical `Epi` statements. The only genuinely new source-facing predicate here is
the surjection-lifting condition.
-/

attribute [local instance] Types.instFunLike Types.instConcreteCategory

-- Proof sketch: a fully faithful functor is faithful after forgetting the fullness data.
/- Canonical companion: property (2) implies property (1), so a fully faithful pushforward is
faithful. This is the exact owner theorem `Functor.FullyFaithful.faithful` specialized to
`f _*`. -/
#check (show (f _*).FullyFaithful → (f _*).Faithful from Functor.FullyFaithful.faithful)

-- Proof sketch: if every counit map is surjective, equality of morphisms can be checked after
-- applying `f_*` and then pulling back along the surjective counit map.
/-- Lemma 7.41.1 (1): property (3) implies property (1), so surjective counit maps force `f_*`
to be faithful. -/
theorem counitIsLocallySurjective_implies_pushforwardFaithful
    (h₃ : ∀ ℱ : Sheaf K (Type w), Sheaf.IsLocallySurjective ((f.adjunction.counit).app ℱ)) :
    (f _*).Faithful := by
  -- The source hypothesis promotes each counit component to an epimorphism by the sheaf-specific
  -- local-surjectivity instance.
  letI (ℱ : Sheaf K (Type w)) : Sheaf.IsLocallySurjective ((f.adjunction.counit).app ℱ) := h₃ ℱ
  letI (ℱ : Sheaf K (Type w)) : Epi ((f.adjunction.counit).app ℱ) := by infer_instance
  -- Then apply the canonical adjunction criterion for faithful right adjoints.
  exact f.adjunction.faithful_R_of_epi_counit_app

/-- Owner-level companion to Lemma 7.41.1 (2): epic counit maps force `f_*` to be faithful. -/
theorem counitEpi_implies_pushforwardFaithful
    (h₃ : ∀ ℱ : Sheaf K (Type w), Epi ((f.adjunction.counit).app ℱ)) :
    (f _*).Faithful := by
  letI (ℱ : Sheaf K (Type w)) : Epi ((f.adjunction.counit).app ℱ) := h₃ ℱ
  exact f.adjunction.faithful_R_of_epi_counit_app

-- Proof sketch: an isomorphism is in particular an epimorphism, so this follows from the previous
-- implication.
/-- Lemma 7.41.1 (2): property (7) implies property (1), so an isomorphic counit makes `f_*`
faithful. -/
theorem counitIsIso_implies_pushforwardFaithful
    (h₇ : IsIso f.adjunction.counit) :
    (f _*).Faithful :=
  letI := h₇
  (f.adjunction.fullyFaithfulROfIsIsoCounit).faithful

/- Canonical companion: property (7) implies property (2), so if every counit map is an
isomorphism, then `f_*` is fully faithful. This is the exact canonical adjunction owner theorem
`Adjunction.fullyFaithfulROfIsIsoCounit` applied to `f.adjunction`. -/
recall Adjunction.fullyFaithfulROfIsIsoCounit

-- Proof sketch: every isomorphism is in particular surjective.
/-- Lemma 7.41.1 (3): property (7) implies property (3), so an isomorphic counit is in
particular surjective. -/
theorem counitIsIso_implies_counitIsLocallySurjective
    (h₇ : IsIso f.adjunction.counit) :
    ∀ ℱ : Sheaf K (Type w), Sheaf.IsLocallySurjective ((f.adjunction.counit).app ℱ) := by
  -- Isomorphisms of sheaves are locally surjective on the nose.
  letI := h₇
  intro ℱ
  infer_instance

/-- Owner-level companion to Lemma 7.41.1 (5): an isomorphic counit is in particular
epimorphic. -/
theorem counitIsIso_implies_counitEpi
    (h₇ : IsIso f.adjunction.counit) :
    ∀ ℱ : Sheaf K (Type w), Epi ((f.adjunction.counit).app ℱ) := by
  letI := h₇
  intro ℱ
  infer_instance

-- Proof sketch: transport monomorphism of `f_* φ` across the counit isomorphisms on source and
-- target and conclude that `φ` is monic.
/-- Lemma 7.41.1 (4): property (7) implies property (8), so if every counit map is an
isomorphism, then `f_*` reflects injections. -/
theorem counitIsIso_implies_pushforwardReflectsMonomorphisms
    (h₇ : IsIso f.adjunction.counit) :
    (f _*).ReflectsMonomorphisms := by
  letI : (f _*).Faithful := counitIsIso_implies_pushforwardFaithful f h₇
  infer_instance

-- Proof sketch: exactness of `f⁻¹` and the counit isomorphisms let one descend epimorphy from
-- `f_* φ` to `φ`.
/-- Lemma 7.41.1 (5): property (7) implies property (9), so if every counit map is an
isomorphism, then `f_*` reflects surjections. -/
theorem counitIsIso_implies_pushforwardReflectsEpimorphisms
    (h₇ : IsIso f.adjunction.counit) :
    (f _*).ReflectsEpimorphisms := by
  letI : (f _*).Faithful := counitIsIso_implies_pushforwardFaithful f h₇
  infer_instance

-- Proof sketch: transport an isomorphism of `f_* φ` across the counit isomorphisms and conclude
-- that `φ` itself is an isomorphism.
/-- Lemma 7.41.1 (6): property (7) implies property (10), so if every counit map is an
isomorphism, then `f_*` reflects bijections. -/
theorem counitIsIso_implies_pushforwardReflectsIsomorphisms
    (h₇ : IsIso f.adjunction.counit) :
    (f _*).ReflectsIsomorphisms := by
  letI := h₇
  exact (f.adjunction.fullyFaithfulROfIsIsoCounit).reflectsIsomorphisms

/-- Helper for Lemma 7.41.1: `uliftFunctor` preserves the sheaf condition for type-valued
sheaves on an arbitrary site. -/
instance uliftFunctor_hasSheafCompose_type :
    J.HasSheafCompose
      (CategoryTheory.uliftFunctor.{max u₁ v₁, w} :
        Type w ⥤ Type (max w (max u₁ v₁))) where
  isSheaf P hP := by
    -- Reduce to the concrete type-valued sheaf condition and apply stability under `ULift`.
    rw [isSheaf_iff_isSheaf_of_type]
    exact Presieve.isSheaf_comp_uliftFunctor (J := J)
      ((isSheaf_iff_isSheaf_of_type J P).1 hP)

/-- Helper for Lemma 7.41.1: whiskering a type-valued presheaf morphism by `ULift` does not
change its image sieve. -/
theorem imageSieve_whisker_ulift
    {P Q : Cᵒᵖ ⥤ Type w} (η : P ⟶ Q) {X : C}
    (x : ULift.{max u₁ v₁} (Q.obj (op X))) :
    Presheaf.imageSieve
        (Functor.whiskerRight η
          (CategoryTheory.uliftFunctor.{max u₁ v₁, w} :
            Type w ⥤ Type (max w (max u₁ v₁)))) x =
      Presheaf.imageSieve η x.down := by
  -- `ULift` only repackages sections, so local preimages descend and lift pointwise.
  ext Y g
  constructor
  · rintro ⟨y, hy⟩
    refine ⟨y.down, ?_⟩
    exact congrArg ULift.down hy
  · rintro ⟨y, hy⟩
    refine ⟨ULift.up y, ?_⟩
    change ULift.up (η.app (op Y) y) = ULift.up (Q.map g.op x.down)
    exact congrArg ULift.up hy

/-- Helper for Lemma 7.41.1: local surjectivity of type-valued presheaf maps is preserved by
whiskering with the ambient `ULift` functor. -/
theorem isLocallySurjective_whisker_ulift
    {P Q : Cᵒᵖ ⥤ Type w} (η : P ⟶ Q)
    [Presheaf.IsLocallySurjective J η] :
    Presheaf.IsLocallySurjective J
      (Functor.whiskerRight η
        (CategoryTheory.uliftFunctor.{max u₁ v₁, w} :
          Type w ⥤ Type (max w (max u₁ v₁)))) where
  imageSieve_mem {X} x := by
    -- After identifying the image sieve, use the original local-surjectivity witness unchanged.
    rw [imageSieve_whisker_ulift (η := η) x]
    exact Presheaf.imageSieve_mem J η x.down

/-- Helper for Lemma 7.41.1: local surjectivity of type-valued presheaf maps is reflected by
whiskering with the ambient `ULift` functor. -/
theorem locallySurjective_of_whisker_ulift
    {P Q : Cᵒᵖ ⥤ Type w} (η : P ⟶ Q)
    [Presheaf.IsLocallySurjective J
      (Functor.whiskerRight η
        (CategoryTheory.uliftFunctor.{max u₁ v₁, w} :
          Type w ⥤ Type (max w (max u₁ v₁))))] :
    Presheaf.IsLocallySurjective J η where
  imageSieve_mem {X} x := by
    -- Lift the chosen section to the ambient universe and then descend the covering image sieve.
    let x' :
        (Q ⋙
          (CategoryTheory.uliftFunctor.{max u₁ v₁, w} :
            Type w ⥤ Type (max w (max u₁ v₁)))).obj (op X) := ULift.up x
    have hS :
        Presheaf.imageSieve
            (Functor.whiskerRight η
              (CategoryTheory.uliftFunctor.{max u₁ v₁, w} :
                Type w ⥤ Type (max w (max u₁ v₁)))) x' ∈
          J X := by
      exact Presheaf.imageSieve_mem J
        (Functor.whiskerRight η
          (CategoryTheory.uliftFunctor.{max u₁ v₁, w} :
            Type w ⥤ Type (max w (max u₁ v₁)))) x'
    simpa [imageSieve_whisker_ulift (η := η) x'] using hS

/-- Helper for Lemma 7.41.1: local injectivity of type-valued presheaf maps is reflected by
whiskering with the ambient `ULift` functor. -/
theorem locallyInjective_of_whisker_ulift
    {P Q : Cᵒᵖ ⥤ Type w} (η : P ⟶ Q)
    [Presheaf.IsLocallyInjective J
      (Functor.whiskerRight η
        (CategoryTheory.uliftFunctor.{max u₁ v₁, w} :
          Type w ⥤ Type (max w (max u₁ v₁))))] :
    Presheaf.IsLocallyInjective J η where
  equalizerSieve_mem {X} x y h := by
    -- Lift the equal pair, use local injectivity upstairs, and then descend the equalizer sieve.
    let x' :
        (P ⋙
          (CategoryTheory.uliftFunctor.{max u₁ v₁, w} :
            Type w ⥤ Type (max w (max u₁ v₁)))).obj X := ULift.up x
    let y' :
        (P ⋙
          (CategoryTheory.uliftFunctor.{max u₁ v₁, w} :
            Type w ⥤ Type (max w (max u₁ v₁)))).obj X := ULift.up y
    have h' :
        (Functor.whiskerRight η
          (CategoryTheory.uliftFunctor.{max u₁ v₁, w} :
            Type w ⥤ Type (max w (max u₁ v₁)))).app X x' =
          (Functor.whiskerRight η
            (CategoryTheory.uliftFunctor.{max u₁ v₁, w} :
              Type w ⥤ Type (max w (max u₁ v₁)))).app X y' := by
      change ULift.up (η.app X x) = ULift.up (η.app X y)
      exact congrArg ULift.up h
    let S : Sieve X.unop :=
      Presheaf.equalizerSieve
        (F := P ⋙
          (CategoryTheory.uliftFunctor.{max u₁ v₁, w} :
            Type w ⥤ Type (max w (max u₁ v₁))))
        x' y'
    have hS : S ∈ J X.unop := by
      exact Presheaf.equalizerSieve_mem J
        (Functor.whiskerRight η
          (CategoryTheory.uliftFunctor.{max u₁ v₁, w} :
            Type w ⥤ Type (max w (max u₁ v₁))))
        x' y' h'
    refine J.superset_covering ?_ hS
    intro Y g hg
    change ULift.up ((P.map g.op) x) = ULift.up ((P.map g.op) y) at hg
    exact ULift.up.inj hg

/-- Helper for Lemma 7.41.1: whiskering a type-valued presheaf epimorphism by `ULift`
preserves epimorphy. -/
theorem whisker_ulift_preservesEpimorphisms
    {P Q : Cᵒᵖ ⥤ Type w} (η : P ⟶ Q) [Epi η] :
    Epi
      (Functor.whiskerRight η
        (CategoryTheory.uliftFunctor.{max u₁ v₁, w} :
          Type w ⥤ Type (max w (max u₁ v₁)))) := by
  -- Check epimorphy objectwise, where `ULift` only repackages the chosen preimage.
  refine (CategoryTheory.NatTrans.epi_iff_epi_app _).2 ?_
  intro X
  rw [CategoryTheory.epi_iff_surjective]
  rintro ⟨x⟩
  have hη : Function.Surjective (η.app X) := by
    -- The original epimorphism is already surjective at each object of the source site.
    exact (CategoryTheory.epi_iff_surjective _).1
      ((CategoryTheory.NatTrans.epi_iff_epi_app η).1 inferInstance X)
  rcases hη x with ⟨y, rfl⟩
  exact ⟨ULift.up y, rfl⟩

namespace Sheaf

/-- Helper for Lemma 7.41.1: after raising the value universe to
`max w (max u₁ v₁)`, the standard sheafification API for types is available. -/
instance hasSheafify_ulift_type :
    HasSheafify J (Type (max w (max u₁ v₁))) := by
  -- The larger universe is large enough to index the cover multiequalizers used by sheafification.
  letI : ∀ X : C, Small.{max w (max u₁ v₁), max u₁ v₁} (J.Cover X)ᵒᵖ := by infer_instance
  infer_instance

/-- Helper for Lemma 7.41.1: after whiskering by `ULift`, the stock
`Sheaf.isLocallySurjective_iff_epi` theorem applies in the larger type universe. -/
theorem isLocallySurjective_iff_epi_ulift
    {ℱ 𝒢 : Sheaf J (Type (max w (max u₁ v₁)))} (φ : ℱ ⟶ 𝒢) :
    Sheaf.IsLocallySurjective φ ↔ Epi φ := by
  -- This is exactly the standard large-universe bridge once the local sheafification instance is set.
  simpa using (Sheaf.isLocallySurjective_iff_epi (J := J) (φ := φ))

/-- Helper for Lemma 7.41.1: sheafwise whiskering by the ambient `ULift` functor preserves
monomorphisms. -/
theorem sheafCompose_ulift_preservesMonomorphisms
    {ℱ 𝒢 : Sheaf J (Type w)} (φ : ℱ ⟶ 𝒢) [Mono φ] :
    Mono
      ((sheafCompose J
        (CategoryTheory.uliftFunctor.{max u₁ v₁, w} :
          Type w ⥤ Type (max w (max u₁ v₁)))).map φ) := by
  -- Move to the underlying presheaf morphism, where `sheafToPresheaf` already preserves monos.
  have hUnderlying :
      Mono ((sheafToPresheaf J (Type (max w (max u₁ v₁)))).map
        ((sheafCompose J
          (CategoryTheory.uliftFunctor.{max u₁ v₁, w} :
            Type w ⥤ Type (max w (max u₁ v₁)))).map φ)) := by
    -- After expanding the lifted sheaf morphism, this is just whiskering a monomorphism by
    -- `uliftFunctor`, which preserves monomorphisms pointwise.
    change Mono
      (Functor.whiskerRight ((sheafToPresheaf J (Type w)).map φ)
        (CategoryTheory.uliftFunctor.{max u₁ v₁, w} :
          Type w ⥤ Type (max w (max u₁ v₁))))
    infer_instance
  -- Finally reflect the monomorphism back from the presheaf inclusion.
  exact (sheafToPresheaf J (Type (max w (max u₁ v₁)))).mono_of_mono_map hUnderlying

/-- Helper for Lemma 7.41.1: if the underlying presheaf map is epic, then its `ULift`-whiskered
sheaf map is epic as well. -/
theorem sheafCompose_ulift_epi_of_underlying_presheaf_epi
    {ℱ 𝒢 : Sheaf J (Type w)} (φ : ℱ ⟶ 𝒢)
    (hφ : Epi ((sheafToPresheaf J (Type w)).map φ)) :
    Epi
      ((sheafCompose J
        (CategoryTheory.uliftFunctor.{max u₁ v₁, w} :
          Type w ⥤ Type (max w (max u₁ v₁)))).map φ) := by
  have hUnderlying :
      Epi ((sheafToPresheaf J (Type (max w (max u₁ v₁)))).map
        ((sheafCompose J
          (CategoryTheory.uliftFunctor.{max u₁ v₁, w} :
            Type w ⥤ Type (max w (max u₁ v₁)))).map φ)) := by
    -- After forgetting to presheaves, this is exactly the whiskered `ULift` map.
    change Epi
      (Functor.whiskerRight ((sheafToPresheaf J (Type w)).map φ)
        (CategoryTheory.uliftFunctor.{max u₁ v₁, w} :
          Type w ⥤ Type (max w (max u₁ v₁))))
    letI : Epi ((sheafToPresheaf J (Type w)).map φ) := hφ
    exact whisker_ulift_preservesEpimorphisms
      ((sheafToPresheaf J (Type w)).map φ)
  -- Then reflect epimorphy back from the fully faithful inclusion of sheaves into presheaves.
  exact (sheafToPresheaf J (Type (max w (max u₁ v₁)))).epi_of_epi_map hUnderlying

/-- Helper for Lemma 7.41.1: whiskering a type-valued presheaf map by `ULift` also reflects
epimorphy. -/
theorem whisker_ulift_reflectsEpimorphisms
    {P Q : Cᵒᵖ ⥤ Type w} (η : P ⟶ Q)
    [Epi
      (Functor.whiskerRight η
        (CategoryTheory.uliftFunctor.{max u₁ v₁, w} :
          Type w ⥤ Type (max w (max u₁ v₁))))] :
    Epi η := by
  -- Check epimorphy objectwise and descend chosen `ULift` preimages componentwise.
  refine (CategoryTheory.NatTrans.epi_iff_epi_app _).2 ?_
  intro X
  rw [CategoryTheory.epi_iff_surjective]
  intro x
  have hη :
      Function.Surjective
        ((Functor.whiskerRight η
          (CategoryTheory.uliftFunctor.{max u₁ v₁, w} :
            Type w ⥤ Type (max w (max u₁ v₁)))).app X) := by
    exact (CategoryTheory.epi_iff_surjective _).1
      ((CategoryTheory.NatTrans.epi_iff_epi_app _).1 inferInstance X)
  rcases hη (ULift.up x) with ⟨y, hy⟩
  refine ⟨y.down, ?_⟩
  exact ULift.up.inj hy

/-- Helper for Lemma 7.41.1: whiskering a type-valued presheaf map by `ULift` preserves and
reflects epimorphy. -/
theorem whisker_ulift_epi_iff
    {P Q : Cᵒᵖ ⥤ Type w} (η : P ⟶ Q) :
    Epi
      (Functor.whiskerRight η
        (CategoryTheory.uliftFunctor.{max u₁ v₁, w} :
          Type w ⥤ Type (max w (max u₁ v₁)))) ↔
      Epi η := by
  constructor
  · intro hη
    letI :
        Epi
          (Functor.whiskerRight η
            (CategoryTheory.uliftFunctor.{max u₁ v₁, w} :
              Type w ⥤ Type (max w (max u₁ v₁)))) := hη
    exact whisker_ulift_reflectsEpimorphisms (η := η)
  · intro hη
    letI : Epi η := hη
    exact whisker_ulift_preservesEpimorphisms (η := η)

/-- Helper for Lemma 7.41.1: sheafwise whiskering by the ambient `ULift` functor reflects
epimorphy. -/
theorem sheafCompose_ulift_reflectsEpimorphisms
    {ℱ 𝒢 : Sheaf J (Type w)} (φ : ℱ ⟶ 𝒢)
    [Epi
      ((sheafCompose J
        (CategoryTheory.uliftFunctor.{max u₁ v₁, w} :
          Type w ⥤ Type (max w (max u₁ v₁)))).map φ)] :
    Epi φ := by
  let F :
      Sheaf J (Type w) ⥤ Sheaf J (Type (max w (max u₁ v₁))) :=
    sheafCompose J
      (CategoryTheory.uliftFunctor.{max u₁ v₁, w} :
        Type w ⥤ Type (max w (max u₁ v₁)))
  -- Move the upstairs epimorphism to the large-universe local-surjectivity criterion and descend
  -- it back along the `ULift` whiskering equivalence.
  have hUpSurj : Sheaf.IsLocallySurjective (F.map φ) :=
    (isLocallySurjective_iff_epi_ulift (J := J) (φ := F.map φ)).2 inferInstance
  have hUpPresheaf :
      Presheaf.IsLocallySurjective J
        (Functor.whiskerRight ((sheafToPresheaf J (Type w)).map φ)
          (CategoryTheory.uliftFunctor.{max u₁ v₁, w} :
            Type w ⥤ Type (max w (max u₁ v₁)))) := by
    simpa [Sheaf.isLocallySurjective_sheafToPresheaf_map_iff] using hUpSurj
  letI :
      Presheaf.IsLocallySurjective J
        (Functor.whiskerRight ((sheafToPresheaf J (Type w)).map φ)
          (CategoryTheory.uliftFunctor.{max u₁ v₁, w} :
            Type w ⥤ Type (max w (max u₁ v₁)))) := hUpPresheaf
  have hDownSurj : Sheaf.IsLocallySurjective φ := by
    simpa [Sheaf.isLocallySurjective_sheafToPresheaf_map_iff] using
      (locallySurjective_of_whisker_ulift
        (J := J) (η := (sheafToPresheaf J (Type w)).map φ) :
        Presheaf.IsLocallySurjective J ((sheafToPresheaf J (Type w)).map φ))
  letI : Sheaf.IsLocallySurjective φ := hDownSurj
  infer_instance

/-- Helper for Lemma 7.41.1: once the `ULift`-whiskered sheaf map is known to be both mono and
epi, the remaining ambient isomorphism statement is obtained by balancedness upstairs and
reflection downstairs. -/
theorem isIso_of_ulift_mono_epi
    {ℱ 𝒢 : Sheaf J (Type w)} (φ : ℱ ⟶ 𝒢)
    [Mono
      ((sheafCompose J
        (CategoryTheory.uliftFunctor.{max u₁ v₁, w} :
          Type w ⥤ Type (max w (max u₁ v₁)))).map φ)]
    [Epi
      ((sheafCompose J
        (CategoryTheory.uliftFunctor.{max u₁ v₁, w} :
          Type w ⥤ Type (max w (max u₁ v₁)))).map φ)] :
    IsIso φ := by
  let F :
      Sheaf J (Type w) ⥤ Sheaf J (Type (max w (max u₁ v₁))) :=
    sheafCompose J
      (CategoryTheory.uliftFunctor.{max u₁ v₁, w} :
        Type w ⥤ Type (max w (max u₁ v₁)))
  -- The upstairs sheaf category is balanced, so the mapped morphism is invertible there.
  have hIso_up : IsIso (F.map φ) := by
    exact isIso_of_mono_of_epi (F.map φ)
  -- Then reflect that isomorphism back along the faithful `ULift` whiskering functor.
  exact (isIso_iff_of_reflects_iso (f := φ) (F := F)).1 hIso_up

/-- Helper for Lemma 7.41.1: a monomorphism identifies its source with its image sheaf. -/
theorem toImage_isIso_of_mono
    {ℱ 𝒢 : Sheaf J (Type w)} (φ : ℱ ⟶ 𝒢) [Mono φ] :
    IsIso (Sheaf.toImage φ) := by
  let F :
      Sheaf J (Type w) ⥤ Sheaf J (Type (max w (max u₁ v₁))) :=
    sheafCompose J
      (CategoryTheory.uliftFunctor.{max u₁ v₁, w} :
        Type w ⥤ Type (max w (max u₁ v₁)))
  have hMono_toImage : Mono (Sheaf.toImage φ) := by
    -- Cancel the image inclusion against the factorization `toImage ≫ imageι = φ`.
    refine ⟨?_⟩
    intro Z g h hEq
    exact (cancel_mono φ).1 <| by
      simpa [Category.assoc, Sheaf.toImage_ι] using congrArg (fun k ↦ k ≫ Sheaf.imageι φ) hEq
  letI : Mono (Sheaf.toImage φ) := hMono_toImage
  have hMono_up : Mono (F.map (Sheaf.toImage φ)) := by
    exact sheafCompose_ulift_preservesMonomorphisms (J := J) (φ := Sheaf.toImage φ)
  have hSurj_up : Sheaf.IsLocallySurjective (F.map (Sheaf.toImage φ)) := by
    -- `toImage` is locally surjective already, and whiskering its underlying map by `ULift`
    -- preserves that presheaf-level witness.
    rw [← Sheaf.isLocallySurjective_sheafToPresheaf_map_iff]
    change Presheaf.IsLocallySurjective J
      (Functor.whiskerRight ((sheafToPresheaf J (Type w)).map (Sheaf.toImage φ))
        (CategoryTheory.uliftFunctor.{max u₁ v₁, w} :
          Type w ⥤ Type (max w (max u₁ v₁))))
    letI : Presheaf.IsLocallySurjective J
        ((sheafToPresheaf J (Type w)).map (Sheaf.toImage φ)) := by
      simpa [Sheaf.isLocallySurjective_sheafToPresheaf_map_iff] using
        (inferInstance : Sheaf.IsLocallySurjective (Sheaf.toImage φ))
    exact isLocallySurjective_whisker_ulift
      (J := J) (η := (sheafToPresheaf J (Type w)).map (Sheaf.toImage φ))
  have hEpi_up : Epi (F.map (Sheaf.toImage φ)) := by
    exact (isLocallySurjective_iff_epi_ulift (J := J) (φ := F.map (Sheaf.toImage φ))).1 hSurj_up
  letI : Mono (F.map (Sheaf.toImage φ)) := hMono_up
  letI : Epi (F.map (Sheaf.toImage φ)) := hEpi_up
  have hIso_up : IsIso (F.map (Sheaf.toImage φ)) := by
    -- Upstairs the sheaf category is balanced, so mono plus epi implies isomorphism.
    exact isIso_of_mono_of_epi (F.map (Sheaf.toImage φ))
  -- Reflect the upstairs isomorphism back along the faithful `ULift` whiskering functor.
  exact (isIso_iff_of_reflects_iso (f := Sheaf.toImage φ) (F := F)).1 hIso_up

/-- Helper for Lemma 7.41.1: an epimorphism factors through an epic image inclusion. -/
theorem image_inclusion_epi_of_epi
    {ℱ 𝒢 : Sheaf J (Type w)} (φ : ℱ ⟶ 𝒢) [Epi φ] :
    Epi (Sheaf.imageι φ) := by
  -- The image inclusion is the second factor in the canonical image factorization of `φ`.
  exact epi_of_epi_fac (Sheaf.toImage_ι φ)

/-- Helper for Lemma 7.41.1: membership in the `ULift`-whiskered image sieve is exactly
factorization of the corresponding restricted section through the lifted sheaf morphism. -/
theorem ulift_whiskered_imageSieve_iff_factorization
    {ℱ 𝒢 : Sheaf J (Type w)} (φ : ℱ ⟶ 𝒢) {U V : C}
    (x :
      ((sheafCompose J
        (CategoryTheory.uliftFunctor.{max u₁ v₁, w} :
          Type w ⥤ Type (max w (max u₁ v₁)))).obj 𝒢).obj.obj (op U))
    (g : V ⟶ U) :
    Presheaf.imageSieve
        (Functor.whiskerRight ((sheafToPresheaf J (Type w)).map φ)
          (CategoryTheory.uliftFunctor.{max u₁ v₁, w} :
            Type w ⥤ Type (max w (max u₁ v₁)))) x g ↔
      ∃ β :
          J.uliftSheafifiedRepresentable V ⟶
            (sheafCompose J
              (CategoryTheory.uliftFunctor.{max u₁ v₁, w} :
                Type w ⥤ Type (max w (max u₁ v₁)))).obj ℱ,
        β ≫
            (sheafCompose J
              (CategoryTheory.uliftFunctor.{max u₁ v₁, w} :
                Type w ⥤ Type (max w (max u₁ v₁)))).map φ =
          (J.uliftSheafifiedRepresentableFunctor).map g ≫
            (J.uliftSheafifiedRepresentableHomEquiv
              ((sheafCompose J
                (CategoryTheory.uliftFunctor.{max u₁ v₁, w} :
                  Type w ⥤ Type (max w (max u₁ v₁)))).obj 𝒢) U).symm x := by
  let F :
      Sheaf J (Type w) ⥤ Sheaf J (Type (max w (max u₁ v₁))) :=
    sheafCompose J
      (CategoryTheory.uliftFunctor.{max u₁ v₁, w} :
        Type w ⥤ Type (max w (max u₁ v₁)))
  let α : J.uliftSheafifiedRepresentable U ⟶ F.obj 𝒢 :=
    (J.uliftSheafifiedRepresentableHomEquiv (F.obj 𝒢) U).symm x
  -- Route correction: first rewrite sieve membership as an upstairs section equation, then use
  -- the sheafified-representable section equivalence to turn that equation into factorization.
  constructor
  · rintro ⟨y, hy⟩
    let β : J.uliftSheafifiedRepresentable V ⟶ F.obj ℱ :=
      (J.uliftSheafifiedRepresentableHomEquiv (F.obj ℱ) V).symm y
    refine ⟨β, ?_⟩
    -- Compare both sides after evaluating them as sections over `V`.
    apply (J.uliftSheafifiedRepresentableHomEquiv (F.obj 𝒢) V).injective
    calc
      J.uliftSheafifiedRepresentableHomEquiv (F.obj 𝒢) V (β ≫ F.map φ) =
        (F.map φ).hom.app (op V)
          (J.uliftSheafifiedRepresentableHomEquiv (F.obj ℱ) V β) := by
            simpa using J.uliftSheafifiedRepresentableHomEquiv_comp β (F.map φ)
      _ = (F.map φ).hom.app (op V) y := by
            rw [(J.uliftSheafifiedRepresentableHomEquiv (F.obj ℱ) V).apply_symm_apply]
      _ = (F.obj 𝒢).obj.map g.op x := hy
      _ = (F.obj 𝒢).obj.map g.op
            (J.uliftSheafifiedRepresentableHomEquiv (F.obj 𝒢) U α) := by
            rw [(J.uliftSheafifiedRepresentableHomEquiv (F.obj 𝒢) U).apply_symm_apply x]
      _ = J.uliftSheafifiedRepresentableHomEquiv (F.obj 𝒢) V
            ((J.uliftSheafifiedRepresentableFunctor).map g ≫ α) := by
            symm
            simpa [F, GrothendieckTopology.uliftSheafifiedRepresentableFunctor] using
              (J.uliftSheafifiedRepresentableHomEquiv_naturality g (F.obj 𝒢) α)
  · rintro ⟨β, hβ⟩
    have hβ' : β ≫ F.map φ = (J.uliftSheafifiedRepresentableFunctor).map g ≫ α := by
      simpa [F, α] using hβ
    refine ⟨J.uliftSheafifiedRepresentableHomEquiv (F.obj ℱ) V β, ?_⟩
    -- Evaluate the factorization equality at `V` and read it back as image-sieve membership.
    calc
      (F.map φ).hom.app (op V)
          (J.uliftSheafifiedRepresentableHomEquiv (F.obj ℱ) V β) =
        J.uliftSheafifiedRepresentableHomEquiv (F.obj 𝒢) V (β ≫ F.map φ) := by
          symm
          simpa using J.uliftSheafifiedRepresentableHomEquiv_comp β (F.map φ)
      _ = J.uliftSheafifiedRepresentableHomEquiv (F.obj 𝒢) V
            ((J.uliftSheafifiedRepresentableFunctor).map g ≫ α) := by
            simpa [hβ']
      _ = (F.obj 𝒢).obj.map g.op
            (J.uliftSheafifiedRepresentableHomEquiv (F.obj 𝒢) U α) := by
            simpa [F, GrothendieckTopology.uliftSheafifiedRepresentableFunctor] using
              (J.uliftSheafifiedRepresentableHomEquiv_naturality g (F.obj 𝒢) α)
      _ = (F.obj 𝒢).obj.map g.op x := by
            rw [(J.uliftSheafifiedRepresentableHomEquiv (F.obj 𝒢) U).apply_symm_apply x]

/-- Helper for Lemma 7.41.1: local surjectivity in the ambient universe still implies
epimorphy after lifting to the large `ULift` universe and reflecting back. -/
theorem epi_of_isLocallySurjective_ambient
    {ℱ 𝒢 : Sheaf J (Type w)} (φ : ℱ ⟶ 𝒢)
    (hφ : Sheaf.IsLocallySurjective φ) :
    Epi φ := by
  let F :
      Sheaf J (Type w) ⥤ Sheaf J (Type (max w (max u₁ v₁))) :=
    sheafCompose J
      (CategoryTheory.uliftFunctor.{max u₁ v₁, w} :
        Type w ⥤ Type (max w (max u₁ v₁)))
  -- First move to presheaves, where the `ULift` transport is already implemented explicitly.
  have hPresheaf :
      Presheaf.IsLocallySurjective J ((sheafToPresheaf J (Type w)).map φ) := by
    simpa [Sheaf.isLocallySurjective_sheafToPresheaf_map_iff] using hφ
  letI :
      Presheaf.IsLocallySurjective J ((sheafToPresheaf J (Type w)).map φ) := hPresheaf
  have hUpPresheaf :
      Presheaf.IsLocallySurjective J
        (Functor.whiskerRight ((sheafToPresheaf J (Type w)).map φ)
          (CategoryTheory.uliftFunctor.{max u₁ v₁, w} :
            Type w ⥤ Type (max w (max u₁ v₁)))) :=
    isLocallySurjective_whisker_ulift
      (J := J) (η := (sheafToPresheaf J (Type w)).map φ)
  have hUpSurj : Sheaf.IsLocallySurjective (F.map φ) := by
    simpa [Sheaf.isLocallySurjective_sheafToPresheaf_map_iff] using hUpPresheaf
  have hUpEpi : Epi (F.map φ) :=
    (isLocallySurjective_iff_epi_ulift (J := J) (φ := F.map φ)).1 hUpSurj
  letI : Epi (F.map φ) := hUpEpi
  -- Then reflect the upstairs epimorphism back along the faithful `ULift` whiskering functor.
  exact sheafCompose_ulift_reflectsEpimorphisms (J := J) (φ := φ)

/-- Helper for Lemma 7.41.1: the image sieve of the `ULift`-lifted sieve inclusion at the
identity section is exactly the original sieve. -/
theorem imageSieve_uliftFunctorInclusion_id
    {U : C} (R : Sieve U) :
    let x : (uliftYoneda.obj.{max w (max u₁ v₁)} U).obj (op U) := ULift.up (𝟙 U)
    Presheaf.imageSieve (Sieve.uliftFunctorInclusion.{max w (max u₁ v₁)} R) x = R := by
  -- Unpack image-sieve membership: a lift of the identity section is exactly an arrow in `R`.
  dsimp
  ext V g
  constructor
  · rintro ⟨y, hy⟩
    have hy' := ULift.up.inj hy
    change y.down.1 = g ≫ 𝟙 U at hy'
    have hy'' : y.down.1 = g := by simpa using hy'
    simpa [hy''] using y.down.2
  · intro hg
    refine ⟨ULift.up ⟨g, hg⟩, ?_⟩
    change ULift.up g = ULift.up (g ≫ 𝟙 U)
    simp

/-- Helper for Lemma 7.41.1: if the sheafified `ULift`-lifted sieve inclusion is epic, then the
original sieve is covering. -/
theorem sieve_mem_of_sheafify_uliftFunctorInclusion_epi
    {U : C} (R : Sieve U)
    (hR :
      Epi
        (J.sheafifyMap
          (Sieve.uliftFunctorInclusion.{max w (max u₁ v₁)} R))) :
    R ∈ J U := by
  let T := Type (max w (max u₁ v₁))
  let P : Cᵒᵖ ⥤ T := Sieve.uliftFunctor.{max w (max u₁ v₁)} R
  let Q : Cᵒᵖ ⥤ T := CategoryTheory.uliftYoneda.obj.{max w (max u₁ v₁)} U
  let f :
      P ⟶ Q :=
    Sieve.uliftFunctorInclusion.{max w (max u₁ v₁)} R
  letI : HasSheafify J T := by
    letI : ∀ X : C, Small.{max w (max u₁ v₁), max u₁ v₁} (J.Cover X)ᵒᵖ := by
      infer_instance
    infer_instance
  have hW : J.W f := by
    let e := plusPlusFunctorIsoSheafification J T
    have hConcrete : Epi ((J.sheafification T).map f) := by
      simpa [f, P, Q, GrothendieckTopology.sheafification_map] using hR
    have hAbstractHom : Epi ((sheafification J T).map f) := by
      have hcomp : Epi (((J.sheafification T).map f) ≫ e.hom.app Q) := by
        letI : Epi ((J.sheafification T).map f) := hConcrete
        infer_instance
      have hnat :
          ((J.sheafification T).map f) ≫ e.hom.app Q =
            e.hom.app P ≫ (sheafification J T).map f := by
        simpa [e] using e.hom.naturality f
      have hcomp' : Epi (e.hom.app P ≫ (sheafification J T).map f) := by
        rw [← hnat]
        exact hcomp
      letI : Epi (e.hom.app P) := by infer_instance
      exact (epi_comp_iff_of_epi (e.hom.app P) ((sheafification J T).map f)).1 hcomp'
    have hSheafEpi : Epi ((presheafToSheaf J T).map f) :=
      (sheafToPresheaf J T).epi_of_epi_map (by
        simpa [CategoryTheory.sheafification, CategoryTheory.sheafifyMap] using hAbstractHom)
    have hSheafMono : Mono ((presheafToSheaf J T).map f) := by infer_instance
    have hSheafIso : IsIso ((presheafToSheaf J T).map f) := by
      letI : Mono ((presheafToSheaf J T).map f) := hSheafMono
      letI : Epi ((presheafToSheaf J T).map f) := hSheafEpi
      exact isIso_of_mono_of_epi ((presheafToSheaf J T).map f)
    exact (J.W_iff f).2 hSheafIso
  exact GrothendieckTopology.covering_of_W_uliftFunctorInclusion (J := J) R (by
    simpa [f] using hW)

/-- Helper for Lemma 7.41.1: after raising values by `ULift`, epimorphisms remain
epimorphisms when the source universe has the standard sheafification bridge. -/
theorem sheafCompose_ulift_epi_of_epi_ambient
    [HasSheafify.{v₁, w, u₁, w + 1} J (Type w)]
    {ℱ 𝒢 : Sheaf J (Type w)} (φ : ℱ ⟶ 𝒢) [Epi φ] :
    Epi
      ((sheafCompose J
        (CategoryTheory.uliftFunctor.{max u₁ v₁, w} :
          Type w ⥤ Type (max w (max u₁ v₁)))).map φ) := by
  let F :
      Sheaf J (Type w) ⥤ Sheaf J (Type (max w (max u₁ v₁))) :=
    sheafCompose J
      (CategoryTheory.uliftFunctor.{max u₁ v₁, w} :
        Type w ⥤ Type (max w (max u₁ v₁)))
  have hSurj : Sheaf.IsLocallySurjective φ := by
    exact (Sheaf.isLocallySurjective_iff_epi (J := J) (φ := φ)).2 inferInstance
  have hUpPresheaf :
      Presheaf.IsLocallySurjective J
        (Functor.whiskerRight ((sheafToPresheaf J (Type w)).map φ)
          (CategoryTheory.uliftFunctor.{max u₁ v₁, w} :
            Type w ⥤ Type (max w (max u₁ v₁)))) := by
    letI : Presheaf.IsLocallySurjective J ((sheafToPresheaf J (Type w)).map φ) := by
      -- Forget to presheaves before whiskering the local-surjectivity witness by `ULift`.
      simpa [Sheaf.isLocallySurjective_sheafToPresheaf_map_iff] using hSurj
    exact isLocallySurjective_whisker_ulift
      (J := J) (η := (sheafToPresheaf J (Type w)).map φ)
  have hUpSurj : Sheaf.IsLocallySurjective (F.map φ) := by
    -- The lifted sheaf map is locally surjective because its underlying presheaf map is.
    simpa [Sheaf.isLocallySurjective_sheafToPresheaf_map_iff] using hUpPresheaf
  exact (isLocallySurjective_iff_epi_ulift (J := J) (φ := F.map φ)).1 hUpSurj

/-- Helper for Lemma 7.41.1: once the `ULift`-whiskered sheaf map is epic, the rest of the
ambient image-inclusion proof is a direct descent of local surjectivity. -/
theorem image_inclusion_isIso_of_ulift_epi
    {ℱ 𝒢 : Sheaf J (Type w)} (φ : ℱ ⟶ 𝒢)
    (hUp :
      Epi
        ((sheafCompose J
          (CategoryTheory.uliftFunctor.{max u₁ v₁, w} :
            Type w ⥤ Type (max w (max u₁ v₁)))).map φ)) :
    IsIso (Sheaf.imageι φ) := by
  let F :
      Sheaf J (Type w) ⥤ Sheaf J (Type (max w (max u₁ v₁))) :=
    sheafCompose J
      (CategoryTheory.uliftFunctor.{max u₁ v₁, w} :
        Type w ⥤ Type (max w (max u₁ v₁)))
  letI : Epi (F.map φ) := hUp
  have hUpSurj : Sheaf.IsLocallySurjective (F.map φ) :=
    (isLocallySurjective_iff_epi_ulift (J := J) (φ := F.map φ)).2 inferInstance
  have hUpPresheaf :
      Presheaf.IsLocallySurjective J
        (Functor.whiskerRight ((sheafToPresheaf J (Type w)).map φ)
          (CategoryTheory.uliftFunctor.{max u₁ v₁, w} :
            Type w ⥤ Type (max w (max u₁ v₁)))) := by
    -- Forgetting to presheaves identifies the lifted sheaf map with `ULift` whiskering.
    simpa [Sheaf.isLocallySurjective_sheafToPresheaf_map_iff] using hUpSurj
  letI :
      Presheaf.IsLocallySurjective J
        (Functor.whiskerRight ((sheafToPresheaf J (Type w)).map φ)
          (CategoryTheory.uliftFunctor.{max u₁ v₁, w} :
            Type w ⥤ Type (max w (max u₁ v₁)))) := hUpPresheaf
  have hDownSurj : Sheaf.IsLocallySurjective φ := by
    -- Descend the `ULift`-whiskered local-surjectivity witness componentwise on presheaves.
    simpa [Sheaf.isLocallySurjective_sheafToPresheaf_map_iff] using
      (locallySurjective_of_whisker_ulift
        (J := J) (η := (sheafToPresheaf J (Type w)).map φ) :
        Presheaf.IsLocallySurjective J ((sheafToPresheaf J (Type w)).map φ))
  -- For sheaves of sets, local surjectivity is exactly invertibility of the image inclusion.
  rw [← Sheaf.isLocallySurjective_iff_isIso (f := φ)]
  exact hDownSurj

/-- Helper for Lemma 7.41.1: an epimorphism has image inclusion an isomorphism even in the
ambient universe where `HasSheafify` is not assumed. -/
theorem image_inclusion_isIso_of_epi_ambient
    [HasSheafify.{v₁, w, u₁, w + 1} J (Type w)]
    {ℱ 𝒢 : Sheaf J (Type w)} (φ : ℱ ⟶ 𝒢) [Epi φ] :
    IsIso (Sheaf.imageι φ) := by
  -- Route correction: isolate the only missing ambient step, namely lifting `[Epi φ]` to the
  -- `ULift`-whiskered sheaf map, and reuse the proved descent once that bridge is available.
  exact image_inclusion_isIso_of_ulift_epi (J := J) (φ := φ)
    (sheafCompose_ulift_epi_of_epi_ambient (J := J) (φ := φ))

/-- Helper for Lemma 7.41.1: in the ambient universe, a mono and epi sheaf morphism should be
an isomorphism. -/
theorem isIso_of_mono_of_epi_ambient
    [HasSheafify.{v₁, w, u₁, w + 1} J (Type w)]
    {ℱ 𝒢 : Sheaf J (Type w)} (φ : ℱ ⟶ 𝒢) [Mono φ] [Epi φ] :
    IsIso φ := by
  -- Follow the source factorization: a monomorphism identifies its source with its image, and the
  -- image inclusion is invertible for an epimorphism.
  have hToImage : IsIso (Sheaf.toImage φ) := toImage_isIso_of_mono (J := J) (φ := φ)
  have hImage : IsIso (Sheaf.imageι φ) := image_inclusion_isIso_of_epi_ambient (J := J) (φ := φ)
  rw [← Sheaf.toImage_ι φ]
  infer_instance

/-- Helper for Lemma 7.41.1: on set-valued sheaves, local surjectivity agrees with `Epi`
when the small-universe sheafification bridge is available explicitly. -/
theorem isLocallySurjective_iff_epi_ambient
    [HasSheafify.{v₁, w, u₁, w + 1} J (Type w)]
    {ℱ 𝒢 : Sheaf J (Type w)} (φ : ℱ ⟶ 𝒢) :
    Sheaf.IsLocallySurjective φ ↔ Epi φ := by
  constructor
  · intro hφ
    -- Lift the source local-surjectivity witness upstairs and reflect the resulting epimorphism.
    exact epi_of_isLocallySurjective_ambient (J := J) (φ := φ) hφ
  · intro hφ
    -- Route correction: follow the source image-factorization route. The image inclusion becomes
    -- an isomorphism for an epimorphism, and local surjectivity is exactly that statement.
    letI : Epi φ := hφ
    have hImageIso : IsIso (Sheaf.imageι φ) :=
      image_inclusion_isIso_of_epi_ambient (J := J) (φ := φ)
    rw [Sheaf.isLocallySurjective_iff_isIso]
    exact hImageIso

/-- Helper for Lemma 7.41.1: local surjectivity of set-valued sheaf morphisms is invariant under
whiskering by the ambient `ULift` functor. -/
theorem isLocallySurjective_whisker_ulift_iff
    {ℱ 𝒢 : Sheaf J (Type w)} (φ : ℱ ⟶ 𝒢) :
    Sheaf.IsLocallySurjective
        ((sheafCompose J
          (CategoryTheory.uliftFunctor.{max u₁ v₁, w} :
            Type w ⥤ Type (max w (max u₁ v₁)))).map φ) ↔
      Sheaf.IsLocallySurjective φ := by
  -- Move to underlying presheaves, where the `ULift` transport is transparent.
  rw [← Sheaf.isLocallySurjective_sheafToPresheaf_map_iff,
    ← Sheaf.isLocallySurjective_sheafToPresheaf_map_iff]
  change Presheaf.IsLocallySurjective J
      (Functor.whiskerRight ((sheafToPresheaf J (Type w)).map φ)
        (CategoryTheory.uliftFunctor.{max u₁ v₁, w} :
          Type w ⥤ Type (max w (max u₁ v₁)))) ↔
    _
  constructor
  · intro h
    letI : Presheaf.IsLocallySurjective J
        (Functor.whiskerRight ((sheafToPresheaf J (Type w)).map φ)
          (CategoryTheory.uliftFunctor.{max u₁ v₁, w} :
            Type w ⥤ Type (max w (max u₁ v₁)))) := h
    exact locallySurjective_of_whisker_ulift
      (J := J) (η := (sheafToPresheaf J (Type w)).map φ)
  · intro h
    letI : Presheaf.IsLocallySurjective J ((sheafToPresheaf J (Type w)).map φ) := h
    exact isLocallySurjective_whisker_ulift
      (J := J) (η := (sheafToPresheaf J (Type w)).map φ)

/-- Helper for Lemma 7.41.1: local injectivity of set-valued sheaf morphisms descends from the
ambient `ULift` whiskering. -/
theorem isLocallyInjective_whisker_ulift_of
    {ℱ 𝒢 : Sheaf J (Type w)} (φ : ℱ ⟶ 𝒢)
    (hφ : Sheaf.IsLocallyInjective
      ((sheafCompose J
        (CategoryTheory.uliftFunctor.{max u₁ v₁, w} :
          Type w ⥤ Type (max w (max u₁ v₁)))).map φ)) :
    Sheaf.IsLocallyInjective φ := by
  -- Again descend to presheaves and apply the reflected local-injectivity witness.
  change Presheaf.IsLocallyInjective J
      ((sheafToPresheaf J (Type (max w (max u₁ v₁)))).map
        ((sheafCompose J
          (CategoryTheory.uliftFunctor.{max u₁ v₁, w} :
            Type w ⥤ Type (max w (max u₁ v₁)))).map φ)) at hφ
  change Presheaf.IsLocallyInjective J ((sheafToPresheaf J (Type w)).map φ)
  letI : Presheaf.IsLocallyInjective J
      (Functor.whiskerRight ((sheafToPresheaf J (Type w)).map φ)
        (CategoryTheory.uliftFunctor.{max u₁ v₁, w} :
          Type w ⥤ Type (max w (max u₁ v₁)))) := by
    simpa using hφ
  exact locallyInjective_of_whisker_ulift
    (J := J) (η := (sheafToPresheaf J (Type w)).map φ)

/-- Helper for Lemma 7.41.1: the singleton coproduct desc map built from identity morphisms is an
isomorphism. -/
theorem singleton_sigma_desc_identity_isIso
    {A : Sheaf J (Type w)} :
    IsIso (Limits.Sigma.desc (fun _ : PUnit ↦ 𝟙 A)) := by
  -- The singleton coproduct injection is a two-sided inverse to the desc of identities.
  refine ⟨⟨Limits.Sigma.ι (fun _ : PUnit ↦ A) PUnit.unit, ?_, ?_⟩⟩
  · -- Compare the two endomorphisms after precomposing with the unique coproduct injection.
    apply Limits.Sigma.hom_ext
    intro i
    cases i
    simpa [Category.assoc] using
      congrArg
        (fun t ↦ t ≫ Limits.Sigma.ι (fun _ : PUnit ↦ A) PUnit.unit)
        (Limits.Sigma.ι_desc (fun _ : PUnit ↦ 𝟙 A) PUnit.unit)
  · -- The reverse composite is exactly the standard singleton `Sigma.ι_desc` identity.
    simpa using Limits.Sigma.ι_desc (fun _ : PUnit ↦ 𝟙 A) PUnit.unit

/-- Helper for Lemma 7.41.1: for a singleton source family, local surjectivity of the associated
sigma-desc map is exactly local surjectivity of the unique component. -/
theorem isLocallySurjective_singleton_sigma_desc_iff
    {A Z : Sheaf J (Type w)} (φ : A ⟶ Z) :
    Sheaf.IsLocallySurjective (Limits.Sigma.desc (fun _ : PUnit ↦ φ)) ↔
      Sheaf.IsLocallySurjective φ := by
  let e : (∐ fun _ : PUnit ↦ A) ⟶ A := Limits.Sigma.desc (fun _ : PUnit ↦ 𝟙 A)
  letI : IsIso e := singleton_sigma_desc_identity_isIso (J := J) (A := A)
  have hcomp : e ≫ φ = Limits.Sigma.desc (fun _ : PUnit ↦ φ) := by
    -- Compare the singleton coproduct map componentwise on the unique summand.
    apply Limits.Sigma.hom_ext
    intro i
    cases i
    calc
      Limits.Sigma.ι (fun _ : PUnit ↦ A) PUnit.unit ≫ e ≫ φ
          = (𝟙 A) ≫ φ := by
              simpa [e, Category.assoc] using
                congrArg (fun t ↦ t ≫ φ)
                  (Limits.Sigma.ι_desc (fun _ : PUnit ↦ 𝟙 A) PUnit.unit)
      _ = φ := by simp
      _ = Limits.Sigma.ι (fun _ : PUnit ↦ A) PUnit.unit ≫
            Limits.Sigma.desc (fun _ : PUnit ↦ φ) := by
              simpa [Category.assoc] using
                (Limits.Sigma.ι_desc (fun _ : PUnit ↦ φ) PUnit.unit).symm
  -- Rewrite both source-facing surjectivity clauses as epimorphism statements and transport
  -- across the singleton coproduct equivalence at the underlying presheaf level.
  rw [← Sheaf.isLocallySurjective_sheafToPresheaf_map_iff,
    ← Sheaf.isLocallySurjective_sheafToPresheaf_map_iff]
  have he :
      Presheaf.IsLocallySurjective J ((sheafToPresheaf J (Type w)).map e) := by
    infer_instance
  letI :
      Presheaf.IsLocallySurjective J ((sheafToPresheaf J (Type w)).map e) := he
  have hcomp_hom :
      ((sheafToPresheaf J (Type w)).map e) ≫
          ((sheafToPresheaf J (Type w)).map φ) =
        (sheafToPresheaf J (Type w)).map (Limits.Sigma.desc (fun _ : PUnit ↦ φ)) := by
    simpa using congrArg (fun t ↦ (sheafToPresheaf J (Type w)).map t) hcomp
  rw [← hcomp_hom]
  exact Presheaf.comp_isLocallySurjective_iff J
    ((sheafToPresheaf J (Type w)).map e)
    ((sheafToPresheaf J (Type w)).map φ)

end Sheaf

/-- Helper for Lemma 7.41.1: surjections onto inverse images lift after pulling back along a
locally surjective cover in the target topos. -/
def surjectionLiftingAlongInverseImage : Prop :=
  ∀ {ℱ : Sheaf K (Type w)} {𝒢 : Sheaf J (Type w)} (φ : ℱ ⟶ f⁻¹.obj 𝒢),
    Sheaf.IsLocallySurjective φ →
      ∃ (𝒢' : Sheaf J (Type w)) (π : 𝒢' ⟶ 𝒢),
        Sheaf.IsLocallySurjective π ∧
          ∃ ι : (f⁻¹).obj 𝒢' ⟶ ℱ,
            ι ≫ φ = (f⁻¹).map π

/-- Helper for Lemma 7.41.1: pullbacks of locally surjective morphisms of sheaves of sets are
again locally surjective. -/
theorem sheaf_pullback_snd_isLocallySurjective
    {A B Z : Sheaf J (Type w)} (φ : A ⟶ Z) (q : B ⟶ Z)
    (hφ : Sheaf.IsLocallySurjective φ) :
    Sheaf.IsLocallySurjective (pullback.snd φ q) := by
  let Fsh := sheafToPresheaf J (Type w)
  -- Move to the underlying presheaf pullback, where the textbook local preimage construction is
  -- completely explicit.
  rw [← Sheaf.isLocallySurjective_sheafToPresheaf_map_iff]
  letI : Presheaf.IsLocallySurjective J (Fsh.map φ) := by
    simpa [Sheaf.isLocallySurjective_sheafToPresheaf_map_iff] using hφ
  have hpres_pullback :
      Presheaf.IsLocallySurjective J (pullback.snd (Fsh.map φ) (Fsh.map q)) := by
    refine ⟨?_⟩
    intro X b
    refine J.superset_covering ?_
      (Presheaf.imageSieve_mem J (Fsh.map φ) ((Fsh.map q).app (op X) b))
    intro Y g hg
    rcases hg with ⟨a, ha⟩
    have hqx :
        (Fsh.map φ).app (op Y) a =
          (Fsh.map q).app (op Y) ((Fsh.obj B).map g.op b) := by
      calc
        (Fsh.map φ).app (op Y) a = (Fsh.obj Z).map g.op ((Fsh.map q).app (op X) b) := ha
        _ = (Fsh.map q).app (op Y) ((Fsh.obj B).map g.op b) := by
          symm
          simpa using congrFun ((Fsh.map q).naturality g.op) b
    let t' :
        Types.PullbackObj ((Fsh.map φ).app (op Y)) ((Fsh.map q).app (op Y)) :=
      ⟨⟨a, (Fsh.obj B).map g.op b⟩, hqx⟩
    let t : (pullback (Fsh.map φ) (Fsh.map q)).obj (op Y) :=
      (Limits.pullbackObjIso (Fsh.map φ) (Fsh.map q) (op Y)).inv
        ((Types.pullbackIsoPullback _ _).inv t')
    refine ⟨t, ?_⟩
    -- The second projection of the pullback element is exactly the chosen local section of `B`.
    dsimp [t]
    simpa [t'] using
      congrFun (Limits.pullbackObjIso_inv_comp_snd (Fsh.map φ) (Fsh.map q) (op Y))
        ((Types.pullbackIsoPullback ((Fsh.map φ).app (op Y)) ((Fsh.map q).app (op Y))).inv t')
  let sourceMap : Fsh.obj (pullback φ q) ⟶ pullback (Fsh.map φ) (Fsh.map q) :=
    Limits.pullbackComparison Fsh φ q
  letI : Presheaf.IsLocallySurjective J sourceMap := by
    infer_instance
  have hcomp :
      Presheaf.IsLocallySurjective J
        (sourceMap ≫ pullback.snd (Fsh.map φ) (Fsh.map q)) := by
    exact (Presheaf.comp_isLocallySurjective_iff
      J sourceMap (pullback.snd (Fsh.map φ) (Fsh.map q))).2 hpres_pullback
  have hfac :
      sourceMap ≫ pullback.snd (Fsh.map φ) (Fsh.map q) =
        Fsh.map (pullback.snd φ q) := by
    simpa [sourceMap] using Limits.pullbackComparison_comp_snd Fsh φ q
  -- Transport the presheaf pullback cover back along the pullback-comparison isomorphism.
  exact hfac ▸ hcomp

/-- Helper for Lemma 7.41.1: the pullback of `(f _*).map φ` along the adjunction unit. -/
noncomputable abbrev unit_pullback_cover
    {ℱ : Sheaf K (Type w)} {𝒢 : Sheaf J (Type w)}
    (φ : ℱ ⟶ (f⁻¹).obj 𝒢) : Sheaf J (Type w) :=
  pullback ((f _*).map φ) ((f.adjunction.unit).app 𝒢)

/-- Helper for Lemma 7.41.1: the canonical projection from the unit pullback cover. -/
noncomputable abbrev unit_pullback_cover_projection
    {ℱ : Sheaf K (Type w)} {𝒢 : Sheaf J (Type w)}
    (φ : ℱ ⟶ (f⁻¹).obj 𝒢) :
    unit_pullback_cover (f := f) φ ⟶ 𝒢 :=
  pullback.snd ((f _*).map φ) ((f.adjunction.unit).app 𝒢)

/-- Helper for Lemma 7.41.1: the inverse-image morphism from the unit pullback cover to `ℱ`. -/
noncomputable abbrev inverseImage_unit_pullback_cover_lift
    {ℱ : Sheaf K (Type w)} {𝒢 : Sheaf J (Type w)}
    (φ : ℱ ⟶ (f⁻¹).obj 𝒢)
    [PreservesFiniteLimits (f⁻¹)] :
    (f⁻¹).obj (unit_pullback_cover (f := f) φ) ⟶ ℱ :=
  (PreservesPullback.iso (f⁻¹) ((f _*).map φ) ((f.adjunction.unit).app 𝒢)).hom ≫
    pullback.fst ((f⁻¹).map ((f _*).map φ)) ((f⁻¹).map ((f.adjunction.unit).app 𝒢)) ≫
      (f.adjunction.counit).app ℱ

/-- Helper for Lemma 7.41.1: moving the pullback-cover projection across the adjunction unit
inside the inverse-image functor. -/
theorem inverseImage_unit_naturality_projection
    {ℱ : Sheaf K (Type w)} {𝒢 : Sheaf J (Type w)}
    (φ : ℱ ⟶ (f⁻¹).obj 𝒢) :
    (unit_pullback_cover_projection (f := f) φ) ≫ (f.adjunction.unit).app 𝒢 =
      (f.adjunction.unit).app (unit_pullback_cover (f := f) φ) ≫
        (f _*).map ((f⁻¹).map (unit_pullback_cover_projection (f := f) φ)) := by
  -- This is exactly naturality of the adjunction unit at the pullback-cover projection.
  simpa using
    (f.adjunction.unit_naturality (unit_pullback_cover_projection (f := f) φ)).symm

/-- Helper for Lemma 7.41.1: moving the mapped pullback-cover projection across the adjunction
counit inside the inverse-image functor. -/
theorem inverseImage_counit_naturality_projection
    {ℱ : Sheaf K (Type w)} {𝒢 : Sheaf J (Type w)}
    (φ : ℱ ⟶ (f⁻¹).obj 𝒢) :
    (f⁻¹).map ((f _*).map ((f⁻¹).map (unit_pullback_cover_projection (f := f) φ))) ≫
        (f.adjunction.counit).app ((f⁻¹).obj 𝒢) =
      (f.adjunction.counit).app ((f⁻¹).obj (unit_pullback_cover (f := f) φ)) ≫
        (f⁻¹).map (unit_pullback_cover_projection (f := f) φ) := by
  -- This is naturality of the counit at the mapped pullback-cover projection.
  simpa using
    f.adjunction.counit_naturality
      ((f⁻¹).map (unit_pullback_cover_projection (f := f) φ))

/-- Helper for Lemma 7.41.1: the canonical map from the inverse image of the pullback cover
factors through the pulled-back surjection. -/
theorem inverseImage_pullback_cover_factorization
    {ℱ : Sheaf K (Type w)} {𝒢 : Sheaf J (Type w)}
    (φ : ℱ ⟶ (f⁻¹).obj 𝒢)
    [PreservesFiniteLimits (f⁻¹)] :
    inverseImage_unit_pullback_cover_lift (f := f) φ ≫ φ =
      (f⁻¹).map (unit_pullback_cover_projection (f := f) φ) := by
  -- Route correction: flatten the transport-heavy composite to a directed rewrite chain instead
  -- of asking `calc` to guess the needed associativity bridges.
  dsimp [inverseImage_unit_pullback_cover_lift, unit_pullback_cover_projection]
  -- First move the counit across `φ`, then swap pullback legs, then identify the mapped
  -- projection downstairs.
  have hCounit :
      (PreservesPullback.iso (f⁻¹) ((f _*).map φ) ((f.adjunction.unit).app 𝒢)).hom ≫
            pullback.fst ((f⁻¹).map ((f _*).map φ))
              ((f⁻¹).map ((f.adjunction.unit).app 𝒢)) ≫
          (f.adjunction.counit).app ℱ ≫ φ
        =
      (PreservesPullback.iso (f⁻¹) ((f _*).map φ) ((f.adjunction.unit).app 𝒢)).hom ≫
            pullback.fst ((f⁻¹).map ((f _*).map φ))
              ((f⁻¹).map ((f.adjunction.unit).app 𝒢)) ≫
          (f⁻¹).map ((f _*).map φ) ≫
            (f.adjunction.counit).app ((f⁻¹).obj 𝒢) := by
    -- Rewrite the final leg using counit naturality at `φ`.
    simpa [Category.assoc] using
      congrArg
        (fun k ↦
          (PreservesPullback.iso (f⁻¹) ((f _*).map φ) ((f.adjunction.unit).app 𝒢)).hom ≫
            pullback.fst ((f⁻¹).map ((f _*).map φ))
              ((f⁻¹).map ((f.adjunction.unit).app 𝒢)) ≫
            k)
        (f.adjunction.counit_naturality φ).symm
  have hPullback :
      (PreservesPullback.iso (f⁻¹) ((f _*).map φ) ((f.adjunction.unit).app 𝒢)).hom ≫
            pullback.fst ((f⁻¹).map ((f _*).map φ))
              ((f⁻¹).map ((f.adjunction.unit).app 𝒢)) ≫
          (f⁻¹).map ((f _*).map φ) ≫
            (f.adjunction.counit).app ((f⁻¹).obj 𝒢)
        =
      (PreservesPullback.iso (f⁻¹) ((f _*).map φ) ((f.adjunction.unit).app 𝒢)).hom ≫
            pullback.snd ((f⁻¹).map ((f _*).map φ))
              ((f⁻¹).map ((f.adjunction.unit).app 𝒢)) ≫
          (f⁻¹).map ((f.adjunction.unit).app 𝒢) ≫
            (f.adjunction.counit).app ((f⁻¹).obj 𝒢) := by
    -- The pullback relation swaps the first leg for the second.
    rw [pullback.condition_assoc]
    rfl
  have hTriangle :
      (PreservesPullback.iso (f⁻¹) ((f _*).map φ) ((f.adjunction.unit).app 𝒢)).hom ≫
            pullback.snd ((f⁻¹).map ((f _*).map φ))
              ((f⁻¹).map ((f.adjunction.unit).app 𝒢)) ≫
          (f⁻¹).map ((f.adjunction.unit).app 𝒢) ≫
            (f.adjunction.counit).app ((f⁻¹).obj 𝒢)
        =
      (f⁻¹).map (pullback.snd ((f _*).map φ) ((f.adjunction.unit).app 𝒢)) := by
    -- Identify the preserved-pullback projection with the mapped projection downstairs, then
    -- contract the unit-counit zig-zag by the basic right triangle identity.
    rw [PreservesPullback.iso_hom_snd_assoc]
    simpa [Category.assoc] using
      congrArg
        (fun k ↦
          (f⁻¹).map (pullback.snd ((f _*).map φ) ((f.adjunction.unit).app 𝒢)) ≫
            k)
        (f.adjunction.right_triangle_components 𝒢)
  exact hCounit.trans (hPullback.trans hTriangle)

/-- Helper for Lemma 7.41.1: if `f_*` maps locally surjective morphisms to locally surjective
morphisms, then covers of inverse images lift after a locally surjective cover upstairs. -/
theorem pullback_cover_lift_data
    (h₄ : ∀ {ℱ 𝒢 : Sheaf K (Type w)} (φ : ℱ ⟶ 𝒢),
      Sheaf.IsLocallySurjective φ →
        Sheaf.IsLocallySurjective ((f _*).map φ))
    {ℱ : Sheaf K (Type w)} {𝒢 : Sheaf J (Type w)}
    (φ : ℱ ⟶ (f⁻¹).obj 𝒢)
    (hφ : Sheaf.IsLocallySurjective φ) :
    ∃ (𝒢' : Sheaf J (Type w)) (π : 𝒢' ⟶ 𝒢),
      Sheaf.IsLocallySurjective π ∧
        ∃ ι : (f⁻¹).obj 𝒢' ⟶ ℱ,
          ι ≫ φ = (f⁻¹).map π := by
  let ψ : (f _*).obj ℱ ⟶ (f _*).obj ((f⁻¹).obj 𝒢) := (f _*).map φ
  let 𝒢' : Sheaf J (Type w) := unit_pullback_cover (f := f) φ
  let π : 𝒢' ⟶ 𝒢 := unit_pullback_cover_projection (f := f) φ
  have hψ : Sheaf.IsLocallySurjective ψ := h₄ φ hφ
  letI : PreservesFiniteLimits (f⁻¹) := by
    simpa using MorphismOfTopoiIn.inverseImage_preservesFiniteLimits f
  have hπ : Sheaf.IsLocallySurjective π := by
    -- Pull back the mapped cover along the unit to build the lifted cover of `𝒢`.
    change Sheaf.IsLocallySurjective (pullback.snd ψ ((f.adjunction.unit).app 𝒢))
    simpa [ψ, unit_pullback_cover, unit_pullback_cover_projection] using
      sheaf_pullback_snd_isLocallySurjective
        (J := J) ψ ((f.adjunction.unit).app 𝒢) hψ
  let ι : (f⁻¹).obj 𝒢' ⟶ ℱ := inverseImage_unit_pullback_cover_lift (f := f) φ
  refine ⟨𝒢', π, hπ, ι, ?_⟩
  -- Route correction: reuse the cached preserved-pullback rewrite lemma instead of replaying the
  -- transport-heavy calculation inline.
  simpa [𝒢', π, ι] using
    inverseImage_pullback_cover_factorization (f := f) (φ := φ)

/-- Helper for Lemma 7.41.1: if `f_*` maps locally surjective morphisms to locally surjective
morphisms, then covers of inverse images lift after a locally surjective cover upstairs. -/
theorem pushforwardMapsLocallySurjective_implies_surjectionLiftingAlongInverseImage
    (h₄ : ∀ {ℱ 𝒢 : Sheaf K (Type w)} (φ : ℱ ⟶ 𝒢),
      Sheaf.IsLocallySurjective φ →
        Sheaf.IsLocallySurjective ((f _*).map φ)) :
    f.surjectionLiftingAlongInverseImage := by
  intro ℱ 𝒢 φ hφ
  -- Use the unit pullback construction to build the lifted cover in the target topos.
  exact pullback_cover_lift_data (f := f) h₄ φ hφ

/-- Helper for Lemma 7.41.1: the pushforward morphism induced by a lifted pullback cover. -/
noncomputable abbrev pushforward_lifted_cover_map
    {ℱ 𝒢 : Sheaf K (Type w)} {𝒢' : Sheaf J (Type w)}
    (φ : ℱ ⟶ 𝒢)
    (ι : (f⁻¹).obj 𝒢' ⟶ pullback φ ((f.adjunction.counit).app 𝒢)) :
    𝒢' ⟶ (f _*).obj ℱ :=
  (f.adjunction.unit).app 𝒢' ≫
    (f _*).map (ι ≫ pullback.fst φ ((f.adjunction.counit).app 𝒢))

/-- Helper for Lemma 7.41.1: the map produced from a lifted pullback cover pushes forward to the
original target cover. -/
theorem lifted_cover_pullback_relation
    {ℱ 𝒢 : Sheaf K (Type w)} {𝒢' : Sheaf J (Type w)}
    (φ : ℱ ⟶ 𝒢)
    (γ : 𝒢' ⟶ (f _*).obj 𝒢)
    (ι : (f⁻¹).obj 𝒢' ⟶ pullback φ ((f.adjunction.counit).app 𝒢))
    (hι : ι ≫ pullback.snd φ ((f.adjunction.counit).app 𝒢) = (f⁻¹).map γ) :
    ι ≫ pullback.fst φ ((f.adjunction.counit).app 𝒢) ≫ φ =
      (f⁻¹).map γ ≫ (f.adjunction.counit).app 𝒢 := by
  -- First rewrite across the pullback square, then substitute the lifted cover factorization.
  calc
    ι ≫ pullback.fst φ ((f.adjunction.counit).app 𝒢) ≫ φ
        = ι ≫ pullback.snd φ ((f.adjunction.counit).app 𝒢) ≫
            (f.adjunction.counit).app 𝒢 := by
          simpa [Category.assoc] using
            congrArg (fun k ↦ ι ≫ k)
              (pullback.condition (f := φ) (g := (f.adjunction.counit).app 𝒢))
    _ = (f⁻¹).map γ ≫ (f.adjunction.counit).app 𝒢 := by
          simpa [Category.assoc] using
            congrArg (fun k ↦ k ≫ (f.adjunction.counit).app 𝒢) hι

/-- Helper for Lemma 7.41.1: the map produced from a lifted pullback cover pushes forward to the
original target cover. -/
theorem pushforward_lifted_cover_factorization
    {ℱ 𝒢 : Sheaf K (Type w)} {𝒢' : Sheaf J (Type w)}
    (φ : ℱ ⟶ 𝒢)
    (γ : 𝒢' ⟶ (f _*).obj 𝒢)
    (ι : (f⁻¹).obj 𝒢' ⟶ pullback φ ((f.adjunction.counit).app 𝒢))
    (hι : ι ≫ pullback.snd φ ((f.adjunction.counit).app 𝒢) = (f⁻¹).map γ) :
    pushforward_lifted_cover_map (f := f) φ ι ≫ (f _*).map φ = γ := by
  have hpb :
      ι ≫ pullback.fst φ ((f.adjunction.counit).app 𝒢) ≫ φ =
        (f⁻¹).map γ ≫ (f.adjunction.counit).app 𝒢 := by
    -- Reuse the isolated pullback normalization before pushing the factorization forward.
    exact lifted_cover_pullback_relation (f := f) (φ := φ) (γ := γ) (ι := ι) hι
  have hmap :
      (f.adjunction.unit).app 𝒢' ≫
          (f _*).map (ι ≫ pullback.fst φ ((f.adjunction.counit).app 𝒢)) ≫
            (f _*).map φ =
        (f.adjunction.unit).app 𝒢' ≫
          (f _*).map (ι ≫ pullback.fst φ ((f.adjunction.counit).app 𝒢) ≫ φ) := by
    -- First combine the two mapped morphisms into the map of their composite.
    simpa [Category.assoc] using
      congrArg
        (fun t ↦ (f.adjunction.unit).app 𝒢' ≫ t)
        ((Functor.map_comp (f _*)
          (ι ≫ pullback.fst φ ((f.adjunction.counit).app 𝒢)) φ).symm)
  have hmap' :
      (f.adjunction.unit).app 𝒢' ≫
          (f _*).map (ι ≫ pullback.fst φ ((f.adjunction.counit).app 𝒢) ≫ φ) =
        (f.adjunction.unit).app 𝒢' ≫
          (f _*).map ((f⁻¹).map γ ≫ (f.adjunction.counit).app 𝒢) := by
    -- Then rewrite the mapped composite using the pullback relation already isolated above.
    simpa using
      congrArg
        (fun t ↦ (f.adjunction.unit).app 𝒢' ≫ (f _*).map t)
        hpb
  -- Push forward the pullback factorization and then contract the unit-counit zig-zag.
  rw [pushforward_lifted_cover_map]
  rw [Category.assoc]
  refine hmap.trans ?_
  refine hmap'.trans ?_
  rw [Functor.map_comp]
  have hnat :
      (f.adjunction.unit).app 𝒢' ≫ (f _*).map ((f⁻¹).map γ) =
        γ ≫ (f.adjunction.unit).app ((f _*).obj 𝒢) := by
    simpa using f.adjunction.unit_naturality γ
  have hnat_assoc :
      (f.adjunction.unit).app 𝒢' ≫
          (f _*).map ((f⁻¹).map γ) ≫
            (f _*).map ((f.adjunction.counit).app 𝒢) =
        γ ≫ (f.adjunction.unit).app ((f _*).obj 𝒢) ≫
          (f _*).map ((f.adjunction.counit).app 𝒢) := by
    simpa [Category.assoc] using
      congrArg
        (fun t ↦ t ≫ (f _*).map ((f.adjunction.counit).app 𝒢))
        hnat
  have htriangle :
      γ ≫ (f.adjunction.unit).app ((f _*).obj 𝒢) ≫
          (f _*).map ((f.adjunction.counit).app 𝒢) = γ := by
    have htriangle_base :
        (f.adjunction.unit).app ((f _*).obj 𝒢) ≫
            (f _*).map ((f.adjunction.counit).app 𝒢) =
          𝟙 ((f _*).obj 𝒢) := by
      exact f.adjunction.right_triangle_components 𝒢
    calc
      γ ≫ (f.adjunction.unit).app ((f _*).obj 𝒢) ≫
          (f _*).map ((f.adjunction.counit).app 𝒢)
          = γ ≫ 𝟙 ((f _*).obj 𝒢) := by
              simpa [Category.assoc] using
                congrArg (fun t ↦ γ ≫ t) htriangle_base
      _ = γ := by simp
  -- Finish by the right triangle identity on the pushforward of `𝒢`.
  exact hnat_assoc.trans htriangle

/-- Helper for Lemma 7.41.1: if covers onto inverse images lift after a locally surjective
cover upstairs, then `f_*` maps locally surjective morphisms to locally surjective morphisms. -/
theorem pushforward_factorization_of_lifted_cover
    {ℱ 𝒢 : Sheaf K (Type w)} {𝒢' : Sheaf J (Type w)}
    (φ : ℱ ⟶ 𝒢)
    (γ : 𝒢' ⟶ (f _*).obj 𝒢)
    (ι : (f⁻¹).obj 𝒢' ⟶ pullback φ ((f.adjunction.counit).app 𝒢))
    (hι : ι ≫ pullback.snd φ ((f.adjunction.counit).app 𝒢) = (f⁻¹).map γ) :
    ∃ δ : 𝒢' ⟶ (f _*).obj ℱ, δ ≫ (f _*).map φ = γ := by
  let δ : 𝒢' ⟶ (f _*).obj ℱ := pushforward_lifted_cover_map (f := f) φ ι
  refine ⟨δ, ?_⟩
  -- Route correction: reuse the cached unit-counit rewrite lemma instead of replaying the full
  -- transport calculation inside this wrapper.
  simpa [δ] using
    pushforward_lifted_cover_factorization
      (f := f) (φ := φ) (γ := γ) (ι := ι) hι

/-- Helper for Lemma 7.41.1: if covers onto inverse images lift after a locally surjective
cover upstairs, then `f_*` maps locally surjective morphisms to locally surjective morphisms. -/
theorem surjectionLiftingAlongInverseImage_implies_pushforwardMapsLocallySurjective
    (hLift : f.surjectionLiftingAlongInverseImage) :
    ∀ {ℱ 𝒢 : Sheaf K (Type w)} (φ : ℱ ⟶ 𝒢),
      Sheaf.IsLocallySurjective φ →
        Sheaf.IsLocallySurjective ((f _*).map φ) := by
  intro ℱ 𝒢 φ hφ
  let b : pullback φ ((f.adjunction.counit).app 𝒢) ⟶ (f⁻¹).obj ((f _*).obj 𝒢) :=
    pullback.snd φ ((f.adjunction.counit).app 𝒢)
  have hb : Sheaf.IsLocallySurjective b := by
    -- Pull back the original cover along the counit before applying the lifting hypothesis.
    simpa [b] using
      sheaf_pullback_snd_isLocallySurjective (J := K) φ ((f.adjunction.counit).app 𝒢) hφ
  rcases hLift b hb with ⟨𝒢', γ, hγ, ι, hι⟩
  rcases pushforward_factorization_of_lifted_cover
      (f := f) (φ := φ) (γ := γ) (ι := ι) hι with ⟨δ, hδ⟩
  -- Descend local surjectivity of `γ` across the exhibited factorization.
  rw [← Sheaf.isLocallySurjective_sheafToPresheaf_map_iff]
  change Presheaf.IsLocallySurjective J (((f _*).map φ).hom)
  letI : Presheaf.IsLocallySurjective J γ.hom := hγ
  simpa using Presheaf.isLocallySurjective_of_isLocallySurjective_fac
    (J := J)
    (f₁ := δ.hom)
    (f₂ := ((f _*).map φ).hom)
    (f₃ := γ.hom)
    (by
      simpa using congrArg (fun t ↦ t.hom) hδ)

-- Proof sketch: for `(3) → (9)`, apply the exact left adjoint `f⁻¹` to an epic image and use the
-- epic counit to descend epimorphy. For `(9) → (3)`, the counit becomes split epic after
-- applying `f_*`, and reflection of epimorphisms brings this back to the source.
/-- Lemma 7.41.1 (7): property (3) is equivalent to property (9), i.e. the counit is surjective
on all sheaves exactly when `f_*` reflects surjections. -/
theorem counitIsLocallySurjective_iff_pushforwardReflectsEpimorphisms
    [HasSheafify.{v₂, w, u₂, w + 1} K (Type w)] :
    (∀ ℱ : Sheaf K (Type w), Sheaf.IsLocallySurjective ((f.adjunction.counit).app ℱ)) ↔
      (f _*).ReflectsEpimorphisms := by
  constructor
  · intro h₃
    -- Rewrite the source-facing counit-surjectivity hypothesis to the owner `Epi` statement.
    refine ⟨?_⟩
    intro ℱ 𝒢 a ha
    letI : (f⁻¹).PreservesEpimorphisms :=
      CategoryTheory.Functor.preservesEpimorphisms_of_adjunction f.adjunction
    have hCounitEpi :
        ∀ X : Sheaf K (Type w), Epi ((f.adjunction.counit).app X) := by
      intro X
      exact Sheaf.epi_of_isLocallySurjective_ambient
        (J := K) ((f.adjunction.counit).app X) (h₃ X)
    letI : Epi ((f _*).map a) := ha
    have hInverseImageMapEpi : Epi ((f⁻¹).map ((f _*).map a)) := by infer_instance
    letI : Epi ((f⁻¹).map ((f _*).map a)) := hInverseImageMapEpi
    letI : Epi ((f.adjunction.counit).app 𝒢) := hCounitEpi 𝒢
    have hMappedEpi :
        Epi ((f⁻¹).map ((f _*).map a) ≫ (f.adjunction.counit).app 𝒢) := by
      exact CategoryTheory.epi_comp' hInverseImageMapEpi (hCounitEpi 𝒢)
    letI : Epi ((f⁻¹).map ((f _*).map a) ≫ (f.adjunction.counit).app 𝒢) := hMappedEpi
    -- Counit naturality identifies this epic composite with `ε_ℱ ≫ a`, so cancellation proves
    -- that `a` is epic.
    refine ⟨?_⟩
    intro Z g h hEq
    apply (cancel_epi ((f⁻¹).map ((f _*).map a) ≫ (f.adjunction.counit).app 𝒢)).1
    have hLeft :
        ((f⁻¹).map ((f _*).map a) ≫ (f.adjunction.counit).app 𝒢) ≫ g =
          (f.adjunction.counit).app ℱ ≫ a ≫ g := by
      simp [Category.assoc]
    have hMiddle :
        (f.adjunction.counit).app ℱ ≫ a ≫ g =
          (f.adjunction.counit).app ℱ ≫ a ≫ h := by
      simp [hEq]
    have hRight :
        (f.adjunction.counit).app ℱ ≫ a ≫ h =
          ((f⁻¹).map ((f _*).map a) ≫ (f.adjunction.counit).app 𝒢) ≫ h := by
      simp [Category.assoc]
    exact hLeft.trans (hMiddle.trans hRight)
  · intro h₉ ℱ
    -- Reflect counit epimorphy first, then translate back to the textbook surjectivity clause.
    have hCounitEpi : Epi ((f.adjunction.counit).app ℱ) := by
      letI : (f _*).ReflectsEpimorphisms := h₉
      have hSplit :
          IsSplitEpi ((f _*).map ((f.adjunction.counit).app ℱ)) := by
        refine IsSplitEpi.mk' ⟨(f.adjunction.unit).app ((f _*).obj ℱ), ?_⟩
        exact f.adjunction.right_triangle_components ℱ
      exact CategoryTheory.Functor.epi_of_epi_map
        (F := (f _*)) (f := (f.adjunction.counit).app ℱ)
        (show Epi ((f _*).map ((f.adjunction.counit).app ℱ)) from inferInstance)
    exact (Sheaf.isLocallySurjective_iff_epi_ambient
      (J := K) ((f.adjunction.counit).app ℱ)).2
      hCounitEpi

/-- Helper for Lemma 7.41.1: epic counit components force `f_*` to reflect epimorphisms. -/
theorem counitEpi_implies_pushforwardReflectsEpimorphisms
    (h₃ : ∀ ℱ : Sheaf K (Type w), Epi ((f.adjunction.counit).app ℱ)) :
    (f _*).ReflectsEpimorphisms := by
  refine ⟨?_⟩
  intro ℱ 𝒢 a ha
  -- The left adjoint `f⁻¹` preserves the mapped epimorphism.
  letI : (f⁻¹).PreservesEpimorphisms :=
    CategoryTheory.Functor.preservesEpimorphisms_of_adjunction f.adjunction
  letI : Epi ((f _*).map a) := ha
  have hInverseImageMapEpi : Epi ((f⁻¹).map ((f _*).map a)) := by infer_instance
  letI : Epi ((f⁻¹).map ((f _*).map a)) := hInverseImageMapEpi
  letI : Epi ((f.adjunction.counit).app 𝒢) := h₃ 𝒢
  have hMappedEpi :
      Epi ((f⁻¹).map ((f _*).map a) ≫ (f.adjunction.counit).app 𝒢) := by
    exact CategoryTheory.epi_comp' hInverseImageMapEpi (h₃ 𝒢)
  letI : Epi ((f⁻¹).map ((f _*).map a) ≫ (f.adjunction.counit).app 𝒢) := hMappedEpi
  -- Counit naturality identifies this epic composite with `ε_ℱ ≫ a`, so cancellation proves
  -- that `a` is epic.
  refine ⟨?_⟩
  intro Z g h hEq
  apply (cancel_epi ((f⁻¹).map ((f _*).map a) ≫ (f.adjunction.counit).app 𝒢)).1
  have hLeft :
      ((f⁻¹).map ((f _*).map a) ≫ (f.adjunction.counit).app 𝒢) ≫ g =
        (f.adjunction.counit).app ℱ ≫ a ≫ g := by
    simp [Category.assoc]
  have hMiddle :
      (f.adjunction.counit).app ℱ ≫ a ≫ g =
        (f.adjunction.counit).app ℱ ≫ a ≫ h := by
    simp [hEq]
  have hRight :
      (f.adjunction.counit).app ℱ ≫ a ≫ h =
        ((f⁻¹).map ((f _*).map a) ≫ (f.adjunction.counit).app 𝒢) ≫ h := by
    simp [Category.assoc]
  exact hLeft.trans (hMiddle.trans hRight)

/-- Helper for Lemma 7.41.1: if `f_*` reflects epimorphisms, then each counit component is epic. -/
theorem counitEpi_of_pushforwardReflectsEpimorphisms
    (h₉ : (f _*).ReflectsEpimorphisms) :
    ∀ ℱ : Sheaf K (Type w), Epi ((f.adjunction.counit).app ℱ) := by
  intro ℱ
  letI : (f _*).ReflectsEpimorphisms := h₉
  -- The right triangle identity gives a section after applying `f_*`.
  have hSplit :
      IsSplitEpi ((f _*).map ((f.adjunction.counit).app ℱ)) := by
    refine IsSplitEpi.mk' ⟨(f.adjunction.unit).app ((f _*).obj ℱ), ?_⟩
    exact f.adjunction.right_triangle_components ℱ
  -- Reflect the resulting epimorphism back along `f_*`.
  exact CategoryTheory.Functor.epi_of_epi_map
    (F := (f _*)) (f := (f.adjunction.counit).app ℱ)
    (show Epi ((f _*).map ((f.adjunction.counit).app ℱ)) from inferInstance)

/-- Owner-level companion to Lemma 7.41.1 (9): using
`Sheaf.isLocallySurjective_iff_epi`, the source-facing counit-surjectivity clause can be read as
the usual `Epi` reformulation. -/
theorem counitEpi_iff_pushforwardReflectsEpimorphisms :
    (∀ ℱ : Sheaf K (Type w), Epi ((f.adjunction.counit).app ℱ)) ↔
      (f _*).ReflectsEpimorphisms := by
  constructor
  · intro h₃
    -- This direction is owner-level: counit naturality and preservation of epis by `f⁻¹`
    -- suffice, so no source-facing bridge is needed.
    exact counitEpi_implies_pushforwardReflectsEpimorphisms (f := f) h₃
  · intro h₉
    -- The counit becomes split epic after applying `f_*`, and `h₉` reflects epimorphisms.
    exact counitEpi_of_pushforwardReflectsEpimorphisms (f := f) h₉

-- Proof sketch: a surjection can be characterized by the pushout square with identical codomain
-- legs, so preservation of pushouts carries surjections to surjections.
/-- Lemma 7.41.1 (8): property (6) implies property (4), so preserving pushouts forces `f_*` to
send surjections to surjections. -/
theorem pushforwardPreservesPushouts_implies_pushforwardMapsLocallySurjective
    [HasSheafify.{v₁, w, u₁, w + 1} J (Type w)]
    (h₆ : PreservesColimitsOfShape WalkingSpan (f _*)) :
    ∀ {ℱ 𝒢 : Sheaf K (Type w)} (φ : ℱ ⟶ 𝒢),
      Sheaf.IsLocallySurjective φ →
        Sheaf.IsLocallySurjective ((f _*).map φ) := by
  intro ℱ 𝒢 φ hφ
  -- First run the textbook pushout argument at the owner `Epi` level.
  letI : PreservesColimitsOfShape WalkingSpan (f _*) := h₆
  letI : Sheaf.IsLocallySurjective φ := hφ
  have hMapEpi : Epi ((f _*).map φ) := by
    letI : Epi φ := by infer_instance
    infer_instance
  -- Translate the mapped epimorphism back to the source-facing local-surjectivity predicate.
  exact (Sheaf.isLocallySurjective_iff_epi_ambient
    (J := J) ((f _*).map φ)).2 hMapEpi

/-- Owner-level companion to Lemma 7.41.1 (10): preserving pushouts makes `f_*` preserve
epimorphisms. -/
theorem pushforwardPreservesPushouts_implies_pushforwardPreservesEpimorphisms
    (h₆ : PreservesColimitsOfShape WalkingSpan (f _*)) :
    (f _*).PreservesEpimorphisms := by
  letI := h₆
  infer_instance

/-- Helper for Lemma 7.41.1: after whiskering by `ULift`, the mapped kernel-pair diagram is
identified with the actual kernel-pair diagram of the whiskered morphism. -/
noncomputable def ulift_mapped_kernel_pair_parallelPair_iso
    {ℱ 𝒢 : Sheaf K (Type w)} (φ : ℱ ⟶ 𝒢) :
    parallelPair
        ((sheafCompose K
          (CategoryTheory.uliftFunctor.{max u₂ v₂, w} :
            Type w ⥤ Type (max w (max u₂ v₂)))).map (pullback.fst φ φ))
        ((sheafCompose K
          (CategoryTheory.uliftFunctor.{max u₂ v₂, w} :
            Type w ⥤ Type (max w (max u₂ v₂)))).map (pullback.snd φ φ)) ≅
      parallelPair
        (pullback.fst
          ((sheafCompose K
            (CategoryTheory.uliftFunctor.{max u₂ v₂, w} :
              Type w ⥤ Type (max w (max u₂ v₂)))).map φ)
          ((sheafCompose K
            (CategoryTheory.uliftFunctor.{max u₂ v₂, w} :
              Type w ⥤ Type (max w (max u₂ v₂)))).map φ))
        (pullback.snd
          ((sheafCompose K
            (CategoryTheory.uliftFunctor.{max u₂ v₂, w} :
              Type w ⥤ Type (max w (max u₂ v₂)))).map φ)
          ((sheafCompose K
            (CategoryTheory.uliftFunctor.{max u₂ v₂, w} :
              Type w ⥤ Type (max w (max u₂ v₂)))).map φ)) := by
  let F :
      Sheaf K (Type w) ⥤ Sheaf K (Type (max w (max u₂ v₂))) :=
    sheafCompose K
      (CategoryTheory.uliftFunctor.{max u₂ v₂, w} :
        Type w ⥤ Type (max w (max u₂ v₂)))
  let G := sheafToPresheaf K (Type (max w (max u₂ v₂)))
  -- Obtain the needed pullback-preservation instance by reflecting it from underlying
  -- presheaves, where whiskering by `ULift` preserves all limits.
  haveI : PreservesLimit (cospan φ φ) (F ⋙ G) := by
    change PreservesLimit (cospan φ φ)
      ((sheafToPresheaf K (Type w)) ⋙
        (Functor.whiskeringRight Dᵒᵖ (Type w) (Type (max w (max u₂ v₂)))).obj
          (CategoryTheory.uliftFunctor.{max u₂ v₂, w} :
            Type w ⥤ Type (max w (max u₂ v₂))))
    infer_instance
  haveI : PreservesLimit (cospan φ φ) F :=
    preservesLimit_of_reflects_of_preserves F G
  -- The zero-component is the canonical pullback comparison isomorphism upstairs.
  refine parallelPair.ext (PreservesPullback.iso F φ φ) (Iso.refl _) ?_ ?_
  · -- The left leg is exactly the first pullback projection comparison.
    exact (PreservesPullback.iso_hom_fst F φ φ).symm
  · -- The right leg is exactly the second pullback projection comparison.
    exact (PreservesPullback.iso_hom_snd F φ φ).symm

/-- Helper for Lemma 7.41.1: the kernel-pair cofork of a locally surjective sheaf map is a
colimit after transporting the source proof to the large `ULift` universe and reflecting it
back to the original sheaf category. -/
noncomputable def ulift_kernel_pair_mapCocone_isColimit
    {ℱ 𝒢 : Sheaf K (Type w)} (φ : ℱ ⟶ 𝒢)
    (hUp : IsColimit
      (Cofork.ofπ
        ((sheafCompose K
          (CategoryTheory.uliftFunctor.{max u₂ v₂, w} :
            Type w ⥤ Type (max w (max u₂ v₂)))).map φ)
        pullback.condition)) :
    IsColimit
      ((sheafCompose K
        (CategoryTheory.uliftFunctor.{max u₂ v₂, w} :
          Type w ⥤ Type (max w (max u₂ v₂)))).mapCocone
        (Cofork.ofπ φ pullback.condition)) := by
  let F :
      Sheaf K (Type w) ⥤ Sheaf K (Type (max w (max u₂ v₂))) :=
    sheafCompose K
      (CategoryTheory.uliftFunctor.{max u₂ v₂, w} :
        Type w ⥤ Type (max w (max u₂ v₂)))
  let e := ulift_mapped_kernel_pair_parallelPair_iso (K := K) (φ := φ)
  let hTransport :
      IsColimit
        ((Cocone.precompose
          e.hom).obj
          (Cofork.ofπ (F.map φ) (pullback.condition (f := F.map φ) (g := F.map φ)))) :=
    (IsColimit.precomposeInvEquiv
      e.symm
      (Cofork.ofπ (F.map φ) (pullback.condition (f := F.map φ) (g := F.map φ)))).2 hUp
  have hMappedCofork :
      IsColimit
        (Cofork.ofπ (F.map φ) (by
          simp only [← F.map_comp, pullback.condition]) :
          Cofork (F.map (pullback.fst φ φ)) (F.map (pullback.snd φ φ))) :=
    IsColimit.ofIsoColimit hTransport (Cofork.ext (Iso.refl _) (by
      change e.hom.app WalkingParallelPair.one ≫ F.map φ = F.map φ
      have hOne : e.hom.app WalkingParallelPair.one = 𝟙 _ := rfl
      simpa [hOne]))
  -- First rewrite the mapped cofork as the cofork of the mapped morphisms.
  exact (Limits.isColimitMapCoconeCoforkEquiv F pullback.condition).symm <|
  -- Then transport along the explicit comparison between the mapped pullback diagram and the
  -- actual pullback diagram upstairs.
    hMappedCofork

noncomputable def sheaf_isColimitCoforkOfIsLocallySurjective_via_ulift
    {ℱ 𝒢 : Sheaf K (Type w)} (φ : ℱ ⟶ 𝒢)
    (hφ : Sheaf.IsLocallySurjective φ) :
    IsColimit (Cofork.ofπ φ pullback.condition) := by
  let F :
      Sheaf K (Type w) ⥤ Sheaf K (Type (max w (max u₂ v₂))) :=
    sheafCompose K
      (CategoryTheory.uliftFunctor.{max u₂ v₂, w} :
        Type w ⥤ Type (max w (max u₂ v₂)))
  have hUpSurj : Sheaf.IsLocallySurjective (F.map φ) :=
    (Sheaf.isLocallySurjective_whisker_ulift_iff (J := K) (φ := φ)).2 hφ
  have hUpKernel :
      IsColimit (Cofork.ofπ (F.map φ) pullback.condition) :=
    Sheaf.isColimitCoforkOfIsLocallySurjective (J := K) (φ := F.map φ) hUpSurj
  have hMapped :
      IsColimit (F.mapCocone (Cofork.ofπ φ pullback.condition)) :=
    ulift_kernel_pair_mapCocone_isColimit (K := K) (φ := φ) hUpKernel
  letI : F.Full := inferInstance
  letI : F.Faithful := inferInstance
  -- Reflect the upstairs colimit through the fully faithful `ULift` whiskering functor by
  -- taking preimages of the universal morphisms and using faithfulness for the required equalities.
  refine
    { desc := fun S => F.preimage (hMapped.desc (F.mapCocone S))
      fac := fun S j => by
        apply F.map_injective
        simpa using hMapped.fac (F.mapCocone S) j
      uniq := fun S m hm => by
        apply F.map_injective
        simpa using hMapped.uniq (F.mapCocone S) (F.map m) (fun j => by
          simpa using congrArg (fun k ↦ F.map k) (hm j)) }

noncomputable def Sheaf.isColimitCoforkOfIsLocallySurjective_ambient
    {ℱ 𝒢 : Sheaf K (Type w)} (φ : ℱ ⟶ 𝒢)
    (hφ : Sheaf.IsLocallySurjective φ) :
    IsColimit (Cofork.ofπ φ pullback.condition) :=
  sheaf_isColimitCoforkOfIsLocallySurjective_via_ulift
    (K := K) (φ := φ) hφ

/-- Helper for Lemma 7.41.1: if `f_*` preserves coequalizers and a sheaf map is exhibited as the
coequalizer of its kernel pair, then the mapped morphism is epic. -/
theorem mapped_epi_of_preservesCoequalizers_of_kernel_pair
    {ℱ 𝒢 : Sheaf K (Type w)} (φ : ℱ ⟶ 𝒢)
    (h₅ : PreservesColimitsOfShape WalkingParallelPair (f _*))
    (hcoeq : IsColimit (Cofork.ofπ φ pullback.condition)) :
    Epi ((f _*).map φ) := by
  -- Preserve the kernel-pair cofork and read the mapped structure map as an epi.
  letI : PreservesColimitsOfShape WalkingParallelPair (f _*) := h₅
  let hMappedCoeq :=
    Limits.isColimitCoforkMapOfIsColimit (G := (f _*)) pullback.condition hcoeq
  exact epi_of_isColimit_cofork hMappedCoeq

-- Proof sketch: a surjection is the coequalizer of its kernel pair, so preservation of
-- coequalizers makes the pushforward of a surjection epic.
/-- Lemma 7.41.1 (9): property (5) implies property (4), so preserving coequalizers forces
`f_*` to send surjections to surjections. -/
theorem pushforwardPreservesCoequalizers_implies_pushforwardMapsLocallySurjective
    [HasSheafify.{v₁, w, u₁, w + 1} J (Type w)]
    (h₅ : PreservesColimitsOfShape WalkingParallelPair (f _*)) :
    ∀ {ℱ 𝒢 : Sheaf K (Type w)} (φ : ℱ ⟶ 𝒢),
      Sheaf.IsLocallySurjective φ →
        Sheaf.IsLocallySurjective ((f _*).map φ) := by
  intro ℱ 𝒢 φ hφ
  -- Follow the source proof literally: a locally surjective map is the coequalizer of its kernel
  -- pair, so preserving that coequalizer makes the mapped morphism epic.
  have hcoeq : IsColimit (Cofork.ofπ φ pullback.condition) :=
    Sheaf.isColimitCoforkOfIsLocallySurjective_ambient (K := K) (φ := φ) hφ
  have hMapEpi : Epi ((f _*).map φ) :=
    mapped_epi_of_preservesCoequalizers_of_kernel_pair
      (f := f) (φ := φ) h₅ hcoeq
  -- Translate the resulting owner-level epimorphism back to the source-facing statement.
  exact (Sheaf.isLocallySurjective_iff_epi_ambient
    (J := J) ((f _*).map φ)).2 hMapEpi

/-- Owner-level companion to Lemma 7.41.1 (11): using
`Sheaf.isLocallySurjective_iff_epi`, preserving coequalizers makes `f_*` preserve
epimorphisms. -/
theorem pushforwardPreservesCoequalizers_implies_pushforwardPreservesEpimorphisms
    [HasSheafify.{v₂, w, u₂, w + 1} K (Type w)]
    (h₅ : PreservesColimitsOfShape WalkingParallelPair (f _*)) :
    ∀ {ℱ 𝒢 : Sheaf K (Type w)} (φ : ℱ ⟶ 𝒢), Epi φ → Epi ((f _*).map φ) := by
  letI := h₅
  intro ℱ 𝒢 φ hφ
  -- Convert the source epimorphism to the source-facing local-surjectivity hypothesis from
  -- Lemma 7.11.2 so that Lemma 7.11.3 supplies the kernel-pair coequalizer.
  have hφ_surj : Sheaf.IsLocallySurjective φ :=
    (Sheaf.isLocallySurjective_iff_epi_ambient (J := K) φ).2 hφ
  let hcoeq := Sheaf.isColimitCoforkOfIsLocallySurjective (J := K) (φ := φ) hφ_surj
  -- Preserving the kernel-pair coequalizer makes the mapped cofork a coequalizer, hence its
  -- structure morphism `(f _*).map φ` is epic.
  let hMappedCoeq :=
    Limits.isColimitCoforkMapOfIsColimit (G := (f _*)) pullback.condition hcoeq
  exact epi_of_isColimit_cofork hMappedCoeq

-- Proof sketch: for `(4) → (11)`, push forward an epic map to `f⁻¹ 𝒢`, pull back along the unit,
-- and use preservation of epimorphisms to build the desired cover of `𝒢`. For `(11) → (4)`,
-- apply the lifting property to the pullback of the counit and push the resulting factorization
-- forward.
/-- Lemma 7.41.1 (10): property (4) is equivalent to property (11), i.e. `f_*` sends surjections
to surjections exactly when surjections onto inverse images lift after a surjective cover. -/
theorem pushforwardMapsLocallySurjective_iff_surjectionLiftingAlongInverseImage :
    (∀ {ℱ 𝒢 : Sheaf K (Type w)} (φ : ℱ ⟶ 𝒢),
      Sheaf.IsLocallySurjective φ →
        Sheaf.IsLocallySurjective ((f _*).map φ)) ↔
      f.surjectionLiftingAlongInverseImage := by
  constructor
  · intro h₄
    -- Use the unit pullback construction to build the lifted cover in the target topos.
    exact pushforwardMapsLocallySurjective_implies_surjectionLiftingAlongInverseImage
      (f := f) h₄
  · intro hLift
    -- Pull back along the counit and descend the lifted cover through the pushed-forward
    -- factorization.
    exact surjectionLiftingAlongInverseImage_implies_pushforwardMapsLocallySurjective
      (f := f) hLift

/-- Owner-level companion to Lemma 7.41.1 (12): using
`Sheaf.isLocallySurjective_iff_epi`, the source-facing preservation-of-surjections clause is
equivalent to the categorical statement that `f_*` preserves epimorphisms. -/
theorem pushforwardPreservesEpimorphisms_iff_surjectionLiftingAlongInverseImage
    [HasSheafify.{v₁, w, u₁, w + 1} J (Type w)]
    [HasSheafify.{v₂, w, u₂, w + 1} K (Type w)] :
    (f _*).PreservesEpimorphisms ↔
      MorphismOfTopoiIn.surjectionLiftingAlongInverseImage.{u₁, u₂, v₁, v₂, w} f := by
  -- Rewrite the source-facing lifting equivalence through the ambient epi/local-surjective bridge.
  rw [← pushforwardMapsLocallySurjective_iff_surjectionLiftingAlongInverseImage.{u₁, u₂, v₁, v₂, w}
    (f := f)]
  constructor
  · intro hPres
    letI : (f _*).PreservesEpimorphisms := hPres
    intro ℱ 𝒢 φ hφ
    -- Convert the source surjectivity hypothesis to an epi, push it forward, and rewrite back.
    have hMapEpi : Epi ((f _*).map φ) := by
      have hEpi : Epi φ :=
        (Sheaf.isLocallySurjective_iff_epi_ambient (J := K) φ).1 hφ
      letI : Epi φ := hEpi
      infer_instance
    exact (Sheaf.isLocallySurjective_iff_epi_ambient
      (J := J) ((f _*).map φ)).2 hMapEpi
  · intro hLift
    refine ⟨?_⟩
    intro ℱ 𝒢 φ hφ
    -- Route correction: use the already established source-facing lifting equivalence first,
    -- then rewrite the two local-surjectivity statements as epimorphism statements.
    have hMapSurj :
        Sheaf.IsLocallySurjective ((f _*).map φ) :=
      hLift φ <|
        (Sheaf.isLocallySurjective_iff_epi_ambient (J := K) φ).2 hφ
    exact (Sheaf.isLocallySurjective_iff_epi_ambient
      (J := J) ((f _*).map φ)).1 hMapSurj

-- Proof sketch: if `f_* φ` is monic, then the induced diagonal map becomes an epimorphism after
-- pushforward; reflection of epimorphisms shows the original diagonal map is epic, hence `φ` is
-- monic.
/-- Lemma 7.41.1 (11): property (9) implies property (8), so if `f_*` reflects surjections then
it also reflects injections. -/
theorem pushforwardReflectsEpimorphisms_implies_pushforwardReflectsMonomorphisms
    (h₉ : (f _*).ReflectsEpimorphisms) :
    (f _*).ReflectsMonomorphisms := by
  -- Property (9) already implies property (3), and property (3) implies faithfulness. A faithful
  -- functor reflects monomorphisms, so we can close the mono clause through the established chain.
  letI : (f _*).Faithful :=
    counitEpi_implies_pushforwardFaithful (f := f)
      ((counitEpi_iff_pushforwardReflectsEpimorphisms (f := f)).2 h₉)
  infer_instance

-- Proof sketch: in a balanced sheaf category, a morphism is an isomorphism as soon as it is both
-- monic and epic; combine the previous implication with reflection of epimorphisms.
/-- Lemma 7.41.1 (12): property (9) implies property (10), so if `f_*` reflects surjections then
it reflects bijections. -/
theorem pushforwardReflectsEpimorphisms_implies_pushforwardReflectsIsomorphisms
    [HasSheafify.{v₂, w, u₂, w + 1} K (Type w)]
    (h₉ : ((f _*) : Sheaf K (Type w) ⥤ Sheaf J (Type w)).ReflectsEpimorphisms) :
    ((f _*) : Sheaf K (Type w) ⥤ Sheaf J (Type w)).ReflectsIsomorphisms := by
  letI : ((f _*) : Sheaf K (Type w) ⥤ Sheaf J (Type w)).ReflectsEpimorphisms := h₉
  letI : ((f _*) : Sheaf K (Type w) ⥤ Sheaf J (Type w)).ReflectsMonomorphisms :=
    pushforwardReflectsEpimorphisms_implies_pushforwardReflectsMonomorphisms
      (f := f) h₉
  refine ⟨?_⟩
  intro ℱ 𝒢 φ hφ
  have hMono : Mono φ := by
    exact CategoryTheory.Functor.mono_of_mono_map
      (F := ((f _*) : Sheaf K (Type w) ⥤ Sheaf J (Type w))) (f := φ)
      (show Mono (((f _*) : Sheaf K (Type w) ⥤ Sheaf J (Type w)).map φ) from inferInstance)
  have hEpi : Epi φ := by
    exact CategoryTheory.Functor.epi_of_epi_map
      (F := ((f _*) : Sheaf K (Type w) ⥤ Sheaf J (Type w))) (f := φ)
      (show Epi (((f _*) : Sheaf K (Type w) ⥤ Sheaf J (Type w)).map φ) from inferInstance)
  letI : Mono φ := hMono
  letI : Epi φ := hEpi
  -- With the small sheafification bridge in this owner-level companion, the sheaf category is
  -- balanced, so mono plus epi gives the desired isomorphism.
  letI : Balanced (Sheaf K (Type w)) := SheafOfTypes.balanced.{w, v₂, u₂} (J := K)
  exact isIso_of_mono_of_epi φ

-- Proof sketch: the forward direction is the standard implication from a fully faithful right
-- adjoint to an isomorphic counit; the reverse direction is already the earlier canonical recall
-- `Adjunction.fullyFaithfulROfIsIsoCounit`, so no extra `Full ∧ Faithful` wrapper is needed.
/- Canonical companion: the direction from full faithfulness of `f_*` to invertibility of the
counit `f⁻¹ f_* ℱ ⟶ ℱ` is the exact canonical adjunction owner theorem
`Adjunction.counit_isIso_of_R_fully_faithful` applied to `f.adjunction`. Together with the
earlier recall `Adjunction.fullyFaithfulROfIsIsoCounit`, this already gives the source
equivalence in canonical owner form. -/
recall Adjunction.counit_isIso_of_R_fully_faithful

end

end MorphismOfTopoiIn

end CategoryTheory
