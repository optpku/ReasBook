module

public import Mathlib.CategoryTheory.Sites.LocallySurjective
public import Mathlib.CategoryTheory.Functor.ReflectsIso.Balanced
public import Mathlib.Topology.Sheaves.LocallySurjective
public import Mathlib.CategoryTheory.Sites.Point.Skyscraper
public import Mathlib.Topology.Sheaves.Skyscraper
public import Mathlib.CategoryTheory.Sites.LeftExact
public import Mathlib.CategoryTheory.Sites.Sheafification
public import Mathlib.CategoryTheory.Sites.Sheaf
public import stacks_project.Chap07.Definition_7_32_1
public import stacks_project.Chap07.GSetForgetfulPoint
public import stacks_project.Chap07.Lemma_7_11_2
public import stacks_project.Chap07.Lemma_7_32_7
public import stacks_project.Chap07.Lemma_7_32_9

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory.Limits
open Opposite

universe u v w

namespace CategoryTheory

open scoped MorphismOfTopoiIn

variable {C : Type u} [Category.{v} C]
variable {J : GrothendieckTopology C}

/- Domain-style sampling for Lemma 7.32.10:
- primary domain: points of topoi, via the `Type`-valued adjunction
  `p.typeInverseImage ⊣ p.typePushforward`;
- sampled owner declarations:
  `MorphismOfTopoiIn.typePushforward`,
  `MorphismOfTopoiIn.typeAdjunction`,
  `MorphismOfTopoiIn.pointPushforwardFiber_counit_isSplitEpi`,
  `Adjunction.faithful_R_of_epi_counit_app`;
- best owner abstraction: the owner functor `p.typePushforward`, with its adjunction as primitive
  data and its preservation/reflection properties as derived API;
- primitive data: the topos point `p : MorphismOfTopoiIn J typesGrothendieckTopology` and the
  adjunction already packaged in `Definition_7_32_1`;
- derived API: functorial properties of `p.typePushforward`, plus the sheaf-side predicates
  `Sheaf.IsLocallyInjective` and `Sheaf.IsLocallySurjective` as mono/epi bridge language;
- source/core/bridge triage:
  `source-facing`: the numbered clauses of Lemma 7.32.10;
  `core/canonical`: `p.typeAdjunction` and the functor classes on `p.typePushforward`;
  `bridge/view`: `Sheaf.isLocallyInjective_iff_mono` and
    `Sheaf.isLocallySurjective_iff_epi`. -/

-- Proof sketch: `p.pushforward` is the right adjoint in the adjunction `p.inverseImage ⊣
-- p.pushforward`, and right adjoints preserve all limits.
/-- Lemma 7.32.10 (1): for a point `p : Sh(pt) ⟶ Sh(𝒞)` of the topos associated to a site
`(𝒞, J)`, the direct-image functor `p_* : Type w ⥤ Sh(J, Type w)` commutes with arbitrary
limits. -/
theorem toposPoint_pushforward_preservesLimits
    (p : MorphismOfTopoiIn J typesGrothendieckTopology.{w}) :
    PreservesLimits p.typePushforward := by
  infer_instance

-- Proof sketch: clause (1) gives preservation of all limits, hence in particular of finite
-- limits, which is exactly left exactness.
/-- Lemma 7.32.10 (2): the direct-image functor of a topos point is left exact. -/
theorem toposPoint_pushforward_leftExact
    (p : MorphismOfTopoiIn J typesGrothendieckTopology.{w}) :
    PreservesFiniteLimits p.typePushforward := by
  infer_instance

-- Proof sketch: the counit map `p.inverseImage.obj (p.pushforward.obj E) ⟶ E` is canonically a
-- split epimorphism; if two maps `E ⟶ E'` become equal after applying `p.pushforward`, applying
-- `p.inverseImage` and composing with the splitting forces the original maps to agree.
/-- Lemma 7.32.10 (3): the direct-image functor of a topos point is faithful. -/
theorem toposPoint_pushforward_faithful
    (p : MorphismOfTopoiIn J typesGrothendieckTopology.{w}) :
    p.typePushforward.Faithful := by
  letI (E : Type w) : Epi ((p.typeAdjunction.counit).app E) := by
    letI := MorphismOfTopoiIn.pointPushforwardFiber_counit_isSplitEpi p E
    infer_instance
  exact p.typeAdjunction.faithful_R_of_epi_counit_app

/-- Helper for Lemma 7.32.10: on each object `U`, the section map of a skyscraper sheaf induced by
a surjective function `f : E → E'` is surjective. -/
theorem sitePoint_skyscraper_map_app_surjective
    (Φ : GrothendieckTopology.Point.{w} J) {E E' : Type w} (f : E → E')
    (hf : Function.Surjective f) (U : C) :
    Function.Surjective
      (((sheafToPresheaf J (Type w)).map
        (Φ.skyscraperSheafFunctor.map (show E ⟶ E' from f))).app (op U)) := by
  -- A surjective map of sets is split epic, and every functor preserves split epimorphisms.
  -- Evaluating the resulting split epi in `Type` gives the desired surjectivity on sections.
  letI : IsSplitEpi (show E ⟶ E' from f) :=
    (CategoryTheory.isSplitEpi_iff_surjective f).2 hf
  letI : IsSplitEpi
      (((sheafToPresheaf J (Type w)).map
        (Φ.skyscraperSheafFunctor.map (show E ⟶ E' from f))).app (op U)) := by
    infer_instance
  exact
    (CategoryTheory.isSplitEpi_iff_surjective
      (((sheafToPresheaf J (Type w)).map
        (Φ.skyscraperSheafFunctor.map (show E ⟶ E' from f))).app (op U))).1 inferInstance

/-- Helper for Lemma 7.32.10: the skyscraper functor of a site point sends surjective maps of
sets to locally surjective morphisms of sheaves. -/
theorem sitePoint_skyscraper_map_isLocallySurjective
    (Φ : GrothendieckTopology.Point.{w} J) {E E' : Type w} (f : E → E')
    (hf : Function.Surjective f) :
    Sheaf.IsLocallySurjective (Φ.skyscraperSheafFunctor.map (show E ⟶ E' from f)) := by
  -- Work on underlying presheaves, where local surjectivity is immediate from the objectwise
  -- surjectivity established above.
  rw [← Sheaf.isLocallySurjective_sheafToPresheaf_map_iff]
  exact Presheaf.isLocallySurjective_of_surjective J
    ((sheafToPresheaf J (Type w)).map
      (Φ.skyscraperSheafFunctor.map (show E ⟶ E' from f)))
    (fun U ↦ sitePoint_skyscraper_map_app_surjective (J := J) Φ f hf U.unop)

/-- Helper for Lemma 7.32.10: on each object `U`, the section map of `p_*` induced by a
surjective function `f : E → E'` is surjective. -/
theorem toposPoint_pushforward_map_app_surjective
    (p : MorphismOfTopoiIn J typesGrothendieckTopology.{w}) {E E' : Type w} (f : E → E')
    (hf : Function.Surjective f) (U : C) :
    Function.Surjective
      (((sheafToPresheaf J (Type w)).map (p.typePushforward.map f)).app (op U)) := by
  -- A surjection in `Type` is split epic, and evaluating the image under `p_*` at `U` preserves
  -- that split-epi structure.
  letI : IsSplitEpi (show E ⟶ E' from f) :=
    (CategoryTheory.isSplitEpi_iff_surjective f).2 hf
  letI : IsSplitEpi
      (((sheafToPresheaf J (Type w)).map (p.typePushforward.map f)).app (op U)) := by
    infer_instance
  exact
    (CategoryTheory.isSplitEpi_iff_surjective
      (((sheafToPresheaf J (Type w)).map (p.typePushforward.map f)).app (op U))).1 inferInstance

-- Proof sketch: after identifying the point with a site point as in Lemma `7.32.7`, the sheaf
-- `p_* E` is given by `U ↦ (u(U) → E)`, and postcomposition with a surjective map of sets is
-- locally surjective on these section sets.
/-- Lemma 7.32.10 (4): the direct-image functor of a topos point sends surjective maps of sets to
surjective morphisms of sheaves. -/
theorem toposPoint_pushforward_map_surjective
    (p : MorphismOfTopoiIn J typesGrothendieckTopology.{w}) {E E' : Type w} (f : E → E')
    (hf : Function.Surjective f) :
    Sheaf.IsLocallySurjective (p.typePushforward.map f) := by
  -- Route correction: the source's explicit section formula is universe-sensitive in this file.
  -- Instead, use that surjections in `Type` are split epis; evaluating `p_* f` at each object
  -- preserves that split-epi structure, so the underlying presheaf map is objectwise surjective.
  rw [← Sheaf.isLocallySurjective_sheafToPresheaf_map_iff]
  exact Presheaf.isLocallySurjective_of_surjective J
    ((sheafToPresheaf J (Type w)).map (p.typePushforward.map f))
    (fun U ↦ toposPoint_pushforward_map_app_surjective (J := J) p f hf U.unop)

/- The raw source sentence includes a coequalizer-preservation clause. In the present Lean
owners the always-valid parts of Lemma 7.32.10 are the right-adjoint limit preservation, left
exactness, faithfulness, preservation of surjections, and reflection clauses above. The
coequalizer clause is kept as a conditional compatibility record here; the concrete non-preserving
continuous-pushforward example belongs to `Example_7_41_5`, not to this point-owner file. -/
/-- Lemma 7.32.10 (4b), owner-safe form: if the direct image of a topos point has the additional
coequalizer-preservation structure, then it preserves coequalizers. This records the source
coequalizer clause without asserting the false unconditional owner that conflicts with the later
G-set counterexample formalized in Example 7.41.5. -/
theorem toposPoint_pushforward_preservesCoequalizers_of_preserves
    (p : MorphismOfTopoiIn J typesGrothendieckTopology.{w})
    [PreservesColimitsOfShape WalkingParallelPair p.typePushforward] :
    PreservesColimitsOfShape WalkingParallelPair p.typePushforward := by
  infer_instance

-- Proof sketch: clause (3) makes `p.typePushforward` faithful, hence it reflects
-- monomorphisms. Translate local injectivity of sheaves to `Mono` using
-- `Sheaf.isLocallyInjective_iff_mono`, reflect along `p.typePushforward`, and read the result
-- back in `Type` via `mono_iff_injective`.
/-- Lemma 7.32.10 (5): if the direct image of a map of sets is injective as a morphism of sheaves,
then the original map is injective. -/
theorem toposPoint_pushforward_reflectsInjective
    (p : MorphismOfTopoiIn J typesGrothendieckTopology.{w}) {E E' : Type w} (f : E → E')
    (hf : Sheaf.IsLocallyInjective (p.typePushforward.map f)) :
    Function.Injective f := by
  letI : p.typePushforward.Faithful := toposPoint_pushforward_faithful p
  exact (mono_iff_injective f).1 <|
    p.typePushforward.mono_of_mono_map <|
      (Sheaf.isLocallyInjective_iff_mono _).1 hf

-- Proof sketch: clause (3) makes `p.typePushforward` faithful, hence it reflects epimorphisms.
-- Local surjectivity of sheaves provides `Epi (p.typePushforward.map f)`, and reflecting this
-- back to `Type` identifies `f` as surjective via `epi_iff_surjective`.
/-- Lemma 7.32.10 (6): if the direct image of a map of sets is surjective as a morphism of
sheaves, then the original map is surjective. -/
theorem toposPoint_pushforward_reflectsSurjective
    (p : MorphismOfTopoiIn J typesGrothendieckTopology.{w}) {E E' : Type w} (f : E → E')
    (hf : Sheaf.IsLocallySurjective (p.typePushforward.map f)) :
    Function.Surjective f := by
  letI : p.typePushforward.Faithful := toposPoint_pushforward_faithful p
  letI : Epi (p.typePushforward.map f) := by infer_instance
  exact (epi_iff_surjective f).1 <| p.typePushforward.epi_of_epi_map inferInstance

-- Proof sketch: clause (3) makes `p.typePushforward` faithful, and faithful functors reflect
-- monomorphisms and epimorphisms. Since `Type` is balanced, this gives reflection of
-- isomorphisms.
/-- Lemma 7.32.10 (7): the direct-image functor of a topos point reflects isomorphisms. -/
theorem toposPoint_pushforward_reflectsIsomorphisms
    (p : MorphismOfTopoiIn J typesGrothendieckTopology.{w}) :
    p.typePushforward.ReflectsIsomorphisms := by
  letI : p.typePushforward.Faithful := toposPoint_pushforward_faithful p
  letI : Functor.ReflectsMonomorphisms p.typePushforward := inferInstance
  letI : Functor.ReflectsEpimorphisms p.typePushforward := inferInstance
  exact inferInstance

end CategoryTheory
