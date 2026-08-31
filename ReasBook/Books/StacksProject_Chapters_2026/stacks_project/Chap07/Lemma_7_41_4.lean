module

public import Mathlib.CategoryTheory.Sites.LocallySurjective
public import Mathlib.Topology.Sheaves.LocallySurjective
public import Mathlib.CategoryTheory.Sites.Sheafification
public import Mathlib.CategoryTheory.Sites.Sheaf
public import Mathlib.CategoryTheory.Sites.PreservesLocallyBijective
public import stacks_project.Chap07.Definition_7_13_1
public import stacks_project.Chap07.Lemma_7_11_2

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits

universe u₁ u₂ v₁ v₂ w

section

variable {C : Type u₁} [Category.{v₁} C]
variable {D : Type u₂} [Category.{v₂} D]
variable {J : Precoverage C} {K : Precoverage D}
variable [J.HasIsos] [J.IsStableUnderBaseChange] [J.IsStableUnderComposition] [J.HasPullbacks]
variable [K.IsStableUnderBaseChange] [K.HasPullbacks]
variable (F : C ⥤ D)
variable [Functor.IsContinuousSiteFunctor F J K] [F.IsCoverDense (Precoverage.toGrothendieck K)]

attribute [local instance] Types.instFunLike Types.instConcreteCategory

local notation "Jᵣ" => Precoverage.toGrothendieck J
local notation "Kᵣ" => Precoverage.toGrothendieck K

/- Domain-style sampling for Lemma 7.41.4:
- primary domain: reflection of local injectivity and surjectivity along a cover-dense
  continuous functor of sites and the induced sheaf pushforward;
- sampled owner API:
  `Functor.sheafPushforwardContinuous`,
  `Presheaf.isLocallyInjective_of_whisker`,
  `Presheaf.isLocallySurjective_of_whisker`,
  `Sheaf.isLocallyInjective_iff_mono`,
  `Sheaf.isLocallySurjective_iff_epi`;
- source/core/bridge triage:
  `source-facing`: the Stacks assertions that the direct image along such a functor reflects
  injective and surjective morphisms of sheaves of sets;
  `core/canonical`: the owner properties
  `(F.sheafPushforwardContinuous (Type w) Jᵣ Kᵣ).ReflectsMonomorphisms` and
  `(F.sheafPushforwardContinuous (Type w) Jᵣ Kᵣ).ReflectsEpimorphisms`;
  `bridge/view`: the sheaf-local predicates `Sheaf.IsLocallyInjective` and
  `Sheaf.IsLocallySurjective`, together with the presheaf whiskering descent lemmas.

Primitive data are only the site functor `F` and the cover-dense/continuous hypotheses. The
locally injective and locally surjective presheaf statements are derived bridge API, so the
refinement below keeps the same source-faithful hypotheses while simplifying the descent proofs to
the minimal canonical whiskering lemmas.
-/

/-- Lemma 7.41.4 (1): if every object of `D` admits a covering by objects in the image of `u`,
then the pushforward functor on sheaves of sets along `u` reflects monomorphisms; equivalently,
it reflects injective morphisms of sheaves. -/
instance sheafPushforwardContinuous_reflectsMonomorphisms :
    (F.sheafPushforwardContinuous (Type w) Jᵣ Kᵣ).ReflectsMonomorphisms where
  reflects a ha := by
    let hF : CoverPreserving Jᵣ Kᵣ F :=
      (inferInstance : Functor.IsContinuousSiteFunctor F J K).coverPreserving
    rw [← Sheaf.isLocallyInjective_iff_mono a]
    letI : Presheaf.IsLocallyInjective Jᵣ (F.op.whiskerLeft a.hom) := by
      have : Sheaf.IsLocallyInjective ((F.sheafPushforwardContinuous (Type w) Jᵣ Kᵣ).map a) :=
        (Sheaf.isLocallyInjective_iff_mono _).2 ha
      simpa [Sheaf.isLocallyInjective_sheafToPresheaf_map_iff] using this
    simpa using
      (Presheaf.isLocallyInjective_of_whisker Jᵣ Kᵣ F a.hom hF)

/-- Lemma 7.41.4 (2): if every object of `D` admits a covering by objects in the image of `u`,
then the pushforward functor on sheaves of sets along `u` reflects epimorphisms; equivalently,
it reflects surjective morphisms of sheaves. -/
instance sheafPushforwardContinuous_reflectsEpimorphisms
    [HasSheafify Jᵣ (Type w)] :
    (F.sheafPushforwardContinuous (Type w) Jᵣ Kᵣ).ReflectsEpimorphisms where
  reflects a ha := by
    let hF : CoverPreserving Jᵣ Kᵣ F :=
      (inferInstance : Functor.IsContinuousSiteFunctor F J K).coverPreserving
    letI : Presheaf.IsLocallySurjective Jᵣ (F.op.whiskerLeft a.hom) := by
      have : Sheaf.IsLocallySurjective ((F.sheafPushforwardContinuous (Type w) Jᵣ Kᵣ).map a) :=
        (Sheaf.isLocallySurjective_iff_epi _).2 ha
      simpa [Sheaf.isLocallySurjective_sheafToPresheaf_map_iff] using this
    letI : Sheaf.IsLocallySurjective a := by
      simpa using
        (Presheaf.isLocallySurjective_of_whisker Jᵣ Kᵣ F a.hom hF)
    infer_instance

end
