module

public import Mathlib.CategoryTheory.Functor.EpiMono
public import Mathlib.CategoryTheory.Sites.CoverLifting
public import Mathlib.CategoryTheory.Sites.PreservesLocallyBijective
public import stacks_project.Chap07.Lemma_7_11_2
@[expose] public section

open CategoryTheory

universe v₁ v₂ u₁ u₂ w

namespace CategoryTheory.Functor

section

attribute [local instance] Types.instFunLike Types.instConcreteCategory

/- Domain-style sampling for Lemma 7.41.2:
- primary domain: sheaf pushforward along continuous/cocontinuous site functors and preservation
  of surjective/epic morphisms;
- sampled owner API:
  `Functor.PreservesEpimorphisms`,
  `Sheaf.IsLocallySurjective`,
  `Sheaf.isLocallySurjective_iff_epi`,
  `Sheaf.isLocallySurjective_sheafToPresheaf_map_iff`,
  `Functor.sheafPushforwardContinuous`,
  `Presheaf.isLocallySurjective_whisker`,
- source/core/bridge triage:
  `source-facing`: the direct-image statement for surjective morphisms of sheaves of types;
  `core/canonical`: the owner property
  `(F.sheafPushforwardContinuous (Type w) J K).PreservesEpimorphisms`;
  `bridge/view`: the sheaf-level predicate `Sheaf.IsLocallySurjective` together with the
  chapter's canonical bridge
  `Sheaf.isLocallySurjective_sheafToPresheaf_map_iff` and the presheaf-level whiskering lemma
  `Presheaf.isLocallySurjective_whisker`.

Primitive data are the sites, the continuous/cocontinuous functor, and the locally surjective
sheaf morphism. The induced locally surjective presheaf map is derived API from
`Presheaf.isLocallySurjective_whisker`. The source-facing theorem below therefore stays the main
entry because it preserves the original assumption set, while the sheaf-level instance and the
owner-level `PreservesEpimorphisms` companion are derived from it under the extra `HasSheafify`
bridge needed to pass from `Epi` to `Sheaf.IsLocallySurjective`.
-/

variable {C : Type u₁} [Category.{v₁} C]
variable {D : Type u₂} [Category.{v₂} D]
variable (J : GrothendieckTopology C) (K : GrothendieckTopology D) (F : C ⥤ D)
variable [Functor.IsContinuous F J K] [F.IsCocontinuous J K]
variable {ℱ 𝒢 : Sheaf K (Type w)} (a : ℱ ⟶ 𝒢)

/-- Lemma 7.41.2: if a continuous functor between sites also lifts covering families along
the induced pushforward on sheaves, then the pushforward sends surjective morphisms of sheaves
of types to surjective morphisms. In this site-level formalization, surjectivity is expressed by
`Sheaf.IsLocallySurjective`. -/
theorem sheafPushforwardContinuous_map_isLocallySurjective
    (ha : Sheaf.IsLocallySurjective a) :
    Sheaf.IsLocallySurjective ((F.sheafPushforwardContinuous (Type w) J K).map a) := by
  -- View the sheaf statement on underlying presheaves, where pushforward is whiskering by `F.op`.
  letI : Sheaf.IsLocallySurjective a := ha
  rw [← Sheaf.isLocallySurjective_sheafToPresheaf_map_iff]
  -- Cocontinuity lifts the local surjectivity witness along the whiskered presheaf map.
  simpa using Presheaf.isLocallySurjective_whisker J K F a.hom

instance [Sheaf.IsLocallySurjective a] :
    Sheaf.IsLocallySurjective ((F.sheafPushforwardContinuous (Type w) J K).map a) :=
  sheafPushforwardContinuous_map_isLocallySurjective J K F a inferInstance

/-- Owner-level companion to Lemma 7.41.2: when surjective morphisms of sheaves of types are read
categorically as epimorphisms, the pushforward functor along a continuous and cocontinuous site
functor preserves them. -/
instance sheafPushforwardContinuous_preservesEpimorphisms [HasSheafify K (Type w)] :
    (F.sheafPushforwardContinuous (Type w) J K).PreservesEpimorphisms where
  preserves a _ := by
    -- Rewrite the input epimorphism into the source-facing local-surjectivity predicate.
    letI : Sheaf.IsLocallySurjective a := (Sheaf.isLocallySurjective_iff_epi a).2 inferInstance
    -- Apply Lemma 7.41.2 to obtain local surjectivity after pushforward.
    letI : Sheaf.IsLocallySurjective ((F.sheafPushforwardContinuous (Type w) J K).map a) :=
      sheafPushforwardContinuous_map_isLocallySurjective J K F a inferInstance
    -- Translate back to the categorical `Epi` formulation.
    infer_instance

end

end CategoryTheory.Functor
