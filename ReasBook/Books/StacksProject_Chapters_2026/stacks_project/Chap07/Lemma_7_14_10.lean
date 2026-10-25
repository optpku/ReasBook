module

public import Mathlib.CategoryTheory.Sites.EffectiveEpimorphic
public import Mathlib.Topology.Sheaves.SheafCondition.Sites
public import Mathlib.Topology.Sheaves.PUnit
public import Mathlib.CategoryTheory.Sites.Sheafification
public import Mathlib.CategoryTheory.Sites.Sheaf
public import stacks_project.Chap07.Definition_7_14_1
public import stacks_project.Chap07.Definition_7_8_2

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.SemiRepresentableFamily.Over

universe u₁ u₂ v₁ v₂

namespace CategoryTheory

section

variable {C : Type u₁} [Category.{v₁} C]
variable {D : Type u₂} [Category.{v₂} D]

/- Domain-style sampling for Lemma 7.14.10:
- primary domain: representably flat functors, structured-arrow categories, and fixed-target
  covering families on a Grothendieck site;
- sampled owner API:
  `RepresentablyFlat`,
  `RepresentablyFlat.cofiltered`,
  `StructuredArrow`,
  `SemiRepresentableFamily.Over.IsCovering`,
  `SemiRepresentableFamily.Over.ofArrows`,
  `GrothendieckTopology.mem_toPrecoverage_iff`;
- source/core/bridge triage:
  `source-facing`: a covering family over `V` whose members admit maps to objects in the image of
  `u`;
  `core/canonical`: `RepresentablyFlat u`, whose owner field says every `StructuredArrow V u` is
  cofiltered and hence nonempty;
  `bridge/view`: the family covering predicate `SemiRepresentableFamily.Over.IsCovering
  K.toPrecoverage 𝒱`, derived from the generated sieve through `mem_toPrecoverage_iff`.

Primitive mathematical input data are only the topology `K`, the functor `u`, and the canonical
owner `RepresentablyFlat u`. The existence of a map from `V` to some object in the image of `u` is
derived canonically as nonemptiness of `StructuredArrow V u`. The covering family is the singleton
identity family on `V`, and its covering property should be stated using the existing family owner
`SemiRepresentableFamily.Over.IsCovering K.toPrecoverage` rather than the raw sieve-membership
bridge.
-/

/-- Lemma 7.14.10, at the canonical covering-family owner level: if `u : C ⥤ D` is representably
flat, then every object `V` of `D` admits a `K`-covering family whose members each map to some
object of the form `u.obj U` with `U : C`. -/
theorem exists_covering_family_with_maps_to_functor_images
    (K : GrothendieckTopology D) (u : C ⥤ D) [RepresentablyFlat u]
    (V : D) :
    ∃ 𝒱 : SemiRepresentableFamily.Over V,
      IsCovering K.toPrecoverage 𝒱 ∧
        ∀ i : 𝒱.index, Nonempty (StructuredArrow (𝒱.obj i).left u) := by
  -- Use the singleton identity family on `V`, which is visibly a cover and keeps the source route
  -- focused on producing image maps rather than refining the cover itself.
  let 𝒱 : SemiRepresentableFamily.Over V :=
    ofArrows (fun _ : PUnit ↦ V) (fun _ ↦ 𝟙 V)
  refine ⟨𝒱, ?_, ?_⟩
  · rw [IsCovering, GrothendieckTopology.mem_toPrecoverage_iff]
    rw [show 𝒱.toPresieve = Presieve.ofArrows (fun _ : PUnit ↦ V) (fun _ ↦ 𝟙 V) by rfl]
    rw [Presieve.ofArrows_pUnit, Sieve.generateSingleton_eq]
    -- The generated sieve of the identity arrow is the maximal sieve, so the singleton family is a
    -- `K`-covering family.
    have htop : Sieve.generateSingleton (𝟙 V) = (⊤ : Sieve V) := by
      rw [← Sieve.id_mem_iff_eq_top]
      exact ⟨𝟙 V, by simp⟩
    rw [htop]
    exact K.top_mem V
  · intro i
    -- The family has a single member, so it suffices to exhibit one map from `V` into the image of
    -- `u`, encoded canonically by a structured arrow.
    cases i
    change Nonempty (StructuredArrow V u)
    let _ : IsCofiltered (StructuredArrow V u) := inferInstance
    exact IsCofiltered.nonempty

/-- Site-morphism specialization of Lemma 7.14.10. The additional source topology `J` is used only
to obtain the canonical owner instance `RepresentablyFlat u`. -/
theorem exists_covering_family_with_maps_to_functor_images_of_isMorphismOfSites
    (J : GrothendieckTopology C) (K : GrothendieckTopology D)
    (u : C ⥤ D) [IsMorphismOfSites J K u]
    (V : D) :
    ∃ 𝒱 : SemiRepresentableFamily.Over V,
      IsCovering K.toPrecoverage 𝒱 ∧
        ∀ i : 𝒱.index, Nonempty (StructuredArrow (𝒱.obj i).left u) := by
  -- The site-morphism hypothesis packages the representable-flatness needed by the owner-level
  -- theorem, so the textbook statement is a direct specialization.
  let _ : RepresentablyFlat u := (inferInstance : IsMorphismOfSites J K u).toRepresentablyFlat
  exact exists_covering_family_with_maps_to_functor_images K u V

end

end CategoryTheory
