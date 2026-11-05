module

public import Mathlib.CategoryTheory.Sites.LocallySurjective
public import Mathlib.Topology.Sheaves.LocallySurjective
public import Mathlib.CategoryTheory.Sites.Sheafification
public import Mathlib.CategoryTheory.Sites.Sheaf
public import Mathlib.Topology.Sheaves.Presheaf
public import stacks_project.Chap06.Definition_6_16_2

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Opposite TopCat TopologicalSpace

universe u

section

/- Domain-style sampling for Lemma 6.17.6:
- primary domain: local surjectivity and local injectivity of sheafified morphisms of set-valued
  presheaves on a topological space;
- inspected owner declarations:
  `Presheaf.isLocallySurjective_presheafToSheaf_map_iff`,
  `Presheaf.isLocallyInjective_presheafToSheaf_map_iff`,
  `Sheaf.mono_of_isLocallyInjective`,
  `presheaf_epi_iff_app_surjective`,
  `presheaf_mono_iff_app_injective`;
- best owner abstraction: the sheafification comparison theorems for local surjectivity and local
  injectivity together with the canonical bridge `Sheaf.mono_of_isLocallyInjective`; the public
  source-facing outputs are `Sheaf.IsLocallySurjective` in the surjective half and `Mono` in the
  injective half.

Source/core/bridge triage:
- `source-facing`: the textbook statement that sheafification sends sectionwise surjective or
  injective presheaf maps to locally surjective or injective sheaf maps;
- `core/canonical`: the owner equivalences
  `Presheaf.isLocallySurjective_presheafToSheaf_map_iff` and
  `Presheaf.isLocallyInjective_presheafToSheaf_map_iff`, with `Sheaf.IsLocallyInjective` as the
  internal proof owner on the sheaf side;
- `bridge/view`: the Chapter 6 bridge theorems `presheaf_epi_iff_app_surjective` and
  `presheaf_mono_iff_app_injective`, which convert the source `Epi`/`Mono` hypotheses into the
  pointwise input used by the core owners, and the canonical implication
  `Sheaf.mono_of_isLocallyInjective`.

Primitive-vs-derived split:
- primitive data: a morphism `φ : F ⟶ G` of set-valued presheaves;
- owner predicates: local surjectivity or local injectivity of `φ` and of its sheafification map;
- derived source-facing API: the `Epi φ` and `Mono φ` hypotheses from the canonical categorical
  owners for set-valued presheaves.

The exact `Epi`/`Mono` to sectionwise surjectivity/injectivity bridge already lives upstream in
Definition 6.16.2, so this file only applies that chapter owner API to the sheafification
comparison.
-/

attribute [local instance] Types.instFunLike Types.instConcreteCategory

variable {X : TopCat.{u}}
variable [HasWeakSheafify (Opens.grothendieckTopology X) (Type u)]
local notation "J" => Opens.grothendieckTopology X
variable {F G : X.Presheaf (Type u)} (φ : F ⟶ G)

-- Proof sketch: rewrite local surjectivity and local injectivity of the sheafified morphism using
-- `Presheaf.isLocallySurjective_presheafToSheaf_map_iff` and
-- `Presheaf.isLocallyInjective_presheafToSheaf_map_iff`, then use the Chapter 6 bridge theorems
-- `presheaf_epi_iff_app_surjective` and `presheaf_mono_iff_app_injective` to reduce to the
-- elementary presheaf theorems
-- `Presheaf.isLocallySurjective_of_surjective` and
-- `Presheaf.isLocallyInjective_of_injective`; in the injective half, conclude with
-- `Sheaf.mono_of_isLocallyInjective`.
/-- Lemma 6.17.6 (surjective case): sheafification sends an epimorphism, equivalently a
sectionwise surjective morphism, of presheaves of sets on `X` to a locally surjective morphism of
sheaves. -/
theorem isLocallySurjective_presheafToSheaf_map_of_epi
    (hφ : Epi φ) :
    Sheaf.IsLocallySurjective
      ((presheafToSheaf J (Type u)).map φ) := by
  simpa [Presheaf.isLocallySurjective_presheafToSheaf_map_iff] using
    Presheaf.isLocallySurjective_of_surjective J φ
      (fun U ↦ (presheaf_epi_iff_app_surjective φ).1 hφ U.unop)

/-- Lemma 6.17.6 (injective case): sheafification sends a monomorphism, equivalently a
sectionwise injective morphism, of presheaves of sets on `X` to a monomorphism of sheaves. -/
theorem mono_presheafToSheaf_map_of_mono
    (hφ : Mono φ) :
    Mono ((presheafToSheaf J (Type u)).map φ) := by
  letI : Sheaf.IsLocallyInjective ((presheafToSheaf J (Type u)).map φ) := by
    simpa [Presheaf.isLocallyInjective_presheafToSheaf_map_iff] using
      Presheaf.isLocallyInjective_of_injective J φ
        (fun U ↦ (presheaf_mono_iff_app_injective φ).1 hφ U.unop)
  exact Sheaf.mono_of_isLocallyInjective ((presheafToSheaf J (Type u)).map φ)

end
