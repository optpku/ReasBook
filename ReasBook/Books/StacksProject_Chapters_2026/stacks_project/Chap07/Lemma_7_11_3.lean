module

public import Mathlib.CategoryTheory.Sites.LocallySurjective
public import Mathlib.Topology.Sheaves.LocallySurjective
public import Mathlib.CategoryTheory.Sites.Sheafification
public import Mathlib.CategoryTheory.Sites.Sheaf


@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

universe u v w

namespace CategoryTheory

open Limits

attribute [local instance] Types.instFunLike Types.instConcreteCategory

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable {F G : Sheaf J (Type w)}

/-
Domain-style sampling for Lemma 7.11.3:
- primary domain: kernel pairs, effective epimorphisms, and coequalizers in the sheaf category;
- sampled owner declarations:
  `Sheaf.epi_of_isLocallySurjective`,
  `regularEpiOfEpi`,
  `isColimitCoforkOfEffectiveEpi`,
  `effectiveEpi_of_kernelPair`;
- best owner abstraction: `isColimitCoforkOfEffectiveEpi` is the canonical owner for the
  coequalizer-of-kernel-pair statement, with `Sheaf.epi_of_isLocallySurjective` as the
  sheaf-specific bridge from the source hypothesis to the categorical owner API;
- primitive data: a morphism `φ : F ⟶ G` together with the source-facing hypothesis that `φ`
  is locally surjective;
- derived API: the induced `Epi` and `EffectiveEpi` instances and the resulting colimit structure
  on the canonical kernel-pair cofork, under the ambient categorical owner hypothesis that
  `Sheaf J (Type w)` is a regular epi category.

Source/core/bridge triage:
- `source-facing`: a locally surjective morphism of sheaves of sets is the coequalizer of its
  kernel pair;
- `core/canonical`: `isColimitCoforkOfEffectiveEpi`;
- `bridge/view`: `Sheaf.epi_of_isLocallySurjective` and `regularEpiOfEpi`.
-/

namespace Sheaf

/-- Lemma 7.11.3: a locally surjective morphism of sheaves of sets is the coequalizer of the two
projections from its kernel pair. -/
noncomputable def isColimitCoforkOfIsLocallySurjective
    [IsRegularEpiCategory (Sheaf J (Type w))]
    (φ : F ⟶ G) (hφ : IsLocallySurjective φ) :
    IsColimit (Cofork.ofπ φ pullback.condition) := by
  let _ : IsLocallySurjective φ := hφ
  let _ : EffectiveEpi φ := (regularEpiOfEpi φ).effectiveEpi
  exact isColimitCoforkOfEffectiveEpi φ (pullback.cone φ φ) (pullback.isLimit φ φ)

/-- The canonical coequalizer witness attached to a locally surjective sheaf morphism agrees with
the standard effective-epimorphism coequalizer witness. -/
-- Proof sketch: unfold `isColimitCoforkOfIsLocallySurjective` and simplify the local bridge
-- instances to identify it with `isColimitCoforkOfEffectiveEpi`.
theorem isColimitCoforkOfIsLocallySurjective_spec
    [IsRegularEpiCategory (Sheaf J (Type w))]
    (φ : F ⟶ G) (hφ : IsLocallySurjective φ) :
    let _ : IsLocallySurjective φ := hφ
    let _ : EffectiveEpi φ := (regularEpiOfEpi φ).effectiveEpi
    isColimitCoforkOfIsLocallySurjective φ hφ =
      isColimitCoforkOfEffectiveEpi φ (pullback.cone φ φ) (pullback.isLimit φ φ) := by
  -- Unfold the source-facing witness so the local bridge instances reduce to the canonical one.
  rfl

end Sheaf

end CategoryTheory
