module

public import Mathlib.CategoryTheory.Sites.LeftExact
public import Mathlib.CategoryTheory.Sites.Sheafification
public import Mathlib.CategoryTheory.Sites.Sheaf
public import stacks_project.Chap07.Definition_7_15_1_Topoi

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

universe u₁ u₂ v₁ v₂ w

namespace CategoryTheory

open scoped MorphismOfTopoiIn

/- Domain-style sampling for Definition 7.43.1:
- primary domain: site-presented morphisms of topoi and fully faithful direct-image functors;
- sampled owner API:
  `Functor.Full`,
  `Functor.Faithful`,
  `Functor.FullyFaithful.ofFullyFaithful`,
  `Adjunction.counit_isIso_of_R_fully_faithful`;
- best owner abstraction: the site-presented morphism `f : MorphismOfTopoiIn J K`, with canonical
  functor-level owners `(f _*).Full`, `(f _*).Faithful`, and derived structure
  `(f _*).FullyFaithful`;
- primitive data: the source-facing property that `f _*` is full and faithful;
- derived API: the bundled `FullyFaithful` structure on `f _*` and the adjunction consequences it
  implies.

Source/core/bridge triage:
- `source-facing`: `MorphismOfTopoiIn.IsEmbedding`;
- `core/canonical`: `Functor.Full`, `Functor.Faithful`, and `Functor.FullyFaithful` on `f _*`;
- `bridge/view`: the fully faithful structure on `f _*` is derived from the source-facing
  proposition rather than stored as primitive data.
-/
namespace MorphismOfTopoiIn

variable {C : Type u₁} [Category.{v₁} C]
variable {D : Type u₂} [Category.{v₂} D]
variable {J : GrothendieckTopology C} {K : GrothendieckTopology D}

/-- Definition 7.43.1: a morphism of topoi `f : Sh(𝒟) ⟶ Sh(𝒞)` is an embedding when its
direct-image functor `f_*` is full and faithful. -/
@[mk_iff isEmbedding_iff_pushforwardFull_and_faithful]
class IsEmbedding (f : MorphismOfTopoiIn J K) : Prop extends (f _*).Full, (f _*).Faithful

/-- For an embedding of topoi, the direct-image functor `f_*` is fully faithful in the canonical
bundled sense. -/
noncomputable instance (f : MorphismOfTopoiIn J K) [f.IsEmbedding] : (f _*).FullyFaithful :=
  .ofFullyFaithful (f _*)

/-- The identity morphism of the topos `Sh(𝒞)` is an embedding. -/
instance id_isEmbedding (J : GrothendieckTopology C) :
    IsEmbedding (id J) where
  toFull := (Functor.FullyFaithful.id _).full
  toFaithful := (Functor.FullyFaithful.id _).faithful

end MorphismOfTopoiIn

end CategoryTheory
