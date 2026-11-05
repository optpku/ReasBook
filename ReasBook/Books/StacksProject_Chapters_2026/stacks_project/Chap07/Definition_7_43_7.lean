module

public import Mathlib.CategoryTheory.Sites.LeftExact
public import Mathlib.CategoryTheory.Sites.Sheafification
public import Mathlib.CategoryTheory.Sites.Sheaf
public import stacks_project.Chap07.Definition_7_43_1
public import stacks_project.Chap07.Definition_7_43_4
public import stacks_project.Chap07.Definition_7_43_6

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

universe u₁ u₂ v₁ v₂ w

namespace CategoryTheory

open scoped MorphismOfTopoiIn

namespace MorphismOfTopoiIn

variable {C : Type u₁} [Category.{v₁} C]
variable {D : Type u₂} [Category.{v₂} D]
variable {J : GrothendieckTopology C} {K : GrothendieckTopology D}

/- Domain-style sampling for Definition 7.43.7:
- primary domain: open and closed immersions of topoi, expressed through the essential image of
  the direct-image functor of a morphism of topoi;
- sampled owner API:
  `MorphismOfTopoiIn.IsEmbedding`,
  `Functor.essImage`,
  `IsOpenSubtopos`,
  `IsClosedSubtopos`;
- best owner abstraction: the source-facing owner classes `MorphismOfTopoiIn.IsOpenImmersion` and
  `MorphismOfTopoiIn.IsClosedImmersion` on a fixed morphism of topoi `f`, with the functorial
  essential image `(f _*).essImage` supplying the canonical subtopos datum;
- primitive data: the embedding hypothesis on `f` together with the open- or closed-subtopos
  predicate on `(f _*).essImage`;
- derived API: the inherited embedding instance and typeclass access to the open/closed-subtopos
  consequence.

Source/core/bridge triage:
- `source-facing`: `MorphismOfTopoiIn.IsOpenImmersion` and
  `MorphismOfTopoiIn.IsClosedImmersion`;
- `core/canonical`: `MorphismOfTopoiIn.IsEmbedding`, `Functor.essImage`, `IsOpenSubtopos`, and
  `IsClosedSubtopos`;
- `bridge/view`: the instance-level access from an immersion hypothesis to the corresponding
  subtopos predicate on the essential image of `f _*`. -/
/-- Definition 7.43.7 (1): a morphism of topoi `f : Sh(𝒟) ⟶ Sh(𝒞)` is an open immersion if it is
an embedding and the essential image of `f_*` is an open subtopos of `Sh(𝒞)`. -/
@[mk_iff isOpenImmersion_iff_embedding_and_openSubtopos]
class IsOpenImmersion (f : MorphismOfTopoiIn J K) : Prop extends IsEmbedding f where
  /-- The essential image of the direct-image functor of an open immersion is an open subtopos. -/
  isOpenSubtopos : IsOpenSubtopos (f _*).essImage

/-- Definition 7.43.7 (2): a morphism of topoi `f : Sh(𝒟) ⟶ Sh(𝒞)` is a closed immersion if it
is an embedding and the essential image of `f_*` is a closed subtopos of `Sh(𝒞)`. -/
@[mk_iff isClosedImmersion_iff_embedding_and_closedSubtopos]
class IsClosedImmersion (f : MorphismOfTopoiIn J K) : Prop extends IsEmbedding f where
  /-- The essential image of the direct-image functor of a closed immersion is a closed subtopos. -/
  isClosedSubtopos : IsClosedSubtopos (f _*).essImage

instance (f : MorphismOfTopoiIn J K) [hf : f.IsOpenImmersion] :
    IsOpenSubtopos (f _*).essImage :=
  hf.isOpenSubtopos

instance (f : MorphismOfTopoiIn J K) [hf : f.IsClosedImmersion] :
    IsClosedSubtopos (f _*).essImage :=
  hf.isClosedSubtopos

end MorphismOfTopoiIn

end CategoryTheory
