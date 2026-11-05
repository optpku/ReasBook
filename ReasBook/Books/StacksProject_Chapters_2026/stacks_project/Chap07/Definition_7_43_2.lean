module

public import Mathlib.CategoryTheory.Sites.LeftExact
public import Mathlib.CategoryTheory.Sites.Sheafification
public import Mathlib.CategoryTheory.Sites.Sheaf
public import stacks_project.Chap07.Definition_7_43_1

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

universe u₁ u₂ v₁ v₂ w

namespace CategoryTheory

open CategoryTheory.Limits
open scoped MorphismOfTopoiIn

section

variable {C : Type u₁} [Category.{v₁} C] (J : GrothendieckTopology C)

/- Domain-style sampling for Definition 7.43.2:
- primary domain: subtopoi presented as essential images of direct-image functors of embeddings of
  topoi;
- sampled owner API:
  `MorphismOfTopoiIn.IsEmbedding`,
  `Functor.essImage`,
  `Functor.obj_mem_essImage`,
  `ObjectProperty.IsClosedUnderIsomorphisms`;
- best owner abstraction: the canonical object property `(f _*).essImage` attached to the
  pushforward functor of an embedding `f`;
- primitive data: the existence of a site-presented embedding whose pushforward has essential image
  `E`;
- derived API: closure of a subtopos under isomorphisms and the ambient-topos example.

Source/core/bridge triage:
- `source-facing`: `IsSubtopos`;
- `core/canonical`: `Functor.essImage` and `MorphismOfTopoiIn.IsEmbedding`;
- `bridge/view`: the chapter-level predicate asserting that an object property is the essential
  image of the pushforward of some embedding. -/
/-- Definition 7.43.2: a strictly full subcategory `E ⊆ Sh(𝒞)` is a subtopos if it is the
essential image of the direct-image functor of some embedding of topoi into `Sh(𝒞)`. -/
def IsSubtopos (E : ObjectProperty (Sheaf J (Type w))) : Prop :=
  ∃ (D : Type u₂) (_ : Category.{v₂} D) (K : GrothendieckTopology D)
    (f : MorphismOfTopoiIn J K) (_ : f.IsEmbedding), E = (f _*).essImage

namespace MorphismOfTopoiIn

variable {D : Type u₂} [Category.{v₂} D] {K : GrothendieckTopology D}

/-- The essential image of the direct-image functor of an embedding of topoi is a subtopos. -/
theorem isSubtopos_essImage (f : MorphismOfTopoiIn J K) [f.IsEmbedding] :
    IsSubtopos.{u₁, u₂, v₁, v₂, w} J (f _*).essImage := by
  exact ⟨D, inferInstance, K, f, inferInstance, rfl⟩

end MorphismOfTopoiIn

/-- A subtopos is strictly full. -/
instance isClosedUnderIsomorphisms_of_isSubtopos
    (E : ObjectProperty (Sheaf J (Type w))) (hE : IsSubtopos J E) :
    E.IsClosedUnderIsomorphisms := by
  rcases hE with ⟨_, _, _, f, _, rfl⟩
  infer_instance

/-- A subtopos is strictly full. -/
theorem IsSubtopos.isClosedUnderIsomorphisms
    {E : ObjectProperty (Sheaf J (Type w))} (hE : IsSubtopos J E) :
    E.IsClosedUnderIsomorphisms := by
  let _ := isClosedUnderIsomorphisms_of_isSubtopos J E hE
  infer_instance

/-- The ambient sheaf topos `Sh(𝒞)` is a subtopos of itself, presented by the identity embedding
of topoi. -/
theorem isSubtopos_top :
    IsSubtopos.{u₁, u₁, v₁, v₁, w} J (⊤ : ObjectProperty (Sheaf J (Type w))) := by
  refine ⟨C, inferInstance, J, MorphismOfTopoiIn.id J, inferInstance, ?_⟩
  ext F
  constructor
  · intro _
    simpa using Functor.obj_mem_essImage (𝟭 (Sheaf J (Type w))) F
  · intro _
    trivial

end

end CategoryTheory
