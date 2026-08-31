module

public import Mathlib.CategoryTheory.Sites.Plus

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Opposite

universe v u

section

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)

/- Domain-style sampling:
- primary domain: the plus construction on set-valued presheaves over a Grothendieck topology;
- sampled owner API:
  `GrothendieckTopology.plusFunctor`,
  `GrothendieckTopology.toPlus_naturality`,
  `GrothendieckTopology.toPlusNatTrans`;
- best owner abstraction: `GrothendieckTopology.toPlusNatTrans`, the natural transformation from
  the identity functor to the plus functor;
- source/core/bridge triage:
  `source-facing`: the functoriality of the canonical maps `J.toPlus P : P ⟶ J.plusObj P`;
  `core/canonical`: `GrothendieckTopology.toPlusNatTrans`;
  `bridge/view`: the componentwise naturality equation
    `GrothendieckTopology.toPlus_naturality`;
- primitive data: the topology `J`;
- derived API: the component maps `J.toPlus P` and their functoriality, packaged canonically by
  `J.toPlusNatTrans`; in the `Type`-valued specialization used here, the plus-construction
  (co)limit assumptions are discharged by existing instances and should not remain as explicit
  public hypotheses.
-/

/- Lemma 7.10.4: the assignment `ℱ ↦ (J.toPlus ℱ : ℱ ⟶ J.plusObj ℱ)` is functorial for
set-valued presheaves. Canonically, this is the `Type`-valued specialization of the natural
transformation from the identity functor to the plus functor; the commutative square for a
morphism `η : ℱ ⟶ 𝒢` is the componentwise naturality equation `J.toPlus_naturality η`. -/
#check
  (J.toPlusNatTrans (Type (max u v)) :
    𝟭 (Cᵒᵖ ⥤ Type (max u v)) ⟶ J.plusFunctor (Type (max u v)))

end
