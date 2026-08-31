module

public import Mathlib.Topology.Sheaves.SheafCondition.Sites
public import Mathlib.CategoryTheory.Sites.Sheafification
public import Mathlib.CategoryTheory.Sites.Sheaf
public import Mathlib.Topology.Sheaves.Sheaf
public import stacks_project.Chap06.Definition_6_30_2

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Opposite TopCat TopologicalSpace
open CategoryTheory.Limits

noncomputable section

universe v u

section

variable {C : Type v} [Category.{u} C]
variable {X : TopCat.{u}}
variable {B : Set (Opens X)}
variable (hB : Opens.IsBasis B)
variable [∀ U : (Opens X)ᵒᵖ, HasLimitsOfShape (StructuredArrow U (basisOpenInclusion B).op) C]

/- Domain-style sampling for Lemma 6.30.10:
- primary domain: dense-subsite comparison for sheaves on a topological basis;
- sampled owner abstractions:
  `basisOpenInclusion_isCoverDense`,
  `Functor.sheafPushforwardContinuous`,
  `Functor.sheafPushforwardContinuousCompSheafToPresheafIso`,
  `Functor.sheafInducedTopologyEquivOfIsCoverDense`,
  `BasisSiteSheaf`;
- best owner abstraction: the canonical dense-subsite comparison, whose inverse functor is the
  restriction functor on sheaves
  `(basisOpenInclusion B).sheafPushforwardContinuous C (basisGrothendieckTopology B hB)
    (Opens.grothendieckTopology X)`;
- primitive data: the basis-open inclusion `basisOpenInclusion B` and the induced topology
  `basisGrothendieckTopology B hB`;
- derived API: continuity of the inclusion, equivalence of the restriction functor, and its
  presheaf-level comparison isomorphism;
- source/core/bridge triage:
  `source-facing`: restriction from sheaves on `X` to sheaves on the basis `B`;
  `core/canonical`: `Functor.sheafPushforwardContinuous` together with
    `Functor.sheafPushforwardContinuousCompSheafToPresheafIso` and
    `Functor.sheafInducedTopologyEquivOfIsCoverDense`;
  `bridge/view`: the equality `BasisSiteSheaf C B = Sheaf (basisGrothendieckTopology B) C`.
-/

/- Lemma 6.30.10: if `B` is a basis for the topology on `X`, then restriction to basis opens
induces an equivalence between `C`-valued sheaves on `X` and `C`-valued sheaves on the basis
site `B`. This is the source-facing specialization of the canonical dense-subsite comparison. -/
#check
  (by
    letI : (basisOpenInclusion B).IsCoverDense (Opens.grothendieckTopology X) :=
      basisOpenInclusion_isCoverDense hB
    letI : Functor.IsContinuous (basisOpenInclusion B)
        (basisGrothendieckTopology B hB) (Opens.grothendieckTopology X) :=
      Functor.IsCoverDense.isContinuous
        (basisGrothendieckTopology B hB) (Opens.grothendieckTopology X) (basisOpenInclusion B)
        (Functor.inducedTopology_coverPreserving (basisOpenInclusion B)
          (Opens.grothendieckTopology X))
    exact
      (show Functor.IsEquivalence
          ((basisOpenInclusion B).sheafPushforwardContinuous C
            (basisGrothendieckTopology B hB) (Opens.grothendieckTopology X)) from by
        simpa using inferInstanceAs
          (((basisOpenInclusion B).sheafPushforwardContinuous C
            (basisGrothendieckTopology B hB) (Opens.grothendieckTopology X)).IsEquivalence)))

variable (ℱ : TopCat.Sheaf C X)

/- Companion view: restricting a sheaf on `X` to the basis site `B` is given on underlying
presheaves by precomposition with `(basisOpenInclusion B).op`. This is exactly the canonical
comparison isomorphism `sheafPushforwardContinuousCompSheafToPresheafIso`. -/
#check
  (by
    letI : (basisOpenInclusion B).IsCoverDense (Opens.grothendieckTopology X) :=
      basisOpenInclusion_isCoverDense hB
    letI : Functor.IsContinuous (basisOpenInclusion B)
        (basisGrothendieckTopology B hB) (Opens.grothendieckTopology X) :=
      Functor.IsCoverDense.isContinuous
        (basisGrothendieckTopology B hB) (Opens.grothendieckTopology X) (basisOpenInclusion B)
        (Functor.inducedTopology_coverPreserving (basisOpenInclusion B)
          (Opens.grothendieckTopology X))
    exact
      (show (((basisOpenInclusion B).sheafPushforwardContinuous C
          (basisGrothendieckTopology B hB) (Opens.grothendieckTopology X)).obj ℱ).obj ≅
            (basisOpenInclusion B).op ⋙ ℱ.presheaf from by
        simpa using
          ((basisOpenInclusion B).sheafPushforwardContinuousCompSheafToPresheafIso C
            (basisGrothendieckTopology B hB) (Opens.grothendieckTopology X)).app ℱ))

end
