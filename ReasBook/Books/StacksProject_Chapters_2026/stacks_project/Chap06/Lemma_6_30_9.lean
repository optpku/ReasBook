module

public import stacks_project.Chap06.Definition_6_30_2

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Opposite TopCat TopologicalSpace
open CategoryTheory.Limits

noncomputable section

universe u

section

variable {X : TopCat.{u}}
variable {C : Type u} [Category.{u} C]
variable {B : Set (Opens X)}
variable (hB : Opens.IsBasis B)
variable [∀ U : (Opens X)ᵒᵖ, HasLimitsOfShape (StructuredArrow U (basisOpenInclusion B).op) C]

/-
Domain-style sampling for Lemma 6.30.9:
- primary domain: dense-subsite comparison for sheaves on a topological basis;
- inspected owner declarations:
  `Functor.sheafInducedTopologyEquivOfIsCoverDense`,
  `basisOpenInclusion_isCoverDense`,
  `basisGrothendieckTopology`,
  `BasisSiteSheaf`;
- source/core/bridge triage:
  `source-facing`: extension and uniqueness for a sheaf on the basis `B`;
  `core/canonical`: `Functor.sheafInducedTopologyEquivOfIsCoverDense`;
  `bridge/view`: the identification of `BasisSiteSheaf C B` with sheaves on the induced topology
  from `basisOpenInclusion B`.

Primitive data is only the basis-site sheaf category `BasisSiteSheaf C B`. The extension object
and uniqueness statement are derived from the dense-subsite equivalence, so the public entry should
be that bridge rather than a parallel local existential or chosen-extension wrapper.
-/

/- Lemma 6.30.9: for a topological basis `B`, sheaves on the basis site and sheaves on `X` are
equivalent. This is the source-facing specialization of the canonical dense-subsite comparison
`(basisOpenInclusion B).sheafInducedTopologyEquivOfIsCoverDense`. -/
#check
  (show BasisSiteSheaf C B hB ≌ TopCat.Sheaf C X from by
    letI : (basisOpenInclusion B).IsCoverDense (Opens.grothendieckTopology X) :=
      basisOpenInclusion_isCoverDense hB
    change Sheaf (basisGrothendieckTopology B hB) C ≌ TopCat.Sheaf C X
    exact
      (basisOpenInclusion B).sheafInducedTopologyEquivOfIsCoverDense
        (Opens.grothendieckTopology X) C)

end
