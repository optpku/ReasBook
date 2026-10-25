module

public import stacks_project.Chap06.Lemma_6_30_6

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory TopologicalSpace

noncomputable section

universe u v

variable {X : TopCat.{u}} {B : Set (Opens X)} (hB : Opens.IsBasis B)

/- Domain-style sampling for Lemma 6.30.7:
- primary domain: restriction of sheaves from a topological space to a chosen basis of opens;
- sampled owner declarations:
  `basisSheafComparisonEquiv`,
  `BasisSheaf.restrictFromSheaf`,
  `BasisSheaf.extend`,
  `basisOpenInclusion`;
- best owner abstraction: the source-facing inverse equivalence
  `(basisSheafComparisonEquiv hB).symm`, together with its canonical restriction object
  `BasisSheaf.restrictFromSheaf`;
- primitive data: only the basis witness `hB` and a sheaf on `X`;
- derived API: the restricted basis sheaf and its underlying presheaf description by
  precomposition with `(basisOpenInclusion B).op`;
- source/core/bridge triage:
  `source-facing`: restriction from sheaves on `X` to source-facing basis sheaves on `B`;
  `core/canonical`: `basisSheafComparisonEquiv hB`;
  `bridge/view`: the underlying presheaf formula for `BasisSheaf.restrictFromSheaf`.

This item adds no new owner beyond the inverse of `basisSheafComparisonEquiv hB`, so the refined
file should recall that canonical equivalence directly rather than keep a parallel local alias. -/

/- Lemma 6.30.7: for a topological space `X` and a basis `B` of open subsets, restriction to
the source-facing basis sheaf category is exactly the inverse equivalence to
`basisSheafComparisonEquiv hB`. -/
#check
  (show TopCat.Sheaf (Type (max u v)) X ≌ BasisSheaf B from
    (basisSheafComparisonEquiv hB).symm)

namespace BasisSheaf

variable {X : TopCat.{u}} {B : Set (Opens X)} {hB : Opens.IsBasis B}

/- Companion view: the restricted basis sheaf is obtained by precomposing the original sheaf with
the basis-open inclusion. -/
theorem restrictFromSheaf_obj
    (F : TopCat.Sheaf (Type (max u v)) X) :
    (restrictFromSheaf hB F).obj = (basisOpenInclusion B).op ⋙ F.presheaf :=
  rfl

end BasisSheaf

end
