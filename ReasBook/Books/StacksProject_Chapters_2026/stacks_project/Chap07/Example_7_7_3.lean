module

public import Mathlib.Topology.Sheaves.SheafCondition.OpensLeCover
import Mathlib.Tactic.Recall

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

variable (X : TopCat.{u}) (F : X.Presheaf (Type v))

/- Source/core/bridge triage for Example 7.7.3:
- primary domain: sheaves of sets on a topological space and on its opens site
- sampled canonical declarations:
  `CategoryTheory.Sheaf`,
  `TopCat.Sheaf`,
  `TopCat.Presheaf.IsSheaf`,
  `TopCat.Presheaf.isSheaf_iff_isSheafOpensLeCover`
- source-facing layer: identify the sheaf category on `X_{Zar}` with the usual sheaf category on `X`
- core/canonical owners: `TopCat.Sheaf` and `TopCat.Presheaf.IsSheaf`
- bridge/view: the opens-site comparison theorem
  `TopCat.Presheaf.isSheaf_iff_isSheafOpensLeCover`
- primitive data: a presheaf on `X`
- derived API: the sheaf predicate and the corresponding full subcategory
-/

/- Example 7.7.3: for a topological space `X`, the category of sheaves of sets on the site
`X_{Zar}` is the usual category `X.Sheaf (Type v)`. -/
#check (X.Sheaf (Type v))

/- The usual sheaf predicate on a presheaf over `X` is the owner
`TopCat.Presheaf.IsSheaf`. -/
#check F.IsSheaf

/- For a presheaf on a topological space, the site-theoretic sheaf condition for the opens site is
equivalent to the usual open-cover sheaf condition. -/
recall TopCat.Presheaf.isSheaf_iff_isSheafOpensLeCover
