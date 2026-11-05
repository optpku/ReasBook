module

public import Mathlib.Topology.Sheaves.SheafCondition.OpensLeCover
import Mathlib.Tactic.Recall

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

/- Domain-style sampling for Example 7.6.4:
- primary domain: the canonical site on the opens category of a topological space and the
  corresponding sheaf condition for presheaves on that site;
- sampled owner API:
  `Opens.pretopology`,
  `Opens.grothendieckTopology`,
  `Opens.pretopology_toGrothendieck`,
  `TopCat.Presheaf.isSheaf_iff_isSheafOpensLeCover`;
- source/core/bridge triage:
  `source-facing`: the textbook description of the opens site by covering families
  `{Uᵢ ⟶ U}` with `iSup Uᵢ = U`, together with the usual open-cover sheaf condition;
  `core/canonical`: the mathlib owners `Opens.pretopology`, `Opens.grothendieckTopology`, and
  `TopCat.Presheaf.isSheaf_iff_isSheafOpensLeCover`;
  `bridge/view`: the theorem `Opens.pretopology_toGrothendieck`, which identifies the
  source-facing covering-family presentation with the canonical opens-site Grothendieck topology.

Primitive data are just the topological space and its opens category. The covering-family and
usual-sheaf-condition phrasing are derived views of the upstream owners, so this file should remain
a pure recall file rather than introduce chapter-local aliases or wrapper definitions.
-/

/- Example 7.6.4: for a topological space `X`, the category of open subsets of `X` with
inclusion morphisms and covering families `{Uᵢ ⟶ U}` satisfying `⋃ i, Uᵢ = U` is the canonical
pretopology `Opens.pretopology` on the opens category. In particular, the empty open and the
empty covering of `⊥` are allowed. -/
recall Opens.pretopology

/- The associated site on the category of open subsets is the canonical Grothendieck topology
`Opens.grothendieckTopology`. -/
recall Opens.grothendieckTopology

/- The source-facing opens-covering pretopology induces that canonical Grothendieck topology. -/
recall Opens.pretopology_toGrothendieck

/- For a presheaf on a topological space, the site-theoretic sheaf condition for the opens site is
equivalent to the usual open-cover sheaf condition. -/
recall TopCat.Presheaf.isSheaf_iff_isSheafOpensLeCover
