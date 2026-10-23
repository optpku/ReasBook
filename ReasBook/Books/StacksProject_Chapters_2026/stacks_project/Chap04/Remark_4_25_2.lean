module

public import Mathlib.Algebra.Category.Grp.Adjunctions
import Mathlib.Tactic.Recall
public import Mathlib.Topology.Category.TopCat.Limits.Basic

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

/- Domain-style sampling for Remark 4.25.2:
- primary domain: categorical examples of adjunctions and colimits.
- inspected owner-level declarations:
  `GrpCat.adj`,
  `AddCommGrpCat.adj`,
  `TopCat.topCat_hasColimits`.
- best owner abstraction: the existing mathlib owner declarations above, with no additional local
  wrapper layer.

Primitive-vs-derived split:
- primitive data: none in this recall-only remark.
- derived API: the source examples are already packaged by the canonical adjunction and colimit
  owners in mathlib.

Source/core/bridge triage:
- `source-facing`: the textbook examples "free group", "free abelian group", and "topological
  spaces admit small colimits".
- `core/canonical`: `GrpCat.adj`, `AddCommGrpCat.adj`, and `TopCat.topCat_hasColimits`.
- `bridge/view`: none needed here, since the source statements are direct recalls of the canonical
  owners. -/

/- Remark 4.25.2: the free group on a set is the canonical left adjoint
`GrpCat.free : Type u ⥤ GrpCat` to the forgetful functor `forget GrpCat`, so its universal
property is packaged by the adjunction `GrpCat.adj`. -/
recall GrpCat.adj

/- Companion recall: the free abelian group example is expressed canonically by the adjunction
`AddCommGrpCat.free ⊣ forget AddCommGrpCat`. -/
recall AddCommGrpCat.adj

/- Companion recall: every small diagram of topological spaces has a colimit via the canonical
instance `TopCat.topCat_hasColimits`. -/
recall TopCat.topCat_hasColimits
