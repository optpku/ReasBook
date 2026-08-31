module

public import Mathlib.Topology.Sheaves.SheafOfFunctions
import Mathlib.Tactic.Recall

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

/- Domain-style sampling for Example 6.7.5:
- primary domain: dependent-function presheaves and their canonical sheaf packaging on a
  topological space;
- sampled owner API:
  `TopCat.presheafToTypes`,
  `TopCat.Presheaf.toTypes_isSheaf`,
  `TopCat.sheafToTypes`,
  `TopCat.presheafToTypes_obj`,
  `TopCat.presheafToTypes_map`;
- source/core/bridge triage:
  `source-facing`: the presheaf `U ↦ ∀ x : U, A x.1` with restriction by precomposition;
  `core/canonical`: the mathlib owner `TopCat.presheafToTypes`;
  `bridge/view`: the sheaf proof `TopCat.Presheaf.toTypes_isSheaf`, the packaged sheaf
    `TopCat.sheafToTypes`, and the companion object/map computation lemmas.

Primitive data are only the dependent-function presheaf itself. The sheaf proof, sheaf packaging,
and object/map formulas are derived API on that owner, so this file should stay as direct recall of
the canonical mathlib declarations rather than introducing any local wrapper or renamed copy.
-/

/- Example 6.7.5: for a family of sets `A : X → Type v` on a topological space `X`, the
presheaf `U ↦ ∀ x : U, A x.1` with restriction by precomposition along inclusions of opens is the
canonical presheaf `TopCat.presheafToTypes`. -/
recall TopCat.presheafToTypes

/- The same presheaf satisfies the sheaf condition. In mathlib this is the canonical theorem
`TopCat.Presheaf.toTypes_isSheaf`. -/
recall TopCat.Presheaf.toTypes_isSheaf

/- Companion recall: packaging the same presheaf together with its sheaf proof gives the mathlib
sheaf `TopCat.sheafToTypes`. -/
recall TopCat.sheafToTypes

/- Companion recall: the value of the underlying presheaf on an open `U` is the product of the
fibers over points of `U`, formalized as dependent functions on `U`. -/
recall TopCat.presheafToTypes_obj

/- Companion recall: the restriction maps are given by restricting a dependent function along the
inclusion of opens. -/
recall TopCat.presheafToTypes_map
