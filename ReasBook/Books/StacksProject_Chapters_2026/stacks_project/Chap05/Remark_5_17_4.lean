module

import stacks_project.Chap05.Lemma_5_17_3
import Mathlib.Tactic.Recall
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Topology.MetricSpace.Pseudo.Defs

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

/- Domain-style sampling for compactness via closed product projections:
- owner predicates in this domain: `IsClosedMap`, `IsProperMap`
- relevant mathlib bridge theorems:
  `isClosedMap_fst_of_compactSpace`,
  `isProperMap_const_iff`,
  `isProperMap_iff_universally_closed`
- source-facing chapter theorem: `compactSpace_iff_forall_isClosedMap_fst`

Layer triage:
- `source-facing`: `compactSpace_iff_forall_isClosedMap_fst`
- `core/canonical`: proper maps and their universally-closed product characterization
- `bridge/view`: the compactness criterion phrased through closedness of `Prod.fst`

Primitive data belongs to the owner layer: compactness, properness, and closedness of the product
projection. The Stacks remark itself is only bibliographic, pointing to Bourbaki as the proof
source for the already-formalized criterion. So this file should stay a direct recall of the
chapter theorem rather than introduce any parallel wrapper or proof-packaging declaration.
-/

/- Remark 5.17.4 is bibliographic: it says that the proof of Lemma 5.17.3 is a combination of
[Bou71, I, p. 75, Lemme 1] and [Bou71, I, p. 76, Corollaire 1]. The formal mathematical content
of the surrounding discussion is already the source-facing theorem
`compactSpace_iff_forall_isClosedMap_fst`. -/
recall compactSpace_iff_forall_isClosedMap_fst
