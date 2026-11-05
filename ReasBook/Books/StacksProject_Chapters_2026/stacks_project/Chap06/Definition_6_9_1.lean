module

public import Mathlib.Topology.Sheaves.SheafCondition.EqualizerProducts
import Mathlib.Tactic.Recall

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

/- Domain-style sampling for Definition 6.9.1:
- primary domain: equalizer-form sheaf conditions for presheaves on a topological space.
- inspected canonical declarations:
  `TopCat.Presheaf.IsSheaf`,
  `TopCat.Presheaf.IsSheafEqualizerProducts`,
  `TopCat.Presheaf.isSheaf_iff_isSheafEqualizerProducts`,
  `SheafConditionEqualizerProducts.fork`.
- owner abstraction: `TopCat.Presheaf.IsSheafEqualizerProducts`.
- primitive data: only a presheaf `F : X.Presheaf C`; the equalizer diagram is derived canonically
  from `F` and an open cover.
- derived API: the comparison theorem
  `TopCat.Presheaf.isSheaf_iff_isSheafEqualizerProducts` identifying this source-facing condition
  with the official sheaf predicate `TopCat.Presheaf.IsSheaf`.

Source/core/bridge triage:
- `source-facing`: the Stacks equalizer-products sheaf condition for a presheaf on `X`.
- `core/canonical`: `TopCat.Presheaf.IsSheafEqualizerProducts`.
- `bridge/view`: the equivalence with the official owner `TopCat.Presheaf.IsSheaf` given by
  `TopCat.Presheaf.isSheaf_iff_isSheafEqualizerProducts`.

This item is already a direct recall of the canonical owner and its comparison theorem, so the
refinement should stay recall-shaped rather than introducing a duplicate local alias or `_iff`
wrapper. -/

/- Definition 6.9.1: for a `C`-valued presheaf on a topological space `X`, the Stacks equalizer
diagram condition for every open covering is the canonical mathlib predicate
`TopCat.Presheaf.IsSheafEqualizerProducts`. -/
recall TopCat.Presheaf.IsSheafEqualizerProducts

/- This source-facing equalizer-products sheaf condition is equivalent to the canonical sheaf
predicate `TopCat.Presheaf.IsSheaf`. -/
recall TopCat.Presheaf.isSheaf_iff_isSheafEqualizerProducts
