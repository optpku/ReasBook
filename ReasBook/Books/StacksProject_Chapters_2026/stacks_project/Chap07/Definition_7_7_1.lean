module

public import Mathlib.CategoryTheory.Sites.Sheaf
import Mathlib.Tactic.Recall

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open Equalizer.Presieve.Arrows

/- Domain-style sampling for Definition 7.7.1:
- primary domain: sheaf conditions for set-valued presheaves on a Grothendieck site;
- sampled owner API:
  `Presieve.IsSheaf`,
  `Equalizer.Presieve.Arrows.sheaf_condition`,
  `isSheaf_iff_isSheaf_of_type`;
- source-facing layer: the Stacks equalizer sheaf condition for set-valued presheaves on `(C, J)`;
- core/canonical owner: `Presieve.IsSheaf`;
- bridge/view:
  `Equalizer.Presieve.Arrows.sheaf_condition` for the equalizer diagram and
  `isSheaf_iff_isSheaf_of_type` for the passage to the later category-valued owner
  `Presheaf.IsSheaf`.

Primitive data are only the site and the set-valued presheaf. The owner abstraction is the
presieve-valued sheaf predicate. The Stacks equalizer diagram and the category-valued owner are
derived bridge API from that source-facing set-valued notion, so this file should recall
`Presieve.IsSheaf` as main and keep the other formulations only as companions.
-/

/- Definition 7.7.1, source-facing recall: a set-valued presheaf on `(C, J)` is a sheaf exactly
when it satisfies the canonical presieve-valued predicate `Presieve.IsSheaf`. -/
recall Presieve.IsSheaf

/- The Stacks equalizer diagram of Definition 7.7.1 is the canonical theorem
`sheaf_condition`. -/
recall sheaf_condition

/- Bridge to the later category-valued owner: for set-valued presheaves,
`Presheaf.IsSheaf` is canonically equivalent to `Presieve.IsSheaf`. -/
recall isSheaf_iff_isSheaf_of_type
