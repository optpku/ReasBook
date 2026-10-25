module

import Mathlib.Tactic.Recall
public import stacks_project.Chap07.Definition_7_10_9

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Opposite

universe w v u

namespace CategoryTheory.Presheaf

variable {C : Type u} [Category.{v} C]
variable (J : GrothendieckTopology C) (F : Cᵒᵖ ⥤ Type w)

/- Domain-style sampling for Definition 7.49.2:
- primary domain: separated presheaves of sets on a Grothendieck site;
- sampled canonical declarations:
  `Presieve.IsSeparatedFor`,
  `Presieve.IsSeparated`,
  `Presieve.IsSheaf.isSeparated`,
  `Presheaf.IsSeparated`;
- best owner abstraction: `Presieve.IsSeparated J F`, already adopted earlier in
  Definition 7.10.9;
- primitive data: only the site `(C, J)` and the set-valued presheaf `F`;
- derived API: coverwise injectivity criteria and the sheaf-to-separated implication.

Source/core/bridge triage:
- `core/canonical`: `Presieve.IsSeparated J F`;
- `bridge/view`: concrete coverwise injectivity reformulations and consequences such as the plus
  construction lemmas.

This numbered item introduces no new source-facing data beyond the canonical separatedness
predicate itself, so keeping a second chapter-local wrapper would only duplicate the owner already
used upstream in Definition 7.10.9.
-/

/- Definition 7.49.2: for a category `C` with Grothendieck topology `J`, the chapter-facing
owner notion that a set-valued presheaf `F` is separated is `CategoryTheory.Presieve.IsSeparated
J F`. This is already the canonical declaration reused earlier in Definition 7.10.9. -/
recall Presieve.IsSeparated

/- Source-facing specialization: separatedness of `F` on `(C, J)` is expressed directly as the
proposition `Presieve.IsSeparated J F`. -/
#check (Presieve.IsSeparated J F : Prop)

end CategoryTheory.Presheaf
