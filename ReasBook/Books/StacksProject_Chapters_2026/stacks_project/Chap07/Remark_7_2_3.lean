module

import Mathlib.Tactic.Recall
public import stacks_project.Chap07.Definition_7_2_2

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

universe u

namespace CategoryTheory

section

variable (C : Type u) [SmallCategory C]
variable (A : Type (u + 1)) [LargeCategory A]

/-
Domain-style sampling for Remark 7.2.3:
- primary domain: presheaf categories as functor categories with inherited size structure
- sampled declarations in this domain:
  `Functor.category`,
  `LargeCategory`,
  the source-facing owner `Cᵒᵖ ⥤ A` from Definition 7.2.2,
  and the set-valued specialization `Presheaf`
- best owner abstraction: the functor category `Cᵒᵖ ⥤ A`
- primitive data: none beyond the owner `Cᵒᵖ ⥤ A` already recalled in Definition 7.2.2
- derived API: the inherited category structure `Functor.category` and the induced
  `LargeCategory (Cᵒᵖ ⥤ A)` instance
-/
/-
Source/core/bridge triage for Remark 7.2.3:
- source-facing content: the category of `A`-valued presheaves on `C`
- core/canonical owner: the functor category `Cᵒᵖ ⥤ A`
- derived API recalled here: its canonical category structure `Functor.category` and the induced
  large-category interface
-/
/- Remark 7.2.3: if `A` is one of the ambient large categories from Remark 4.2.2, then the
category of `A`-valued presheaves on a small category `C` is again the canonical functor category.
The new content here is therefore the inherited category structure and size interface on
`Cᵒᵖ ⥤ A`, not a second restatement of its underlying type. -/
recall Functor.category

/- Companion size recall: the presheaf functor category again satisfies the canonical
large-category interface. -/
#check (inferInstance : LargeCategory (Cᵒᵖ ⥤ A))

end

end CategoryTheory
