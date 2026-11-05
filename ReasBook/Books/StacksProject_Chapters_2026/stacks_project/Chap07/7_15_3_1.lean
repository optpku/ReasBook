module

public import Mathlib.CategoryTheory.Sites.Types
import Mathlib.Tactic.Recall

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory

/- Domain-style sampling for 7.15.3.1:
- primary domain: the canonical equivalence between sets and set-valued sheaves on
  `typesGrothendieckTopology`;
- sampled declarations:
  `typeEquiv`,
  `typeEquiv_inverse_obj`,
  `typeEquiv_functor_obj_obj_obj`,
  `fullSubcategorySetDirectImage_obj_obj`;
- best owner abstraction: the mathlib equivalence `typeEquiv`;
- source/core/bridge triage:
  `source-facing`: evaluation of the inverse-image functor at the singleton object and the
    explicit description of the direct-image sheaf on a set `U`;
  `core/canonical`: the mathlib equivalence `typeEquiv`;
  `bridge/view`: the two computation theorems above, together with the chapter-level full
    subcategory specialization `fullSubcategorySetDirectImage_obj_obj`.

Primitive data are carried entirely by the owner equivalence `typeEquiv`; the objectwise formulas
in this file, and their full-subcategory generalization later in the chapter, are derived API and
should therefore be direct uses of the canonical computation theorems, specialized only to the
source-facing arguments. -/

/- 7.15.3.1 (1): for the canonical equivalence between sets and sheaves on the jointly
surjective site of types, the inverse-image functor evaluates a sheaf at the singleton object
`e = PUnit`. This is the owner lemma `typeEquiv_inverse_obj`. -/
recall typeEquiv_inverse_obj

/- 7.15.3.1 (2): under the same equivalence, the direct-image of a set `E` is the sheaf whose
value on a set `U` is the hom-set `U ⟶ E`, equivalently the function type `U → E`. This is the
canonical computation theorem `typeEquiv_functor_obj_obj_obj`, evaluated at `Y = op U`. -/
recall typeEquiv_functor_obj_obj_obj
