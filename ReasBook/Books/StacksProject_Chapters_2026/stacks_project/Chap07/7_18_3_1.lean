module

public import Mathlib.CategoryTheory.Functor.KanExtension.Adjunction
import Mathlib.Tactic.Recall

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory

/- Domain-style sampling:
- primary domain: category-theoretic left Kan extensions and their objectwise colimit formulas on
  presheaf categories;
- sampled owner API:
  `Functor.leftKanExtensionObjIsoColimit`,
  `Functor.ι_leftKanExtensionObjIsoColimit_inv`,
  `Functor.ι_leftKanExtensionObjIsoColimit_hom`,
  `Functor.leftKanExtensionUnit`;
- source/core/bridge triage:
  `source-facing`: the textbook clause computing the inverse-image presheaf at `i` as the colimit
    over arrows `u.obj j ⟶ i`;
  `core/canonical`: the chosen left Kan extension owner `u.leftKanExtension F`;
  `bridge/view`: the canonical objectwise comparison isomorphism
    `Functor.leftKanExtensionObjIsoColimit`.

Primitive data are the functor `u`, the presheaf `F`, and the chosen pointwise left Kan extension
instance. The colimit formula is derived API from the chosen owner `u.leftKanExtension F`, so this
file should recall the owner-level comparison isomorphism directly rather than the lower witness
theorem `Functor.LeftExtension.IsPointwiseLeftKanExtensionAt.isoColimit`. -/

/- 7.18.3.1: the value at `i` of the inverse-image presheaf, realized as the chosen left Kan
extension along `u`, is the colimit over arrows `u.obj j ⟶ i`. In mathlib this is the canonical
owner-level comparison isomorphism `Functor.leftKanExtensionObjIsoColimit`. -/
recall Functor.leftKanExtensionObjIsoColimit
