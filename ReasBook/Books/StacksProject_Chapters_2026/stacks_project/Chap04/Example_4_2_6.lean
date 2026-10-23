module

public import Mathlib.CategoryTheory.SingleObj
import Mathlib.Tactic.Recall
@[expose] public section

namespace CategoryTheory

/- Domain-style sampling for Example 4.2.6:
- primary domain: one-object categories/groupoids attached to algebraic structures;
- sampled owner-level declarations:
  `CategoryTheory.SingleObj`,
  `CategoryTheory.SingleObj.groupoid`,
  `CategoryTheory.SingleObj.functor`,
  `CategoryTheory.Functor.Faithful`,
  `CategoryTheory.Functor.Full`,
  `CategoryTheory.Functor.essSurj_of_surj`,
  `CategoryTheory.Functor.asEquivalence`;
- best owner abstraction: the source example is already owned canonically by the instance
  `SingleObj.groupoid`; the converse is expressed by the owner-level functor
  `SingleObj.functor (MonoidHom.id (End c)) : SingleObj (End c) ⥤ C` together with the canonical
  functor-owner predicates `Faithful`, `Full`, `EssSurj`, and `asEquivalence`;
- primitive data: the group structure on `G`, or equivalently the endomorphism group `End c` of
  the chosen object `c` of a groupoid `C` with subsingleton object type, whose endomorphism group
  is `End c`;
- derived API: the induced groupoid structure on `SingleObj G` and, for a unique-object groupoid,
  the realization equivalence from `SingleObj (End c)` to `C`.

Source/core/bridge triage:
- `source-facing`: a group determines a one-object groupoid, and conversely every one-object
  groupoid comes from the endomorphism group of its unique object;
- `core/canonical`: `SingleObj.groupoid`;
- `bridge/view`: `SingleObj.functor` realizes `SingleObj (End c)` inside a one-object groupoid,
  while `SingleObj.toEnd` identifies the endomorphisms of the model object with the original
  group. -/

/- Example 4.2.6: a group `G` determines the one-object groupoid `SingleObj G` via the canonical
instance `CategoryTheory.SingleObj.groupoid`. -/
recall SingleObj.groupoid

/-- Example 4.2.6 (converse): if a groupoid `C` has subsingleton object type and `c : C` is the
chosen object, then `C` is equivalent to the single-object groupoid attached to `End c`. -/
noncomputable def oneObjectGroupoidEquivSingleObjEnd
    {C : Type*} [Groupoid C] [Subsingleton C] (c : C) : C ≌ SingleObj (End c) :=
  let F := SingleObj.functor (MonoidHom.id (End c))
  letI : F.Faithful :=
    { map_injective := by
        intro X Y f g h
        cases X
        cases Y
        exact h }
  letI : F.Full :=
    { map_surjective := by
        intro X Y f
        cases X
        cases Y
        exact ⟨f, rfl⟩ }
  letI : F.IsEquivalence :=
    { faithful := inferInstance
      full := inferInstance
      essSurj := Functor.essSurj_of_surj fun X ↦
        ⟨SingleObj.star (End c), Subsingleton.elim c X⟩ }
  F.asEquivalence.symm

end CategoryTheory
