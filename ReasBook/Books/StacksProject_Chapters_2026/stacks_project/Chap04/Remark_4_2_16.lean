module

public import Mathlib.CategoryTheory.Products.Basic
public import Mathlib.CategoryTheory.Types.Basic
public import Mathlib.Logic.Small.Basic
@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

universe u

namespace CategoryTheory

/-
Domain-style sampling for Remark 4.2.16:
- primary domain: universe-smallness of functor types.
- sampled owner-level declarations:
  `Small`,
  `small_of_surjective`,
  `not_small_type`,
  `evaluation`,
  `Functor.const`;
- best owner abstraction: `Small`.

Source/core/bridge triage:
- `source-facing`: the specific Stacks remark that `Type u ⥤ Type u` is not `u`-small.
- `core/canonical`: the owner predicate `Small` together with the core theorem `not_small_type`.
- `bridge/view`: the owner-level evaluation map at `PUnit`,
  `((evaluation (Type u) (Type u)).obj PUnit).obj : (Type u ⥤ Type u) → Type u`, which is
  surjective because every type is the value at `PUnit` of its constant endofunctor.

Primitive-vs-derived split:
- primitive data: none in this file; the relevant notions already live upstream.
- derived API: the theorem below, deduced from `not_small_type` by applying the canonical
  smallness transfer `small_of_surjective` to evaluation at `PUnit`.
-/

/-- Remark 4.2.16 (Stacks tag `02C2`): when `Sets` is modeled by the big category `Type u`, the
type of endofunctors `Type u ⥤ Type u` is not `u`-small. Equivalently, a functor `Sets → Sets`
is not itself a set-sized mathematical object. -/
theorem type_endofunctor_not_small :
    ¬ Small.{u} (Type u ⥤ Type u) := by
  intro hsmall
  letI := hsmall
  let ev : (Type u ⥤ Type u) → Type u := ((evaluation (Type u) (Type u)).obj PUnit).obj
  have hsurj : Function.Surjective ev := fun X ↦ ⟨(Functor.const (Type u)).obj X, rfl⟩
  exact not_small_type <| small_of_surjective hsurj

end CategoryTheory
