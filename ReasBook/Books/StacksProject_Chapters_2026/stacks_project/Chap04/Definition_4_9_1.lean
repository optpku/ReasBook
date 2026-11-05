module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs
import Mathlib.Tactic.Recall

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

universe v u

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]

/- Domain-style sampling for Definition 4.9.1:
- primary domain: pushout squares and their universal property in `CategoryTheory.Limits`.
- inspected owner declarations:
  `IsPushout`,
  `IsPushout.exists_desc`,
  `IsPushout.hom_ext`,
  `IsPushout.of_isColimit`.
- best owner abstraction: `IsPushout`; the commutative square and colimit witness are primitive
  data of the owner, while the textbook existence, uniqueness, and converse clauses are derived
  owner API.
- primitive-vs-derived split:
  primitive data: `IsPushout f g p q`.
  derived API reused here:
    the existence clause `IsPushout.exists_desc`,
    the uniqueness clause `IsPushout.hom_ext`,
    the converse constructor `IsPushout.of_isColimit`. -/

/- Source/core/bridge triage for Definition 4.9.1:
- source-facing: the textbook universal property of a pushout square.
- core/canonical: `IsPushout`.
- bridge/view: the thin owner lemmas `IsPushout.exists_desc`, `IsPushout.hom_ext`, and
  `IsPushout.of_isColimit`. -/

/-
Definition 4.9.1: a pushout of morphisms `f : y ⟶ x` and `g : y ⟶ z` is the canonical
mathlib notion `CategoryTheory.IsPushout f g p q`, consisting of an object `po` with
morphisms `p : x ⟶ po` and `q : z ⟶ po` forming a commutative square and satisfying the
stated universal property.
-/
recall IsPushout

variable {x y z po w : C}
variable {f : y ⟶ x} {g : y ⟶ z} {p : x ⟶ po} {q : z ⟶ po}

/- Companion recall: the existence clause in the textbook universal property is the canonical
theorem `IsPushout.exists_desc`. -/
recall IsPushout.exists_desc

/- Companion recall: the uniqueness clause in the textbook universal property is the canonical
theorem `IsPushout.hom_ext`. -/
recall IsPushout.hom_ext

/- Companion recall: the converse direction from a colimiting pushout cocone is the canonical
constructor `IsPushout.of_isColimit`. -/
recall IsPushout.of_isColimit

end CategoryTheory
