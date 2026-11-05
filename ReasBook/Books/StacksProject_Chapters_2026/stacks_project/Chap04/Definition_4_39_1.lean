module

public import Mathlib.CategoryTheory.Endomorphism
public import Mathlib.CategoryTheory.Groupoid.Basic
import Mathlib.Tactic.Recall

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

namespace CategoryTheory

open Groupoid

variable {C : Type u} [Category.{v} C]

/-
Domain-style sampling for Definition 4.39.1:
- primary domain: thin groupoids as the canonical model of setoid `1`-categories;
- sampled owner-level declarations:
  `CategoryTheory.IsGroupoid`,
  `Quiver.IsThin`,
  `CategoryTheory.Groupoid.isThin_iff`,
  `CategoryTheory.Groupoid.isoEquivHom`;
- best owner abstraction: the source notion is exactly the conjunction of the canonical owners
  `[IsGroupoid C] [Quiver.IsThin C]`, so this file should recall those owners and keep only the
  source-facing bridge to trivial automorphisms;
- primitive owner data: invertibility of all morphisms and subsingleton endomorphism types;
- derived API: the automorphism reformulation, obtained by transporting the canonical owner theorem
  `Groupoid.isThin_iff` across `Groupoid.isoEquivHom`.

Source/core/bridge triage:
- `source-facing`: the source wording that a setoid `1`-category has only trivial automorphisms;
- `core/canonical`: `IsGroupoid` and `Quiver.IsThin`;
- `bridge/view`: `isThin_iff_subsingleton_aut`. -/

/- Definition 4.39.1: a setoid `1`-category is expressed in the owner API by the pair of
assumptions `[IsGroupoid C] [Quiver.IsThin C]`. -/
recall IsGroupoid

/- The second owner condition in Definition 4.39.1 is thinness. -/
recall Quiver.IsThin

/-- In a groupoid, thinness is equivalent to requiring each object to have a subsingleton
automorphism type. This is the source-facing reformulation of Definition 4.39.1. -/
theorem isThin_iff_subsingleton_aut [IsGroupoid C] :
    Quiver.IsThin C ↔ ∀ X : C, Subsingleton (Aut X) := by
  letI : Groupoid C := ofIsGroupoid
  refine (isThin_iff C).trans ?_
  constructor
  · intro h X
    exact (isoEquivHom X X).subsingleton_congr.2 (h X)
  · intro h X
    exact (isoEquivHom X X).subsingleton_congr.1 (h X)

end CategoryTheory
