module

public import Mathlib.CategoryTheory.Whiskering
public import Mathlib.CategoryTheory.Yoneda


@[expose] public section

open CategoryTheory

namespace PresheafCostalk

open CategoryTheory
open CategoryTheory.Functor

/- Textbook notation for the presheaf-valued costalk functor attached to `u`. -/
scoped syntax:100 term noWs "^p" : term
scoped macro_rules
  | `($u^p) =>
      `(yoneda ⋙ (whiskeringLeft _ _ _).obj (Functor.op $u))

end PresheafCostalk

namespace CategoryTheory

open scoped PresheafCostalk
open Functor

section

universe u v w

variable {C : Type u} [Category.{v} C]
variable (u : C ⥤ Type w)

/- Domain-style sampling for 7.32.3.1:
- primary domain: set-valued presheaf fiber/costalk constructions and their adjunction;
- sampled declarations in the same domain:
  `Functor.presheafFiber`,
  `CategoryTheory.yoneda`,
  `Functor.whiskeringLeft`,
  `Functor.lanAdjunction`;
- source/core/bridge triage:
  `source-facing`: the textbook notation `u^p` for the costalk functor attached to `u`;
  `core/canonical`: the composite
    `yoneda ⋙ (whiskeringLeft Cᵒᵖ (Type w)ᵒᵖ (Type w)).obj u.op`;
  `bridge/view`: the notation `u^p` for that composite and the adjunction with
    `Functor.presheafFiber`.

Primitive data are only the set-valued functor `u`. The canonical owner is the composite above;
the textbook notation `u^p` is the only source-facing bridge kept here, and the adjunction with
`Functor.presheafFiber` is further derived API built on that owner. This file therefore keeps the
owner expression as the mathematical core and adds only the notation bridge, rather than
introducing a parallel wrapper declaration for the same functor.
-/

/- 7.32.3.1: the Stacks construction sending a set `E` to the presheaf
`U ↦ Map(u(U), E)` is the canonical composite of the Yoneda embedding of `Type w` with
precomposition along `u.op`. -/
#check (yoneda ⋙ (whiskeringLeft Cᵒᵖ (Type w)ᵒᵖ (Type w)).obj u.op)

/- Source-facing notation check: the textbook notation `u^p` is just surface syntax for the same
canonical composite above. -/
#check u^p

end

end CategoryTheory
