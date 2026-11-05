module

public import Mathlib.CategoryTheory.Functor.KanExtension.Basic
public import Mathlib.CategoryTheory.Limits.Presheaf
public import Mathlib.CategoryTheory.Yoneda
import Mathlib.Tactic.Recall

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

universe v u₁ u₂

namespace CategoryTheory

open Opposite Functor

variable {C : Type u₁} [Category.{v} C]
variable {D : Type u₂} [Category.{v} D]
variable (u : C ⥤ D) (U : C)

/- Domain-style sampling:
- primary domain: presheaf left Kan extensions of representables along `u.op`;
- sampled owner API:
  `Functor.leftKanExtensionUnique`,
  `Functor.leftKanExtensionUnit`,
  `CategoryTheory.yonedaMap`,
  the mathlib instance `(yoneda.obj (u.obj U)).IsLeftKanExtension (yonedaMap u U)`;
- source-facing: Lemma 7.5.6 says the pushforward of the representable presheaf `h_U` is
  canonically represented by `u.obj U`;
- core/canonical: the chosen left Kan extension `u.op.leftKanExtension (yoneda.obj U)` and its
  unit;
- bridge/view: specialize the canonical uniqueness isomorphism for left Kan extensions to the
  upstream Yoneda left-extension datum.

Primitive data are only `u` and `U`. The representability isomorphism is derived API from the
owner theorem `Functor.leftKanExtensionUnique`, after supplying the canonical local existence
witness coming from `(yoneda.obj (u.obj U)).IsLeftKanExtension (yonedaMap u U)`. This keeps the
file at the intended bridge/view layer and avoids any parallel local owner declaration.
-/

/- Lemma 7.5.6: for a functor `u : C ⥤ D` and an object `U : C`, the pushforward presheaf
`u_p h_U` is canonically represented by `u.obj U`; in mathlib terms, the chosen left Kan
extension of `yoneda.obj U` along `u.op` is canonically isomorphic to `yoneda.obj (u.obj U)`.
This is the direct specialization of `leftKanExtensionUnique` to the upstream left Kan extension
datum `yonedaMap u U`. -/
recall Functor.leftKanExtensionUnique

#check
  (by
    letI : u.op.HasLeftKanExtension (yoneda.obj U) :=
      HasLeftKanExtension.mk (yoneda.obj (u.obj U)) (yonedaMap u U)
    exact
      (Functor.leftKanExtensionUnique (u.op.leftKanExtension (yoneda.obj U))
        (u.op.leftKanExtensionUnit (yoneda.obj U))
        (yoneda.obj (u.obj U))
        (yonedaMap u U) :
          u.op.leftKanExtension (yoneda.obj U) ≅ yoneda.obj (u.obj U)))

end CategoryTheory
