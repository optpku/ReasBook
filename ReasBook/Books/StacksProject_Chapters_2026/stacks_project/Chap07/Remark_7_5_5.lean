module

public import Mathlib.CategoryTheory.Functor.KanExtension.Adjunction

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Opposite
open CategoryTheory.Functor

universe uC vC uD vD uA vA

section

variable {C : Type uC} [Category.{vC} C]
variable {D : Type uD} [Category.{vD} D]
variable {A : Type uA} [Category.{vA} A]
variable (u : C ⥤ D)
variable [∀ F : Cᵒᵖ ⥤ A, u.op.HasLeftKanExtension F]

/- Domain-style sampling:
- primary domain: category-theoretic presheaf Kan extensions and their adjunctions;
- sampled owner API:
  `Functor.lanAdjunction`,
  `HasLeftKanExtension`,
  `whiskeringLeft`;
- source-facing: Remark 7.5.5 identifies the presheaf pullback functor
  `(whiskeringLeft Cᵒᵖ Dᵒᵖ A).obj u.op` with a functor admitting the canonical left adjoint
  `u.op.lan`;
- core/canonical: the Kan-extension adjunction `Functor.lanAdjunction`;
- bridge/view: the presheaf specialization obtained by applying that owner theorem to `u.op`.

Primitive data are the functor `u` and the hypothesis that the needed pointwise left Kan
extensions along `u.op` exist; the canonical owner itself only needs the resulting left Kan
extensions. The adjunction itself is derived API owned upstream by
`Functor.lanAdjunction`, so this file should use its presheaf specialization directly rather than
keep a parallel local wrapper or a less specific generic recall.
-/

/- Remark 7.5.5: if every diagram `I_Y ⥤ A` has the colimits needed to form the pointwise left
Kan extension along `u.op`, then on `A`-valued presheaves the pullback functor
`u^p = (whiskeringLeft Cᵒᵖ Dᵒᵖ A).obj u.op` has the usual left adjoint
`u_p = u.op.lan`; in Lean this is exactly the specialized adjunction
`u.op.lanAdjunction A`. -/
#check (u.op.lanAdjunction A :
  u.op.lan ⊣ (whiskeringLeft Cᵒᵖ Dᵒᵖ A).obj u.op)

end
