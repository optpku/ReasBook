module

public import Mathlib.CategoryTheory.Yoneda
import Mathlib.Tactic.Recall
public import stacks_project.Chap04.Example_4_3_4

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

universe v u

namespace CategoryTheory

open scoped RepresentablePresheaf

variable {C : Type u} [Category.{v} C]

/- Source/core/bridge triage for Lemma 4.3.5:
- source-facing content: the Yoneda embedding is full and faithful, together with the standard
  evaluation equivalence it induces;
- core/canonical owner: `Yoneda.fullyFaithful`, `yonedaLemma`, and their pointwise companions
  `yonedaEquiv`, `yonedaEquiv_naturality`, `yonedaEquiv_apply`;
- bridge layer: none is needed here, because the source statement is already the canonical
  mathlib Yoneda API.
-/

/- Lemma 4.3.5 (Yoneda lemma): the Yoneda embedding `yoneda : C ⥤ Presheaf.{v} C` is full and
faithful. The canonical mathlib owner packaging this statement is `Yoneda.fullyFaithful`, from
which fullness and faithfulness are derived. -/
recall Yoneda.fullyFaithful

/- More generally, the Yoneda lemma identifies the Yoneda pairing with evaluation by a natural
isomorphism. This is the canonical mathlib natural isomorphism `yonedaLemma`. -/
recall yonedaLemma

/- Pointwise, for every object `U` of `C` and every presheaf `F : Presheaf.{v} C`, morphisms
`h[U] ⟶ F` are in bijection with elements of `F.obj (op U)`. This is the componentwise
equivalence underlying `yonedaLemma`. -/
recall yonedaEquiv

/- The pointwise Yoneda equivalence is natural in the Yoneda variable. -/
recall yonedaEquiv_naturality

/- Companion recall: the Yoneda equivalence is evaluation at `𝟙 U`, namely
`f ↦ f.app (op U) (𝟙 U)`. -/
recall yonedaEquiv_apply

end CategoryTheory
