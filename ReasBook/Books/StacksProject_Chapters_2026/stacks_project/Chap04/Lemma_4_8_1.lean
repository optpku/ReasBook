module

public import Mathlib.CategoryTheory.Limits.FunctorCategory.Shapes.Pullbacks
public import Mathlib.CategoryTheory.Limits.Types.Pullbacks
import Mathlib.Tactic.Recall

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

universe w v u

open CategoryTheory

namespace CategoryTheory.Limits

variable {C : Type u} [Category.{v} C]
variable {F G H : Cᵒᵖ ⥤ Type w}

/- Domain-style sampling for Lemma 4.8.1:
- primary domain: pullbacks in functor categories, specialized to set-valued presheaves
  `Cᵒᵖ ⥤ Type w`;
- sampled owner declarations:
  `pullbackObjIso`,
  `pullbackObjIso_hom_comp_fst`,
  `pullbackObjIso_hom_comp_snd`,
  `pullbackObjIso_inv_comp_fst`;
- best owner abstraction: the canonical objectwise pullback comparison isomorphism
  `pullbackObjIso a b X`;
- primitive data: only the natural transformations `a : F ⟶ G` and `b : H ⟶ G`;
- derived API: the projection comparison lemmas such as `pullbackObjIso_hom_comp_fst`.

Source/core/bridge triage:
- `source-facing`: the textbook statement that fibre products of set-valued presheaves exist and
  are computed objectwise;
- `core/canonical`: mathlib's owner declaration `pullbackObjIso`;
- `bridge/view`: the projection identities, here recalled via `pullbackObjIso_hom_comp_fst`.

There is no local primitive wrapper to keep: the correct refinement is direct recall of the
canonical mathlib owner and its derived projection lemma. -/

/- Lemma 4.8.1: for set-valued presheaves `F, G, H : Cᵒᵖ ⥤ Type w` and natural transformations
`a : F ⟶ G`, `b : H ⟶ G`, the fibre product presheaf is computed objectwise. The canonical
mathlib statement is the objectwise pullback isomorphism `pullbackObjIso a b X`. -/
recall pullbackObjIso

/- The first projection of the objectwise pullback agrees with evaluation of the presheaf pullback
projection; this is exactly `pullbackObjIso_hom_comp_fst`. -/
recall pullbackObjIso_hom_comp_fst

end CategoryTheory.Limits
