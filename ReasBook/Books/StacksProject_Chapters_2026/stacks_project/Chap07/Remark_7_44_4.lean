module

public import Mathlib.Topology.Sheaves.AddCommGrpCat
public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.Algebra.Category.Grp.Zero
public import Mathlib.Algebra.Category.Grp.Basic
import Mathlib.Tactic.Recall

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Opposite
open CategoryTheory.Functor

universe uC vC uD vD w

section

variable {C : Type uC} [Category.{vC} C]
variable {D : Type uD} [Category.{vD} D]
variable (u : D ⥤ C)

/- Domain-style sampling for Remark 7.44.4:
- primary domain: presheaf left Kan extensions and forgetful comparison for abelian-group-valued
  presheaves;
- sampled owner API:
  `Functor.lan`,
  `Functor.lanAdjunction`,
  `Functor.lanCompIsoOfPreserves`,
  `Functor.whiskeringRight`;
- current-chapter reuse point:
  `Lemma_7_44_2`, which already reuses `Functor.lanAdjunction` and
  `Functor.lanCompIsoOfPreserves` for general algebraic-structure-valued presheaves, so this file
  should specialize the same owners to `AddCommGrpCat` rather than introduce a parallel abelian
  wrapper;
- source/core/bridge triage:
  `source-facing`: the Stacks remark identifying the abelian-presheaf pullback functor `uₚ^{ab}`
  and its adjunction/preservation properties;
  `core/canonical`: mathlib's left Kan extension owner `u.op.lan`, together with
  `u.op.lanAdjunction AddCommGrpCat` and the forgetful comparison isomorphism
  `(forget AddCommGrpCat).lanCompIsoOfPreserves u.op`;
  `bridge/view`: the specialization from the general presheaf Kan-extension API to the specific
  target category `AddCommGrpCat`.

Primitive data are the functor `u`, the existence of left Kan extensions along `u.op` for
`AddCommGrpCat`-valued and set-valued presheaves, and preservation of those left Kan extensions by
`forget AddCommGrpCat`. The functor `u.op.lan`, its adjunction, and the forgetful comparison
isomorphism are derived API owned upstream, so this file should reuse those owners directly rather
than introduce a parallel local wrapper for abelian presheaves.
-/

section PresheafAdjunction

variable [∀ F : Dᵒᵖ ⥤ AddCommGrpCat, u.op.HasLeftKanExtension F]

/- Remark 7.44.4: for a functor `u : D ⥤ C`, the abelian-presheaf pullback functor `uₚ^{ab}` is
the canonical left Kan extension along `u.op`, i.e. `u.op.lan`. Its adjunction with
precomposition by `u.op` is the specialized Kan-extension adjunction
`u.op.lanAdjunction AddCommGrpCat`, while agreement with the set-valued left Kan extension after
forgetting to sets is a separate comparison statement and need not hold without extra hypotheses.
-/
#check (u.op.lan : (Dᵒᵖ ⥤ AddCommGrpCat) ⥤ Cᵒᵖ ⥤ AddCommGrpCat)

/- Remark 7.44.4, owner form: the adjunction between abelian-presheaf pullback and pushforward is
the `AddCommGrpCat` specialization of the canonical presheaf left-Kan-extension adjunction. -/
recall Functor.lanAdjunction

/- Remark 7.44.4, specialized form: the abelian-presheaf pullback/pushforward adjunction is
`u.op.lanAdjunction AddCommGrpCat`. -/
#check (u.op.lanAdjunction AddCommGrpCat :
  (u.op.lan : (Dᵒᵖ ⥤ AddCommGrpCat) ⥤ Cᵒᵖ ⥤ AddCommGrpCat) ⊣
    (whiskeringLeft Dᵒᵖ Cᵒᵖ AddCommGrpCat).obj u.op)

end PresheafAdjunction

variable [∀ F : Dᵒᵖ ⥤ AddCommGrpCat, u.op.HasLeftKanExtension F]

section PresheafForgetComparison

variable [∀ F : Dᵒᵖ ⥤ Type w, u.op.HasLeftKanExtension F]
variable [(forget AddCommGrpCat).PreservesLeftKanExtensions u.op]

/- Companion check: when `forget AddCommGrpCat` preserves the left Kan extensions along `u.op`,
forgetting the abelian-group-valued left Kan extension agrees canonically with the set-valued left
Kan extension of the underlying presheaf. This is exactly the conditional comparison alluded to in
the remark; the remark also notes that such agreement need not hold without extra hypotheses. -/
recall Functor.lanCompIsoOfPreserves

#check ((forget AddCommGrpCat).lanCompIsoOfPreserves u.op)

end PresheafForgetComparison

end
