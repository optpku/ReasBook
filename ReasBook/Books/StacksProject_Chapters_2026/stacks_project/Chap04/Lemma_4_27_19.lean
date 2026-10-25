module

import Mathlib.Tactic.Recall
public import stacks_project.Chap04.Definition_4_27_1

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

universe v u

namespace CategoryTheory

open MorphismProperty
open Localization
open Functor.IsLocalization

variable {C : Type u} [Category.{v} C]
variable (W : MorphismProperty C) [W.HasLeftCalculusOfFractions] [W.HasRightCalculusOfFractions]

local notation "Q" => LeftFraction.Localization.Q

/-
Companion recall: the left-fraction model localizes `C` at `W` via the canonical functor
`LeftFraction.Localization.Q W`.
-/
recall LeftFraction.Localization.Q

/-
Companion recall: replacing the target of a localization functor by an equivalent category
preserves the localization property via `Functor.IsLocalization.of_equivalence_target`.
-/
recall Functor.IsLocalization.of_equivalence_target

/-
Companion recall: transporting a localization functor across opposites is controlled by
`Functor.IsLocalization.op_iff`.
-/
recall Functor.IsLocalization.op_iff

/- Domain-style sampling in the localization owner API:
- source-facing model: `LeftFraction.Localization W`
- source-facing right-fraction model: `(LeftFraction.Localization W.op)ᵒᵖ`, presented by the
  functor `(LeftFraction.Localization.Q W.op).rightOp`
- core/canonical owner predicate: `Functor.IsLocalization`
- core/canonical uniqueness equivalence: `Localization.uniq`

Primitive data: the morphism property `W`.
Derived API: the two source-model localization functors and the canonical equivalence between
their targets. The right-fraction-model localization proof for `(Q W.op).rightOp` is auxiliary
infrastructure, so it should stay local rather than becoming a named bridge declaration.

Lemma 4.27.19 is a `bridge/view` item: it specializes the canonical owner equivalence to the
left-fraction model `LeftFraction.Localization W` and the textbook right-fraction model
`(LeftFraction.Localization W.op)ᵒᵖ`. The main item should therefore be a direct specialization
of `Localization.uniq`, not a renamed shell around it.
-/
section

omit [W.HasLeftCalculusOfFractions] in
local instance : (Q W.op).rightOp.IsLocalization W := by
  let G := (Q W.op).rightOp
  have hGop : G.op.IsLocalization W.op :=
    of_equivalence_target (Q W.op) W.op _
      (opOpEquivalence (LeftFraction.Localization W.op)).symm (Iso.refl _)
  exact (op_iff G W).1 hGop

/- Lemma 4.27.19: the left-fraction localization of `C` at `W` is canonically equivalent to the
opposite of the left-fraction localization of `Cᵒᵖ` at `W.op`, i.e. to the textbook
right-fraction model. This is exactly the owner equivalence `Localization.uniq`, specialized to
`Q W` and `(Q W.op).rightOp`. -/
#check (uniq (Q W) (Q W.op).rightOp W :
  LeftFraction.Localization W ≌ (LeftFraction.Localization W.op)ᵒᵖ)

end

end CategoryTheory
