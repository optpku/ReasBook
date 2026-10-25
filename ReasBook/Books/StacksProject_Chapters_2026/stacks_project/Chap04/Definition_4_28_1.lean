module

public import Mathlib.CategoryTheory.Whiskering
import Mathlib.Tactic.Recall

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

namespace CategoryTheory

/- Domain-style sampling for Definition 4.28.1:
- primary domain: horizontal composition and whiskering for natural transformations in
  `CategoryTheory`.
- inspected owner declarations: `NatTrans.hcomp`, `Functor.whiskerLeft`, `Functor.whiskerRight`,
  and the companion formulas
  `Functor.NatTrans.hcomp_eq_whiskerLeft_comp_whiskerRight` /
  `Functor.NatTrans.hcomp_eq_whiskerRight_comp_whiskerLeft`.
- best owner abstraction: `NatTrans.hcomp`; the whiskering formulas are derived bridge theorems,
  not primitive source-owned data.
- primitive-vs-derived split:
  primitive owner data: the canonical horizontal composite `α ◫ β`.
  derived API kept here: the two standard whiskering decompositions of `α ◫ β`. -/

/- Source/core/bridge triage for Definition 4.28.1:
- source-facing: the textbook horizontal composite `s ⋆ t`.
- core/canonical: `NatTrans.hcomp`.
- bridge/view: the two whiskering factorization formulas for `NatTrans.hcomp`. -/

/- Canonical recall: horizontal composition of natural transformations is the existing owner
operation `NatTrans.hcomp`, written infix as `t ◫ s`. -/
recall NatTrans.hcomp

/- Definition 4.28.1: the textbook horizontal composite `s ⋆ t` is the canonical horizontal
composition `t ◫ s`, computed by first whiskering `s` on the left and then whiskering `t` on the
right. -/
recall Functor.NatTrans.hcomp_eq_whiskerLeft_comp_whiskerRight

/- Definition 4.28.1: equivalently, the textbook horizontal composite `s ⋆ t` is the canonical
horizontal composition `t ◫ s`, computed by first whiskering `t` on the right and then whiskering
`s` on the left. -/
recall Functor.NatTrans.hcomp_eq_whiskerRight_comp_whiskerLeft

end CategoryTheory
