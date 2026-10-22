/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

/- Definition 3.1.5.2 is the textbook positive-part map `x ↦ (x)_+`. In mathlib this notion is
owned by the notation class `PosPart`, whose canonical map is `posPart`, written `x⁺`.

Primary domain:
- positive-part operations in ordered additive algebra.

Relevant owner-style declarations sampled before refinement:
- `posPart`
- `posPart_def`
- `posPart_eq_ite`

Best owner abstraction:
- `posPart`

Primitive data:
- none in this file; the positive-part operation is supplied upstream by mathlib instances.

Derived API:
- `posPart_def`
- `posPart_eq_ite`

Source/core/bridge triage:
- source-facing: the textbook positive-part map `x ↦ (x)_+`
- core/canonical: `posPart`
- bridge/view: `posPart_def` and `posPart_eq_ite`, giving the lattice and linear-order formulas

This file therefore recalls the owner declaration directly together with its canonical lattice and
linear-order formulas. Downstream specializations should use these upstream bridge lemmas directly
instead of introducing parallel public shell theorems. -/

recall posPart {α : Type*} [PosPart α] : α → α

recall posPart_def
    {α : Type*} [Lattice α] [AddGroup α] (a : α) :
    a⁺ = a ⊔ 0

recall posPart_eq_ite
    {α : Type*} [LinearOrder α] [AddGroup α] {a : α} :
    a⁺ = if 0 ≤ a then a else 0
