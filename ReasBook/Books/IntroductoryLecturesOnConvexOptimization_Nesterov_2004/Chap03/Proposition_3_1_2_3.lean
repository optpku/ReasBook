/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import Mathlib.Tactic.Recall
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Proposition_3_11

-- Declarations for this item will be appended below by the statement pipeline.

/- Proposition 3.1.2.3 lies in the chapter's support-function / effective-domain domain.

Sampled owner-style declarations:
- `extendedRealEffectiveDomain` in `Definition_3_1_1_2`
- `supportFunction` in `Definition_3_9`
- `supportFunction_mem_extendedRealEffectiveDomain_of_nonempty_bounded` in `Proposition_3_11`
- `supportFunction_dom_eq_univ_of_nonempty_bounded` in `Proposition_3_11`

Best owner abstraction:
- the existing chapter theorem
  `supportFunction_dom_eq_univ_of_nonempty_bounded`, together with its pointwise companion
  `supportFunction_mem_extendedRealEffectiveDomain_of_nonempty_bounded`

Primitive data:
- a set `Q : Set E` in a real inner-product space `E`
- hypotheses `Q.Nonempty` and `Bornology.IsBounded Q`

Derived API:
- pointwise finiteness of `supportFunction Q`
- the domain identity `dom (supportFunction Q) = Set.univ`

Source/core/bridge triage:
- source-facing: the bounded-set support-function finiteness statement
- core/canonical: `supportFunction_dom_eq_univ_of_nonempty_bounded`
- bridge/view: the pointwise companion theorem

This file previously duplicated the exact pointwise companion theorem already formalized in
`Proposition_3_11` and also kept a renamed shell for the global domain theorem. Since the chapter
already has the owner theorem family, and that family has now been generalized to arbitrary real
inner-product spaces, this numbered item is recall-only and keeps no parallel local theorem names.
The textbook `ℝⁿ` statement remains an immediate specialization. -/

recall supportFunction_mem_extendedRealEffectiveDomain_of_nonempty_bounded

recall supportFunction_dom_eq_univ_of_nonempty_bounded
