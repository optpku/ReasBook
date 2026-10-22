/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import Mathlib.Tactic.Recall
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Theorem_3_1_5_6

-- Declarations for this item will be appended below by the statement pipeline.

/- Proposition 3.33 lies in the chapter's extended-valued convex-analysis / subdifferential
domain.

Sampled owner-style declarations:
- `dom` in `Definition_3_3`, the chapter owner for effective domains of `WithTop ℝ`-valued
  functions;
- `subdifferential` and `mem_subdifferential_iff` in `Definition_3_1_5`, the source-facing owner
  API for extended-valued subgradients;
- `subgradient_nonneg_on_sublevelSet_of_mem_subdifferential` in `Theorem_3_1_18`, the canonical
  sublevel-set inequality behind the minimizer pairing result;
- `subgradient_inner_sub_nonneg_of_isMinOn` in `Theorem_3_1_5_6`, the chapter owner theorem for
  pairing a subgradient at a feasible point with the displacement to a minimizer.

Best owner abstraction:
- core/canonical: `subgradient_inner_sub_nonneg_of_isMinOn`;
- bridge/view: the codomain coercion from a real-valued objective `f : E → ℝ` to the
  `WithTop ℝ`-valued owner surface `fun y ↦ (f y : WithTop ℝ)`.

Primitive data:
- an inner-product space `E`, a feasible set `Q`, a real-valued objective `f`, points `x`, `xStar`
  and a subgradient `g`;
- the feasibility hypothesis `x ∈ Q`;
- the minimizing hypothesis `IsMinOn f Q xStar`;
- the owner-membership hypothesis `g ∈ ∂ (fun y ↦ (f y : WithTop ℝ))(x)`.

Derived API:
- the nonnegativity inequality `0 ≤ inner ℝ g (x - xStar)`.

Source/core/bridge triage:
- source-facing: the textbook real-valued spelling of the minimizer-pairing inequality;
- core/canonical: `subgradient_inner_sub_nonneg_of_isMinOn`;
- bridge/view: the coercion from real-valued objectives to the chapter's extended-valued
  subdifferential owner.

This proposition contributes no new public owner beyond the existing theorem
`subgradient_inner_sub_nonneg_of_isMinOn`: its former local theorem was only the codomain-coercion
specialization of that owner theorem, and its second theorem was a verbatim alias of the first.
The file therefore keeps the canonical owner theorem directly instead of preserving a parallel
specialized wrapper API. -/

recall subgradient_inner_sub_nonneg_of_isMinOn
