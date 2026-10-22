/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import Mathlib.Tactic.Recall
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap01.Definition_1_3_3
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Definition_5_1_1

-- Declarations for this item will be appended below by the statement pipeline.

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/- Definition 5.3.1 lies in the constrained barrier / path-following domain.

Sampled owner declarations:
- `SetConstrainedMinimizationProblem` in `Chap01/Definition_1_3_3`, the project owner for a
  feasible set together with its objective;
- `IsStandardSelfConcordantOn` in `Definition_5_1_1`, the Chapter 5 owner for a standard
  self-concordant potential on an open convex domain;
- `IsSelfConcordantOnWith.isBarrierFunctionOn` in `Theorem_5_1_3`, the canonical bridge turning
  self-concordance on `dom` into a barrier on `closure dom`;
- `SetConstrainedMinimizationProblem` in `Chap03/Definition_3_36`, where the chapter keeps the
  constrained problem at the owner level instead of introducing a parallel wrapper.

Best owner abstraction:
- source-facing data: a domain `dom`, an objective vector `c`, and a standard self-concordant
  potential `F` on `dom`;
- core/canonical ambient owner:
  `SetConstrainedMinimizationProblem E` with feasible set `closure dom` and objective `inner ℝ c`;
- bridge/view: the Chapter 5 regularity/barrier hypothesis `IsStandardSelfConcordantOn dom F`.

Primitive data:
- the ambient constrained problem owner on `closure dom` with linear objective `inner ℝ c`;
- the barrier-side hypothesis `IsStandardSelfConcordantOn dom F`.

Derived API:
- openness and convexity of `dom`, recovered from `IsStandardSelfConcordantOn dom F`;
- closedness of the feasible set `closure dom`;
- later barrier facts on `closure dom`, derived through `Theorem_5_1_3`.

Source/core/bridge triage:
- source-facing: the textbook triple `(dom, c, F)`;
- core/canonical: `SetConstrainedMinimizationProblem E`;
- bridge/view: `IsStandardSelfConcordantOn dom F` and its barrier consequences on `closure dom`.

This file therefore keeps no parallel `StandardConstrainedMinimizationProblem` wrapper. The
constrained problem is the existing owner `SetConstrainedMinimizationProblem`, and the Chapter 5
barrier data remain separate owner-level hypotheses. -/

section

variable (dom : Set E) (c : E) (F : E → ℝ)

/- Definition 5.3.1 uses the existing constrained-problem owner together with the existing
Chapter 5 standard self-concordance owner. -/
recall SetConstrainedMinimizationProblem
recall IsStandardSelfConcordantOn

set_option linter.hashCommand false in
#check
  (.mk (closure dom) (inner ℝ c) : SetConstrainedMinimizationProblem E)

set_option linter.hashCommand false in
#check (IsStandardSelfConcordantOn dom F)

end
