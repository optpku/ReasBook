/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import Mathlib.Tactic.Recall
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Lemma_3_15

-- Declarations for this item will be appended below by the statement pipeline.

/- Lemma 3.1.15 lies in the chapter's real-valued subdifferential / positive-homogeneity domain.

Primary domain:
- subdifferentials of positively homogeneous real-valued functions on real inner-product spaces.

Sampled owner-style declarations:
- `IsSubgradientAt` in `Definition_3_1_5`, the chapter owner predicate for extended-valued
  subgradients;
- `subdifferential` in `Definition_3_1_5`, the derived owner set-valued API;
- `IsPositivelyHomogeneousOn` in `Definition_3_1_7`, the chapter owner predicate for positive
  homogeneity;
- `subdifferential_eq_subdifferential_zero_of_posHomogeneous` in `Lemma_3_15`, the existing
  chapter theorem for this source fact.

Best owner abstraction:
- `subdifferential_eq_subdifferential_zero_of_posHomogeneous`, organized around
  `subdifferential (fun y ↦ (f y : WithTop ℝ))` and `IsPositivelyHomogeneousOn 1 Set.univ f`.

Primitive data:
- a real inner-product space `E`;
- a real-valued function `f : E → ℝ`;
- the positive-homogeneity owner hypothesis `IsPositivelyHomogeneousOn 1 Set.univ f`.

Derived API:
- the subdifferential identity at `x` in terms of the origin subdifferential and the touching
  condition `inner ℝ g x = f x`.

Source/core/bridge triage:
- source-facing: Lemma 3.1.15's description of the subdifferential of a positively
  `1`-homogeneous function;
- core/canonical: `IsSubgradientAt`, `subdifferential`, and `IsPositivelyHomogeneousOn`;
- bridge/view: none beyond the coercion `fun y ↦ (f y : WithTop ℝ)` already absorbed by the owner
  theorem in `Lemma_3_15`.

The previous version duplicated a real-valued subgradient predicate, a real-valued
subdifferential, and a parallel theorem with an extra convexity hypothesis. That convexity
hypothesis is mathematically redundant here, and the owner theorem in `Lemma_3_15` already states
the source fact canonically. This file therefore recalls that theorem directly instead of keeping a
second local wrapper API. -/

recall subdifferential_eq_subdifferential_zero_of_posHomogeneous
