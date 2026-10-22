/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import Mathlib.Tactic.Recall
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Theorem_3_35

-- Declarations for this item will be appended below by the statement pipeline.

/- Theorem 3.1.28 is recall-only in the chapter's affine-fiber value-function /
multiplier-subgradient domain.

Mandatory domain-style sampling before refinement:
- `dom` and `withTopRealPart` in `Definition_3_3`, the chapter owners for effective domains and
  finite real parts of `WithTop ℝ`-valued objectives;
- `subdifferential` and the notation `∂ f(x)` in `Definition_3_1_5`, the chapter owner for
  ambient extended-valued subgradients;
- `linearEqualityFeasibleSet` in `LinearEqualityFeasibleSet`, the primitive affine-fiber owner;
- `affinePartialInfProjection_realPart_convexOn` and
  `mem_subdifferentialWithin_affinePartialInfProjection_of_variational_inequality` in
  `Theorem_3_35`, the canonical owner-level affine-fiber convexity and multiplier-subgradient
  declarations.

Best owner abstraction:
- core/canonical: the two owner declarations in `Theorem_3_35`, stated directly on the chapter's
  affine-fiber `partialInfProjection` surface;
- bridge/view: this numbered recall surface.

Primitive data:
- none in this file; the affine-fiber owner data already live upstream.

Derived API:
- this numbered recall surface.

Source/core/bridge triage:
- source-facing: Theorem 3.1.28's convexity and multiplier-subgradient clauses for a linearly
  constrained value function;
- core/canonical: the owner declarations in `Theorem_3_35`;
- bridge/view: this recall surface.

The previous file kept a second public `WithTop ℝ` value-function owner together with parallel
theorem wrappers around the affine-fiber owner already developed in `Theorem_3_35`. That local
surface was not the chapter owner abstraction: the canonical construction already lives on
`partialInfProjection`, with `linearEqualityFeasibleSet` as the primitive affine-fiber data and
the per-multiplier relative-subdifferential theorem already stated upstream. This file therefore
reuses those owner declarations directly instead of maintaining a second value-function API. -/

/- Theorem 3.1.28 (1): the affine-fiber projected value function is convex on its finite-value
domain under the standard convexity hypotheses on `f` and `Q`. -/
recall affinePartialInfProjection_realPart_convexOn

/- Theorem 3.1.28 (2): a feasible primal point together with a primal subgradient satisfying the
affine variational inequality yields a relative subgradient of the canonical affine-fiber
projected value function. -/
recall mem_subdifferentialWithin_affinePartialInfProjection_of_variational_inequality
