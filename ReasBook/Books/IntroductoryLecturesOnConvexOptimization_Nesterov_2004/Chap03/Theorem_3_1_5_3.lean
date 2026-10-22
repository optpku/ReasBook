/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import Mathlib.Tactic.Recall
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Theorem_3_21

-- Declarations for this item will be appended below by the statement pipeline.

/- Theorem 3.1.5.3 is a recall-only surface in the chapter's convex directional-derivative /
subdifferential domain.

Primary domain:
- finite directional derivatives of convex `ℝ ∪ {+∞}`-valued functions at interior points of
  their effective domains.

Relevant owner-style declarations sampled before refinement:
- `convexDirectionalDerivative` in `Theorem_3_21`, the chapter owner for the extended-valued
  directional derivative;
- the inline coercion
  `fun p ↦ ((((convexDirectionalDerivative f x0 p).toReal : ℝ) : WithTop ℝ))` used in
  `Theorem_3_21` for the subdifferential-at-the-origin comparison;
- `subdifferential` in `Definition_3_1_5`, the chapter owner for subgradients of
  `WithTop ℝ`-valued functions;
- `convexDirectionalDerivativeReal_isGreatest_subgradientPairing_of_mem_interior` in
  `Theorem_3_21`, the canonical max-formula theorem on that owner surface.

Best owner abstraction:
- `convexDirectionalDerivativeReal_isGreatest_subgradientPairing_of_mem_interior`.

Primitive data:
- none in this file; the directional-derivative construction and the supporting subdifferential
  API already live upstream in `Theorem_3_21`.

Derived API:
- this recall-only source-facing entry point for the textbook max formula.

Source/core/bridge triage:
- source-facing: Theorem 3.1.5.3's statement that `f'(x₀; p)` is the maximum of
  `⟪g, p⟫` over `g ∈ ∂f(x₀)`;
- core/canonical: `convexDirectionalDerivative` together with the owner theorem
  `convexDirectionalDerivativeReal_isGreatest_subgradientPairing_of_mem_interior`;
- bridge/view: this file's numbered recall surface.

The previous file duplicated the secant-slope construction, the finite directional derivative, its
`WithTop ℝ` lift, and two owner theorems that already exist in `Theorem_3_21`. The refined file
reuses the chapter owner theorem directly and deletes the parallel local API.
-/

/- Theorem 3.1.5.3: at an interior point of the effective domain of a convex
`ℝ ∪ {+∞}`-valued function, the finite directional derivative in direction `p` is the maximum of
the pairings `⟪g, p⟫` over all subgradients `g ∈ ∂f(x₀)`. -/
recall convexDirectionalDerivativeReal_isGreatest_subgradientPairing_of_mem_interior
