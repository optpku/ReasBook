/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import Mathlib.Tactic.Recall
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Theorem_3_21

-- Declarations for this item will be appended below by the statement pipeline.

open scoped WithTopConvexAnalysis

universe u

/- Theorem 3.1.5.4 is a recall-only surface in the chapter's convex directional-derivative and
subdifferential domain.

Primary domain:
- directional derivatives and subdifferentials of convex `ℝ ∪ {+∞}`-valued functions on real
  normed and inner-product spaces.

Relevant owner-style declarations sampled before refinement:
- `convexDirectionalDerivative` in `Theorem_3_21`, the chapter owner for the extended-valued
  directional derivative at a finite base point;
- `convexDirectionalDerivativeReal_convexOn_univ_of_mem_interior` in `Theorem_3_21`, the convexity
  theorem for the finite interior-point directional derivative;
- `subdifferential` in `Definition_3_1_5`, the chapter owner for subgradients, with notation
  `∂ f(x)`;
- `subdifferential_convexDirectionalDerivativeReal_at_zero_eq_subdifferential` and
  `convexDirectionalDerivativeReal_isGreatest_subgradientPairing_of_mem_interior` in
  `Theorem_3_21`, the canonical comparison and max-formula theorems for that owner surface.

Best owner abstraction:
- the finite directional-derivative owner `f′[hx0]`, derived in `Theorem_3_21` from the
  extended-valued owner `convexDirectionalDerivative`.

Primitive data:
- none in this file; the directional-derivative and subdifferential owners already live upstream.

Derived API:
- the convexity of `f′[hx0]` on all directions;
- the identity `∂₂ f′(x₀; 0) = ∂ f(x₀)`;
- the max formula for `f′(x₀; p)` over the subdifferential.

Source/core/bridge triage:
- source-facing: the three textbook clauses of Theorem 3.1.5.4;
- core/canonical: `convexDirectionalDerivative`, `f′[hx0]`, and `∂ f(x0)`;
- bridge/view: this recall-only item file.

The textbook states the theorem for proper convex functions on `ℝⁿ`. In the chapter API, the
properness content is absorbed by the effective-domain owner `dom f` and the interior hypothesis
`x0 ∈ interior (dom f)`, while the ambient space is generalized to the natural real normed or
inner-product setting. This file therefore recalls the exact upstream owner theorems rather than
introducing a second parallel theorem vocabulary.
-/

section DirectionalDerivative

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]

/- Theorem 3.1.5.4 (1): if `f` is convex on its effective domain and `x₀` lies in the interior of
that domain, then the directional derivative `p ↦ f′(x₀; p)` is a finite convex function on all
directions. The finiteness is built into the recalled owner surface `f′[hx0] : E → ℝ`. -/
recall convexDirectionalDerivativeReal_convexOn_univ_of_mem_interior

end DirectionalDerivative

section Subdifferential

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/- Theorem 3.1.5.4 (2): the subdifferential with respect to the direction variable of
`p ↦ f′(x₀; p)` at `0` equals the subdifferential of `f` at `x₀`. -/
recall subdifferential_convexDirectionalDerivativeReal_at_zero_eq_subdifferential

/- Theorem 3.1.5.4 (3): for every direction `p`, the directional derivative `f′(x₀; p)` is the
maximum of the pairings `⟪g, p⟫` over `g ∈ ∂ f(x₀)`, recorded in the owner API as an
`IsGreatest` statement. -/
recall convexDirectionalDerivativeReal_isGreatest_subgradientPairing_of_mem_interior

end Subdifferential
