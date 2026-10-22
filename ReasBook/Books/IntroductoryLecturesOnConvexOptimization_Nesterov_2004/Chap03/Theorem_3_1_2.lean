/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

/- Theorem 3.1.2 is recall-only in the real convex-analysis / epigraph domain.

Primary domain:
- convexity of the epigraph of a real-valued function on a convexity domain, with the textbook
  specialization `s ⊆ ℝⁿ`.

Sampled owner-style declarations:
- mathlib `ConvexOn`;
- mathlib `ConvexOn.convex_epigraph`;
- mathlib `convexOn_iff_convex_epigraph`;
- the chapter bridge `convexOn_iff_convex_effective_epigraph` in `Theorem_3_3`, which handles the
  `WithTop ℝ`-valued effective-epigraph variant by reducing to the same owner theorem.

Best owner abstraction:
- `convexOn_iff_convex_epigraph`.

Primitive data:
- a scalar type `𝕜`, ambient module `E`, and codomain ordered additive module `β` in the owner
  theorem;
- in the textbook specialization, `𝕜 = ℝ`, `E = EuclideanSpace ℝ (Fin n)`, and `β = ℝ`.

Derived API:
- convexity of the epigraph `{p : E × ℝ | p.1 ∈ s ∧ f p.1 ≤ p.2}`;
- the one-direction owner theorem `ConvexOn.convex_epigraph`.

Source/core/bridge triage:
- source-facing: the Euclidean textbook epigraph characterization of convexity;
- core/canonical: mathlib `convexOn_iff_convex_epigraph`;
- bridge/view: the Euclidean specialization recorded below.

The previous declaration `convexOn_iff_convex_epigraph_euclidean` was an exact-interface duplicate
of the mathlib owner theorem. This file therefore recalls the canonical owner directly instead of
keeping a second public theorem name for the same mathematics; the textbook Euclidean statement is
its immediate specialization.
-/

recall convexOn_iff_convex_epigraph
