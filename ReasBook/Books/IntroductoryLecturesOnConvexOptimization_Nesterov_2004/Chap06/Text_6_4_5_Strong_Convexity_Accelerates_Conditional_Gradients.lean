/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import Mathlib.Tactic.Recall
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Definition_3_2_2

-- Declarations for this item will be appended below by the statement pipeline.

/- Text 6.4.5 is a recall-only bridge in the Chapter 6 conditional-gradient / strong-convexity
domain.

Primary domain:
- strong convexity of a real-valued regularizer on a feasible set, expressed through the standard
  quadratic segment upper bound.

Sampled owner-style declarations:
- `StrongConvexOn` from mathlib;
- `strongConvexOn_iff_quadratic_jensen_bound` in `Nesterov.Chap02.Theorem_2_10`;
- `exists_pos_strongConvexOn_iff_forall_segment_upper_bound` in
  `Nesterov.Chap03.Definition_3_2_2`;
- `𝒮^0_μ(Q)` / `StrongConvexOn Q μ f` in `Nesterov.Chap03.Definition_3_47`.

Best owner abstraction:
- source-facing: the positive-modulus strong-convexity assumption used in the text;
- core/canonical: `StrongConvexOn Q μ f`;
- bridge/view: `exists_pos_strongConvexOn_iff_forall_segment_upper_bound`.

Primitive data:
- a feasible set `Q`;
- a real-valued function `Ψ` on the ambient space.

Derived API:
- convexity of `Q` together with the segment inequality;
- the equivalent canonical owner expression `∃ μ > 0, StrongConvexOn Q μ Ψ`.

Source/core/bridge triage:
- source-facing: Text 6.4.5's standing assumption for the accelerated conditional-gradient regime;
- core/canonical: `StrongConvexOn`;
- bridge/view: the chapter equivalence between the textbook segment inequality and positive-modulus
  strong convexity.

Text 6.4.5 does not define a new owner beyond the chapter's strong-convexity API. The correct
public surface is therefore a direct recall of the existing bridge theorem, not a parallel local
wrapper around the same condition. -/

/- Text 6.4.5-Strong Convexity Accelerates Conditional Gradients: the standing assumption for the
composite conditional-gradient regime is that `Ψ` is strongly convex on the feasible set `Q`,
which means exactly that `Q` is convex and there exists a positive constant `σΨ` such that for
all `x, y ∈ Q` and all `τ ∈ [0,1]`,
`Ψ (τ • x + (1 - τ) • y) ≤ τ * Ψ x + (1 - τ) * Ψ y - (σΨ / 2) * τ * (1 - τ) * ‖x - y‖ ^ 2`.
This is the curvature assumption used later for the faster rate of method `(6.4.12)`. -/
recall exists_pos_strongConvexOn_iff_forall_segment_upper_bound
