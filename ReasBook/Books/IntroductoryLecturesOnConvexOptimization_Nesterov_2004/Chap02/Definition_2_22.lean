/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap02.Definition_2_17

-- Declarations for this item will be appended below by the statement pipeline.

open scoped StrongConvexSmooth

/- This item lies in the smooth strongly convex minimization domain.

Sampled owner-style declarations in this domain:
* `IsStrongConvexSmoothObjective` in `Definition_2_17`, which owns the objective-side
  `μ`-strong-convexity and `L`-gradient-Lipschitz assumptions;
* `𝓢[μ, L]¹¹` and `q[μ, L]` in `Definition_2_17`, which give the chapter's source-facing class
  and reciprocal-condition-number notation;
* `IsStrongConvexSmoothObjective.mu_pos`, showing that positivity of `μ` is primitive data of
  that owner predicate;
* `IsStrongConvexSmoothObjective.mu_le_L`, showing on nontrivial ambient spaces that admissible
  owner parameters satisfy `μ ≤ L`, so the ratio `μ / L` is the canonical reciprocal
  condition-number scalar seen downstream;
* `ConstantStepSchemeIII` in `Proposition_2_12`, a downstream chapter consumer that takes the
  reciprocal condition number directly as the scalar input `μ / L`.

Best abstraction triage:
* source-facing: the strongly convex smooth class `𝓢[μ, L]¹¹` together with the reciprocal
  condition-number notation `q[μ, L]`;
* core/canonical: `IsStrongConvexSmoothObjective μ L f`;
* bridge/view: the definitional identification `q[μ, L] = μ / L`.

Primitive data:
* the strong-convexity parameter `μ`;
* the gradient-Lipschitz constant `L`;
* an objective `f` together with the owner hypothesis
  `IsStrongConvexSmoothObjective μ L f`.

Derived API:
* the reciprocal condition number `q_f = q[μ, L] = μ / L`.

Definition 2.22 therefore uses the chapter owner and its source-facing notation directly. It adds
no wrapper predicate and no packaged reciprocal-condition-number object beyond the notation
`q[μ, L]`. -/

section

variable (μ L : ℝ)

/- Definition 2.22: for a `μ`-strongly convex function with `L`-Lipschitz continuous gradient,
the textbook reciprocal condition number `q_f` is the chapter scalar `q[μ, L]`, namely the
reciprocal of `Q_f` and concretely the ratio `μ / L`. -/
#check (rfl : q[μ, L] = μ / L)

end
