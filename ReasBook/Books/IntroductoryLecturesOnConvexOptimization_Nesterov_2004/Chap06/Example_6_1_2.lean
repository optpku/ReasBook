/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import Mathlib.Tactic.Recall
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap06.Proposition_6_5

-- Declarations for this item will be appended below by the statement pipeline.

universe u

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {p : Seminorm ℝ E} [Seminorm.IsNorm p]

/- Example 6.1.2 lies in the chapter's prox-function / prox-center quadratic-growth domain.

Primary domain:
- prox-functions and normalized prox-centers on real normed spaces

Sampled owner declarations:
- `NesterovIsProxFunction` in `Definition_6_31`, the chapter owner for prox-function data
- `NesterovIsProxCenter` in `Definition_6_31`, the chapter owner for normalized prox-center data
- `StrongConvexOnWith.quadratic_growth_of_isMinOn_of_mem` in `Chap02/Definition_2_14`, the
  canonical quadratic-growth theorem behind the chapter specialization
- `prox_center_quadratic_lower_bound` in `Proposition_6_5`, the exact chapter-level owner theorem
  for this lower bound

Best owner abstraction:
- source-facing: the quadratic lower bound at a normalized prox-center
- core/canonical: `NesterovIsProxFunction p Q d`, `NesterovIsProxCenter Q d x₀`, and
  `prox_center_quadratic_lower_bound`
- bridge/view: the source's differentiability wording is auxiliary here and does not enter the
  owner theorem, since the lower-bound proof uses only strong convexity, minimality, and the
  normalization `d x₀ = 0`

Primitive data:
- the feasible set `Q`
- the prox-function owner `hd : NesterovIsProxFunction p Q d`
- the normalized prox-center owner `hx₀ : NesterovIsProxCenter Q d x₀`
- the comparison point `u ∈ Q`

Derived API:
- `hd.strongConvexOnWith`
- `hx₀.mem`, `hx₀.isMinOn`, and `hx₀.value_eq_zero`
- the quadratic lower bound itself

This file therefore does not keep a second local theorem with the same mathematical content under
raw `DifferentiableOn` / `StrongConvexOn` / `IsMinOn` hypotheses. The exact owner theorem already
exists upstream in `Proposition_6_5`, so Example 6.1.2 should be a direct recall surface. -/

section

variable {Q : Set E} {d : E → ℝ} {x₀ u : E}

/- Example 6.1.2: a normalized prox-center of a prox-function on `Q` gives the quadratic lower
bound `d u ≥ (1 / 2) p(u - x₀)^2` at every feasible point `u ∈ Q`. -/
recall prox_center_quadratic_lower_bound
    (hd : NesterovIsProxFunction p Q d)
    (hx₀ : NesterovIsProxCenter Q d x₀)
    (hu : u ∈ Q) :
    d u ≥ (1 / 2 : ℝ) * (p (u - x₀)) ^ (2 : ℕ)

end
