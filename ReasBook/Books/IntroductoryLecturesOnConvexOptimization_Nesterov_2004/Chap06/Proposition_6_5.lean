/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap06.Definition_6_31

-- Declarations for this item will be appended below by the statement pipeline.

universe u

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {p : Seminorm ℝ E} [Seminorm.IsNorm p]

/- Proposition 6.5 lies in the chapter's prox-function / prox-center quadratic-growth domain.

Sampled owner declarations in this domain:
- `NesterovIsProxFunction` in `Definition_6_31`, the chapter owner for prox-function data;
- `NesterovIsProxCenter` in `Definition_6_31`, the chapter owner for normalized prox-center data;
- `StrongConvexOnWith.quadratic_growth_of_isMinOn_of_mem` in `Chap02/Definition_2_14`, the
  canonical quadratic-growth theorem behind the prox-center lower bound.

Best owner abstraction:
- source-facing: the normalized prox-center lower bound;
- core/canonical: `NesterovIsProxFunction p Q₂ d₂`, `NesterovIsProxCenter Q₂ d₂ u₀`, and the owner theorem
  `prox_center_quadratic_lower_bound`;
- bridge/view: `StrongConvexOnWith.quadratic_growth_of_isMinOn_of_mem`.

Primitive data:
- the prox-function owner `hd₂ : NesterovIsProxFunction p Q₂ d₂`;
- the prox-center owner `hu₀ : NesterovIsProxCenter Q₂ d₂ u₀`;
- the feasible comparison point `u ∈ Q₂`.

Derived API:
- `hd₂.strongConvexOnWith`;
- `hu₀.mem`, `hu₀.isMinOn`, and `hu₀.value_eq_zero`;
- the quadratic lower bound itself.

The previous version duplicated the proposition theorem upstream in `Definition_6_31`, which left
the chapter with two owners of the same global declaration name. This file now restores the
numbered proposition as the sole owner of the lower bound, while `Definition_6_31` keeps only the
prox-function and prox-center data.
-/

section

variable {Q₂ : Set E} {d₂ : E → ℝ} {u₀ u : E}

/- Proposition 6.5: a normalized prox-center of a prox-function on `Q₂` gives the lower bound
`d₂ u ≥ (1 / 2) p(u - u₀)^2` at every feasible point `u ∈ Q₂`. -/
theorem prox_center_quadratic_lower_bound
    (hd₂ : NesterovIsProxFunction p Q₂ d₂)
    (hu₀ : NesterovIsProxCenter Q₂ d₂ u₀)
    (hu : u ∈ Q₂) :
    d₂ u ≥ (1 / 2 : ℝ) * (p (u - u₀)) ^ (2 : ℕ) := by
  have hquad :
      d₂ u ≥ d₂ u₀ + (1 / 2 : ℝ) * (p (u - u₀)) ^ (2 : ℕ) :=
    hd₂.strongConvexOnWith.quadratic_growth_of_isMinOn_of_mem hu₀.mem hu₀.isMinOn u hu
  simpa [hu₀.value_eq_zero] using hquad

end
