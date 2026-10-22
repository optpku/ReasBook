/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import FirstOrderMethodsOptimization_Beck_2017.Chap06.Theorem_6_6
import FirstOrderMethodsOptimization_Beck_2017.Chap10.Definition_10_2
import FirstOrderMethodsOptimization_Beck_2017.Chap11.Definition_11_4
import FirstOrderMethodsOptimization_Beck_2017.Chap14.Algorithm_14_1
import FirstOrderMethodsOptimization_Beck_2017.Chap14.AlternatingMinimizationCompositeModel

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u

open scoped BigOperators

section

variable {p : ℕ} {Ei : Fin p → Type u}

/- `prompt_add/` is absent in this workspace, so the statement design is sampled directly from the
nearby optimization API.

This item is `source-facing`: it does not introduce a new global optimization problem, but rewrites
the Chapter 14 alternating-minimization step for the composite objective
`x ↦ f x + ∑ i, g_i (x_i)` into the displayed one-block minimization formula. In this item file,
the generic block-state geometry is already owned by Algorithm 14.1 and is reused directly here.

Domain sampling against the local project identifies the relevant owners:
- the Chapter 14 block-update geometry, formalized here by
  `alternating_minimization_partial_state` and `alternating_minimization_block_objective`;
- the Chapter 6 block-separable owner `separableSum` and the Chapter 10 composite-objective owner
  `composite_model_objective` for `x ↦ f x + ∑ i, g_i (x_i)`;
- Chapter 2's `IsProperExtendedRealFunction`, `LowerSemicontinuous`,
  `is_convex_function`, and `effective_domain` for the standing assumptions;
- mathlib's `ContinuousOn`, `DifferentiableOn`, and `IsMinOn` for continuity,
  differentiability, and argmin statements.

Accordingly, the assumptions are recorded as a small Prop-valued class on `(f, g)`. Its primitive
data follow the same owner discipline as the Chapter 10/11 composite-model APIs: the smooth term
must explicitly exclude the pathological value `⊥`, while properness of `f` itself is derived
from that clause together with the block-separable properness and domain-compatibility
hypotheses. The algorithmic content is then recorded as a one-step predicate on `(xk, xNext)`
rather than by choosing a recursive update map. -/

/-- The one-block composite objective in Algorithm 14.3 is obtained by freezing the earlier
blocks at their updated values from `xNext`, the later blocks at their old values from `xk`, and
keeping only the active penalty term `g_i(xi)` variable. -/
def alternating_minimization_composite_block_objective
    (f : ((i : Fin p) → Ei i) → EReal)
    (g : (i : Fin p) → Ei i → EReal)
    (xk xNext : (i : Fin p) → Ei i) (i : Fin p) : Ei i → EReal :=
  composite_model_objective
    (alternating_minimization_block_objective f xk xNext i)
    (g i)

-- Proof sketch: unfold `alternating_minimization_composite_block_objective`; evaluation at `xi`
-- is definitionally the displayed Algorithm 14.3 one-block objective.
/-- Evaluating the composite one-block objective at `xi` gives the textbook expression
`f(x_1^{k+1}, ..., x_{i-1}^{k+1}, xi, x_{i+1}^k, ..., x_p^k) + g_i(xi)`. -/
@[simp] theorem alternating_minimization_composite_block_objective_apply
    (f : ((i : Fin p) → Ei i) → EReal)
    (g : (i : Fin p) → Ei i → EReal)
    (xk xNext : (i : Fin p) → Ei i) (i : Fin p) (xi : Ei i) :
    alternating_minimization_composite_block_objective f g xk xNext i xi =
      f (alternating_minimization_partial_state xk xNext i xi) + g i xi :=
  by
    simp [alternating_minimization_composite_block_objective]

variable [∀ i, NormedAddCommGroup (Ei i)]
variable [∀ i, NormedSpace ℝ (Ei i)]

/-- Algorithm 14.3: under Assumption 14.6, one alternating-minimization step from `xk` to
`xNext` for the composite model `f + ∑ i, g_i` means that, for each block
`i : Fin p` corresponding to textbook block `i + 1`, the updated block `xNext i` globally
minimizes
`xi ↦ f(x_1^{k+1}, ..., x_{i-1}^{k+1}, xi, x_{i+1}^k, ..., x_p^k) + g_i(xi)`. -/
class IsAlternatingMinimizationCompositeStep
    (f : ((i : Fin p) → Ei i) → EReal)
    (g : (i : Fin p) → Ei i → EReal)
    (xk xNext : (i : Fin p) → Ei i) : Prop
    extends IsAlternatingMinimizationCompositeModel f g where
  block_isMinOn (i : Fin p) :
    IsMinOn
      (alternating_minimization_composite_block_objective f g xk xNext i)
      Set.univ
      (xNext i)

namespace IsAlternatingMinimizationCompositeStep

variable {f : ((i : Fin p) → Ei i) → EReal}
variable {g : (i : Fin p) → Ei i → EReal}
variable {xk xNext : (i : Fin p) → Ei i}

/-- An Algorithm 14.3 composite step carries the standing composite-model assumptions. -/
instance instIsAlternatingMinimizationCompositeModel
    (h : IsAlternatingMinimizationCompositeStep f g xk xNext) :
    IsAlternatingMinimizationCompositeModel f g :=
  h.toIsAlternatingMinimizationCompositeModel

end IsAlternatingMinimizationCompositeStep

end
