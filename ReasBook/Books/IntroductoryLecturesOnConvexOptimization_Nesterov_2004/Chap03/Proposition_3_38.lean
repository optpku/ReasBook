/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import Mathlib.Analysis.Convex.Strong
import Mathlib.Tactic.Ring

-- Declarations for this item will be appended below by the statement pipeline.

universe u

/- Primary domain: weighted-sum closure for strong convexity on a fixed feasible set in a real
normed space.

Sampled owner-style declarations before refining this file:
* mathlib `StrongConvexOn`
* mathlib `UniformConvexOn.add`
* project `StrongConvexOn.add_convexOn` in `Chap02/Proposition_2_3`
* project `StrongConvexOnWith.nonneg_combo_inter` in `Chap02/Definition_2_14`

Best owner abstraction:
* `StrongConvexOn Q μ f`

Primitive data:
* the common feasible set `Q`
* the two strong-convexity owner hypotheses
* the nonnegative scalar weights

Derived API:
* strong convexity of the weighted sum with modulus `α₁ * μ₁ + α₂ * μ₂`

Source/core/bridge triage:
* bridge/view: this proposition is the same-domain weighted-sum closure rule for the canonical
  owner `StrongConvexOn`; it is not a second owner declaration
-/

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]

namespace StrongConvexOn

/-- Proposition 3.38: a nonnegative linear combination of two strongly convex functions on the
same convex domain is strongly convex, with strong-convexity parameter
`α₁ * μ₁ + α₂ * μ₂`. -/
-- Proof sketch: `StrongConvexOn` is the canonical `UniformConvexOn` owner with quadratic modulus.
-- Multiply the two owner inequalities by the nonnegative weights `α₁`, `α₂`, add them, and
-- collect the quadratic terms.
theorem nonneg_weighted_add
    {Q : Set E} {f₁ f₂ : E → ℝ} {μ₁ μ₂ α₁ α₂ : ℝ}
    (hf₁ : StrongConvexOn Q μ₁ f₁)
    (hf₂ : StrongConvexOn Q μ₂ f₂)
    (hα₁ : 0 ≤ α₁) (hα₂ : 0 ≤ α₂) :
    StrongConvexOn Q (α₁ * μ₁ + α₂ * μ₂) (α₁ • f₁ + α₂ • f₂) := by
  refine ⟨hf₁.1, ?_⟩
  intro x hx y hy a b ha hb hab
  have h₁ := mul_le_mul_of_nonneg_left (hf₁.2 hx hy ha hb hab) hα₁
  have h₂ := mul_le_mul_of_nonneg_left (hf₂.2 hx hy ha hb hab) hα₂
  have h := add_le_add h₁ h₂
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at h ⊢
  ring_nf at h ⊢
  exact h

end StrongConvexOn
