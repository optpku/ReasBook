/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import Mathlib.Tactic.Recall
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Theorem_3_21

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open scoped WithTopConvexAnalysis

open scoped Topology

variable {n : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin n)

/- Theorem 3.1.17 is a `bridge/view` Euclidean specialization in the chapter's convex
directional-derivative domain.

Primary domain:
- convex directional derivatives and subdifferentials of `ℝ ∪ {+∞}`-valued functions on `ℝⁿ`.

Relevant owner-style declarations sampled before refinement:
- `convexDirectionalDerivative` in `Theorem_3_21`, the chapter owner for the extended-valued
  directional derivative;
- `subdifferential_convexDirectionalDerivativeReal_at_zero_eq_subdifferential` in
  `Theorem_3_21`, the canonical subdifferential comparison theorem;
- `convexDirectionalDerivativeReal_isGreatest_subgradientPairing_of_mem_interior` in
  `Theorem_3_21`, the canonical max-formula theorem;
- `dom`, `withTopRealPart`, and `subdifferential` from `Definition_3_3` and `Definition_3_1_5`,
  which already own the effective-domain and subgradient vocabulary used here.

Best owner abstraction:
- the chapter owner `convexDirectionalDerivative`, together with the canonical finite
  theorem-level `toReal` view used under interior hypotheses, and the
  subdifferential owner `∂ f(x)`.

Primitive data:
- none in this file; the directional-derivative construction and subdifferential owners are
  already defined upstream.

Derived API:
- this Euclidean recall surface for the subdifferential identity and max formula.

Source/core/bridge triage:
- source-facing: the Euclidean specialization of the directional-derivative subdifferential
  identity and max formula;
- core/canonical: `convexDirectionalDerivative` and `subdifferential`;
- bridge/view: this recall file.

The previous version redefined the effective domain, finite real part, subdifferential, and
directional derivative locally on `ℝⁿ`. Those were duplicate wheels once `Theorem_3_21`,
`Definition_3_3`, and `Definition_3_1_5` became the chapter owners. This file now reuses the
canonical owner vocabulary directly and keeps only the Euclidean specialization layer. -/

section Subdifferential

variable {f : E → WithTop ℝ} {x0 : E}

/-- Theorem 3.1.17: for a convex `ℝ ∪ {+∞}`-valued function on `ℝⁿ`, the
subdifferential with respect to the direction variable of `p ↦ f'(x₀; p)` at
`0` coincides with the subdifferential of `f` at `x₀`. The companion
directional-derivative max formula is recalled immediately below in the
canonical `IsGreatest` owner form. -/
-- This Euclidean bridge theorem restates the owner-level subdifferential
-- identity already proved upstream in `Theorem_3_21`.
theorem convexDirectionalDerivativeReal_subdifferential_eq_at_zero
    (hf : ConvexOn ℝ (dom f) (withTopRealPart f))
    (hx0 : x0 ∈ interior (dom f)) :
    ∂[Set.univ] f′[hx0](0) = ∂ f(x0) :=
  subdifferential_convexDirectionalDerivativeReal_at_zero_eq_subdifferential
    hf hx0

/-- The companion max formula is recorded in the canonical greatest-element
form for the image of the subdifferential under `g ↦ ⟪g, p⟫`. -/
-- The recalled `IsGreatest` formulation is the chapter-owner form of the textbook maximum claim.
recall convexDirectionalDerivativeReal_isGreatest_subgradientPairing_of_mem_interior

end Subdifferential

end
