/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Definition_3_1_5
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Definition_3_1_5_2

-- Declarations for this item will be appended below by the statement pipeline.

open scoped WithTopConvexAnalysis

/- Proposition 3.12 lies in the chapter's one-dimensional positive-part / subdifferential domain.

Relevant owner-style declarations sampled before refinement:
- `posPart`
- `posPart_def`
- `subdifferential`
- `mem_subdifferential_iff`

Best owner abstraction:
- the chapter owner `subdifferential`, specialized to the lifted positive-part map
  `fun x : ℝ ↦ ((x⁺ : ℝ) : WithTop ℝ)`

Primitive data:
- the canonical positive-part owner `x ↦ x⁺`
- the owner-level subgradient predicate from `mem_subdifferential_iff`

Derived API:
- the interval description of the source-facing subdifferential at `0`

Source/core/bridge triage:
- source-facing: the subdifferential of `x ↦ (x)_+` at `0`
- core/canonical: `subdifferential`
- bridge/view: `mem_subdifferential_iff`, `posPart_def`

This file therefore removes the duplicate raw set-builder formulation and states the textbook claim
directly on the chapter owner `∂ f(x)`, while keeping the same mathematical meaning. -/

/-- Helper for Proposition 3.12: on the real line, the inner product is ordinary multiplication. -/
lemma real_inner_eq_mul (g x : ℝ) : inner ℝ g x = g * x := by
  -- The one-dimensional Euclidean pairing is just scalar multiplication.
  simpa using (RCLike.inner_apply' g x)

/-- Helper for Proposition 3.12: the global support inequality for `x ↦ x⁺` forces the slope to
lie in `[0, 1]`. -/
lemma subgradient_bounds_of_posPart_support {g : ℝ}
    (hg : ∀ x : ℝ, x⁺ ≥ g * x) : 0 ≤ g ∧ g ≤ 1 := by
  constructor
  · -- Test the support inequality at `x = -1` to obtain the lower bound `0 ≤ g`.
    have hminus := hg (-1)
    have hminus' : 0 ≥ g * (-1 : ℝ) := by
      simpa [posPart_eq_ite] using hminus
    linarith
  · -- Test the support inequality at `x = 1` to obtain the upper bound `g ≤ 1`.
    have hplus := hg 1
    have hplus' : 1 ≥ g * (1 : ℝ) := by
      simpa [posPart_eq_ite] using hplus
    linarith

/-- Helper for Proposition 3.12: every slope `g ∈ [0, 1]` supports the positive-part function from
below at the origin. -/
lemma posPart_support_of_mem_Icc {g : ℝ} (hg : g ∈ Set.Icc (0 : ℝ) 1) :
    ∀ x : ℝ, x⁺ ≥ g * x := by
  intro x
  by_cases hx : 0 ≤ x
  · -- On the nonnegative ray, `x⁺ = x`, so it is enough to compare `g * x` with `x`.
    have hmul : g * x ≤ x := by
      have hmul' : g * x ≤ 1 * x := mul_le_mul_of_nonneg_right hg.2 hx
      simpa using hmul'
    simpa [posPart_eq_ite, hx] using hmul
  · -- On the nonpositive ray, `x⁺ = 0`, and `g * x ≤ 0` follows from `g ≥ 0`.
    have hx' : x ≤ 0 := le_of_not_ge hx
    have hmul : g * x ≤ 0 := by
      exact mul_nonpos_of_nonneg_of_nonpos hg.1 hx'
    simpa [posPart_eq_ite, hx] using hmul

/-- Proposition 3.12: for `f(x) = (x)_+`, the subdifferential at `0` is exactly the interval
`[0, 1]`. -/
-- Proof sketch: rewrite membership in the owner subdifferential `∂ f(0)` via
-- `mem_subdifferential_coe_real_iff`, which produces the textbook support inequality
-- `x⁺ ≥ g * x`. Testing at `x = -1` and `x = 1` gives `0 ≤ g ≤ 1`. Conversely, if
-- `g ∈ [0, 1]`, then `g * x ≤ x⁺` follows from the cases `x ≥ 0` and `x ≤ 0`.
theorem real_posPart_subdifferential_at_zero_eq_Icc :
    ∂ (fun x : ℝ ↦ (x⁺ : ℝ))(0) = Set.Icc (0 : ℝ) 1 := by
  ext g
  rw [Set.mem_Icc, mem_subdifferential_coe_real_iff]
  -- Rewrite the owner-level subgradient condition into the scalar support inequality from the
  -- source proof.
  constructor
  · intro hg
    -- The forward inclusion is exactly the endpoint test from the source proof.
    exact subgradient_bounds_of_posPart_support (fun x ↦ by
      have hx := hg x
      simpa [real_inner_eq_mul, sub_eq_add_neg] using hx)
  · intro hg x
    -- The reverse inclusion is the two-case sign split proving `x⁺ ≥ g * x`.
    have hx := posPart_support_of_mem_Icc hg x
    simpa [real_inner_eq_mul, sub_eq_add_neg] using hx
