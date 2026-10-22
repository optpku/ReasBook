/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import FirstOrderMethodsOptimization_Beck_2017.Chap02.Definition_2_2
import FirstOrderMethodsOptimization_Beck_2017.Chap02.Definition_2_9
import FirstOrderMethodsOptimization_Beck_2017.Chap04.Definition_4_1

-- Declarations for this item will be appended below by the statement pipeline.

universe u

section

variable {E : Type u} [AddCommGroup E] [Module ℝ E]

/- Proposition 4.1 is `source-facing`. Its owner abstractions already exist upstream:
the indicator notation `δ_ C` in Chapter 2, the support-function notation `σ_ C` in Chapter 2,
and `conjugate_function` in Definition 4.1. This file therefore keeps only the
indicator-conjugate identity itself. -/
-- Semantic recall: `lean_leansearch` did not surface a project-specific conjugate/support-function
-- identity, so this item keeps the faithful source-facing statements directly.

-- Proof sketch: on `C`, the indicator term vanishes, so the conjugate integrand is `y x`; outside
-- `C`, the indicator term is `⊤`, so the integrand is `⊥`. Hence the supremum over all `x`
-- agrees with the supremum over `C`.
/-- Proposition 4.1: equations (4.2) and (4.3) identify the Fenchel conjugate of the indicator
function `δ_C` with the support function `σ_C`. -/
theorem conjugate_function_extendedIndicator_eq_support_function (C : Set E) :
    conjugate_function (δ_ C) = σ_ C := by
  funext y
  rw [conjugate_function_apply, support_function_apply]
  apply le_antisymm
  · refine sSup_le ?_
    rintro r ⟨x, rfl⟩
    by_cases hx : x ∈ C
    · simpa [extendedIndicator, hx] using le_support_function_of_mem hx y
    · simp [extendedIndicator, hx]
  · refine sSup_le ?_
    rintro r ⟨x, hx, rfl⟩
    exact le_sSup (Set.mem_range.mpr ⟨x, by simp [extendedIndicator, hx]⟩)

-- Proof sketch: apply the function identity of Proposition 4.1 to the dual argument `y`.
/-- The pointwise form of Proposition 4.1: the Fenchel conjugate of `δ_C` at `y` is the support
function `σ_C (y)`. -/
theorem conjugate_function_extendedIndicator_apply_eq_support_function (C : Set E)
    (y : Module.Dual ℝ E) :
    conjugate_function (δ_ C) y = (σ_ C) y := by
  simpa using congrFun (conjugate_function_extendedIndicator_eq_support_function C) y

end
