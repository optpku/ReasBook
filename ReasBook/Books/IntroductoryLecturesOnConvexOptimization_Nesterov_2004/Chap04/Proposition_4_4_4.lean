/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap04.Definition_4_4_1
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap04.Definition_4_4_10

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

variable {E₁ : Type u} {E₂ : Type v} [Zero E₂]

/- Proposition 4.4.4 lies in the merit-scalarization / nonlinear-system-solvability domain.

Sampled owner-style declarations:
* `IsMeritFunction` in `Definition_4_4_1`, the chapter owner for nonnegative residual
  scalarizations vanishing exactly at `0`
* `IsMeritFunction.eq_zero_iff`, the owner zero-detection theorem for merit functions
* `IsMinOn` in mathlib, the canonical owner for minimizers on a set
* `isMinOn_univ_iff` in mathlib, the textbook bridge from `IsMinOn ... Set.univ ...` to the
  pointwise inequality form

Best owner abstraction:
* source-facing: solvability of `F x = 0` detected through the merit reformulation
  `meritFunctionReformulation F φ` at a global minimizer
* core/canonical: `IsMeritFunction φ` together with `IsMinOn (fun x ↦ φ (F x)) Set.univ xStar`
* bridge/view: the zero-detection consequence obtained by specializing
  `IsMeritFunction.eq_zero_iff` to residuals of the form `F x`

Primitive data:
* the residual map `F`
* the merit scalarizer `φ`
* the chosen minimizer `xStar`

Derived API:
* the residual zero-detection step `φ (F x) = 0 ↔ F x = 0`
* the minimizer comparison
  `meritFunctionReformulation F φ xStar ≤ meritFunctionReformulation F φ x` for every `x`

Source/core/bridge triage:
* source-facing: the iff between solvability of `F x = 0` and vanishing minimum merit value of
  `meritFunctionReformulation F φ`
* core/canonical: `IsMeritFunction` and `IsMinOn`
* bridge/view: specializing the owner zero-detection theorem to `F x`

The theorem surface is organized around the canonical owners
`meritFunctionReformulation F φ` and `IsMinOn`, rather than a parallel free-standing wrapper for
the same minimizer data. The proof still derives the zero-detection step directly from
`IsMeritFunction.eq_zero_iff`.
-/

-- Proof sketch: if `F x = 0` for some `x`, then `IsMeritFunction.eq_zero_iff` gives
-- `φ (F x) = 0`, and the minimizer inequality at `xStar` forces the minimum value to be at most
-- `0`; `IsMeritFunction.nonneg` makes it exactly `0`. Conversely, if the minimizing value at
-- `xStar` is `0`, then `IsMeritFunction.eq_zero_iff` gives `F xStar = 0`, so `xStar` solves the
-- nonlinear system.

/-- Any exact solution `F xStar = 0` globally minimizes the merit reformulation when the merit
function is nonnegative and vanishes only at the zero residual. -/
theorem exact_solution_isMinOn_meritFunctionReformulation
    {F : E₁ → E₂} {φ : E₂ → ℝ} [IsMeritFunction φ] {xStar : E₁}
    (hxStar : F xStar = 0) :
    IsMinOn (meritFunctionReformulation F φ) Set.univ xStar := by
  rw [isMinOn_univ_iff]
  intro x
  have hxStar_zero : meritFunctionReformulation F φ xStar = 0 := by
    simpa using (IsMeritFunction.eq_zero_iff (F xStar)).2 hxStar
  rw [hxStar_zero]
  simpa using IsMeritFunction.nonneg (F x)

namespace IsMinOn

/-- Proposition 4.4.4: if `xStar` realizes the minimum value `f*` of the merit reformulation
`meritFunctionReformulation F φ`, and `φ` is nonnegative and vanishes only at the zero residual,
then that minimum value is `0` if and only if the nonlinear equation `F x = 0` is solvable. -/
theorem meritFunctionReformulation_eq_zero_iff_exists_zero_residual
    {F : E₁ → E₂} {φ : E₂ → ℝ} [IsMeritFunction φ] {xStar : E₁}
    (hxStar : IsMinOn (meritFunctionReformulation F φ) Set.univ xStar) :
    meritFunctionReformulation F φ xStar = 0 ↔ ∃ x : E₁, F x = 0 := by
  constructor
  · intro hxStar_zero
    exact ⟨xStar, (IsMeritFunction.eq_zero_iff (F xStar)).1 hxStar_zero⟩
  · rintro ⟨x, hx⟩
    have hx_zero : meritFunctionReformulation F φ x = 0 := by
      simpa using (IsMeritFunction.eq_zero_iff (F x)).2 hx
    have hxMin : IsMinOn (meritFunctionReformulation F φ) Set.univ x :=
      exact_solution_isMinOn_meritFunctionReformulation hx
    have hxStar_le_x :
        meritFunctionReformulation F φ xStar ≤ meritFunctionReformulation F φ x :=
      (isMinOn_univ_iff.mp hxStar) x
    have hx_le_xStar :
        meritFunctionReformulation F φ x ≤ meritFunctionReformulation F φ xStar :=
      (isMinOn_univ_iff.mp hxMin) xStar
    exact le_antisymm (hx_zero ▸ hxStar_le_x) (hx_zero ▸ hx_le_xStar)

end IsMinOn
