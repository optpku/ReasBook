/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Order.Filter.Basic

open Filter

section Convergence

variable {E : Type*} [NormedAddCommGroup E]

/-- A sequence converges linearly to `xStar` when it converges to `xStar` and admits a
uniform one-step contraction factor strictly between `0` and `1`. -/
@[mk_iff hasLinearConvergenceTo_iff]
class HasLinearConvergenceTo (x : ℕ → E) (xStar : E) : Prop where
  tendsto : Tendsto x atTop (nhds xStar)
  contraction :
    ∃ c ∈ Set.Ioo (0 : ℝ) 1, ∀ k : ℕ, ‖x (k + 1) - xStar‖ ≤ c * ‖x k - xStar‖

/-- A sequence converges eventually linearly to `xStar` when it converges to `xStar` and,
from some index onward, admits a uniform one-step contraction factor strictly between `0`
and `1`. -/
@[mk_iff hasEventuallyLinearConvergenceTo_iff]
class HasEventuallyLinearConvergenceTo (x : ℕ → E) (xStar : E) : Prop where
  tendsto : Tendsto x atTop (nhds xStar)
  eventualContraction :
    ∃ c ∈ Set.Ioo (0 : ℝ) 1,
      ∀ᶠ k in atTop, ‖x (k + 1) - xStar‖ ≤ c * ‖x k - xStar‖

/-- A sequence converges superlinearly to `xStar` when it converges to `xStar` and its
next-step error is little-o of the current error. -/
@[mk_iff hasSuperlinearConvergenceTo_iff]
class HasSuperlinearConvergenceTo (x : ℕ → E) (xStar : E) : Prop where
  tendsto : Tendsto x atTop (nhds xStar)
  isLittleO : (fun k ↦ ‖x (k + 1) - xStar‖) =o[atTop] fun k ↦ ‖x k - xStar‖

/-- A sequence converges quadratically to `xStar` when it converges to `xStar` and its
next-step error is `O(‖x k - xStar‖^2)` along `atTop`. -/
@[mk_iff hasQuadraticConvergenceTo_iff]
class HasQuadraticConvergenceTo (x : ℕ → E) (xStar : E) : Prop where
  tendsto : Tendsto x atTop (nhds xStar)
  isBigO : (fun k ↦ ‖x (k + 1) - xStar‖) =O[atTop] fun k ↦ ‖x k - xStar‖ ^ (2 : ℕ)

end Convergence
