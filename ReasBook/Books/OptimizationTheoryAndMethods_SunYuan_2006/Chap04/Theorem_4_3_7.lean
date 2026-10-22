/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Order.Filter.Extr
import OptimizationTheoryAndMethods_SunYuan_2006.Chap01.Definition_1_4_7
import OptimizationTheoryAndMethods_SunYuan_2006.Chap04.Algorithm_4_2_2
import OptimizationTheoryAndMethods_SunYuan_2006.Chap04.Algorithm_4_2_extra_4
import OptimizationTheoryAndMethods_SunYuan_2006.Chap04.Assumption_4_3_extra_1

noncomputable section

open Filter

section

variable {n : ℕ}

local notation "Point" => ConjugateGradientPoint n

-- Domain sampling pass:
-- * primary domain: local asymptotic rate statements for nonlinear conjugate-gradient restart
--   methods on `ℝ^n`;
-- * inspected owner declarations in this domain:
--   - `PolakRibierePolyakConjugateGradientMethod` from `Algorithm_4_2_extra_4`;
--   - `PeriodicRestartFRConjugateGradientMethod` from `Algorithm_4_2_2`;
--   - `HasBoundedLowerLevelSetHessianBounds` from `Assumption_4_3_extra_1`;
--   - `IsStationaryPoint` from `Chapter01.Definition_1_4_7`;
-- * best owner abstraction: keep the four labeled rate theorems source-facing, but factor their
--   repeated standing hypotheses into small `Prop`-valued restart-rate assumption owners over
--   the existing chapter method owners;
-- * layer targeted here: `source-facing` theorem statements over those restart-rate owners, with
--   mathlib's asymptotic owners `=O[atTop]` and `=o[atTop]` used directly instead of local
--   witness wrappers;
-- * primitive data: the method, restart period, distinguished point `xStar`, lower-level-set
--   membership of the iterates, convergence to `xStar`, and stationarity of `xStar`;
-- * derived API here: the source quadratic and superquadratic asymptotic conclusions, together
--   with the boundedness companion inherited from the Hessian-bound assumption owner.

/-- Shared Chapter 4.3.7 standing assumptions: the recorded iterates stay in the canonical lower
level set `lowerLevelSetOn Set.univ f x0`, that lower level set satisfies the Chapter 4 Hessian
bounds, the iterate sequence converges to `xStar`, and `xStar` is stationary for `f`. This is
the common source-facing setup reused by both the PRP and restart Fletcher-Reeves rate theorems.
-/
class HasRestartRateCoreAssumptions
    (f : Point → ℝ) (x0 : Point) (x : ℕ → Point) (xStar : Point) : Prop where
  hessianBounds : HasBoundedLowerLevelSetHessianBounds f x0
  iteratesMem : ∀ k : ℕ, x k ∈ lowerLevelSetOn Set.univ f x0
  tendsto : Tendsto x atTop (nhds xStar)
  stationary : IsStationaryPoint f xStar

/-- The common Chapter 4.3.7 setup inherits boundedness of the canonical lower level set from
Assumption 4.3-extra-1. -/
theorem HasRestartRateCoreAssumptions.levelSet_bounded
    {f : Point → ℝ} {x0 : Point} {x : ℕ → Point} {xStar : Point}
    (h : HasRestartRateCoreAssumptions f x0 x xStar) :
    Bornology.IsBounded (lowerLevelSetOn Set.univ f x0) :=
  h.hessianBounds.levelSet_bounded

namespace PolakRibierePolyakConjugateGradientMethod

/-- Chapter 4.3.7 PRP setup: the common restart-rate assumptions hold for the PRP iterates, the
restart period is positive, and every `r`-th search direction is reset to steepest descent. -/
class HasRestartRateAssumptions {f : Point → ℝ}
    (method : PolakRibierePolyakConjugateGradientMethod n f) (r : ℕ) (xStar : Point) : Prop extends
    HasRestartRateCoreAssumptions f method.x0 method.x xStar where
  restartPeriod_pos : 0 < r
  periodicRestart : ∀ k : ℕ, method.d (k * r) = -method.g (k * r)

end PolakRibierePolyakConjugateGradientMethod

namespace PeriodicRestartFRConjugateGradientMethod

/-- Chapter 4.3.7 restart Fletcher-Reeves setup: the common restart-rate assumptions hold for the
periodic-restart F-R iterates, and the restart period is positive. -/
class HasRestartRateAssumptions {r : ℕ} {f : Point → ℝ}
    (method : PeriodicRestartFRConjugateGradientMethod n r f) (xStar : Point) : Prop extends
    HasRestartRateCoreAssumptions f method.x0 method.x xStar where
  restartPeriod_pos : 0 < r

end PeriodicRestartFRConjugateGradientMethod

section PolakRibierePolyak

variable (f : Point → ℝ)
variable (method : PolakRibierePolyakConjugateGradientMethod n f)
variable (r : ℕ) (xStar : Point)

/-- Chapter04 Theorem 4.3.7 (1): let `method` be a PRP-CG run, let `xStar = x*` be the source
limit point, and package the source standing hypotheses into
`h : PolakRibierePolyakConjugateGradientMethod.HasRestartRateAssumptions method r xStar`:
restart every `r > 0` steps, every iterate stays
in the bounded lower level set `lowerLevelSetOn Set.univ f method.x0` carrying the `(A1)`/`(A2)`
Hessian bounds, the iterates converge to `xStar`, and `xStar` is stationary for `f`. Then the
source `n`-step quadratic rate conclusion `(4.3.42)` is encoded canonically as a big-`O`
statement for the error vector, with right-hand side the squared source error norm
`dist (x_(k r), x*)²`. This is equivalent to the displayed source norm formula
`‖x_(k r + n) - x*‖ = O(‖x_(k r) - x*‖²)`. -/
theorem polakRibierePolyakRestart_nStepQuadraticRate
    (h : PolakRibierePolyakConjugateGradientMethod.HasRestartRateAssumptions method r xStar) :
    ((fun k : ℕ ↦ (method.x (k * r + n) : Point) - xStar) : ℕ → Point) =O[atTop]
      ((fun k : ℕ ↦ dist (method.x (k * r)) xStar ^ (2 : ℕ)) : ℕ → ℝ) := sorry

/-- Chapter04 Theorem 4.3.7 (3): under the same PRP restart hypotheses as in `(1)`, Ritter's
stronger source conclusion says that for `xStar = x*`, the `n`-step superquadratic estimate
`(4.3.43)` holds directly, encoded canonically as a little-`o` statement on the error vector with
right-hand side `dist (x_k, x*)²`; this is equivalent to the displayed source norm formula
`‖method.x (k + n) - x*‖ = o(‖method.x k - x*‖²)`. -/
theorem polakRibierePolyakRestart_nStepSuperquadratic
    (h : PolakRibierePolyakConjugateGradientMethod.HasRestartRateAssumptions method r xStar) :
    ((fun k : ℕ ↦ (method.x (k + n) : Point) - xStar) : ℕ → Point) =o[atTop]
      ((fun k : ℕ ↦ dist (method.x k) xStar ^ (2 : ℕ)) : ℕ → ℝ) := sorry

end PolakRibierePolyak

section FletcherReeves

variable (f : Point → ℝ)
variable (r : ℕ)
variable (method : PeriodicRestartFRConjugateGradientMethod n r f)
variable (xStar : Point)

/-- Chapter04 Theorem 4.3.7 (2): let `method` be an F-R-CG restart run with restart period `r`,
let `xStar = x*` be the source point from the surrounding setup, and package the standing
hypotheses into
`h : PeriodicRestartFRConjugateGradientMethod.HasRestartRateAssumptions method xStar`:
the restart period satisfies
`r > 0`, every iterate stays in the bounded lower level set
`lowerLevelSetOn Set.univ f method.x0` carrying the `(A1)`/`(A2)` Hessian bounds, the iterate
sequence `method.x` converges to `xStar`, and `xStar` is stationary for `f`. Then the source
`n`-step quadratic estimate `(4.3.42)` is encoded canonically as a big-`O` statement for the
error vector, with right-hand side `dist (method.x (k r), x*)²`; this is equivalent to the
displayed source norm formula `‖method.x (k r + n) - x*‖ = O(‖method.x (k r) - x*‖²)`. -/
theorem fletcherReevesRestart_nStepQuadraticRate
    (h : PeriodicRestartFRConjugateGradientMethod.HasRestartRateAssumptions method xStar) :
    ((fun k : ℕ ↦ (method.x (k * r + n) : Point) - xStar) : ℕ → Point) =O[atTop]
      ((fun k : ℕ ↦ dist (method.x (k * r)) xStar ^ (2 : ℕ)) : ℕ → ℝ) := sorry

/-- Chapter04 Theorem 4.3.7 (4): under the same F-R restart hypotheses as in `(2)`, that restart
Fletcher-Reeves sequence also has the stronger source conclusion that for `xStar = x*`, Ritter's
`n`-step superquadratic estimate holds directly, encoded canonically as a little-`o` statement on
the error vector with right-hand side `dist (method.x k, x*)²`; this is equivalent to the source
norm formula `‖method.x (k + n) - x*‖ = o(‖method.x k - x*‖²)`. -/
theorem fletcherReevesRestart_nStepSuperquadratic
    (h : PeriodicRestartFRConjugateGradientMethod.HasRestartRateAssumptions method xStar) :
    ((fun k : ℕ ↦ (method.x (k + n) : Point) - xStar) : ℕ → Point) =o[atTop]
      ((fun k : ℕ ↦ dist (method.x k) xStar ^ (2 : ℕ)) : ℕ → ℝ) := sorry

end FletcherReeves

end
