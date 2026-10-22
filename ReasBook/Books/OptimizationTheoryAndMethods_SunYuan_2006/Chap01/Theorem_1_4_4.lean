/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import OptimizationTheoryAndMethods_SunYuan_2006.Chap01.Definition_1_4_7

section Chapter01Theorem144

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

-- Domain sampling:
-- * primary domain: first-order calculus at local extrema on real inner-product spaces
-- * core/canonical owner abstractions inspected:
--   `IsLocalMin`, `IsLocalMinOn.isLocalMin`, `IsLocalMin.hasFDerivAt_eq_zero`,
--   `IsStationaryPoint`
-- * source-facing data: an open domain `D`, a local minimizer `xStar ∈ D`, and differentiability
--   at `xStar`
-- * derived API: the stationary-point conclusion and its zero-gradient corollary

/-- Canonical first-order Fermat bridge: a differentiable local minimizer is a stationary point. -/
theorem isStationaryPoint_of_isLocalMin
    (f : E → ℝ) (xStar : E)
    (hdiff : DifferentiableAt ℝ f xStar) (hmin : IsLocalMin f xStar) :
    IsStationaryPoint f xStar := by
  have hfderiv0 : fderiv ℝ f xStar = 0 :=
    hmin.hasFDerivAt_eq_zero hdiff.hasFDerivAt
  simpa [IsStationaryPoint, hasGradientAt_iff_hasFDerivAt, hfderiv0] using hdiff.hasFDerivAt

/-- Chapter01 Theorem 1.4.4 (First-Order Necessary Condition): if `xStar ∈ D` is a local
minimizer of `f` on the open set `D` and `f` is differentiable at `xStar`, then `xStar` is a
stationary point of `f`. This is the source-facing open-set bridge to
`isStationaryPoint_of_isLocalMin`. -/
theorem isStationaryPoint_of_isLocalMinOn
    (D : Set E) (f : E → ℝ) (xStar : E)
    (hD_open : IsOpen D) (hxStar : xStar ∈ D) (hdiff : DifferentiableAt ℝ f xStar)
    (hmin : IsLocalMinOn f D xStar) :
    IsStationaryPoint f xStar := by
  have hlocal : IsLocalMin f xStar := hmin.isLocalMin (hD_open.mem_nhds hxStar)
  exact isStationaryPoint_of_isLocalMin f xStar hdiff hlocal

/-- Derived zero-gradient form of Theorem 1.4.4: under the same differentiability hypothesis as
the source theorem, a local minimizer on an open set has vanishing gradient. -/
theorem gradient_eq_zero_of_isLocalMinOn
    (D : Set E) (f : E → ℝ) (xStar : E)
    (hD_open : IsOpen D) (hxStar : xStar ∈ D) (hdiff : DifferentiableAt ℝ f xStar)
    (hmin : IsLocalMinOn f D xStar) :
    gradient f xStar = 0 := by
  exact (isStationaryPoint_of_isLocalMinOn D f xStar hD_open hxStar hdiff hmin).gradient_eq_zero

end Chapter01Theorem144
