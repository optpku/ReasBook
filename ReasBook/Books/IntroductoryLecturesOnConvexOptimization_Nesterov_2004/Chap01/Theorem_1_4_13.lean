/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Calculus.LocalExtr.Basic

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Gradient

noncomputable section

universe u

/-
Theorem 1.4.13 lies in first-order differential calculus and stationarity for local minimizers.

Relevant owner-style declarations sampled before refining:
* `HasGradientAt`, the chapter's owner predicate for stationarity
* `DifferentiableAt.hasGradientAt`, which supplies the canonical gradient witness
* `gradient_eq_zero_of_not_differentiableAt`, which totalizes the gradient off the differentiable
  locus
* `IsLocalMin.fderiv_eq_zero`, mathlib's Fermat theorem for local minima

Best owner abstraction:
* `HasGradientAt f 0 xStar`

Primitive data:
* the function `f`
* the point `xStar`
* local or global minimality at `xStar`

Derived API:
* the stationary-point equality for local and global minimizers
* the global-minimizer specialization below
* the differentiable `HasGradientAt` bridge theorems below

Source/core/bridge triage:
* source-facing: Theorem 1.4.13's stationary-point conclusion
* core/canonical: `HasGradientAt f 0 xStar`
* bridge/view: the thin differentiable `HasGradientAt` companion deduced from
  `IsLocalMin.fderiv_eq_zero` and `DifferentiableAt.hasGradientAt`

The source statement is about `f : ℝⁿ → ℝ`, but the mathematical content uses only the ambient
real inner-product-space structure needed for the canonical gradient owner. The refined file keeps
the same semantics while dropping the unnecessary concrete `EuclideanSpace ℝ (Fin n)` model layer.
-/

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

-- Proof sketch: if `f` is differentiable at `xStar`, apply Fermat's theorem
-- `IsLocalMin.fderiv_eq_zero` and recover the gradient from `hf.hasGradientAt`; otherwise the
-- totalized gradient already vanishes by `gradient_eq_zero_of_not_differentiableAt`.
/-- Theorem 1.4.13: a local minimizer of a real-valued function on a real inner-product space has
vanishing totalized gradient. -/
theorem isLocalMin_gradient_eq_zero
    {f : E → ℝ} {xStar : E} (hmin : IsLocalMin f xStar) :
    ∇ f xStar = 0 := by
  by_cases hf : DifferentiableAt ℝ f xStar
  · have hstationary : HasGradientAt f 0 xStar := by
      rw [hasGradientAt_iff_hasFDerivAt]
      simpa [IsLocalMin.fderiv_eq_zero hmin] using hf.hasFDerivAt
    exact hstationary.gradient
  · simpa using gradient_eq_zero_of_not_differentiableAt hf

/-- Companion bridge: a differentiable local minimizer carries the canonical zero-gradient owner
`HasGradientAt f 0 xStar`. -/
theorem isLocalMin_hasGradientAt_zero_of_differentiableAt
    {f : E → ℝ} {xStar : E} (hmin : IsLocalMin f xStar) (hf : DifferentiableAt ℝ f xStar) :
    HasGradientAt f 0 xStar := by
  convert hf.hasGradientAt using 1
  exact (isLocalMin_gradient_eq_zero hmin).symm

-- Proof sketch: convert `IsMinOn f Set.univ xStar` to a local minimum using
-- `IsMinOn.isLocalMin`, then invoke Theorem 1.4.13 at the minimizer.
/-- A global minimizer on `Set.univ` has vanishing totalized gradient. -/
theorem isMinOn_gradient_eq_zero
    {f : E → ℝ} {xStar : E} (hmin : IsMinOn f Set.univ xStar) :
    ∇ f xStar = 0 := by
  exact isLocalMin_gradient_eq_zero (hmin.isLocalMin (by simp))

/-- Companion bridge: a global minimizer on `Set.univ` carries the canonical stationary witness as
soon as `f` is differentiable at that minimizer. -/
theorem isMinOn_hasGradientAt_zero_of_differentiableAt
    {f : E → ℝ} {xStar : E} (hf : DifferentiableAt ℝ f xStar)
    (hmin : IsMinOn f Set.univ xStar) :
    HasGradientAt f 0 xStar := by
  convert hf.hasGradientAt using 1
  exact (isMinOn_gradient_eq_zero hmin).symm

end
