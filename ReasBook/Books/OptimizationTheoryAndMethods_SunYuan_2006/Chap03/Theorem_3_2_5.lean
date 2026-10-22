/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import OptimizationTheoryAndMethods_SunYuan_2006.Chap01.Theorem_1_3_19
import OptimizationTheoryAndMethods_SunYuan_2006.Chap03.Algorithm_3_2_3
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Order.Filter.Extr

noncomputable section

open Filter
open scoped Gradient
open scoped RealInnerProductSpace
open scoped Topology

section NewtonMethod

variable {n : ℕ}

local notation "Point" => EuclideanSpace ℝ (Fin n)

-- Domain sampling:
-- * source-facing owner: `NewtonMethodWithLineSearch` from `Algorithm_3_2_3`
-- * source-facing lower-level-set Hessian hypothesis:
--   `HasLowerLevelHessianLowerBound D f A.x0 m` from `Theorem_1_3_19`
-- * core/canonical convex-analysis owners for the uniqueness conclusion:
--   `StrongConvexOn` / `StrictConvexOn`
-- * bridge already available upstream: Chapter 1 relates Hessian lower bounds on convex sets to
--   those canonical convexity owners.
-- * Chapter 2 already owns exact line search itself, so this file keeps only the additional
--   source decrease inequality `(3.2.13)` as a theorem hypothesis instead of a parallel run API.

variable {f : Point → ℝ} {D : Set Point} (A : NewtonMethodWithLineSearch n f)

/-- Chapter03 Theorem 3.2.5 (1): for a run `A` of Algorithm 3.2.3, if the Hessian lower bound
holds on the lower level set determined by the actual initial point `A.x0` and the source
line-search decrease inequality `(3.2.13)` holds along the run, then the gradient norms along
the Newton iterates tend to `0`. -/
theorem newtonSequence_gradient_tendsto_zero
    (hD_open : IsOpen D)
    (hD_convex : Convex ℝ D)
    (hC2 : ContDiffOn ℝ 2 f D)
    (hLevelHessian : ∃ m > 0, HasLowerLevelHessianLowerBound D f A.x0 m)
    (hIterates : ∀ k : ℕ, A k ∈ D)
    (hLineSearch :
      ∃ ηbar > 0, ∀ k : ℕ,
        ηbar * (((-(⟪A.d k, A.g k⟫)) / ‖A.d k‖) ^ (2 : ℕ)) ≤
          f (A k) - f (A (k + 1))) :
    Tendsto (fun k : ℕ ↦ ‖∇ f (A k)‖) atTop (nhds (0 : ℝ)) := sorry

/-- Chapter03 Theorem 3.2.5 (2): under the same hypotheses on the run `A`, the Newton iterates
converge to a minimizer of `f` on `D`. -/
theorem newtonSequence_tendsto_minimizer
    (hD_open : IsOpen D)
    (hD_convex : Convex ℝ D)
    (hC2 : ContDiffOn ℝ 2 f D)
    (hLevelHessian : ∃ m > 0, HasLowerLevelHessianLowerBound D f A.x0 m)
    (hIterates : ∀ k : ℕ, A k ∈ D)
    (hLineSearch :
      ∃ ηbar > 0, ∀ k : ℕ,
        ηbar * (((-(⟪A.d k, A.g k⟫)) / ‖A.d k‖) ^ (2 : ℕ)) ≤
          f (A k) - f (A (k + 1))) :
    ∃ xStar : Point, Tendsto A atTop (nhds xStar) ∧ IsMinOn f D xStar := sorry

/-- Chapter03 Theorem 3.2.5 (3): once the lower-level-set Hessian bound is fixed at an initial
point `x0 ∈ D`, uniqueness of minimizers on `D` is an objective-level consequence of the
convexity and regularity hypotheses, and no longer depends on the Newton run data. -/
theorem newtonSequence_minimizer_unique
    (x0 : Point)
    (hx0 : x0 ∈ D)
    (hD_open : IsOpen D)
    (hD_convex : Convex ℝ D)
    (hC2 : ContDiffOn ℝ 2 f D)
    (hLevelHessian : ∃ m > 0, HasLowerLevelHessianLowerBound D f x0 m)
    (y z : Point) (hy : IsMinOn f D y) (hz : IsMinOn f D z) :
    y = z := sorry

end NewtonMethod
