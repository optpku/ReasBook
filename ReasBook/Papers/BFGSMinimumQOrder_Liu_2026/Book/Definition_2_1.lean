/-
Authors: Chenyi Li
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@5bf5af722d85bd5c98368c41c4066124a15e8fd3:ReasBook/Papers/BFGSMinimumQOrder_Liu_2026/README.md (formalization contributor).
-/

module

public import ReasLib.Analysis.Convergence.QOrder
public import Mathlib.Analysis.InnerProductSpace.PiL2

public section

universe u

open scoped Topology

variable {ι : Type u} [Fintype ι] [DecidableEq ι]

/- Definition 2.1 (1): Q-order at least `p` is the eventual uniform power estimate
for a convergent, eventually nonstationary sequence in Euclidean space. -/
#check (QConvergence.hasOrderAtLeast_iff :
  ∀ (x : ℕ → EuclideanSpace ℝ ι) (xStar : EuclideanSpace ℝ ι) (p : ℝ),
    QConvergence.HasOrderAtLeast x xStar p ↔
      Filter.Tendsto x Filter.atTop (𝓝 xStar) ∧
        (∀ᶠ k in Filter.atTop, x k ≠ xStar) ∧
          1 ≤ p ∧
            ∃ C > 0, ∀ᶠ k in Filter.atTop,
              QConvergence.error x xStar (k + 1) ≤
                C * QConvergence.error x xStar k ^ p)

/- Definition 2.1 (2): the Q-order power estimate is equivalent to finite
extended-nonnegative-real limsup of the adjacent error ratios. -/
#check (QConvergence.hasOrderAtLeast_iff_limsup_lt_top :
  ∀ (x : ℕ → EuclideanSpace ℝ ι) (xStar : EuclideanSpace ℝ ι) (p : ℝ),
    QConvergence.HasOrderAtLeast x xStar p ↔
      Filter.Tendsto x Filter.atTop (𝓝 xStar) ∧
        (∀ᶠ k in Filter.atTop, x k ≠ xStar) ∧
          1 ≤ p ∧
            Filter.limsup
                (fun k ↦ ENNReal.ofReal
                  (QConvergence.error x xStar (k + 1) /
                    QConvergence.error x xStar k ^ p))
                Filter.atTop < ⊤)

/- Definition 2.1 (3): the Q-order is the extended supremum of the admissible
real exponents whenever that set is nonempty. -/
#check (QConvergence.order_def :
  ∀ (x : ℕ → EuclideanSpace ℝ ι) (xStar : EuclideanSpace ℝ ι),
    QConvergence.order x xStar =
      sSup (ENNReal.ofReal '' QConvergence.admissibleExponents x xStar))

/- Definition 2.1 (4): Q-superlinear convergence is convergence with adjacent
error ratio tending to zero. -/
#check (QConvergence.isSuperlinear_iff_ratio :
  ∀ (x : ℕ → EuclideanSpace ℝ ι) (xStar : EuclideanSpace ℝ ι),
    QConvergence.IsSuperlinear x xStar ↔
      Filter.Tendsto x Filter.atTop (𝓝 xStar) ∧
        (∀ᶠ k in Filter.atTop, x k ≠ xStar) ∧
          Filter.Tendsto
            (fun k ↦ QConvergence.error x xStar (k + 1) /
              QConvergence.error x xStar k)
            Filter.atTop (𝓝 0))
