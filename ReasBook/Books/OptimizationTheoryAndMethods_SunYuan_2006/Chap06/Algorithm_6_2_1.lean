/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import Mathlib
import Mathlib.Analysis.Calculus.Deriv.Basic

-- Domain sampling:
-- * primary domain: one-dimensional smooth optimization;
-- * inspected canonical calculus owners: `HasDerivAt`, `HasDerivAt.deriv`, and `deriv`;
-- * owner choice: the source-facing owner remains the algorithm structure, while objective and
--   derivative samples are derived from `f` and `deriv f` rather than stored as primitive data.

noncomputable section

/-- The radicand in the one-dimensional conic-model formula for `ρ_k`. -/
def conicModelRhoRadicand (fk fkNext fDerivk fDerivNext sk : ℝ) : ℝ :=
  (fk - fkNext) ^ 2 - (fDerivk * sk) * (fDerivNext * sk)

/-- The one-dimensional conic-model quantity `ρ_k`. -/
def conicModelRho (fk fkNext fDerivk fDerivNext sk : ℝ) : ℝ :=
  Real.sqrt (conicModelRhoRadicand fk fkNext fDerivk fDerivNext sk)

/-- The denominator in the one-dimensional conic-model formula for `γ_k`. -/
def conicModelGammaDenominator (fk fkNext rho : ℝ) : ℝ :=
  fk - fkNext + rho

/-- The one-dimensional conic-model quantity `γ_k`. -/
def conicModelGamma (fk fkNext fDerivk sk rho : ℝ) : ℝ :=
  -(fDerivk * sk) / conicModelGammaDenominator fk fkNext rho

/-- The denominator in the one-dimensional conic-model update for `s_(k + 1)`. -/
def conicModelStepDenominator (gamma fDerivk fDerivNext : ℝ) : ℝ :=
  (1 / gamma ^ 3) * (fDerivk / fDerivNext) - 1

/-- The one-dimensional conic-model update for the next step `s_(k + 1)`. -/
def conicModelNextStep (sk gamma fDerivk fDerivNext : ℝ) : ℝ :=
  sk / conicModelStepDenominator gamma fDerivk fDerivNext

/-- Chapter06 Algorithm 6.2.1: a one-dimensional conic-model algorithm for an
objective `f : ℝ → ℝ` consists of initial data `x1`, `s1` and sequences `x`, `s`,
`rho`, and `gamma` indexed by `ℕ`, where the book's index `k = 1, 2, ...` is
represented literally. The sampled objective values are `f (x k)`, and the sampled
derivative values are the canonical derivatives `deriv f (x k)`, with explicit
`HasDerivAt` hypotheses at the iterate points `x k` for `k ≥ 1`. Step `0` gives
`x 1 = x1` and `s 1 = s1`; Step `k.1` gives `x (k + 1) = x k + s k`; Step `k.3`
gives the formulas for `rho k` and `gamma k`; and Step `k.4` gives the formula for
`s (k + 1)`, together with the explicit side conditions making the displayed square
root and divisions mathematically well-defined for `k ≥ 1`. -/
structure ConicModelOneDimensionalAlgorithm (f : ℝ → ℝ) where
  x1 : ℝ
  s1 : ℝ
  x : ℕ → ℝ
  s : ℕ → ℝ
  rho : ℕ → ℝ
  gamma : ℕ → ℝ
  x_one : x 1 = x1
  s_one : s 1 = s1
  hasDerivAt : ∀ ⦃k : ℕ⦄, 1 ≤ k → HasDerivAt f (deriv f (x k)) (x k)
  iterate_update : ∀ ⦃k : ℕ⦄, 1 ≤ k → x (k + 1) = x k + s k
  rhoRadicand_nonneg :
    ∀ ⦃k : ℕ⦄, 1 ≤ k →
      0 ≤
        conicModelRhoRadicand
          (f (x k))
          (f (x (k + 1)))
          (deriv f (x k))
          (deriv f (x (k + 1)))
          (s k)
  rho_update :
    ∀ ⦃k : ℕ⦄, 1 ≤ k →
      rho k =
        conicModelRho
          (f (x k))
          (f (x (k + 1)))
          (deriv f (x k))
          (deriv f (x (k + 1)))
          (s k)
  gammaDenominator_ne_zero :
    ∀ ⦃k : ℕ⦄, 1 ≤ k →
      conicModelGammaDenominator (f (x k)) (f (x (k + 1))) (rho k) ≠ 0
  gamma_update :
    ∀ ⦃k : ℕ⦄, 1 ≤ k →
      gamma k =
        conicModelGamma
          (f (x k))
          (f (x (k + 1)))
          (deriv f (x k))
          (s k)
          (rho k)
  gamma_ne_zero : ∀ ⦃k : ℕ⦄, 1 ≤ k → gamma k ≠ 0
  nextDeriv_ne_zero : ∀ ⦃k : ℕ⦄, 1 ≤ k → deriv f (x (k + 1)) ≠ 0
  stepDenominator_ne_zero :
    ∀ ⦃k : ℕ⦄, 1 ≤ k →
      conicModelStepDenominator (gamma k) (deriv f (x k)) (deriv f (x (k + 1))) ≠ 0
  step_update :
    ∀ ⦃k : ℕ⦄, 1 ≤ k →
      s (k + 1) =
        conicModelNextStep (s k) (gamma k) (deriv f (x k)) (deriv f (x (k + 1)))

/-- A one-dimensional conic-model algorithm can be used as its iterate sequence `x`. -/
instance {f : ℝ → ℝ} :
    CoeFun (ConicModelOneDimensionalAlgorithm f) (fun _ ↦ ℕ → ℝ) where
  coe A := A.x
