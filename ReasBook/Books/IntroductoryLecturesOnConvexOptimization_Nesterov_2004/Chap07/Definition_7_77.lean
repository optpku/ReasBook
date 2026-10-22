/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat

-- Declarations for this item will be appended below by the statement pipeline.

open scoped BigOperators
open Matrix

noncomputable section

variable {n N : ℕ}

/- Definition 7.77 lies in the finite-horizon simplex-portfolio / dynamic-growth domain.

Mandatory domain-style sampling before refinement:
- `constantShareObjective` and `optimalAverageGrowthRate` in `Chap07/Definition_7_75`, the nearby
  chapter owners showing that portfolio growth is best organized as cumulative return first and
  average growth second;
- `positiveIterateGeometricMean` in `Chap07/Theorem_7_16`, the sequence-level geometric-mean
  owner used elsewhere in the chapter when outputs are strictly positive real numbers;
- `dynamicStrategyAverageRateOfGrowth` in `Chap07/Definition_7_74`, the finite-horizon dynamic
  geometric-mean owner on a realized trace of strictly positive outputs;
- mathlib `stdSimplex`, the canonical owner for simplex-valued portfolio weights.

Best owner abstraction:
- source-facing: the cumulative return of an iterated portfolio together with the derived average
  growth rate over the finite horizon `0, ..., N`;
- core/canonical: `stdSimplex NNReal (Fin n)` and the finite product of period returns;
- bridge/view: the expansion theorems below and the constant-share specialization to
  the constant-share product formula already used elsewhere in Chapter 7.

Primitive data:
- the price-relative sequence `c`;
- the iterated portfolio trace `x`.

Derived API:
- the cumulative return `∏ k, ⟪c_k, x_k⟫`;
- the average growth rate as the `(N + 1)`-st geometric mean of that cumulative return;
- the constant-trace specialization back to the same finite product formula.

Source/core/bridge triage:
- source-facing: `iteratedPortfolioCumulativeReturn` and `iteratedPortfolioAverageGrowthRate`;
- core/canonical: `stdSimplex NNReal (Fin n)` and `Finset.prod`;
- bridge/view: the definitional expansion lemmas.

Unlike `Definition_7_74`, this file cannot reuse `positiveIterateGeometricMean` directly: the
portfolio returns live in `NNReal` and may be zero, whereas that owner is designed for strictly
positive real outputs. The refinement therefore stays source-faithful but follows the Chapter 7
owner pattern from `Definition_7_75`: cumulative return is primitive, and average growth is a
derived owner. -/

/-- The cumulative return of an iterated portfolio over the periods `0, ..., N`. -/
def iteratedPortfolioCumulativeReturn
    {P : Set (stdSimplex NNReal (Fin n))}
    (c : Fin (N + 1) → Fin n → NNReal)
    (x : Fin (N + 1) → P) : NNReal :=
  ∏ k : Fin (N + 1), c k ⬝ᵥ (x k : Fin n → NNReal)

/-- Expanding `iteratedPortfolioCumulativeReturn c x` gives the period-by-period product of
returns `∏_{k=0}^N ⟪c_k, x_k⟫`. -/
@[simp] theorem iteratedPortfolioCumulativeReturn_def
    {P : Set (stdSimplex NNReal (Fin n))}
    (c : Fin (N + 1) → Fin n → NNReal)
    (x : Fin (N + 1) → P) :
    iteratedPortfolioCumulativeReturn c x =
      ∏ k : Fin (N + 1), c k ⬝ᵥ (x k : Fin n → NNReal) :=
  rfl

/-- Definition 7.77: the average growth rate of an iterated portfolio over the periods
`0, ..., N` is the geometric mean of the period returns `⟪c_k, x_k⟫`. -/
def iteratedPortfolioAverageGrowthRate
    {P : Set (stdSimplex NNReal (Fin n))}
    (c : Fin (N + 1) → Fin n → NNReal)
    (x : Fin (N + 1) → P) : NNReal :=
  iteratedPortfolioCumulativeReturn c x ^ ((1 : ℝ) / (N + 1))

/-- Expanding `iteratedPortfolioAverageGrowthRate c x` gives the geometric mean
`[∏_{k=0}^N ⟪c_k, x_k⟫]^(1 / (N + 1))` of the period-by-period portfolio returns. -/
@[simp] theorem iteratedPortfolioAverageGrowthRate_eq_rpow_cumulativeReturn
    {P : Set (stdSimplex NNReal (Fin n))}
    (c : Fin (N + 1) → Fin n → NNReal)
    (x : Fin (N + 1) → P) :
    iteratedPortfolioAverageGrowthRate c x =
      iteratedPortfolioCumulativeReturn c x ^ ((1 : ℝ) / (N + 1)) :=
  rfl

theorem iteratedPortfolioAverageGrowthRate_def
    {P : Set (stdSimplex NNReal (Fin n))}
    (c : Fin (N + 1) → Fin n → NNReal)
    (x : Fin (N + 1) → P) :
    iteratedPortfolioAverageGrowthRate c x =
      (∏ k : Fin (N + 1), c k ⬝ᵥ (x k : Fin n → NNReal)) ^ ((1 : ℝ) / (N + 1)) := by
  rw [iteratedPortfolioAverageGrowthRate_eq_rpow_cumulativeReturn,
    iteratedPortfolioCumulativeReturn_def]
