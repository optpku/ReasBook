/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap07.Theorem_7_16

-- Declarations for this item will be appended below by the statement pipeline.

open scoped BigOperators

noncomputable section

universe u

section

variable {X : Type u}

/- Definition 7.74 lies in the chapter's finite-horizon geometric-mean-growth domain.

Mandatory domain-style sampling:
- `positiveIterateGeometricMean` in `Chap07/Theorem_7_16`, the chapter's sequence-level
  geometric-mean owner for positive outputs along an iterate trace.
- `positiveIterateGeometricMean_def` in `Chap07/Theorem_7_16`, the direct bridge back to the
  textbook `Real.rpow`-of-product formula.
- `staticProductionAverageEfficiency` in `Chap07/Definition_7_73`, the nearby static-strategy
  geometric-mean owner that remains relevant only as a comparison object in Theorem 7.17.

Best owner abstraction:
- source-facing: the average rate of growth of a dynamic strategy over the realized trace
  `x₀, ..., x_N`;
- core/canonical: `positiveIterateGeometricMean`, applied to the realized output sequence
  `i ↦ ψ_i(x_i)` and evaluated at the horizon `N`;
- bridge/view: the expansion theorem below, which recovers the textbook finite-horizon geometric
  mean formula.

Primitive data:
- the feasible subtype `P`;
- the horizon `N`;
- the stagewise positive outputs `ψ`;
- the realized adaptive trace `x`.

Derived API:
- the realized positive output sequence `i ↦ ψ_i(x_i)` continued beyond the horizon by the neutral
  value `1` only as internal bookkeeping for the sequence owner;
- the geometric-mean owner `positiveIterateGeometricMean` evaluated at the horizon `N`.

The previous version presented the dynamic growth notion through the auxiliary singleton encoding
needed to reuse the static owner. This file instead keeps the source-facing dynamic-growth name on
the direct sequence-level geometric-mean owner already used elsewhere in the chapter, and leaves
the raw product formula as the companion bridge theorem.
-/

/-- Definition 7.74: the average rate of growth of a dynamic strategy over the periods
`0, ..., N` is the geometric mean of the outputs `ψ_k(x_k)` along the adaptive strategy
trace. -/
def dynamicStrategyAverageRateOfGrowth
    {P : Set X} {N : ℕ}
    (ψ : Fin (N + 1) → P → {r : ℝ // 0 < r})
    (x : Fin (N + 1) → P) : ℝ :=
  positiveIterateGeometricMean
    (fun i : ℕ ↦ if h : i < N + 1 then ψ ⟨i, h⟩ (x ⟨i, h⟩) else ⟨1, by positivity⟩)
    id
    N

-- Proof sketch: unfold `dynamicStrategyAverageRateOfGrowth`.
/-- Expanding `dynamicStrategyAverageRateOfGrowth ψ x` gives the geometric mean
`[∏_{k=0}^N ψ_k(x_k)]^(1 / (N + 1))` of the outputs along the adaptive strategy trace. -/
theorem dynamicStrategyAverageRateOfGrowth_def
    {P : Set X} {N : ℕ}
    (ψ : Fin (N + 1) → P → {r : ℝ // 0 < r})
    (x : Fin (N + 1) → P) :
    dynamicStrategyAverageRateOfGrowth ψ x =
      Real.rpow
        (∏ k : Fin (N + 1), (ψ k (x k) : ℝ))
        ((1 : ℝ) / (N + 1 : ℝ)) := by
  rw [dynamicStrategyAverageRateOfGrowth, positiveIterateGeometricMean_def]
  congr 1
  trans ∏ i ∈ Finset.range (N + 1),
      if h : i < N + 1 then (ψ ⟨i, h⟩ (x ⟨i, h⟩) : ℝ) else 1
  · refine Finset.prod_congr rfl ?_
    intro i hi
    by_cases h : i < N + 1
    · simp [h]
    · simp [h]
  · rw [← Fin.prod_univ_eq_prod_range
      (fun i : ℕ ↦ if h : i < N + 1 then (ψ ⟨i, h⟩ (x ⟨i, h⟩) : ℝ) else 1)
      (N + 1)]
    refine Finset.prod_congr rfl ?_
    intro i hi
    simp [i.is_lt]

end
