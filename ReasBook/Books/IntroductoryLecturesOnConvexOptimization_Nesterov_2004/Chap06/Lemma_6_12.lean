/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

-- Proof sketch: the inequalities `φ uBar ≤ fμ₂ xBar ≤ f xBar` give the lower bound
-- `0 ≤ f xBar - φ uBar`. The local estimate for `fμ₂` at `xBar` bounds the smoothing defect
-- `f xBar - fμ₂ xBar` by `μ₂ * D₂`; adding the assumed residual smoothed gap bound
-- `fμ₂ xBar - φ uBar ≤ r` gives the upper bound
-- `f xBar - φ uBar ≤ μ₂ * D₂ + r`.
/-- Lemma 6.12: if `fμ₂` satisfies the local lower smoothing bound
`f xBar - μ₂ D₂ ≤ fμ₂ xBar`, if
`φ uBar ≤ fμ₂ xBar ≤ f xBar`, and if the residual smoothed gap `fμ₂ xBar - φ uBar` is bounded
above by `r`, then the raw primal-dual gap at `(xBar, uBar)` lies in the interval
`[0, μ₂ D₂ + r]`. -/
theorem primal_dual_gap_bound_of_smoothed_lower_approximation
    {Q₁ : Type u} {Q₂ : Type v}
    {f fμ₂ : Q₁ → ℝ} {φ : Q₂ → ℝ} {μ₂ D₂ r : ℝ}
    {xBar : Q₁} {uBar : Q₂}
    (happrox : f xBar - μ₂ * D₂ ≤ fμ₂ xBar)
    (hφ_le : φ uBar ≤ fμ₂ xBar) (hresidual : fμ₂ xBar - φ uBar ≤ r)
    (hsmoothed_le : fμ₂ xBar ≤ f xBar) :
    f xBar - φ uBar ∈ Set.Icc 0 (μ₂ * D₂ + r) := by
  have hsmoothing_defect : f xBar - fμ₂ xBar ≤ μ₂ * D₂ := by
    linarith
  refine Set.mem_Icc.mpr ⟨sub_nonneg.mpr (le_trans hφ_le hsmoothed_le), ?_⟩
  linarith
