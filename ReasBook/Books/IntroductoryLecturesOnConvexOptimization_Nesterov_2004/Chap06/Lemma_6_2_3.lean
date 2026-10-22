/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap06.Theorem_6_4

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open scoped ConstrainedArgmin Gradient

universe u v

variable {E₁ : Type u} {E₂ : Type v}
  [NormedAddCommGroup E₁] [InnerProductSpace ℝ E₁] [CompleteSpace E₁]

-- Semantic recall: `upper_model_of_hasGradientWithinAt_lipschitzOn` in `Theorem_6_4` is the
-- nearby Chapter 6 owner for the missing smoothness premise, while later Chapter 6 files consume
-- this item through a direct ambient excessive-gap theorem rather than through a bundled
-- `ImplementablePrimalDualStructure`.
/-- Lemma 6.2.3: let `x₀ ∈ Q₁`, let `\bar x` minimize the linearized prox model
`x ↦ ⟪∇ f_{μ₂}(x₀), x - x₀⟫ + L₁(f_{μ₂}) d₁(x)`, and let
`\bar u := u_{μ₂}(x₀)`. This direct owner theorem records the hidden Chapter 6 ingredients
explicitly: `L₁(f_{μ₂})` is realized by the displayed prox upper model at `x₀`, `d₁` is
nonnegative on `Q₁`, and `\bar u` enters only through the bridge inequality coming from the
selected `μ₁`-primal point. Under these source-faithful hypotheses, every `μ₁ ≥ L₁(f_{μ₂})`
yields the excessive-gap inequality `f_{μ₂}(\bar x) ≤ φ_{μ₁}(\bar u)`. -/
theorem smoothed_pair_excessive_gap_of_linearized_prox_minimizers
    {Q₁ : Set E₁} {fμ₂ : E₁ → ℝ} {φμ₁ : E₂ → ℝ} {d₁ : E₁ → ℝ}
    {x₀ xBar xμ₁uBar : Q₁} {uBar : E₂} {μ₁ Lfμ₂ : ℝ}
    (hconv : ConvexOn ℝ Q₁ fμ₂)
    (hfμ₂_grad :
      HasGradientWithinAt
        fμ₂
        (gradientWithin fμ₂ Q₁ x₀)
        Q₁
        x₀)
    (hfμ₂_upper :
      ∀ ⦃x : E₁⦄, x ∈ Q₁ →
        fμ₂ x ≤
          fμ₂ x₀ +
            inner ℝ (gradientWithin fμ₂ Q₁ x₀) (x - x₀) +
              Lfμ₂ * d₁ x)
    (hbar_min :
      IsMinOn
        (fun x ↦
          inner ℝ (gradientWithin fμ₂ Q₁ x₀) (x - x₀) +
            Lfμ₂ * d₁ x)
        Q₁
        xBar)
    (hd₁_nonneg :
      ∀ ⦃x : E₁⦄, x ∈ Q₁ → 0 ≤ d₁ x)
    (horacle_bridge :
      fμ₂ x₀ +
          inner ℝ (gradientWithin fμ₂ Q₁ x₀) ((xμ₁uBar : E₁) - x₀) +
            μ₁ * d₁ xμ₁uBar ≤
        φμ₁ uBar)
    (hμ₁ : Lfμ₂ ≤ μ₁) :
    fμ₂ xBar ≤ φμ₁ uBar := by
  -- First place `xBar` under the explicit prox upper model available at `x₀`.
  have upperModelAtBar :
      fμ₂ xBar ≤
        fμ₂ x₀ +
          inner ℝ (gradientWithin fμ₂ Q₁ x₀) ((xBar : E₁) - x₀) +
            Lfμ₂ * d₁ xBar := by
    simpa using hfμ₂_upper xBar.property
  -- Then compare the minimizing linearized prox model at `xBar` with the oracle point.
  have linearizedModelAtBar_le_linearizedModelAtOraclePoint :
      inner ℝ (gradientWithin fμ₂ Q₁ x₀) ((xBar : E₁) - x₀) +
          Lfμ₂ * d₁ xBar ≤
        inner ℝ (gradientWithin fμ₂ Q₁ x₀) ((xμ₁uBar : E₁) - x₀) +
          Lfμ₂ * d₁ xμ₁uBar := by
    simpa using (isMinOn_iff.mp hbar_min) xμ₁uBar xμ₁uBar.property
  -- The prox term is monotone in its weight because `d₁` is nonnegative on `Q₁`.
  have proxWeightUpgradeAtOraclePoint :
      Lfμ₂ * d₁ xμ₁uBar ≤ μ₁ * d₁ xμ₁uBar := by
    exact mul_le_mul_of_nonneg_right hμ₁ (hd₁_nonneg xμ₁uBar.property)
  -- Transport the coefficient upgrade into the full oracle model and finish by transitivity.
  have oracleModelLePhi :
      fμ₂ x₀ +
          inner ℝ (gradientWithin fμ₂ Q₁ x₀) ((xμ₁uBar : E₁) - x₀) +
            Lfμ₂ * d₁ xμ₁uBar ≤
        φμ₁ uBar := by
    have hAffineUpgrade :=
      add_le_add_left
        proxWeightUpgradeAtOraclePoint
        (fμ₂ x₀ + inner ℝ (gradientWithin fμ₂ Q₁ x₀) ((xμ₁uBar : E₁) - x₀))
    exact le_trans (by simpa [add_assoc] using hAffineUpgrade) horacle_bridge
  calc
    fμ₂ xBar
        ≤ fμ₂ x₀ +
            inner ℝ (gradientWithin fμ₂ Q₁ x₀) ((xBar : E₁) - x₀) +
              Lfμ₂ * d₁ xBar := upperModelAtBar
    _ ≤ fμ₂ x₀ +
          inner ℝ (gradientWithin fμ₂ Q₁ x₀) ((xμ₁uBar : E₁) - x₀) +
            Lfμ₂ * d₁ xμ₁uBar := by
      simpa [add_assoc, add_left_comm, add_comm] using
        add_le_add_left linearizedModelAtBar_le_linearizedModelAtOraclePoint (fμ₂ x₀)
    _ ≤ φμ₁ uBar := oracleModelLePhi

end
