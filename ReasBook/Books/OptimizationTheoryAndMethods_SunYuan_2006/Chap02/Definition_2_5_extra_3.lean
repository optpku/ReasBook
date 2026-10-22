/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import Mathlib.Data.Real.Basic

-- Semantic recall: `lean_leansearch` did not surface a dedicated mathlib owner for
-- Wolfe-Powell line-search rules, so this item records the weak and strong
-- one-dimensional acceptance predicates directly.

section

/-- The admissible Wolfe-Powell parameters satisfy `0 < ρ < σ < 1`. -/
class WolfePowellParameters (ρ σ : ℝ) : Prop where
  rho_pos : 0 < ρ
  rho_lt_sigma : ρ < σ
  sigma_lt_one : σ < 1

/-- Expanding `WolfePowellParameters` gives the chain `0 < ρ < σ < 1`. -/
theorem wolfePowellParameters_iff {ρ σ : ℝ} :
    WolfePowellParameters ρ σ ↔ 0 < ρ ∧ ρ < σ ∧ σ < 1 := by
  constructor
  · intro h
    -- Read the parameter class back as the three scalar inequalities it stores.
    exact ⟨h.rho_pos, h.rho_lt_sigma, h.sigma_lt_one⟩
  · rintro ⟨hρ, hρσ, hσ⟩
    -- Repackage the explicit inequalities into the Wolfe-Powell parameter class.
    exact ⟨hρ, hρσ, hσ⟩

/-- Helper for Chapter02 Definition 2.5-extra-3: the Wolfe-Powell rule for a
one-dimensional line-search model requires a positive steplength together with
sufficient decrease and the curvature inequality `σ * φ' 0 ≤ φ' α`. -/
class WolfePowellCondition (φ φ' : ℝ → ℝ) (ρ σ α : ℝ) : Prop where
  parameters : WolfePowellParameters ρ σ
  step_pos : 0 < α
  sufficientDecrease : φ α ≤ φ 0 + ρ * α * φ' 0
  curvature : σ * φ' 0 ≤ φ' α

/-- Expanding `WolfePowellCondition` gives the positive-step, sufficient-decrease,
and curvature inequalities. -/
theorem wolfePowellCondition_iff {φ φ' : ℝ → ℝ} {ρ σ α : ℝ} :
    WolfePowellCondition φ φ' ρ σ α ↔
      WolfePowellParameters ρ σ ∧
        0 < α ∧
        φ α ≤ φ 0 + ρ * α * φ' 0 ∧
        σ * φ' 0 ≤ φ' α := by
  constructor
  · intro h
    -- Expand the class fields into the conjunction used by later companion lemmas.
    exact ⟨h.parameters, h.step_pos, h.sufficientDecrease, h.curvature⟩
  · rintro ⟨hparams, hα, hdec, hcurv⟩
    -- Assemble the Wolfe-Powell structure from the explicit line-search inequalities.
    exact ⟨hparams, hα, hdec, hcurv⟩

/-- Helper for Chapter02 Definition 2.5-extra-3: the strong Wolfe-Powell rule for a
one-dimensional line-search model requires a positive steplength together with
the Armijo condition and `|φ' α| ≤ -σ * φ' 0`. -/
class StrongWolfeCondition (φ φ' : ℝ → ℝ) (ρ σ α : ℝ) : Prop where
  parameters : WolfePowellParameters ρ σ
  step_pos : 0 < α
  sufficientDecrease : φ α ≤ φ 0 + ρ * α * φ' 0
  strongCurvature : |φ' α| ≤ -σ * φ' 0

/-- Expanding `StrongWolfeCondition` gives the positive-step, sufficient-decrease, and
strong-curvature inequalities. -/
theorem strongWolfeCondition_iff {φ φ' : ℝ → ℝ} {ρ σ α : ℝ} :
    StrongWolfeCondition φ φ' ρ σ α ↔
      WolfePowellParameters ρ σ ∧
        0 < α ∧
        φ α ≤ φ 0 + ρ * α * φ' 0 ∧
        |φ' α| ≤ -σ * φ' 0 := by
  constructor
  · intro h
    -- Expand the strong Wolfe condition into its parameter, step, decrease, and slope bounds.
    exact ⟨h.parameters, h.step_pos, h.sufficientDecrease, h.strongCurvature⟩
  · rintro ⟨hparams, hα, hdec, hcurv⟩
    -- Rebuild the class once the four defining inequalities are available explicitly.
    exact ⟨hparams, hα, hdec, hcurv⟩

/-- Chapter02 Definition 2.5-extra-3: when the initial slope is nonpositive, the
strong Wolfe-Powell inequality is equivalently written as
`|φ' α| ≤ σ * |φ' 0|`. -/
theorem strongWolfeCondition_iff_abs
    {φ φ' : ℝ → ℝ} {ρ σ α : ℝ} (h_nonpos : φ' 0 ≤ 0) :
    StrongWolfeCondition φ φ' ρ σ α ↔
      WolfePowellParameters ρ σ ∧
        0 < α ∧
        φ α ≤ φ 0 + ρ * α * φ' 0 ∧
        |φ' α| ≤ σ * |φ' 0| := by
  constructor
  · intro h
    -- First reduce to the standard strong-Wolfe expansion with `-σ * φ' 0` on the right.
    rcases strongWolfeCondition_iff.mp h with ⟨hparams, hα, hdec, hcurv⟩
    refine ⟨hparams, hα, hdec, ?_⟩
    -- Then rewrite the initial slope norm using `φ' 0 ≤ 0`.
    simpa [abs_of_nonpos h_nonpos, mul_neg, neg_mul] using hcurv
  · rintro ⟨hparams, hα, hdec, hcurv⟩
    -- Rewrite the absolute-value bound back to the `-σ * φ' 0` form expected by the class.
    refine strongWolfeCondition_iff.mpr ?_
    refine ⟨hparams, hα, hdec, ?_⟩
    simpa [abs_of_nonpos h_nonpos, mul_neg, neg_mul] using hcurv

end
