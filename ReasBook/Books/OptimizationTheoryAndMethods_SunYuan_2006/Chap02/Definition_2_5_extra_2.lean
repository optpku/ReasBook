/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import OptimizationTheoryAndMethods_SunYuan_2006.Chap02.Algorithm_2_5_1

-- Chapter 2 already records the core Goldstein inequalities as
-- `goldsteinCondition φ φPrime0 ρ α` using the stored slope datum `φPrime0`.
-- This file keeps the source-facing parameter and positive-steplength layer
-- around that core owner for the profile/slope-datum formulation.

section

/-- Chapter02 Definition 2.5-extra-2 (1): a positive steplength `α` satisfies the
Goldstein inexact line-search rule for the one-dimensional profile `φ` with stored
slope datum `φPrime0` when `0 < ρ < 1 / 2`, `0 < α`, and both Goldstein inequalities hold:
`φ α ≤ φ 0 + ρ * α * φPrime0` and `φ 0 + (1 - ρ) * α * φPrime0 ≤ φ α`. -/
class GoldsteinCondition (φ : ℝ → ℝ) (φPrime0 ρ α : ℝ) : Prop where
  parameters : GoldsteinParameters ρ
  step_pos : 0 < α
  core : goldsteinCondition φ φPrime0 ρ α

/-- Any Goldstein-condition witness carries the admissible-parameter data. -/
theorem goldsteinCondition_parameters {φ : ℝ → ℝ} {φPrime0 ρ α : ℝ}
    (h : GoldsteinCondition φ φPrime0 ρ α) :
    GoldsteinParameters ρ :=
  h.parameters

/-- Any Goldstein-condition witness carries the positivity of the steplength. -/
theorem goldsteinCondition_step_pos {φ : ℝ → ℝ} {φPrime0 ρ α : ℝ}
    (h : GoldsteinCondition φ φPrime0 ρ α) :
    0 < α :=
  h.step_pos

/-- Any Goldstein-condition witness yields the core Goldstein inequalities evaluated at the
slope datum `φPrime0`. -/
theorem goldsteinCondition_core {φ : ℝ → ℝ} {φPrime0 ρ α : ℝ}
    (h : GoldsteinCondition φ φPrime0 ρ α) :
    goldsteinCondition φ φPrime0 ρ α :=
  h.core

/-- Expanding `GoldsteinCondition` gives the admissible parameter bounds,
positivity of the steplength, and the two Goldstein inequalities. -/
theorem goldsteinCondition_iff {φ : ℝ → ℝ} {φPrime0 ρ α : ℝ} :
    GoldsteinCondition φ φPrime0 ρ α ↔
      GoldsteinParameters ρ ∧
        0 < α ∧
        φ α ≤ φ 0 + ρ * α * φPrime0 ∧
        φ 0 + (1 - ρ) * α * φPrime0 ≤ φ α := by
  constructor
  · intro h
    exact ⟨h.parameters, h.step_pos, h.core.1, h.core.2⟩
  · rintro ⟨hParameters, hα, hUpper, hLower⟩
    exact ⟨hParameters, hα, ⟨hUpper, hLower⟩⟩

/-- Chapter02 Definition 2.5-extra-2 (2): the acceptable interval for the Goldstein
rule consists of exactly the steplengths satisfying `GoldsteinCondition`. -/
def goldsteinAcceptableInterval (φ : ℝ → ℝ) (φPrime0 ρ : ℝ) : Set ℝ :=
  { α | GoldsteinCondition φ φPrime0 ρ α }

/-- Membership in `goldsteinAcceptableInterval` is exactly the Goldstein rule. -/
theorem mem_goldsteinAcceptableInterval {φ : ℝ → ℝ} {φPrime0 ρ α : ℝ} :
    α ∈ goldsteinAcceptableInterval φ φPrime0 ρ ↔ GoldsteinCondition φ φPrime0 ρ α :=
  Iff.rfl

end
