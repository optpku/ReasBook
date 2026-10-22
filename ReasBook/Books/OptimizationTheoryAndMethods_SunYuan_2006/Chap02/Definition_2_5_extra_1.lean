/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import OptimizationTheoryAndMethods_SunYuan_2006.Chap02.Algorithm_2_5_2
import Mathlib.Order.Bounds.Basic

section

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

-- Source/core/bridge triage:
-- * source-facing: admissible Armijo parameters and the first accepted exponent `mk`
--   for the geometric trial steps `τ, β * τ, β ^ 2 * τ, ...`;
-- * core/canonical: `armijoBacktrackingAccepts`, `IsBacktrackingLineSearchStep`, and
--   `IsBacktrackingStepSequence`;
-- * bridge/view: `armijoAcceptsAtExponent` records the textbook exponent-indexed view
--   by evaluating the canonical Armijo predicate on the geometric backtracking steps.

/-- The admissible Armijo backtracking parameters satisfy `0 < β < 1`,
`0 < ρ < 1 / 2`, and `0 < τ`. -/
class ArmijoParameters (β ρ τ : ℝ) : Prop where
  beta_pos : 0 < β
  beta_lt_one : β < 1
  rho_pos : 0 < ρ
  rho_lt_half : ρ < (1 / 2 : ℝ)
  tau_pos : 0 < τ

/-- Armijo parameter data is proposition-valued, hence subsingleton. -/
instance armijoParametersSubsingleton (β ρ τ : ℝ) :
    Subsingleton (ArmijoParameters β ρ τ) := inferInstance

/-- Expanding `ArmijoParameters` gives the interval constraints on `β`, `ρ`, and `τ`. -/
theorem armijoParameters_iff {β ρ τ : ℝ} :
    ArmijoParameters β ρ τ ↔
      0 < β ∧ β < 1 ∧ 0 < ρ ∧ ρ < (1 / 2 : ℝ) ∧ 0 < τ := by
  constructor
  · intro h
    exact ⟨h.beta_pos, h.beta_lt_one, h.rho_pos, h.rho_lt_half, h.tau_pos⟩
  · rintro ⟨hβ_pos, hβ_lt_one, hρ_pos, hρ_lt_half, hτ_pos⟩
    exact ⟨hβ_pos, hβ_lt_one, hρ_pos, hρ_lt_half, hτ_pos⟩

namespace ArmijoParameters

/-- The geometric trial sequence `m ↦ β ^ m` attached to admissible Armijo parameters is a
canonical backtracking step sequence. -/
theorem geometricStepSequence {β ρ τ : ℝ} (h : ArmijoParameters β ρ τ) :
    IsBacktrackingStepSequence (fun m ↦ β ^ m) := by
  refine
    { start := by simp
      step_pos := fun n ↦ pow_pos h.beta_pos n
      strictReduction := ?_ }
  intro n
  have hpow : 0 < β ^ n := pow_pos h.beta_pos n
  simpa [pow_succ, mul_comm] using mul_lt_mul_of_pos_left h.beta_lt_one hpow

end ArmijoParameters

/-- The Armijo sufficient-decrease test at the backtracking exponent `m`, viewed through
the canonical Armijo acceptance predicate on the geometric step size `(β ^ m) * τ`. -/
def armijoAcceptsAtExponent
    (f : E → ℝ) (xk dk gk : E) (β ρ τ : ℝ) (m : ℕ) : Prop :=
  armijoBacktrackingAccepts f ρ xk gk (τ • dk) (β ^ m)

/-- `armijoAcceptsAtExponent` is the exponent-indexed view of
`armijoBacktrackingAccepts` on the scaled direction `τ • dk`. -/
theorem armijoAcceptsAtExponent_iff_armijoBacktrackingAccepts
    {f : E → ℝ} {xk dk gk : E} {β ρ τ : ℝ} {m : ℕ} :
    armijoAcceptsAtExponent f xk dk gk β ρ τ m ↔
      armijoBacktrackingAccepts f ρ xk gk (τ • dk) (β ^ m) :=
  Iff.rfl

/-- Unfolding `armijoAcceptsAtExponent` recovers the textbook Armijo sufficient-decrease
inequality at the geometric trial step `(β ^ m) * τ`. -/
theorem armijoAcceptsAtExponent_iff
    {f : E → ℝ} {xk dk gk : E} {β ρ τ : ℝ} {m : ℕ} :
    armijoAcceptsAtExponent f xk dk gk β ρ τ m ↔
      f xk - f (xk + ((β ^ m) * τ) • dk) ≥
        -(ρ * (β ^ m) * τ * inner ℝ gk dk) := by
  rw [armijoAcceptsAtExponent_iff_armijoBacktrackingAccepts, armijoBacktrackingAccepts_iff]
  constructor
  · intro h
    have h' :
        f (xk + ((β ^ m) * τ) • dk) ≤ f xk + ρ * (β ^ m) * τ * inner ℝ gk dk := by
      simpa [smul_smul, inner_smul_right, mul_assoc, mul_left_comm, mul_comm] using h
    linarith
  · intro h
    have h' :
        f (xk + ((β ^ m) * τ) • dk) ≤ f xk + ρ * (β ^ m) * τ * inner ℝ gk dk := by
      linarith
    simpa [smul_smul, inner_smul_right, mul_assoc, mul_left_comm, mul_comm] using h'

/-- Chapter02 Definition 2.5-extra-1: `mk` is an Armijo backtracking index when
`β ∈ (0, 1)`, `ρ ∈ (0, 1 / 2)`, and `τ > 0`, and the geometric trial sequence
`αm = β ^ m` on the scaled direction `τ • dk` satisfies the canonical backtracking
owner with first accepted index `mk`. Equivalently, the accepted step size is
`(β ^ mk) * τ`, and no earlier exponent satisfies the Armijo test. -/
class IsArmijoIndex
    (f : E → ℝ) (xk dk gk : E) (β ρ τ : ℝ) (mk : ℕ) : Prop extends
    ArmijoParameters β ρ τ,
    IsBacktrackingLineSearchStep
      (fun α _ ↦ armijoBacktrackingAccepts f ρ xk gk (τ • dk) α)
      xk (τ • dk) (fun m ↦ β ^ m) mk

/-- An Armijo index witness is proposition-valued, hence subsingleton. -/
instance isArmijoIndexSubsingleton
    (f : E → ℝ) (xk dk gk : E) (β ρ τ : ℝ) (mk : ℕ) :
    Subsingleton (IsArmijoIndex f xk dk gk β ρ τ mk) := inferInstance

/-- Expanding `IsArmijoIndex` gives the admissible Armijo parameters together with the
canonical backtracking-step owner for the Armijo acceptance predicate on the geometric
trial sequence. -/
theorem isArmijoIndex_iff
    {f : E → ℝ} {xk dk gk : E} {β ρ τ : ℝ} {mk : ℕ} :
    IsArmijoIndex f xk dk gk β ρ τ mk ↔
      ArmijoParameters β ρ τ ∧
        IsBacktrackingLineSearchStep
          (fun α _ ↦ armijoBacktrackingAccepts f ρ xk gk (τ • dk) α)
          xk (τ • dk) (fun m ↦ β ^ m) mk := by
  constructor
  · intro h
    exact ⟨h.toArmijoParameters, h.toIsBacktrackingLineSearchStep⟩
  · rintro ⟨hParameters, hStep⟩
    exact { toArmijoParameters := hParameters, toIsBacktrackingLineSearchStep := hStep }

namespace IsArmijoIndex

/-- The least Armijo backtracking index `mk` satisfies the Armijo sufficient-decrease test. -/
theorem accepts
    {f : E → ℝ} {xk dk gk : E} {β ρ τ : ℝ} {mk : ℕ}
    (h : IsArmijoIndex f xk dk gk β ρ τ mk) :
    armijoAcceptsAtExponent f xk dk gk β ρ τ mk := by
  simpa [armijoAcceptsAtExponent] using h.toIsBacktrackingLineSearchStep.accepts

/-- No earlier exponent than `mk` satisfies the Armijo sufficient-decrease test. -/
theorem not_accepts_of_lt
    {f : E → ℝ} {xk dk gk : E} {β ρ τ : ℝ} {mk m : ℕ}
    (h : IsArmijoIndex f xk dk gk β ρ τ mk) (hm : m < mk) :
    ¬ armijoAcceptsAtExponent f xk dk gk β ρ τ m := by
  intro hAccepts
  exact Nat.not_lt_of_ge
      (h.toIsBacktrackingLineSearchStep.le_of_accepts
        (by simpa [armijoAcceptsAtExponent] using hAccepts)) hm

/-- Any accepted Armijo exponent is at least the least Armijo index. -/
theorem le_of_accepts
    {f : E → ℝ} {xk dk gk : E} {β ρ τ : ℝ} {mk m : ℕ}
    (h : IsArmijoIndex f xk dk gk β ρ τ mk)
    (hm : armijoAcceptsAtExponent f xk dk gk β ρ τ m) :
    mk ≤ m :=
  h.toIsBacktrackingLineSearchStep.le_of_accepts (by simpa [armijoAcceptsAtExponent] using hm)

/-- The canonical backtracking owner attached to `h` yields the source-facing least-index
statement for the accepted Armijo exponents. -/
theorem isLeastAcceptedExponent
    {f : E → ℝ} {xk dk gk : E} {β ρ τ : ℝ} {mk : ℕ}
    (h : IsArmijoIndex f xk dk gk β ρ τ mk) :
    IsLeast {m : ℕ | armijoAcceptsAtExponent f xk dk gk β ρ τ m} mk := by
  simpa [armijoAcceptsAtExponent] using h.toIsBacktrackingLineSearchStep.isLeastAcceptedIndex

end IsArmijoIndex

/-- Source-facing expansion of `IsArmijoIndex`: the generic backtracking owner is equivalent
to saying that the Armijo parameter bounds hold and `mk` is the least accepted exponent. -/
theorem isArmijoIndex_iff_isLeastAcceptedExponent
    {f : E → ℝ} {xk dk gk : E} {β ρ τ : ℝ} {mk : ℕ} :
    IsArmijoIndex f xk dk gk β ρ τ mk ↔
      ArmijoParameters β ρ τ ∧
        IsLeast {m : ℕ | armijoAcceptsAtExponent f xk dk gk β ρ τ m} mk := by
  constructor
  · intro h
    exact ⟨h.toArmijoParameters, h.isLeastAcceptedExponent⟩
  · rintro ⟨hParameters, hLeast⟩
    refine
      { toArmijoParameters := hParameters
        toIsBacktrackingLineSearchStep := ?_ }
    refine (isBacktrackingLineSearchStep_iff _ _ _ _ _).2 ?_
    exact
      ⟨hParameters.geometricStepSequence, by simpa [armijoAcceptsAtExponent] using hLeast⟩

attribute [instance] IsArmijoIndex.toArmijoParameters
attribute [instance] IsArmijoIndex.toIsBacktrackingLineSearchStep

end
