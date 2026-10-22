/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import OptimizationTheoryAndMethods_SunYuan_2006.Chap10.Definition_10_6_extra_1
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.InnerProductSpace.Adjoint

noncomputable section

section

variable {n m : ℕ}

local notation "Point" => EuclideanSpace ℝ (Fin n)
local notation "ConstraintPoint" => EuclideanSpace ℝ (Fin m)

-- Domain sampling:
-- * `StandardPenaltyProblem.nonsmoothExactPenalty` in `Definition_10_6_extra_1` is the
--   canonical Chapter 10 exact-penalty owner.
-- * `subgradientNormSet` is the source-facing owner for the maximal Euclidean norm bound on
--   `∂ h 0`, expressed directly by the Euclidean affine-support inequality
--   `h y ≥ h 0 + ⟪v, y⟫` for all `y`.
-- * `ContinuousLinearMap.adjoint` is the canonical calculus owner for the transposed derivative
--   term appearing in the source subgradient representation.
-- This file therefore keeps only the source stationarity/norm-obstruction layer, reuses the
-- chapter's exact-penalty owner directly, and records the subgradient condition in its Euclidean
-- affine-support form.

/-- The set of norms of Euclidean subgradients `v` whose Riesz dual lies in the canonical
subdifferential `∂ h 0`. -/
def subgradientNormSet (h : ConstraintPoint → ℝ) : Set ℝ :=
  {t | ∃ v : ConstraintPoint, (∀ y : ConstraintPoint, h y ≥ h 0 + inner ℝ v y) ∧ ‖v‖ = t}

/-- Membership in `subgradientNormSet h` means that `t` is the norm of some Euclidean
subgradient `v` whose Riesz dual lies in `∂ h 0`. -/
theorem mem_subgradientNormSet_iff (h : ConstraintPoint → ℝ) (t : ℝ) :
    t ∈ subgradientNormSet h ↔
      ∃ v : ConstraintPoint, (∀ y : ConstraintPoint, h y ≥ h 0 + inner ℝ v y) ∧ ‖v‖ = t :=
  Iff.rfl

namespace StandardPenaltyProblem

/-- Given derivative data `objectiveGradient` and `constraintViolationDeriv` at a candidate
point, the source subgradient set `∂ P_(σ,h)` from `(10.6.57)` is represented by
`objectiveGradient + σ * constraintViolationDerivᵀ ∂ h(0)`. -/
def penaltyStationaritySubgradient
    (h : ConstraintPoint → ℝ) (σ : ℝ)
    (objectiveGradient : Point) (constraintViolationDeriv : Point →L[ℝ] ConstraintPoint) :
    Set Point :=
  {g | ∃ v : ConstraintPoint, (∀ y : ConstraintPoint, h y ≥ h 0 + inner ℝ v y) ∧
      g = objectiveGradient + σ • (constraintViolationDeriv.adjoint v)}

/-- Given derivative data at a candidate point, penalty stationarity is the source subgradient
condition `0 ∈ ∂ P_(σ,h)`. -/
def IsPenaltyStationary
    (h : ConstraintPoint → ℝ) (σ : ℝ)
    (objectiveGradient : Point) (constraintViolationDeriv : Point →L[ℝ] ConstraintPoint) :
    Prop :=
  (0 : Point) ∈ penaltyStationaritySubgradient h σ objectiveGradient constraintViolationDeriv

/-- Membership in
`penaltyStationaritySubgradient h σ objectiveGradient constraintViolationDeriv`
is exactly the source representation
`objectiveGradient + σ * constraintViolationDerivᵀ ∂ h(0)`. -/
@[simp] theorem mem_penaltyStationaritySubgradient_iff
    (h : ConstraintPoint → ℝ) (g : Point) (σ : ℝ)
    (objectiveGradient : Point) (constraintViolationDeriv : Point →L[ℝ] ConstraintPoint) :
    g ∈ penaltyStationaritySubgradient h σ objectiveGradient constraintViolationDeriv ↔
      ∃ v : ConstraintPoint, (∀ y : ConstraintPoint, h y ≥ h 0 + inner ℝ v y) ∧
        g = objectiveGradient + σ • (constraintViolationDeriv.adjoint v) :=
  Iff.rfl

/-- Given derivative data, penalty stationarity is exactly the source subgradient inclusion
`0 ∈ ∂ P_(σ,h)`. -/
@[simp] theorem isPenaltyStationary_iff
    (h : ConstraintPoint → ℝ) (σ : ℝ)
    (objectiveGradient : Point) (constraintViolationDeriv : Point →L[ℝ] ConstraintPoint) :
    IsPenaltyStationary h σ objectiveGradient constraintViolationDeriv ↔
      (0 : Point) ∈
        penaltyStationaritySubgradient h σ objectiveGradient constraintViolationDeriv :=
  Iff.rfl

/-- If the source penalty-stationarity condition `0 ∈ ∂ P_(σ,h)` holds for the derivative data
`objectiveGradient` and `constraintViolationDeriv`, and if `T` is the maximal norm of a
subgradient in `∂ h(0)`, then `‖objectiveGradient‖ ≤ σ * ‖constraintViolationDeriv‖ * T`. -/
theorem norm_gradient_le_of_isPenaltyStationary
    (h : ConstraintPoint → ℝ) (σ T : ℝ) (objectiveGradient : Point)
    (constraintViolationDeriv : Point →L[ℝ] ConstraintPoint)
    (h_stationary : IsPenaltyStationary h σ objectiveGradient constraintViolationDeriv)
    (hT : IsGreatest (subgradientNormSet h) T)
    (hσ_nonneg : 0 ≤ σ) :
    ‖objectiveGradient‖ ≤ σ * ‖constraintViolationDeriv‖ * T := by
  set A : Point →L[ℝ] ConstraintPoint := constraintViolationDeriv
  rw [isPenaltyStationary_iff] at h_stationary
  rcases h_stationary with ⟨v, hv, hgrad⟩
  have hv_le : ‖v‖ ≤ T := by
    exact hT.2 <|
      (mem_subgradientNormSet_iff h ‖v‖).2 ⟨v, hv, rfl⟩
  have hgrad_eq : objectiveGradient = -(σ • (A.adjoint v)) := by
    exact eq_neg_of_add_eq_zero_left (by simpa [A] using hgrad.symm)
  have hadjoint_norm : ‖A.adjoint‖ = ‖A‖ := by
    exact ContinuousLinearMap.adjoint.norm_map A
  calc
    ‖objectiveGradient‖ = ‖σ • (A.adjoint v)‖ := by
      rw [hgrad_eq, norm_neg]
    _ = σ * ‖A.adjoint v‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hσ_nonneg]
    _ ≤ σ * (‖A.adjoint‖ * ‖v‖) := by
      exact mul_le_mul_of_nonneg_left (A.adjoint.le_opNorm v) hσ_nonneg
    _ = σ * (‖A‖ * ‖v‖) := by rw [hadjoint_norm]
    _ ≤ σ * (‖A‖ * T) := by
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hv_le (norm_nonneg A)) hσ_nonneg
    _ = σ * ‖constraintViolationDeriv‖ * T := by
      simp [A, mul_assoc]

/-- `problem.IsPenaltyStationaryAt h σ xStar` is the source stationarity condition for the
exact-penalty objective `problem.nonsmoothExactPenalty h σ` at `xStar`, written using the actual
objective gradient and the actual derivative of the Chapter 10 violation map `c⁽-⁾[problem]` at
that point. -/
def IsPenaltyStationaryAt
    (problem : StandardPenaltyProblem n m) (h : ConstraintPoint → ℝ) (σ : ℝ) (xStar : Point) :
    Prop :=
  IsPenaltyStationary h σ (gradient problem.objective xStar) (fderiv ℝ (c⁽-⁾[problem]) xStar)

/-- Unfolding `problem.IsPenaltyStationaryAt h σ xStar` gives the source subgradient inclusion
`0 ∈ ∂ P_(σ,h)(xStar)` with the actual derivative data at `xStar`. -/
@[simp] theorem isPenaltyStationaryAt_iff
    (problem : StandardPenaltyProblem n m) (h : ConstraintPoint → ℝ) (σ : ℝ) (xStar : Point) :
    problem.IsPenaltyStationaryAt h σ xStar ↔
      IsPenaltyStationary h σ
        (gradient problem.objective xStar)
        (fderiv ℝ (c⁽-⁾[problem]) xStar) :=
  Iff.rfl

end StandardPenaltyProblem

/-- Reusable derivative-data obstruction for `(10.6.57)`: if `0 ≤ σ`, `0 < T`, and
`σ * ‖constraintViolationDeriv‖ < ‖objectiveGradient‖ / T`, then the source stationarity
condition `0 ∈ ∂ P_(σ,h)` cannot hold for those derivative data. -/
theorem not_isPenaltyStationary_of_norm_mul_lt_gradient_norm_div_subgradientMax
    (h : ConstraintPoint → ℝ) (σ T : ℝ) (objectiveGradient : Point)
    (constraintViolationDeriv : Point →L[ℝ] ConstraintPoint)
    (hT : IsGreatest (subgradientNormSet h) T)
    (hσ_nonneg : 0 ≤ σ)
    (hT_pos : 0 < T)
    (hσ : σ * ‖constraintViolationDeriv‖ < ‖objectiveGradient‖ / T) :
    ¬ StandardPenaltyProblem.IsPenaltyStationary
      h σ objectiveGradient constraintViolationDeriv := by
  intro h_stationary
  have h_le :=
    StandardPenaltyProblem.norm_gradient_le_of_isPenaltyStationary
      h σ T objectiveGradient constraintViolationDeriv h_stationary hT hσ_nonneg
  have h_lt : σ * ‖constraintViolationDeriv‖ * T < ‖objectiveGradient‖ := by
    exact (lt_div_iff₀ hT_pos).mp hσ
  exact (not_le_of_gt h_lt) h_le

namespace StandardPenaltyProblem

/-- Chapter10 Theorem 10.6.8: write `T` for the maximum norm over Euclidean subgradients
`v ∈ ∂ h(0)`. If `0 ≤ σ` and
`σ * ‖fderiv ℝ (c⁽-⁾[problem]) xStar‖ < ‖gradient problem.objective xStar‖ / T`,
then `xStar` is not stationary for the exact-penalty objective
`problem.nonsmoothExactPenalty h σ`. The source's local-minimizer preamble and explicit
nonzero-gradient hypothesis are omitted because this obstruction is purely pointwise and the
displayed strict inequality already forces `‖gradient problem.objective xStar‖ > 0`. -/
theorem not_isPenaltyStationaryAt_of_norm_mul_lt_gradient_norm_div_subgradientMax
    (problem : StandardPenaltyProblem n m) (h : ConstraintPoint → ℝ) (σ T : ℝ) (xStar : Point)
    (hT : IsGreatest (subgradientNormSet h) T)
    (hσ_nonneg : 0 ≤ σ)
    (hσ :
      σ * ‖fderiv ℝ (c⁽-⁾[problem]) xStar‖ <
        ‖gradient problem.objective xStar‖ / T) :
    ¬ problem.IsPenaltyStationaryAt h σ xStar := by
  have hleft_nonneg : 0 ≤ σ * ‖fderiv ℝ (c⁽-⁾[problem]) xStar‖ := by
    exact mul_nonneg hσ_nonneg (norm_nonneg _)
  have h_rhs_pos : 0 < ‖gradient problem.objective xStar‖ / T := by
    exact lt_of_le_of_lt hleft_nonneg hσ
  have hT_pos : 0 < T := by
    by_contra hT_pos
    have h_rhs_nonpos : ‖gradient problem.objective xStar‖ / T ≤ 0 := by
      exact div_nonpos_of_nonneg_of_nonpos (norm_nonneg _) (le_of_not_gt hT_pos)
    exact (not_le_of_gt h_rhs_pos) h_rhs_nonpos
  exact
    not_isPenaltyStationary_of_norm_mul_lt_gradient_norm_div_subgradientMax
      h σ T (gradient problem.objective xStar) (fderiv ℝ (c⁽-⁾[problem]) xStar)
      hT hσ_nonneg hT_pos hσ

end StandardPenaltyProblem

#print axioms subgradientNormSet
#print axioms StandardPenaltyProblem.penaltyStationaritySubgradient
#print axioms StandardPenaltyProblem.IsPenaltyStationaryAt

end
