/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Order.Filter.AtTopBot.Basic
import OptimizationTheoryAndMethods_SunYuan_2006.Chap12.Assumption_12_3_2

noncomputable section

section

open Asymptotics Filter

-- The source-facing 12.6 correction-step surface is expressed with the chapter's canonical SQP
-- subproblem owners from `Assumption_12_3_2`, while the asymptotic pieces use the canonical
-- mathlib owners `Asymptotics.IsBigO` and `Filter.Eventually`.

section Step

variable {Point : Type*}
variable [NormedAddCommGroup Point]

/-- Chapter12 Definition 12.6-extra-1: for a penalty function `Pσ`, iterate sequence `x_k`,
SQP step sequence `d_k`, and correction sequence `dHat_k`, `IsSecondOrderCorrectionStep Pσ x d
dHat` means that `‖dHat_k‖ = O(‖d_k‖^2)` and
`Pσ (x_k + d_k + dHat_k) < Pσ (x_k)` for all sufficiently large `k`, matching `(12.6.1)` and
`(12.6.2)`. -/
class IsSecondOrderCorrectionStep
    (Pσ : Point → ℝ) (x d dHat : ℕ → Point) : Prop where
  isBigO :
    IsBigO atTop (fun k ↦ ‖dHat k‖) (fun k ↦ ‖d k‖ ^ (2 : ℕ))
  penaltyDecrease :
    ∀ᶠ k in atTop, Pσ (x k + d k + dHat k) < Pσ (x k)

/-- Unfolding `IsSecondOrderCorrectionStep Pσ x d dHat` gives the canonical asymptotic size
estimate and eventual penalty decrease fields. -/
theorem isSecondOrderCorrectionStep_iff
    (Pσ : Point → ℝ) (x d dHat : ℕ → Point) :
    IsSecondOrderCorrectionStep Pσ x d dHat ↔
      IsBigO atTop (fun k ↦ ‖dHat k‖) (fun k ↦ ‖d k‖ ^ (2 : ℕ)) ∧
        ∀ᶠ k in atTop, Pσ (x k + d k + dHat k) < Pσ (x k) := by
  constructor
  · intro h
    exact ⟨h.isBigO, h.penaltyDecrease⟩
  · rintro ⟨isBigO, penaltyDecrease⟩
    exact ⟨isBigO, penaltyDecrease⟩

/-- Rewriting the eventual penalty decrease field at `atTop` recovers the source threshold form
`Pσ (x_k + d_k + dHat_k) < Pσ (x_k)` for all sufficiently large `k`. -/
theorem isSecondOrderCorrectionStep_iff_exists_eventually
    (Pσ : Point → ℝ) (x d dHat : ℕ → Point) :
    IsSecondOrderCorrectionStep Pσ x d dHat ↔
      IsBigO atTop (fun k ↦ ‖dHat k‖) (fun k ↦ ‖d k‖ ^ (2 : ℕ)) ∧
        ∃ K : ℕ, ∀ k : ℕ, K ≤ k → Pσ (x k + d k + dHat k) < Pσ (x k) := by
  rw [isSecondOrderCorrectionStep_iff, Filter.eventually_atTop]

end Step

section Objective

variable {Point : Type*}
variable [NormedAddCommGroup Point] [InnerProductSpace ℝ Point]

/-- The equality-constrained second-order correction objective from `(12.6.3)`,
`dHat ↦ g_kᵀ (d_k + dHat) + (1 / 2) (d_k + dHat)ᵀ B_k (d_k + dHat)`. -/
def secondOrderCorrectionObjective
    (gk dk : Point) (Bk : Point →L[ℝ] Point) (dHat : Point) : ℝ :=
  sqpSubproblemObjective gk Bk (dk + dHat)

/-- Unfolding `secondOrderCorrectionObjective gk dk Bk dHat` gives the source quadratic model
from `(12.6.3)`. -/
theorem secondOrderCorrectionObjective_eq
    (gk dk : Point) (Bk : Point →L[ℝ] Point) (dHat : Point) :
    secondOrderCorrectionObjective gk dk Bk dHat =
      inner ℝ gk (dk + dHat) +
        (1 / 2 : ℝ) * inner ℝ (dk + dHat) (Bk (dk + dHat)) := rfl

end Objective

section Subproblem

variable {Point Multiplier : Type*}
variable [NormedAddCommGroup Point] [InnerProductSpace ℝ Point] [CompleteSpace Point]
variable [NormedAddCommGroup Multiplier] [InnerProductSpace ℝ Multiplier]
  [CompleteSpace Multiplier]

/-- A correction vector `dHat_k` solves the equality-constrained second-order correction
subproblem when it satisfies the `(12.6.4)` correction equation, expressed by the chapter's
canonical predicate `satisfiesSqpLinearizedConstraints Ak cNext dHat`, and minimizes the shifted
quadratic model `(12.6.3)` over all equality-feasible correction vectors. -/
def IsSecondOrderCorrectionSubproblemSolution
    (gk dk : Point) (Bk : Point →L[ℝ] Point)
    (Ak : Multiplier →L[ℝ] Point) (cNext : Multiplier) (dHat : Point) : Prop :=
  satisfiesSqpLinearizedConstraints Ak cNext dHat ∧
    ∀ d' : Point, satisfiesSqpLinearizedConstraints Ak cNext d' →
      secondOrderCorrectionObjective gk dk Bk dHat ≤
        secondOrderCorrectionObjective gk dk Bk d'

/-- Unfolding `IsSecondOrderCorrectionSubproblemSolution` gives the equality-feasibility and
global minimality conditions of the correction subproblem. -/
theorem isSecondOrderCorrectionSubproblemSolution_iff
    (gk dk : Point) (Bk : Point →L[ℝ] Point)
    (Ak : Multiplier →L[ℝ] Point) (cNext : Multiplier) (dHat : Point) :
    IsSecondOrderCorrectionSubproblemSolution gk dk Bk Ak cNext dHat ↔
      satisfiesSqpLinearizedConstraints Ak cNext dHat ∧
        ∀ d' : Point, satisfiesSqpLinearizedConstraints Ak cNext d' →
          secondOrderCorrectionObjective gk dk Bk dHat ≤
            secondOrderCorrectionObjective gk dk Bk d' := Iff.rfl

/-- A solution of the second-order correction subproblem satisfies the equality constraint
`A(x_k)ᵀ dHat_k = -c(x_k + d_k)`. -/
theorem IsSecondOrderCorrectionSubproblemSolution.feasible
    {gk dk : Point} {Bk : Point →L[ℝ] Point}
    {Ak : Multiplier →L[ℝ] Point} {cNext : Multiplier} {dHat : Point}
    (h : IsSecondOrderCorrectionSubproblemSolution gk dk Bk Ak cNext dHat) :
    satisfiesSqpLinearizedConstraints Ak cNext dHat :=
  h.1

/-- A solution of the second-order correction subproblem minimizes the shifted quadratic model
over all equality-feasible correction vectors. -/
theorem IsSecondOrderCorrectionSubproblemSolution.objective_le
    {gk dk : Point} {Bk : Point →L[ℝ] Point}
    {Ak : Multiplier →L[ℝ] Point} {cNext : Multiplier} {dHat : Point}
    (h : IsSecondOrderCorrectionSubproblemSolution gk dk Bk Ak cNext dHat)
    (d' : Point) (hd' : satisfiesSqpLinearizedConstraints Ak cNext d') :
    secondOrderCorrectionObjective gk dk Bk dHat ≤
      secondOrderCorrectionObjective gk dk Bk d' :=
  h.2 d' hd'

-- The book derives the multiplier equations only after extra convergence and second-order
-- hypotheses, so this file keeps `(12.6.6)`-`(12.6.9)` as an explicit predicate on the equations
-- themselves rather than as a stronger existence theorem.

/-- The equality-constrained multiplier equations `(12.6.6)`-`(12.6.9)` for the base SQP step
`d_k` and second-order correction `dHat_k`. This is kept as an explicit predicate on the
equations themselves, rather than as a derived existence theorem, because the source deduces
these multipliers only after adding further hypotheses not formalized in this file. -/
def satisfiesSecondOrderCorrectionMultiplierEquations
    (gk dk dHat : Point)
    (Bk : Point →L[ℝ] Point)
    (Ak : Multiplier →L[ℝ] Point)
    (ck cNext : Multiplier) : Prop :=
    ∃ lam lamHat : Multiplier,
      Bk dk = -gk + Ak lam ∧
        satisfiesSqpLinearizedConstraints Ak ck dk ∧
        Bk dk + Bk dHat = -gk + Ak lamHat ∧
        satisfiesSqpLinearizedConstraints Ak cNext dHat

/-- Unfolding `satisfiesSecondOrderCorrectionMultiplierEquations` gives the explicit multiplier
equations `(12.6.6)`-`(12.6.9)`. -/
theorem satisfiesSecondOrderCorrectionMultiplierEquations_iff
    (gk dk dHat : Point)
    (Bk : Point →L[ℝ] Point)
    (Ak : Multiplier →L[ℝ] Point)
    (ck cNext : Multiplier) :
    satisfiesSecondOrderCorrectionMultiplierEquations gk dk dHat Bk Ak ck cNext ↔
      ∃ lam lamHat : Multiplier,
        Bk dk = -gk + Ak lam ∧
          Ak.adjoint dk = -ck ∧
          Bk dk + Bk dHat = -gk + Ak lamHat ∧
          Ak.adjoint dHat = -cNext := by
  rw [satisfiesSecondOrderCorrectionMultiplierEquations, satisfiesSqpLinearizedConstraints_iff,
    satisfiesSqpLinearizedConstraints_iff]

/-- The multiplier equations `(12.6.6)`-`(12.6.9)` include the base SQP feasibility equation
`A(x_k)ᵀ d_k = -c(x_k)` from `(12.6.7)`. -/
theorem satisfiesSecondOrderCorrectionMultiplierEquations_baseFeasibility
    (gk dk dHat : Point)
    (Bk : Point →L[ℝ] Point)
    (Ak : Multiplier →L[ℝ] Point)
    (ck cNext : Multiplier)
    (hMultipliers :
      satisfiesSecondOrderCorrectionMultiplierEquations gk dk dHat Bk Ak ck cNext) :
    satisfiesSqpLinearizedConstraints Ak ck dk := by
  rcases hMultipliers with ⟨_, _, _, hFeasible, _, _⟩
  exact hFeasible

/-- The multiplier equations `(12.6.6)`-`(12.6.9)` include the second-order correction
feasibility equation `A(x_k)ᵀ dHat_k = -c(x_k + d_k)` from `(12.6.9)`. -/
theorem satisfiesSecondOrderCorrectionMultiplierEquations_correctionFeasibility
    (gk dk dHat : Point)
    (Bk : Point →L[ℝ] Point)
    (Ak : Multiplier →L[ℝ] Point)
    (ck cNext : Multiplier)
    (hMultipliers :
      satisfiesSecondOrderCorrectionMultiplierEquations gk dk dHat Bk Ak ck cNext) :
    satisfiesSqpLinearizedConstraints Ak cNext dHat := by
  rcases hMultipliers with ⟨_, _, _, _, _, hFeasible⟩
  exact hFeasible

/-- If `P_k` annihilates the range of `A(x_k)`, then the multiplier equations `(12.6.6)` and
`(12.6.8)` from `satisfiesSecondOrderCorrectionMultiplierEquations` imply the projected relation
`P_k (B_k dHat_k) = 0` from `(12.6.10)`. -/
theorem projectedSecondOrderCorrection_eq_zero_of_multiplierEquations
    (projector : Point →L[ℝ] Point)
    (gk dk dHat : Point)
    (Bk : Point →L[ℝ] Point)
    (Ak : Multiplier →L[ℝ] Point)
    (ck cNext : Multiplier)
    (hProjectorA : ∀ μ : Multiplier, projector (Ak μ) = 0)
    (hMultipliers :
      satisfiesSecondOrderCorrectionMultiplierEquations gk dk dHat Bk Ak ck cNext) :
    projector (Bk dHat) = 0 := by
  rcases hMultipliers with ⟨lam, lamHat, hBaseStationarity, _, hCorrectionStationarity, _⟩
  have hBaseProjected : projector (Bk dk) = projector (-gk) := by
    simpa [hProjectorA lam] using congrArg projector hBaseStationarity
  have hCorrectionProjected :
      projector (Bk dk) + projector (Bk dHat) = projector (-gk) := by
    simpa [map_add, hProjectorA lamHat] using congrArg projector hCorrectionStationarity
  have hCancel :
      projector (Bk dk) + projector (Bk dHat) = projector (Bk dk) + 0 := by
    calc
      projector (Bk dk) + projector (Bk dHat) = projector (-gk) := hCorrectionProjected
      _ = projector (Bk dk) := hBaseProjected.symm
      _ = projector (Bk dk) + 0 := by simp
  exact add_left_cancel hCancel

end Subproblem

#print axioms IsSecondOrderCorrectionStep
#print axioms sqpSubproblemObjective
#print axioms isSqpSubproblemSolution
#print axioms secondOrderCorrectionObjective
#print axioms IsSecondOrderCorrectionSubproblemSolution
#print axioms satisfiesSecondOrderCorrectionMultiplierEquations

end
