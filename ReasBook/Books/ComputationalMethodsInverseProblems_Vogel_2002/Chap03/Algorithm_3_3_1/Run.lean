/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import ComputationalMethodsInverseProblems_Vogel_2002.Chap03.Definition_3_2.Profile
public import ComputationalMethodsInverseProblems_Vogel_2002.Chap03.Definition_3_3_3.Update
public import Mathlib.Analysis.Calculus.Gradient.Basic
public import Mathlib.Order.Filter.Extr

public section

noncomputable section

namespace BFGS

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- Helper for Algorithm 3.3.1: a BFGS stage stores the current iterate, the
current gradient, and the current Hessian approximation. -/
structure State (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℝ H] where
  point : H
  gradient : H
  hessian : H →L[ℝ] H

/-- Helper for Algorithm 3.3.1: when the current Hessian approximation is
invertible, the BFGS search direction is `-H_v⁻¹ g_v`. -/
def direction (state : State H) (hH : IsUnit state.hessian) : H :=
  let _ : IsUnit state.hessian := hH;
  -Ring.inverse state.hessian state.gradient

/-- Helper for Algorithm 3.3.1: the secant step `s_v = τ_v • p_v`. -/
def stepVector (τ : ℝ) (state : State H) (hH : IsUnit state.hessian) : H :=
  τ • direction state hH

/-- Helper for Algorithm 3.3.1: the next iterate is `f_v + τ_v • p_v`. -/
def nextPoint (τ : ℝ) (state : State H) (hH : IsUnit state.hessian) : H :=
  state.point + stepVector τ state hH

section CompleteSpace

variable [CompleteSpace H]

/-- Helper for Algorithm 3.3.1: the initial BFGS state has point `f0`,
gradient `gradient J f0`, and Hessian approximation `H0`. -/
def initialState (J : H → ℝ) (f0 : H) (H0 : H →L[ℝ] H) : State H :=
  { point := f0, gradient := gradient J f0, hessian := H0 }

/-- Helper for Algorithm 3.3.1: one BFGS step records invertibility of the
current Hessian approximation, exact line search on the positive ray, the
iterate update, the gradient refresh, and the Hessian update `(3.23)`. -/
structure Step (J : H → ℝ) (τ : ℝ) (current next : State H) : Prop where
  hessian_isUnit : IsUnit current.hessian
  lineSearch :
    IsMinOn
      (LineSearch.profile J current.point (BFGS.direction current hessian_isUnit))
      (Set.Ioi (0 : ℝ))
      τ
  point_eq : next.point = BFGS.nextPoint τ current hessian_isUnit
  gradient_eq : next.gradient = gradient J next.point
  hessian_eq :
    next.hessian =
      BFGS.update
        current.hessian
        (next.point - current.point)
        (next.gradient - current.gradient)

namespace Step

/-- Builds a BFGS step from the displayed Algorithm 3.3.1 clauses. -/
theorem ofClauses
    (J : H → ℝ) (τ : ℝ) (current next : State H)
    (h_hessian_isUnit : IsUnit current.hessian)
    (h_lineSearch :
      IsMinOn
        (LineSearch.profile J current.point (BFGS.direction current h_hessian_isUnit))
        (Set.Ioi (0 : ℝ))
        τ)
    (h_point : next.point = BFGS.nextPoint τ current h_hessian_isUnit)
    (h_gradient : next.gradient = gradient J next.point)
    (h_hessian :
      next.hessian =
        BFGS.update
          current.hessian
          (next.point - current.point)
          (next.gradient - current.gradient)) :
    BFGS.Step J τ current next :=
  { hessian_isUnit := h_hessian_isUnit
    lineSearch := h_lineSearch
    point_eq := h_point
    gradient_eq := h_gradient
    hessian_eq := h_hessian }

/-- Specification theorem for the one-step BFGS relation `BFGS.Step`. -/
theorem step_iff
    (J : H → ℝ) (τ : ℝ) (current next : State H) :
    BFGS.Step J τ current next ↔
      ∃ h_hessian_isUnit : IsUnit current.hessian,
        IsMinOn
          (LineSearch.profile J current.point (BFGS.direction current h_hessian_isUnit))
          (Set.Ioi (0 : ℝ))
          τ ∧
        next.point = BFGS.nextPoint τ current h_hessian_isUnit ∧
        next.gradient = gradient J next.point ∧
        next.hessian =
          BFGS.update
            current.hessian
            (next.point - current.point)
            (next.gradient - current.gradient) := by
  constructor
  · intro h
    exact ⟨h.hessian_isUnit, h.lineSearch, h.point_eq, h.gradient_eq, h.hessian_eq⟩
  · rintro ⟨h_hessian_isUnit, h_lineSearch, h_point, h_gradient, h_hessian⟩
    exact ofClauses J τ current next h_hessian_isUnit h_lineSearch h_point h_gradient h_hessian

end Step

/-- Algorithm 3.3.1. A sequence `σ` with step sizes `τ` is a BFGS run for `J`
from `f0` and `H0` when it starts from the prescribed initial state and each
successor pair satisfies the BFGS step clauses. -/
def IsRun
    (J : H → ℝ) (f0 : H) (H0 : H →L[ℝ] H)
    (σ : ℕ → State H) (τ : ℕ → ℝ) : Prop :=
  σ 0 = initialState J f0 H0 ∧ ∀ v : ℕ, BFGS.Step J (τ v) (σ v) (σ (v + 1))

namespace IsRun

/-- Specification theorem for `BFGS.IsRun`. -/
theorem isRun_iff
    (J : H → ℝ) (f0 : H) (H0 : H →L[ℝ] H)
    (σ : ℕ → State H) (τ : ℕ → ℝ) :
    BFGS.IsRun J f0 H0 σ τ ↔
      σ 0 = BFGS.initialState J f0 H0 ∧
        ∀ v : ℕ, BFGS.Step J (τ v) (σ v) (σ (v + 1)) :=
  Iff.rfl

/-- Extracts the initialization clause from `BFGS.IsRun`. -/
theorem init_eq
    {J : H → ℝ} {f0 : H} {H0 : H →L[ℝ] H}
    {σ : ℕ → State H} {τ : ℕ → ℝ}
    (h : BFGS.IsRun J f0 H0 σ τ) :
    σ 0 = BFGS.initialState J f0 H0 :=
  h.1

/-- Extracts the one-step BFGS relation from `BFGS.IsRun`. -/
theorem step
    {J : H → ℝ} {f0 : H} {H0 : H →L[ℝ] H}
    {σ : ℕ → State H} {τ : ℕ → ℝ}
    (h : BFGS.IsRun J f0 H0 σ τ) (v : ℕ) :
    BFGS.Step J (τ v) (σ v) (σ (v + 1)) :=
  h.2 v

/-- Extracts the invertibility clause for the current Hessian approximation from
`BFGS.IsRun`. -/
theorem hessian_isUnit
    {J : H → ℝ} {f0 : H} {H0 : H →L[ℝ] H}
    {σ : ℕ → State H} {τ : ℕ → ℝ}
    (h : BFGS.IsRun J f0 H0 σ τ) (v : ℕ) :
    IsUnit (σ v).hessian :=
  (step h v).hessian_isUnit

/-- Extracts the exact line-search clause from `BFGS.IsRun`. -/
theorem lineSearch
    {J : H → ℝ} {f0 : H} {H0 : H →L[ℝ] H}
    {σ : ℕ → State H} {τ : ℕ → ℝ}
    (h : BFGS.IsRun J f0 H0 σ τ) (v : ℕ) :
    IsMinOn
      (LineSearch.profile J (σ v).point (BFGS.direction (σ v) (hessian_isUnit h v)))
      (Set.Ioi (0 : ℝ))
      (τ v) := by
  simpa using (step h v).lineSearch

/-- Extracts the iterate-update clause from `BFGS.IsRun`. -/
theorem point_eq
    {J : H → ℝ} {f0 : H} {H0 : H →L[ℝ] H}
    {σ : ℕ → State H} {τ : ℕ → ℝ}
    (h : BFGS.IsRun J f0 H0 σ τ) (v : ℕ) :
    (σ (v + 1)).point = BFGS.nextPoint (τ v) (σ v) (hessian_isUnit h v) := by
  simpa using (step h v).point_eq

/-- Extracts the gradient-refresh clause from `BFGS.IsRun`. -/
theorem gradient_eq
    {J : H → ℝ} {f0 : H} {H0 : H →L[ℝ] H}
    {σ : ℕ → State H} {τ : ℕ → ℝ}
    (h : BFGS.IsRun J f0 H0 σ τ) (v : ℕ) :
    (σ (v + 1)).gradient = gradient J (σ (v + 1)).point :=
  (step h v).gradient_eq

/-- Extracts the BFGS Hessian-update clause from `BFGS.IsRun`. -/
theorem hessian_eq
    {J : H → ℝ} {f0 : H} {H0 : H →L[ℝ] H}
    {σ : ℕ → State H} {τ : ℕ → ℝ}
    (h : BFGS.IsRun J f0 H0 σ τ) (v : ℕ) :
    (σ (v + 1)).hessian =
      BFGS.update
        (σ v).hessian
        ((σ (v + 1)).point - (σ v).point)
        ((σ (v + 1)).gradient - (σ v).gradient) :=
  (step h v).hessian_eq

end IsRun

end CompleteSpace

end BFGS
