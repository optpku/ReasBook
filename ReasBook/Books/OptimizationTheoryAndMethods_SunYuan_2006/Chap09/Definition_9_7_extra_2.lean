/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import OptimizationTheoryAndMethods_SunYuan_2006.Chap09.Algorithm_9_7_1

noncomputable section

/-
Domain sampling:
* primary domain: primal-dual interior-point central-path residual data
* inspected project declarations:
  - `PrimalDualState` and `IsStrictlyPositive` from `Algorithm_9_7_1`
  - `centralPath` and `centralResidualMap` from `Definition_9_7_extra_1`
  - `DualMethodState` from `Algorithm_9_5_1`, confirming the chapter style of using named state
    owners instead of nested tuple coordinates
* source/core/bridge triage:
  - source-facing owner here: `residualCentralPath F`
  - core/canonical owner here: `CentralPathState n m`
  - bridge/view here: `CentralPathState.tauTarget` and `IsTauCentralPathPoint`
* primitive data: a residual map `F` and a point `(x, y, λ)`
* derived API: the residual target `(0, 0, τ e)`, fixed-`τ` central-path membership, and the
  existential-path set

There is no upstream Chapter 9 owner for residual-map states of shape `(x, y, λ)` with both
`y` and `λ` in `ℝ^m`, so this file keeps `CentralPathState` as the primitive owner and derives
the recurring residual target `(0, 0, τ e)` from it instead of rebuilding that target state
ad hoc in every declaration.
-/

section

variable {n m : ℕ}

local notation "PrimalPoint" => EuclideanSpace ℝ (Fin n)
local notation "DualPoint" => EuclideanSpace ℝ (Fin m)

/-- A central-path state `(x, y, λ)` for the residual-map formulation of Definition 9.7-extra-2. -/
structure CentralPathState (n m : ℕ) where
  x : EuclideanSpace ℝ (Fin n)
  y : EuclideanSpace ℝ (Fin m)
  lam : EuclideanSpace ℝ (Fin m)

namespace CentralPathState

/-- The residual target `(0, 0, τ e)` in the residual-map formulation of
Definition 9.7-extra-2. -/
def tauTarget (τ : ℝ) : CentralPathState n m :=
  ⟨(0 : PrimalPoint), (0 : DualPoint), WithLp.toLp 2 (fun _ ↦ τ)⟩

end CentralPathState

/-- A state `(x, y, λ)` is a `τ`-central-path point for the residual map `F` when
`F (x, y, λ) = (0, 0, τ e)` and both `y` and `λ` are strictly positive. -/
def IsTauCentralPathPoint
    (F : CentralPathState n m → CentralPathState n m) (τ : ℝ)
    (point : CentralPathState n m) : Prop :=
  F point = CentralPathState.tauTarget τ ∧
    IsStrictlyPositive point.y ∧
    IsStrictlyPositive point.lam

/-- Unfolding `IsTauCentralPathPoint F τ point` gives the residual equation `F point = (0, 0, τ e)`
and strict positivity of the `y`- and `λ`-components. -/
@[simp] theorem isTauCentralPathPoint_iff
    (F : CentralPathState n m → CentralPathState n m) (τ : ℝ)
    (point : CentralPathState n m) :
    IsTauCentralPathPoint F τ point ↔
      F point = CentralPathState.tauTarget τ ∧
        IsStrictlyPositive point.y ∧
        IsStrictlyPositive point.lam :=
  Iff.rfl

/-- Chapter09 Definition 9.7-extra-2: the central path `𝒞` attached to the residual map `F` is
the set of triples `(x_τ, y_τ, λ_τ)` for which there exists `τ > 0` such that
`F (x_τ, y_τ, λ_τ) = (0, 0, τ e)` and both `y_τ` and `λ_τ` are strictly positive. -/
def residualCentralPath
    (F : CentralPathState n m → CentralPathState n m) : Set (CentralPathState n m) :=
  {point | ∃ τ > 0, IsTauCentralPathPoint F τ point}

#print axioms residualCentralPath

/-- Membership in `residualCentralPath F` means that the point satisfies the `τ`-central-path
system for some positive parameter `τ`. -/
theorem mem_residualCentralPath_iff
    (F : CentralPathState n m → CentralPathState n m) (point : CentralPathState n m) :
    point ∈ residualCentralPath F ↔
      ∃ τ > 0, IsTauCentralPathPoint F τ point := by
  rfl

/-- Membership in `residualCentralPath F` is equivalent to solving the residual equation
`F point = (0, 0, τ e)` for some `τ > 0` with strictly positive `y`- and `λ`-components. -/
theorem mem_residualCentralPath_iff_exists_target_eq
    (F : CentralPathState n m → CentralPathState n m) (point : CentralPathState n m) :
    point ∈ residualCentralPath F ↔
      ∃ τ > 0,
        F point = CentralPathState.tauTarget τ ∧
          IsStrictlyPositive point.y ∧
          IsStrictlyPositive point.lam := by
  rw [mem_residualCentralPath_iff]
  simp

end
