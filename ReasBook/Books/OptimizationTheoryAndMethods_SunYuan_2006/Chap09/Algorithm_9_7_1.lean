/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Basic

noncomputable section

section Chapter09Algorithm971

variable {n m : ℕ}

local notation "PrimalPoint" => EuclideanSpace ℝ (Fin n)
local notation "DualPoint" => EuclideanSpace ℝ (Fin m)
local notation "ConstraintMatrix" => Matrix (Fin m) (Fin n) ℝ

-- Semantic recall: `lean_leansearch` surfaced only unrelated positivity/cone infrastructure,
-- not a reusable mathlib owner for this primal-dual interior-point framework. Following nearby
-- Chapter 9 precedent, this file therefore keeps the LP data and iteration rules explicit.

/-- A primal-dual-slack state `(x, λ, s)` for the linear constraints in Section 9.7. -/
structure PrimalDualState (n m : ℕ) where
  x : EuclideanSpace ℝ (Fin n)
  lam : EuclideanSpace ℝ (Fin m)
  s : EuclideanSpace ℝ (Fin n)

/-- A Newton search direction `(Δx, Δλ, Δs)` for a primal-dual state. -/
structure PrimalDualDirection (n m : ℕ) where
  dx : EuclideanSpace ℝ (Fin n)
  dlam : EuclideanSpace ℝ (Fin m)
  ds : EuclideanSpace ℝ (Fin n)

/-- A finite Euclidean vector is strictly positive when every coordinate is positive. -/
def IsStrictlyPositive {ι : Type*} [Fintype ι] (x : EuclideanSpace ℝ ι) : Prop :=
  ∀ i, 0 < x i

namespace PrimalDualState

/-- The complementarity average `μ = xᵀ s / n` attached to a primal-dual state. -/
def complementarityAverage (z : PrimalDualState n m) : ℝ :=
  dotProduct z.x z.s / (n : ℝ)

/-- The coordinatewise complementarity right-hand side
`-x_i s_i + σ * (xᵀ s / n)` from Algorithm 9.7.1. -/
def complementarityCorrection (z : PrimalDualState n m) (sigma : ℝ) : PrimalPoint :=
  (EuclideanSpace.equiv (Fin n) ℝ).symm
    (fun i ↦ -z.x i * z.s i + sigma * z.complementarityAverage)

/-- The update `(x, λ, s) + α (Δx, Δλ, Δs)` used in Algorithm 9.7.1. -/
def updated
    (z : PrimalDualState n m) (alpha : ℝ) (d : PrimalDualDirection n m) :
    PrimalDualState n m where
  x := z.x + alpha • d.dx
  lam := z.lam + alpha • d.dlam
  s := z.s + alpha • d.ds

end PrimalDualState

#print axioms PrimalDualState.updated

/-- The strictly feasible set `𝓕ᵒ` consists of the triples `(x, λ, s)` satisfying
`A.mulVec x = b`, `A.transpose.mulVec λ + s = c`, and strict positivity of `x` and `s`. -/
def strictlyFeasibleSet
    (A : ConstraintMatrix) (b : DualPoint) (c : PrimalPoint) :
    Set (PrimalDualState n m) :=
  {z |
    A.mulVec z.x = b ∧
      A.transpose.mulVec z.lam + z.s = c ∧
      IsStrictlyPositive z.x ∧
      IsStrictlyPositive z.s}

/-- Membership in `strictlyFeasibleSet A b c` is exactly the affine primal-dual feasibility
conditions together with strict positivity of `x` and `s`. -/
@[simp] theorem mem_strictlyFeasibleSet_iff
    (A : ConstraintMatrix) (b : DualPoint) (c : PrimalPoint) (z : PrimalDualState n m) :
    z ∈ strictlyFeasibleSet A b c ↔
      A.mulVec z.x = b ∧
        A.transpose.mulVec z.lam + z.s = c ∧
        IsStrictlyPositive z.x ∧
        IsStrictlyPositive z.s :=
  Iff.rfl

/-- `solvesPrimalDualNewtonSystem A z σ d` is the coordinate form of the linear system
`[0, Aᵀ, I; A, 0, 0; S, 0, X] [Δx; Δλ; Δs] = [0; 0; -X S e + σ μ e]`
at the current state `z = (x, λ, s)`. -/
def solvesPrimalDualNewtonSystem
    (A : ConstraintMatrix) (z : PrimalDualState n m) (sigma : ℝ)
    (d : PrimalDualDirection n m) : Prop :=
  A.transpose.mulVec d.dlam + d.ds = 0 ∧
    A.mulVec d.dx = 0 ∧
    ∀ i : Fin n, z.s i * d.dx i + z.x i * d.ds i = z.complementarityCorrection sigma i

/-- Unfolding `solvesPrimalDualNewtonSystem` gives the three block equations of the Newton
system from Algorithm 9.7.1. -/
@[simp] theorem solvesPrimalDualNewtonSystem_iff
    (A : ConstraintMatrix) (z : PrimalDualState n m) (sigma : ℝ)
    (d : PrimalDualDirection n m) :
    solvesPrimalDualNewtonSystem A z sigma d ↔
      A.transpose.mulVec d.dlam + d.ds = 0 ∧
        A.mulVec d.dx = 0 ∧
        (∀ i : Fin n,
          z.s i * d.dx i + z.x i * d.ds i = z.complementarityCorrection sigma i) :=
  Iff.rfl

/-- Chapter09 Algorithm 9.7.1: a primal-dual interior-point framework for the linear data
`(A, b, c)`. The sequence `state k` represents `(xᵏ, λᵏ, sᵏ)`, `direction k` represents
`(Δxᵏ, Δλᵏ, Δsᵏ)`, `sigma k ∈ [0, 1]` is the centering parameter `σ_k`, and
`μ_k = (state k).xᵀ (state k).s / n` is attached definitionally to the current state. The
initial state lies in `𝓕ᵒ`, each direction solves the Newton system with right-hand side
`-Xᵏ Sᵏ e + σ_k μ_k e`, and the next iterate is updated by
`(xᵏ⁺¹, λᵏ⁺¹, sᵏ⁺¹) = (xᵏ, λᵏ, sᵏ) + α_k (Δxᵏ, Δλᵏ, Δsᵏ)` with `xᵏ⁺¹` and `sᵏ⁺¹`
remaining strictly positive. -/
structure PrimalDualInteriorPointFramework
    (A : ConstraintMatrix) (b : DualPoint) (c : PrimalPoint) where
  state : ℕ → PrimalDualState n m
  direction : ℕ → PrimalDualDirection n m
  sigma : ℕ → ℝ
  alpha : ℕ → ℝ
  initial_mem : state 0 ∈ strictlyFeasibleSet A b c
  sigma_mem_Icc : ∀ k : ℕ, sigma k ∈ Set.Icc (0 : ℝ) 1
  newton_system :
    ∀ k : ℕ, solvesPrimalDualNewtonSystem A (state k) (sigma k) (direction k)
  update :
    ∀ k : ℕ, state (k + 1) = (state k).updated (alpha k) (direction k)
  next_strictPos :
    ∀ k : ℕ,
      IsStrictlyPositive (state (k + 1)).x ∧
        IsStrictlyPositive (state (k + 1)).s

/-- A primal-dual interior-point framework can be evaluated as its state sequence. -/
instance
    (A : ConstraintMatrix) (b : DualPoint) (c : PrimalPoint) :
    CoeFun (PrimalDualInteriorPointFramework A b c) (fun _ ↦ ℕ → PrimalDualState n m) where
  coe F := F.state

namespace PrimalDualInteriorPointFramework

/-- The quantity `μ_k` from Algorithm 9.7.1 is the complementarity average of the current
primal-dual state. -/
def mu
    {A : ConstraintMatrix} {b : DualPoint} {c : PrimalPoint}
    (F : PrimalDualInteriorPointFramework A b c) (k : ℕ) : ℝ :=
  (F.state k).complementarityAverage

#print axioms PrimalDualInteriorPointFramework.mu

/-- The framework quantity `μ_k` is definitionally the complementarity average
`(state k).xᵀ (state k).s / n`. -/
@[simp] theorem mu_eq
    {A : ConstraintMatrix} {b : DualPoint} {c : PrimalPoint}
    (F : PrimalDualInteriorPointFramework A b c) (k : ℕ) :
    F.mu k = (F.state k).complementarityAverage :=
  rfl

/-- Evaluating a primal-dual interior-point framework as a function returns its state
sequence. -/
@[simp] theorem coe_apply
    {A : ConstraintMatrix} {b : DualPoint} {c : PrimalPoint}
    (F : PrimalDualInteriorPointFramework A b c) (k : ℕ) :
    F k = F.state k :=
  rfl

/-- Unfolding `PrimalDualInteriorPointFramework` gives the source data of Algorithm 9.7.1:
strict-feasible initialization, `σ_k ∈ [0, 1]`, `μ_k = xᵏᵀ sᵏ / n`, the Newton-system solve,
the affine update, and strict positivity of `xᵏ⁺¹` and `sᵏ⁺¹`. -/
theorem spec
    {A : ConstraintMatrix} {b : DualPoint} {c : PrimalPoint}
    (F : PrimalDualInteriorPointFramework A b c) :
    F.state 0 ∈ strictlyFeasibleSet A b c ∧
      (∀ k : ℕ, F.sigma k ∈ Set.Icc (0 : ℝ) 1) ∧
      (∀ k : ℕ, F.mu k = (F.state k).complementarityAverage) ∧
      (∀ k : ℕ, solvesPrimalDualNewtonSystem A (F.state k) (F.sigma k) (F.direction k)) ∧
      (∀ k : ℕ, F.state (k + 1) = (F.state k).updated (F.alpha k) (F.direction k)) ∧
      (∀ k : ℕ,
        IsStrictlyPositive (F.state (k + 1)).x ∧
          IsStrictlyPositive (F.state (k + 1)).s) := by
  exact ⟨F.initial_mem, F.sigma_mem_Icc, fun k ↦ F.mu_eq k, F.newton_system, F.update,
    F.next_strictPos⟩

end PrimalDualInteriorPointFramework

end Chapter09Algorithm971
