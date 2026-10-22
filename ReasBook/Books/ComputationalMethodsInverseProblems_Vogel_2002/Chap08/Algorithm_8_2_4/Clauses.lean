/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import Mathlib.Data.Matrix.Diagonal
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Real.Basic
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.Order.ConditionallyCompletePartialOrder.Basic

public section

open scoped Matrix

universe u v w

namespace TVPrimalDualNewton

/-- Algorithm 8.2.4 (1). The primal-dual Newton run starts from the displayed
initial primal and dual guesses `f0`, `u0`, and `v0`. -/
structure IsInitialized {ι : Type u} {δ : Type v}
    (f0 : ι → ℝ) (u0 v0 : δ → ℝ)
    (f : ℕ → ι → ℝ) (uDual vDual : ℕ → δ → ℝ) : Prop where
  primal_eq : f 0 = f0
  firstDual_eq : uDual 0 = u0
  secondDual_eq : vDual 0 = v0

set_option linter.defProp false in
/-- Builds the initialization clause from the three displayed starting
equalities. -/
def IsInitialized.ofEq {ι : Type u} {δ : Type v}
    (f0 : ι → ℝ) (u0 v0 : δ → ℝ)
    (f : ℕ → ι → ℝ) (uDual vDual : ℕ → δ → ℝ)
    (h_primal : f 0 = f0) (h_firstDual : uDual 0 = u0)
    (h_secondDual : vDual 0 = v0) :
    IsInitialized f0 u0 v0 f uDual vDual :=
  { primal_eq := h_primal
    firstDual_eq := h_firstDual
    secondDual_eq := h_secondDual }

/-- Extracts the displayed primal initialization equality from
`TVPrimalDualNewton.IsInitialized`. -/
theorem IsInitialized.init_eq {ι : Type u} {δ : Type v}
    {f0 : ι → ℝ} {u0 v0 : δ → ℝ}
    {f : ℕ → ι → ℝ} {uDual vDual : ℕ → δ → ℝ}
    (h : IsInitialized f0 u0 v0 f uDual vDual) :
    f 0 = f0 :=
  h.primal_eq

/-- Extracts the displayed first dual initialization equality from
`TVPrimalDualNewton.IsInitialized`. -/
theorem IsInitialized.u_init_eq {ι : Type u} {δ : Type v}
    {f0 : ι → ℝ} {u0 v0 : δ → ℝ}
    {f : ℕ → ι → ℝ} {uDual vDual : ℕ → δ → ℝ}
    (h : IsInitialized f0 u0 v0 f uDual vDual) :
    uDual 0 = u0 :=
  h.firstDual_eq

/-- Extracts the displayed second dual initialization equality from
`TVPrimalDualNewton.IsInitialized`. -/
theorem IsInitialized.v_init_eq {ι : Type u} {δ : Type v}
    {f0 : ι → ℝ} {u0 v0 : δ → ℝ}
    {f : ℕ → ι → ℝ} {uDual vDual : ℕ → δ → ℝ}
    (h : IsInitialized f0 u0 v0 f uDual vDual) :
    vDual 0 = v0 :=
  h.secondDual_eq

/-- The displayed intermediate diagonal, diffusion, and residual assignments at
iterate `n`. -/
structure IntermediateAssignmentsStep
    {ι : Type u} {δ : Type v} {κ : Type w}
    [Fintype ι] [DecidableEq ι] [Fintype δ] [DecidableEq δ]
    [Fintype κ] [DecidableEq κ]
    (ψ' ψ'' : (ι → ℝ) → δ → ℝ)
    (K : Matrix κ ι ℝ) (Dx Dy Dv : Matrix δ ι ℝ) (α : ℝ) (d : κ → ℝ)
    (f : ℕ → ι → ℝ) (uDual vDual wVec : ℕ → δ → ℝ)
    (bInv E11 E12 E21 E22 : ℕ → Matrix δ δ ℝ)
    (lbar : ℕ → Matrix ι ι ℝ) (r : ℕ → ι → ℝ) (n : ℕ) : Prop where
  bInv_eq : bInv n = Matrix.diagonal (ψ' (f n))
  w_eq : wVec n = fun i ↦ (2 : ℝ) * ψ' (f n) i / ψ'' (f n) i
  E11_eq :
    E11 n =
      Matrix.diagonal
        (fun i ↦ wVec n i * Matrix.mulVec Dx (f n) i * uDual n i)
  E12_eq :
    E12 n =
      Matrix.diagonal
        (fun i ↦ wVec n i * Matrix.mulVec Dy (f n) i * uDual n i)
  E21_eq :
    E21 n =
      Matrix.diagonal
        (fun i ↦ wVec n i * Matrix.mulVec Dx (f n) i * vDual n i)
  E22_eq :
    E22 n =
      Matrix.diagonal
        (fun i ↦ wVec n i * Matrix.mulVec Dy (f n) i * vDual n i)
  lbar_eq :
    lbar n =
      Dxᵀ * bInv n * E11 n * Dx +
        Dxᵀ * bInv n * E12 n * Dy +
          Dyᵀ * bInv n * E21 n * Dx +
            Dvᵀ * bInv n * E22 n * Dy
  residual_eq :
    r n =
      Matrix.mulVec Kᵀ (fun i ↦ d i - Matrix.mulVec K (f n) i) -
        Matrix.mulVec (α • (Dxᵀ * bInv n * Dx + Dyᵀ * bInv n * Dy)) (f n)

set_option linter.defProp false in
/-- Builds the iterate-`n` intermediate-assignment clause from the eight
displayed equalities. -/
def IntermediateAssignmentsStep.ofEq
    {ι : Type u} {δ : Type v} {κ : Type w}
    [Fintype ι] [DecidableEq ι] [Fintype δ] [DecidableEq δ]
    [Fintype κ] [DecidableEq κ]
    (ψ' ψ'' : (ι → ℝ) → δ → ℝ)
    (K : Matrix κ ι ℝ) (Dx Dy Dv : Matrix δ ι ℝ) (α : ℝ) (d : κ → ℝ)
    (f : ℕ → ι → ℝ) (uDual vDual wVec : ℕ → δ → ℝ)
    (bInv E11 E12 E21 E22 : ℕ → Matrix δ δ ℝ)
    (lbar : ℕ → Matrix ι ι ℝ) (r : ℕ → ι → ℝ) (n : ℕ)
    (h_bInv : bInv n = Matrix.diagonal (ψ' (f n)))
    (h_w : wVec n = fun i ↦ (2 : ℝ) * ψ' (f n) i / ψ'' (f n) i)
    (h_E11 :
      E11 n =
        Matrix.diagonal
          (fun i ↦ wVec n i * Matrix.mulVec Dx (f n) i * uDual n i))
    (h_E12 :
      E12 n =
        Matrix.diagonal
          (fun i ↦ wVec n i * Matrix.mulVec Dy (f n) i * uDual n i))
    (h_E21 :
      E21 n =
        Matrix.diagonal
          (fun i ↦ wVec n i * Matrix.mulVec Dx (f n) i * vDual n i))
    (h_E22 :
      E22 n =
        Matrix.diagonal
          (fun i ↦ wVec n i * Matrix.mulVec Dy (f n) i * vDual n i))
    (h_lbar :
      lbar n =
        Dxᵀ * bInv n * E11 n * Dx +
          Dxᵀ * bInv n * E12 n * Dy +
            Dyᵀ * bInv n * E21 n * Dx +
              Dvᵀ * bInv n * E22 n * Dy)
    (h_residual :
      r n =
        Matrix.mulVec Kᵀ (fun i ↦ d i - Matrix.mulVec K (f n) i) -
          Matrix.mulVec (α • (Dxᵀ * bInv n * Dx + Dyᵀ * bInv n * Dy)) (f n)) :
    IntermediateAssignmentsStep
      ψ' ψ'' K Dx Dy Dv α d f uDual vDual wVec bInv E11 E12 E21 E22 lbar r n :=
  { bInv_eq := h_bInv
    w_eq := h_w
    E11_eq := h_E11
    E12_eq := h_E12
    E21_eq := h_E21
    E22_eq := h_E22
    lbar_eq := h_lbar
    residual_eq := h_residual }

/-- Algorithm 8.2.4 (2). The displayed intermediate diagonal, diffusion, and
residual assignments hold at every iterate. -/
abbrev HasIntermediateAssignments
    {ι : Type u} {δ : Type v} {κ : Type w}
    [Fintype ι] [DecidableEq ι] [Fintype δ] [DecidableEq δ]
    [Fintype κ] [DecidableEq κ]
    (ψ' ψ'' : (ι → ℝ) → δ → ℝ)
    (K : Matrix κ ι ℝ) (Dx Dy Dv : Matrix δ ι ℝ) (α : ℝ) (d : κ → ℝ)
    (f : ℕ → ι → ℝ) (uDual vDual wVec : ℕ → δ → ℝ)
    (bInv E11 E12 E21 E22 : ℕ → Matrix δ δ ℝ)
    (lbar : ℕ → Matrix ι ι ℝ) (r : ℕ → ι → ℝ) : Prop :=
  ∀ n : ℕ,
    IntermediateAssignmentsStep
      ψ' ψ'' K Dx Dy Dv α d f uDual vDual wVec bInv E11 E12 E21 E22 lbar r n

/-- Extracts the displayed `B_v⁻¹` equality from
`TVPrimalDualNewton.HasIntermediateAssignments`. -/
theorem HasIntermediateAssignments.bInv_eq
    {ι : Type u} {δ : Type v} {κ : Type w}
    [Fintype ι] [DecidableEq ι] [Fintype δ] [DecidableEq δ]
    [Fintype κ] [DecidableEq κ]
    {ψ' ψ'' : (ι → ℝ) → δ → ℝ}
    {K : Matrix κ ι ℝ} {Dx Dy Dv : Matrix δ ι ℝ} {α : ℝ} {d : κ → ℝ}
    {f : ℕ → ι → ℝ} {uDual vDual wVec : ℕ → δ → ℝ}
    {bInv E11 E12 E21 E22 : ℕ → Matrix δ δ ℝ}
    {lbar : ℕ → Matrix ι ι ℝ} {r : ℕ → ι → ℝ}
    (h : HasIntermediateAssignments
      ψ' ψ'' K Dx Dy Dv α d f uDual vDual wVec bInv E11 E12 E21 E22 lbar r)
    (n : ℕ) :
    bInv n = Matrix.diagonal (ψ' (f n)) :=
  (h n).bInv_eq

/-- Extracts the displayed `w_v` equality from
`TVPrimalDualNewton.HasIntermediateAssignments`. -/
theorem HasIntermediateAssignments.w_eq
    {ι : Type u} {δ : Type v} {κ : Type w}
    [Fintype ι] [DecidableEq ι] [Fintype δ] [DecidableEq δ]
    [Fintype κ] [DecidableEq κ]
    {ψ' ψ'' : (ι → ℝ) → δ → ℝ}
    {K : Matrix κ ι ℝ} {Dx Dy Dv : Matrix δ ι ℝ} {α : ℝ} {d : κ → ℝ}
    {f : ℕ → ι → ℝ} {uDual vDual wVec : ℕ → δ → ℝ}
    {bInv E11 E12 E21 E22 : ℕ → Matrix δ δ ℝ}
    {lbar : ℕ → Matrix ι ι ℝ} {r : ℕ → ι → ℝ}
    (h : HasIntermediateAssignments
      ψ' ψ'' K Dx Dy Dv α d f uDual vDual wVec bInv E11 E12 E21 E22 lbar r)
    (n : ℕ) :
    wVec n = fun i ↦ (2 : ℝ) * ψ' (f n) i / ψ'' (f n) i :=
  (h n).w_eq

/-- Extracts the displayed `E₁₁` formula from
`TVPrimalDualNewton.HasIntermediateAssignments`. -/
theorem HasIntermediateAssignments.E11_eq
    {ι : Type u} {δ : Type v} {κ : Type w}
    [Fintype ι] [DecidableEq ι] [Fintype δ] [DecidableEq δ]
    [Fintype κ] [DecidableEq κ]
    {ψ' ψ'' : (ι → ℝ) → δ → ℝ}
    {K : Matrix κ ι ℝ} {Dx Dy Dv : Matrix δ ι ℝ} {α : ℝ} {d : κ → ℝ}
    {f : ℕ → ι → ℝ} {uDual vDual wVec : ℕ → δ → ℝ}
    {bInv E11 E12 E21 E22 : ℕ → Matrix δ δ ℝ}
    {lbar : ℕ → Matrix ι ι ℝ} {r : ℕ → ι → ℝ}
    (h : HasIntermediateAssignments
      ψ' ψ'' K Dx Dy Dv α d f uDual vDual wVec bInv E11 E12 E21 E22 lbar r)
    (n : ℕ) :
    E11 n =
      Matrix.diagonal
        (fun i ↦ wVec n i * Matrix.mulVec Dx (f n) i * uDual n i) :=
  (h n).E11_eq

/-- Extracts the displayed `E₁₂` formula from
`TVPrimalDualNewton.HasIntermediateAssignments`. -/
theorem HasIntermediateAssignments.E12_eq
    {ι : Type u} {δ : Type v} {κ : Type w}
    [Fintype ι] [DecidableEq ι] [Fintype δ] [DecidableEq δ]
    [Fintype κ] [DecidableEq κ]
    {ψ' ψ'' : (ι → ℝ) → δ → ℝ}
    {K : Matrix κ ι ℝ} {Dx Dy Dv : Matrix δ ι ℝ} {α : ℝ} {d : κ → ℝ}
    {f : ℕ → ι → ℝ} {uDual vDual wVec : ℕ → δ → ℝ}
    {bInv E11 E12 E21 E22 : ℕ → Matrix δ δ ℝ}
    {lbar : ℕ → Matrix ι ι ℝ} {r : ℕ → ι → ℝ}
    (h : HasIntermediateAssignments
      ψ' ψ'' K Dx Dy Dv α d f uDual vDual wVec bInv E11 E12 E21 E22 lbar r)
    (n : ℕ) :
    E12 n =
      Matrix.diagonal
        (fun i ↦ wVec n i * Matrix.mulVec Dy (f n) i * uDual n i) :=
  (h n).E12_eq

/-- Extracts the displayed `E₂₁` formula from
`TVPrimalDualNewton.HasIntermediateAssignments`. -/
theorem HasIntermediateAssignments.E21_eq
    {ι : Type u} {δ : Type v} {κ : Type w}
    [Fintype ι] [DecidableEq ι] [Fintype δ] [DecidableEq δ]
    [Fintype κ] [DecidableEq κ]
    {ψ' ψ'' : (ι → ℝ) → δ → ℝ}
    {K : Matrix κ ι ℝ} {Dx Dy Dv : Matrix δ ι ℝ} {α : ℝ} {d : κ → ℝ}
    {f : ℕ → ι → ℝ} {uDual vDual wVec : ℕ → δ → ℝ}
    {bInv E11 E12 E21 E22 : ℕ → Matrix δ δ ℝ}
    {lbar : ℕ → Matrix ι ι ℝ} {r : ℕ → ι → ℝ}
    (h : HasIntermediateAssignments
      ψ' ψ'' K Dx Dy Dv α d f uDual vDual wVec bInv E11 E12 E21 E22 lbar r)
    (n : ℕ) :
    E21 n =
      Matrix.diagonal
        (fun i ↦ wVec n i * Matrix.mulVec Dx (f n) i * vDual n i) :=
  (h n).E21_eq

/-- Extracts the displayed `E₂₂` formula from
`TVPrimalDualNewton.HasIntermediateAssignments`. -/
theorem HasIntermediateAssignments.E22_eq
    {ι : Type u} {δ : Type v} {κ : Type w}
    [Fintype ι] [DecidableEq ι] [Fintype δ] [DecidableEq δ]
    [Fintype κ] [DecidableEq κ]
    {ψ' ψ'' : (ι → ℝ) → δ → ℝ}
    {K : Matrix κ ι ℝ} {Dx Dy Dv : Matrix δ ι ℝ} {α : ℝ} {d : κ → ℝ}
    {f : ℕ → ι → ℝ} {uDual vDual wVec : ℕ → δ → ℝ}
    {bInv E11 E12 E21 E22 : ℕ → Matrix δ δ ℝ}
    {lbar : ℕ → Matrix ι ι ℝ} {r : ℕ → ι → ℝ}
    (h : HasIntermediateAssignments
      ψ' ψ'' K Dx Dy Dv α d f uDual vDual wVec bInv E11 E12 E21 E22 lbar r)
    (n : ℕ) :
    E22 n =
      Matrix.diagonal
        (fun i ↦ wVec n i * Matrix.mulVec Dy (f n) i * vDual n i) :=
  (h n).E22_eq

/-- Extracts the displayed `L̄_v` formula from
`TVPrimalDualNewton.HasIntermediateAssignments`. -/
theorem HasIntermediateAssignments.lbar_eq
    {ι : Type u} {δ : Type v} {κ : Type w}
    [Fintype ι] [DecidableEq ι] [Fintype δ] [DecidableEq δ]
    [Fintype κ] [DecidableEq κ]
    {ψ' ψ'' : (ι → ℝ) → δ → ℝ}
    {K : Matrix κ ι ℝ} {Dx Dy Dv : Matrix δ ι ℝ} {α : ℝ} {d : κ → ℝ}
    {f : ℕ → ι → ℝ} {uDual vDual wVec : ℕ → δ → ℝ}
    {bInv E11 E12 E21 E22 : ℕ → Matrix δ δ ℝ}
    {lbar : ℕ → Matrix ι ι ℝ} {r : ℕ → ι → ℝ}
    (h : HasIntermediateAssignments
      ψ' ψ'' K Dx Dy Dv α d f uDual vDual wVec bInv E11 E12 E21 E22 lbar r)
    (n : ℕ) :
    lbar n =
      Dxᵀ * bInv n * E11 n * Dx +
        Dxᵀ * bInv n * E12 n * Dy +
          Dyᵀ * bInv n * E21 n * Dx +
            Dvᵀ * bInv n * E22 n * Dy :=
  (h n).lbar_eq

/-- Extracts the displayed residual formula from
`TVPrimalDualNewton.HasIntermediateAssignments`. -/
theorem HasIntermediateAssignments.residual_eq
    {ι : Type u} {δ : Type v} {κ : Type w}
    [Fintype ι] [DecidableEq ι] [Fintype δ] [DecidableEq δ]
    [Fintype κ] [DecidableEq κ]
    {ψ' ψ'' : (ι → ℝ) → δ → ℝ}
    {K : Matrix κ ι ℝ} {Dx Dy Dv : Matrix δ ι ℝ} {α : ℝ} {d : κ → ℝ}
    {f : ℕ → ι → ℝ} {uDual vDual wVec : ℕ → δ → ℝ}
    {bInv E11 E12 E21 E22 : ℕ → Matrix δ δ ℝ}
    {lbar : ℕ → Matrix ι ι ℝ} {r : ℕ → ι → ℝ}
    (h : HasIntermediateAssignments
      ψ' ψ'' K Dx Dy Dv α d f uDual vDual wVec bInv E11 E12 E21 E22 lbar r)
    (n : ℕ) :
    r n =
      Matrix.mulVec Kᵀ (fun i ↦ d i - Matrix.mulVec K (f n) i) -
        Matrix.mulVec (α • (Dxᵀ * bInv n * Dx + Dyᵀ * bInv n * Dy)) (f n) :=
  (h n).residual_eq

/-- The displayed Newton-step and dual-increment assignments at iterate `n`. -/
structure NewtonAndDualIncrementsStep
    {ι : Type u} {δ : Type v} {κ : Type w}
    [Fintype ι] [DecidableEq ι] [Fintype δ] [DecidableEq δ]
    [Fintype κ] [DecidableEq κ]
    (K : Matrix κ ι ℝ) (Dx Dy : Matrix δ ι ℝ) (α : ℝ)
    (f : ℕ → ι → ℝ) (uDual : ℕ → δ → ℝ)
    (bInv E11 E12 E21 E22 : ℕ → Matrix δ δ ℝ)
    (lbar : ℕ → Matrix ι ι ℝ) (r deltaF : ℕ → ι → ℝ)
    (deltaU deltaV : ℕ → δ → ℝ) (n : ℕ) : Prop where
  deltaF_eq : deltaF n = Matrix.mulVec ((Kᵀ * K + α • lbar n)⁻¹) (r n)
  deltaU_eq :
    deltaU n =
      -uDual n +
        Matrix.mulVec (bInv n)
          (Matrix.mulVec Dx (f n) +
            Matrix.mulVec (E11 n * Dx + E12 n * Dy) (deltaF n))
  deltaV_eq :
    deltaV n =
      -uDual n +
        Matrix.mulVec (bInv n)
          (Matrix.mulVec Dy (f n) +
            Matrix.mulVec (E21 n * Dx + E22 n * Dy) (deltaF n))

set_option linter.defProp false in
/-- Builds the iterate-`n` Newton-step and dual-increment clause from the three
displayed equalities. -/
def NewtonAndDualIncrementsStep.ofEq
    {ι : Type u} {δ : Type v} {κ : Type w}
    [Fintype ι] [DecidableEq ι] [Fintype δ] [DecidableEq δ]
    [Fintype κ] [DecidableEq κ]
    (K : Matrix κ ι ℝ) (Dx Dy : Matrix δ ι ℝ) (α : ℝ)
    (f : ℕ → ι → ℝ) (uDual : ℕ → δ → ℝ)
    (bInv E11 E12 E21 E22 : ℕ → Matrix δ δ ℝ)
    (lbar : ℕ → Matrix ι ι ℝ) (r deltaF : ℕ → ι → ℝ)
    (deltaU deltaV : ℕ → δ → ℝ) (n : ℕ)
    (h_deltaF : deltaF n = Matrix.mulVec ((Kᵀ * K + α • lbar n)⁻¹) (r n))
    (h_deltaU :
      deltaU n =
        -uDual n +
          Matrix.mulVec (bInv n)
            (Matrix.mulVec Dx (f n) +
              Matrix.mulVec (E11 n * Dx + E12 n * Dy) (deltaF n)))
    (h_deltaV :
      deltaV n =
        -uDual n +
          Matrix.mulVec (bInv n)
            (Matrix.mulVec Dy (f n) +
              Matrix.mulVec (E21 n * Dx + E22 n * Dy) (deltaF n))) :
    NewtonAndDualIncrementsStep
      K Dx Dy α f uDual bInv E11 E12 E21 E22 lbar r deltaF deltaU deltaV n :=
  { deltaF_eq := h_deltaF, deltaU_eq := h_deltaU, deltaV_eq := h_deltaV }

/-- Algorithm 8.2.4 (3). The displayed Newton-step and dual-increment formulas
hold at every iterate. -/
abbrev HasNewtonAndDualIncrements
    {ι : Type u} {δ : Type v} {κ : Type w}
    [Fintype ι] [DecidableEq ι] [Fintype δ] [DecidableEq δ]
    [Fintype κ] [DecidableEq κ]
    (K : Matrix κ ι ℝ) (Dx Dy : Matrix δ ι ℝ) (α : ℝ)
    (f : ℕ → ι → ℝ) (uDual : ℕ → δ → ℝ)
    (bInv E11 E12 E21 E22 : ℕ → Matrix δ δ ℝ)
    (lbar : ℕ → Matrix ι ι ℝ) (r deltaF : ℕ → ι → ℝ)
    (deltaU deltaV : ℕ → δ → ℝ) : Prop :=
  ∀ n : ℕ,
    NewtonAndDualIncrementsStep
      K Dx Dy α f uDual bInv E11 E12 E21 E22 lbar r deltaF deltaU deltaV n

/-- Extracts the displayed Newton-step equality from
`TVPrimalDualNewton.HasNewtonAndDualIncrements`. -/
theorem HasNewtonAndDualIncrements.deltaF_eq
    {ι : Type u} {δ : Type v} {κ : Type w}
    [Fintype ι] [DecidableEq ι] [Fintype δ] [DecidableEq δ]
    [Fintype κ] [DecidableEq κ]
    {K : Matrix κ ι ℝ} {Dx Dy : Matrix δ ι ℝ} {α : ℝ}
    {f : ℕ → ι → ℝ} {uDual : ℕ → δ → ℝ}
    {bInv E11 E12 E21 E22 : ℕ → Matrix δ δ ℝ}
    {lbar : ℕ → Matrix ι ι ℝ} {r deltaF : ℕ → ι → ℝ}
    {deltaU deltaV : ℕ → δ → ℝ}
    (h : HasNewtonAndDualIncrements
      K Dx Dy α f uDual bInv E11 E12 E21 E22 lbar r deltaF deltaU deltaV)
    (n : ℕ) :
    deltaF n = Matrix.mulVec ((Kᵀ * K + α • lbar n)⁻¹) (r n) :=
  (h n).deltaF_eq

/-- Extracts the displayed `Δu` equality from
`TVPrimalDualNewton.HasNewtonAndDualIncrements`. -/
theorem HasNewtonAndDualIncrements.deltaU_eq
    {ι : Type u} {δ : Type v} {κ : Type w}
    [Fintype ι] [DecidableEq ι] [Fintype δ] [DecidableEq δ]
    [Fintype κ] [DecidableEq κ]
    {K : Matrix κ ι ℝ} {Dx Dy : Matrix δ ι ℝ} {α : ℝ}
    {f : ℕ → ι → ℝ} {uDual : ℕ → δ → ℝ}
    {bInv E11 E12 E21 E22 : ℕ → Matrix δ δ ℝ}
    {lbar : ℕ → Matrix ι ι ℝ} {r deltaF : ℕ → ι → ℝ}
    {deltaU deltaV : ℕ → δ → ℝ}
    (h : HasNewtonAndDualIncrements
      K Dx Dy α f uDual bInv E11 E12 E21 E22 lbar r deltaF deltaU deltaV)
    (n : ℕ) :
    deltaU n =
      -uDual n +
        Matrix.mulVec (bInv n)
          (Matrix.mulVec Dx (f n) +
            Matrix.mulVec (E11 n * Dx + E12 n * Dy) (deltaF n)) :=
  (h n).deltaU_eq

/-- Extracts the displayed `Δv` equality from
`TVPrimalDualNewton.HasNewtonAndDualIncrements`. -/
theorem HasNewtonAndDualIncrements.deltaV_eq
    {ι : Type u} {δ : Type v} {κ : Type w}
    [Fintype ι] [DecidableEq ι] [Fintype δ] [DecidableEq δ]
    [Fintype κ] [DecidableEq κ]
    {K : Matrix κ ι ℝ} {Dx Dy : Matrix δ ι ℝ} {α : ℝ}
    {f : ℕ → ι → ℝ} {uDual : ℕ → δ → ℝ}
    {bInv E11 E12 E21 E22 : ℕ → Matrix δ δ ℝ}
    {lbar : ℕ → Matrix ι ι ℝ} {r deltaF : ℕ → ι → ℝ}
    {deltaU deltaV : ℕ → δ → ℝ}
    (h : HasNewtonAndDualIncrements
      K Dx Dy α f uDual bInv E11 E12 E21 E22 lbar r deltaF deltaU deltaV)
    (n : ℕ) :
    deltaV n =
      -uDual n +
        Matrix.mulVec (bInv n)
          (Matrix.mulVec Dy (f n) +
            Matrix.mulVec (E21 n * Dx + E22 n * Dy) (deltaF n)) :=
  (h n).deltaV_eq

/-- The displayed primal update, maximal feasible-step, and dual updates at
iterate `n`. -/
structure PrimalDualUpdateStep
    {ι : Type u} {δ : Type v}
    (f : ℕ → ι → ℝ) (uDual vDual : ℕ → δ → ℝ)
    (deltaF : ℕ → ι → ℝ) (deltaU deltaV : ℕ → δ → ℝ)
    (τ : ℕ → ℝ) (𝒞star : Set ((δ → ℝ) × (δ → ℝ))) (n : ℕ) : Prop where
  primal_eq : f (n + 1) = f n + deltaF n
  feasibleStep :
    IsGreatest
      {t : ℝ |
        0 ≤ t ∧ t ≤ 1 ∧
          (uDual n + t • deltaU n, vDual n + t • deltaV n) ∈ 𝒞star}
      (τ n)
  u_update_eq : uDual (n + 1) = uDual n + τ n • deltaU n
  v_update_eq : vDual (n + 1) = vDual n + τ n • deltaV n

set_option linter.defProp false in
/-- Builds the iterate-`n` primal-dual update clause from the four displayed
conditions. -/
def PrimalDualUpdateStep.ofEq
    {ι : Type u} {δ : Type v}
    (f : ℕ → ι → ℝ) (uDual vDual : ℕ → δ → ℝ)
    (deltaF : ℕ → ι → ℝ) (deltaU deltaV : ℕ → δ → ℝ)
    (τ : ℕ → ℝ) (𝒞star : Set ((δ → ℝ) × (δ → ℝ))) (n : ℕ)
    (h_primal : f (n + 1) = f n + deltaF n)
    (h_feasible :
      IsGreatest
        {t : ℝ |
          0 ≤ t ∧ t ≤ 1 ∧
            (uDual n + t • deltaU n, vDual n + t • deltaV n) ∈ 𝒞star}
        (τ n))
    (h_uUpdate : uDual (n + 1) = uDual n + τ n • deltaU n)
    (h_vUpdate : vDual (n + 1) = vDual n + τ n • deltaV n) :
    PrimalDualUpdateStep f uDual vDual deltaF deltaU deltaV τ 𝒞star n :=
  { primal_eq := h_primal
    feasibleStep := h_feasible
    u_update_eq := h_uUpdate
    v_update_eq := h_vUpdate }

/-- Algorithm 8.2.4 (4). The displayed primal update, maximal feasible step,
and dual updates hold at every iterate. -/
abbrev HasPrimalDualUpdate
    {ι : Type u} {δ : Type v}
    (f : ℕ → ι → ℝ) (uDual vDual : ℕ → δ → ℝ)
    (deltaF : ℕ → ι → ℝ) (deltaU deltaV : ℕ → δ → ℝ)
    (τ : ℕ → ℝ) (𝒞star : Set ((δ → ℝ) × (δ → ℝ))) : Prop :=
  ∀ n : ℕ, PrimalDualUpdateStep f uDual vDual deltaF deltaU deltaV τ 𝒞star n

/-- Extracts the displayed primal update equality from
`TVPrimalDualNewton.HasPrimalDualUpdate`. -/
theorem HasPrimalDualUpdate.primal_eq
    {ι : Type u} {δ : Type v}
    {f : ℕ → ι → ℝ} {uDual vDual : ℕ → δ → ℝ}
    {deltaF : ℕ → ι → ℝ} {deltaU deltaV : ℕ → δ → ℝ}
    {τ : ℕ → ℝ} {𝒞star : Set ((δ → ℝ) × (δ → ℝ))}
    (h : HasPrimalDualUpdate f uDual vDual deltaF deltaU deltaV τ 𝒞star)
    (n : ℕ) :
    f (n + 1) = f n + deltaF n :=
  (h n).primal_eq

/-- Extracts the maximal feasible-step clause from
`TVPrimalDualNewton.HasPrimalDualUpdate`. -/
theorem HasPrimalDualUpdate.feasibleStep
    {ι : Type u} {δ : Type v}
    {f : ℕ → ι → ℝ} {uDual vDual : ℕ → δ → ℝ}
    {deltaF : ℕ → ι → ℝ} {deltaU deltaV : ℕ → δ → ℝ}
    {τ : ℕ → ℝ} {𝒞star : Set ((δ → ℝ) × (δ → ℝ))}
    (h : HasPrimalDualUpdate f uDual vDual deltaF deltaU deltaV τ 𝒞star)
    (n : ℕ) :
    IsGreatest
      {t : ℝ |
        0 ≤ t ∧ t ≤ 1 ∧
          (uDual n + t • deltaU n, vDual n + t • deltaV n) ∈ 𝒞star}
      (τ n) :=
  (h n).feasibleStep

/-- Helper for Algorithm 8.2.4: the maximal step `τ_v` is itself a feasible
trial step. -/
theorem HasPrimalDualUpdate.tau_mem_feasibleSet
    {ι : Type u} {δ : Type v}
    {f : ℕ → ι → ℝ} {uDual vDual : ℕ → δ → ℝ}
    {deltaF : ℕ → ι → ℝ} {deltaU deltaV : ℕ → δ → ℝ}
    {τ : ℕ → ℝ} {𝒞star : Set ((δ → ℝ) × (δ → ℝ))}
    (h : HasPrimalDualUpdate f uDual vDual deltaF deltaU deltaV τ 𝒞star)
    (n : ℕ) :
    0 ≤ τ n ∧ τ n ≤ 1 ∧
      (uDual n + τ n • deltaU n, vDual n + τ n • deltaV n) ∈ 𝒞star := by
  -- The greatest feasible step belongs to the feasible set it maximizes.
  exact (HasPrimalDualUpdate.feasibleStep h n).1

/-- Helper for Algorithm 8.2.4: the maximal feasible step satisfies the lower
interval bound from the source formula. -/
theorem HasPrimalDualUpdate.tau_nonneg
    {ι : Type u} {δ : Type v}
    {f : ℕ → ι → ℝ} {uDual vDual : ℕ → δ → ℝ}
    {deltaF : ℕ → ι → ℝ} {deltaU deltaV : ℕ → δ → ℝ}
    {τ : ℕ → ℝ} {𝒞star : Set ((δ → ℝ) × (δ → ℝ))}
    (h : HasPrimalDualUpdate f uDual vDual deltaF deltaU deltaV τ 𝒞star)
    (n : ℕ) :
    0 ≤ τ n := by
  -- The lower bound is the first component of the feasible-membership proof.
  exact (HasPrimalDualUpdate.tau_mem_feasibleSet h n).1

/-- Helper for Algorithm 8.2.4: the maximal feasible step satisfies the upper
interval bound from the source formula. -/
theorem HasPrimalDualUpdate.tau_le_one
    {ι : Type u} {δ : Type v}
    {f : ℕ → ι → ℝ} {uDual vDual : ℕ → δ → ℝ}
    {deltaF : ℕ → ι → ℝ} {deltaU deltaV : ℕ → δ → ℝ}
    {τ : ℕ → ℝ} {𝒞star : Set ((δ → ℝ) × (δ → ℝ))}
    (h : HasPrimalDualUpdate f uDual vDual deltaF deltaU deltaV τ 𝒞star)
    (n : ℕ) :
    τ n ≤ 1 := by
  -- The upper bound is the second component of the feasible-membership proof.
  exact (HasPrimalDualUpdate.tau_mem_feasibleSet h n).2.1

/-- Helper for Algorithm 8.2.4: every feasible trial step is bounded above by
the maximal feasible step `τ_v`. -/
theorem HasPrimalDualUpdate.le_tau_of_mem_feasibleSet
    {ι : Type u} {δ : Type v}
    {f : ℕ → ι → ℝ} {uDual vDual : ℕ → δ → ℝ}
    {deltaF : ℕ → ι → ℝ} {deltaU deltaV : ℕ → δ → ℝ}
    {τ : ℕ → ℝ} {𝒞star : Set ((δ → ℝ) × (δ → ℝ))}
    (h : HasPrimalDualUpdate f uDual vDual deltaF deltaU deltaV τ 𝒞star)
    (n : ℕ) {t : ℝ}
    (ht :
      0 ≤ t ∧ t ≤ 1 ∧
        (uDual n + t • deltaU n, vDual n + t • deltaV n) ∈ 𝒞star) :
    t ≤ τ n := by
  -- The `IsGreatest` witness makes `τ n` an upper bound for every feasible step.
  exact (HasPrimalDualUpdate.feasibleStep h n).2 ht

/-- Extracts the displayed first dual-update equality from
`TVPrimalDualNewton.HasPrimalDualUpdate`. -/
theorem HasPrimalDualUpdate.u_update_eq
    {ι : Type u} {δ : Type v}
    {f : ℕ → ι → ℝ} {uDual vDual : ℕ → δ → ℝ}
    {deltaF : ℕ → ι → ℝ} {deltaU deltaV : ℕ → δ → ℝ}
    {τ : ℕ → ℝ} {𝒞star : Set ((δ → ℝ) × (δ → ℝ))}
    (h : HasPrimalDualUpdate f uDual vDual deltaF deltaU deltaV τ 𝒞star)
    (n : ℕ) :
    uDual (n + 1) = uDual n + τ n • deltaU n :=
  (h n).u_update_eq

/-- Extracts the displayed second dual-update equality from
`TVPrimalDualNewton.HasPrimalDualUpdate`. -/
theorem HasPrimalDualUpdate.v_update_eq
    {ι : Type u} {δ : Type v}
    {f : ℕ → ι → ℝ} {uDual vDual : ℕ → δ → ℝ}
    {deltaF : ℕ → ι → ℝ} {deltaU deltaV : ℕ → δ → ℝ}
    {τ : ℕ → ℝ} {𝒞star : Set ((δ → ℝ) × (δ → ℝ))}
    (h : HasPrimalDualUpdate f uDual vDual deltaF deltaU deltaV τ 𝒞star)
    (n : ℕ) :
    vDual (n + 1) = vDual n + τ n • deltaV n :=
  (h n).v_update_eq

end TVPrimalDualNewton
