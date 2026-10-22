/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import OptimizationTheoryAndMethods_SunYuan_2006.Chap01.Theorem_1_4_4
import OptimizationTheoryAndMethods_SunYuan_2006.Chap03.Theorem_3_2_2
import OptimizationTheoryAndMethods_SunYuan_2006.Chap03.Definition_3_5_1
import OptimizationTheoryAndMethods_SunYuan_2006.Chap05.Theorem_5_4_4
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Convex.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Data.Matrix.Mul
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.ToLin

noncomputable section

open scoped Matrix.Norms.L2Operator

section Chapter05Assumption542

variable {n : ℕ}

local notation "Point" => EuclideanSpace ℝ (Fin n)
local notation "MatrixN" => Matrix (Fin n) (Fin n) ℝ

-- Semantic recall: `lean_leansearch` surfaced `IsLocalMin`, `StrongConvexOn`, and
-- `ContDiffAt.exists_lipschitzOnWith`, but no canonical owner for the source's strong
-- local-minimizer plus Hessian-Lipschitz assumption package. The item is therefore stated
-- directly with a quadratic-growth predicate and the canonical Hessian of `f`.

/-- A point `xStar` is a strong local minimizer of `f` on `D` when `f` has quadratic growth
above `f xStar` on some ball about `xStar` contained in `D`. -/
def IsStrongLocalMinOn (f : Point → ℝ) (D : Set Point) (xStar : Point) : Prop :=
  ∃ c > 0, ∃ ε > 0,
    Metric.ball xStar ε ⊆ D ∧
      ∀ x, x ∈ Metric.ball xStar ε →
        f xStar + c * ‖x - xStar‖ ^ (2 : ℕ) ≤ f x

/-- Unfolding formula for `IsStrongLocalMinOn`. -/
theorem isStrongLocalMinOn_iff
    (f : Point → ℝ) (D : Set Point) (xStar : Point) :
    IsStrongLocalMinOn f D xStar ↔
      ∃ c > 0, ∃ ε > 0,
        Metric.ball xStar ε ⊆ D ∧
          ∀ x, x ∈ Metric.ball xStar ε →
            f xStar + c * ‖x - xStar‖ ^ (2 : ℕ) ≤ f x := Iff.rfl

namespace IsStrongLocalMinOn

/-- A strong local minimizer on `D` lies in `D`. -/
theorem mem
    {f : Point → ℝ} {D : Set Point} {xStar : Point}
    (h : IsStrongLocalMinOn f D xStar) :
    xStar ∈ D := by
  rcases h with ⟨_, _, ε, hε, hball, _⟩
  exact hball <| by simpa [Metric.mem_ball] using hε

/-- The quadratic-growth owner `IsStrongLocalMinOn f D xStar` implies the canonical local
minimizer owner `IsLocalMin f xStar`. -/
theorem isLocalMin
    {f : Point → ℝ} {D : Set Point} {xStar : Point}
    (h : IsStrongLocalMinOn f D xStar) :
    IsLocalMin f xStar := by
  rcases h with ⟨c, hc, ε, hε, _, hbound⟩
  change {x | f xStar ≤ f x} ∈ nhds xStar
  refine Filter.mem_of_superset (Metric.ball_mem_nhds xStar hε) ?_
  intro x hx
  have hnonneg : 0 ≤ c * ‖x - xStar‖ ^ (2 : ℕ) := by
    positivity
  have hle : f xStar ≤ f xStar + c * ‖x - xStar‖ ^ (2 : ℕ) := by
    linarith
  exact le_trans hle (hbound x hx)

end IsStrongLocalMinOn

/-- The Chapter 5 Hessian matrix surface for `f` at `x`, obtained by expressing the Chapter 3
operator Hessian owner `hessianAt f x` in the Euclidean matrix basis. This is a bridge/view,
retaining the Chapter 5 name used downstream in the quasi-Newton section. -/
noncomputable abbrev quasiNewtonHessianMatrix (f : Point → ℝ) (x : Point) : MatrixN :=
  (Matrix.toEuclideanCLM : MatrixN ≃⋆ₐ[ℝ] Point →L[ℝ] Point).symm (hessianAt f x)

/-- `quasiNewtonHessianMatrix` is the Euclidean matrix representation of `hessianAt`. -/
theorem quasiNewtonHessianMatrix_eq
    (f : Point → ℝ) (x : Point) :
    quasiNewtonHessianMatrix f x =
      (Matrix.toEuclideanCLM : MatrixN ≃⋆ₐ[ℝ] Point →L[ℝ] Point).symm (hessianAt f x) :=
  rfl

/-- Converting `quasiNewtonHessianMatrix` back to a linear map recovers the Chapter 3 Hessian
owner `hessianAt`. -/
theorem toEuclideanCLM_quasiNewtonHessianMatrix
    (f : Point → ℝ) (x : Point) :
    (Matrix.toEuclideanCLM : MatrixN ≃⋆ₐ[ℝ] Point →L[ℝ] Point)
        (quasiNewtonHessianMatrix f x) =
      hessianAt f x := by
  simp [quasiNewtonHessianMatrix, hessianAt]

/-- Chapter05 Assumption 5.4.2: `f : ℝ^n → ℝ` is twice continuously differentiable on an open
convex set `D`, there is a distinguished point `xStar` that is a strong local minimizer of `f`
on `D`, the canonical Hessian matrix `quasiNewtonHessianMatrix f xStar` is positive definite,
hence symmetric, and on some neighborhood `Metric.ball xStar ε ⊆ D` this Hessian matrix field
is `γ`-Lipschitz for a nonnegative Lipschitz constant `γ`. -/
structure HasQuasiNewtonStrongLocalMinimizerAssumptions
    (D : Set Point) (f : Point → ℝ) where
  open_domain : IsOpen D
  convex_domain : Convex ℝ D
  contDiffOn : ContDiffOn ℝ 2 f D
  xStar : Point
  strong_local_min : IsStrongLocalMinOn f D xStar
  xStar_hessian_posDef : (quasiNewtonHessianMatrix f xStar).PosDef
  ε : ℝ
  ε_pos : 0 < ε
  ball_subset_domain : Metric.ball xStar ε ⊆ D
  γ : NNReal
  hessian_lipschitz (x xBar : Point)
      (hx : x ∈ Metric.ball xStar ε)
      (hxBar : xBar ∈ Metric.ball xStar ε) :
      ‖quasiNewtonHessianMatrix f xBar - quasiNewtonHessianMatrix f x‖ ≤ γ * ‖xBar - x‖

namespace HasQuasiNewtonStrongLocalMinimizerAssumptions

/-- The distinguished strong local minimizer in Assumption 5.4.2 lies in the domain `D`. -/
theorem xStar_mem
    {D : Set Point} {f : Point → ℝ}
    (h : HasQuasiNewtonStrongLocalMinimizerAssumptions D f) :
    h.xStar ∈ D :=
  h.strong_local_min.mem

/-- The Chapter 5 strong-local-minimizer owner supplies differentiability of `f` at the
distinguished point `xStar`. -/
theorem differentiableAt_xStar
    {D : Set Point} {f : Point → ℝ}
    (h : HasQuasiNewtonStrongLocalMinimizerAssumptions D f) :
    DifferentiableAt ℝ f h.xStar :=
  (h.contDiffOn.contDiffAt (h.open_domain.mem_nhds h.xStar_mem)).differentiableAt (by norm_num)

/-- The distinguished point in Assumption 5.4.2 is stationary for `f`. This is the owner-level
Chapter 5 bridge to the canonical first-order necessary condition from Chapter 1. -/
theorem gradient_eq_zero
    {D : Set Point} {f : Point → ℝ}
    (h : HasQuasiNewtonStrongLocalMinimizerAssumptions D f) :
    gradient f h.xStar = 0 :=
  (isStationaryPoint_of_isLocalMin f h.xStar h.differentiableAt_xStar
    h.strong_local_min.isLocalMin).gradient_eq_zero

/-- Positive definiteness in Assumption 5.4.2 implies the source's symmetry clause for the
Hessian at `xStar`. -/
theorem xStar_hessian_symm
    {D : Set Point} {f : Point → ℝ}
    (h : HasQuasiNewtonStrongLocalMinimizerAssumptions D f) :
    (quasiNewtonHessianMatrix f h.xStar).IsSymm := by
  simpa using h.xStar_hessian_posDef.isHermitian

/-- The Hessian Lipschitz constant in Assumption 5.4.2 is nonnegative. -/
theorem gamma_nonneg
    {D : Set Point} {f : Point → ℝ}
    (h : HasQuasiNewtonStrongLocalMinimizerAssumptions D f) :
    0 ≤ (h.γ : ℝ) :=
  h.γ.2

/-- The Assumption 5.4.2 owner canonically supplies the weaker scaled quasi-Newton local
assumptions for `gradient f`. -/
def toHasScaledQuasiNewtonLocalAssumptions
    {D : Set Point} {f : Point → ℝ}
    (h : HasQuasiNewtonStrongLocalMinimizerAssumptions D f) :
    HasScaledQuasiNewtonLocalAssumptions D (gradient f) where
  open_domain := h.open_domain
  convex_domain := h.convex_domain
  contDiffOn := by
    sorry
  xStar := h.xStar
  xStar_mem := h.xStar_mem
  fderiv_isInvertible := by
    sorry
  gamma := h.γ
  lipschitz_fderiv := by
    sorry

/-- Assumption 5.4.2 supplies the Chapter 3 canonical local Hessian owner
`HasLocalLipschitzHessianMatrixAt` for the Chapter 5 Hessian surface
`quasiNewtonHessianMatrix`. -/
theorem hasLocalLipschitzHessianMatrixAt
    {D : Set Point} {f : Point → ℝ}
    (h : HasQuasiNewtonStrongLocalMinimizerAssumptions D f) :
    HasLocalLipschitzHessianMatrixAt f (quasiNewtonHessianMatrix f) h.xStar := by
  refine ⟨h.ε, h.ε_pos, ?_, h.γ, h.gamma_nonneg, ?_⟩
  · intro x hx
    sorry
  · intro x xBar hx hxBar
    simpa using h.hessian_lipschitz xBar x hxBar hx

/-- Source-semantic expansion of `HasQuasiNewtonStrongLocalMinimizerAssumptions D f`. -/
theorem spec
    {D : Set Point} {f : Point → ℝ}
    (h : HasQuasiNewtonStrongLocalMinimizerAssumptions D f) :
    IsOpen D ∧
      Convex ℝ D ∧
      ContDiffOn ℝ 2 f D ∧
      h.xStar ∈ D ∧
      IsStrongLocalMinOn f D h.xStar ∧
      (quasiNewtonHessianMatrix f h.xStar).PosDef ∧
      0 < h.ε ∧
      Metric.ball h.xStar h.ε ⊆ D ∧
      0 ≤ (h.γ : ℝ) ∧
      ∀ x xBar,
        x ∈ Metric.ball h.xStar h.ε →
        xBar ∈ Metric.ball h.xStar h.ε →
        ‖quasiNewtonHessianMatrix f xBar - quasiNewtonHessianMatrix f x‖ ≤
          h.γ * ‖xBar - x‖ := by
  exact ⟨h.open_domain, h.convex_domain, h.contDiffOn, h.xStar_mem, h.strong_local_min,
    h.xStar_hessian_posDef, h.ε_pos, h.ball_subset_domain, h.gamma_nonneg,
    h.hessian_lipschitz⟩

/-- Membership in `HasQuasiNewtonStrongLocalMinimizerAssumptions D f` is membership in the
ambient domain `D`. -/
instance instMembershipPointHasQuasiNewtonStrongLocalMinimizerAssumptions
    {D : Set Point} {f : Point → ℝ} :
    Membership Point (HasQuasiNewtonStrongLocalMinimizerAssumptions D f) where
  mem _ x := x ∈ D

/-- Membership in `h : HasQuasiNewtonStrongLocalMinimizerAssumptions D f` is exactly
membership in the domain `D`. -/
@[simp] theorem mem_iff
    {D : Set Point} {f : Point → ℝ}
    (h : HasQuasiNewtonStrongLocalMinimizerAssumptions D f) (x : Point) :
    x ∈ h ↔ x ∈ D :=
  Iff.rfl

@[simp] theorem mem_xStar
    {D : Set Point} {f : Point → ℝ}
    (h : HasQuasiNewtonStrongLocalMinimizerAssumptions D f) :
    h.xStar ∈ h :=
  h.xStar_mem

/-- The distinguished local minimizer `xStar` from Chapter05 Assumption 5.4.2, viewed as a
point of `D`. -/
def xStarInDomain
    {D : Set Point} {f : Point → ℝ}
    (h : HasQuasiNewtonStrongLocalMinimizerAssumptions D f) : D :=
  ⟨h.xStar, h.xStar_mem⟩

@[simp] theorem coe_xStarInDomain
    {D : Set Point} {f : Point → ℝ}
    (h : HasQuasiNewtonStrongLocalMinimizerAssumptions D f) :
    ((xStarInDomain h : D) : Point) = h.xStar :=
  rfl

@[simp] theorem xStarInDomain_mem
    {D : Set Point} {f : Point → ℝ}
    (h : HasQuasiNewtonStrongLocalMinimizerAssumptions D f) :
    (xStarInDomain h : Point) ∈ D :=
  h.xStar_mem

end HasQuasiNewtonStrongLocalMinimizerAssumptions

end Chapter05Assumption542
