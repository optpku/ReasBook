/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import OptimizationTheoryAndMethods_SunYuan_2006.Chap01.Definition_1_2_3
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.Matrix.Basis
import Mathlib.Analysis.Normed.Lp.PiLp
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.Mul
import Mathlib.Topology.MetricSpace.Lipschitz

open Set
open Matrix
open scoped BigOperators

universe u v

noncomputable section

-- Domain sampling:
-- * primary domain: first-order finite-difference error bounds for maps between real normed spaces
-- * sampled owner declarations:
--   `holderRemainderBound`,
--   `quadraticRemainderBound_of_fderiv_lipschitzOn`,
--   `linearizationError_le_lipschitz_maxDistance`,
--   `jacobianMatrix_eq_gateauxDerivativeMatrix`
-- * core/canonical owner in the project: `quadraticRemainderBound_of_fderiv_lipschitzOn`
-- * source-facing item here: the Jacobian-column error estimate in chosen bases
-- * bridge/view items here: the intrinsic directional estimate and the `ℓ₁` matrix-norm corollary

/-- The forward finite-difference Jacobian matrix with common scalar step `h`. -/
def finiteDifferenceJacobianMatrix
    {X : Type u} {Y : Type v} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] {n m : ℕ}
    (e : Module.Basis (Fin n) ℝ X) (u : Module.Basis (Fin m) ℝ Y)
    (F : X → Y) (x : X) (h : ℝ) : Matrix (Fin m) (Fin n) ℝ :=
  u.toMatrix fun j ↦ h⁻¹ • (F (x + h • e j) - F x)

/-- The Jacobian matrix of `F` at `x` in the chosen bases `e` and `u`. -/
def jacobianMatrixAt
    {X : Type u} {Y : Type v} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] {n m : ℕ}
    (e : Module.Basis (Fin n) ℝ X) (u : Module.Basis (Fin m) ℝ Y)
    (F : X → Y) (x : X) : Matrix (Fin m) (Fin n) ℝ :=
  LinearMap.toMatrix e u (fderiv ℝ F x).toLinearMap

section Theorem341

variable {n m : ℕ}

local notation "L1Point" => WithLp (1 : ENNReal) (Fin n → ℝ)
local notation "L1Value" => WithLp (1 : ENNReal) (Fin m → ℝ)
local notation "l1PointBasis" => PiLp.basisFun (1 : ENNReal) ℝ (Fin n)
local notation "l1ValueBasis" => PiLp.basisFun (1 : ENNReal) ℝ (Fin m)

/-- Helper for Chapter03 Theorem 3.4.1: a Lipschitz bound on `fderiv ℝ F` along a convex segment
gives the standard quadratic first-order remainder estimate. -/
lemma quadraticRemainderBoundAlongSegment_of_fderiv_lipschitzOn
    {X : Type u} {Y : Type v}
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (D : Set X)
    (F : X → Y)
    (x d : X)
    (γ : NNReal)
    (hD_open : IsOpen D)
    (hD_convex : Convex ℝ D)
    (hx : x ∈ D)
    (hF : DifferentiableOn ℝ F D)
    (hLip : LipschitzOnWith γ (fderiv ℝ F) D)
    (hxd : x + d ∈ D) :
    ‖F (x + d) - F x - fderiv ℝ F x d‖ ≤ ((γ : ℝ) / 2) * ‖d‖ ^ 2 := by
  let line : ℝ → X := fun t ↦ x + t • d
  let remainder : ℝ → Y := fun t ↦ F (line t) - F x - t • fderiv ℝ F x d
  let remainderDeriv : ℝ → Y := fun t ↦ (fderiv ℝ F (line t) - fderiv ℝ F x) d
  let barrier : ℝ → ℝ := fun t ↦ (((γ : ℝ) * ‖d‖ ^ 2) / 2) * t ^ (2 : ℕ)
  let barrierDeriv : ℝ → ℝ := fun t ↦ ((γ : ℝ) * ‖d‖ ^ 2) * t
  have hline_mem : ∀ t ∈ Set.Icc (0 : ℝ) 1, line t ∈ D := by
    intro t ht
    simpa [line, add_comm, AffineMap.lineMap_apply_module'] using hD_convex.add_smul_mem hx hxd ht
  have hline_cont : ContinuousOn line (Set.Icc (0 : ℝ) 1) := by
    intro t ht
    simpa [line] using
      ((((hasDerivAt_id t).smul_const d).const_add x).continuousAt.continuousWithinAt)
  have hcont : ContinuousOn remainder (Set.Icc (0 : ℝ) 1) := by
    have hcomp : ContinuousOn (fun t : ℝ ↦ F (line t)) (Set.Icc (0 : ℝ) 1) :=
      hF.continuousOn.comp hline_cont hline_mem
    have hlin : ContinuousOn (fun t : ℝ ↦ t • fderiv ℝ F x d) (Set.Icc (0 : ℝ) 1) := by
      fun_prop
    exact hcomp.sub continuousOn_const |>.sub hlin
  have hderiv :
      ∀ t ∈ Set.Ico (0 : ℝ) 1, HasDerivWithinAt remainder (remainderDeriv t) (Set.Ici t) t := by
    intro t ht
    have hz : line t ∈ D := hline_mem t ⟨ht.1, ht.2.le⟩
    have hFline : HasFDerivAt F (fderivWithin ℝ F D (line t)) (line t) := by
      exact (hF (line t) hz).hasFDerivWithinAt.hasFDerivAt (hD_open.mem_nhds hz)
    have hline' : HasDerivAt line d t := by
      simpa [line] using (((hasDerivAt_id t).smul_const d).const_add x)
    have hcomp : HasDerivAt (F ∘ line) (fderiv ℝ F (line t) d) t := by
      have hcomp' := hFline.comp_hasDerivAt t hline'
      simpa [Function.comp, line, fderivWithin_of_isOpen hD_open hz] using hcomp'
    have hlin : HasDerivAt (fun s : ℝ ↦ s • fderiv ℝ F x d) (fderiv ℝ F x d) t := by
      simpa using (hasDerivAt_id t).smul_const (fderiv ℝ F x d)
    have hrem : HasDerivAt remainder (remainderDeriv t) t := by
      have hrem' := (hcomp.sub_const (F x)).sub hlin
      convert hrem' using 1
      · funext s
        simp [remainder, Function.comp, sub_eq_add_neg]
      · simp [remainderDeriv, sub_eq_add_neg]
    exact hrem.hasDerivWithinAt
  have hbarrier : ∀ t, HasDerivAt barrier (barrierDeriv t) t := by
    intro t
    have hpow := (hasDerivAt_id t).mul (hasDerivAt_id t)
    have hbarrier' := hpow.const_mul ((((γ : ℝ) * ‖d‖ ^ 2) / 2))
    have hbarrier'' : HasDerivAt barrier ((((γ : ℝ) * ‖d‖ ^ 2) / 2) * (t + t)) t := by
      simpa [Pi.mul_apply, barrier, pow_two, mul_assoc, mul_left_comm, mul_comm] using hbarrier'
    convert hbarrier'' using 1
    ring
  have hbound : ∀ t ∈ Set.Ico (0 : ℝ) 1, ‖remainderDeriv t‖ ≤ barrierDeriv t := by
    intro t ht
    have hz : line t ∈ D := hline_mem t ⟨ht.1, ht.2.le⟩
    have hdist_line : dist (line t) x = t * ‖d‖ := by
      simp [line, dist_eq_norm, norm_smul, Real.norm_of_nonneg ht.1, sub_eq_add_neg, add_assoc]
    have hdist :
        ‖fderiv ℝ F (line t) - fderiv ℝ F x‖ ≤ (γ : ℝ) * (t * ‖d‖) := by
      have hdist' : dist (fderiv ℝ F (line t)) (fderiv ℝ F x) ≤ (γ : ℝ) * dist (line t) x := by
        simpa using hLip.dist_le_mul (x := line t) (y := x) hz hx
      have hdist'' : ‖fderiv ℝ F (line t) - fderiv ℝ F x‖ ≤ (γ : ℝ) * dist (line t) x := by
        simpa [dist_eq_norm] using hdist'
      rw [hdist_line] at hdist''
      exact hdist''
    calc
      ‖remainderDeriv t‖ = ‖(fderiv ℝ F (line t) - fderiv ℝ F x) d‖ := rfl
      _ ≤ ‖fderiv ℝ F (line t) - fderiv ℝ F x‖ * ‖d‖ := by
            exact ContinuousLinearMap.le_opNorm _ _
      _ ≤ ((γ : ℝ) * (t * ‖d‖)) * ‖d‖ := by
            exact mul_le_mul_of_nonneg_right hdist (norm_nonneg d)
      _ = barrierDeriv t := by
            simp [barrierDeriv, pow_two, mul_left_comm, mul_comm]
  have hmain :=
    image_norm_le_of_norm_deriv_right_le_deriv_boundary
      (f := remainder) (f' := remainderDeriv) (a := 0) (b := 1)
      hcont hderiv (by simp [remainder, line, barrier]) hbarrier hbound
  have hfinal : ‖F (x + d) - F x - fderiv ℝ F x d‖ ≤ ((γ : ℝ) * ‖d‖ ^ 2) / 2 := by
    simpa [remainder, line, barrier] using
      hmain (show (1 : ℝ) ∈ Set.Icc (0 : ℝ) 1 by simp)
  simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hfinal

/-- Helper for Chapter03 Theorem 3.4.1: the intrinsic forward-difference error along the basis
direction `e j` is controlled by the quadratic remainder estimate from Chapter 1. -/
lemma directionalFiniteDifferenceErrorBound
    {X : Type u} {Y : Type v}
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (e : Module.Basis (Fin n) ℝ X)
    (D : Set X)
    (F : X → Y)
    (x : X)
    (h : ℝ)
    (γ : NNReal)
    (j : Fin n)
    (hD_open : IsOpen D)
    (hD_convex : Convex ℝ D)
    (hx : x ∈ D)
    (hF : DifferentiableOn ℝ F D)
    (hLip : LipschitzOnWith γ (fderiv ℝ F) D)
    (hunit : ‖e j‖ = 1)
    (hstep : x + h • e j ∈ D)
    (hh : h ≠ 0) :
    ‖h⁻¹ • (F (x + h • e j) - F x) - fderiv ℝ F x (e j)‖ ≤ ((γ : ℝ) / 2) * |h| := by
  let d := h • e j
  let error := h⁻¹ • (F (x + h • e j) - F x) - fderiv ℝ F x (e j)
  -- Start from the Chapter 1 quadratic remainder bound with the single-coordinate step `h • e j`.
  have hquadratic :=
    quadraticRemainderBoundAlongSegment_of_fderiv_lipschitzOn
      D F x d γ hD_open hD_convex hx hF hLip (by simpa [d] using hstep)
  have habs : 0 < |h| := abs_pos.mpr hh
  have hstepNorm : ‖h • e j‖ = |h| := by
    simp [norm_smul, hunit]
  have hfactor :
      F (x + h • e j) - F x - fderiv ℝ F x (h • e j) = h • error := by
    -- Factor one power of `h` out of the remainder so the quadratic bound becomes linear in `|h|`.
    dsimp [error]
    symm
    calc
      h • (h⁻¹ • (F (x + h • e j) - F x) - fderiv ℝ F x (e j))
          = h • (h⁻¹ • (F (x + h • e j) - F x)) - h • fderiv ℝ F x (e j) := by
              rw [smul_sub]
      _ = (h * h⁻¹) • (F (x + h • e j) - F x) - h • fderiv ℝ F x (e j) := by
            rw [smul_smul]
      _ = F (x + h • e j) - F x - h • fderiv ℝ F x (e j) := by
            rw [mul_inv_cancel₀ hh, one_smul]
      _ = F (x + h • e j) - F x - fderiv ℝ F x (h • e j) := by
            rw [map_smul]
  have hscaled :
      ‖error‖ * |h| ≤ (((γ : ℝ) / 2) * |h|) * |h| := by
    -- Rewrite the quadratic estimate into a form where the positive factor `|h|` cancels.
    have hnormsq : ‖d‖ ^ 2 = h * h := by
      change ‖h • e j‖ ^ 2 = h * h
      simp [norm_smul, hunit, Real.norm_eq_abs, pow_two]
    have hquadraticNorm : ‖F (x + d) - F x - fderiv ℝ F x d‖ ≤ ((γ : ℝ) / 2) * (h * h) := by
      calc
        ‖F (x + d) - F x - fderiv ℝ F x d‖ ≤ ((γ : ℝ) / 2) * ‖d‖ ^ 2 := hquadratic
        _ = ((γ : ℝ) / 2) * (h * h) := by rw [hnormsq]
    have hleft : ‖F (x + d) - F x - fderiv ℝ F x d‖ = |h| * ‖error‖ := by
      simpa [d, hfactor, norm_smul, Real.norm_eq_abs, mul_comm] using congrArg norm hfactor
    have hquadratic' : |h| * ‖error‖ ≤ ((γ : ℝ) / 2) * (h * h) := by
      rw [← hleft]
      exact hquadraticNorm
    have hsquare : h * h = |h| * |h| := by
      nlinarith [sq_abs h]
    convert hquadratic' using 1
    · ring
    · rw [hsquare]
      ring
  exact le_of_mul_le_mul_right hscaled habs

/-- Helper for Chapter03 Theorem 3.4.1: the `j`-th coordinate column of the finite-difference
Jacobian error reconstructs the intrinsic directional finite-difference error. -/
lemma finiteDifferenceJacobianErrorColumn_eq_directional
    {X : Type u} {Y : Type v}
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (e : Module.Basis (Fin n) ℝ X)
    (u : Module.Basis (Fin m) ℝ Y)
    (F : X → Y)
    (x : X)
    (h : ℝ)
    (j : Fin n) :
    u.equivFun.symm
        ((finiteDifferenceJacobianMatrix e u F x h - jacobianMatrixAt e u F x).col j) =
      h⁻¹ • (F (x + h • e j) - F x) - fderiv ℝ F x (e j) := by
  -- Compare both vectors through their coordinates in the codomain basis `u`.
  apply u.equivFun.injective
  ext i
  simp [finiteDifferenceJacobianMatrix, jacobianMatrixAt, u.toMatrix_apply,
    LinearMap.toMatrix_apply, Matrix.sub_apply, Matrix.col_apply, u.equivFun_symm_apply,
    Finsupp.single_apply]

/-- Helper for Chapter03 Theorem 3.4.1: reconstructing a coordinate vector through
`PiLp.basisFun (1 : ENNReal) ℝ (Fin m)` preserves the public `ℓ₁` norm. -/
lemma piLpBasisFunEquivFunSymm_norm_eq_l1Norm
    (c : Fin m → ℝ) :
    ‖(PiLp.basisFun (1 : ENNReal) ℝ (Fin m)).equivFun.symm c‖ = ‖c‖₁ := by
  -- Move from the `WithLp 1` carrier back to the coordinate formula for the `ℓ₁` norm.
  simpa [PiLp.basisFun_equivFun, WithLp.coe_symm_linearEquiv, _root_.l1Norm_eq_sum_abs,
    Real.norm_eq_abs] using
    (PiLp.norm_eq_of_L1 (WithLp.toLp (1 : ENNReal) c))

/-- Chapter03 Theorem 3.4.1 (1): for `F : X → Y` on real normed spaces with chosen bases `e`
and `u`, if `fderiv ℝ F` is `γ`-Lipschitz on the open convex set `D`, then the `j`-th column of
the forward finite-difference Jacobian error, read back in the codomain basis `u`, has norm at
most `((γ : ℝ) / 2) * |h|` whenever `‖e j‖ = 1`. -/
theorem finiteDifferenceJacobianColumnError_le
    {X : Type u} {Y : Type v}
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (e : Module.Basis (Fin n) ℝ X)
    (u : Module.Basis (Fin m) ℝ Y)
    (D : Set X)
    (F : X → Y)
    (x : X)
    (h : ℝ)
    (γ : NNReal)
    (j : Fin n)
    (hD_open : IsOpen D)
    (hD_convex : Convex ℝ D)
    (hx : x ∈ D)
    (hF : DifferentiableOn ℝ F D)
    (hLip : LipschitzOnWith γ (fderiv ℝ F) D)
    (hunit : ‖e j‖ = 1)
    (hstep : x + h • e j ∈ D)
    (hh : h ≠ 0) :
    ‖u.equivFun.symm
        ((finiteDifferenceJacobianMatrix e u F x h - jacobianMatrixAt e u F x).col j)‖ ≤
      ((γ : ℝ) / 2) * |h| := by
  -- Rewrite the coordinate column back to the intrinsic forward-difference error.
  rw [finiteDifferenceJacobianErrorColumn_eq_directional]
  -- The remaining bound is exactly the intrinsic directional estimate.
  exact
    directionalFiniteDifferenceErrorBound
      e D F x h γ j hD_open hD_convex hx hF hLip hunit hstep hh

/-- Intrinsic directional bridge for Chapter03 Theorem 3.4.1 (1): the source-facing Jacobian
column estimate is the basis-free directional finite-difference error along `e j`. -/
theorem finiteDifferenceDirectionalError_le
    {X : Type u} {Y : Type v}
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (e : Module.Basis (Fin n) ℝ X)
    (D : Set X)
    (F : X → Y)
    (x : X)
    (h : ℝ)
    (γ : NNReal)
    (j : Fin n)
    (hD_open : IsOpen D)
    (hD_convex : Convex ℝ D)
    (hx : x ∈ D)
    (hF : DifferentiableOn ℝ F D)
    (hLip : LipschitzOnWith γ (fderiv ℝ F) D)
    (hunit : ‖e j‖ = 1)
    (hstep : x + h • e j ∈ D)
    (hh : h ≠ 0) :
    ‖h⁻¹ • (F (x + h • e j) - F x) - fderiv ℝ F x (e j)‖ ≤ ((γ : ℝ) / 2) * |h| := by
  -- Reuse the intrinsic estimate directly instead of re-running the scaling algebra.
  exact
    directionalFiniteDifferenceErrorBound
      e D F x h γ j hD_open hD_convex hx hF hLip hunit hstep hh

/-- Chapter03 Theorem 3.4.1 (2): for the `ℓ₁` specialization
`F : L1Point = WithLp 1 (Fin n → ℝ) → L1Value = WithLp 1 (Fin m → ℝ)`, if the derivative is
`γ`-Lipschitz in the ambient `ℓ₁` geometry and every coordinate step stays in `D`, then the
forward finite-difference Jacobian error satisfies
`‖A - J(x)‖₁ ≤ ((γ : ℝ) / 2) * |h|`. -/
theorem matrixOneNorm_finiteDifferenceJacobianError_le
    (D : Set L1Point)
    (F : L1Point → L1Value)
    (x : L1Point)
    (h : ℝ)
    (γ : NNReal)
    (hD_open : IsOpen D)
    (hD_convex : Convex ℝ D)
    (hx : x ∈ D)
    (hF : DifferentiableOn ℝ F D)
    (hLip : LipschitzOnWith γ (fderiv ℝ F) D)
    (hstep : ∀ j : Fin n, x + h • l1PointBasis j ∈ D)
    (hh : h ≠ 0) :
    ‖(finiteDifferenceJacobianMatrix
        l1PointBasis
        l1ValueBasis
        F x h -
      jacobianMatrixAt
        l1PointBasis
        l1ValueBasis
        F x)‖₁ ≤
      ((γ : ℝ) / 2) * |h| := by
  let E :=
    finiteDifferenceJacobianMatrix l1PointBasis l1ValueBasis F x h -
      jacobianMatrixAt l1PointBasis l1ValueBasis F x
  have hbasisUnit : ∀ j : Fin n, ‖l1PointBasis j‖ = 1 := by
    intro j
    -- The `ℓ₁` basis vector has exactly one nonzero coordinate of size `1`.
    simp [PiLp.basisFun_apply]
  have hrow : ∀ j : Fin n, ‖(E.transpose).row j‖₁ ≤ ((γ : ℝ) / 2) * |h| := by
    intro j
    -- Specialize the column estimate to the `WithLp 1` bases.
    have hcol :=
      finiteDifferenceJacobianColumnError_le
        l1PointBasis l1ValueBasis D F x h γ j
        hD_open hD_convex hx hF hLip (hbasisUnit j) (hstep j) hh
    -- Convert the codomain-basis norm in the column theorem to the public `ℓ₁` row norm.
    rw [piLpBasisFunEquivFunSymm_norm_eq_l1Norm] at hcol
    have hrowEq : (E.transpose).row j = E.col j := by
      ext i
      simp [E, Matrix.row_apply, Matrix.col_apply, Matrix.transpose_apply, Matrix.sub_apply]
    simpa [hrowEq] using hcol
  -- Transport the rowwise `ℓ₁` control on `Eᵀ` to the matrix `ℓ₁` norm of `E`.
  rw [matrixOneNorm_eq_matrixInfinityNorm_transpose]
  exact
    matrixInfinityNorm_le_of_rowVectorOneNorm_le
      E.transpose (((γ : ℝ) / 2) * |h|) (by positivity) hrow

end Theorem341
