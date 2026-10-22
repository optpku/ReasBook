/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import Mathlib
import FirstOrderMethodsOptimization_Beck_2017.Chap06.Definition_6_3
import FirstOrderMethodsOptimization_Beck_2017.Chap06.Example_6_8
import FirstOrderMethodsOptimization_Beck_2017.Chap06.Proposition_6_2_3
import FirstOrderMethodsOptimization_Beck_2017.Chap15.Algorithm_15_7

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u v

section

open scoped RealInnerProductSpace
open scoped SoftThreshold

variable {ι : Type u} {κ : Type v}
variable [Fintype ι] [Fintype κ]

local notation "X" => EuclideanSpace ℝ ι
local notation "Y" => EuclideanSpace ℝ κ

/- Semantic search note: `lean_leansearch` is unavailable in this runner, and `prompt_add/` is
absent in this workspace, so the owner choice is sampled from the sibling API-design philosophy
and the nearby explicit recursive algorithm files.

This item is `source-facing`: Algorithm 15.9 gives concrete update formulas for the five iterates
`x^k`, `z^k`, `w^k`, `y₁^k`, and `y₂^k`. Sampling the nearby owner layer in
`Algorithm_15_7`, `Algorithm_15_2`, and `Definition_6_3` shows that the primitive public data
here should be:
- the Chapter 15 owner `admm_sum_composition_v2_x_update` for the resolvent `x`-step;
  this owner lives on `ContinuousLinearMap`, so the matrix-style `LinearMap` input is used there
  through `A.toContinuousLinearMap`;
- the Chapter 15 owner `admm_multiplier_update` for the two affine dual recursions;
- the Chapter 6 owner `T_[·]` for the soft-thresholding `w`-step;
The only genuinely new source-specific public data are therefore the explicit `z`-average together
with the five iterate sequences themselves. A deterministic internal state recursion is acceptable
only as implementation scaffolding for those public sequences, since no proximal-choice ambiguity
remains. Since the thresholding steps are genuinely pointwise, the natural owner layer is the
canonical finite Euclidean product `EuclideanSpace ℝ ι`/`EuclideanSpace ℝ κ`; the matrix
specialization is a downstream view obtained from `Matrix.toEuclideanLin`, not the main API. -/

private structure IterateState (X' Y' : Type*) where
  x : X'
  z : Y'
  w : X'
  y1 : Y'
  y2 : X'

private def initialState
    (x0 : X) (z0 : Y) (w0 : X) (y10 : Y) (y20 : X) : IterateState X Y :=
  { x := x0
    z := z0
    w := w0
    y1 := y10
    y2 := y20 }

/-- The explicit `z`-update
`z^(k+1) = (ρ A x^(k+1) + y₁^k + b) / (ρ + 1)`. -/
def l1_regularized_least_squares_admm_v2_z_update
    (A : X →ₗ[ℝ] Y) (b : Y) (ρ : PosReal)
    (xNext : X) (y1k : Y) : Y :=
  (1 / ((ρ : ℝ) + 1)) • ((ρ : ℝ) • A xNext + y1k + b)

-- Proof sketch: unfold `l1_regularized_least_squares_admm_v2_z_update`; the body is the
-- displayed affine average formula for `z^(k+1)`.
/-- Expanding the `z`-update yields the explicit affine formula
`(ρ A x^(k+1) + y₁^k + b) / (ρ + 1)`. -/
@[simp] theorem l1_regularized_least_squares_admm_v2_z_update_eq
    (A : X →ₗ[ℝ] Y) (b : Y) (ρ : PosReal)
    (xNext : X) (y1k : Y) :
    l1_regularized_least_squares_admm_v2_z_update A b ρ xNext y1k =
      (1 / ((ρ : ℝ) + 1)) • ((ρ : ℝ) • A xNext + y1k + b) :=
  rfl

/-- The explicit threshold update
`w^(k+1) = T_[λ / ρ] (x^(k+1) + (1 / ρ) y₂^k)`. -/
def l1_regularized_least_squares_admm_v2_w_update
    (ρ : PosReal) (lam : ℝ) (xNext y2k : X) : X :=
  T_[lam / (ρ : ℝ)] (xNext + (1 / (ρ : ℝ)) • y2k)

-- Proof sketch: unfold `l1_regularized_least_squares_admm_v2_w_update`; the right-hand side is
-- definitionally the displayed thresholded formula for `w^(k+1)`.
/-- Expanding the `w`-update yields the thresholded formula
`T_[λ / ρ] (x^(k+1) + (1 / ρ) y₂^k)`. -/
@[simp] theorem l1_regularized_least_squares_admm_v2_w_update_eq
    (ρ : PosReal) (lam : ℝ) (xNext y2k : X) :
    l1_regularized_least_squares_admm_v2_w_update ρ lam xNext y2k =
      T_[lam / (ρ : ℝ)] (xNext + (1 / (ρ : ℝ)) • y2k) :=
  rfl

/-- Under `0 ≤ λ`, the explicit soft-thresholding step in Algorithm 15.9 is the corresponding
proximal update for the `ℓ¹` regularizer. -/
theorem l1_regularized_least_squares_admm_v2_w_update_mem_prox
    (ρ : PosReal) (lam : ℝ) (hlam : 0 ≤ lam) (xNext y2k : X) :
    l1_regularized_least_squares_admm_v2_w_update ρ lam xNext y2k ∈
      prox[((((1 / ρ : PosReal) : EReal) •
        (fun x : X ↦ ((lam * ‖x‖₁ : ℝ) : EReal))))]
        (xNext + (1 / (ρ : ℝ)) • y2k) := by
  have hscaled :
      ((((1 / ρ : PosReal) : EReal) •
        (fun x : X ↦ ((lam * ‖x‖₁ : ℝ) : EReal)))) =
          fun x : X ↦ (((lam / (ρ : ℝ)) * ‖x‖₁ : ℝ) : EReal) := by
    funext x
    simp [Pi.smul_apply, smul_eq_mul, EReal.coe_mul, div_eq_mul_inv]
    ac_rfl
  have hprox :=
    prox_euclidean_l1_eq_singleton_softThreshold
      (div_nonneg hlam ρ.2.le) (xNext + (1 / (ρ : ℝ)) • y2k)
  rw [l1_regularized_least_squares_admm_v2_w_update_eq, hscaled, hprox]
  simp

/-- The explicit affine-average step in Algorithm 15.9 is the corresponding proximal update for
the least-squares block. -/
theorem l1_regularized_least_squares_admm_v2_z_update_mem_prox
    (A : X →ₗ[ℝ] Y) (b : Y) (ρ : PosReal) (xNext : X) (y1k : Y) :
    l1_regularized_least_squares_admm_v2_z_update A b ρ xNext y1k ∈
      prox[((((1 / ρ : PosReal) : EReal) •
        (fun z : Y ↦ ((((1 / 2 : ℝ) * ‖z - b‖ ^ (2 : ℕ) : ℝ)) : EReal))))]
        (A xNext + (1 / (ρ : ℝ)) • y1k) := by
  classical
  let Aρ : Matrix κ κ ℝ := ((ρ : ℝ)⁻¹) • 1
  let c : Y := -((ρ : ℝ)⁻¹) • b
  let g : Y → EReal :=
    fun z : Y ↦ (((1 / 2 : ℝ) * ⟪Aρ.toEuclideanLin z, z⟫ + ⟪c, z⟫ : ℝ) : EReal)
  let d : ℝ := (1 / (2 * (ρ : ℝ))) * ‖b‖ ^ (2 : ℕ)
  have hρ_nonneg : 0 ≤ (ρ : ℝ)⁻¹ := (inv_pos.mpr ρ.2).le
  have hpsd : Aρ.PosSemidef := by
    simpa [Aρ] using
      (Matrix.PosDef.one : Matrix.PosDef (1 : Matrix κ κ ℝ)).posSemidef.smul hρ_nonneg
  have hscaled_fun :
      ((((1 / ρ : PosReal) : EReal) •
        (fun z : Y ↦ ((((1 / 2 : ℝ) * ‖z - b‖ ^ (2 : ℕ) : ℝ)) : EReal)))) =
          fun z : Y ↦ g z + (d : EReal) := by
    have hAρ_apply (z : Y) : Aρ.toEuclideanLin z = (ρ : ℝ)⁻¹ • z := by
      ext i
      change ((Aρ.mulVec z.ofLp) i = (((ρ : ℝ)⁻¹ • z).ofLp i))
      simp [Aρ, Matrix.smul_mulVec, Matrix.one_mulVec]
    funext z
    have hinner : ⟪Aρ.toEuclideanLin z, z⟫ = (ρ : ℝ)⁻¹ * ‖z‖ ^ (2 : ℕ) := by
      rw [hAρ_apply z, real_inner_smul_left, real_inner_self_eq_norm_sq]
    have hreal :
        ((ρ : ℝ)⁻¹ * ((1 / 2 : ℝ) * ‖z - b‖ ^ (2 : ℕ))) =
          (1 / 2 : ℝ) * ⟪Aρ.toEuclideanLin z, z⟫ + ⟪c, z⟫ + d := by
      rw [hinner]
      simp [c, d, norm_sub_sq_real, real_inner_smul_right, real_inner_comm]
      ring
    simp only [g, PosReal.coe_div, PosReal.coe_one, one_div, EReal.coe_mul, EReal.coe_pow,
      Pi.smul_apply, smul_eq_mul]
    norm_num
    exact_mod_cast hreal
  have hprox_const := congrFun (prox_add_const g d) (A xNext + (1 / (ρ : ℝ)) • y1k)
  have hprox_g :
      prox[g] (A xNext + (1 / (ρ : ℝ)) • y1k) =
        prox[((((1 / ρ : PosReal) : EReal) •
          (fun z : Y ↦ ((((1 / 2 : ℝ) * ‖z - b‖ ^ (2 : ℕ) : ℝ)) : EReal))))]
          (A xNext + (1 / (ρ : ℝ)) • y1k) := by
    rw [← hscaled_fun] at hprox_const
    simpa using hprox_const.symm
  have hquad :
      prox[g] (A xNext + (1 / (ρ : ℝ)) • y1k) =
        {((Aρ + 1)⁻¹).toEuclideanLin (A xNext + (1 / (ρ : ℝ)) • y1k - c)} := by
    simpa [g] using
      prox_quadratic_affine_function_eq_singleton
        Aρ hpsd c (A xNext + (1 / (ρ : ℝ)) • y1k)
  have hcenter :
      ((Aρ + 1)⁻¹).toEuclideanLin (A xNext + (1 / (ρ : ℝ)) • y1k - c) =
        l1_regularized_least_squares_admm_v2_z_update A b ρ xNext y1k := by
    have hAρ_add : Aρ + 1 = (((ρ : ℝ)⁻¹ + 1 : ℝ) • (1 : Matrix κ κ ℝ)) := by
      ext i j
      by_cases hij : i = j <;> simp [Aρ, hij]
    rw [hAρ_add, l1_regularized_least_squares_admm_v2_z_update_eq]
    have hρ0 : (ρ : ℝ) ≠ 0 := ρ.2.ne'
    have hkinv : 0 < ((ρ : ℝ)⁻¹) := inv_pos.mpr ρ.2
    have hkpos : 0 < (((ρ : ℝ)⁻¹ + 1 : ℝ)) := by linarith
    have hk : (((ρ : ℝ)⁻¹ + 1 : ℝ)) ≠ 0 := hkpos.ne'
    let _ := invertibleOfNonzero hk
    ext i
    change ((((((ρ : ℝ)⁻¹ + 1 : ℝ) • (1 : Matrix κ κ ℝ))⁻¹).mulVec
        (A xNext + (1 / (ρ : ℝ)) • y1k - c).ofLp) i =
      (((1 / ((ρ : ℝ) + 1)) • ((ρ : ℝ) • A xNext + y1k + b)).ofLp i))
    have hinv : ((((ρ : ℝ)⁻¹ + 1 : ℝ) • (1 : Matrix κ κ ℝ))⁻¹) =
        ((((ρ : ℝ)⁻¹ + 1 : ℝ)⁻¹) • (1 : Matrix κ κ ℝ)) := by
      simp [Matrix.inv_smul]
    rw [hinv, Matrix.smul_mulVec]
    simp [c, Matrix.one_mulVec]
    field_simp [hρ0]
    ring
  rw [← hprox_g, hquad, hcenter]
  simp

private def stateUpdate
    (A : X →ₗ[ℝ] Y) (b : Y) (lam : ℝ) (ρ : PosReal)
    (state : IterateState X Y) : IterateState X Y :=
  let xNext :=
    admm_sum_composition_v2_x_update ρ A.toContinuousLinearMap state.z state.y1 state.w
      state.y2
  let zNext := l1_regularized_least_squares_admm_v2_z_update A b ρ xNext state.y1
  let wNext := l1_regularized_least_squares_admm_v2_w_update ρ lam xNext state.y2
  { x := xNext
    z := zNext
    w := wNext
    y1 := admm_multiplier_update ρ A (-LinearMap.id) 0 state.y1 xNext zNext
    y2 :=
      admm_multiplier_update
        ρ
        (LinearMap.id : X →ₗ[ℝ] X)
        (-LinearMap.id)
        0
        state.y2
        xNext
        wNext }

private def iterateState
    (A : X →ₗ[ℝ] Y) (b : Y) (lam : ℝ) (ρ : PosReal)
    (x0 : X) (z0 : Y) (w0 : X) (y10 : Y) (y20 : X) :
    ℕ → IterateState X Y
  | 0 => initialState x0 z0 w0 y10 y20
  | k + 1 => stateUpdate A b lam ρ (iterateState A b lam ρ x0 z0 w0 y10 y20 k)

/-- Algorithm 15.9 (1) `x`-iterate sequence for the `ℓ¹`-regularized least-squares split
problem. -/
def l1_regularized_least_squares_admm_v2_x
    (A : X →ₗ[ℝ] Y) (b : Y) (lam : ℝ) (ρ : PosReal)
    (x0 : X) (z0 : Y) (w0 : X) (y10 : Y) (y20 : X) :
    ℕ → X :=
  fun k ↦ (iterateState A b lam ρ x0 z0 w0 y10 y20 k).x

/-- Algorithm 15.9 (2) `z`-iterate sequence for the `ℓ¹`-regularized least-squares split
problem. -/
def l1_regularized_least_squares_admm_v2_z
    (A : X →ₗ[ℝ] Y) (b : Y) (lam : ℝ) (ρ : PosReal)
    (x0 : X) (z0 : Y) (w0 : X) (y10 : Y) (y20 : X) :
    ℕ → Y :=
  fun k ↦ (iterateState A b lam ρ x0 z0 w0 y10 y20 k).z

/-- Algorithm 15.9 (3) threshold iterate sequence `w^k` for the `ℓ¹`-regularized least-squares
split problem. -/
def l1_regularized_least_squares_admm_v2_w
    (A : X →ₗ[ℝ] Y) (b : Y) (lam : ℝ) (ρ : PosReal)
    (x0 : X) (z0 : Y) (w0 : X) (y10 : Y) (y20 : X) :
    ℕ → X :=
  fun k ↦ (iterateState A b lam ρ x0 z0 w0 y10 y20 k).w

/-- Algorithm 15.9 (4) first dual-block sequence `y₁^k` for the `ℓ¹`-regularized least-squares
split problem. -/
def l1_regularized_least_squares_admm_v2_y1
    (A : X →ₗ[ℝ] Y) (b : Y) (lam : ℝ) (ρ : PosReal)
    (x0 : X) (z0 : Y) (w0 : X) (y10 : Y) (y20 : X) :
    ℕ → Y :=
  fun k ↦ (iterateState A b lam ρ x0 z0 w0 y10 y20 k).y1

/-- Algorithm 15.9 (5) second dual-block sequence `y₂^k` for the `ℓ¹`-regularized least-squares
split problem. -/
def l1_regularized_least_squares_admm_v2_y2
    (A : X →ₗ[ℝ] Y) (b : Y) (lam : ℝ) (ρ : PosReal)
    (x0 : X) (z0 : Y) (w0 : X) (y10 : Y) (y20 : X) :
    ℕ → X :=
  fun k ↦ (iterateState A b lam ρ x0 z0 w0 y10 y20 k).y2

section

variable (A : X →ₗ[ℝ] Y) (b : Y) (lam : ℝ) (ρ : PosReal)
variable (x0 : X) (z0 : Y) (w0 : X) (y10 : Y) (y20 : X)

local notation "x[" k "]" =>
  (l1_regularized_least_squares_admm_v2_x A b lam ρ x0 z0 w0 y10 y20 k : X)
local notation "z[" k "]" =>
  (l1_regularized_least_squares_admm_v2_z A b lam ρ x0 z0 w0 y10 y20 k : Y)
local notation "w[" k "]" =>
  (l1_regularized_least_squares_admm_v2_w A b lam ρ x0 z0 w0 y10 y20 k : X)
local notation "y1[" k "]" =>
  (l1_regularized_least_squares_admm_v2_y1 A b lam ρ x0 z0 w0 y10 y20 k : Y)
local notation "y2[" k "]" =>
  (l1_regularized_least_squares_admm_v2_y2 A b lam ρ x0 z0 w0 y10 y20 k : X)
local notation "f1" =>
  (fun x : X ↦ ((lam * ‖x‖₁ : ℝ) : EReal))
local notation "f2" =>
  (fun z : Y ↦ ((((1 / 2 : ℝ) * ‖z - b‖ ^ (2 : ℕ) : ℝ)) : EReal))

/-- The `x`-iterate sequence starts at the prescribed initial point `x⁰ = x0`. -/
theorem l1_regularized_least_squares_admm_v2_x_zero :
    x[0] = x0 := rfl

/-- The `z`-iterate sequence starts at the prescribed initial point `z⁰ = z0`. -/
theorem l1_regularized_least_squares_admm_v2_z_zero :
    z[0] = z0 := rfl

/-- The threshold iterate sequence starts at the prescribed initial point `w⁰ = w0`. -/
theorem l1_regularized_least_squares_admm_v2_w_zero :
    w[0] = w0 := rfl

/-- The first dual-block sequence starts at the prescribed initial point `y₁⁰ = y10`. -/
theorem l1_regularized_least_squares_admm_v2_y1_zero :
    y1[0] = y10 := rfl

/-- The second dual-block sequence starts at the prescribed initial point `y₂⁰ = y20`. -/
theorem l1_regularized_least_squares_admm_v2_y2_zero :
    y2[0] = y20 := rfl

/-- At every iteration `k`, the next `x`-iterate is given by the explicit linear solve. -/
theorem l1_regularized_least_squares_admm_v2_x_succ (k : ℕ) :
    x[k + 1] =
      admm_sum_composition_v2_x_update
        ρ A.toContinuousLinearMap z[k] y1[k] w[k] y2[k] := rfl

/-- At every iteration `k`, the next `z`-iterate is given by the affine average formula. -/
theorem l1_regularized_least_squares_admm_v2_z_succ (k : ℕ) :
    z[k + 1] = l1_regularized_least_squares_admm_v2_z_update A b ρ x[k + 1] y1[k] := rfl

/-- At every iteration `k`, the next `w`-iterate is given by the soft-thresholding formula. -/
theorem l1_regularized_least_squares_admm_v2_w_succ (k : ℕ) :
    w[k + 1] = l1_regularized_least_squares_admm_v2_w_update ρ lam x[k + 1] y2[k] := rfl

/-- At every iteration `k`, the first dual block is obtained by the canonical ADMM affine
multiplier update specialized to `A x - z = 0`. -/
theorem l1_regularized_least_squares_admm_v2_y1_step (k : ℕ) :
    l1_regularized_least_squares_admm_v2_y1 A b lam ρ x0 z0 w0 y10 y20 (k + 1) =
      admm_multiplier_update
        ρ
        (A : X →ₗ[ℝ] Y)
        (-LinearMap.id : Y →ₗ[ℝ] Y)
        (0 : Y)
        (l1_regularized_least_squares_admm_v2_y1 A b lam ρ x0 z0 w0 y10 y20 k : Y)
        (l1_regularized_least_squares_admm_v2_x A b lam ρ x0 z0 w0 y10 y20 (k + 1) : X)
        (l1_regularized_least_squares_admm_v2_z A b lam ρ x0 z0 w0 y10 y20 (k + 1) : Y) :=
  rfl

/-- At every iteration `k`, the first dual block satisfies the affine recursion
`y₁^(k+1) = y₁^k + ρ (A x^(k+1) - z^(k+1))`. -/
theorem l1_regularized_least_squares_admm_v2_y1_succ (k : ℕ) :
    y1[k + 1] = y1[k] + (ρ : ℝ) • (A x[k + 1] - z[k + 1]) :=
  by
    simpa [admm_multiplier_update, sub_eq_add_neg] using
      l1_regularized_least_squares_admm_v2_y1_step k

/-- At every iteration `k`, the second dual block is obtained by the canonical ADMM affine
multiplier update specialized to `x - w = 0`. -/
theorem l1_regularized_least_squares_admm_v2_y2_step (k : ℕ) :
    l1_regularized_least_squares_admm_v2_y2 A b lam ρ x0 z0 w0 y10 y20 (k + 1) =
      admm_multiplier_update
        ρ
        (LinearMap.id : X →ₗ[ℝ] X)
        (-LinearMap.id)
        0
        (l1_regularized_least_squares_admm_v2_y2 A b lam ρ x0 z0 w0 y10 y20 k)
        (l1_regularized_least_squares_admm_v2_x A b lam ρ x0 z0 w0 y10 y20 (k + 1))
        (l1_regularized_least_squares_admm_v2_w A b lam ρ x0 z0 w0 y10 y20 (k + 1)) :=
  rfl

/-- At every iteration `k`, the second dual block satisfies the affine recursion
`y₂^(k+1) = y₂^k + ρ (x^(k+1) - w^(k+1))`. -/
theorem l1_regularized_least_squares_admm_v2_y2_succ (k : ℕ) :
    y2[k + 1] = y2[k] + (ρ : ℝ) • (x[k + 1] - w[k + 1]) := rfl

set_option linter.unusedVariables false in
/-- Under `0 ≤ λ`, the explicit iterates form the canonical Chapter 15 ADMM-version-2 trajectory
for the `ℓ¹`/least-squares specialization. -/
theorem l1_regularized_least_squares_admm_v2_isADMMSumCompositionTrajectoryV2
    (hlam : 0 ≤ lam) :
    IsADMMSumCompositionTrajectoryV2
      ρ f1 f2 A.toContinuousLinearMap
      (l1_regularized_least_squares_admm_v2_x A b lam ρ x0 z0 w0 y10 y20)
      (l1_regularized_least_squares_admm_v2_w A b lam ρ x0 z0 w0 y10 y20)
      (l1_regularized_least_squares_admm_v2_y2 A b lam ρ x0 z0 w0 y10 y20)
      (l1_regularized_least_squares_admm_v2_z A b lam ρ x0 z0 w0 y10 y20)
      (l1_regularized_least_squares_admm_v2_y1 A b lam ρ x0 z0 w0 y10 y20)
      x0 w0 y20 z0 y10 :=
  { x_zero := l1_regularized_least_squares_admm_v2_x_zero A b lam ρ x0 z0 w0 y10 y20
    w_zero := l1_regularized_least_squares_admm_v2_w_zero A b lam ρ x0 z0 w0 y10 y20
    y2_zero := l1_regularized_least_squares_admm_v2_y2_zero A b lam ρ x0 z0 w0 y10 y20
    z_zero := l1_regularized_least_squares_admm_v2_z_zero A b lam ρ x0 z0 w0 y10 y20
    y1_zero := l1_regularized_least_squares_admm_v2_y1_zero A b lam ρ x0 z0 w0 y10 y20
    x_step := fun k ↦ l1_regularized_least_squares_admm_v2_x_succ A b lam ρ x0 z0 w0 y10 y20 k
    z_step := fun k ↦
      l1_regularized_least_squares_admm_v2_z_update_mem_prox A b ρ x[k + 1] y1[k]
    w_step := fun k ↦
      l1_regularized_least_squares_admm_v2_w_update_mem_prox ρ lam hlam x[k + 1] y2[k]
    y1_step := fun k ↦ l1_regularized_least_squares_admm_v2_y1_succ A b lam ρ x0 z0 w0 y10 y20 k
    y2_step := fun k ↦ l1_regularized_least_squares_admm_v2_y2_succ A b lam ρ x0 z0 w0 y10 y20 k }

end

end
