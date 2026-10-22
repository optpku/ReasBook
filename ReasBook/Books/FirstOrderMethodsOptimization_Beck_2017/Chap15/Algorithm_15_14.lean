/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import FirstOrderMethodsOptimization_Beck_2017.Chap02.Definition_2_2
import FirstOrderMethodsOptimization_Beck_2017.Chap06.Example_6_53
import FirstOrderMethodsOptimization_Beck_2017.Chap06.Theorem_6_25
import FirstOrderMethodsOptimization_Beck_2017.Chap15.Algorithm_15_10

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open scoped SoftThreshold

universe u v

section

variable {Y : Type u} {ι : Type v}
variable [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [FiniteDimensional ℝ Y]
variable [Fintype ι]

local notation "E" => EuclideanSpace ℝ ι

/- Algorithm 15.14 is `source-facing`: it keeps only the basis-pursuit specialization of the
Algorithm 15.10 AD-LPMM recursion, namely the fixed branch `z^k = b` and the resulting
`x`- and `y`-iterates.

The chapter-level owner from `Algorithm_15_10` remains the canonical bridge for the generic
AD-LPMM recursion, including the explicit soft-thresholding step `ad_lpmm_x_update`.
This file keeps the source-facing basis-pursuit step-size names
`ad_lpmm_basis_pursuit_alpha_parameter` and `ad_lpmm_basis_pursuit_beta_parameter` only as thin
bridges to the canonical Chapter 15 owners from `Algorithm_15_10`, then specializes the recursive
iterate families to `λ = 1`, `z^k = b`, `x^0 = x0`, and `y^0 = y0`. The resulting public surface
keeps the source-facing basis-pursuit recursion and the singleton-constraint trajectory bridge
with `z = fun _ ↦ b` and `h₂ = δ_ ({b} : Set Y)`. -/

/-- The basis-pursuit specialization of the explicit soft-thresholded AD-LPMM `x`-update is the
Algorithm 15.10 formula with `λ = 1` and `z^k = b`, under the standing positivity condition
`0 < adlpmm_linearization_bound (1 : PosReal) A`. -/
abbrev ad_lpmm_basis_pursuit_x_update
    (A : E →ₗ[ℝ] Y) (ρ : PosReal)
    (hL : 0 < adlpmm_linearization_bound (1 : PosReal) A)
    (xk : E) (b yk : Y) : E :=
  ad_lpmm_x_update A ρ (1 : NNReal) hL xk b yk

/-- The basis-pursuit `x`-linearization parameter is the canonical Chapter 15 owner
`ad_lpmm_alpha_parameter` specialized to `λ = 1` and `z^k = b`. -/
abbrev ad_lpmm_basis_pursuit_alpha_parameter
    (A : E →ₗ[ℝ] Y) (ρ : PosReal)
    (hL : 0 < adlpmm_linearization_bound (1 : PosReal) A) :
    ADLPMMLinearizationParameter ρ A :=
  ad_lpmm_alpha_parameter A ρ hL

omit [FiniteDimensional ℝ Y] in
/-- Coercing the basis-pursuit `x`-linearization parameter to `ℝ` returns `α = ρ L`. -/
@[simp] theorem ad_lpmm_basis_pursuit_alpha_parameter_coe
    (A : E →ₗ[ℝ] Y) (ρ : PosReal)
    (hL : 0 < adlpmm_linearization_bound (1 : PosReal) A) :
    ((ad_lpmm_basis_pursuit_alpha_parameter A ρ hL : PosReal) : ℝ) =
      (ρ : ℝ) * adlpmm_linearization_bound (1 : PosReal) A := by
  simp [ad_lpmm_basis_pursuit_alpha_parameter, ad_lpmm_alpha_parameter_coe]

/-- The basis-pursuit `z`-linearization parameter is the canonical Chapter 15 owner
`ad_lpmm_beta_parameter` specialized to the fixed constraint `z^k = b`. -/
abbrev ad_lpmm_basis_pursuit_beta_parameter
    (ρ : PosReal) :
    ADLPMMLinearizationParameter ρ (-LinearMap.id : Y →ₗ[ℝ] Y) :=
  ad_lpmm_beta_parameter ρ

/-- Coercing the basis-pursuit `z`-linearization parameter to `PosReal` returns `β = ρ`. -/
@[simp] theorem ad_lpmm_basis_pursuit_beta_parameter_coe
    (ρ : PosReal) :
    ((ad_lpmm_basis_pursuit_beta_parameter ρ :
        ADLPMMLinearizationParameter ρ (-LinearMap.id : Y →ₗ[ℝ] Y)) : PosReal) = ρ := by
  simp [ad_lpmm_basis_pursuit_beta_parameter, ad_lpmm_beta_parameter_coe]

/-- Internal recursive state for the basis-pursuit specialization of Algorithm 15.14, storing
the pair `(x^k, y^k)` with the fixed branch `z^k = b`. -/
private def basisPursuitState
    (ρ : PosReal) (A : E →ₗ[ℝ] Y)
    (hL : 0 < adlpmm_linearization_bound (1 : PosReal) A)
    (b : Y) (x0 : E) (y0 : Y) :
    ℕ → E × Y
  | 0 => (x0, y0)
  | k + 1 =>
      let statek := basisPursuitState ρ A hL b x0 y0 k
      let xNext := ad_lpmm_basis_pursuit_x_update A ρ hL statek.1 b statek.2
      (xNext, admm_multiplier_update ρ A (-LinearMap.id) 0 statek.2 xNext b)

/-- The basis-pursuit `x`-iterates from Algorithm 15.14, obtained by recursively applying the
soft-thresholded Chapter 15 `x`-update with `λ = 1` and `z^k = b`. -/
def ad_lpmm_basis_pursuit_x
    (ρ : PosReal) (A : E →ₗ[ℝ] Y)
    (hL : 0 < adlpmm_linearization_bound (1 : PosReal) A)
    (b : Y) (x0 : E) (y0 : Y) :
    ℕ → E :=
  fun k ↦ (basisPursuitState ρ A hL b x0 y0 k).1

/-- The basis-pursuit multiplier iterates from Algorithm 15.14, obtained by recursively applying
the canonical affine multiplier update with `z^k = b`. -/
def ad_lpmm_basis_pursuit_y
    (ρ : PosReal) (A : E →ₗ[ℝ] Y)
    (hL : 0 < adlpmm_linearization_bound (1 : PosReal) A)
    (b : Y) (x0 : E) (y0 : Y) :
    ℕ → Y :=
  fun k ↦ (basisPursuitState ρ A hL b x0 y0 k).2

section

/-- The basis-pursuit `x`-sequence starts from `x^0 = x0`. -/
theorem ad_lpmm_basis_pursuit_x_zero
    (ρ : PosReal) (A : E →ₗ[ℝ] Y)
    (hL : 0 < adlpmm_linearization_bound (1 : PosReal) A)
    (b : Y) (x0 : E) (y0 : Y) :
    ad_lpmm_basis_pursuit_x ρ A hL b x0 y0 0 = x0 := by
  -- Evaluating the recursive state at `0` exposes the initial `x`-component.
  rfl

/-- The basis-pursuit multiplier sequence starts from `y^0 = y0`. -/
theorem ad_lpmm_basis_pursuit_y_zero
    (ρ : PosReal) (A : E →ₗ[ℝ] Y)
    (hL : 0 < adlpmm_linearization_bound (1 : PosReal) A)
    (b : Y) (x0 : E) (y0 : Y) :
    ad_lpmm_basis_pursuit_y ρ A hL b x0 y0 0 = y0 := by
  -- Evaluating the recursive state at `0` exposes the initial multiplier.
  rfl

/-- At every iteration `k`, the next basis-pursuit `x`-iterate is the canonical Chapter 15
soft-thresholding update specialized to `λ = 1` and `z^k = b`. -/
theorem ad_lpmm_basis_pursuit_x_succ
    (ρ : PosReal) (A : E →ₗ[ℝ] Y)
    (hL : 0 < adlpmm_linearization_bound (1 : PosReal) A)
    (b : Y) (x0 : E) (y0 : Y) (k : ℕ) :
    ad_lpmm_basis_pursuit_x ρ A hL b x0 y0 (k + 1) =
      ad_lpmm_basis_pursuit_x_update A ρ hL
        (ad_lpmm_basis_pursuit_x ρ A hL b x0 y0 k)
        b
        (ad_lpmm_basis_pursuit_y ρ A hL b x0 y0 k) := by
  -- One recursive unfolding shows that the next `x`-iterate is the stored update.
  rfl

/-- Helper for Algorithm 15.14: scaling the basis-pursuit `ℓ¹` regularizer by `(1 / α)`
specializes the generic Chapter 15 `ℓ¹` scaling formula to the case `λ = 1`. -/
theorem basisPursuitScaledL1Regularizer_eq
    (α : PosReal) :
    ((((1 / α : PosReal) : EReal) • ad_lpmm_l1_regularizer (1 : NNReal)) : E → EReal) =
      fun x : E ↦ ((((1 : ℝ) / (α : ℝ)) * ‖x‖₁ : ℝ) : EReal) := by
  -- Normalize the pointwise scaling on the specialized basis-pursuit `ℓ¹` penalty.
  funext x
  simp [Pi.smul_apply, smul_eq_mul, EReal.coe_mul, div_eq_mul_inv]

/-- Helper for Algorithm 15.14: the basis-pursuit `x`-update matches the owner soft-threshold
formula when the residual is written in the unsimplified `Algorithm 15.5` normal form. -/
theorem basisPursuitXUpdate_eq_ownerCenterSoftThreshold
    (ρ : PosReal) (A : E →ₗ[ℝ] Y) (b : Y)
    (hL : 0 < adlpmm_linearization_bound (1 : PosReal) A)
    (xk : E) (yk : Y) :
    ad_lpmm_basis_pursuit_x_update A ρ hL xk b yk =
      T_[((1 : ℝ) / ((ad_lpmm_basis_pursuit_alpha_parameter A ρ hL : PosReal) : ℝ))]
        (xk - (((ρ / (ad_lpmm_basis_pursuit_alpha_parameter A ρ hL : PosReal)) : PosReal) : ℝ) •
          A.adjoint (A xk + (-LinearMap.id : Y →ₗ[ℝ] Y) b - (0 : Y) + (1 / (ρ : ℝ)) • yk)) := by
  have hcenter :
      A xk - b + (1 / (ρ : ℝ)) • yk =
        A xk + (-LinearMap.id : Y →ₗ[ℝ] Y) b - (0 : Y) + (1 / (ρ : ℝ)) • yk := by
    -- Normalize the basis-pursuit residual to the owner `Algorithm 15.5` spelling once.
    simp only [sub_eq_add_neg, LinearMap.neg_apply, LinearMap.id_apply, neg_zero, zero_add,
      add_left_comm, add_comm]
  -- Route correction: keep the owner center unsimplified so the closing step avoids broad
  -- normalization of the large linear-composite residual.
  rw [ad_lpmm_basis_pursuit_x_update, ad_lpmm_x_update_eq,
    ad_lpmm_basis_pursuit_alpha_parameter, hcenter]
  norm_num

/-- Helper for Algorithm 15.14: the basis-pursuit one-step `x`-update is the generic
Algorithm 15.10 `x`-step specialized to `λ = 1` and `z^k = b`. -/
theorem ad_lpmm_basis_pursuit_x_update_mem_adlpmm_x_step
    (ρ : PosReal) (A : E →ₗ[ℝ] Y) (b : Y)
    (hL : 0 < adlpmm_linearization_bound (1 : PosReal) A)
    (xk : E) (yk : Y) :
    ad_lpmm_basis_pursuit_x_update A ρ hL xk b yk ∈
      adlpmm_x_step (ad_lpmm_l1_regularizer (1 : NNReal)) ρ
        (ad_lpmm_basis_pursuit_alpha_parameter A ρ hL) A (-LinearMap.id) 0
        xk
        b
        yk := by
  have hlam :
      0 ≤ (1 : ℝ) / ((ad_lpmm_basis_pursuit_alpha_parameter A ρ hL : PosReal) : ℝ) := by
    -- The basis-pursuit soft-threshold parameter is nonnegative because `α > 0`.
    exact div_nonneg zero_le_one (ad_lpmm_basis_pursuit_alpha_parameter A ρ hL : PosReal).2.le
  -- Route correction: rewrite the step definition to the owner prox form, then reduce membership
  -- to the singleton soft-threshold formula before applying the owner-center bridge.
  rw [mem_adlpmm_x_step_iff, basisPursuitScaledL1Regularizer_eq,
    prox_euclidean_l1_eq_singleton_softThreshold hlam, Set.mem_singleton_iff]
  -- The remaining equality is exactly the stable owner-center rewrite recorded above.
  exact basisPursuitXUpdate_eq_ownerCenterSoftThreshold ρ A b hL xk yk

/-- The next basis-pursuit `x`-iterate belongs to the canonical Chapter 15 linear-composite
AD-LPMM `x`-step set specialized to the `ℓ¹` term and the fixed value `z^k = b`. -/
theorem ad_lpmm_basis_pursuit_x_succ_mem_adlpmm_x_step
    (ρ : PosReal) (A : E →ₗ[ℝ] Y) (b : Y)
    (hL : 0 < adlpmm_linearization_bound (1 : PosReal) A)
    (x0 : E) (y0 : Y) (k : ℕ) :
    ad_lpmm_basis_pursuit_x ρ A hL b x0 y0 (k + 1) ∈
      adlpmm_x_step (ad_lpmm_l1_regularizer (1 : NNReal)) ρ
        (ad_lpmm_basis_pursuit_alpha_parameter A ρ hL) A (-LinearMap.id) 0
        (ad_lpmm_basis_pursuit_x ρ A hL b x0 y0 k)
        b
        (ad_lpmm_basis_pursuit_y ρ A hL b x0 y0 k) := by
  -- First unfold the recursive successor once, then reuse the stable one-step bridge.
  rw [ad_lpmm_basis_pursuit_x_succ]
  simpa using
    ad_lpmm_basis_pursuit_x_update_mem_adlpmm_x_step
      ρ A b hL
      (ad_lpmm_basis_pursuit_x ρ A hL b x0 y0 k)
      (ad_lpmm_basis_pursuit_y ρ A hL b x0 y0 k)

/-- Expanding the recursive basis-pursuit `x`-step gives the textbook soft-thresholding formula
from Algorithm 15.14. -/
theorem ad_lpmm_basis_pursuit_x_succ_eq
    (ρ : PosReal) (A : E →ₗ[ℝ] Y)
    (hL : 0 < adlpmm_linearization_bound (1 : PosReal) A)
    (b : Y) (x0 : E) (y0 : Y) (k : ℕ) :
    ad_lpmm_basis_pursuit_x ρ A hL b x0 y0 (k + 1) =
      T_[((1 : ℝ) / (adlpmm_linearization_bound (1 : PosReal) A * (ρ : ℝ)))]
        (ad_lpmm_basis_pursuit_x ρ A hL b x0 y0 k -
          (1 / adlpmm_linearization_bound (1 : PosReal) A : ℝ) •
            A.adjoint
              (A (ad_lpmm_basis_pursuit_x ρ A hL b x0 y0 k) - b +
                (1 / (ρ : ℝ)) • ad_lpmm_basis_pursuit_y ρ A hL b x0 y0 k)) := by
  have hρα :
      (((ρ / (ad_lpmm_basis_pursuit_alpha_parameter A ρ hL : PosReal)) : PosReal) : ℝ) =
        (1 / adlpmm_linearization_bound (1 : PosReal) A : ℝ) := by
    -- Rewrite the coefficient `(ρ / α)` using the basis-pursuit specialization `α = ρ L`.
    have hρ0 : (ρ : ℝ) ≠ 0 := ρ.2.ne'
    rw [PosReal.coe_div, ad_lpmm_basis_pursuit_alpha_parameter_coe]
    field_simp [hρ0]
  -- Expand one recursive step and normalize the two scalar coefficients in the soft threshold.
  rw [ad_lpmm_basis_pursuit_x_succ, ad_lpmm_basis_pursuit_x_update, ad_lpmm_x_update_eq, hρα]
  simp [mul_comm]

/-- At every iteration `k`, the next basis-pursuit multiplier iterate is the canonical affine
multiplier update specialized to `z^k = b`. -/
theorem ad_lpmm_basis_pursuit_y_succ
    (ρ : PosReal) (A : E →ₗ[ℝ] Y)
    (hL : 0 < adlpmm_linearization_bound (1 : PosReal) A)
    (b : Y) (x0 : E) (y0 : Y) (k : ℕ) :
    ad_lpmm_basis_pursuit_y ρ A hL b x0 y0 (k + 1) =
      admm_multiplier_update ρ A (-LinearMap.id) 0
        (ad_lpmm_basis_pursuit_y ρ A hL b x0 y0 k)
        (ad_lpmm_basis_pursuit_x ρ A hL b x0 y0 (k + 1))
        b := by
  -- One recursive unfolding shows that the next multiplier is the stored affine update.
  rfl

/-- Expanding the recursive basis-pursuit multiplier step gives the textbook affine formula
`y^(k+1) = y^k + ρ (A x^(k+1) - b)`. -/
theorem ad_lpmm_basis_pursuit_y_succ_eq
    (ρ : PosReal) (A : E →ₗ[ℝ] Y)
    (hL : 0 < adlpmm_linearization_bound (1 : PosReal) A)
    (b : Y) (x0 : E) (y0 : Y) (k : ℕ) :
    ad_lpmm_basis_pursuit_y ρ A hL b x0 y0 (k + 1) =
      ad_lpmm_basis_pursuit_y ρ A hL b x0 y0 k +
        (ρ : ℝ) • (A (ad_lpmm_basis_pursuit_x ρ A hL b x0 y0 (k + 1)) - b) := by
  -- Specialize the canonical ADMM affine update to the fixed branch `z^k = b`.
  rw [ad_lpmm_basis_pursuit_y_succ]
  rw [admm_multiplier_update_eq]
  simp [sub_eq_add_neg]

/-- Helper for Algorithm 15.14: the fixed singleton constraint `δ_ ({b})` forces the next
`z`-iterate to stay equal to `b`. -/
theorem singletonIndicator_point_mem_adlpmm_z_step
    (ρ : PosReal) (A : E →ₗ[ℝ] Y) (b : Y)
    (xNext : E) (yk : Y) :
    b ∈ adlpmm_z_step (δ_ ({b} : Set Y)) ρ
      ((ad_lpmm_basis_pursuit_beta_parameter ρ :
          ADLPMMLinearizationParameter ρ (-LinearMap.id : Y →ₗ[ℝ] Y)) : PosReal)
      A (-LinearMap.id) 0 xNext b yk := by
  let β : PosReal :=
    ((ad_lpmm_basis_pursuit_beta_parameter ρ :
        ADLPMMLinearizationParameter ρ (-LinearMap.id : Y →ₗ[ℝ] Y)) : PosReal)
  let center : Y :=
    b - ((ρ / β : PosReal) : ℝ) •
      (-LinearMap.id : Y →ₗ[ℝ] Y).adjoint
        (A xNext + (-LinearMap.id : Y →ₗ[ℝ] Y) b - 0 + (1 / (ρ : ℝ)) • yk)
  have hprox :
      prox[((((1 / β : PosReal) : EReal) • δ_ ({b} : Set Y)))] center =
        {
          Pp[({b} : Set Y), Set.singleton_nonempty b, isClosed_singleton, convex_singleton b]
            center
        } := by
    -- The prox of a scaled singleton indicator is the singleton metric projection onto `{b}`.
    simpa [center] using
      prox_scaledExtendedIndicator_eq_singleton_metricProjection
        ({b} : Set Y)
        (Set.singleton_nonempty b)
        isClosed_singleton
        (convex_singleton b)
        (1 / β : PosReal)
        center
  -- Unfold the `z`-step and replace the proximal map of the scaled singleton indicator by the
  -- singleton metric projection at the same center.
  rw [mem_adlpmm_z_step_iff, hprox]
  -- The metric projection onto a singleton lands at its unique point.
  have hmem :
      Pp[({b} : Set Y), Set.singleton_nonempty b, isClosed_singleton, convex_singleton b] center
        ∈ ({b} : Set Y) :=
    projectionPoint_mem
      ({b} : Set Y)
      (Set.singleton_nonempty b)
      isClosed_singleton
      (convex_singleton b)
      center
  have hprojection :
      Pp[({b} : Set Y), Set.singleton_nonempty b, isClosed_singleton, convex_singleton b] center =
        b := by
    exact Set.mem_singleton_iff.mp hmem
  rw [Set.mem_singleton_iff, hprojection]

/-- Algorithm 15.14: the explicit basis-pursuit iterates form the canonical linear-composite
AD-LPMM trajectory with `h₁ x = ‖x‖₁`, `h₂ = δ_ ({b} : Set Y)`, `α = ρ L`,
`β = ρ`, and the fixed `z^k = b`. -/
theorem ad_lpmm_basis_pursuit_trajectory
    (ρ : PosReal) (A : E →ₗ[ℝ] Y) (b : Y)
    (hL : 0 < adlpmm_linearization_bound (1 : PosReal) A)
    (x0 : E) (y0 : Y) :
    IsADLPMMTrajectory ρ A (-LinearMap.id) 0
      (ad_lpmm_basis_pursuit_alpha_parameter A ρ hL) (ad_lpmm_basis_pursuit_beta_parameter ρ)
      (ad_lpmm_l1_regularizer (1 : NNReal)) (δ_ ({b} : Set Y))
      (ad_lpmm_basis_pursuit_x ρ A hL b x0 y0) (fun _ ↦ b)
      (ad_lpmm_basis_pursuit_y ρ A hL b x0 y0) x0 b y0 := by
  refine
    { x_zero := ?_
      z_zero := ?_
      y_zero := ?_
      x_step := ?_
      z_step := ?_
      y_step := ?_ }
  · -- The recursive basis-pursuit `x`-sequence starts from the prescribed `x0`.
    simpa using ad_lpmm_basis_pursuit_x_zero ρ A hL b x0 y0
  · -- The frozen `z`-branch is constantly equal to `b`.
    rfl
  · -- The recursive multiplier sequence starts from the prescribed `y0`.
    simpa using ad_lpmm_basis_pursuit_y_zero ρ A hL b x0 y0
  · intro k
    -- Reuse the one-step `x` bridge after matching the constant `z`-branch.
    simpa using ad_lpmm_basis_pursuit_x_succ_mem_adlpmm_x_step ρ A b hL x0 y0 k
  · intro k
    -- The singleton indicator forces every `z`-update to remain at the fixed point `b`.
    simpa using
      singletonIndicator_point_mem_adlpmm_z_step
        ρ
        A
        b
        (ad_lpmm_basis_pursuit_x ρ A hL b x0 y0 (k + 1))
        (ad_lpmm_basis_pursuit_y ρ A hL b x0 y0 k)
  · intro k
    -- The multiplier recursion is already the canonical affine ADMM update.
    simpa using ad_lpmm_basis_pursuit_y_succ ρ A hL b x0 y0 k

end

end
