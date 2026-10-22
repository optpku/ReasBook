/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import FirstOrderMethodsOptimization_Beck_2017.Chap06.EuclideanL1Norm
import FirstOrderMethodsOptimization_Beck_2017.Chap06.Definition_6_3
import FirstOrderMethodsOptimization_Beck_2017.Chap06.Example_6_8
import FirstOrderMethodsOptimization_Beck_2017.Chap06.Proposition_6_2_3
import FirstOrderMethodsOptimization_Beck_2017.Chap12.Definition_12_10
import FirstOrderMethodsOptimization_Beck_2017.Chap15.Algorithm_15_5

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open scoped RealInnerProductSpace
open scoped SoftThreshold

universe u v

section

variable {X : Type u} {Y : Type v}
variable [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X]
variable [NormedAddCommGroup Y] [NormedSpace ℝ Y]

/- Semantic search did not return a useful Chapter 15 AD-LPMM hit for this niche specialization,
so the owner/API choice was verified against the local Chapter 15 AD-LPMM files
(`Algorithm_15_5`, `Algorithm_15_8`, `Algorithm_15_9`) and the Chapter 6 soft-threshold
notation.

This item is `source-facing`: Algorithm 15.10 gives the concrete AD-LPMM specialization
`α = ρ L`, `β = ρ`, with `L = λ_max(Aᵀ A)`, together with explicit recursions for
`x^(k+1)`, `z^(k+1)`, and `y^(k+1)`. The public surface here therefore keeps:
- the exact Chapter 15 parameter choices `ad_lpmm_alpha_parameter` and
  `ad_lpmm_beta_parameter`;
- the explicit soft-thresholded `x`-update, guarded by the source-faithful condition `0 < L`;
- the recursive iterate families `ad_lpmm_x`, `ad_lpmm_z`, and `ad_lpmm_y` built from that
  guarded `x`-update;
- bridge theorems connecting those explicit recursions to the canonical linear-composite
  AD-LPMM owners from Algorithms 15.5, 15.8, and 15.9;
- reusable companion lemmas exposing the one-step `x`- and `z`-updates directly, and recovering
  those same formulas from any canonical `IsADLPMMTrajectory` carrying the Algorithm 15.10
  specialization data. -/

/-- Positivity of the exact Algorithm 15.10 choice `α = ρ L`. -/
theorem ad_lpmm_alpha_pos
    (A : X →ₗ[ℝ] Y) (ρ : PosReal)
    (hL : 0 < adlpmm_linearization_bound (1 : PosReal) A) :
    0 < (ρ : ℝ) * adlpmm_linearization_bound (1 : PosReal) A := by
  -- The specialized parameter `α = ρ L` is positive because both factors are positive.
  exact mul_pos ρ.2 hL

/-- The exact Algorithm 15.10 choice `α = ρ L` is admissible for the generic AD-LPMM
`x`-linearization bound. -/
theorem ad_lpmm_alpha_admissible
    (A : X →ₗ[ℝ] Y) (ρ : PosReal) :
    adlpmm_linearization_bound ρ A ≤
      (ρ : ℝ) * adlpmm_linearization_bound (1 : PosReal) A := by
  -- Unfold the canonical bound on both sides; the claimed inequality is equality.
  simp [adlpmm_linearization_bound]

/-- The Algorithm 15.10 choice `α = ρ L` as the canonical Chapter 15 `x`-linearization
parameter. -/
def ad_lpmm_alpha_parameter
    (A : X →ₗ[ℝ] Y) (ρ : PosReal)
    (hL : 0 < adlpmm_linearization_bound (1 : PosReal) A) :
    ADLPMMLinearizationParameter ρ A :=
  ⟨⟨(ρ : ℝ) * adlpmm_linearization_bound (1 : PosReal) A, ad_lpmm_alpha_pos A ρ hL⟩,
    ad_lpmm_alpha_admissible A ρ⟩

/-- Coercing the canonical Algorithm 15.10 `x`-linearization parameter to `ℝ` returns
`α = ρ L`. -/
@[simp] theorem ad_lpmm_alpha_parameter_coe
    (A : X →ₗ[ℝ] Y) (ρ : PosReal)
    (hL : 0 < adlpmm_linearization_bound (1 : PosReal) A) :
    ((ad_lpmm_alpha_parameter A ρ hL : PosReal) : ℝ) =
      (ρ : ℝ) * adlpmm_linearization_bound (1 : PosReal) A := by
  -- The subtype stores `α = ρ L` in its first component.
  rfl

end

section

variable {Y : Type v}
variable [NormedAddCommGroup Y] [NormedSpace ℝ Y] [FiniteDimensional ℝ Y]

/-- The Algorithm 15.10 choice `β = ρ` as the canonical Chapter 15 `z`-linearization
parameter for the linear-composite specialization `B = -I`. -/
def ad_lpmm_beta_parameter
    (ρ : PosReal) :
    ADLPMMLinearizationParameter ρ (-LinearMap.id : Y →ₗ[ℝ] Y) :=
  ⟨ρ, adlpmm_linearization_bound_neg_id_le ρ⟩

/-- Coercing the canonical Algorithm 15.10 `z`-linearization parameter to `PosReal` returns
`β = ρ`. -/
@[simp] theorem ad_lpmm_beta_parameter_coe
    (ρ : PosReal) :
    ((ad_lpmm_beta_parameter ρ :
        ADLPMMLinearizationParameter ρ (-LinearMap.id : Y →ₗ[ℝ] Y)) : PosReal) = ρ := by
  -- The subtype stores `β = ρ` in its first component.
  rfl

end

section

variable {ι : Type u} {Y : Type v}
variable [Fintype ι]
variable [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [FiniteDimensional ℝ Y]

local notation "X" => EuclideanSpace ℝ ι

/-- The Algorithm 15.10 `ℓ¹` regularizer `x ↦ λ ‖x‖₁`. -/
abbrev ad_lpmm_l1_regularizer (lam : NNReal) : X → EReal :=
  fun x ↦ (((lam : ℝ) * ‖x‖₁ : ℝ) : EReal)

/-- Evaluating `ad_lpmm_l1_regularizer` gives the displayed `ℓ¹` penalty `λ ‖x‖₁`. -/
@[simp] theorem ad_lpmm_l1_regularizer_apply
    (lam : NNReal) (x : X) :
    ad_lpmm_l1_regularizer lam x = (((lam : ℝ) * ‖x‖₁ : ℝ) : EReal) := rfl

/-- The explicit soft-thresholding `x`-update used by Algorithm 15.10 under the standing
positivity condition `0 < L`, where `L = adlpmm_linearization_bound (1 : PosReal) A`. -/
def ad_lpmm_x_update
    (A : X →ₗ[ℝ] Y) (ρ : PosReal) (lam : NNReal)
    (hL : 0 < adlpmm_linearization_bound (1 : PosReal) A)
    (xk : X) (zk yk : Y) : X :=
  T_[((lam : ℝ) / ((ad_lpmm_alpha_parameter A ρ hL : PosReal) : ℝ))]
    (xk - (((ρ / (ad_lpmm_alpha_parameter A ρ hL : PosReal)) : PosReal) : ℝ) •
      A.adjoint (A xk - zk + (1 / (ρ : ℝ)) • yk))

/-- Expanding `ad_lpmm_x_update` yields the displayed soft-threshold formula from Algorithm 15.10.
-/
theorem ad_lpmm_x_update_eq
    (A : X →ₗ[ℝ] Y) (ρ : PosReal) (lam : NNReal)
    (hL : 0 < adlpmm_linearization_bound (1 : PosReal) A)
    (xk : X) (zk yk : Y) :
    ad_lpmm_x_update A ρ lam hL xk zk yk =
      T_[((lam : ℝ) / ((ad_lpmm_alpha_parameter A ρ hL : PosReal) : ℝ))]
        (xk - (((ρ / (ad_lpmm_alpha_parameter A ρ hL : PosReal)) : PosReal) : ℝ) •
          A.adjoint (A xk - zk + (1 / (ρ : ℝ)) • yk)) := rfl

end

section

variable {ι : Type u} {Y : Type v}
variable [Fintype ι]
variable [NormedAddCommGroup Y] [NormedSpace ℝ Y]

local notation "X" => EuclideanSpace ℝ ι

/-- The explicit affine-average `z`-update used by Algorithm 15.10. -/
def ad_lpmm_z_update
    (A : X →ₗ[ℝ] Y) (b : Y) (ρ : PosReal)
    (xNext : X) (yk : Y) : Y :=
  (1 / ((ρ : ℝ) + 1)) • ((ρ : ℝ) • A xNext + yk + b)

/-- Expanding `ad_lpmm_z_update` yields the displayed affine-average formula from
Algorithm 15.10. -/
@[simp] theorem ad_lpmm_z_update_eq
    (A : X →ₗ[ℝ] Y) (b : Y) (ρ : PosReal)
    (xNext : X) (yk : Y) :
    ad_lpmm_z_update A b ρ xNext yk =
      (1 / ((ρ : ℝ) + 1)) • ((ρ : ℝ) • A xNext + yk + b) := rfl

end

section

variable {ι : Type u} {κ : Type v}
variable [Fintype ι] [Fintype κ]

local notation "X" => EuclideanSpace ℝ ι
local notation "Y" => EuclideanSpace ℝ κ

/-- The recursive internal Algorithm 15.10 state sequence. -/
private def iterateState
    (A : X →ₗ[ℝ] Y) (ρ : PosReal) (lam : NNReal)
    (hL : 0 < adlpmm_linearization_bound (1 : PosReal) A)
    (b : Y) (x0 : X) (z0 y0 : Y) :
    ℕ → X × Y × Y
  | 0 => (x0, z0, y0)
  | k + 1 =>
      let ⟨xk, zk, yk⟩ := iterateState A ρ lam hL b x0 z0 y0 k
      let xNext := ad_lpmm_x_update A ρ lam hL xk zk yk
      let zNext := ad_lpmm_z_update A b ρ xNext yk
      (xNext, zNext, admm_multiplier_update ρ A (-LinearMap.id) 0 yk xNext zNext)

/-- The `x`-iterate sequence from Algorithm 15.10. -/
def ad_lpmm_x
    (A : X →ₗ[ℝ] Y) (ρ : PosReal) (lam : NNReal)
    (hL : 0 < adlpmm_linearization_bound (1 : PosReal) A)
    (b : Y) (x0 : X) (z0 y0 : Y) :
    ℕ → X :=
  fun k ↦
    let ⟨xk, _, _⟩ := iterateState A ρ lam hL b x0 z0 y0 k
    xk

/-- The `z`-iterate sequence from Algorithm 15.10. -/
def ad_lpmm_z
    (A : X →ₗ[ℝ] Y) (ρ : PosReal) (lam : NNReal)
    (hL : 0 < adlpmm_linearization_bound (1 : PosReal) A)
    (b : Y) (x0 : X) (z0 y0 : Y) :
    ℕ → Y :=
  fun k ↦
    let ⟨_, zk, _⟩ := iterateState A ρ lam hL b x0 z0 y0 k
    zk

/-- The multiplier sequence from Algorithm 15.10. -/
def ad_lpmm_y
    (A : X →ₗ[ℝ] Y) (ρ : PosReal) (lam : NNReal)
    (hL : 0 < adlpmm_linearization_bound (1 : PosReal) A)
    (b : Y) (x0 : X) (z0 y0 : Y) :
    ℕ → Y :=
  fun k ↦
    let ⟨_, _, yk⟩ := iterateState A ρ lam hL b x0 z0 y0 k
    yk

section

/-- The Algorithm 15.10 `x`-sequence starts from `x^0 = x0`. -/
theorem ad_lpmm_x_zero
    (A : X →ₗ[ℝ] Y) (ρ : PosReal) (lam : NNReal)
    (hL : 0 < adlpmm_linearization_bound (1 : PosReal) A)
    (b : Y) (x0 : X) (z0 y0 : Y) :
    ad_lpmm_x A ρ lam hL b x0 z0 y0 0 = x0 := by
  -- Evaluating the recursive state at `0` exposes the initial `x`-component.
  rfl

/-- The Algorithm 15.10 `z`-sequence starts from `z^0 = z0`. -/
theorem ad_lpmm_z_zero
    (A : X →ₗ[ℝ] Y) (ρ : PosReal) (lam : NNReal)
    (hL : 0 < adlpmm_linearization_bound (1 : PosReal) A)
    (b : Y) (x0 : X) (z0 y0 : Y) :
    ad_lpmm_z A ρ lam hL b x0 z0 y0 0 = z0 := by
  -- Evaluating the recursive state at `0` exposes the initial `z`-component.
  rfl

/-- The Algorithm 15.10 multiplier sequence starts from `y^0 = y0`. -/
theorem ad_lpmm_y_zero
    (A : X →ₗ[ℝ] Y) (ρ : PosReal) (lam : NNReal)
    (hL : 0 < adlpmm_linearization_bound (1 : PosReal) A)
    (b : Y) (x0 : X) (z0 y0 : Y) :
    ad_lpmm_y A ρ lam hL b x0 z0 y0 0 = y0 := by
  -- Evaluating the recursive state at `0` exposes the initial multiplier.
  rfl

/-- The recursive `x`-iterate is obtained by applying the explicit soft-thresholding
one-step update to the previous state. -/
theorem ad_lpmm_x_succ
    (A : X →ₗ[ℝ] Y) (ρ : PosReal) (lam : NNReal)
    (hL : 0 < adlpmm_linearization_bound (1 : PosReal) A)
    (b : Y) (x0 : X) (z0 y0 : Y) (k : ℕ) :
    ad_lpmm_x A ρ lam hL b x0 z0 y0 (k + 1) =
      ad_lpmm_x_update
        A
        ρ
        lam
        hL
        (ad_lpmm_x A ρ lam hL b x0 z0 y0 k)
        (ad_lpmm_z A ρ lam hL b x0 z0 y0 k)
        (ad_lpmm_y A ρ lam hL b x0 z0 y0 k) := by
  -- One recursive unfolding shows that the next `x`-iterate is exactly the stored update.
  rfl

/-- At every iteration `k`, the next `x`-iterate is the displayed
soft-thresholding update
`x^(k+1) = T_[λ / (L ρ)] (x^k - (1 / L) Aᵀ (A x^k - z^k + (1 / ρ) y^k))`. -/
theorem ad_lpmm_x_succ_eq
    (A : X →ₗ[ℝ] Y) (ρ : PosReal) (lam : NNReal)
    (hL : 0 < adlpmm_linearization_bound (1 : PosReal) A)
    (b : Y) (x0 : X) (z0 y0 : Y) (k : ℕ) :
    ad_lpmm_x A ρ lam hL b x0 z0 y0 (k + 1) =
      T_[((lam : ℝ) / (adlpmm_linearization_bound (1 : PosReal) A * (ρ : ℝ)))]
        (ad_lpmm_x A ρ lam hL b x0 z0 y0 k -
          (1 / adlpmm_linearization_bound (1 : PosReal) A : ℝ) •
            A.adjoint
              (A (ad_lpmm_x A ρ lam hL b x0 z0 y0 k) -
                ad_lpmm_z A ρ lam hL b x0 z0 y0 k +
                (1 / (ρ : ℝ)) • ad_lpmm_y A ρ lam hL b x0 z0 y0 k)) := by
  have hρα :
      (((ρ / (ad_lpmm_alpha_parameter A ρ hL : PosReal)) : PosReal) : ℝ) =
        (1 / adlpmm_linearization_bound (1 : PosReal) A : ℝ) := by
    -- Rewrite the coefficient `(ρ / α)` using the specialization `α = ρ L`.
    have hρ0 : (ρ : ℝ) ≠ 0 := ρ.2.ne'
    rw [PosReal.coe_div, ad_lpmm_alpha_parameter_coe]
    field_simp [hρ0]
  -- Expand one step of the recursion and then normalize the two scalar coefficients.
  rw [ad_lpmm_x_succ, ad_lpmm_x_update_eq, hρα]
  simp [ad_lpmm_alpha_parameter_coe, mul_comm]

/-- The recursive `z`-iterate is obtained by applying the shared least-squares affine-average
update to the current `x^(k+1)` and `y^k`. -/
theorem ad_lpmm_z_succ
    (A : X →ₗ[ℝ] Y) (ρ : PosReal) (lam : NNReal)
    (hL : 0 < adlpmm_linearization_bound (1 : PosReal) A)
    (b : Y) (x0 : X) (z0 y0 : Y) (k : ℕ) :
    ad_lpmm_z A ρ lam hL b x0 z0 y0 (k + 1) =
      ad_lpmm_z_update
        A
        b
        ρ
        (ad_lpmm_x A ρ lam hL b x0 z0 y0 (k + 1))
        (ad_lpmm_y A ρ lam hL b x0 z0 y0 k) := by
  -- One recursive unfolding shows that the next `z`-iterate is exactly the stored affine average.
  rfl

/-- For Algorithm 15.10, at every iteration `k`, the next `z`-iterate satisfies
`z^(k+1) = (ρ A x^(k+1) + y^k + b) / (ρ + 1)`. -/
theorem ad_lpmm_z_succ_eq
    (A : X →ₗ[ℝ] Y) (ρ : PosReal) (lam : NNReal)
    (hL : 0 < adlpmm_linearization_bound (1 : PosReal) A)
    (b : Y) (x0 : X) (z0 y0 : Y) (k : ℕ) :
    ad_lpmm_z A ρ lam hL b x0 z0 y0 (k + 1) =
      (1 / ((ρ : ℝ) + 1)) •
        ((ρ : ℝ) • A (ad_lpmm_x A ρ lam hL b x0 z0 y0 (k + 1)) +
          ad_lpmm_y A ρ lam hL b x0 z0 y0 k + b) := by
  -- Expand the recursive `z`-step to the displayed affine-average formula.
  rw [ad_lpmm_z_succ, ad_lpmm_z_update_eq]

/-- The recursive multiplier iterate is obtained by the canonical linear-composite ADMM
multiplier update specialized to `A x - z = 0`. -/
theorem ad_lpmm_y_succ
    (A : X →ₗ[ℝ] Y) (ρ : PosReal) (lam : NNReal)
    (hL : 0 < adlpmm_linearization_bound (1 : PosReal) A)
    (b : Y) (x0 : X) (z0 y0 : Y) (k : ℕ) :
    ad_lpmm_y A ρ lam hL b x0 z0 y0 (k + 1) =
      admm_multiplier_update
        ρ
        A
        (-LinearMap.id)
        0
        (ad_lpmm_y A ρ lam hL b x0 z0 y0 k)
        (ad_lpmm_x A ρ lam hL b x0 z0 y0 (k + 1))
        (ad_lpmm_z A ρ lam hL b x0 z0 y0 (k + 1)) := by
  -- One recursive unfolding shows that the next multiplier is the stored ADMM affine update.
  rfl

/-- For Algorithm 15.10, at every iteration `k`, the multiplier update is
`y^(k+1) = y^k + ρ (A x^(k+1) - z^(k+1))`. -/
theorem ad_lpmm_y_succ_eq
    (A : X →ₗ[ℝ] Y) (ρ : PosReal) (lam : NNReal)
    (hL : 0 < adlpmm_linearization_bound (1 : PosReal) A)
    (b : Y) (x0 : X) (z0 y0 : Y) (k : ℕ) :
    ad_lpmm_y A ρ lam hL b x0 z0 y0 (k + 1) =
      ad_lpmm_y A ρ lam hL b x0 z0 y0 k +
        (ρ : ℝ) •
          (A (ad_lpmm_x A ρ lam hL b x0 z0 y0 (k + 1)) -
            ad_lpmm_z A ρ lam hL b x0 z0 y0 (k + 1)) := by
  -- Specialize the canonical linear-composite multiplier owner to `A x - z = 0`.
  simpa [admm_multiplier_update, sub_eq_add_neg] using
    ad_lpmm_y_succ A ρ lam hL b x0 z0 y0 k

/-- Helper for Algorithm 15.10: scaling `ad_lpmm_l1_regularizer lam` by `(1 / α)` yields the
explicit `ℓ¹` penalty with coefficient `(lam : ℝ) / (α : ℝ)`. -/
theorem scaledAdLpmmL1Regularizer_eq
    (lam : NNReal) (α : PosReal) :
    ((((1 / α : PosReal) : EReal) • ad_lpmm_l1_regularizer lam) : X → EReal) =
      fun x : X ↦ ((((lam : ℝ) / (α : ℝ)) * ‖x‖₁ : ℝ) : EReal) := by
  -- Normalize the pointwise scalar multiplication on the `EReal`-valued regularizer.
  funext x
  simp [Pi.smul_apply, smul_eq_mul, EReal.coe_mul, div_eq_mul_inv]
  ac_rfl

/-- Helper for Algorithm 15.10: the scaled denoising fidelity block has the affine-average prox
singleton centered at `A xNext + (1 / ρ) • yk`. -/
theorem prox_scaledDenoisingDataFidelity_eq_singleton
    (A : X →ₗ[ℝ] Y) (b : Y) (ρ : PosReal) (xNext : X) (yk : Y) :
    prox[((((1 / ρ : PosReal) : EReal) • denoising_data_fidelity b))]
      (A xNext + (1 / (ρ : ℝ)) • yk) =
        {ad_lpmm_z_update A b ρ xNext yk} := by
  classical
  let Aρ : Matrix κ κ ℝ := ((ρ : ℝ)⁻¹) • 1
  let c : Y := -((ρ : ℝ)⁻¹) • b
  let g : Y → EReal :=
    fun z : Y ↦ (((1 / 2 : ℝ) * ⟪Aρ.toEuclideanLin z, z⟫ + ⟪c, z⟫ : ℝ) : EReal)
  let d : ℝ := (1 / (2 * (ρ : ℝ))) * ‖b‖ ^ (2 : ℕ)
  have hρ_nonneg : 0 ≤ (ρ : ℝ)⁻¹ := (inv_pos.mpr ρ.2).le
  have hpsd : Aρ.PosSemidef := by
    -- The scaled identity matrix stays positive semidefinite.
    simpa [Aρ] using
      (Matrix.PosDef.one : Matrix.PosDef (1 : Matrix κ κ ℝ)).posSemidef.smul hρ_nonneg
  have hscaled_fun :
      ((((1 / ρ : PosReal) : EReal) • denoising_data_fidelity b) : Y → EReal) =
        fun z : Y ↦ g z + (d : EReal) := by
    have hAρ_apply (z : Y) : Aρ.toEuclideanLin z = (ρ : ℝ)⁻¹ • z := by
      ext i
      change ((Aρ.mulVec z.ofLp) i = (((ρ : ℝ)⁻¹ • z).ofLp i))
      simp [Aρ, Matrix.smul_mulVec, Matrix.one_mulVec]
    funext z
    have hinner : ⟪Aρ.toEuclideanLin z, z⟫ = (ρ : ℝ)⁻¹ * ‖z‖ ^ (2 : ℕ) := by
      rw [hAρ_apply z, real_inner_smul_left, real_inner_self_eq_norm_sq]
    have hreal :
        ((ρ : ℝ)⁻¹ * (‖z - b‖ ^ (2 : ℕ) / 2)) =
          (1 / 2 : ℝ) * ⟪Aρ.toEuclideanLin z, z⟫ + ⟪c, z⟫ + d := by
      rw [hinner]
      simp [c, d, norm_sub_sq_real, real_inner_smul_right, real_inner_comm, div_eq_mul_inv]
      ring
    simp only [denoising_data_fidelity_apply, g, PosReal.coe_div, PosReal.coe_one, one_div,
      Pi.smul_apply, smul_eq_mul]
    norm_num
    exact_mod_cast hreal
  have hprox_const := congrFun (prox_add_const g d) (A xNext + (1 / (ρ : ℝ)) • yk)
  have hprox_g :
      prox[g] (A xNext + (1 / (ρ : ℝ)) • yk) =
        prox[((((1 / ρ : PosReal) : EReal) • denoising_data_fidelity b))]
          (A xNext + (1 / (ρ : ℝ)) • yk) := by
    -- Remove the irrelevant additive constant from the proximal set.
    rw [← hscaled_fun] at hprox_const
    simpa using hprox_const.symm
  have hquad :
      prox[g] (A xNext + (1 / (ρ : ℝ)) • yk) =
        {((Aρ + 1)⁻¹).toEuclideanLin (A xNext + (1 / (ρ : ℝ)) • yk - c)} := by
    -- Reduce the prox to the standard quadratic-affine singleton formula.
    simpa [g] using
      prox_quadratic_affine_function_eq_singleton
        Aρ hpsd c (A xNext + (1 / (ρ : ℝ)) • yk)
  have hcenter :
      ((Aρ + 1)⁻¹).toEuclideanLin (A xNext + (1 / (ρ : ℝ)) • yk - c) =
        ad_lpmm_z_update A b ρ xNext yk := by
    have hAρ_add : Aρ + 1 = (((ρ : ℝ)⁻¹ + 1 : ℝ) • (1 : Matrix κ κ ℝ)) := by
      ext i j
      by_cases hij : i = j <;> simp [Aρ, hij]
    rw [hAρ_add, ad_lpmm_z_update_eq]
    have hρ0 : (ρ : ℝ) ≠ 0 := ρ.2.ne'
    have hkpos : 0 < (((ρ : ℝ)⁻¹ + 1 : ℝ)) := by
      have hkinv : 0 < ((ρ : ℝ)⁻¹) := inv_pos.mpr ρ.2
      linarith
    have hk : (((ρ : ℝ)⁻¹ + 1 : ℝ)) ≠ 0 := hkpos.ne'
    let _ := invertibleOfNonzero hk
    -- Rewrite the inverse scaled identity explicitly and simplify the affine center.
    ext i
    change ((((((ρ : ℝ)⁻¹ + 1 : ℝ) • (1 : Matrix κ κ ℝ))⁻¹).mulVec
        (A xNext + (1 / (ρ : ℝ)) • yk - c).ofLp) i =
      (((1 / ((ρ : ℝ) + 1)) • ((ρ : ℝ) • A xNext + yk + b)).ofLp i))
    have hinv :
        ((((ρ : ℝ)⁻¹ + 1 : ℝ) • (1 : Matrix κ κ ℝ))⁻¹) =
          ((((ρ : ℝ)⁻¹ + 1 : ℝ)⁻¹) • (1 : Matrix κ κ ℝ)) := by
      simp [Matrix.inv_smul]
    rw [hinv, Matrix.smul_mulVec]
    simp [c, Matrix.one_mulVec]
    field_simp [hρ0]
    ring
  -- Chain the constant-removal, quadratic prox, and center-identification steps.
  rw [← hprox_g, hquad, hcenter]

end

/-- The explicit Algorithm 15.10 `x`-update belongs to the corresponding linear-composite
AD-LPMM `x`-step with `α = ρ L`. -/
theorem ad_lpmm_x_update_mem_adlpmm_x_step
    (A : X →ₗ[ℝ] Y) (ρ : PosReal) (lam : NNReal)
    (hL : 0 < adlpmm_linearization_bound (1 : PosReal) A)
    (xk : X) (zk yk : Y) :
    ad_lpmm_x_update A ρ lam hL xk zk yk ∈
      adlpmm_x_step
        (ad_lpmm_l1_regularizer lam)
        ρ
        (ad_lpmm_alpha_parameter A ρ hL : PosReal)
        A
        (-LinearMap.id)
        0
        xk
        zk
        yk := by
  have hlam :
      0 ≤ (lam : ℝ) / ((ad_lpmm_alpha_parameter A ρ hL : PosReal) : ℝ) := by
    -- The threshold parameter is nonnegative because `λ ≥ 0` and `α > 0`.
    exact div_nonneg lam.2 (show 0 ≤ ((ad_lpmm_alpha_parameter A ρ hL : PosReal) : ℝ) from
      (ad_lpmm_alpha_parameter A ρ hL : PosReal).2.le)
  -- Unfold the generic AD-LPMM `x`-step and simplify the `B = -I`, `c = 0` specialization.
  rw [mem_adlpmm_x_step_iff, scaledAdLpmmL1Regularizer_eq,
    prox_euclidean_l1_eq_singleton_softThreshold hlam, Set.mem_singleton_iff]
  simp [sub_eq_add_neg, ad_lpmm_x_update_eq]

/-- The explicit least-squares affine-average update used in Algorithm 15.10 belongs to the
corresponding linear-composite AD-LPMM `z`-step with `β = ρ`. -/
theorem ad_lpmm_z_update_mem_adlpmm_z_step
    (A : X →ₗ[ℝ] Y) (ρ : PosReal)
    (b : Y) (xNext : X) (zk yk : Y) :
    ad_lpmm_z_update A b ρ xNext yk ∈
    adlpmm_z_step
        (denoising_data_fidelity b)
        ρ
        ρ
        A
        (-LinearMap.id)
        0
        xNext
        zk
        yk := by
  have hρdivρ : (((ρ / ρ : PosReal) : ℝ)) = 1 := by
    have hρ0 : (ρ : ℝ) ≠ 0 := by
      exact ne_of_gt ρ.2
    rw [PosReal.coe_div]
    exact div_self hρ0
  have hcenter :
      zk + ((1 / (ρ : ℝ)) • yk + (-zk + A xNext)) =
        A xNext + (1 / (ρ : ℝ)) • yk := by
    abel_nf
  -- Reduce the generic AD-LPMM `z`-step to the prox centered at `A xNext + (1 / ρ) • yk`.
  rw [mem_adlpmm_z_step_iff]
  have hsimple :
      ad_lpmm_z_update A b ρ xNext yk ∈
        prox[((((1 / ρ : PosReal) : EReal) • denoising_data_fidelity b))]
          (A xNext + (1 / (ρ : ℝ)) • yk) := by
    rw [prox_scaledDenoisingDataFidelity_eq_singleton, Set.mem_singleton_iff]
  have hmem :
      ad_lpmm_z_update A b ρ xNext yk ∈
        prox[((((1 / ρ : PosReal) : EReal) • denoising_data_fidelity b))]
          (zk + ((1 / (ρ : ℝ)) • yk + (-zk + A xNext))) := by
    exact hcenter.symm ▸ hsimple
  simpa [sub_eq_add_neg, hρdivρ, add_assoc, add_comm, add_left_comm] using hmem

/-- Algorithm 15.10: the explicit AD-LPMM iterates form the canonical linear-composite
trajectory with `α = ρ L` and `β = ρ`. -/
theorem ad_lpmm_trajectory
    (A : X →ₗ[ℝ] Y) (ρ : PosReal) (lam : NNReal)
    (hL : 0 < adlpmm_linearization_bound (1 : PosReal) A)
    (b : Y) (x0 : X) (z0 y0 : Y) :
    IsADLPMMTrajectory
      ρ
      A
      (-LinearMap.id)
      0
      (ad_lpmm_alpha_parameter A ρ hL)
      (ad_lpmm_beta_parameter ρ)
      (ad_lpmm_l1_regularizer lam)
      (denoising_data_fidelity b)
      (ad_lpmm_x A ρ lam hL b x0 z0 y0)
      (ad_lpmm_z A ρ lam hL b x0 z0 y0)
      (ad_lpmm_y A ρ lam hL b x0 z0 y0)
      x0
      z0
      y0 := by
  refine
    { x_zero := ?_
      z_zero := ?_
      y_zero := ?_
      x_step := ?_
      z_step := ?_
      y_step := ?_ }
  · -- The recursive trajectory starts from the prescribed initial `x`-state.
    exact ad_lpmm_x_zero A ρ lam hL b x0 z0 y0
  · -- The recursive trajectory starts from the prescribed initial `z`-state.
    exact ad_lpmm_z_zero A ρ lam hL b x0 z0 y0
  · -- The recursive trajectory starts from the prescribed initial multiplier.
    exact ad_lpmm_y_zero A ρ lam hL b x0 z0 y0
  · intro k
    -- Replace `x^(k+1)` by the explicit update and use the singleton prox bridge.
    simpa [ad_lpmm_x_succ] using
      ad_lpmm_x_update_mem_adlpmm_x_step
        A ρ lam hL
        (ad_lpmm_x A ρ lam hL b x0 z0 y0 k)
        (ad_lpmm_z A ρ lam hL b x0 z0 y0 k)
        (ad_lpmm_y A ρ lam hL b x0 z0 y0 k)
  · intro k
    -- Replace `z^(k+1)` by the explicit affine average and use the singleton prox bridge.
    simpa [ad_lpmm_z_succ] using
      ad_lpmm_z_update_mem_adlpmm_z_step
        A ρ b
        (ad_lpmm_x A ρ lam hL b x0 z0 y0 (k + 1))
        (ad_lpmm_z A ρ lam hL b x0 z0 y0 k)
        (ad_lpmm_y A ρ lam hL b x0 z0 y0 k)
  · intro k
    -- The multiplier clause is already the recursive state update.
    exact ad_lpmm_y_succ A ρ lam hL b x0 z0 y0 k

namespace IsADLPMMTrajectory

/-- For the Algorithm 15.10 specialization of the linear-composite AD-LPMM trajectory owner, the
canonical `x`-step is exactly the displayed soft-threshold update. -/
theorem x_step_eq_softThreshold
    {ρ : PosReal}
    {A : X →ₗ[ℝ] Y}
    {lam : NNReal}
    {hL : 0 < adlpmm_linearization_bound (1 : PosReal) A}
    {b : Y}
    {x : ℕ → X} {z y : ℕ → Y}
    {x0 : X} {z0 y0 : Y}
    (h : IsADLPMMTrajectory
      ρ
      A
      (-LinearMap.id)
      0
      (ad_lpmm_alpha_parameter A ρ hL)
      (ad_lpmm_beta_parameter ρ)
      (ad_lpmm_l1_regularizer lam)
      (denoising_data_fidelity b)
      x
      z
      y
      x0
      z0
      y0)
    (k : ℕ) :
    x (k + 1) = ad_lpmm_x_update A ρ lam hL (x k) (z k) (y k) := by
  have hlam :
      0 ≤ (lam : ℝ) / ((ad_lpmm_alpha_parameter A ρ hL : PosReal) : ℝ) := by
    -- The threshold parameter is nonnegative because `λ ≥ 0` and `α > 0`.
    exact div_nonneg lam.2 (show 0 ≤ ((ad_lpmm_alpha_parameter A ρ hL : PosReal) : ℝ) from
      (ad_lpmm_alpha_parameter A ρ hL : PosReal).2.le)
  -- Unfold the generic AD-LPMM `x`-step and simplify the linear-composite residual.
  have hx' := h.x_step k
  rw [mem_adlpmm_x_step_iff, scaledAdLpmmL1Regularizer_eq,
    prox_euclidean_l1_eq_singleton_softThreshold hlam, Set.mem_singleton_iff] at hx'
  simpa [sub_eq_add_neg, ad_lpmm_x_update_eq] using hx'

/-- For the Algorithm 15.10 specialization of the linear-composite AD-LPMM trajectory owner, the
canonical `z`-step is exactly the displayed affine-average update. -/
theorem z_step_eq_affineAverage
    {ρ : PosReal}
    {A : X →ₗ[ℝ] Y}
    {lam : NNReal}
    {hL : 0 < adlpmm_linearization_bound (1 : PosReal) A}
    {b : Y}
    {x : ℕ → X} {z y : ℕ → Y}
    {x0 : X} {z0 y0 : Y}
    (h : IsADLPMMTrajectory
      ρ
      A
      (-LinearMap.id)
      0
      (ad_lpmm_alpha_parameter A ρ hL)
      (ad_lpmm_beta_parameter ρ)
      (ad_lpmm_l1_regularizer lam)
      (denoising_data_fidelity b)
      x
      z
      y
      x0
      z0
      y0)
    (k : ℕ) :
    z (k + 1) = ad_lpmm_z_update A b ρ (x (k + 1)) (y k) := by
  have hρdivρ : ((ρ : ℝ) / (ρ : ℝ)) = 1 := by
    exact div_self (ne_of_gt ρ.2)
  have hcenter :
      z k + ((1 / (ρ : ℝ)) • y k + (-z k + A (x (k + 1)))) =
        A (x (k + 1)) + (1 / (ρ : ℝ)) • y k := by
    abel_nf
  -- Reduce the generic AD-LPMM `z`-step to the prox centered at `A (x (k + 1)) + (1 / ρ) • y k`.
  have hz := h.z_step k
  rw [mem_adlpmm_z_step_iff] at hz
  have hmem :
      z (k + 1) ∈
        prox[((((1 / ρ : PosReal) : EReal) • denoising_data_fidelity b))]
          (z k + ((1 / (ρ : ℝ)) • y k + (-z k + A (x (k + 1))))) := by
    simpa [ad_lpmm_beta_parameter_coe, PosReal.coe_div, sub_eq_add_neg, hρdivρ, one_smul,
      add_assoc, add_comm, add_left_comm] using hz
  have hz' :
      z (k + 1) ∈
        prox[((((1 / ρ : PosReal) : EReal) • denoising_data_fidelity b))]
          (A (x (k + 1)) + (1 / (ρ : ℝ)) • y k) := by
    exact hcenter ▸ hmem
  rw [prox_scaledDenoisingDataFidelity_eq_singleton, Set.mem_singleton_iff] at hz'
  simpa using hz'

end IsADLPMMTrajectory

end
