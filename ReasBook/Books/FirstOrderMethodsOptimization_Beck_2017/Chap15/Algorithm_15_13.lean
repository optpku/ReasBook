/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import FirstOrderMethodsOptimization_Beck_2017.Chap06.Definition_6_3
import FirstOrderMethodsOptimization_Beck_2017.Chap06.Proposition_6_2_1
import FirstOrderMethodsOptimization_Beck_2017.Chap15.Algorithm_15_5
import FirstOrderMethodsOptimization_Beck_2017.Chap15.Algorithm_15_12

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open scoped SoftThreshold

universe u v

section

variable {X : Type u} {ι : Type v}
variable [NormedAddCommGroup X] [InnerProductSpace ℝ X] [FiniteDimensional ℝ X]
variable [Fintype ι]

local notation "E" => EuclideanSpace ℝ ι

/- `lean_leansearch` is unavailable in this environment, so the owner/API choice was checked
against the local Chapter 15 files `Algorithm_15_5`, `Algorithm_15_12`, and `Algorithm_15_14`.

`source-facing`: the recursive iterate families for Algorithm 15.13.

The resulting owner split is:

- `core/canonical`: `IsADLPMMTrajectory` together with the generic
  `ADLPMMLinearizationParameter`;
- `bridge/view`: `admm_linear_composite_shifted_l1_regularizer` and
  `admm_linear_composite_shifted_l1_z_update` from `Algorithm_15_12` for the shifted `ℓ¹`
  residual block, together with `admm_multiplier_update` for the affine dual step;
- `source-facing`: only the explicit recursive iterate families specialized to `h₁ = 0` and
  `h₂(z) = ‖z - b‖₁`, together with the item-local parameter specializations
  `ad_lpmm_l1_residual_alpha_parameter` and
  `ad_lpmm_l1_residual_beta_parameter` and the positivity hypothesis
  `hL : 0 < adlpmm_linearization_bound (1 : PosReal) A` needed for the source step size
  `1 / L`.

The internal three-component recursion is therefore implementation scaffolding and stays private.
The public surface keeps only the iterate sequences and the source-facing step formulas, with the
shared chapter owners exposed as the canonical bridge theorems. -/

/-- Positivity of the item-local choice `α = ρ L` used in the shifted `ℓ¹` residual
specialization. -/
theorem ad_lpmm_l1_residual_alpha_pos
    (A : X →ₗ[ℝ] E) (ρ : PosReal)
    (hL : 0 < adlpmm_linearization_bound (1 : PosReal) A) :
    0 < (ρ : ℝ) * adlpmm_linearization_bound (1 : PosReal) A := by
  -- The specialized parameter `α = ρ L` is positive because both factors are positive.
  exact mul_pos ρ.2 hL

/-- The item-local choice `α = ρ L` dominates the canonical AD-LPMM lower bound for `A`. -/
theorem ad_lpmm_l1_residual_alpha_admissible
    (A : X →ₗ[ℝ] E) (ρ : PosReal) :
    adlpmm_linearization_bound ρ A ≤
      (ρ : ℝ) * adlpmm_linearization_bound (1 : PosReal) A := by
  -- Unfold the canonical linearization bound on both sides; the desired inequality is equality.
  simp [adlpmm_linearization_bound]

/-- The canonical `x`-linearization parameter `α = ρ L` for the shifted `ℓ¹` residual
specialization. -/
def ad_lpmm_l1_residual_alpha_parameter
    (A : X →ₗ[ℝ] E) (ρ : PosReal)
    (hL : 0 < adlpmm_linearization_bound (1 : PosReal) A) :
    ADLPMMLinearizationParameter ρ A :=
  ⟨⟨(ρ : ℝ) * adlpmm_linearization_bound (1 : PosReal) A,
      ad_lpmm_l1_residual_alpha_pos A ρ hL⟩,
    ad_lpmm_l1_residual_alpha_admissible A ρ⟩

/-- The canonical `z`-linearization parameter `β = ρ` for the shifted `ℓ¹` residual
specialization. -/
def ad_lpmm_l1_residual_beta_parameter
    (ρ : PosReal) :
    ADLPMMLinearizationParameter ρ (-LinearMap.id : E →ₗ[ℝ] E) :=
  ⟨ρ, adlpmm_linearization_bound_neg_id_le ρ⟩

private structure IterateState (X' E' : Type*) where
  x : X'
  z : E'
  y : E'

private def initialState (x0 : X) (z0 y0 : E) : IterateState X E :=
  { x := x0
    z := z0
    y := y0 }

private def stateUpdate
    (A : X →ₗ[ℝ] E) (ρ : PosReal) (b : E)
    (state : IterateState X E) : IterateState X E :=
  let xNext :=
    state.x - (1 / adlpmm_linearization_bound (1 : PosReal) A : ℝ) •
      A.adjoint (A state.x - state.z + (1 / (ρ : ℝ)) • state.y)
  let zNext := admm_linear_composite_shifted_l1_z_update ρ A b xNext state.y
  { x := xNext
    z := zNext
    y := admm_multiplier_update ρ A (-LinearMap.id) 0 state.y xNext zNext }

private def iterateState
    (A : X →ₗ[ℝ] E) (ρ : PosReal)
    (b : E) (x0 : X) (z0 y0 : E) :
    ℕ → IterateState X E :=
  Nat.rec (initialState x0 z0 y0) (fun _ state ↦ stateUpdate A ρ b state)

/-- The first iterate family for Algorithm 15.13:
the explicit `x`-sequence in the shifted `ℓ¹` residual specialization of AD-LPMM. -/
def ad_lpmm_l1_residual_x
    (A : X →ₗ[ℝ] E) (ρ : PosReal)
    (b : E) (x0 : X) (z0 y0 : E) :
    ℕ → X :=
  fun k ↦ (iterateState A ρ b x0 z0 y0 k).x

/-- The second iterate family for Algorithm 15.13:
the explicit shifted-soft-threshold `z`-sequence. -/
def ad_lpmm_l1_residual_z
    (A : X →ₗ[ℝ] E) (ρ : PosReal)
    (b : E) (x0 : X) (z0 y0 : E) :
    ℕ → E :=
  fun k ↦ (iterateState A ρ b x0 z0 y0 k).z

/-- The third iterate family for Algorithm 15.13:
the multiplier sequence for the shifted `ℓ¹` residual specialization. -/
def ad_lpmm_l1_residual_y
    (A : X →ₗ[ℝ] E) (ρ : PosReal)
    (b : E) (x0 : X) (z0 y0 : E) :
    ℕ → E :=
  fun k ↦ (iterateState A ρ b x0 z0 y0 k).y

section

variable (A : X →ₗ[ℝ] E) (ρ : PosReal)
variable (b : E) (x0 : X) (z0 y0 : E)

local notation "f2" => admm_linear_composite_shifted_l1_regularizer b
local notation "β" => ad_lpmm_l1_residual_beta_parameter ρ
local notation "x[" k "]" => ad_lpmm_l1_residual_x A ρ b x0 z0 y0 k
local notation "z[" k "]" => ad_lpmm_l1_residual_z A ρ b x0 z0 y0 k
local notation "y[" k "]" => ad_lpmm_l1_residual_y A ρ b x0 z0 y0 k

/-- The `x`-sequence starts from `x^0 = x0`. -/
theorem ad_lpmm_l1_residual_x_zero
    (A' : X →ₗ[ℝ] E) (ρ' : PosReal)
    (b' : E) (x0' : X) (z0' y0' : E) :
    ad_lpmm_l1_residual_x A' ρ' b' x0' z0' y0' 0 = x0' := by
  change (initialState x0' z0' y0').x = x0'
  rfl

/-- The `z`-sequence starts from `z^0 = z0`. -/
theorem ad_lpmm_l1_residual_z_zero
    (A' : X →ₗ[ℝ] E) (ρ' : PosReal)
    (b' : E) (x0' : X) (z0' y0' : E) :
    ad_lpmm_l1_residual_z A' ρ' b' x0' z0' y0' 0 = z0' := by
  change (initialState x0' z0' y0').z = z0'
  rfl

/-- The multiplier sequence starts from `y^0 = y0`. -/
theorem ad_lpmm_l1_residual_y_zero
    (A' : X →ₗ[ℝ] E) (ρ' : PosReal)
    (b' : E) (x0' : X) (z0' y0' : E) :
    ad_lpmm_l1_residual_y A' ρ' b' x0' z0' y0' 0 = y0' := by
  change (initialState x0' z0' y0').y = y0'
  rfl

/-- For Algorithm 15.13, at every iteration `k`, the next `x`-iterate is given by the displayed
gradient step. -/
theorem ad_lpmm_l1_residual_x_succ (k : ℕ) :
    x[k + 1] =
      x[k] - (1 / adlpmm_linearization_bound (1 : PosReal) A : ℝ) •
        A.adjoint (A x[k] - z[k] + (1 / (ρ : ℝ)) • y[k]) :=
  rfl

/-- At every iteration `k`, the next `z`-iterate is the canonical shifted `ℓ¹` update from
`Algorithm_15_12`. -/
theorem ad_lpmm_l1_residual_z_succ
    (A' : X →ₗ[ℝ] E) (ρ' : PosReal)
    (b' : E) (x0' : X) (z0' y0' : E) (k : ℕ) :
    ad_lpmm_l1_residual_z A' ρ' b' x0' z0' y0' (k + 1) =
      admm_linear_composite_shifted_l1_z_update ρ' A' b'
        (ad_lpmm_l1_residual_x A' ρ' b' x0' z0' y0' (k + 1))
        (ad_lpmm_l1_residual_y A' ρ' b' x0' z0' y0' k) := by
  change (stateUpdate A' ρ' b' (iterateState A' ρ' b' x0' z0' y0' k)).z =
    admm_linear_composite_shifted_l1_z_update ρ' A' b'
      (stateUpdate A' ρ' b' (iterateState A' ρ' b' x0' z0' y0' k)).x
      (iterateState A' ρ' b' x0' z0' y0' k).y
  rfl

/-- For Algorithm 15.13, expanding the recursive `z`-step gives the displayed shifted
soft-threshold formula. -/
theorem ad_lpmm_l1_residual_z_succ_eq
    (A' : X →ₗ[ℝ] E) (ρ' : PosReal)
    (b' : E) (x0' : X) (z0' y0' : E) (k : ℕ) :
    ad_lpmm_l1_residual_z A' ρ' b' x0' z0' y0' (k + 1) =
      T_[1 / (ρ' : ℝ)]
        (A' (ad_lpmm_l1_residual_x A' ρ' b' x0' z0' y0' (k + 1)) - b' +
          (1 / (ρ' : ℝ)) • (ad_lpmm_l1_residual_y A' ρ' b' x0' z0' y0' k)) + b' := by
  rw [ad_lpmm_l1_residual_z_succ A' ρ' b' x0' z0' y0' k,
    admm_linear_composite_shifted_l1_z_update_eq]
  simp [sub_eq_add_neg, add_comm, add_left_comm]

/-- At every iteration `k`, the next multiplier iterate is the canonical ADMM affine update. -/
theorem ad_lpmm_l1_residual_y_succ
    (A' : X →ₗ[ℝ] E) (ρ' : PosReal)
    (b' : E) (x0' : X) (z0' y0' : E) (k : ℕ) :
    ad_lpmm_l1_residual_y A' ρ' b' x0' z0' y0' (k + 1) =
      admm_multiplier_update ρ' A' (-LinearMap.id) 0
        (ad_lpmm_l1_residual_y A' ρ' b' x0' z0' y0' k)
        (ad_lpmm_l1_residual_x A' ρ' b' x0' z0' y0' (k + 1))
        (ad_lpmm_l1_residual_z A' ρ' b' x0' z0' y0' (k + 1)) := by
  change (stateUpdate A' ρ' b' (iterateState A' ρ' b' x0' z0' y0' k)).y =
    admm_multiplier_update ρ' A' (-LinearMap.id) 0
      (iterateState A' ρ' b' x0' z0' y0' k).y
      (stateUpdate A' ρ' b' (iterateState A' ρ' b' x0' z0' y0' k)).x
      (stateUpdate A' ρ' b' (iterateState A' ρ' b' x0' z0' y0' k)).z
  rfl

/-- For Algorithm 15.13, expanding the recursive multiplier step gives the displayed affine
update. -/
theorem ad_lpmm_l1_residual_y_succ_eq
    (A' : X →ₗ[ℝ] E) (ρ' : PosReal)
    (b' : E) (x0' : X) (z0' y0' : E) (k : ℕ) :
    ad_lpmm_l1_residual_y A' ρ' b' x0' z0' y0' (k + 1) =
      ad_lpmm_l1_residual_y A' ρ' b' x0' z0' y0' k +
        (ρ' : ℝ) •
          (A' (ad_lpmm_l1_residual_x A' ρ' b' x0' z0' y0' (k + 1)) -
            ad_lpmm_l1_residual_z A' ρ' b' x0' z0' y0' (k + 1)) := by
  rw [ad_lpmm_l1_residual_y_succ A' ρ' b' x0' z0' y0' k,
    admm_multiplier_update_eq]
  simp [sub_eq_add_neg, add_comm, add_left_comm]

end

/-- Helper for Algorithm 15.13: scaling the zero objective by `1 / α` still gives the zero
objective. -/
theorem ad_lpmm_l1_residual_scaled_zero_eq_zero
    (A : X →ₗ[ℝ] E) (ρ : PosReal)
    (hL : 0 < adlpmm_linearization_bound (1 : PosReal) A) :
    ((((1 / (ad_lpmm_l1_residual_alpha_parameter A ρ hL : PosReal) : PosReal) : EReal) •
      (0 : X → EReal)) : X → EReal) = 0 := by
  -- Scaling the zero objective leaves the zero objective pointwise.
  funext x
  simp

/-- Helper for Algorithm 15.13: the specialized coefficient `(ρ / α)` for `α = ρ L` reduces to
`1 / L`. -/
theorem ad_lpmm_l1_residual_rho_div_alpha_eq_inv_linearization_bound
    (A : X →ₗ[ℝ] E) (ρ : PosReal)
    (hL : 0 < adlpmm_linearization_bound (1 : PosReal) A) :
    (((ρ / (ad_lpmm_l1_residual_alpha_parameter A ρ hL : PosReal)) : PosReal) : ℝ) =
      (1 / adlpmm_linearization_bound (1 : PosReal) A : ℝ) := by
  have hρ0 : (ρ : ℝ) ≠ 0 := ne_of_gt ρ.2
  have hαcoe :
      (((ad_lpmm_l1_residual_alpha_parameter A ρ hL : PosReal) : ℝ)) =
        (ρ : ℝ) * adlpmm_linearization_bound (1 : PosReal) A := by
    -- The specialized parameter stores the textbook choice `α = ρ L` in its first component.
    rfl
  -- Cancel the common factor `ρ` to recover the gradient-step coefficient `1 / L`.
  rw [PosReal.coe_div, hαcoe]
  rw [div_mul_eq_div_div, div_self hρ0, one_div]

/-- Helper for Algorithm 15.13: the explicit gradient `x`-update with `h₁ = 0` is the canonical
linear-composite AD-LPMM `x`-step for `α = ρ L`. -/
theorem ad_lpmm_l1_residual_x_update_mem_adlpmm_x_step
    (A : X →ₗ[ℝ] E) (ρ : PosReal)
    (hL : 0 < adlpmm_linearization_bound (1 : PosReal) A)
    (xk : X) (zk yk : E) :
    xk - (1 / adlpmm_linearization_bound (1 : PosReal) A : ℝ) •
        A.adjoint (A xk - zk + (1 / (ρ : ℝ)) • yk) ∈
      adlpmm_x_step (0 : X → EReal) ρ (ad_lpmm_l1_residual_alpha_parameter A ρ hL) A
        (-LinearMap.id) 0 xk zk yk := by
  -- Rewrite the generic AD-LPMM `x`-step to the prox owner and collapse the zero objective.
  rw [mem_adlpmm_x_step_iff, ad_lpmm_l1_residual_scaled_zero_eq_zero, prox_zero_eq_singleton,
    Set.mem_singleton_iff]
  -- The remaining equality is the displayed gradient step after normalizing `ρ / α`.
  calc
    xk - (1 / adlpmm_linearization_bound (1 : PosReal) A : ℝ) •
        A.adjoint (A xk - zk + (1 / (ρ : ℝ)) • yk)
      = xk -
          (((ρ / (ad_lpmm_l1_residual_alpha_parameter A ρ hL : PosReal)) : PosReal) : ℝ) •
            A.adjoint (A xk - zk + (1 / (ρ : ℝ)) • yk) := by
              rw [ad_lpmm_l1_residual_rho_div_alpha_eq_inv_linearization_bound]
    _ = xk -
          (((ρ / (ad_lpmm_l1_residual_alpha_parameter A ρ hL : PosReal)) : PosReal) : ℝ) •
            A.adjoint (A xk + (-LinearMap.id) zk - 0 + (1 / (ρ : ℝ)) • yk) := by
              simp [sub_eq_add_neg, add_comm, add_left_comm]

/-- The explicit Algorithm 15.13 `x`-update belongs to the canonical linear-composite AD-LPMM
`x`-step for `h₁ = 0` and `α = ρ L`. -/
theorem ad_lpmm_l1_residual_x_succ_mem_adlpmm_x_step
    (A : X →ₗ[ℝ] E) (ρ : PosReal) (b : E) (x0 : X) (z0 y0 : E)
    (hL : 0 < adlpmm_linearization_bound (1 : PosReal) A) (k : ℕ) :
    ad_lpmm_l1_residual_x A ρ b x0 z0 y0 (k + 1) ∈
      adlpmm_x_step (0 : X → EReal) ρ (ad_lpmm_l1_residual_alpha_parameter A ρ hL) A
        (-LinearMap.id) 0
        (ad_lpmm_l1_residual_x A ρ b x0 z0 y0 k)
        (ad_lpmm_l1_residual_z A ρ b x0 z0 y0 k)
        (ad_lpmm_l1_residual_y A ρ b x0 z0 y0 k) := by
  -- First unfold the recursive successor once, then reuse the stable one-step bridge.
  change
    ad_lpmm_l1_residual_x A ρ b x0 z0 y0 k -
        (1 / adlpmm_linearization_bound (1 : PosReal) A : ℝ) •
          A.adjoint
            (A (ad_lpmm_l1_residual_x A ρ b x0 z0 y0 k) -
              ad_lpmm_l1_residual_z A ρ b x0 z0 y0 k +
              (1 / (ρ : ℝ)) • ad_lpmm_l1_residual_y A ρ b x0 z0 y0 k) ∈
      adlpmm_x_step (0 : X → EReal) ρ (ad_lpmm_l1_residual_alpha_parameter A ρ hL) A
        (-LinearMap.id) 0
        (ad_lpmm_l1_residual_x A ρ b x0 z0 y0 k)
        (ad_lpmm_l1_residual_z A ρ b x0 z0 y0 k)
        (ad_lpmm_l1_residual_y A ρ b x0 z0 y0 k)
  exact
    ad_lpmm_l1_residual_x_update_mem_adlpmm_x_step
      A ρ hL
      (ad_lpmm_l1_residual_x A ρ b x0 z0 y0 k)
      (ad_lpmm_l1_residual_z A ρ b x0 z0 y0 k)
      (ad_lpmm_l1_residual_y A ρ b x0 z0 y0 k)

section

omit [FiniteDimensional ℝ X]

/-- Helper for Algorithm 15.13: the explicit shifted-soft-threshold `z`-update is the canonical
linear-composite AD-LPMM `z`-step for `β = ρ`. -/
theorem ad_lpmm_l1_residual_z_update_mem_adlpmm_z_step
    (A : X →ₗ[ℝ] E) (ρ : PosReal)
    (b : E) (xNext : X) (zk yk : E) :
    admm_linear_composite_shifted_l1_z_update ρ A b xNext yk ∈
      adlpmm_z_step (admm_linear_composite_shifted_l1_regularizer b) ρ
        (((ad_lpmm_l1_residual_beta_parameter (ι := ι) ρ) :
            ADLPMMLinearizationParameter ρ (-LinearMap.id : E →ₗ[ℝ] E))) A
        (-LinearMap.id : E →ₗ[ℝ] E) 0 xNext zk yk := by
  have hρ0 : (ρ : ℝ) ≠ 0 := ne_of_gt ρ.2
  have hρdivβ :
      (((ρ /
          (((ad_lpmm_l1_residual_beta_parameter (ι := ι) ρ) :
              ADLPMMLinearizationParameter ρ (-LinearMap.id : E →ₗ[ℝ] E)) : PosReal)) :
          PosReal) : ℝ) = 1 := by
    -- The source specialization fixes `β = ρ`, so the AD-LPMM `z`-center uses coefficient `1`.
    rw [PosReal.coe_div]
    change (ρ : ℝ) / (ρ : ℝ) = 1
    exact div_self hρ0
  have hcenter :
      zk + ((1 / (ρ : ℝ)) • yk + (-zk + A xNext)) =
        A xNext + (1 / (ρ : ℝ)) • yk := by
    -- Normalize the generic `B = -I` center to the shifted `ℓ¹` prox center.
    abel_nf
  -- Rewrite the generic AD-LPMM `z`-step to prox membership and transport the owner center.
  rw [mem_adlpmm_z_step_iff]
  have hsimple :
      admm_linear_composite_shifted_l1_z_update ρ A b xNext yk ∈
        prox[((((1 / ρ : PosReal) : EReal) • admm_linear_composite_shifted_l1_regularizer b))]
          (A xNext + (1 / (ρ : ℝ)) • yk) :=
    admm_linear_composite_shifted_l1_z_update_mem_prox ρ A b xNext yk
  have hmem :
      admm_linear_composite_shifted_l1_z_update ρ A b xNext yk ∈
        prox[((((1 / ρ : PosReal) : EReal) • admm_linear_composite_shifted_l1_regularizer b))]
          (zk + ((1 / (ρ : ℝ)) • yk + (-zk + A xNext))) := by
    exact hcenter.symm ▸ hsimple
  have htarget :
      zk -
          (((ρ /
                (((ad_lpmm_l1_residual_beta_parameter (ι := ι) ρ) :
                    ADLPMMLinearizationParameter ρ (-LinearMap.id : E →ₗ[ℝ] E)) : PosReal)) :
              PosReal) : ℝ) •
            (LinearMap.adjoint (-LinearMap.id : E →ₗ[ℝ] E))
              (A xNext + (-LinearMap.id : E →ₗ[ℝ] E) zk - 0 + (1 / (ρ : ℝ)) • yk) =
        zk + ((1 / (ρ : ℝ)) • yk + (-zk + A xNext)) := by
    -- Normalize the generic AD-LPMM `z`-center after specializing `β = ρ` and `B = -I`.
    simp [hρdivβ, sub_eq_add_neg, add_comm, add_left_comm]
  rw [htarget]
  simpa [ad_lpmm_l1_residual_beta_parameter] using hmem

end

/-- The explicit shifted `ℓ¹` update belongs to the canonical linear-composite AD-LPMM `z`-step
for `β = ρ`. -/
theorem ad_lpmm_l1_residual_z_succ_mem_adlpmm_z_step
    (A : X →ₗ[ℝ] E) (ρ : PosReal)
    (b : E) (x0 : X) (z0 y0 : E) (k : ℕ) :
    ad_lpmm_l1_residual_z A ρ b x0 z0 y0 (k + 1) ∈
      adlpmm_z_step (admm_linear_composite_shifted_l1_regularizer b) ρ
        (ad_lpmm_l1_residual_beta_parameter (ι := ι) ρ) A (-LinearMap.id) 0
        (ad_lpmm_l1_residual_x A ρ b x0 z0 y0 (k + 1))
        (ad_lpmm_l1_residual_z A ρ b x0 z0 y0 k)
        (ad_lpmm_l1_residual_y A ρ b x0 z0 y0 k) := by
  change
    admm_linear_composite_shifted_l1_z_update ρ A b
        (ad_lpmm_l1_residual_x A ρ b x0 z0 y0 (k + 1))
        (ad_lpmm_l1_residual_y A ρ b x0 z0 y0 k) ∈
      adlpmm_z_step (admm_linear_composite_shifted_l1_regularizer b) ρ
        (ad_lpmm_l1_residual_beta_parameter (ι := ι) ρ) A (-LinearMap.id) 0
        (ad_lpmm_l1_residual_x A ρ b x0 z0 y0 (k + 1))
        (ad_lpmm_l1_residual_z A ρ b x0 z0 y0 k)
        (ad_lpmm_l1_residual_y A ρ b x0 z0 y0 k)
  exact
    ad_lpmm_l1_residual_z_update_mem_adlpmm_z_step
      (A := A) (ρ := ρ) (b := b)
      (xNext := ad_lpmm_l1_residual_x A ρ b x0 z0 y0 (k + 1))
      (zk := ad_lpmm_l1_residual_z A ρ b x0 z0 y0 k)
      (yk := ad_lpmm_l1_residual_y A ρ b x0 z0 y0 k)

/-- Algorithm 15.13: the explicit iterates form the canonical linear-composite AD-LPMM trajectory
for `h₁ = 0` and `h₂(z) = ‖z - b‖₁`, under the source specialization `α = ρ L`
and `β = ρ`. -/
theorem ad_lpmm_l1_residual_trajectory
    (A : X →ₗ[ℝ] E) (ρ : PosReal)
    (hL : 0 < adlpmm_linearization_bound (1 : PosReal) A)
    (b : E) (x0 : X) (z0 y0 : E) :
    IsADLPMMTrajectory ρ A (-LinearMap.id) 0
      (ad_lpmm_l1_residual_alpha_parameter A ρ hL) (ad_lpmm_l1_residual_beta_parameter ρ)
      (0 : X → EReal) (admm_linear_composite_shifted_l1_regularizer b)
      (ad_lpmm_l1_residual_x A ρ b x0 z0 y0)
      (ad_lpmm_l1_residual_z A ρ b x0 z0 y0)
      (ad_lpmm_l1_residual_y A ρ b x0 z0 y0)
      x0 z0 y0 := by
  refine
    { x_zero := ?_
      z_zero := ?_
      y_zero := ?_
      x_step := ?_
      z_step := ?_
      y_step := ?_ }
  · -- The recursive trajectory starts from the prescribed initial `x`-state.
    exact ad_lpmm_l1_residual_x_zero A ρ b x0 z0 y0
  · -- The recursive trajectory starts from the prescribed initial `z`-state.
    exact ad_lpmm_l1_residual_z_zero A ρ b x0 z0 y0
  · -- The recursive trajectory starts from the prescribed initial multiplier.
    exact ad_lpmm_l1_residual_y_zero A ρ b x0 z0 y0
  · intro k
    -- The recursive `x`-update is exactly the canonical AD-LPMM `x`-step membership.
    simpa using
      (ad_lpmm_l1_residual_x_succ_mem_adlpmm_x_step
        (A := A) (ρ := ρ) (b := b) (x0 := x0) (z0 := z0) (y0 := y0) hL k)
  · intro k
    -- The recursive `z`-update is exactly the canonical shifted `ℓ¹` AD-LPMM `z`-step.
    simpa using
      (ad_lpmm_l1_residual_z_succ_mem_adlpmm_z_step
        (A := A) (ρ := ρ) (b := b) (x0 := x0) (z0 := z0) (y0 := y0) k)
  · intro k
    -- The multiplier recursion was defined from the canonical ADMM affine update.
    rfl

end

end
