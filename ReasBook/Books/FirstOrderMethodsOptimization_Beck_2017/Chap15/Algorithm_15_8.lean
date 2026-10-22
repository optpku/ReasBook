/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import Mathlib
import FirstOrderMethodsOptimization_Beck_2017.Chap15.Algorithm_15_5
import FirstOrderMethodsOptimization_Beck_2017.Chap15.Algorithm_15_6

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u v

section

variable {X : Type u} {Y : Type v}
variable [NormedAddCommGroup X] [InnerProductSpace ℝ X] [FiniteDimensional ℝ X]
variable [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [FiniteDimensional ℝ Y]

/- `prompt_add/` is absent in this workspace, so the owner choice is sampled from the nearby
Chapter 15 AD-LPMM and linear-composite ADMM files together with the Chapter 6 proximal owner.

The textbook formulas in Algorithm 15.8 are `source-facing`, but the owner abstraction is already
present upstream:
- `core/canonical`: `ADLPMMLinearizationParameter`,
  `adlpmm_x_step`, `adlpmm_z_step`, and `IsADLPMMTrajectory` from Algorithm 15.5;
- `core/canonical`: `admm_multiplier_update` from Algorithm 15.2, whose
  linear-composite specialization `A x - z = 0` is simplified directly here;
- `bridge/view`: the linear-composite specialization `B = -LinearMap.id`, `c = 0`, together with
  the textbook inequality `ρ ≤ β` recovered from the specialized canonical `β` under the usual
  nontriviality hypothesis on the ambient space.

Primitive data therefore remain the generic AD-LPMM parameters and iterates. This file keeps the
source-facing linear-composite specialization layer as thin bridge/view API over the generic
owners, together with the corresponding simplification lemmas. -/

/- Algorithm 15.8 trajectories are the generic AD-LPMM trajectories specialized to `B = -I`
and `c = 0`. -/
recall IsADLPMMTrajectory

-- Proof sketch: specialize `mem_adlpmm_x_step_iff` from Algorithm 15.5 at `B = -LinearMap.id`
-- and `c = 0`, then simplify the residual `A x^k + (-id) z^k - 0`.
/-- In the linear-composite specialization `B = -I`, `c = 0`, membership in the AD-LPMM
`x`-update set is exactly the textbook proximal clause
`x^(k+1) ∈ prox[((1 / α) f₁)] (x^k - (ρ / α) Aᵀ (A x^k - z^k + (1 / ρ) y^k))`. -/
@[simp] theorem mem_adlpmm_x_step_linear_composite_iff
    {f₁ : X → EReal}
    {ρ : PosReal}
    {A : X →ₗ[ℝ] Y}
    {α : PosReal}
    {xk xNext : X}
    {zk yk : Y} :
    xNext ∈ adlpmm_x_step f₁ ρ α A (-LinearMap.id) 0 xk zk yk ↔
      xNext ∈ prox[((((1 / α : PosReal) : EReal) • f₁))]
        (xk - ((ρ / α : PosReal) : ℝ) •
          A.adjoint (A xk - zk + (1 / (ρ : ℝ)) • yk)) := by
  simp [mem_adlpmm_x_step_iff, sub_eq_add_neg, add_left_comm, add_comm]

-- Proof sketch: specialize `mem_adlpmm_z_step_iff` from Algorithm 15.5 at `B = -LinearMap.id`
-- and `c = 0`, then simplify the resulting residual and adjoint.
/-- In the linear-composite specialization `B = -I`, `c = 0`, membership in the AD-LPMM
`z`-update set is exactly the textbook proximal clause
`z^(k+1) ∈ prox[((1 / β) f₂)] (z^k + (ρ / β) (A x^(k+1) - z^k + (1 / ρ) y^k))`. -/
@[simp] theorem mem_adlpmm_z_step_linear_composite_iff
    {f₂ : Y → EReal}
    {ρ β : PosReal}
    {A : X →ₗ[ℝ] Y}
    {xNext : X}
    {zk yk zNext : Y} :
    zNext ∈ adlpmm_z_step f₂ ρ β A (-LinearMap.id) 0 xNext zk yk ↔
      zNext ∈ prox[((((1 / β : PosReal) : EReal) • f₂))]
        (zk + ((ρ / β : PosReal) : ℝ) •
          (A xNext - zk + (1 / (ρ : ℝ)) • yk)) := by
  simp [mem_adlpmm_z_step_iff, sub_eq_add_neg, add_left_comm, add_comm]

namespace IsADLPMMTrajectory

/-- In the linear-composite specialization of Algorithm 15.8, the generic AD-LPMM `x`-step is
exactly the textbook proximal update from part (a). -/
theorem x_step_linear_composite
    {ρ : PosReal}
    {A : X →ₗ[ℝ] Y}
    {α : ADLPMMLinearizationParameter ρ A}
    {β : ADLPMMLinearizationParameter ρ (-LinearMap.id : Y →ₗ[ℝ] Y)}
    {h₁ : X → EReal} {h₂ : Y → EReal}
    {x : ℕ → X} {z y : ℕ → Y}
    {x0 : X} {z0 y0 : Y}
    (h : IsADLPMMTrajectory ρ A (-LinearMap.id) 0 α β h₁ h₂ x z y x0 z0 y0)
    (k : ℕ) :
    x (k + 1) ∈ prox[((((1 / α : PosReal) : EReal) • h₁))]
      (x k - ((ρ / α : PosReal) : ℝ) •
        A.adjoint (A (x k) - z k + (1 / (ρ : ℝ)) • y k)) := by
  simpa using mem_adlpmm_x_step_linear_composite_iff.mp (h.x_step k)

/-- In the linear-composite specialization of Algorithm 15.8, the generic AD-LPMM `z`-step is
exactly the textbook proximal update from part (b). -/
theorem z_step_linear_composite
    {ρ : PosReal}
    {A : X →ₗ[ℝ] Y}
    {α : ADLPMMLinearizationParameter ρ A}
    {β : ADLPMMLinearizationParameter ρ (-LinearMap.id : Y →ₗ[ℝ] Y)}
    {h₁ : X → EReal} {h₂ : Y → EReal}
    {x : ℕ → X} {z y : ℕ → Y}
    {x0 : X} {z0 y0 : Y}
    (h : IsADLPMMTrajectory ρ A (-LinearMap.id) 0 α β h₁ h₂ x z y x0 z0 y0)
    (k : ℕ) :
    z (k + 1) ∈ prox[((((1 / β : PosReal) : EReal) • h₂))]
      (z k + ((ρ / β : PosReal) : ℝ) •
        (A (x (k + 1)) - z k + (1 / (ρ : ℝ)) • y k)) := by
  simpa using mem_adlpmm_z_step_linear_composite_iff.mp (h.z_step k)

/-- In the linear-composite specialization of Algorithm 15.8, the generic AD-LPMM multiplier
update simplifies to `y^(k+1) = y^k + ρ (A x^(k+1) - z^(k+1))`. -/
theorem y_step_linear_composite
    {ρ : PosReal}
    {A : X →ₗ[ℝ] Y}
    {α : ADLPMMLinearizationParameter ρ A}
    {β : ADLPMMLinearizationParameter ρ (-LinearMap.id : Y →ₗ[ℝ] Y)}
    {h₁ : X → EReal} {h₂ : Y → EReal}
    {x : ℕ → X} {z y : ℕ → Y}
    {x0 : X} {z0 y0 : Y}
    (h : IsADLPMMTrajectory ρ A (-LinearMap.id) 0 α β h₁ h₂ x z y x0 z0 y0)
    (k : ℕ) :
    y (k + 1) = y k + (ρ : ℝ) • (A (x (k + 1)) - z (k + 1)) := by
  simpa using
    Eq.trans (h.y_step k)
      (admm_multiplier_update_linear_composite_eq ρ A (y k) (x (k + 1)) (z (k + 1)))

end IsADLPMMTrajectory

end
