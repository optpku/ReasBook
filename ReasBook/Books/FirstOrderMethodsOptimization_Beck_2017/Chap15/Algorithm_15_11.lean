/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import Mathlib
import FirstOrderMethodsOptimization_Beck_2017.Chap15.Algorithm_15_6
import FirstOrderMethodsOptimization_Beck_2017.Chap15.Algorithm_15_12

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u v

section

variable {X : Type u} {ι : Type v}
variable [AddCommMonoid X] [Module ℝ X]
variable [Fintype ι]

local notation "Y" => EuclideanSpace ℝ ι

/- `prompt_add/` is absent in this workspace, so the owner choice is sampled from the nearby
Chapter 15 ADMM files.

This item is `source-facing`: Algorithm 15.11 keeps the `x`-subproblem set-valued and records the
initialization by `z⁰` and `y⁰`, while its part-(b) `z`-formula is already the same canonical
linear-composite soft-threshold map used elsewhere in the chapter. Domain sampling against
`Algorithm_15_3`, `Algorithm_15_6`, and `Algorithm_15_12` shows the following split.

- `core/canonical`: `admm_x_update_argmin`, `admm_z_update_argmin`, and
  `admm_multiplier_update` from the alternating-ADMM owner;
- `bridge/view`: `admm_linear_composite_shifted_l1_z_update` from `Algorithm_15_12` as the
  shared owner of the shifted soft-threshold `z`-update;
- `bridge/view`: `mem_admm_x_update_argmin_linear_composite_iff`,
  `admm_multiplier_update_linear_composite_eq`, and the specialized proximal/argmin theorems for
  `admm_linear_composite_shifted_l1_z_update`;
- `source-facing`: only the trajectory wrapper that records the source's initialization by `z⁰`
  and `y⁰` while leaving the `x`-step set-valued.

Accordingly, the duplicate version-1 `z`-update owner is deleted here. Algorithm 15.11 now reuses
the canonical Chapter 15 linear-composite `z`-update directly and keeps only the source-facing
trajectory package as primitive public data. -/

/-- Algorithm 15.11: given initial iterates `z^0 = z0` and `y^0 = y0` and a positive penalty
parameter `ρ`, the sequences `x`, `z`, and `y` form the version-1 ADMM trajectory when, for every
iteration `k`, `x^(k+1)` belongs to the canonical linear-composite ADMM `x`-argmin set,
`z^(k+1)` is the canonical shifted soft-threshold update from part (b), and
`y^(k+1)` is the canonical affine multiplier update specialized to `A x - z = 0`.

This is the `source-facing` view of alternating ADMM specialized to
`h₁ = 0`, `h₂(z) = ‖z - b‖₁`, `B = -I`, and `c = 0`; the source-specific content here is only the
trajectory packaging by `z⁰` and `y⁰`. -/
class IsADMMSoftThresholdTrajectoryV1
    (ρ : PosReal)
    (A : X →ₗ[ℝ] Y)
    (b : Y)
    (x : ℕ → X)
    (z y : ℕ → Y)
    (z0 y0 : Y) : Prop where
  z_zero : z 0 = z0
  y_zero : y 0 = y0
  x_step (k : ℕ) :
    x (k + 1) ∈
      admm_x_update_argmin
        ρ
        (fun _ : X ↦ (0 : EReal))
        A
        (-LinearMap.id)
        0
        (z k)
        (y k)
  z_step (k : ℕ) :
    z (k + 1) = admm_linear_composite_shifted_l1_z_update ρ A b (x (k + 1)) (y k)
  y_step (k : ℕ) :
    y (k + 1) =
      admm_multiplier_update ρ A (-LinearMap.id) 0 (y k) (x (k + 1)) (z (k + 1))

namespace IsADMMSoftThresholdTrajectoryV1

/-- A source-facing Algorithm 15.11 trajectory canonically determines the alternating-ADMM
trajectory for `h₁ = 0`, `h₂(z) = ‖z - b‖₁`, `B = -I`, and `c = 0`, with the initial point
`x^0` read off as `x 0`. -/
theorem toIsADMMAlternatingTrajectory
    {ρ : PosReal}
    {A : X →ₗ[ℝ] Y}
    {b : Y}
    {x : ℕ → X}
    {z y : ℕ → Y}
    {z0 y0 : Y}
    (h : IsADMMSoftThresholdTrajectoryV1 ρ A b x z y z0 y0) :
    IsADMMAlternatingTrajectory
      ρ
      (fun _ : X ↦ (0 : EReal))
      (admm_linear_composite_shifted_l1_regularizer b)
      A
      (-LinearMap.id)
      0
      x
      z
      y
      (x 0)
      z0
      y0 where
  x_zero := rfl
  z_zero := h.z_zero
  y_zero := h.y_zero
  x_step := h.x_step
  z_step k := by
    rw [h.z_step k]
    exact admm_linear_composite_shifted_l1_z_update_mem_argmin ρ A b (x (k + 1)) (y k)
  y_step := h.y_step

/-- In Algorithm 15.11, the canonical linear-composite ADMM `x`-step is exactly the displayed
global minimization problem `x ↦ (ρ / 2) ‖A x - z^k + (1 / ρ) y^k‖²`. -/
theorem x_step_isMinOn
    {ρ : PosReal}
    {A : X →ₗ[ℝ] Y}
    {b : Y}
    {x : ℕ → X}
    {z y : ℕ → Y}
    {z0 y0 : Y}
    (h : IsADMMSoftThresholdTrajectoryV1 ρ A b x z y z0 y0)
    (k : ℕ) :
    IsMinOn
      (fun xNext : X ↦
        ((((ρ : ℝ) / 2) * ‖A xNext - z k + (1 / (ρ : ℝ)) • y k‖ ^ (2 : ℕ) : ℝ) : EReal))
      Set.univ
      (x (k + 1)) := by
  simpa using h.toIsADMMAlternatingTrajectory.x_step_linear_composite k

/-- Along an Algorithm 15.11 trajectory, the explicit thresholded `z`-step is the canonical
proximal point of the shifted `ℓ¹` block. -/
theorem z_step_mem_prox
    {ρ : PosReal}
    {A : X →ₗ[ℝ] Y}
    {b : Y}
    {x : ℕ → X}
    {z y : ℕ → Y}
    {z0 y0 : Y}
    (h : IsADMMSoftThresholdTrajectoryV1 ρ A b x z y z0 y0)
    (k : ℕ) :
    z (k + 1) ∈
      prox[((((1 / ρ : PosReal) : EReal) • admm_linear_composite_shifted_l1_regularizer b))]
        (A (x (k + 1)) + (1 / (ρ : ℝ)) • y k) := by
  simpa using h.toIsADMMAlternatingTrajectory.z_step_linear_composite k

/-- Along an Algorithm 15.11 trajectory, the explicit thresholded `z`-step belongs to the
canonical linear-composite ADMM `z`-argmin set for the shifted `ℓ¹` block. -/
theorem z_step_mem_argmin
    {ρ : PosReal}
    {A : X →ₗ[ℝ] Y}
    {b : Y}
    {x : ℕ → X}
    {z y : ℕ → Y}
    {z0 y0 : Y}
    (h : IsADMMSoftThresholdTrajectoryV1 ρ A b x z y z0 y0)
    (k : ℕ) :
    z (k + 1) ∈
      admm_z_update_argmin
        ρ
        (admm_linear_composite_shifted_l1_regularizer b)
        A
        (-LinearMap.id)
        0
        (x (k + 1))
        (y k) := by
  exact h.toIsADMMAlternatingTrajectory.z_step k

/-- Along an Algorithm 15.11 trajectory, the canonical linear-composite ADMM multiplier update
reduces to the displayed affine recursion `y^(k+1) = y^k + ρ (A x^(k+1) - z^(k+1))`. -/
theorem y_step_eq
    {ρ : PosReal}
    {A : X →ₗ[ℝ] Y}
    {b : Y}
    {x : ℕ → X}
    {z y : ℕ → Y}
    {z0 y0 : Y}
    (h : IsADMMSoftThresholdTrajectoryV1 ρ A b x z y z0 y0)
    (k : ℕ) :
    y (k + 1) = y k + (ρ : ℝ) • (A (x (k + 1)) - z (k + 1)) := by
  simpa using h.toIsADMMAlternatingTrajectory.y_step_linear_composite k

end IsADMMSoftThresholdTrajectoryV1

/-- An Algorithm 15.11 trajectory starts from the prescribed initial iterates
`z^0 = z0` and `y^0 = y0`. -/
theorem is_admm_soft_threshold_trajectory_v1_zero
    {ρ : PosReal}
    {A : X →ₗ[ℝ] Y}
    {b : Y}
    {x : ℕ → X}
    {z y : ℕ → Y}
    {z0 y0 : Y}
    (h : IsADMMSoftThresholdTrajectoryV1 ρ A b x z y z0 y0) :
    z 0 = z0 ∧ y 0 = y0 :=
  ⟨h.z_zero, h.y_zero⟩

/-- At every iteration `k`, an Algorithm 15.11 trajectory satisfies the canonical ADMM
`x`-subproblem clause, the explicit shifted soft-threshold `z`-update, and the affine multiplier
recursion. -/
theorem is_admm_soft_threshold_trajectory_v1_step
    {ρ : PosReal}
    {A : X →ₗ[ℝ] Y}
    {b : Y}
    {x : ℕ → X}
    {z y : ℕ → Y}
    {z0 y0 : Y}
    (h : IsADMMSoftThresholdTrajectoryV1 ρ A b x z y z0 y0)
    (k : ℕ) :
    x (k + 1) ∈
        admm_x_update_argmin
          ρ
          (fun _ : X ↦ (0 : EReal))
          A
          (-LinearMap.id)
          0
          (z k)
          (y k) ∧
      z (k + 1) = admm_linear_composite_shifted_l1_z_update ρ A b (x (k + 1)) (y k) ∧
      y (k + 1) =
        admm_multiplier_update ρ A (-LinearMap.id) 0 (y k) (x (k + 1)) (z (k + 1)) :=
  ⟨h.x_step k, h.z_step k, h.y_step k⟩

end
