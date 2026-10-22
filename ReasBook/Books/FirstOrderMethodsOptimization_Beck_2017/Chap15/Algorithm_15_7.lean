/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import Mathlib
import FirstOrderMethodsOptimization_Beck_2017.Chap06.Lemma_6_68
import FirstOrderMethodsOptimization_Beck_2017.Chap15.Algorithm_15_6

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u v

open ContinuousLinearMap
open scoped InnerProduct

/- `prompt_add/` is absent in this workspace, so the design is sampled from the nearby Chapter 15
ADMM files together with the Chapter 6 proximal owner.

This item is `source-facing`: Algorithm 15.7 gives an explicit linear solve for `x^(k+1)`, two
proximal updates for `z^(k+1)` and `w^(k+1)`, and two affine multiplier updates for
`y₁^(k+1)` and `y₂^(k+1)`. The canonical local owners are therefore:
- `ContinuousLinearMap.IsInvertible` together with the canonical inverse map for the displayed
  resolvent `(I + Aᵀ A)⁻¹`;
- `prox[...]` from Chapter 6 for the two proximal steps, keeping the source semantics without
  prematurely choosing proximal points;
- `admm_multiplier_update` from Algorithm 15.2 together with the canonical specialization
  `admm_multiplier_update_linear_composite_eq` from Algorithm 15.6 for the two affine multiplier
  steps `A x - z = 0` and `x - w = 0`;
- a single Prop-valued trajectory class packaging the initialization and per-iteration update
  clauses. -/

section

variable {X : Type u} {Y : Type v}
variable [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
variable [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [CompleteSpace Y]

/-- The ADMM version-2 normal operator `I + Aᵀ A` is invertible because `Aᵀ A` is positive and
its spectrum is contained in `[0, ∞)`. -/
lemma admm_sum_composition_v2_x_resolvent_isInvertible (A : X →L[ℝ] Y) :
    (1 + A† ∘L A).IsInvertible := by
  simpa [one_smul, add_comm] using
    (gram_shift_isInvertible_of_pos A.adjoint 1 zero_lt_one)

/-- The explicit `x`-update in Algorithm 15.7:
`x^(k+1) = (I + Aᵀ A)⁻¹ (Aᵀ (z^k - (1 / ρ) y₁^k) + w^k - (1 / ρ) y₂^k)`. -/
def admm_sum_composition_v2_x_update
    (ρ : PosReal) (A : X →L[ℝ] Y) (zk y1k : Y) (wk y2k : X) : X :=
  ((1 + A† ∘L A).inverse)
    (A.adjoint (zk - (1 / (ρ : ℝ)) • y1k) + (wk - (1 / (ρ : ℝ)) • y2k))

-- Proof sketch: unfold `admm_sum_composition_v2_x_update`; the right-hand side is exactly the
-- displayed linear-solve formula defining `x^(k+1)` in Algorithm 15.7.
/-- Expanding `admm_sum_composition_v2_x_update` gives the resolvent formula
`(I + Aᵀ A)⁻¹ (Aᵀ (z^k - (1 / ρ) y₁^k) + w^k - (1 / ρ) y₂^k)`. -/
@[simp] theorem admm_sum_composition_v2_x_update_eq
    (ρ : PosReal) (A : X →L[ℝ] Y) (zk y1k : Y) (wk y2k : X) :
    admm_sum_composition_v2_x_update ρ A zk y1k wk y2k =
      ((1 + A† ∘L A).inverse)
        (A.adjoint (zk - (1 / (ρ : ℝ)) • y1k) + (wk - (1 / (ρ : ℝ)) • y2k)) := rfl

end

section

variable {X : Type u} {Y : Type v}
variable [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
variable [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [CompleteSpace Y]

/-- Algorithm 15.7: given initial iterates `x^0`, `w^0`, `y₂^0` in `X`, `z^0`, `y₁^0` in `Y`,
and a positive parameter `ρ`, the sequences `x`, `z`, `w`, `y₁`, and `y₂` follow ADMM version 2
for minimizing `f₁(x) + f₂(A x)` when each iteration satisfies the displayed linear `x`-solve,
the proximal updates
`z^(k+1) ∈ prox[((1 / ρ) f₂)] (A x^(k+1) + (1 / ρ) y₁^k)` and
`w^(k+1) ∈ prox[((1 / ρ) f₁)] (x^(k+1) + (1 / ρ) y₂^k)`,
and the two affine multiplier recursions
`y₁^(k+1) = y₁^k + ρ (A x^(k+1) - z^(k+1))` and
`y₂^(k+1) = y₂^k + ρ (x^(k+1) - w^(k+1))`. -/
class IsADMMSumCompositionTrajectoryV2
    (ρ : PosReal) (f₁ : X → EReal) (f₂ : Y → EReal) (A : X →L[ℝ] Y)
    (x w y2 : ℕ → X) (z y1 : ℕ → Y)
    (x0 w0 y20 : X) (z0 y10 : Y) : Prop where
  x_zero : x 0 = x0
  w_zero : w 0 = w0
  y2_zero : y2 0 = y20
  z_zero : z 0 = z0
  y1_zero : y1 0 = y10
  x_step (k : ℕ) :
    x (k + 1) = admm_sum_composition_v2_x_update ρ A (z k) (y1 k) (w k) (y2 k)
  z_step (k : ℕ) :
    z (k + 1) ∈ prox[((((1 / ρ : PosReal) : EReal) • f₂))]
      (A (x (k + 1)) + (1 / (ρ : ℝ)) • y1 k)
  w_step (k : ℕ) :
    w (k + 1) ∈ prox[((((1 / ρ : PosReal) : EReal) • f₁))]
      (x (k + 1) + (1 / (ρ : ℝ)) • y2 k)
  y1_step (k : ℕ) :
    y1 (k + 1) = y1 k + (ρ : ℝ) • (A (x (k + 1)) - z (k + 1))
  y2_step (k : ℕ) :
    y2 (k + 1) = y2 k + (ρ : ℝ) • (x (k + 1) - w (k + 1))

recall IsADMMSumCompositionTrajectoryV2

namespace IsADMMSumCompositionTrajectoryV2

/-- An Algorithm 15.7 trajectory starts from the prescribed initial iterates
`x^0 = x0`, `w^0 = w0`, `y₂^0 = y20`, `z^0 = z0`, and `y₁^0 = y10`. -/
theorem zero
    {ρ : PosReal}
    {f₁ : X → EReal} {f₂ : Y → EReal} {A : X →L[ℝ] Y}
    {x w y2 : ℕ → X} {z y1 : ℕ → Y}
    {x0 w0 y20 : X} {z0 y10 : Y}
    (h : IsADMMSumCompositionTrajectoryV2 ρ f₁ f₂ A x w y2 z y1 x0 w0 y20 z0 y10) :
    x 0 = x0 ∧ w 0 = w0 ∧ y2 0 = y20 ∧ z 0 = z0 ∧ y1 0 = y10 :=
  ⟨h.x_zero, h.w_zero, h.y2_zero, h.z_zero, h.y1_zero⟩

/-- At every iteration `k`, an Algorithm 15.7 trajectory satisfies the displayed linear `x`-solve,
the two proximal updates, and the two affine multiplier recursions. -/
theorem step
    {ρ : PosReal}
    {f₁ : X → EReal} {f₂ : Y → EReal} {A : X →L[ℝ] Y}
    {x w y2 : ℕ → X} {z y1 : ℕ → Y}
    {x0 w0 y20 : X} {z0 y10 : Y}
    (h : IsADMMSumCompositionTrajectoryV2 ρ f₁ f₂ A x w y2 z y1 x0 w0 y20 z0 y10)
    (k : ℕ) :
    x (k + 1) = admm_sum_composition_v2_x_update ρ A (z k) (y1 k) (w k) (y2 k) ∧
      z (k + 1) ∈ prox[((((1 / ρ : PosReal) : EReal) • f₂))]
        (A (x (k + 1)) + (1 / (ρ : ℝ)) • y1 k) ∧
      w (k + 1) ∈ prox[((((1 / ρ : PosReal) : EReal) • f₁))]
        (x (k + 1) + (1 / (ρ : ℝ)) • y2 k) ∧
      y1 (k + 1) = y1 k + (ρ : ℝ) • (A (x (k + 1)) - z (k + 1)) ∧
      y2 (k + 1) = y2 k + (ρ : ℝ) • (x (k + 1) - w (k + 1)) :=
  ⟨h.x_step k, h.z_step k, h.w_step k, h.y1_step k, h.y2_step k⟩

/-- The displayed first dual recursion in Algorithm 15.7 is the canonical ADMM multiplier update
specialized to `A x - z = 0`. -/
theorem y1_step_admm_multiplier_update
    {ρ : PosReal}
    {f₁ : X → EReal} {f₂ : Y → EReal} {A : X →L[ℝ] Y}
    {x w y2 : ℕ → X} {z y1 : ℕ → Y}
    {x0 w0 y20 : X} {z0 y10 : Y}
    (h : IsADMMSumCompositionTrajectoryV2 ρ f₁ f₂ A x w y2 z y1 x0 w0 y20 z0 y10)
    (k : ℕ) :
    y1 (k + 1) =
      admm_multiplier_update ρ A (-LinearMap.id) 0 (y1 k) (x (k + 1)) (z (k + 1)) := by
  calc
    y1 (k + 1) = y1 k + (ρ : ℝ) • (A (x (k + 1)) - z (k + 1)) := h.y1_step k
    _ = admm_multiplier_update ρ A (-LinearMap.id) 0 (y1 k) (x (k + 1)) (z (k + 1)) := by
      symm
      exact admm_multiplier_update_linear_composite_eq ρ A (y1 k) (x (k + 1)) (z (k + 1))

/-- The displayed second dual recursion in Algorithm 15.7 is the canonical ADMM multiplier update
specialized to `x - w = 0`. -/
theorem y2_step_admm_multiplier_update
    {ρ : PosReal}
    {f₁ : X → EReal} {f₂ : Y → EReal} {A : X →L[ℝ] Y}
    {x w y2 : ℕ → X} {z y1 : ℕ → Y}
    {x0 w0 y20 : X} {z0 y10 : Y}
    (h : IsADMMSumCompositionTrajectoryV2 ρ f₁ f₂ A x w y2 z y1 x0 w0 y20 z0 y10)
    (k : ℕ) :
    y2 (k + 1) =
      admm_multiplier_update
        ρ
        (LinearMap.id : X →ₗ[ℝ] X)
        (-LinearMap.id)
        0
        (y2 k)
        (x (k + 1))
        (w (k + 1)) := by
  calc
    y2 (k + 1) = y2 k + (ρ : ℝ) • (x (k + 1) - w (k + 1)) := h.y2_step k
    _ =
        admm_multiplier_update
          ρ
          (LinearMap.id : X →ₗ[ℝ] X)
          (-LinearMap.id)
          0
          (y2 k)
          (x (k + 1))
          (w (k + 1)) := by
        symm
        exact
          admm_multiplier_update_linear_composite_eq
            ρ
            (LinearMap.id : X →ₗ[ℝ] X)
            (y2 k)
            (x (k + 1))
            (w (k + 1))

end IsADMMSumCompositionTrajectoryV2

end
