/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import Mathlib
import FirstOrderMethodsOptimization_Beck_2017.Chap06.Theorem_6_63
import FirstOrderMethodsOptimization_Beck_2017.Chap15.Algorithm_15_3

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u v

section

variable {X : Type u} {Y : Type v}
variable [AddCommMonoid X] [Module ℝ X]
variable [NormedAddCommGroup Y] [InnerProductSpace ℝ Y]

/- `prompt_add/` is absent in this workspace, so the owner choice is sampled from the nearby
Chapter 15 ADMM files together with the shared proximal API from Chapter 6.

This item is `source-facing`: Algorithm 15.6 specializes alternating ADMM to the linear-composite
problem `min_x f₁(x) + f₂(Ax)`. Domain sampling shows that the best owner abstraction is already
upstream:
- `core/canonical`: `IsADMMAlternatingTrajectory` from Algorithm 15.3 for the alternating ADMM
  iteration data;
- `core/canonical`: `admm_x_update_argmin`, `admm_z_update_argmin`, and
  `admm_multiplier_update` for the three alternating ADMM clauses;
- `bridge/view`: the linear-composite specialization `B = -LinearMap.id`, `c = 0`;
- `core/canonical`: Chapter 6's proximal owner `prox[...]` together with
  `scaled_proximal_objective_div_eq_moreau_penalty` for the specialized `z`-step.

Primitive data are therefore just the iterates and initial values already owned by
`IsADMMAlternatingTrajectory`; the specialized `x`-argmin clause, proximal `z`-clause, and
simplified multiplier recursion are derived API for the linear-composite specialization, not a
second trajectory owner. The `z`-step bridge is the direct positive-rescaling comparison encoded by
the Chapter 6 scaled-prox objective identity. -/

/-- The `x`-update in Algorithm 15.6(a) is exactly the specialized alternating ADMM `x`-argmin
set for `B = -I` and `c = 0`, written with the displayed linear-composite objective. -/
@[simp] theorem mem_admm_x_update_argmin_linear_composite_iff
    {ρ : PosReal}
    {f₁ : X → EReal}
    {A : X →ₗ[ℝ] Y}
    {zk yk : Y}
    {xNext : X} :
    xNext ∈ admm_x_update_argmin ρ f₁ A (-LinearMap.id) 0 zk yk ↔
      IsMinOn
        (fun x : X ↦
          f₁ x +
            ((((ρ : ℝ) / 2) * ‖A x - zk + (1 / (ρ : ℝ)) • yk‖ ^ (2 : ℕ) : ℝ) : EReal))
        Set.univ
        xNext := by
  rw [mem_admm_x_update_argmin_iff]
  constructor <;> intro hx <;>
    simpa [sub_eq_add_neg, add_left_comm, add_comm] using hx

/-- The proximal `z`-update in Algorithm 15.6(b) is exactly the specialized alternating ADMM
`z`-argmin set for `B = -I` and `c = 0`, written directly on the canonical proximal-set owner. -/
@[simp] theorem mem_admm_z_update_argmin_linear_composite_iff
    [InnerProductSpace ℝ Y] [ProperSpace Y]
    {ρ : PosReal}
    {f₂ : Y → EReal}
    {A : X →ₗ[ℝ] Y}
    {xNext : X}
    {yk zNext : Y} :
    zNext ∈ admm_z_update_argmin ρ f₂ A (-LinearMap.id) 0 xNext yk ↔
      zNext ∈ prox[(((1 / ρ : PosReal) : EReal) • f₂)]
        (A xNext + (1 / (ρ : ℝ)) • yk) := by
  let μ : PosReal := 1 / ρ
  let x : Y := A xNext + (1 / (ρ : ℝ)) • yk
  have hcoeff : (1 / (2 * (μ : ℝ)) : ℝ) = (ρ : ℝ) / 2 := by
    have hρ : (ρ : ℝ) ≠ 0 := ne_of_gt ρ.2
    change 1 / (2 * (1 / (ρ : ℝ))) = (ρ : ℝ) / 2
    field_simp [hρ]
  have hprox :
      zNext ∈ prox[((μ : EReal) • f₂)] x ↔
        IsMinOn
          (fun v : Y ↦
            f₂ v + ((((1 / (2 * (μ : ℝ)) : ℝ) * ‖x - v‖ ^ (2 : ℕ) : ℝ) : EReal)))
          Set.univ
          zNext := by
    constructor
    · exact isMinOn_moreau_penalty_of_mem_scaled_prox
    · intro hz
      rw [mem_proximal_mapping_iff, isMinOn_univ_iff]
      rw [isMinOn_univ_iff] at hz
      intro v
      have hz_div :
          proximal_objective (((μ : EReal) • f₂)) x zNext / ((μ : ℝ) : EReal) ≤
            proximal_objective (((μ : EReal) • f₂)) x v / ((μ : ℝ) : EReal) := by
        rw [scaled_proximal_objective_div_eq_moreau_penalty,
          scaled_proximal_objective_div_eq_moreau_penalty]
        exact hz v
      have hμ_nonneg : 0 ≤ ((μ : ℝ) : EReal) := by
        exact_mod_cast μ.2.le
      have hμ_top : ((μ : ℝ) : EReal) ≠ ⊤ := EReal.coe_ne_top _
      have hμ_bot : ((μ : ℝ) : EReal) ≠ ⊥ := EReal.coe_ne_bot _
      have hμ_zero : ((μ : ℝ) : EReal) ≠ 0 := by
        exact_mod_cast μ.2.ne'
      have hz_scaled := mul_le_mul_of_nonneg_right hz_div hμ_nonneg
      rw [EReal.div_mul_cancel hμ_bot hμ_top hμ_zero,
        EReal.div_mul_cancel hμ_bot hμ_top hμ_zero] at hz_scaled
      exact hz_scaled
  rw [mem_admm_z_update_argmin_iff]
  constructor
  · intro hz
    exact hprox.mpr (by
      simpa [μ, x, hcoeff, sub_eq_add_neg, norm_sub_rev, add_assoc, add_left_comm, add_comm]
        using hz)
  · intro hz
    exact (by
      simpa [μ, x, hcoeff, sub_eq_add_neg, norm_sub_rev, add_assoc, add_left_comm, add_comm]
        using hprox.mp hz)

/-- The affine dual recursion in Algorithm 15.6(c) is the generic ADMM multiplier update
specialized to `B = -I` and `c = 0`. -/
@[simp] theorem admm_multiplier_update_linear_composite_eq
    (ρ : PosReal)
    (A : X →ₗ[ℝ] Y)
    (yk : Y)
    (xNext : X)
    (zNext : Y) :
    admm_multiplier_update ρ A (-LinearMap.id) 0 yk xNext zNext =
      yk + (ρ : ℝ) • (A xNext - zNext) := by
  simp [admm_multiplier_update, sub_eq_add_neg]

/- Algorithm 15.6 trajectories are the alternating ADMM trajectories specialized to
`B = -LinearMap.id` and `c = 0`. -/
recall IsADMMAlternatingTrajectory

namespace IsADMMAlternatingTrajectory

/-- In the linear-composite specialization of Algorithm 15.6, the generic alternating ADMM
`x`-argmin clause is exactly the displayed step-(a) minimization problem. -/
theorem x_step_linear_composite
    {ρ : PosReal}
    {f₁ : X → EReal} {f₂ : Y → EReal}
    {A : X →ₗ[ℝ] Y}
    {x : ℕ → X} {z y : ℕ → Y}
    {x0 : X} {z0 y0 : Y}
    (h : IsADMMAlternatingTrajectory ρ f₁ f₂ A (-LinearMap.id) 0 x z y x0 z0 y0)
    (k : ℕ) :
    IsMinOn
      (fun xNext : X ↦
        f₁ xNext +
          ((((ρ : ℝ) / 2) * ‖A xNext - z k + (1 / (ρ : ℝ)) • y k‖ ^ (2 : ℕ) : ℝ) : EReal))
      Set.univ
      (x (k + 1)) := by
  simpa [sub_eq_add_neg, add_left_comm, add_comm] using
    mem_admm_x_update_argmin_linear_composite_iff.mp (h.x_step k)

/-- In the linear-composite specialization of Algorithm 15.6, the generic alternating ADMM
`z`-argmin clause is exactly the proximal update from part (b). -/
theorem z_step_linear_composite
    [InnerProductSpace ℝ Y] [ProperSpace Y]
    {ρ : PosReal}
    {f₁ : X → EReal} {f₂ : Y → EReal}
    {A : X →ₗ[ℝ] Y}
    {x : ℕ → X} {z y : ℕ → Y}
    {x0 : X} {z0 y0 : Y}
    (h : IsADMMAlternatingTrajectory ρ f₁ f₂ A (-LinearMap.id) 0 x z y x0 z0 y0)
    (k : ℕ) :
    z (k + 1) ∈ prox[(((1 / ρ : PosReal) : EReal) • f₂)]
      (A (x (k + 1)) + (1 / (ρ : ℝ)) • y k) := by
  simpa using mem_admm_z_update_argmin_linear_composite_iff.mp (h.z_step k)

/-- In the linear-composite specialization of Algorithm 15.6, the generic alternating ADMM
multiplier update simplifies to `y^(k+1) = y^k + ρ (A x^(k+1) - z^(k+1))`. -/
theorem y_step_linear_composite
    {ρ : PosReal}
    {f₁ : X → EReal} {f₂ : Y → EReal}
    {A : X →ₗ[ℝ] Y}
    {x : ℕ → X} {z y : ℕ → Y}
    {x0 : X} {z0 y0 : Y}
    (h : IsADMMAlternatingTrajectory ρ f₁ f₂ A (-LinearMap.id) 0 x z y x0 z0 y0)
    (k : ℕ) :
    y (k + 1) = y k + (ρ : ℝ) • (A (x (k + 1)) - z (k + 1)) := by
  simpa [smul_sub, sub_eq_add_neg] using
    Eq.trans (h.y_step k) (admm_multiplier_update_linear_composite_eq ρ A (y k) (x (k + 1))
      (z (k + 1)))

end IsADMMAlternatingTrajectory

end
