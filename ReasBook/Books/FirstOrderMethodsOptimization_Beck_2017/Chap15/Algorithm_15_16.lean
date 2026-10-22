/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import Mathlib
import FirstOrderMethodsOptimization_Beck_2017.Chap15.Algorithm_15_15
import FirstOrderMethodsOptimization_Beck_2017.Chap15.Algorithm_15_10

-- Declarations for this item will be appended below by the statement pipeline.

open scoped BigOperators

noncomputable section

universe u v w

section

variable {ι : Type v} {X : Type u} {Y : ι → Type w}
variable [Fintype ι]
variable [NormedAddCommGroup X] [InnerProductSpace ℝ X] [FiniteDimensional ℝ X]
variable [∀ i, NormedAddCommGroup (Y i)] [∀ i, InnerProductSpace ℝ (Y i)]
variable [∀ i, FiniteDimensional ℝ (Y i)]

local notation "Z" => PiLp (2 : ENNReal) Y

/- `prompt_add/` is absent in this workspace, so the owner choice is sampled from the nearby
Chapter 15 AD-LPMM and finite-sum linear-composite files.

This item is `source-facing`: Algorithm 15.16 keeps its explicit multi-block `x`-update and the
source-facing aggregate `z`-clause, but its ambient trajectory data already have canonical owners
upstream.
- `core/canonical`: `IsADLPMMTrajectory`, together with `ad_lpmm_alpha_parameter` and
  `ad_lpmm_beta_parameter`, is the chapter owner for the linear-composite AD-LPMM recursion.
- `core/canonical`: `admm_finite_sum_linear_composite_stacked_map` from Algorithm 15.15 is the
  correct stacked `PiLp` block operator, so the source constant `L` is read through that owner
  rather than by rebuilding a separate normal-map interface.
- `bridge/view`: `admm_finite_sum_linear_composite_v1_z_update_center` and
  `admm_finite_sum_linear_composite_v1_z_step_iff` from Algorithm 15.15 present the inherited
  aggregate separable-prox `z`-step and its coordinatewise block formula.
- `core/canonical`: `admm_multiplier_update` on the stacked constraint
  `admm_finite_sum_linear_composite_stacked_map A x - z = 0` is already the exact affine
  multiplier owner, so the local `y`-formula should be inherited rather than stored again.

Primitive data are therefore the family `A`, the block functions `g`, the nondegeneracy
hypothesis `0 < L`, and the iterate sequences. The owner abstraction itself is the canonical
specialized `IsADLPMMTrajectory`; the displayed `x`-, `z`-, and `y`-formulas are derived bridge
theorems, and coordinatewise properness is needed only for the companion `z`-formula theorem. -/

/- Algorithm 15.16 uses the canonical stacked `IsADLPMMTrajectory` specialized to
`α = ρ L`, `β = ρ`, `h₁ = 0`, and `h₂ = ∑ᵢ gᵢ`. The explicit `x`-, `z`-, and `y`-formulas are
recovered as derived bridge theorems below. -/
recall IsADLPMMTrajectory

namespace IsADLPMMTrajectory

variable {ρ : PosReal}
variable {A : (i : ι) → X →ₗ[ℝ] Y i}
variable (hL : 0 < adlpmm_linearization_bound (1 : PosReal)
  (admm_finite_sum_linear_composite_stacked_map A))
variable {g : (i : ι) → Y i → EReal}
variable {x : ℕ → X}
variable {z y : ℕ → Z}
variable {x0 : X}
variable {z0 y0 : Z}

/- The explicit `x`-formula is the source-facing view of the trajectory's local `x`-owner. -/
/-- In an Algorithm 15.16 trajectory, the local `x`-owner reduces to the displayed gradient-type
multi-block update
`x^(k+1) = x^k - (1 / L) ∑ᵢ Aᵢᵀ (Aᵢ x^k - zᵢ^k + (1 / ρ) yᵢ^k)`. -/
theorem x_step_eq
    (h : IsADLPMMTrajectory
      ρ
      (admm_finite_sum_linear_composite_stacked_map A)
      (-LinearMap.id)
      0
      (ad_lpmm_alpha_parameter (admm_finite_sum_linear_composite_stacked_map A) ρ hL)
      (ad_lpmm_beta_parameter ρ)
      (fun _ : X ↦ (0 : EReal))
      (PiLp.separableSum g)
      x
      z
      y
      x0
      z0
      y0)
    (k : ℕ) :
    x (k + 1) =
      x k - (1 / adlpmm_linearization_bound (1 : PosReal)
        (admm_finite_sum_linear_composite_stacked_map A) : ℝ) •
        ∑ i, (A i).adjoint (A i (x k) - z k i + (1 / (ρ : ℝ)) • y k i) :=
  let A' := admm_finite_sum_linear_composite_stacked_map A
  have hx := h.x_step_linear_composite k
  have hzero :
      ((((1 / (ad_lpmm_alpha_parameter A' ρ hL : PosReal) : PosReal) : EReal) •
        fun _ : X ↦ (0 : EReal)) : X → EReal) = 0 := by
    funext u
    simp
  have hx' :
      x (k + 1) =
        x k - (((ρ / (ad_lpmm_alpha_parameter A' ρ hL : PosReal)) : PosReal) : ℝ) •
          A'.adjoint (A' (x k) - z k + (1 / (ρ : ℝ)) • y k) := by
    rw [hzero, prox_zero_eq_singleton, Set.mem_singleton_iff] at hx
    exact hx
  have hρα :
      (((ρ / (ad_lpmm_alpha_parameter A' ρ hL : PosReal)) : PosReal) : ℝ) =
        (1 / adlpmm_linearization_bound (1 : PosReal)
          A' : ℝ) := by
    rw [PosReal.coe_div, ad_lpmm_alpha_parameter_coe]
    field_simp
  by simpa [A', hρα] using hx'

/-- In an Algorithm 15.16 trajectory, the inherited canonical AD-LPMM `z`-step is exactly the
aggregate separable proximal update from Algorithm 15.15. -/
theorem z_step_mem
    (h : IsADLPMMTrajectory
      ρ
      (admm_finite_sum_linear_composite_stacked_map A)
      (-LinearMap.id)
      0
      (ad_lpmm_alpha_parameter (admm_finite_sum_linear_composite_stacked_map A) ρ hL)
      (ad_lpmm_beta_parameter ρ)
      (fun _ : X ↦ (0 : EReal))
      (PiLp.separableSum g)
      x
      z
      y
      x0
      z0
      y0)
    (k : ℕ) :
    z (k + 1) ∈ prox[(((1 / ρ : PosReal) : EReal) • PiLp.separableSum g)]
      (admm_finite_sum_linear_composite_v1_z_update_center ρ A (x (k + 1)) (y k)) :=
  by
    simpa [admm_finite_sum_linear_composite_v1_z_update_center, sub_eq_add_neg,
      add_assoc, add_left_comm, add_comm] using
      h.z_step_linear_composite k

/-- Under coordinatewise properness of the block penalties, the canonical finite-sum proximal
`z`-step in an Algorithm 15.16 trajectory reduces coordinatewise to the displayed blockwise
proximal formula. -/
theorem z_step_prox
    (hg_proper : ∀ i, IsProperExtendedRealFunction (g i))
    (h : IsADLPMMTrajectory
      ρ
      (admm_finite_sum_linear_composite_stacked_map A)
      (-LinearMap.id)
      0
      (ad_lpmm_alpha_parameter (admm_finite_sum_linear_composite_stacked_map A) ρ hL)
      (ad_lpmm_beta_parameter ρ)
      (fun _ : X ↦ (0 : EReal))
      (PiLp.separableSum g)
      x
      z
      y
      x0
      z0
      y0)
    (k : ℕ)
    (i : ι) :
    z (k + 1) i ∈ prox[((((1 / ρ : PosReal) : EReal) • g i))]
      (A i (x (k + 1)) + (1 / (ρ : ℝ)) • y k i) :=
  by
    simpa using (admm_finite_sum_linear_composite_v1_z_step_iff hg_proper).mp (h.z_step_mem k)

/-- In an Algorithm 15.16 trajectory, the canonical stacked multiplier update reduces
coordinatewise to the displayed affine recursion
`yᵢ^(k+1) = yᵢ^k + ρ (Aᵢ x^(k+1) - zᵢ^(k+1))`. -/
theorem y_step_apply
    (h : IsADLPMMTrajectory
      ρ
      (admm_finite_sum_linear_composite_stacked_map A)
      (-LinearMap.id)
      0
      (ad_lpmm_alpha_parameter (admm_finite_sum_linear_composite_stacked_map A) ρ hL)
      (ad_lpmm_beta_parameter ρ)
      (fun _ : X ↦ (0 : EReal))
      (PiLp.separableSum g)
      x
      z
      y
      x0
      z0
      y0)
    (k : ℕ)
    (i : ι) :
    y (k + 1) i = y k i + (ρ : ℝ) • (A i (x (k + 1)) - z (k + 1) i) :=
  by
    simpa using congrArg (fun u : Z ↦ u i) (h.y_step_linear_composite k)

end IsADLPMMTrajectory

end
