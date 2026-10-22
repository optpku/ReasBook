/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import FirstOrderMethodsOptimization_Beck_2017.Chap08.Definition_8_16
import FirstOrderMethodsOptimization_Beck_2017.Chap10.Definition_10_2
import FirstOrderMethodsOptimization_Beck_2017.Chap12.Definition_12_12
import FirstOrderMethodsOptimization_Beck_2017.Chap12.Definition_12_22

-- Declarations for this item will be appended below by the statement pipeline.

open scoped BigOperators Matrix.Norms.Frobenius

noncomputable section

section

variable {m n : ℕ}

local notation "Mmn" => Matrix (Fin m) (Fin n) ℝ

open IsotropicTwoDimensionalTotalVariation

/-
Definition 12.23 is a `bridge/view`: Definition 12.21 already fixes the isotropic
two-dimensional denoising objective, and Definition 12.22 already decomposes the isotropic
regularizer `TV_I` into the three diagonal components `ψ[i]`.

Domain sampling in the surrounding Chapter 12 API identifies:
- `core/canonical`: `two_dimensional_total_variation_denoising_objective` from Definition 12.12;
- `source-facing`: `TV_I` and the diagonal component family `isotropic_diagonal_component`;
- `core/canonical`: `denoising_data_fidelity`, `composite_model_objective`, and
  `finite_sum_objective`;
- `bridge/view`: the three-block family obtained by scaling the diagonal components by `λ`.

Primitive data here are only the datum `d`, the positive parameter `λ`, and the diagonal
component family from Definition 12.22. The public API should therefore be only the bridge from
the existing isotropic denoising owner to the canonical Chapter 10/8 composite finite-sum owner
layer, rather than a parallel local wrapper.
-/

local instance instDefinition1223NormedAddCommGroupMatrix : NormedAddCommGroup Mmn :=
  Matrix.frobeniusNormedAddCommGroup

local instance instDefinition1223NormedSpaceMatrix : NormedSpace ℝ Mmn :=
  Matrix.frobeniusNormedSpace

local notation "ψ[" i "]" => isotropic_diagonal_component m n i
local notation "G[" lam "]" =>
  ((fun i x ↦ (((lam : ℝ) * ψ[i] x : ℝ) : EReal)) : Fin 3 → Mmn → EReal)

/-- Definition 12.23: the isotropic total-variation denoising problem can be rewritten as the
composite objective with quadratic data-fidelity term `x ↦ (1 / 2) ‖x - d‖_F^2` and finite-sum
penalty term `∑ i : Fin 3, λ * ψ[i] x`. -/
theorem isotropic_two_dimensional_total_variation_denoising_fits_dual_block_model
    (d : Mmn) (lam : PosReal) :
    two_dimensional_total_variation_denoising_objective TV_I d lam =
      composite_model_objective
        (denoising_data_fidelity d)
        (finite_sum_objective G[lam]) := by
  ext x
  rw [two_dimensional_total_variation_denoising_objective_apply, composite_model_objective_apply,
    denoising_data_fidelity_apply, finite_sum_objective_apply,
    isotropic_two_dimensional_total_variation_eq_sum_diagonal_components, Fin.sum_univ_three,
    Fin.sum_univ_three, mul_add, mul_add, EReal.coe_add, EReal.coe_add]

/-- Evaluating the Definition 12.23 rewrite gives the quadratic Frobenius data-fidelity term plus
the three scaled diagonal components from Definition 12.22. -/
theorem isotropic_two_dimensional_total_variation_denoising_fits_dual_block_model_apply
    (d x : Mmn) (lam : PosReal) :
    two_dimensional_total_variation_denoising_objective TV_I d lam x =
      ((‖x - d‖ ^ (2 : ℕ) / 2 : ℝ) : EReal) +
        ∑ i : Fin 3, ↑((lam : ℝ) * ψ[i] x) := by
  rw [isotropic_two_dimensional_total_variation_denoising_fits_dual_block_model,
    composite_model_objective_apply, denoising_data_fidelity_apply, finite_sum_objective_apply]

end
