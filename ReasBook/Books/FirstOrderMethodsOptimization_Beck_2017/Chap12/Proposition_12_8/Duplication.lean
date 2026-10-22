/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Operator.NormedSpace
import FirstOrderMethodsOptimization_Beck_2017.Chap12.Algorithm_12_1

open scoped ENNReal BigOperators

noncomputable section

universe u

section

variable {E : Type u}
variable [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The diagonal duplication operator sending `z` to the constant `p`-block vector
`(z, …, z)` in the `L²` block product `PiLp (2 : ENNReal) (fun _ : Fin p ↦ E)`. -/
abbrev dual_block_duplication
    (E : Type u) [NormedAddCommGroup E] [NormedSpace ℝ E]
    (p : ℕ) : E →L[ℝ] PiLp (2 : ENNReal) (fun _ : Fin p ↦ E) :=
  ((PiLp.continuousLinearEquiv (2 : ENNReal) ℝ (fun _ : Fin p ↦ E)).symm.toContinuousLinearMap).comp
    (ContinuousLinearMap.pi fun _ : Fin p ↦ ContinuousLinearMap.id ℝ E)

/-- Every block coordinate of the duplicated vector `𝒜(z)` is equal to `z`. -/
@[simp] theorem dual_block_duplication_apply
    (p : ℕ) (z : E) (i : Fin p) :
    dual_block_duplication E p z i = z := by
  simp [dual_block_duplication]

/-- The duplicated `L²` block vector has squared norm `p * ‖z‖²`. -/
lemma dual_block_duplication_norm_sq_apply
    (p : ℕ) (z : E) :
    ‖dual_block_duplication E p z‖ ^ (2 : ℕ) = (p : ℝ) * ‖z‖ ^ (2 : ℕ) := by
  calc
    ‖dual_block_duplication E p z‖ ^ (2 : ℕ)
        = ∑ i : Fin p, ‖dual_block_duplication E p z i‖ ^ (2 : ℕ) := by
            simpa using
              (PiLp.norm_sq_eq_of_L2 (fun _ : Fin p ↦ E) (dual_block_duplication E p z))
    _ = ∑ i : Fin p, ‖z‖ ^ (2 : ℕ) := by
          simp
    _ = (p : ℝ) * ‖z‖ ^ (2 : ℕ) := by
          simp

/-- The duplication map scales every norm by `√p`. -/
lemma dual_block_duplication_norm_apply
    (p : ℕ) (z : E) :
    ‖dual_block_duplication E p z‖ = Real.sqrt (p : ℝ) * ‖z‖ := by
  have hp_nonneg : 0 ≤ (p : ℝ) := by
    exact_mod_cast Nat.zero_le p
  refine (sq_eq_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))).mp ?_
  rw [dual_block_duplication_norm_sq_apply, mul_pow, Real.sq_sqrt hp_nonneg]

end

section

variable {E : Type u}
variable [NormedAddCommGroup E] [NormedSpace ℝ E] [Nontrivial E]

/-- The diagonal duplication operator on the `p`-fold `L²` block product has squared operator norm
`p`. -/
theorem dual_block_duplication_opNorm_sq
    (p : ℕ) :
    ‖dual_block_duplication E p‖ ^ (2 : ℕ) = (p : ℝ) := by
  have hp_nonneg : 0 ≤ (p : ℝ) := by
    exact_mod_cast Nat.zero_le p
  have hnorm :
      ‖dual_block_duplication E p‖ = Real.sqrt (p : ℝ) := by
    simpa using
      (ContinuousLinearMap.homothety_norm (dual_block_duplication E p)
        (dual_block_duplication_norm_apply (E := E) p))
  calc
    ‖dual_block_duplication E p‖ ^ (2 : ℕ) = (Real.sqrt (p : ℝ)) ^ (2 : ℕ) := by
      rw [hnorm]
    _ = (p : ℝ) := by
      exact Real.sq_sqrt hp_nonneg

/-- For the diagonal duplication operator `𝒜(z) = (z, …, z)`, the FDPG parameter from Algorithm
12.1 satisfies `L = ‖𝒜‖² / σ = p / σ`. -/
@[simp] theorem dual_block_duplication_fdpg_lipschitz_constant_eq
    (σ : PosReal) (p : ℕ) :
    dual_based_proximal_gradient_dual_lipschitz_constant
        (dual_block_duplication E p) σ =
      (p : ℝ) / (σ : ℝ) := by
  rw [dual_based_proximal_gradient_dual_lipschitz_constant_eq, dual_block_duplication_opNorm_sq]

end
