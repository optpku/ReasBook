/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import Mathlib
import FirstOrderMethodsOptimization_Beck_2017.Chap11.Algorithm_11_5

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u v

open scoped Gradient

/- Theorem 11.10 is `source-facing`: it rewrites the realized RBPG update from
`Algorithm_11_5` using the owner-level Chapter 11 residual map. Domain sampling identifies:
- `block_coordinate_update` from `Definition_11_4` as the canonical one-block update owner;
- `IsBlockProximalGradientProblem.prox_point`/`gradient_mapping` and
  `IsBlockProximalGradientProblem.gradient_mapping_def` as the canonical residual API;
- `randomized_block_proximal_gradient_method_succ` from `Algorithm_11_5` as the pathwise RBPG
  recursion owner.

The primitive data are only the block-problem owner `hproblem`, the current iterate, and the
realized sampled block. The subtraction-by-residual formula proved here is derived API, so the
proof should reuse the existing owner theorem `gradient_mapping_def` instead of rebuilding a
parallel local residual definition. -/

section

variable {ι : Type u} [Fintype ι] {Ei : ι → Type v}
variable [∀ i, NormedAddCommGroup (Ei i)] [∀ i, InnerProductSpace ℝ (Ei i)]
variable [∀ i, ProperSpace (Ei i)]
variable {Li : (i : ι) → PosReal}
variable {f : ((i : ι) → Ei i) → EReal} {g : (i : ι) → Ei i → EReal}
variable {block_gradient : (i : ι) → ((j : ι) → Ei j) → Ei i}
variable {XStar : Set ((i : ι) → Ei i)} {FOpt : ℝ}

/-- A realized RBPG step can be written as the current iterate minus the injected partial
gradient mapping in the sampled block. -/
-- Proof sketch: rewrite the block displacement term in the textbook step
-- `block_coordinate_update xk ik (T_{L_{ik}}^{ik}(xk) - xk_ik)` using the residual identity
-- defining `block_partial_gradient_mapping` at the textbook stepsize `L_{i_k}`. This turns
-- `T^i_{L_i}(x) - x_i` into `-(1 / L_i) • G^i_{L_i}(x)`.
theorem block_coordinate_update_eq_sub_block_partial_gradient_mapping
    (hproblem : IsBlockProximalGradientProblem f g block_gradient XStar FOpt Li)
    (xk : (i : ι) → Ei i) (ik : ι) :
    block_coordinate_update xk ik
      (T[Li ik; hproblem] xk ik - xk ik) =
      xk - (1 / (Li ik : ℝ)) • 𝒰[ik] (G[Li ik; hproblem] xk ik) := by
  classical
  ext j
  by_cases hj : j = ik
  · subst j
    have hLi_ne : (Li ik : ℝ) ≠ 0 := ne_of_gt (Li ik).2
    have hinv_mul : (1 / (Li ik : ℝ)) * (Li ik : ℝ) = 1 := by
      field_simp [hLi_ne]
    calc
      block_coordinate_update xk ik
          (T[Li ik; hproblem] xk ik - xk ik) ik
        = (T[Li ik; hproblem] xk ik - xk ik) + xk ik := by
            simp [block_coordinate_update, add_comm]
      _ = T[Li ik; hproblem] xk ik := sub_add_cancel _ _
      _ = xk ik - (1 / (Li ik : ℝ)) • (G[Li ik; hproblem] xk ik) := by
            change hproblem.prox_point (Li ik) ik xk =
              xk ik - (1 / (Li ik : ℝ)) • hproblem.gradient_mapping (Li ik) ik xk
            rw [hproblem.gradient_mapping_def, smul_smul, hinv_mul, one_smul]
            exact (sub_sub_cancel (xk ik) (T[Li ik; hproblem] xk ik)).symm
      _ = (xk - (1 / (Li ik : ℝ)) • 𝒰[ik] (G[Li ik; hproblem] xk ik)) ik := by
            simp
  · simp [block_coordinate_update, hj]
variable (hproblem : IsBlockProximalGradientProblem f g block_gradient XStar FOpt Li)
variable (x0 : interior (effective_domain f))
variable (sampled_block : ℕ → ι)

local notation "x[" k "]" =>
  randomized_block_proximal_gradient_method hproblem x0 sampled_block k

-- Proof sketch: combine the recursive RBPG update
-- `randomized_block_proximal_gradient_method_succ` with the one-step reformulation
-- `block_coordinate_update_eq_sub_block_partial_gradient_mapping` at the
-- realized sampled block `i_k = sampled_block k`.
/-- Theorem 11.10: Remark 11.22 rewrites step (b) of the randomized block proximal gradient
algorithm as
`x^{k+1} = x^k - (1 / L_{i_k}) 𝒰_{i_k}(G^{i_k}_{L_{i_k}}(x^k))`. -/
theorem randomized_block_proximal_gradient_method_succ_eq_sub_block_partial_gradient_mapping
    (k : ℕ) :
    x[k + 1] =
      x[k] - (1 / (Li (sampled_block k) : ℝ)) •
        𝒰[sampled_block k] (G[Li (sampled_block k); hproblem] x[k] (sampled_block k)) := by
  simpa [randomized_block_proximal_gradient_method_succ] using
    block_coordinate_update_eq_sub_block_partial_gradient_mapping
      hproblem
      x[k] (sampled_block k)

end

end
