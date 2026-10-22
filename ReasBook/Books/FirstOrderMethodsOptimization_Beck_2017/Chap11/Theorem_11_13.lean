/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import FirstOrderMethodsOptimization_Beck_2017.Chap11.Algorithm_11_5
import FirstOrderMethodsOptimization_Beck_2017.Chap11.Definition_11_13
import FirstOrderMethodsOptimization_Beck_2017.Chap11.Lemma_11_3

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u v

open scoped BigOperators Gradient

section

variable {ι : Type u} [Fintype ι] {Ei : ι → Type v}
variable [∀ i, NormedAddCommGroup (Ei i)] [∀ i, InnerProductSpace ℝ (Ei i)]
variable [∀ i, ProperSpace (Ei i)]
variable {Li : (i : ι) → PosReal}

variable {f : ((i : ι) → Ei i) → EReal} {g : (i : ι) → Ei i → EReal}
variable {block_gradient : (i : ι) → ((j : ι) → Ei j) → Ei i}
variable {XStar : Set ((i : ι) → Ei i)} {FOpt : ℝ}

namespace IsBlockProximalGradientProblem

variable (hproblem : IsBlockProximalGradientProblem f g block_gradient XStar FOpt Li)
variable (x0 : effective_domain (separableSum g))
variable (sampled_block : ℕ → ι)

/-- Helper for Theorem 11.13: one realized RBPG block update preserves the effective domain of
the block-separable regularizer. -/
private lemma randomizedBlockProximalGradientStepMemEffectiveDomain
    (k : ℕ) {xk : (j : ι) → Ei j} (hxk : xk ∈ effective_domain (separableSum g)) :
    block_coordinate_update xk (sampled_block k)
      (hproblem.prox_point (Li (sampled_block k)) (sampled_block k) xk - xk (sampled_block k)) ∈
        effective_domain (separableSum g) := by
  let xkEff : effective_domain (separableSum g) := ⟨xk, hxk⟩
  -- Package the raw iterate as a subtype so the owner-level domain-preservation theorem applies.
  simpa [xkEff] using
    IsBlockProximalGradientProblem.block_coordinate_update_prox_point_mem_effective_domain
      hproblem
      (Li (sampled_block k))
      xkEff
      (sampled_block k)

-- Proof sketch: argue by induction on `k`. The base case is `x0.2`. For the inductive step,
-- `x[k + 1]` is obtained from `x[k]` by one realized RBPG update, and
-- `block_coordinate_update_prox_point_mem_effective_domain` preserves the effective domain of the
-- block-separable regularizer.
/-- Every realized RBPG iterate remains in the effective domain of the block-separable
regularizer, provided the initial point does. -/
theorem randomized_block_proximal_gradient_iterate_mem_effective_domain
    (k : ℕ) :
    randomized_block_proximal_gradient_method
        hproblem
        (hproblem.interior_effective_domain_point x0)
        sampled_block
        k ∈
      effective_domain (separableSum g) := by
  induction k with
  | zero =>
      -- The initial iterate is exactly the given starting point in the effective domain.
      exact x0.2
  | succ k ih =>
      -- Rewrite the next iterate as one realized RBPG update and propagate domain membership.
      rw [randomized_block_proximal_gradient_method_succ]
      exact randomizedBlockProximalGradientStepMemEffectiveDomain hproblem sampled_block k ih

end IsBlockProximalGradientProblem

namespace RandomizedBlockProximalGradientAssumptions

variable (hproblem : RandomizedBlockProximalGradientAssumptions f g block_gradient XStar FOpt Li)
variable (x0 : effective_domain (separableSum g))
variable (sampled_block : ℕ → ι)

-- Proof sketch: combine the iterate-domain theorem with the owner-level sufficient-decrease
-- theorem
-- `IsBlockProximalGradientProblem.block_partial_gradient_sufficient_decrease_of_block_lipschitz`
-- from `Lemma_11_3`, specialized to the current iterate `x[k]` and the realized sampled block
-- `i_k = sampled_block k`. The convexity input is supplied by
-- `effective_domain_convex_of_is_convex_function hproblem.f_convex`, and the resulting one-step
-- update agrees with `x[k + 1]` by `randomized_block_proximal_gradient_method_succ`.
/-- Theorem 11.13: along any realized RBPG sample path, each step decreases the composite
objective by at least `(1 / (2 L_{i_k})) ‖G^{i_k}_{L_{i_k}}(x^k)‖^2`. -/
theorem randomized_block_proximal_gradient_sufficient_decrease
    (k : ℕ) :
    composite_model_objective f (separableSum g)
        (randomized_block_proximal_gradient_method
          hproblem.toIsBlockProximalGradientProblem
          (hproblem.interior_effective_domain_point x0)
          sampled_block
          k) -
      composite_model_objective f (separableSum g)
        (randomized_block_proximal_gradient_method
          hproblem.toIsBlockProximalGradientProblem
          (hproblem.interior_effective_domain_point x0)
          sampled_block
          (k + 1)) ≥
      ((((1 : ℝ) / (2 * (Li (sampled_block k) : ℝ))) *
          ‖G[Li (sampled_block k); hproblem.toIsBlockProximalGradientProblem]
              (randomized_block_proximal_gradient_method
                hproblem.toIsBlockProximalGradientProblem
                (hproblem.interior_effective_domain_point x0)
                sampled_block
                k)
              (sampled_block k)‖ ^
            (2 : ℕ) :
          ℝ) :
        EReal) := by
  let xk : effective_domain (separableSum g) :=
    ⟨randomized_block_proximal_gradient_method
        hproblem.toIsBlockProximalGradientProblem
        (hproblem.interior_effective_domain_point x0)
        sampled_block
        k,
      IsBlockProximalGradientProblem.randomized_block_proximal_gradient_iterate_mem_effective_domain
        hproblem.toIsBlockProximalGradientProblem
        x0
        sampled_block
        k⟩
  simpa [xk, randomized_block_proximal_gradient_method_succ] using
    IsBlockProximalGradientProblem.block_partial_gradient_sufficient_decrease_of_block_lipschitz
      hproblem.toIsBlockProximalGradientProblem
      (effective_domain_convex_of_is_convex_function hproblem.f_convex)
      (sampled_block k)
      (Li (sampled_block k))
      (fun x d hx hxd ↦ by
        simpa using
          hproblem.block_partial_gradient_lipschitz
            (sampled_block k)
            hx
            hxd)
      xk

end RandomizedBlockProximalGradientAssumptions

end

end
