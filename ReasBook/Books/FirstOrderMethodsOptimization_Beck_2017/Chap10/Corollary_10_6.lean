/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import FirstOrderMethodsOptimization_Beck_2017.Chap10.Lemma_10_4

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u

open scoped Gradient

section

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [ProperSpace E]

/- Corollary 10.6 is `source-facing` in the Chapter 10 proximal-gradient API.

Domain sampling in the local owner ecosystem:
- `composite_model_objective` from Definition 10.2 is the chapter owner for the composite value
  `F = f + g`;
- `prox_grad_operator` from Definition 10.9, with notation `T[...]`, is the canonical one-step
  prox-gradient update;
- `gradient_mapping` from Definition 10.5, with notation `G[...]`, is the canonical residual
  owner;
- `prox_grad_sufficient_decrease` from Lemma 10.4 is the upstream descent theorem this
  corollary specializes.

Primitive data are exactly the hypotheses already required by Lemma 10.4, with the positivity of
the smoothness constant carried canonically by `PosReal`. The displayed inequality is therefore
derived API obtained by specializing the owner theorem to the stepsize `L = L_f`, not a new local
descent owner. -/

variable (f g : E → EReal)
variable (Lf : PosReal)
variable [IsProperExtendedRealFunction g] [Fact (LowerSemicontinuous g)]
  [Fact (is_convex_function g)]

local notation "F" => composite_model_objective f g

-- Proof sketch: specialize `prox_grad_sufficient_decrease` to the stepsize `L = Lf`. The
-- coefficient `((L_f - L_f / 2) / L_f^2)` then simplifies to `1 / (2 L_f)`, and the residual
-- term is already expressed through the Chapter 10 owners `T[Lf, f, g]` and `G[Lf, f, g]` from
-- `Lemma_10_4`.
/-- Corollary 10.6: under the assumptions of Lemma 10.4, specializing the prox-gradient descent
estimate to the stepsize `L_f` gives
`F(x) - F(T[L_f, f, g] x) ≥ (1 / (2 L_f)) ‖G[L_f, f, g] x‖^2` for every
`x ∈ interior (effective_domain f)`. -/
theorem prox_grad_sufficient_decrease_at_smoothness_constant
    (hf_ne_bot : ∀ y, f y ≠ ⊥)
    (hf_effective_domain_convex : Convex ℝ (effective_domain f))
    (hg_effective_domain_subset_interior_f_effective_domain :
      effective_domain g ⊆ interior (effective_domain f))
    (hf_toReal_smooth_on_interior_effective_domain :
      is_l_smooth_on (fun y ↦ (f y).toReal) (interior (effective_domain f))
        (PosReal.toNNReal Lf))
    (x : interior (effective_domain f)) :
    F (x : E) - F (T[Lf, f, g] x) ≥
      (((1 / (2 * (Lf : ℝ)) * ‖G[Lf, f, g] x‖ ^ (2 : ℕ) : ℝ) : EReal)) := by
  have hLf0 : (Lf : ℝ) ≠ 0 := (PosReal.coe_pos Lf).ne'
  have hhalf : (Lf : ℝ) - (Lf : ℝ) / 2 = (Lf : ℝ) / 2 := by ring
  have hcoeff :
      (((Lf : ℝ) - (Lf : ℝ) / 2) / (Lf : ℝ) ^ (2 : ℕ)) =
        1 / (2 * (Lf : ℝ)) := by
    rw [hhalf, pow_two]
    field_simp [hLf0]
  simpa [hcoeff] using
    (prox_grad_sufficient_decrease
      f g (PosReal.toNNReal Lf)
      hf_ne_bot
      hf_effective_domain_convex
      hg_effective_domain_subset_interior_f_effective_domain
      hf_toReal_smooth_on_interior_effective_domain
      Lf
      x)

end
