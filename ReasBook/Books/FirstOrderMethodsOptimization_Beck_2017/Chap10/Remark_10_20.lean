/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import FirstOrderMethodsOptimization_Beck_2017.Chap10.Algorithm_10_66
import FirstOrderMethodsOptimization_Beck_2017.Chap10.Definition_10_2

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u

open scoped Gradient

section

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/- Remark 10.20 is `bridge/view` in the Chapter 10 proximal-gradient API.

Domain sampling in the proximal-gradient layer identifies:
- `is_proximal_gradient_trajectory` from Algorithm 10.1 as the source-facing owner for the
  iterate sequence `x^k`;
- `mem_proximal_gradient_step_iff_isMinOn_curvature_model` from Algorithm 10.66 as the canonical
  curvature-model bridge for one proximal-gradient step in the complete inner-product setting;
- `composite_model_objective` from Definition 10.2 as the chapter owner for the composite value
  `F = f + g`;
- the stronger `ProperSpace`/single-valued bridge
  `prox_grad_sufficient_decrease_of_upper_model` as the packaged descendant of the same
  upper-model mechanism once `g` is upgraded to the prox-gradient operator setting.

Primitive data here are therefore just:
- a proximal-gradient trajectory `x`;
- Chapter 3 differentiability of `f` at the current iterate `x^k`, ensuring that the displayed
  gradient is the genuine textbook gradient;
- the explicit upper-model inequality at the realized successor iterate `x^(k+1)`.

The curvature-model comparison and the resulting monotonicity consequence are derived API from
that source-facing data, so this file keeps the weaker trajectory-level monotonicity formulation
as the main entry rather than strengthening it to the single-valued B2 owner. In particular, the
owner `is_proximal_gradient_trajectory` already lives over `[CompleteSpace E]`, so
finite-dimensionality would be non-primitive ambient data here and is intentionally not part of
the public API. -/

section

variable {f g : E → EReal} {x : ℕ → E} {L : ℕ → PosReal}

local notation "F" => composite_model_objective f g

-- Proof sketch: use `is_proximal_gradient_trajectory_step` together with the canonical
-- curvature-model bridge from Algorithm 10.66 to view `x (k + 1)` as a minimizer of the one-step
-- quadratic model at `x k`. Testing that minimizing property against `x k` bounds the curvature
-- model at `x (k + 1)` by `F (x k)`.
/-- Along a proximal-gradient trajectory, the one-step curvature model at `x^k` evaluated at the
realized successor iterate `x^(k+1)` is bounded above by the current composite objective
`F(x^k)`. -/
lemma proximal_gradient_curvature_model_next_le_current
    (htraj : is_proximal_gradient_trajectory f g x L) (k : ℕ)
    (hfxk : is_differentiable_at f (x k)) :
    proximal_gradient_curvature_model f g (x k) (L k) (x (k + 1)) ≤ F (x k) := by
  have hstep :
      x (k + 1) ∈ proximal_gradient_step f g (x k) (L k) :=
    (is_proximal_gradient_trajectory_step htraj k).2
  have hmin :
      IsMinOn (proximal_gradient_curvature_model f g (x k) (L k)) Set.univ (x (k + 1)) :=
    (mem_proximal_gradient_step_iff_isMinOn_curvature_model hfxk).1 hstep
  rw [isMinOn_univ_iff] at hmin
  simpa [composite_model_objective_apply, proximal_gradient_curvature_model_apply] using hmin (x k)

-- Proof sketch: use the upper-model hypothesis to bound `F (x^(k+1))` by the curvature model at
-- `x^(k+1)`, then apply the preceding minimizing-property comparison against `x^k`.
/-- Remark 10.20: if `x` is a proximal-gradient trajectory for `f + g`, `f` is differentiable at
`x^k` in the Chapter 3 sense, and the local quadratic upper model of `f` holds at the realized
successor iterate `x^(k+1)`, then the composite objective is monotone at that step:
`F(x^(k+1)) ≤ F(x^k)`, where `F = f + g`. -/
theorem composite_model_objective_monotone_of_upper_model
    (htraj : is_proximal_gradient_trajectory f g x L) (k : ℕ)
    (hfxk : is_differentiable_at f (x k))
    (hmodel :
      f (x (k + 1)) ≤
        (((f (x k)).toReal +
            inner ℝ (∇ (fun y ↦ (f y).toReal) (x k)) (x (k + 1) - x k) +
            ((L k : ℝ) / 2) * ‖x (k + 1) - x k‖ ^ (2 : ℕ) : ℝ) : EReal)) :
    F (x (k + 1)) ≤ F (x k) := by
  have hxk_finite : x k ∈ finite_domain f := interior_subset hfxk.1
  have hfxk_top : f (x k) ≠ ⊤ := (mem_finite_domain.mp hxk_finite).1.ne
  have hfxk_bot : f (x k) ≠ ⊥ := (mem_finite_domain.mp hxk_finite).2
  have hfxk_value : (((f (x k)).toReal : ℝ) : EReal) = f (x k) :=
    EReal.coe_toReal hfxk_top hfxk_bot
  have hnext_le_model :
      F (x (k + 1)) ≤ proximal_gradient_curvature_model f g (x k) (L k) (x (k + 1)) := by
    rw [composite_model_objective_apply, proximal_gradient_curvature_model_apply]
    have hmodel' :
        f (x (k + 1)) ≤
          f (x k) +
            ((inner ℝ (∇ (fun y ↦ (f y).toReal) (x k)) (x (k + 1) - x k) : ℝ) : EReal) +
            ((((L k : ℝ) / 2) * ‖x (k + 1) - x k‖ ^ (2 : ℕ) : ℝ) : EReal) := by
      simpa [hfxk_value, add_assoc] using hmodel
    have hsum := add_le_add_right hmodel' (g (x (k + 1)))
    simpa [add_assoc, add_left_comm, add_comm] using hsum
  exact le_trans hnext_le_model (proximal_gradient_curvature_model_next_le_current htraj k hfxk)

end

section

variable {E : Type u} [NormedAddCommGroup E]
variable {f g : E → EReal} {x : ℕ → E} {L : ℕ → PosReal}

local notation "F" => composite_model_objective f g

-- Proof sketch: the correction term in the descent inequality is nonnegative because `L k > 0`
-- by definition of `PosReal` and squared norms are nonnegative. Dropping this term gives the
-- monotonicity of the composite objective values.
/-- Helper for Remark 10.20: the quadratic correction term appearing in the descent estimate is
always nonnegative. -/
lemma proximal_gradient_quadratic_term_nonneg (k : ℕ) :
    0 ≤ ((((L k : ℝ) / 2) * ‖x (k + 1) - x k‖ ^ (2 : ℕ) : ℝ) : EReal) := by
  -- Positivity of the stepsize and of squared norms gives positivity of the real coefficient.
  have hL_half_nonneg : 0 ≤ (L k : ℝ) / 2 := by
    have hL_pos : 0 < (L k : ℝ) := PosReal.coe_pos (L k)
    linarith
  have hsq_nonneg : 0 ≤ ‖x (k + 1) - x k‖ ^ (2 : ℕ) := by
    exact sq_nonneg ‖x (k + 1) - x k‖
  exact_mod_cast mul_nonneg hL_half_nonneg hsq_nonneg

/-- A quadratic descent bound for one proximal-gradient step implies monotonicity of the composite
objective at that step. -/
theorem composite_model_objective_monotone_of_descent_ineq
    {k : ℕ}
    (hdescent :
      F (x (k + 1)) +
          ((((L k : ℝ) / 2) * ‖x (k + 1) - x k‖ ^ (2 : ℕ) : ℝ) : EReal) ≤
        F (x k)) :
    F (x (k + 1)) ≤ F (x k) := by
  -- First insert the nonnegative correction term on the left-hand side.
  have hleft :
      F (x (k + 1)) ≤
        F (x (k + 1)) +
          ((((L k : ℝ) / 2) * ‖x (k + 1) - x k‖ ^ (2 : ℕ) : ℝ) : EReal) := by
    exact le_add_of_nonneg_right (proximal_gradient_quadratic_term_nonneg k)
  -- Then compose with the assumed descent estimate.
  exact le_trans hleft hdescent

end

end
