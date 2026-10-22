/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import FirstOrderMethodsOptimization_Beck_2017.Chap10.Algorithm_10_3
import FirstOrderMethodsOptimization_Beck_2017.Chap10.Definition_10_2
import FirstOrderMethodsOptimization_Beck_2017.Chap10.Definition_10_5
import FirstOrderMethodsOptimization_Beck_2017.Chap10.Remark_10_13
import FirstOrderMethodsOptimization_Beck_2017.Chap10.Theorem_10_16

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u

open scoped Gradient

section

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [ProperSpace E]
variable {f g : E → EReal} [IsProperExtendedRealFunction g]
  [Fact (LowerSemicontinuous g)] [Fact (is_convex_function g)]

local notation "F" => composite_model_objective f g

/-- Helper for Corollary 10.18: specializing the fundamental prox-gradient inequality at the base
point `x` removes the comparison-distance term. -/
lemma fundamental_prox_grad_inequality_at_base_point
    (L : PosReal) (x : interior (effective_domain f))
    (hupper : proximal_gradient_backtracking_B2_accepts f g L x) :
    F x - F (T[L, f, g] x) ≥
      ((((L : ℝ) / 2) * ‖(x : E) - T[L, f, g] x‖ ^ (2 : ℕ) : ℝ) : EReal) +
        ℓ[f, (x : E), x] := by
  -- Specialize Theorem 10.16 with the comparison point equal to the base point.
  simpa [sub_self] using
    (fundamental_prox_grad_inequality (f := f) (g := g) (x := (x : E)) (y := x) L hupper)

/-- Helper for Corollary 10.18: the first-order linearization defect vanishes at its own base
point. -/
lemma prox_gradient_linearization_defect_self
    (hf_ne_bot : ∀ y, f y ≠ ⊥)
    (x : interior (effective_domain f)) :
    ℓ[f, (x : E), x] = 0 := by
  have hx_ne_top : f (x : E) ≠ ⊤ := (mem_effective_domain.mp (interior_subset x.2)).ne
  have hx_val : f (x : E) = (((f (x : E)).toReal : ℝ) : EReal) := by
    exact (EReal.coe_toReal hx_ne_top (hf_ne_bot _)).symm
  -- Expand the defect, identify both function values with the same real coercion, and cancel.
  rw [prox_gradient_linearization_defect_eq, hx_val, hx_val]
  simp

/-- Helper for Corollary 10.18: the quadratic step term equals the standard gradient-mapping
lower-bound coefficient. -/
lemma half_step_norm_eq_gradient_mapping_term
    (L : PosReal) (x : interior (effective_domain f)) :
    ((((L : ℝ) / 2) * ‖(x : E) - T[L, f, g] x‖ ^ (2 : ℕ) : ℝ) : EReal) =
      (((1 : ℝ) / (2 * (L : ℝ)) * ‖G[L, f, g] x‖ ^ (2 : ℕ) : ℝ) : EReal) := by
  have hL0 : (L : ℝ) ≠ 0 := (PosReal.coe_pos L).ne'
  have hreal :
      ((L : ℝ) / 2) * ‖(x : E) - T[L, f, g] x‖ ^ (2 : ℕ) =
        (1 : ℝ) / (2 * (L : ℝ)) * ‖G[L, f, g] x‖ ^ (2 : ℕ) := by
    -- Rewrite the gradient mapping norm through the residual step norm, then simplify scalars.
    rw [gradient_mapping_norm_sq_eq_scaled_step_norm_sq (f := f) (g := g) L x]
    field_simp [hL0]
  exact congrArg (fun t : ℝ ↦ ((t : ℝ) : EReal)) hreal

/-- Corollary 10.18: if the local quadratic upper model of `f` at the prox-grad step `T_L(x)`
holds, then the composite objective decreases by at least
`(1 / (2L)) ‖G_L(x)‖²`. The standing composite-model hypothesis `f y ≠ ⊥` for all `y`
is kept explicit here because it is part of the chapter setup used to interpret the displayed
extended-real subtraction. -/
theorem prox_grad_sufficient_decrease_of_upper_model
    (hf_ne_bot : ∀ y, f y ≠ ⊥)
    (L : PosReal) (x : interior (effective_domain f))
    (hupper : proximal_gradient_backtracking_B2_accepts f g L x) :
    F x - F (T[L, f, g] x) ≥
      (((1 : ℝ) / (2 * (L : ℝ)) * ‖G[L, f, g] x‖ ^ (2 : ℕ) : ℝ) : EReal) := by
  -- Follow the source proof: prox-optimality plus the upper model gives the base inequality.
  calc
    F x - F (T[L, f, g] x) ≥
        ((((L : ℝ) / 2) * ‖(x : E) - T[L, f, g] x‖ ^ (2 : ℕ) : ℝ) : EReal) +
          ℓ[f, (x : E), x] :=
      fundamental_prox_grad_inequality_at_base_point (f := f) (g := g) L x hupper
    _ = ((((L : ℝ) / 2) * ‖(x : E) - T[L, f, g] x‖ ^ (2 : ℕ) : ℝ) : EReal) := by
      -- At the base point, the linearization defect is exactly zero.
      rw [prox_gradient_linearization_defect_self (f := f) hf_ne_bot x]
      simp
    _ = (((1 : ℝ) / (2 * (L : ℝ)) * ‖G[L, f, g] x‖ ^ (2 : ℕ) : ℝ) : EReal) := by
      -- Convert the prox-step norm into the gradient-mapping norm.
      rw [half_step_norm_eq_gradient_mapping_term (f := f) (g := g) L x]

end
