/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import Mathlib
import FirstOrderMethodsOptimization_Beck_2017.Chap06.Definition_6_1

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u

open scoped Pointwise RealInnerProductSpace

section

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/- Theorem 6.13 is `source-facing` in the Chapter 6 proximal-operator API. Domain sampling in the
minimal closure separates the layers as follows:

- `source-facing`: this theorem, stated directly on the proximal owner `prox[...]`;
- `core/canonical`: `proximal_objective`, `prox[...]`, `prox_add_const`, and
  `prox_eq_of_proximal_objective_eq_pos_mul_add_const` from Definition 6.1;
- `bridge/view`: the nearby proximal transport theorems
  `proximal_mapping_scaling_translation` and
  `proximal_mapping_smul_precompose_inv_smul`.

The primitive data here are only the objective `g`, the quadratic coefficient `c`, the linear
perturbation vector `a`, and the base point `x`. Additive constants are already handled by the
owner-level API, so they should not remain primitive data in the main public statement. The public
statement therefore stays directly on `prox[...]`, with the completed-square identity used only in
the proof rather than via a local wrapper around the transformed objective. -/

-- Proof sketch: expand the proximal objective for the quadratic perturbation, combine the two
-- quadratic terms into `((c + 1) / 2) * ‖u - ((c + 1)⁻¹ • (x - a))‖^2` up to an additive
-- constant, and then factor out the positive scalar `c + 1`. The resulting minimization problem
-- is exactly the
-- proximal objective for the scaled function `u ↦ (1 / (c + 1)) g u` at
-- `((c + 1)⁻¹) • (x - a)`.
/-- Theorem 6.13: quadratic perturbation for the source-facing proximal mapping. For
`f u = g u + (c / 2) ‖u‖² + ⟪a, u⟫` with `c > -1`, the proximal points of `f` at `x` are exactly
the proximal points of the scaled function `u ↦ (1 / (c + 1)) g u` at the shifted base point
`((c + 1)⁻¹) • (x - a)`. The textbook properness hypothesis on `g` is redundant for this
minimizer-set identity, the additive constant term is already covered upstream by `prox_add_const`,
and the textbook condition `c > 0` is stronger than needed: the completed-square argument only
requires `c + 1 > 0`. -/
theorem proximal_mapping_quadratic_perturbation
    (g : E → EReal) (c : ℝ) (hc : -1 < c) (a x : E) :
    prox[g + fun u ↦ (((c / 2 : ℝ) * ‖u‖ ^ 2 + ⟪a, u⟫ : ℝ) : EReal)] x =
      prox[((c + 1)⁻¹ : EReal) • g] (((c + 1)⁻¹) • (x - a)) := by
  set f : E → EReal := g + fun u ↦ (((c / 2 : ℝ) * ‖u‖ ^ 2 + ⟪a, u⟫ : ℝ) : EReal)
  set s : ℝ := c + 1
  set x' : E := s⁻¹ • (x - a)
  set g' : E → EReal := (s⁻¹ : EReal) • g
  set δ : ℝ := (1 / 2 : ℝ) * ‖x‖ ^ 2 - ((c + 1) / 2 : ℝ) * ‖x'‖ ^ 2
  have hs : 0 < s := by
    dsimp [s]
    linarith
  have hs_mul_inv : (s : EReal) * (s⁻¹ : EReal) = 1 := by
    change ((s * s⁻¹ : ℝ) : EReal) = 1
    exact_mod_cast mul_inv_cancel₀ hs.ne'
  have hobjective (u : E) :
      proximal_objective f x u =
        ((s : EReal) * proximal_objective g' x' u) +
          (δ : EReal) := by
    have hreal :
        (((c / 2 : ℝ) * ‖u‖ ^ 2) + ⟪a, u⟫ : ℝ) + (1 / 2 : ℝ) * ‖u - x‖ ^ 2 =
          s * ((1 / 2 : ℝ) * ‖u - x'‖ ^ 2) + δ := by
      rw [norm_sub_sq_real, norm_sub_sq_real, inner_smul_right, inner_sub_right]
      rw [real_inner_comm a u]
      simp only [x', δ, s, one_div]
      set α : ℝ := ⟪a, u⟫
      set β : ℝ := ⟪u, x⟫
      ring_nf
      have hsum : c * (1 + c)⁻¹ + (1 + c)⁻¹ = (1 : ℝ) := by
        calc
          c * (1 + c)⁻¹ + (1 + c)⁻¹ = (c + 1) * (1 + c)⁻¹ := by ring
          _ = 1 := by
            rw [show c + 1 = 1 + c by ring, mul_inv_cancel₀]
            linarith
      have hα : α * 2 = c * α * (1 + c)⁻¹ * 2 + α * (1 + c)⁻¹ * 2 := by
        calc
          α * 2 = (c * (1 + c)⁻¹ + (1 + c)⁻¹) * (α * 2) := by rw [hsum, one_mul]
          _ = c * α * (1 + c)⁻¹ * 2 + α * (1 + c)⁻¹ * 2 := by ring
      have hβ : β * 2 = c * β * (1 + c)⁻¹ * 2 + β * (1 + c)⁻¹ * 2 := by
        calc
          β * 2 = (c * (1 + c)⁻¹ + (1 + c)⁻¹) * (β * 2) := by rw [hsum, one_mul]
          _ = c * β * (1 + c)⁻¹ * 2 + β * (1 + c)⁻¹ * 2 := by ring
      nlinarith [hα, hβ]
    have hreal_ereal :
        (((((c / 2 : ℝ) * ‖u‖ ^ 2) + ⟪a, u⟫ +
            (1 / 2 : ℝ) * ‖u - x‖ ^ 2 : ℝ)) : EReal) =
          (((s * ((1 / 2 : ℝ) * ‖u - x'‖ ^ 2) + δ : ℝ) : EReal)) := by
      exact_mod_cast hreal
    calc
      proximal_objective f x u
        = g u + (((((c / 2 : ℝ) * ‖u‖ ^ 2) + ⟪a, u⟫ +
            (1 / 2 : ℝ) * ‖u - x‖ ^ 2 : ℝ)) : EReal) := by
            simp [f, proximal_objective, EReal.coe_add, EReal.coe_mul, add_assoc, add_comm]
      _ = g u + (((s * ((1 / 2 : ℝ) * ‖u - x'‖ ^ 2) + δ : ℝ) : EReal)) := by
            rw [hreal_ereal]
      _ = g u + ((s : EReal) *
            ((((1 / 2 : ℝ) * ‖u - x'‖ ^ 2 : ℝ)) : EReal)) + (δ : EReal) := by
            rw [EReal.coe_add, EReal.coe_mul]
            ac_rfl
      _ = ((s : EReal) * proximal_objective g' x' u) + (δ : EReal) := by
            have hg :
                (s : EReal) * ((s⁻¹ : EReal) * g u) = g u := by
              simpa [mul_assoc] using congrArg (fun z : EReal ↦ z * g u) hs_mul_inv
            dsimp [proximal_objective]
            rw [EReal.left_distrib_of_nonneg_of_ne_top]
            · let q : EReal := ((((1 / 2 : ℝ) * ‖u - x'‖ ^ 2 : ℝ)) : EReal)
              simpa [g', q, add_assoc] using
                congrArg
                  (fun t : EReal ↦ t + ((s : EReal) * q) + (δ : EReal))
                  hg.symm
            · exact_mod_cast hs.le
            · exact EReal.coe_ne_top _
  simpa [f, g', s, x'] using
    prox_eq_of_proximal_objective_eq_pos_mul_add_const
      hs hobjective

end
