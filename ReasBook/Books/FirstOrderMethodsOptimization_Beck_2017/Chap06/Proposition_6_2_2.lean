/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import Mathlib
import FirstOrderMethodsOptimization_Beck_2017.Chap06.Proposition_6_2_1

-- Declarations for this item will be appended below by the statement pipeline.

universe u

noncomputable section

open scoped RealInnerProductSpace

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/- Proposition 6.2.2 is `source-facing` in the Chapter 6 proximal API. Domain sampling in the
minimal closure identifies the upstream owner abstractions:

- `prox[...]` and `proximal_objective` from Definition 6.1 as the `core/canonical` owners,
- `prox_eq_of_proximal_objective_eq_pos_mul_add_const` as the canonical objective-comparison API,
- `prox_add_const` as the owner-level theorem showing additive real constants are derived data,
- `prox_const_eq_singleton` from Proposition 6.2.1 as the constant-function computation,
- mathlib's `innerSL ℝ a` as the canonical owner of the rank-one functional `u ↦ ⟪a, u⟫`.

The primitive source-facing data for the proximal formula are only the linear coefficient `a` and
the base point `x`. The affine offset `b` is derived API because `prox_add_const` already removes
finite real constants from the objective. The completed-square constant is also derived proof data,
so the refinement should keep the normalized linear theorem as the main entry and recover the
affine `+ b` form only as a thin companion. -/

-- Proof sketch: rewrite the proximal objective for `u ↦ ⟪a, u⟫` as the proximal objective of a
-- constant function at the shifted base point `x - a` by completing the square, then conclude
-- with the owner comparison theorem plus Proposition 6.2.1.
/-- Proposition 6.2.2: for the linear functional `u ↦ ⟪a, u⟫_ℝ`, the proximal mapping at `x` is
the singleton `{x - a}`. Equivalently, the proximal operator of this rank-one functional
translates `x` by `-a`. -/
theorem prox_inner_eq_singleton_sub (a x : E) :
    prox[fun u ↦ ((⟪a, u⟫ : ℝ) : EReal)] x = {x - a} := by
  let x' : E := x - a
  let c : ℝ := ⟪a, x⟫ - (1 / 2 : ℝ) * ‖a‖ ^ (2 : ℕ)
  have hobjective (u : E) :
      proximal_objective (fun v ↦ ((⟪a, v⟫ : ℝ) : EReal)) x u =
        ((1 : ℝ) : EReal) * proximal_objective (fun _ ↦ (c : EReal)) x' u + (0 : EReal) := by
    simpa [proximal_objective] using
      (show (((⟪a, u⟫ : ℝ) + (1 / 2 : ℝ) * ‖u - x‖ ^ (2 : ℕ) : ℝ) : EReal) =
          (((c : ℝ) + (1 / 2 : ℝ) * ‖u - x'‖ ^ (2 : ℕ) : ℝ) : EReal) from by
        exact_mod_cast show
          (⟪a, u⟫ : ℝ) + (1 / 2 : ℝ) * ‖u - x‖ ^ (2 : ℕ) =
            c + (1 / 2 : ℝ) * ‖u - x'‖ ^ (2 : ℕ) by
          dsimp [c, x']
          rw [norm_sub_sq_real, norm_sub_sq_real, norm_sub_sq_real x a, inner_sub_right]
          rw [real_inner_comm a u, real_inner_comm x a]
          ring)
  calc
    prox[fun u ↦ ((⟪a, u⟫ : ℝ) : EReal)] x = prox[fun _ ↦ (c : EReal)] x' := by
      exact prox_eq_of_proximal_objective_eq_pos_mul_add_const zero_lt_one hobjective
    _ = {x'} := prox_const_eq_singleton c x'
    _ = {x - a} := by simp [x']

-- Proof sketch: remove the additive constant from the affine objective with `prox_add_const`, then
-- apply the normalized linear computation above.
/-- For the affine function `u ↦ ⟪a, u⟫_ℝ + b`, the proximal mapping at `x` is still the singleton
`{x - a}`; the additive constant is derived data and does not affect `prox`. -/
theorem prox_inner_add_const_eq_singleton_sub (a x : E) (b : ℝ) :
    prox[fun u ↦ ((⟪a, u⟫ + b : ℝ) : EReal)] x = {x - a} := by
  have hconst :
      prox[fun u ↦ ((⟪a, u⟫ + b : ℝ) : EReal)] x =
        prox[fun u ↦ ((⟪a, u⟫ : ℝ) : EReal)] x := by
    change prox[fun u ↦ (Real.toEReal ∘ innerSL ℝ a) u + (b : EReal)] x =
      prox[Real.toEReal ∘ innerSL ℝ a] x
    simpa [Function.comp, innerSL_apply_apply, EReal.coe_add] using
      congrFun (prox_add_const (Real.toEReal ∘ innerSL ℝ a) b) x
  calc
    prox[fun u ↦ ((⟪a, u⟫ + b : ℝ) : EReal)] x =
        prox[fun u ↦ ((⟪a, u⟫ : ℝ) : EReal)] x := hconst
    _ = {x - a} := prox_inner_eq_singleton_sub a x

end
