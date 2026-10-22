/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import Mathlib
import FirstOrderMethodsOptimization_Beck_2017.Chap06.Theorem_6_13
import FirstOrderMethodsOptimization_Beck_2017.Chap12.Definition_12_10
import FirstOrderMethodsOptimization_Beck_2017.Chap12.Algorithm_12_2

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u

open scoped RealInnerProductSpace

section

variable {E : Type u}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/- Proposition 12.9 is a `bridge/view` item in the denoising/proximal API.

Domain sampling in the minimal closure gives the relevant owner split:
- `source-facing`: `denoising_data_fidelity`, `denoising_problem_objective`, and
  `dual_proximal_gradient_primal_x_argmax`;
- `core/canonical`: `prox[...]`, `proximal_objective`, and
  `proximal_mapping_quadratic_perturbation`;
- `bridge/view`: this proposition, specialized to the identity map.

The primitive data here are only the datum `d`, the regularizer `g₁`, and the current dual point
`w`. The half-squared-distance formula is derived API from `denoising_problem_objective_apply`, so
the public surface should use the Chapter 12 denoising owner rather than repeating the quadratic
term inline. -/

-- Proof sketch: unfold `dual_proximal_gradient_primal_x_argmax` for `A = id`, convert the argmax
-- condition to an argmin condition by negating the objective, expand the denoising owner through
-- `denoising_problem_objective_apply`, and complete the square to identify the resulting
-- minimizer set with the Chapter 6 proximal objective for `g₁` at `d + w`.
/-- Proposition 12.9: for the Chapter 12 denoising objective with identity forward map, the
step-(a) argmax set is exactly the proximal set `prox[g1] (d + w)`. -/
theorem dual_proximal_gradient_primal_x_argmax_denoising_problem_objective_eq_prox
    (g1 : E → EReal) (d w : E) :
    dual_proximal_gradient_primal_x_argmax
      (denoising_problem_objective d g1 id)
      (LinearMap.id : E →ₗ[ℝ] E)
      w =
      prox[g1] (d + w) := by
  -- First convert the argmax problem into the proximal problem with a linear perturbation.
  calc
    dual_proximal_gradient_primal_x_argmax
        (denoising_problem_objective d g1 id)
        (LinearMap.id : E →ₗ[ℝ] E)
        w =
      prox[g1 + fun x : E ↦ ((inner ℝ (-w) x : ℝ) : EReal)] d := by
        let φ : E → EReal :=
          fun x ↦
            ((inner ℝ x w : ℝ) : EReal) -
              denoising_problem_objective d g1 id x
        let ψ : E → EReal :=
          proximal_objective (g1 + fun y : E ↦ ((inner ℝ (-w) y : ℝ) : EReal)) d
        have hψ : ψ = fun x : E ↦ -(φ x) := by
          funext x
          let r : EReal := ((((1 / 2 : ℝ) * ‖x - d‖ ^ (2 : ℕ)) : ℝ) : EReal)
          let q : EReal := r + g1 x
          let a : EReal := ((inner ℝ x w : ℝ) : EReal)
          have hr : ((‖x - d‖ ^ (2 : ℕ) / 2 : ℝ) : EReal) = r := by
            change (((‖x - d‖ ^ (2 : ℕ) / 2 : ℝ) : EReal) =
              (((1 / 2 : ℝ) * ‖x - d‖ ^ (2 : ℕ) : ℝ) : EReal))
            congr 1
            ring
          have hneg : -(a - q) = -a + q := by
            rw [EReal.neg_sub] <;> simp [a, q, r]
          have h1 : ψ x = g1 x + ((inner ℝ (-w) x : ℝ) : EReal) + r := by
            simp [ψ, r, add_assoc]
          have hF : denoising_problem_objective d g1 id x = q := by
            rw [denoising_problem_objective_apply, hr]
            simp [q, r, add_comm]
          have h2 : g1 x + ((inner ℝ (-w) x : ℝ) : EReal) + r = -a + q := by
            simp [a, q, r, real_inner_comm, add_assoc, add_left_comm, add_comm]
          rw [h1, h2]
          change -a + q = -(a - denoising_problem_objective d g1 id x)
          rw [hF]
          exact hneg.symm
        ext u
        rw [mem_dual_proximal_gradient_primal_x_argmax_iff, mem_proximal_mapping_iff,
          isMaxOn_univ_iff, isMinOn_univ_iff]
        constructor
        · intro hu v
          have hψu : ψ u = -(φ u) := by
            simpa using congrFun hψ u
          have hψv : ψ v = -(φ v) := by
            simpa using congrFun hψ v
          have huv : φ v ≤ φ u := by
            simpa [φ] using hu v
          change ψ u ≤ ψ v
          rw [hψu, hψv]
          exact EReal.neg_le_neg_iff.2 huv
        · intro hu v
          have hψu : ψ u = -(φ u) := by
            simpa using congrFun hψ u
          have hψv : ψ v = -(φ v) := by
            simpa using congrFun hψ v
          have huv := hu v
          change ψ u ≤ ψ v at huv
          rw [hψu, hψv] at huv
          have hφ : φ v ≤ φ u := EReal.neg_le_neg_iff.1 huv
          simpa [φ] using hφ
    _ = prox[g1] (d + w) := by
      -- Then specialize the quadratic-perturbation proximal identity with `c = 0`.
      have hc : -1 < (0 : ℝ) := by
        norm_num
      simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
        proximal_mapping_quadratic_perturbation g1 0 hc (-w) d

-- Proof sketch: rewrite membership using
-- `dual_proximal_gradient_primal_x_argmax_denoising_problem_objective_eq_prox`.
/-- Membership in the denoising step-(a) argmax set is equivalent to membership in the proximal
set `prox[g1] (d + w)`. -/
@[simp] theorem mem_dual_proximal_gradient_primal_x_argmax_denoising_problem_objective_iff
    {g1 : E → EReal} {d w u : E} :
    u ∈ dual_proximal_gradient_primal_x_argmax
      (denoising_problem_objective d g1 id)
      (LinearMap.id : E →ₗ[ℝ] E)
      w ↔
      u ∈ prox[g1] (d + w) := by
  rw [dual_proximal_gradient_primal_x_argmax_denoising_problem_objective_eq_prox]

end
