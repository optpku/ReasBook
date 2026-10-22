/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import Mathlib
import FirstOrderMethodsOptimization_Beck_2017.Chap05.Lemma_5_7
import FirstOrderMethodsOptimization_Beck_2017.Chap10.Algorithm_10_61

local notation "Λ[" a "]" => primalCounterparts a

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u

open scoped DualNorm

section

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]

/- Lemma 10.65 is `source-facing`: it is the one-step sufficient-decrease estimate for the
non-Euclidean gradient method. Domain sampling points to the Chapter 5 smoothness owner
`is_l_smooth_on`, Chapter 10's dual-norm owner surface `‖·‖_*`, Chapter 6's positive-scalar
owner `PosReal`, and Chapter 10's primal-counterpart owner `Λ[·]` for the chosen descent
direction. The primitive data are therefore just the current point `x`, the positive curvature
parameter `L`, and the chosen primal counterpart `xDagger`; the trial iterate is the displayed
update `x - (‖f'(x)‖_* / L) • xDagger`, not an additional packaged owner. -/

-- Proof sketch: use `hf` on `Set.univ` to obtain differentiability of `f` at `x` and the
-- descent estimate for the pair
-- `(x, x - (‖f'(x)‖_* / L) • xDagger)`. Rewrite the derivative pairing with
-- `apply_eq_norm_of_mem_primalCounterparts hDagger`, and reduce the squared norm term with
-- `norm_eq_one_of_mem_primalCounterparts (by intro h; simpa [h] using hDagger) hDagger`.
/-- Helper for Lemma 10.65: the primal-counterpart equality rewrites the linear term in the
non-Euclidean step. -/
lemma scaled_primal_counterpart_pairing
    {a : E →L[ℝ] ℝ} {xDagger : E} (hDagger : xDagger ∈ Λ[a]) (L : PosReal) :
    a (-(‖a‖ / (L : ℝ)) • xDagger) = -((‖a‖ / (L : ℝ)) * ‖a‖) := by
  -- Expand the scalar action and use the norm-attainment identity from `Λ[a]`.
  calc
    a (-(‖a‖ / (L : ℝ)) • xDagger) = (-(‖a‖ / (L : ℝ))) * a xDagger := by
      simp
    _ = -((‖a‖ / (L : ℝ)) * ‖a‖) := by
      rw [apply_eq_norm_of_mem_primalCounterparts hDagger]
      ring

/-- Helper for Lemma 10.65: the step direction has squared norm at most the square of its
scalar coefficient because primal counterparts lie in the unit ball. -/
lemma scaled_primal_counterpart_norm_sq_le
    {a : E →L[ℝ] ℝ} {xDagger : E} (hDagger : xDagger ∈ Λ[a]) (L : PosReal) :
    ‖-(‖a‖ / (L : ℝ)) • xDagger‖ ^ (2 : ℕ) ≤ (‖a‖ / (L : ℝ)) ^ (2 : ℕ) := by
  have hscale_nonneg : 0 ≤ ‖a‖ / (L : ℝ) := by
    exact div_nonneg (norm_nonneg _) L.2.le
  have hnorm :
      ‖-(‖a‖ / (L : ℝ)) • xDagger‖ ≤ ‖a‖ / (L : ℝ) := by
    calc
      ‖-(‖a‖ / (L : ℝ)) • xDagger‖ = (‖a‖ / (L : ℝ)) * ‖xDagger‖ := by
        rw [norm_smul, Real.norm_eq_abs, abs_neg, abs_of_nonneg hscale_nonneg]
      _ ≤ (‖a‖ / (L : ℝ)) * 1 := by
        exact mul_le_mul_of_nonneg_left hDagger.1 hscale_nonneg
      _ = ‖a‖ / (L : ℝ) := by
        ring
  have hleft_nonneg : 0 ≤ ‖-(‖a‖ / (L : ℝ)) • xDagger‖ := norm_nonneg _
  have hright_nonneg : 0 ≤ ‖a‖ / (L : ℝ) := hscale_nonneg
  -- Square the norm bound to match the quadratic remainder term.
  nlinarith [hnorm, hleft_nonneg, hright_nonneg]

/-- Lemma 10.65: if `f` is globally `L_f`-smooth and `xDagger ∈ Λ_{f'(x)}`, then the
non-Euclidean trial point
`x - (‖f'(x)‖_* / L) • xDagger`
satisfies the sufficient-decrease inequality
`f(x - (‖f'(x)‖_* / L) • xDagger) ≤ f(x) - ((L - L_f / 2) / L^2) ‖f'(x)‖_*^2`. -/
theorem non_euclidean_gradient_method_sufficient_decrease
    {f : E → ℝ} {Lf : NNReal} (hf : is_l_smooth_on f Set.univ Lf)
    (x : E) (L : PosReal) (xDagger : E)
    (hDagger : xDagger ∈ Λ[fderiv ℝ f x]) :
    f (x - (‖fderiv ℝ f x‖_* / (L : ℝ)) • xDagger) ≤
      f x -
        (((L : ℝ) - (Lf : ℝ) / 2) / (L : ℝ) ^ 2) *
          ‖fderiv ℝ f x‖_* ^ 2 := by
  set a : E →L[ℝ] ℝ := fderiv ℝ f x
  set α : ℝ := ‖a‖ / (L : ℝ)
  set d : E := -α • xDagger
  have htrial : x + d = x - (‖fderiv ℝ f x‖_* / (L : ℝ)) • xDagger := by
    simp [a, α, d, sub_eq_add_neg]
  have hdescent :
      f (x + d) ≤ f x + a d + ((Lf : ℝ) / 2) * ‖d‖ ^ (2 : ℕ) := by
    -- Apply the Banach-space descent lemma to the trial point `x + d`.
    simpa [a, d] using
      is_l_smooth_on_univ_fderiv_descent hf x (x + d)
  have hpair : a d = -((α : ℝ) * ‖a‖) := by
    -- The primal-counterpart equality identifies the linear term with `-α ‖a‖`.
    simpa [α, d] using scaled_primal_counterpart_pairing hDagger L
  have hnorm_sq : ‖d‖ ^ (2 : ℕ) ≤ α ^ (2 : ℕ) := by
    -- The unit-ball part of `Λ[a]` controls the norm of the step direction.
    simpa [α, d] using scaled_primal_counterpart_norm_sq_le hDagger L
  have hquad :
      ((Lf : ℝ) / 2) * ‖d‖ ^ (2 : ℕ) ≤ ((Lf : ℝ) / 2) * α ^ (2 : ℕ) := by
    exact mul_le_mul_of_nonneg_left hnorm_sq (by positivity)
  have hL_ne : (L : ℝ) ≠ 0 := by
    exact ne_of_gt L.2
  have hcoeff :
      f x + (-((α : ℝ) * ‖a‖) + ((Lf : ℝ) / 2) * α ^ (2 : ℕ)) =
        f x - (((L : ℝ) - (Lf : ℝ) / 2) / (L : ℝ) ^ 2) * ‖a‖ ^ (2 : ℕ) := by
    -- Normalize the coefficient of `‖a‖²` to the textbook form.
    dsimp [α]
    field_simp [hL_ne]
    ring
  have hmain :
      f (x + d) ≤
        f x - (((L : ℝ) - (Lf : ℝ) / 2) / (L : ℝ) ^ 2) * ‖a‖ ^ (2 : ℕ) := by
    calc
      f (x + d) ≤ f x + a d + ((Lf : ℝ) / 2) * ‖d‖ ^ (2 : ℕ) := hdescent
      _ = f x + (-((α : ℝ) * ‖a‖) + ((Lf : ℝ) / 2) * ‖d‖ ^ (2 : ℕ)) := by
            rw [hpair]
            ring
      _ ≤ f x + (-((α : ℝ) * ‖a‖) + ((Lf : ℝ) / 2) * α ^ (2 : ℕ)) := by
            linarith
      _ = f x - (((L : ℝ) - (Lf : ℝ) / 2) / (L : ℝ) ^ 2) * ‖a‖ ^ (2 : ℕ) := hcoeff
  -- Rewrite the trial point and derivative norm back to the source-facing statement.
  simpa [a, htrial] using hmain

end
