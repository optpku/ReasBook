/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Definition_5_3_2

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Gradient HessianLocalNorm

noncomputable section

universe u

/- Proposition 5.3.3 lies in the Chapter 5 barrier-parameter / local-Hessian-norm domain.

Sampled owner-style declarations in this domain:
* `IsSelfConcordantBarrierOnWith.barrier_parameter_bound` in `Definition_5_3_2`, the source
  owner inequality for a `ν`-self-concordant barrier;
* `hessianLocalNorm` and the notation `‖u‖[F; x]` in `Definition_5_1_1`, the chapter owner for
  the Hessian-induced local norm;
* `hessianLocalNorm_def` in `Definition_5_1_1`, the canonical owner expansion;
* `sublevelLogBarrier_hessian_quadraticForm_ge_gradient_sq` in `Theorem_5_1_4`, the earlier
  quadratic-form inequality in the same Chapter 5 differential domain.

Source/core/bridge triage:
* source-facing: the fixed-point barrier inequality at `x`;
* core/canonical: the Hessian local norm `‖u‖[F; x]`;
* bridge/view: `hessianLocalNorm_def` together with `Real.sq_sqrt`, which recovers
  `inner ℝ u (hessian F x u)` from that owner.

Primitive data:
* a function `F`;
* a barrier parameter `ν`;
* a base point `x`.
* pointwise Hessian positivity at `x`.

Derived API:
* the equivalent local-norm-square estimate
  `⟪∇ F(x), u⟫² ≤ ν ‖u‖[F; x]^2`;
* the raw Hessian-quadratic-form presentation, recovered canonically from
  `hessianLocalNorm_def`.

This proposition therefore keeps the source-facing left-hand side from
`IsSelfConcordantBarrierOnWith.barrier_parameter_bound`, but refines the right-hand side to the
chapter owner `‖u‖[F; x]` instead of repeating the quadratic form inline. The pointwise theorem
below is the public bridge, and barrier-owner applications should use it with the Hessian
positivity already supplied by `IsSelfConcordantOnWith.hessian_isPositive`. -/

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- Helper for Proposition 5.3.3: squaring the Chapter 5 local norm recovers the raw Hessian
quadratic form once that quadratic form is known to be nonnegative. -/
private theorem sq_hessianLocalNorm_eq_inner_hessian
    {F : E → ℝ} {x u : E} (hquad : 0 ≤ inner ℝ u (hessian F x u)) :
    ‖u‖[F; x] ^ (2 : ℕ) = inner ℝ u (hessian F x u) := by
  -- The local norm is defined as the square root of the Hessian quadratic form.
  simpa [hessianLocalNorm_def] using Real.sq_sqrt hquad

/-- Helper for Proposition 5.3.3: evaluating the barrier expression on a scaled direction `t • u`
produces the expected scalar quadratic family in `t`. -/
private theorem barrier_expression_smul
    {F : E → ℝ} {x u : E} (t : ℝ) :
    2 * inner ℝ (∇ F x) (t • u) - inner ℝ (t • u) (hessian F x (t • u)) =
      2 * t * inner ℝ (∇ F x) u - t ^ (2 : ℕ) * inner ℝ u (hessian F x u) := by
  -- Pull the scalar through the gradient pairing and the Hessian quadratic form.
  simp [inner_smul_left, inner_smul_right, pow_two, mul_comm, mul_left_comm, mul_assoc]

/-- Helper for Proposition 5.3.3: a scalar quadratic family bounded above by `ν` forces the
discriminant-style estimate `a² ≤ ν b`. -/
private theorem sq_le_mul_of_barrier_line_family
    {a b ν : ℝ} (hb : 0 ≤ b)
    (hline : ∀ t : ℝ, 2 * t * a - t ^ (2 : ℕ) * b ≤ ν) :
    a ^ (2 : ℕ) ≤ ν * b := by
  by_cases hb0 : b = 0
  · by_cases ha0 : a = 0
    · -- If both coefficients vanish, the quadratic bound is immediate.
      simp [ha0, hb0]
    · -- If `b = 0`, the family is linear in `t`; testing a large multiple contradicts boundedness.
      have htest := hline ((ν + 1) / (2 * a))
      have hcontr : ν + 1 ≤ ν := by
        have hrew : 2 * ((ν + 1) / (2 * a)) * a ≤ ν := by
          simpa [hb0] using htest
        field_simp [ha0] at hrew
        linarith
      linarith
  · have hb_pos : 0 < b := lt_of_le_of_ne hb (by simpa [eq_comm] using hb0)
    have hb_ne : b ≠ 0 := ne_of_gt hb_pos
    have htest := hline (a / b)
    have hquot : a ^ (2 : ℕ) / b ≤ ν := by
      have hrewrite :
          2 * (a / b) * a - (a / b) ^ (2 : ℕ) * b = a ^ (2 : ℕ) / b := by
        field_simp [hb_ne]
        ring
      simpa [hrewrite] using htest
    -- Multiply the quotient estimate by the positive scalar `b`.
    exact (_root_.div_le_iff₀ hb_pos).1 hquot

/-- Helper for Proposition 5.3.3: the squared estimate `a² ≤ ν s²` implies the original scalar
barrier inequality `2a - s² ≤ ν`. -/
private theorem barrier_line_of_sq_le_mul
    {a s ν : ℝ} (hs : 0 ≤ s) (hν : 0 ≤ ν)
    (hsq : a ^ (2 : ℕ) ≤ ν * s ^ (2 : ℕ)) :
    2 * a - s ^ (2 : ℕ) ≤ ν := by
  have hsqrt_sq : (Real.sqrt ν * s) ^ (2 : ℕ) = ν * s ^ (2 : ℕ) := by
    -- Rewrite the comparison surface as the square of `√ν * s`.
    calc
      (Real.sqrt ν * s) ^ (2 : ℕ) = (Real.sqrt ν) ^ (2 : ℕ) * s ^ (2 : ℕ) := by ring
      _ = ν * s ^ (2 : ℕ) := by rw [Real.sq_sqrt hν]
  have habs_sq : |a| ^ (2 : ℕ) ≤ (Real.sqrt ν * s) ^ (2 : ℕ) := by
    -- This is the same squared inequality, written with a manifestly nonnegative right-hand side.
    simpa [sq_abs, hsqrt_sq] using hsq
  have habs_le : |a| ≤ Real.sqrt ν * s := by
    exact le_of_sq_le_sq habs_sq (mul_nonneg (Real.sqrt_nonneg ν) hs)
  have ha_le : a ≤ Real.sqrt ν * s := le_trans (le_abs_self a) habs_le
  have htwo : 2 * (Real.sqrt ν * s) ≤ ν + s ^ (2 : ℕ) := by
    -- The standard `2ab ≤ a² + b²` estimate closes the scalar barrier line.
    simpa [pow_two, Real.sq_sqrt hν, mul_comm, mul_left_comm, mul_assoc] using
      (two_mul_le_add_sq (Real.sqrt ν) s)
  -- Combine the bound on `a` with the quadratic estimate for `√ν` and `s`.
  nlinarith

-- Proof sketch: for the forward implication, apply the bound to the scaled direction `t • u`,
-- obtaining a quadratic inequality in `t`; nonpositivity of its discriminant yields
-- `⟪∇ F(x), u⟫² ≤ ν ‖u‖[F; x]^2`. Conversely, from the squared bound, use
-- `2ab ≤ a² + b²` after normalizing by `ν`, or complete the square in
-- `2 * ⟪∇ F(x), u⟫ - ⟪∇² F(x)u, u⟫`, to recover the original inequality. The pointwise
-- positivity hypothesis is essential: without it, `‖u‖[F; x]` can vanish on directions where the
-- Hessian quadratic form is negative, so the squared local-norm bound no longer detects the
-- barrier inequality.
/-- Proposition 5.3.3, pointwise owner form: at a fixed point `x` with positive Hessian,
the barrier inequality `2 ⟪∇ F(x), u⟫ - ⟪∇² F(x)u, u⟫ ≤ ν` for every direction `u` is
equivalent to the quadratic-form bound `⟪∇ F(x), u⟫² ≤ ν ‖u‖[F; x]^2` for every `u`,
written on the canonical Chapter 5 local-norm surface. -/
theorem barrier_parameter_bound_iff_gradient_inner_sq_le
    {F : E → ℝ} {ν : NNReal} {x : E} (hPos : (hessian F x).IsPositive) :
    (∀ u : E,
      2 * inner ℝ (∇ F x) u - inner ℝ u (hessian F x u) ≤ (ν : ℝ)) ↔
      ∀ u : E,
        (inner ℝ (∇ F x) u) ^ (2 : ℕ) ≤
          (ν : ℝ) * ‖u‖[F; x] ^ (2 : ℕ) := by
  constructor
  · intro hbound u
    have hquad : 0 ≤ inner ℝ u (hessian F x u) := hPos.inner_nonneg_right u
    have hline :
        ∀ t : ℝ,
          2 * t * inner ℝ (∇ F x) u - t ^ (2 : ℕ) * inner ℝ u (hessian F x u) ≤ (ν : ℝ) := by
      intro t
      -- Evaluate the barrier inequality on the line spanned by `u`.
      have ht := hbound (t • u)
      rw [barrier_expression_smul] at ht
      exact ht
    have hsq_raw :
        (inner ℝ (∇ F x) u) ^ (2 : ℕ) ≤
          (ν : ℝ) * inner ℝ u (hessian F x u) :=
      sq_le_mul_of_barrier_line_family hquad hline
    -- Replace the raw Hessian quadratic form with the Chapter 5 local norm square.
    simpa [sq_hessianLocalNorm_eq_inner_hessian hquad, mul_comm, mul_left_comm, mul_assoc] using
      hsq_raw
  · intro hsq u
    let a : ℝ := inner ℝ (∇ F x) u
    let s : ℝ := ‖u‖[F; x]
    have hs : 0 ≤ s := hessianLocalNorm_nonneg F x u
    have hν : 0 ≤ (ν : ℝ) := by
      exact_mod_cast ν.2
    have hquad : 0 ≤ inner ℝ u (hessian F x u) := hPos.inner_nonneg_right u
    have hline : 2 * a - s ^ (2 : ℕ) ≤ (ν : ℝ) := by
      -- Apply the scalar reverse implication to the local norm `s = ‖u‖[F; x]`.
      refine barrier_line_of_sq_le_mul hs hν ?_
      simpa [a, s] using hsq u
    -- Rewrite the local norm square back to the raw Hessian quadratic form.
    simpa [a, s, sq_hessianLocalNorm_eq_inner_hessian hquad] using hline

end
