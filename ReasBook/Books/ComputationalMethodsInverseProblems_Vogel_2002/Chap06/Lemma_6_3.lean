/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import ComputationalMethodsInverseProblems_Vogel_2002.Chap06.Lemma_6_3.Approximation
public import Mathlib.Analysis.Real.Sqrt

public section

open Filter
open OutputLeastSquares
open scoped Topology

universe u v

variable {Q : Type u} {Y : Type v} [NormedAddCommGroup Y]
variable (F : Q → Y) (Fn : ℕ → Q → Y) (T : ℕ → Q → ℝ)
variable (C : ℕ → Set Q) (q : ℕ → Q) (d : ℕ → Y) (J : Q → ℝ) (α δ : ℕ → ℝ) (qTrue : Q)

/-- Helper for Lemma 6.3: the minimizing property bounds the displayed squared residual
by the true-data error term plus the regularization penalty at `qTrue`. -/
lemma residualSq_le_deltaSq_add_alphaMulTruePenalty
    (h : MinimizingSequence F Fn T C q d J α δ qTrue) (hJ_nonneg_q : ∀ n, 0 ≤ J (q n))
    (n : ℕ) :
    ‖F (q n) - d n‖ ^ 2 ≤ δ n ^ 2 + α n * J qTrue := by
  -- Rewrite the minimizing property into the residual-square inequality from the source proof.
  have h_min := h.objective_le_true n
  simp only [h.objective_eq, h.q_residual_eq, h.qTrue_residual_eq] at h_min
  rw [← h.delta_eq n] at h_min
  -- Drop the nonnegative penalty term at `q n` from the left-hand side.
  have h_penalty_nonneg : 0 ≤ α n * J (q n) :=
    mul_nonneg (le_of_lt (h.alpha_pos n)) (hJ_nonneg_q n)
  exact le_trans (le_add_of_nonneg_right h_penalty_nonneg) h_min

/-- Helper for Lemma 6.3: the Chapter 6 regularization regime forces `δ n ^ 2` to vanish. -/
lemma deltaSqTendstoZero
    (h : MinimizingSequence F Fn T C q d J α δ qTrue) :
    Tendsto (fun n ↦ δ n ^ 2) atTop (𝓝 0) := by
  -- Multiply the two asymptotic assumptions to recover the unsplit error term.
  have h_product :
      Tendsto (fun n ↦ (δ n ^ 2 / α n) * α n) atTop (𝓝 (0 * 0)) :=
    h.regularization.tendstoErrorSqDivAlpha.mul h.regularization.tendstoAlpha
  -- Positivity of `α n` turns the product back into `δ n ^ 2`.
  have h_rewrite : (fun n ↦ (δ n ^ 2 / α n) * α n) = fun n ↦ δ n ^ 2 := by
    funext n
    exact div_mul_cancel₀ _ (h.alpha_pos n).ne'
  simpa [h_rewrite] using h_product

/-- Helper for Lemma 6.3: dividing the minimizing-sequence estimate by `α n` gives the
explicit penalty bound used in `(6.36)`. -/
lemma penalty_le_deltaSqDivAlpha_add_truePenalty
    (h : MinimizingSequence F Fn T C q d J α δ qTrue) (n : ℕ) :
    J (q n) ≤ δ n ^ 2 / α n + J qTrue := by
  -- Rewrite the minimizing property into the source inequality on residual and penalty terms.
  have h_min := h.objective_le_true n
  simp only [h.objective_eq, h.q_residual_eq, h.qTrue_residual_eq] at h_min
  rw [← h.delta_eq n] at h_min
  -- Drop the nonnegative residual square before dividing by the positive parameter `α n`.
  have h_residual_nonneg : 0 ≤ ‖F (q n) - d n‖ ^ 2 := sq_nonneg _
  have h_alpha_mul :
      α n * J (q n) ≤ δ n ^ 2 + α n * J qTrue := by
    exact le_trans (le_add_of_nonneg_left h_residual_nonneg) h_min
  have h_div :
      J (q n) ≤ (δ n ^ 2 + α n * J qTrue) / α n := by
    exact (le_div_iff₀ (h.alpha_pos n)).2 (by simpa [mul_comm] using h_alpha_mul)
  calc
    J (q n) ≤ (δ n ^ 2 + α n * J qTrue) / α n := h_div
    _ = δ n ^ 2 / α n + J qTrue := by
      rw [add_div, mul_div_cancel_left₀]
      exact (h.alpha_pos n).ne'

/-- Lemma 6.3 (1). Under the Chapter 6 regularization-parameter regime, if each `q n`
minimizes `T n`, the shared Chapter 6 setup is recorded by
`OutputLeastSquares.MinimizingSequence F Fn T C q d J α δ qTrue`, the penalty is
nonnegative along `q`, then the displayed residual in `(6.35)` tends to `0`. The
residual compatibility between `F` and `Fn` at `q n` is part of the shared
`MinimizingSequence` data. -/
theorem residualTendstoZero
    (h : MinimizingSequence F Fn T C q d J α δ qTrue) (hJ_nonneg_q : ∀ n, 0 ≤ J (q n)) :
    Tendsto (fun n ↦ ‖F (q n) - d n‖) atTop (𝓝 0) := by
  -- Squeeze the squared residual by the direct estimate coming from the minimizing property.
  have h_truePenalty :
      Tendsto (fun n ↦ α n * J qTrue) atTop (𝓝 0) := by
    simpa using h.regularization.tendstoAlpha.mul_const (J qTrue)
  have h_upper :
      Tendsto (fun n ↦ δ n ^ 2 + α n * J qTrue) atTop (𝓝 0) := by
    simpa using (deltaSqTendstoZero (F := F) (Fn := Fn) (T := T) (C := C) (q := q)
      (d := d) (J := J) (α := α) (δ := δ) (qTrue := qTrue) h).add h_truePenalty
  have h_sq :
      Tendsto (fun n ↦ ‖F (q n) - d n‖ ^ 2) atTop (𝓝 0) := by
    -- The upper bound tends to `0`, so the squared residual does as well.
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h_upper ?_ ?_
    · exact fun n ↦ sq_nonneg _
    · exact fun n ↦
        residualSq_le_deltaSq_add_alphaMulTruePenalty (F := F) (Fn := Fn) (T := T) (C := C)
          (q := q) (d := d) (J := J) (α := α) (δ := δ) (qTrue := qTrue) h hJ_nonneg_q n
  -- Apply `sqrt` to pass from the squared residual to the residual itself.
  simpa [Real.sqrt_sq (norm_nonneg _)] using h_sq.sqrt

/-- Lemma 6.3 (2). Under the same Chapter 6 setup recorded by
`OutputLeastSquares.MinimizingSequence F Fn T C q d J α δ qTrue`, the penalty values
`J (q n)` satisfy the explicit estimate in `(6.36)`. -/
theorem penaltyBounded
    (h : MinimizingSequence F Fn T C q d J α δ qTrue) (n : ℕ) :
    J (q n) ≤ δ n ^ 2 / α n + J qTrue := by
  -- Reuse the divided minimizing-sequence estimate proved above.
  exact penalty_le_deltaSqDivAlpha_add_truePenalty (F := F) (Fn := Fn) (T := T) (C := C)
    (q := q) (d := d) (J := J) (α := α) (δ := δ) (qTrue := qTrue) h n
