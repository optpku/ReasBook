module

public import ReasLib.Optimization.LineSearch.Wolfe.StepLowerBound
public import ReasLib.Analysis.Calculus.Gradient.HessianLipschitz

public section

open scoped BigOperators

/-!
# Finite and infinite Zoutendijk bounds

This module lifts the one-step Lipschitz-gradient estimate for weak Wolfe steps to
finite partial sums and to a summable directional-cosine series.  The sequence
interface is deliberately independent of any particular optimization algorithm.
-/

noncomputable section

universe u

namespace LineSearch.Wolfe

/-- A termwise bound by successive decreases telescopes over a finite initial segment. -/
theorem sum_range_le_of_term_le_sub {a b : ℕ → ℝ} {N : ℕ}
    (h : ∀ k < N, a k ≤ b k - b (k + 1)) :
    ∑ k ∈ Finset.range N, a k ≤ b 0 - b N := by
  calc
    ∑ k ∈ Finset.range N, a k ≤
        ∑ k ∈ Finset.range N, (b k - b (k + 1)) := by
      exact Finset.sum_le_sum (fun k hk => h k (Finset.mem_range.mp hk))
    _ = b 0 - b N := by
      exact Finset.sum_range_sub' b N

/-- Weak-Wolfe one-step decrease bounds the finite Zoutendijk sum along a sequence of steps. -/
theorem zoutendijk_partial_sum_le
    {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    {N : ℕ} {c₁ c₂ L : ℝ} {f : E → ℝ}
    {x d : ℕ → E} {α : ℕ → ℝ}
    (hα : ∀ k, 0 < α k)
    (hd : ∀ k, d k ≠ 0)
    (hdescent : ∀ k, inner ℝ (gradient f (x k)) (d k) < 0)
    (hcert : ∀ k, LineSearch.IsWeakWolfe c₁ c₂ f (x k) (α k • d k))
    (hL : 0 < L)
    (hLip : ∀ u v : E, ‖gradient f u - gradient f v‖ ≤ L * ‖u - v‖)
    (hstep : ∀ k, x (k + 1) = x k + α k • d k) :
    ∑ k ∈ Finset.range N,
        c₁ * (1 - c₂) * (inner ℝ (gradient f (x k)) (d k)) ^ 2 /
          (L * ‖d k‖ ^ 2) ≤
      f (x 0) - f (x N) := by
  refine sum_range_le_of_term_le_sub
    (a := fun k ↦ c₁ * (1 - c₂) * (inner ℝ (gradient f (x k)) (d k)) ^ 2 /
      (L * ‖d k‖ ^ 2))
    (b := fun k ↦ f (x k)) ?_
  intro k hk
  have hdecrease := weakWolfe_decrease_lower_bound (hcert k) (hα k) hL (hd k)
    (hdescent k) hLip
  rw [← hstep k] at hdecrease
  exact hdecrease

/-- A global `C²` Hessian norm bound supplies the Lipschitz-gradient hypothesis for the finite
Zoutendijk partial-sum estimate. -/
theorem zoutendijk_partial_sum_le_of_contDiff_hessian_norm_le
    {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    {N : ℕ} {c₁ c₂ L : ℝ} {f : E → ℝ}
    {x d : ℕ → E} {α : ℕ → ℝ}
    (hf : ContDiff ℝ 2 f)
    (hbound : ∀ z : E, ‖fderiv ℝ (gradient f) z‖ ≤ L)
    (hα : ∀ k, 0 < α k)
    (hd : ∀ k, d k ≠ 0)
    (hdescent : ∀ k, inner ℝ (gradient f (x k)) (d k) < 0)
    (hcert : ∀ k, LineSearch.IsWeakWolfe c₁ c₂ f (x k) (α k • d k))
    (hL : 0 < L)
    (hstep : ∀ k, x (k + 1) = x k + α k • d k) :
    ∑ k ∈ Finset.range N,
        c₁ * (1 - c₂) * (inner ℝ (gradient f (x k)) (d k)) ^ 2 /
          (L * ‖d k‖ ^ 2) ≤
      f (x 0) - f (x N) := by
  have hLip : ∀ u v : E, ‖gradient f u - gradient f v‖ ≤ L * ‖u - v‖ := by
    intro u v
    exact norm_gradient_sub_le_of_contDiff_hessian_norm_le hf hbound v u
  exact zoutendijk_partial_sum_le hα hd hdescent hcert hL hLip hstep

/-- A lower-bounded objective makes the Zoutendijk directional-cosine series summable. -/
theorem zoutendijk_summable_of_bounded_below
    {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    {c₁ c₂ L m : ℝ} {f : E → ℝ}
    {x d : ℕ → E} {α : ℕ → ℝ}
    (hα : ∀ k, 0 < α k)
    (hd : ∀ k, d k ≠ 0)
    (hdescent : ∀ k, inner ℝ (gradient f (x k)) (d k) < 0)
    (hcert : ∀ k, LineSearch.IsWeakWolfe c₁ c₂ f (x k) (α k • d k))
    (hL : 0 < L)
    (hLip : ∀ u v : E, ‖gradient f u - gradient f v‖ ≤ L * ‖u - v‖)
    (hstep : ∀ k, x (k + 1) = x k + α k • d k)
    (hbelow : ∀ k, m ≤ f (x k)) :
    Summable (fun k ↦
      c₁ * (1 - c₂) * (inner ℝ (gradient f (x k)) (d k)) ^ 2 /
        (L * ‖d k‖ ^ 2)) ∧
      (∑' k, c₁ * (1 - c₂) * (inner ℝ (gradient f (x k)) (d k)) ^ 2 /
        (L * ‖d k‖ ^ 2)) ≤ f (x 0) - m := by
  have hnonneg : ∀ k, 0 ≤
      c₁ * (1 - c₂) * (inner ℝ (gradient f (x k)) (d k)) ^ 2 /
        (L * ‖d k‖ ^ 2) := by
    intro k
    have hden : 0 < L * ‖d k‖ ^ 2 := by
      exact mul_pos hL (sq_pos_of_pos (norm_pos_iff.mpr (hd k)))
    have hc₁ : 0 ≤ c₁ := (hcert k).c₁_pos.le
    have hc₂ : 0 ≤ 1 - c₂ := sub_nonneg.mpr (hcert k).c₂_lt_one.le
    exact div_nonneg
      (mul_nonneg (mul_nonneg hc₁ hc₂) (sq_nonneg _)) hden.le
  have hpartial : ∀ N, ∑ k ∈ Finset.range N,
      c₁ * (1 - c₂) * (inner ℝ (gradient f (x k)) (d k)) ^ 2 /
        (L * ‖d k‖ ^ 2) ≤ f (x 0) - m := by
    intro N
    have hsum := zoutendijk_partial_sum_le hα hd hdescent hcert hL hLip hstep (N := N)
    have hlower := hbelow N
    linarith
  constructor
  · exact summable_of_sum_range_le hnonneg hpartial
  · exact Real.tsum_le_of_sum_range_le hnonneg hpartial

/-- A global `C²` Hessian norm bound supplies the Lipschitz-gradient hypothesis needed by the
Zoutendijk summability theorem. -/
theorem zoutendijk_summable_of_contDiff_hessian_norm_le
    {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    {c₁ c₂ L m : ℝ} {f : E → ℝ}
    {x d : ℕ → E} {α : ℕ → ℝ}
    (hf : ContDiff ℝ 2 f)
    (hbound : ∀ z : E, ‖fderiv ℝ (gradient f) z‖ ≤ L)
    (hα : ∀ k, 0 < α k)
    (hd : ∀ k, d k ≠ 0)
    (hdescent : ∀ k, inner ℝ (gradient f (x k)) (d k) < 0)
    (hcert : ∀ k, LineSearch.IsWeakWolfe c₁ c₂ f (x k) (α k • d k))
    (hL : 0 < L)
    (hstep : ∀ k, x (k + 1) = x k + α k • d k)
    (hbelow : ∀ k, m ≤ f (x k)) :
    Summable (fun k ↦
      c₁ * (1 - c₂) * (inner ℝ (gradient f (x k)) (d k)) ^ 2 /
        (L * ‖d k‖ ^ 2)) ∧
      (∑' k, c₁ * (1 - c₂) * (inner ℝ (gradient f (x k)) (d k)) ^ 2 /
        (L * ‖d k‖ ^ 2)) ≤ f (x 0) - m := by
  have hLip : ∀ u v : E, ‖gradient f u - gradient f v‖ ≤ L * ‖u - v‖ := by
    intro u v
    exact norm_gradient_sub_le_of_contDiff_hessian_norm_le hf hbound v u
  exact zoutendijk_summable_of_bounded_below hα hd hdescent hcert hL hLip hstep hbelow

end LineSearch.Wolfe
