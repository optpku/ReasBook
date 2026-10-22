/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

import ComputationalMethodsInverseProblems_Vogel_2002.Chap03.Algorithm_3_4_extra_3
import ComputationalMethodsInverseProblems_Vogel_2002.Chap03.Remark_3_4.Wolfe
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Order.Filter.Extr

section

noncomputable section

namespace LineSearch

/-- The quadratic interpolant matching `φ 0`, `φ τ₀`, and slope `d₀` at `0`. -/
def quadraticInterpolant (φ : ℝ → ℝ) (τ₀ d₀ : ℝ) : ℝ → ℝ :=
  fun τ ↦ φ 0 + d₀ * τ + ((φ τ₀ - φ 0 - d₀ * τ₀) / τ₀ ^ 2) * τ ^ 2

/-- Evaluating `quadraticInterpolant` at `0` recovers `φ 0`. -/
theorem quadraticInterpolant_apply_zero (φ : ℝ → ℝ) (τ₀ d₀ : ℝ) :
    quadraticInterpolant φ τ₀ d₀ 0 = φ 0 := by
  -- Expand the interpolant and evaluate each polynomial term at `0`.
  simp [quadraticInterpolant]

/-- The derivative of `quadraticInterpolant φ τ₀ d₀` at `τ` is the affine
function obtained by differentiating its quadratic term. -/
theorem quadraticInterpolant_hasDerivAt (φ : ℝ → ℝ) (τ₀ d₀ τ : ℝ) :
    HasDerivAt (quadraticInterpolant φ τ₀ d₀)
      (d₀ + 2 * ((φ τ₀ - φ 0 - d₀ * τ₀) / τ₀ ^ 2) * τ) τ := by
  let a := (φ τ₀ - φ 0 - d₀ * τ₀) / τ₀ ^ 2
  have hq :
      quadraticInterpolant φ τ₀ d₀ = fun t ↦ φ 0 + d₀ * t + a * t ^ 2 := by
    -- Normalize the interpolant to a sum of elementary differentiable terms.
    funext t
    simp [quadraticInterpolant, a]
  have hsum :
      (fun t ↦ φ 0 + d₀ * t + a * t ^ 2) =
        (fun x ↦ φ 0) + ((fun y ↦ d₀ * id y) + fun y ↦ a * y ^ 2) := by
    -- Match the interpolant with the sum structure produced by derivative rules.
    funext t
    simp
    ring
  have hder :
      d₀ + 2 * ((φ τ₀ - φ 0 - d₀ * τ₀) / τ₀ ^ 2) * τ =
        0 + (d₀ * 1 + a * ((2 : ℝ) * τ ^ (2 - 1))) := by
    -- The derivative of the quadratic term reduces to the expected affine slope.
    simp only [a, Nat.reduceSubDiff, pow_one, zero_add, mul_one]
    ring
  rw [hq]
  rw [hsum]
  rw [hder]
  exact (hasDerivAt_const τ (φ 0)).add
    (((hasDerivAt_id τ).const_mul d₀).add ((hasDerivAt_pow 2 τ).const_mul a))

/-- The derivative of `quadraticInterpolant` is its expected affine slope
function. -/
theorem quadraticInterpolant_deriv (φ : ℝ → ℝ) (τ₀ d₀ τ : ℝ) :
    deriv (quadraticInterpolant φ τ₀ d₀) τ =
      d₀ + 2 * ((φ τ₀ - φ 0 - d₀ * τ₀) / τ₀ ^ 2) * τ :=
  (quadraticInterpolant_hasDerivAt φ τ₀ d₀ τ).deriv

/-- The quadratic interpolant has derivative `d₀` at `0`. -/
theorem quadraticInterpolant_hasDerivAt_zero (φ : ℝ → ℝ) (τ₀ d₀ : ℝ) :
    HasDerivAt (quadraticInterpolant φ τ₀ d₀) d₀ 0 := by
  simpa using quadraticInterpolant_hasDerivAt φ τ₀ d₀ 0

/-- Evaluating `quadraticInterpolant` at `τ₀` recovers `φ τ₀`. -/
theorem quadraticInterpolant_apply_tau0 (φ : ℝ → ℝ) (τ₀ d₀ : ℝ) :
    quadraticInterpolant φ τ₀ d₀ τ₀ = φ τ₀ := by
  by_cases hτ₀ : τ₀ = 0
  · -- The degenerate branch collapses to the value at `0`.
    subst hτ₀
    simp [quadraticInterpolant]
  · -- For `τ₀ ≠ 0`, clear the denominator and simplify the polynomial identity.
    unfold quadraticInterpolant
    field_simp [hτ₀]
    ring

/-- First part of Exercise 3.10: if `τ₁` is a stationary point of the quadratic
interpolant, then `τ₁` satisfies formula `(3.30)`. -/
theorem quadraticInterpolant_stationaryPoint_formula {φ : ℝ → ℝ} {τ₀ d₀ τ₁ : ℝ}
    (hτ₀ : τ₀ ≠ 0) (hden : φ τ₀ - φ 0 - d₀ * τ₀ ≠ 0)
    (hstat : deriv (quadraticInterpolant φ τ₀ d₀) τ₁ = 0) :
    τ₁ = -d₀ * τ₀ ^ 2 / (2 * (φ τ₀ - φ 0 - d₀ * τ₀)) := by
  -- Rewrite stationarity as a linear equation in `τ₁`.
  rw [quadraticInterpolant_deriv] at hstat
  have htwo : (2 : ℝ) ≠ 0 := by
    norm_num
  have htwoDen : 2 * (φ τ₀ - φ 0 - d₀ * τ₀) ≠ 0 := mul_ne_zero htwo hden
  -- Clear denominators and solve the resulting scalar equation.
  field_simp [hτ₀, hden, htwoDen] at hstat ⊢
  nlinarith

/-- Helper for Exercise 3.10: failure of sufficient decrease yields a strict
half-slope gap for the quadratic-interpolation denominator. -/
lemma halfSlopeGap_of_not_sufficientDecrease {φ : ℝ → ℝ} {τ₀ d₀ c₁ : ℝ}
    (h0 : HasDerivAt φ d₀ 0) (hτ₀ : 0 < τ₀) (hd₀ : d₀ < 0) (hc₁₀ : 0 < c₁)
    (hc₁ : c₁ < (1 / 2 : ℝ)) (hfail : ¬ SufficientDecrease φ τ₀ c₁) :
    (-d₀ * τ₀) / 2 < φ τ₀ - φ 0 - d₀ * τ₀ :=
  set_option allowUnsafeReducibility true in
  by
    have hc₁_lt_one : c₁ < 1 := by
      linarith
    have hbds_eq : SufficientDecreaseBounds τ₀ c₁ = (0 < τ₀ ∧ 0 < c₁ ∧ c₁ < 1) := rfl
    have hbds : SufficientDecreaseBounds τ₀ c₁ :=
      -- Transport the visible conjunction into the hidden side-condition predicate.
      hbds_eq.symm ▸ (show 0 < τ₀ ∧ 0 < c₁ ∧ c₁ < 1 from ⟨hτ₀, hc₁₀, hc₁_lt_one⟩)
    have hnot_le : ¬ φ τ₀ ≤ φ 0 + c₁ * τ₀ * deriv φ 0 := by
      intro hle
      apply hfail
      rw [sufficientDecrease_iff]
      exact ⟨hbds, hle⟩
    have harmijo : φ 0 + c₁ * τ₀ * deriv φ 0 < φ τ₀ := by
      -- Negating the Armijo inequality turns failure into a strict inequality.
      linarith
    have hphi : φ 0 + c₁ * τ₀ * d₀ < φ τ₀ := by
      -- Replace `deriv φ 0` with the supplied slope `d₀`.
      simpa [h0.deriv] using harmijo
    have hmul_neg : τ₀ * d₀ < 0 := mul_neg_of_pos_of_neg hτ₀ hd₀
    have hhalf : c₁ * τ₀ * d₀ > (1 / 2 : ℝ) * τ₀ * d₀ := by
      -- Multiplying `c₁ < 1/2` by the negative quantity `τ₀ * d₀` reverses the order.
      nlinarith
    linarith

/-- Helper for Exercise 3.10: at any stationary point `τ₁`, the quadratic
interpolant differs from its stationary value by a positive quadratic square. -/
lemma quadraticInterpolant_sub_stationary_eq {φ : ℝ → ℝ} {τ₀ d₀ τ₁ : ℝ}
    (hstat : deriv (quadraticInterpolant φ τ₀ d₀) τ₁ = 0) (τ : ℝ) :
    quadraticInterpolant φ τ₀ d₀ τ - quadraticInterpolant φ τ₀ d₀ τ₁ =
      ((φ τ₀ - φ 0 - d₀ * τ₀) / τ₀ ^ 2) * (τ - τ₁) ^ 2 := by
  let a := (φ τ₀ - φ 0 - d₀ * τ₀) / τ₀ ^ 2
  have hq :
      quadraticInterpolant φ τ₀ d₀ = fun t ↦ φ 0 + d₀ * t + a * t ^ 2 := by
    -- Keep the interpolant in a stable polynomial normal form.
    funext t
    simp [quadraticInterpolant, a]
  have hstat' : d₀ + 2 * a * τ₁ = 0 := by
    -- Translate stationarity into the vanishing of the affine derivative.
    rw [quadraticInterpolant_deriv] at hstat
    simpa [a, mul_assoc, mul_left_comm, mul_comm] using hstat
  have hd : d₀ = -2 * a * τ₁ := by
    nlinarith [hstat']
  have ha : (φ τ₀ - φ 0 - d₀ * τ₀) / τ₀ ^ 2 = a := by
    rfl
  rw [hq, ha, hd]
  -- Completing the square isolates the stationary value.
  ring

/-- Under explicit derivative data at `0`, a stationary point of
`quadraticInterpolant φ τ₀ d₀` is exactly the quadratic backtracking step. -/
theorem quadraticInterpolant_stationaryPoint_eq_quadraticBacktrackingStep
    {φ : ℝ → ℝ} {τ₀ d₀ τ₁ : ℝ} (h0 : HasDerivAt φ d₀ 0) (hτ₀ : τ₀ ≠ 0)
    (hden : φ τ₀ - φ 0 - d₀ * τ₀ ≠ 0)
    (hstat : deriv (quadraticInterpolant φ τ₀ d₀) τ₁ = 0) :
    τ₁ = quadraticBacktrackingStep φ τ₀ := by
  rw [quadraticBacktrackingStep_eq_of_hasDerivAt h0]
  exact quadraticInterpolant_stationaryPoint_formula hτ₀ hden hstat

/-- Exercise 3.10. If `τ₀ > 0`, `d₀ < 0`, `c₁ < 1 / 2`, and sufficient decrease
fails at `τ₀`, then the quadratic-backtracking stationary point of the quadratic
interpolant minimizes it on `Set.univ` and lies in `Set.Ioo 0 τ₀`. -/
theorem quadraticInterpolant_minimizer_mem_Ioo {φ : ℝ → ℝ} {τ₀ d₀ c₁ : ℝ}
    (h0 : HasDerivAt φ d₀ 0) (hτ₀ : 0 < τ₀) (hd₀ : d₀ < 0) (hc₁₀ : 0 < c₁)
    (hc₁ : c₁ < (1 / 2 : ℝ)) (hfail : ¬ SufficientDecrease φ τ₀ c₁) :
    IsMinOn (quadraticInterpolant φ τ₀ d₀) Set.univ (quadraticBacktrackingStep φ τ₀) ∧
      quadraticBacktrackingStep φ τ₀ ∈ Set.Ioo 0 τ₀ := by
  -- Route correction: prove global minimality from an exact square identity,
  -- then deduce `0 < τ₁ < τ₀` from the explicit backtracking formula and the gap estimate.
  have hgap :=
    halfSlopeGap_of_not_sufficientDecrease h0 hτ₀ hd₀ hc₁₀ hc₁ hfail
  have hhalfPos : 0 < (-d₀ * τ₀) / 2 := by
    nlinarith [hd₀, hτ₀]
  have hdenPos : 0 < φ τ₀ - φ 0 - d₀ * τ₀ := by
    -- The gap estimate already forces the interpolation denominator to be positive.
    linarith
  have hτ₀ne : τ₀ ≠ 0 := ne_of_gt hτ₀
  have hden : φ τ₀ - φ 0 - d₀ * τ₀ ≠ 0 := ne_of_gt hdenPos
  have hstepDeriv :
      deriv (quadraticInterpolant φ τ₀ d₀) (quadraticBacktrackingStep φ τ₀) = 0 := by
    -- Substitute the explicit quadratic-backtracking formula into the derivative.
    rw [quadraticInterpolant_deriv]
    rw [quadraticBacktrackingStep_eq_of_hasDerivAt (φ := φ) (τ₀ := τ₀) h0]
    have htwoDen : 2 * (φ τ₀ - φ 0 - d₀ * τ₀) ≠ 0 := by
      nlinarith
    field_simp [hτ₀ne, hden, htwoDen]
    ring
  have hcoeffPos : 0 < (φ τ₀ - φ 0 - d₀ * τ₀) / τ₀ ^ 2 := by
    exact div_pos hdenPos (pow_pos hτ₀ 2)
  have hstepPos : 0 < quadraticBacktrackingStep φ τ₀ := by
    -- Both the numerator and denominator of `(3.30)` are positive.
    rw [quadraticBacktrackingStep_eq_of_hasDerivAt (φ := φ) (τ₀ := τ₀) h0]
    have hnumPos : 0 < -d₀ * τ₀ ^ 2 := by
      have hpow : 0 < τ₀ ^ 2 := by
        positivity
      nlinarith
    have hden2Pos : 0 < 2 * (φ τ₀ - φ 0 - d₀ * τ₀) := by
      nlinarith
    exact div_pos hnumPos hden2Pos
  have hstepLt : quadraticBacktrackingStep φ τ₀ < τ₀ := by
    -- Compare the explicit step to `τ₀` using the same half-slope gap.
    rw [quadraticBacktrackingStep_eq_of_hasDerivAt (φ := φ) (τ₀ := τ₀) h0]
    have hden2Pos : 0 < 2 * (φ τ₀ - φ 0 - d₀ * τ₀) := by
      nlinarith
    rw [_root_.div_lt_iff₀ hden2Pos]
    nlinarith [hgap, hτ₀]
  constructor
  · rw [isMinOn_univ_iff]
    intro τ
    have hsq := quadraticInterpolant_sub_stationary_eq hstepDeriv τ
    have hnonneg :
        0 ≤
          ((φ τ₀ - φ 0 - d₀ * τ₀) / τ₀ ^ 2) *
            (τ - quadraticBacktrackingStep φ τ₀) ^ 2 := by
      -- The square term is nonnegative and its coefficient is positive.
      exact mul_nonneg (le_of_lt hcoeffPos) (sq_nonneg _)
    linarith
  · exact ⟨hstepPos, hstepLt⟩

/-- Under the hypotheses of Exercise 3.10 (2), the quadratic backtracking step
minimizes the quadratic interpolant on `Set.univ`. -/
theorem quadraticInterpolant_isMinOn_quadraticBacktrackingStep {φ : ℝ → ℝ}
    {τ₀ d₀ c₁ : ℝ} (h0 : HasDerivAt φ d₀ 0) (hτ₀ : 0 < τ₀) (hd₀ : d₀ < 0)
    (hc₁₀ : 0 < c₁) (hc₁ : c₁ < (1 / 2 : ℝ))
    (hfail : ¬ SufficientDecrease φ τ₀ c₁) :
    IsMinOn (quadraticInterpolant φ τ₀ d₀) Set.univ (quadraticBacktrackingStep φ τ₀) :=
  (quadraticInterpolant_minimizer_mem_Ioo h0 hτ₀ hd₀ hc₁₀ hc₁ hfail).1

/-- Under the hypotheses of Exercise 3.10 (2), the quadratic backtracking step
lies in the open interval `Set.Ioo 0 τ₀`. -/
theorem quadraticBacktrackingStep_mem_Ioo_of_not_sufficientDecrease
    {φ : ℝ → ℝ} {τ₀ d₀ c₁ : ℝ} (h0 : HasDerivAt φ d₀ 0) (hτ₀ : 0 < τ₀)
    (hd₀ : d₀ < 0) (hc₁₀ : 0 < c₁) (hc₁ : c₁ < (1 / 2 : ℝ))
    (hfail : ¬ SufficientDecrease φ τ₀ c₁) :
    quadraticBacktrackingStep φ τ₀ ∈ Set.Ioo 0 τ₀ :=
  (quadraticInterpolant_minimizer_mem_Ioo h0 hτ₀ hd₀ hc₁₀ hc₁ hfail).2

end LineSearch
end
end
