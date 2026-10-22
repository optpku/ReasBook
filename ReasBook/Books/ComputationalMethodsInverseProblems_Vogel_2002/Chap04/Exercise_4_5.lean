/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import ComputationalMethodsInverseProblems_Vogel_2002.Chap04.Example_4_17

public section

universe u

namespace PoissonLikelihood

/-- If every observed count is strictly positive, then the observed count vector lies in the
positive orthant. -/
theorem observedCountVector_mem_positiveOrthant
    {ι : Type u} (d : ι → ℕ) (hposd : ∀ i, 0 < d i) :
    (fun i ↦ (d i : ℝ)) ∈ positiveOrthant ι := by
  refine (mem_positiveOrthant_iff _).2 ?_
  intro i
  exact_mod_cast hposd i

variable {ι : Type u}

/-- Helper for Exercise 4.5: the scalar Poisson negative log-likelihood term is minimized at the
observed count when both arguments are positive. -/
lemma poissonCoordinateTerm_le_of_pos {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    a - a * Real.log a ≤ b - a * Real.log b := by
  -- Rewrite the desired comparison into the standard inequality `log x ≤ x - 1`.
  have hlog : Real.log (b / a) ≤ b / a - 1 :=
    Real.log_le_sub_one_of_pos (div_pos hb ha)
  have hscaled : a * Real.log (b / a) ≤ a * (b / a - 1) :=
    mul_le_mul_of_nonneg_left hlog (le_of_lt ha)
  have hratio : a * (b / a - 1) = b - a := by
    field_simp [ha.ne']
  have hlogDiv : a * (Real.log b - Real.log a) ≤ b - a := by
    simpa [Real.log_div hb.ne' ha.ne', hratio] using hscaled
  -- Rearranging the scaled log inequality gives the target coordinate bound.
  linarith

/-- Helper for Exercise 4.5: every coordinate of the observed count vector is no larger than the
corresponding coordinate contribution of any point in `positiveOrthant ι`. -/
lemma observedCountCoordinateBound
    (d : ι → ℕ) (hposd : ∀ i, 0 < d i) {lambda : ι → ℝ}
    (hlambda : lambda ∈ positiveOrthant ι) (i : ι) :
    (d i : ℝ) - (d i : ℝ) * Real.log (d i : ℝ) ≤
      lambda i - (d i : ℝ) * Real.log (lambda i) := by
  -- Extract positivity from the orthant constraint and the observed counts.
  have hdi : 0 < (d i : ℝ) := by
    exact_mod_cast hposd i
  have hlambdai : 0 < lambda i :=
    (mem_positiveOrthant_iff lambda).1 hlambda i
  -- Apply the one-dimensional inequality at the current coordinate.
  exact poissonCoordinateTerm_le_of_pos hdi hlambdai

section

variable [Fintype ι]

/-- Helper for Exercise 4.5: the observed count vector globally minimizes the Poisson objective on
`positiveOrthant ι` at the level of function values. -/
lemma observedCountVector_le_on_positiveOrthant
    (d : ι → ℕ) (hposd : ∀ i, 0 < d i) {lambda : ι → ℝ}
    (hlambda : lambda ∈ positiveOrthant ι) :
    poissonNegLogLikelihood d (fun i ↦ (d i : ℝ)) ≤ poissonNegLogLikelihood d lambda := by
  -- Expand the objective into its finite sum and compare the summands coordinatewise.
  rw [poissonNegLogLikelihood_def, poissonNegLogLikelihood_def]
  refine Finset.sum_le_sum ?_
  intro i _
  exact observedCountCoordinateBound d hposd hlambda i

/- Exercise 4.5 (1): if every observed count is strictly positive, then the negative Poisson log
likelihood is strictly convex on the interior of the nonnegative orthant, formalized as
`positiveOrthant ι`. -/
#check poissonNegLogLikelihood_strictConvexOn

/-- Exercise 4.5: the observed count vector is a minimizer of the Poisson negative
log-likelihood on `positiveOrthant ι` when every observed count is strictly positive. -/
theorem isMinOn_observedCountVector
    (d : ι → ℕ) (hposd : ∀ i, 0 < d i) :
    IsMinOn (poissonNegLogLikelihood d) (positiveOrthant ι) (fun i ↦ (d i : ℝ)) := by
  -- Reduce minimization to the pointwise objective comparison on the feasible set.
  rw [isMinOn_iff]
  intro lambda hlambda
  exact observedCountVector_le_on_positiveOrthant d hposd hlambda

/-- Consequence for Exercise 4.5: on `positiveOrthant ι`, any minimizer of the negative
Poisson log likelihood equals the observed count vector. -/
theorem eq_observedCountVector_of_isMinOn
    (d : ι → ℕ) (hposd : ∀ i, 0 < d i) {lambda : ι → ℝ}
    (hlambda : lambda ∈ positiveOrthant ι)
    (hmin : IsMinOn (poissonNegLogLikelihood d) (positiveOrthant ι) lambda) :
    lambda = fun i ↦ (d i : ℝ) := by
  exact
    (poissonNegLogLikelihood_strictConvexOn d hposd).eq_of_isMinOn
      hmin (isMinOn_observedCountVector d hposd) hlambda
      (observedCountVector_mem_positiveOrthant d hposd)

end

end PoissonLikelihood
