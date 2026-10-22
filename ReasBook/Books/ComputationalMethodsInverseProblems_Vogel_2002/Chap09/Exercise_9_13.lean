/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import ComputationalMethodsInverseProblems_Vogel_2002.Chap09.Exercise_9_13.AdmissibleSet
public import ComputationalMethodsInverseProblems_Vogel_2002.Chap09.Exercise_9_13.NegLogLikelihood
public import Mathlib.Order.Filter.Extr

public section

noncomputable section

namespace PoissonInverse

open scoped BigOperators

/-- Helper for Exercise 9.13: for positive data `a` and positive prediction `b`,
the scalar Poisson negative log-likelihood term is minimized at `b = a`. -/
lemma poissonCoordinateTerm_le_of_pos {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    a - a * Real.log a ≤ b - a * Real.log b := by
  -- Apply the standard logarithm bound to the positive ratio `b / a`.
  have hlog : Real.log (b / a) ≤ b / a - 1 :=
    Real.log_le_sub_one_of_pos (div_pos hb ha)
  have hscaled : a * Real.log (b / a) ≤ a * (b / a - 1) :=
    mul_le_mul_of_nonneg_left hlog ha.le
  have hratio : a * (b / a - 1) = b - a := by
    field_simp [ha.ne']
  have hlogDiv : a * (Real.log b - Real.log a) ≤ b - a := by
    simpa [Real.log_div hb.ne' ha.ne', hratio, mul_sub] using hscaled
  -- Rearranging the scaled inequality gives the desired scalar comparison.
  linarith

/-- Helper for Exercise 9.13: once the positivity side conditions are available,
exact data fit gives the coordinatewise finite-sum comparison for the Chapter 9
objective. -/
lemma coordinateSum_le_of_mulVec_eq
    {m n : ℕ}
    {K : Matrix (Fin m) (Fin n) ℝ}
    {d : EuclideanSpace ℝ (Fin m)}
    {f g : EuclideanSpace ℝ (Fin n)}
    (hdPos : ∀ i : Fin m, 0 < d i)
    (hg_forwardPos : ∀ i : Fin m, 0 < Matrix.mulVec K g i)
    (hfit : Matrix.mulVec K f = d) :
    (∑ i : Fin m,
        (Matrix.mulVec K f i - d i * Real.log (Matrix.mulVec K f i))) ≤
      ∑ i : Fin m,
        (Matrix.mulVec K g i - d i * Real.log (Matrix.mulVec K g i)) := by
  -- Compare the finite sum termwise after rewriting the fitted point to the data.
  refine Finset.sum_le_sum ?_
  intro i hi
  have hfit_i : Matrix.mulVec K f i = d i := by
    simpa using congrArg (fun x ↦ x i) hfit
  simpa [hfit_i] using
    (poissonCoordinateTerm_le_of_pos (a := d i) (b := Matrix.mulVec K g i)
      (hdPos i) (hg_forwardPos i))

/-- Exercise 9.13. If `K f = d`, then any admissible point `f` minimizes the
Chapter 9 objective `J(f) = -ℓ(f; d)` from `(9.44)` on the nonnegative
feasible set with positive forward data, formalized by
`PoissonInverse.admissibleSet K`. -/
theorem isMinOn_of_mulVec_eq_observation
    {m n : ℕ}
    (K : Matrix (Fin m) (Fin n) ℝ)
    (d : EuclideanSpace ℝ (Fin m))
    (f : EuclideanSpace ℝ (Fin n))
    (hf_admissible : f ∈ admissibleSet K)
    (hfit : Matrix.mulVec K f = d) :
    IsMinOn
      (negLogLikelihood K d)
      (admissibleSet K)
      f := by
  -- Route correction: the main theorem now uses the cleaned owner lemmas for
  -- admissibility and the objective formula instead of unfolding imported defs.
  rw [isMinOn_iff]
  intro g hg_admissible
  -- Extract the positivity side conditions from admissibility at both points.
  have hf_forwardPos : ∀ i : Fin m, 0 < Matrix.mulVec K f i :=
    forwardPos_of_mem_admissibleSet hf_admissible
  have hg_forwardPos : ∀ i : Fin m, 0 < Matrix.mulVec K g i :=
    forwardPos_of_mem_admissibleSet hg_admissible
  have hdPos : ∀ i : Fin m, 0 < d i := by
    intro i
    have hfit_i : Matrix.mulVec K f i = d i := by
      simpa using congrArg (fun x ↦ x i) hfit
    -- Transport positivity from the fitted forward data to the observation.
    simpa [hfit_i] using hf_forwardPos i
  -- Normalize both objective values to the coordinate sum and compare termwise.
  rw [negLogLikelihood_def, negLogLikelihood_def]
  exact coordinateSum_le_of_mulVec_eq hdPos hg_forwardPos hfit

end PoissonInverse
