/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Books.ProbabilityTheory_Klenke_2020.Items.Chap15.Definition_15_27

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory
open BoundedContinuousFunction
open scoped BigOperators ComplexOrder

/-- Helper for Lemma 15.28: the oscillatory difference kernel is the pointwise square of the
corresponding phase sum. -/
lemma differenceInnerProbCharKernel_eq_phaseSquare {d n : ℕ}
    (x : EuclideanSpace ℝ (Fin d))
    (t : Fin n → EuclideanSpace ℝ (Fin d)) (c : Fin n → ℂ) :
    ∑ i, ∑ j, star (c i) * innerProbChar (t i - t j) x * c j =
      star (∑ i, c i * innerProbChar (-t i) x) * (∑ j, c j * innerProbChar (-t j) x) := by
  -- Proof comment: expand the product of the two phase sums and identify each kernel entry with
  -- the product of a conjugate phase and a phase.
  symm
  calc
    star (∑ i, c i * innerProbChar (-t i) x) * (∑ j, c j * innerProbChar (-t j) x)
        = ∑ i, ∑ j, star (c i * innerProbChar (-t i) x) * (c j * innerProbChar (-t j) x) := by
            rw [star_sum, Finset.sum_mul]
            refine Finset.sum_congr rfl ?_
            intro i hi
            rw [Finset.mul_sum]
    _ = ∑ i, ∑ j, star (c i) * innerProbChar (t i - t j) x * c j := by
          refine Finset.sum_congr rfl ?_
          intro i hi
          refine Finset.sum_congr rfl ?_
          intro j hj
          have hstarExp :
              star (Complex.exp (↑(inner ℝ x (-t i)) * Complex.I)) =
                Complex.exp (↑(inner ℝ x (t i)) * Complex.I) := by
            simpa using (Complex.exp_conj (↑(inner ℝ x (-t i)) * Complex.I)).symm
          have hphase :
              star (innerProbChar (-t i) x) * innerProbChar (-t j) x =
                innerProbChar (t i - t j) x := by
            rw [innerProbChar_apply, innerProbChar_apply, innerProbChar_apply, hstarExp]
            rw [← Complex.exp_add]
            congr 1
            rw [sub_eq_add_neg, inner_add_right]
            rw [← add_mul]
            simp
          calc
            star (c i * innerProbChar (-t i) x) * (c j * innerProbChar (-t j) x)
                = (star (c i) * star (innerProbChar (-t i) x)) *
                    (c j * innerProbChar (-t j) x) := by
                    simp [star_mul, mul_left_comm, mul_comm]
            _ = star (c i) * (star (innerProbChar (-t i) x) * innerProbChar (-t j) x) * c j := by
                  ring
            _ = star (c i) * innerProbChar (t i - t j) x * c j := by
                  simpa [mul_assoc] using congrArg (fun z : ℂ ↦ star (c i) * z * c j) hphase

/-- Helper for Lemma 15.28: every quadratic form of the characteristic-function kernel is a
nonnegative integral of a pointwise square. -/
lemma charFunQuadraticSum_nonneg {d n : ℕ}
    (μ : Measure (EuclideanSpace ℝ (Fin d))) [IsFiniteMeasure μ]
    (t : Fin n → EuclideanSpace ℝ (Fin d)) (c : Fin n → ℂ) :
    0 ≤ ∑ i, ∑ j, star (c i) * charFun μ (t i - t j) * c j := by
  let integrand : EuclideanSpace ℝ (Fin d) → ℂ :=
    fun x ↦ ∑ i, ∑ j, star (c i) * innerProbChar (t i - t j) x * c j
  have hterm :
      ∀ i j,
        Integrable (fun x ↦ star (c i) * innerProbChar (t i - t j) x * c j) μ := by
    intro i j
    -- Proof comment: each kernel summand is a bounded continuous character multiplied by constants.
    simpa [mul_assoc] using
      (((integrable μ (innerProbChar (t i - t j))).const_mul (star (c i))).mul_const (c j))
  have hkernel :
      ∑ i, ∑ j, star (c i) * charFun μ (t i - t j) * c j = ∫ x, integrand x ∂μ := by
    -- Proof comment: rewrite each characteristic-function entry as a bounded-character integral and
    -- exchange the finite sums with the integral.
    have hinnerSum :
        ∀ i : Fin n,
          Integrable (fun x ↦ ∑ j, star (c i) * innerProbChar (t i - t j) x * c j) μ := by
      intro i
      exact integrable_finset_sum _ (fun j _ ↦ hterm i j)
    calc
      ∑ i, ∑ j, star (c i) * charFun μ (t i - t j) * c j
          = ∑ i, ∑ j, ∫ x, star (c i) * innerProbChar (t i - t j) x * c j ∂μ := by
              refine Finset.sum_congr rfl ?_
              intro i hi
              refine Finset.sum_congr rfl ?_
              intro j hj
              have hleft :
                  star (c i) * ∫ x, innerProbChar (t i - t j) x ∂μ =
                    ∫ x, star (c i) * innerProbChar (t i - t j) x ∂μ := by
                simpa using
                  (integral_const_mul (star (c i))
                    (fun x ↦ innerProbChar (t i - t j) x)).symm
              have hright :
                  (∫ x, star (c i) * innerProbChar (t i - t j) x ∂μ) * c j =
                    ∫ x, star (c i) * innerProbChar (t i - t j) x * c j ∂μ := by
                simpa [mul_assoc] using
                  (integral_mul_const (c j)
                    (fun x ↦ star (c i) * innerProbChar (t i - t j) x)).symm
              calc
                star (c i) * charFun μ (t i - t j) * c j
                    = (star (c i) * ∫ x, innerProbChar (t i - t j) x ∂μ) * c j := by
                        rw [charFun_eq_integral_innerProbChar]
                _ = (∫ x, star (c i) * innerProbChar (t i - t j) x ∂μ) * c j := by
                      rw [hleft]
                _ = ∫ x, star (c i) * innerProbChar (t i - t j) x * c j ∂μ := by
                      rw [hright]
      _ = ∑ i, ∫ x, ∑ j, star (c i) * innerProbChar (t i - t j) x * c j ∂μ := by
            refine Finset.sum_congr rfl ?_
            intro i hi
            symm
            exact integral_finset_sum _ (fun j _ ↦ hterm i j)
      _ = ∫ x, integrand x ∂μ := by
            symm
            simp only [integrand]
            exact integral_finset_sum _ (fun i _ ↦ hinnerSum i)
  have hnonneg : 0 ≤ ∫ x, integrand x ∂μ := by
    -- Proof comment: the integrand is the pointwise square `star z * z`, hence nonnegative.
    refine integral_nonneg ?_
    intro x
    simp only [integrand]
    rw [differenceInnerProbCharKernel_eq_phaseSquare]
    simpa using star_mul_self_nonneg (∑ i, c i * innerProbChar (-t i) x)
  rw [hkernel]
  exact hnonneg

-- Proof sketch: expand the quadratic form of the matrix
-- `((MeasureTheory.charFun μ (t i - t j)))` using the integral formula for the characteristic
-- function, rearrange the finite sums under the integral, and identify the integrand as the
-- pointwise squared norm `‖∑ i, z i * exp (⟪x, t i⟫ * Complex.I)‖^2`.
/-- Lemma 15.28: the characteristic function of a finite measure on `ℝ^d` is positive
semidefinite. The matrix formulation is the finite-family specialization of this owner-level
statement. -/
theorem charFun_isPositiveSemidefiniteFunction_of_isFiniteMeasure {d : ℕ}
    (μ : Measure (EuclideanSpace ℝ (Fin d))) [IsFiniteMeasure μ] :
    IsPositiveSemidefiniteFunction (charFun μ) := by
  -- Proof comment: use the quadratic-sum criterion from Definition 15.27 and close each quadratic
  -- form by the nonnegative integral from `charFunQuadraticSum_nonneg`.
  rw [isPositiveSemidefiniteFunction_iff_quadratic_sum_nonneg]
  intro n t c
  exact charFunQuadraticSum_nonneg μ t c

/-- Lemma 15.28, matrix form: every finite difference-kernel matrix associated with the
characteristic function of a finite measure on `ℝ^d` is positive semidefinite. -/
theorem charFun_posSemidef {d n : ℕ} (μ : Measure (EuclideanSpace ℝ (Fin d)))
    [IsFiniteMeasure μ] (t : Fin n → EuclideanSpace ℝ (Fin d)) :
    (Matrix.of fun i j ↦ charFun μ (t i - t j)).PosSemidef := by
  simpa [IsPositiveSemidefiniteFunction] using
    charFun_isPositiveSemidefiniteFunction_of_isFiniteMeasure μ n t
