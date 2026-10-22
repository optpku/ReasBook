/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Books.ProbabilityTheory_Klenke_2020.Items.Chap17.Definition_17_42
import Books.ProbabilityTheory_Klenke_2020.Items.Chap17.Definition_17_43
import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal ProbabilityTheory

noncomputable section

universe u

namespace ProbabilityTheory

variable {E : Type u}

/-- Helper for Remark 17.44: every entry of a stochastic matrix is finite, because each entry is
dominated by the corresponding row sum `1`. -/
theorem stochasticEntry_neTop (p : E → E → ℝ≥0∞) (hp : IsStochasticMatrix p) :
    ∀ x y : E, p x y ≠ ∞ := by
  intro x y
  -- Compare one matrix entry with the full row sum and use `hp x : ∑' z, p x z = 1`.
  have hle : p x y ≤ 1 := by
    calc
      p x y ≤ ∑' z : E, p x z := ENNReal.le_tsum y
      _ = 1 := hp x
  exact (lt_of_le_of_lt hle (by simp)).ne

/-- Helper for Remark 17.44: summability of the weighted row norms already forces summability of
the underlying row action. -/
theorem rowSummableOfSummableNorm
    (p : E → E → ℝ≥0∞) (f : E → ℝ) (x : E)
    (hsumNorm : Summable (fun y : E ↦ (p x y).toReal * ‖f y‖)) :
    Summable (fun y : E ↦ (p x y).toReal * f y) := by
  -- Rewrite the norm of each row term into the given weighted norm series.
  have hnorm : Summable (fun y : E ↦ ‖(p x y).toReal * f y‖) := by
    simpa [abs_mul, abs_of_nonneg (ENNReal.toReal_nonneg)] using hsumNorm
  exact hnorm.of_norm

/-- Helper for Remark 17.44: summability of the row action implies summability of the weighted row
norms. -/
theorem rowNormSummableOfSummable
    (p : E → E → ℝ≥0∞) (f : E → ℝ) (x : E)
    (hsum : Summable (fun y : E ↦ (p x y).toReal * f y)) :
    Summable (fun y : E ↦ (p x y).toReal * ‖f y‖) := by
  -- Pass to norms termwise so the later `lintegral` computation can use nonnegative coefficients.
  simpa [abs_mul, abs_of_nonneg (ENNReal.toReal_nonneg)] using hsum.norm

section

variable [MeasurableSpace E] [DiscreteMeasurableSpace E]

/-- Helper for Remark 17.44: harmonicity of `f` for `discreteMatrixKernel p` forces absolute
summability of each row action `∑' y, (p x y).toReal * f y`. -/
theorem rowSummableOfHarmonic (p : E → E → ℝ≥0∞) (f : E → ℝ)
    (hf : IsHarmonic (discreteMatrixKernel p) f) :
    ∀ x : E, Summable (fun y : E ↦ (p x y).toReal * f y) := by
  intro x
  rcases (isHarmonic_iff (p := discreteMatrixKernel p) (f := f)).mp hf with ⟨hint, _⟩
  -- Rewrite the row measure into a countable sum of Dirac masses before reading off
  -- absolute summability from the integrability criterion.
  have hrow :
      Integrable f (Measure.sum (fun y : E ↦ p x y • Measure.dirac y)) := by
    simpa [discreteMatrixKernel_apply] using hint x
  have hsumNorm : Summable (fun y : E ↦ (p x y).toReal * ‖f y‖) := by
    simpa using hrow.summable_of_dirac
  exact rowSummableOfSummableNorm p f x hsumNorm

/-- Helper for Remark 17.44: rowwise summability together with the fixed-point equation
`(p ⋆ᶠ f) x = f x` implies `f` is harmonic for `discreteMatrixKernel p`. -/
theorem harmonicOfRowSummableFixedPoint
    (p : E → E → ℝ≥0∞) (hp : IsStochasticMatrix p) (f : E → ℝ)
    (hf : ∀ x : E, Summable (fun y : E ↦ (p x y).toReal * f y) ∧ (p ⋆ᶠ f) x = f x) :
    IsHarmonic (discreteMatrixKernel p) f := by
  refine (isHarmonic_iff (p := discreteMatrixKernel p) (f := f)).mpr ?_
  constructor
  · intro x
    -- Rebuild rowwise integrability by computing the lintegral of `‖f‖` against the explicit
    -- row measure and using the summability assumption to show finiteness.
    have hsum : Summable (fun y : E ↦ (p x y).toReal * f y) := (hf x).1
    have hsumNorm : Summable (fun y : E ↦ (p x y).toReal * ‖f y‖) := by
      exact rowNormSummableOfSummable p f x hsum
    refine ⟨Measurable.of_discrete.aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_norm, discreteMatrixKernel_apply, lintegral_sum_measure]
    have hterm :
        (fun y : E ↦ p x y * ENNReal.ofReal ‖f y‖) =
          fun y : E ↦ ENNReal.ofReal ((p x y).toReal * ‖f y‖) := by
      funext y
      have hentry :
          p x y = ENNReal.ofReal (p x y).toReal :=
        (ENNReal.ofReal_toReal (stochasticEntry_neTop p hp x y)).symm
      calc
        p x y * ENNReal.ofReal ‖f y‖
          = ENNReal.ofReal (p x y).toReal * ENNReal.ofReal ‖f y‖ := by
            simpa using congrArg (fun t : ℝ≥0∞ ↦ t * ENNReal.ofReal ‖f y‖) hentry
        _ = ENNReal.ofReal ((p x y).toReal * ‖f y‖) := by
            exact
              (ENNReal.ofReal_mul (p := (p x y).toReal) (q := ‖f y‖)
                ENNReal.toReal_nonneg).symm
    have hlintegralTerms :
        (fun y : E ↦ ∫⁻ a, ENNReal.ofReal ‖f a‖ ∂p x y • Measure.dirac y) =
          (fun y : E ↦ p x y * ENNReal.ofReal ‖f y‖) := by
      funext y
      rw [lintegral_smul_measure, lintegral_dirac, smul_eq_mul]
    rw [hlintegralTerms]
    rw [hterm, ← ENNReal.ofReal_tsum_of_nonneg (fun y ↦ by positivity) hsumNorm]
    simp
  · intro x
    -- Rewrite the assumed fixed-point equation into the owner-level harmonicity identity.
    simpa [matrixFunctionAction_apply] using ((hf x).2).symm

/- Remark 17.44 records two source-facing clauses about the discrete matrix kernel:
an invariant measure is a left eigenvector of the transition matrix at eigenvalue `1`, and
a harmonic function is a right eigenvector at eigenvalue `1`. Keep the two theorem clauses below
adjacent so the file exposes the textbook remark as one contiguous main block. -/
-- Proof sketch: combine `Kernel.Invariant (discreteMatrixKernel p) μ` with
-- `comp_discreteMatrixKernel_apply_singleton_eq_tsum` for the source-facing action `μ ⋆ₘ p`,
-- then use `Measure.ext_of_singleton` on the countable discrete state space to pass between
-- equality of measures and equality of all singleton masses.
/-- Left-eigenvector clause of Remark 17.44: on a countable discrete state space, an invariant
measure for the canonical
discrete kernel `discreteMatrixKernel p` is exactly a left eigenvector of the transition matrix
`p` for the eigenvalue `1`, written on the singleton mass function `x ↦ μ {x}`. -/
theorem kernelInvariant_iff_leftEigenvectorAtOne [Countable E]
    (p : E → E → ℝ≥0∞) (μ : Measure E) :
    Kernel.Invariant (discreteMatrixKernel p) μ ↔
      ∀ x : E, ∑' y : E, μ {y} * p y x = μ {x} := by
  constructor
  · intro h x
    -- Evaluate the invariant-measure identity on the singleton `{x}` and rewrite it as the
    -- source-facing matrix action.
    have hx :
        (μ.bind (discreteMatrixKernel p)) ({x} : Set E) = μ ({x} : Set E) :=
      congrArg (fun ν : Measure E ↦ ν ({x} : Set E)) h
    simpa [comp_discreteMatrixKernel_apply_singleton_eq_tsum] using hx
  · intro h
    -- On a countable discrete space, equality of all singleton masses determines the measure.
    refine Measure.ext_of_singleton fun x ↦ ?_
    simpa [comp_discreteMatrixKernel_apply_singleton_eq_tsum] using h x

-- Proof sketch: unfold `IsHarmonic`, rewrite the kernel integral with
-- `integral_discreteMatrixKernel_eq_tsum` for the source-facing action `p ⋆ᶠ f`, and use the
-- summability part as the needed integrability witness for each row.
/-- Right-eigenvector clause of Remark 17.44: a harmonic function for the canonical discrete kernel
`discreteMatrixKernel
p` is exactly a right eigenvector of the stochastic transition matrix `p` for the eigenvalue `1`,
with the required summability of the row action recorded explicitly. -/
theorem isHarmonic_iff_rightEigenvectorAtOne
    (p : E → E → ℝ≥0∞) (hp : IsStochasticMatrix p) (f : E → ℝ) :
    IsHarmonic (discreteMatrixKernel p) f ↔
      ∀ x : E, Summable (fun y : E ↦ (p x y).toReal * f y) ∧
        (p ⋆ᶠ f) x = f x := by
  constructor
  · intro hf x
    rcases (isHarmonic_iff (p := discreteMatrixKernel p) (f := f)).mp hf with ⟨_, hfix⟩
    constructor
    · -- Use the dedicated rowwise summability bridge instead of rebuilding the Dirac argument
      -- inside the main theorem.
      exact rowSummableOfHarmonic p f hf x
    · -- The harmonic fixed-point identity is exactly the right-eigenvector equation.
      simpa [matrixFunctionAction_apply] using (hfix x).symm
  · intro hf
    -- Assemble harmonicity from the rowwise summability and fixed-point data.
    exact harmonicOfRowSummableFixedPoint p hp f hf

-- Proof comment: package the two source-facing clauses under the single item label so the file
-- exposes Remark 17.44 as one main declaration with two conjunctive parts.
/-- Remark 17.44: on a countable discrete state space, invariant measures for
`discreteMatrixKernel p` are exactly the left eigenvectors of `p` at eigenvalue `1`, and harmonic
functions are exactly the right eigenvectors at eigenvalue `1` with the row summability recorded
explicitly. -/
theorem «kernelInvariant_iff_leftEigenvectorAtOne / isHarmonic_iff_rightEigenvectorAtOne»
    [Countable E] (p : E → E → ℝ≥0∞) (μ : Measure E) (hp : IsStochasticMatrix p) (f : E → ℝ) :
    (Kernel.Invariant (discreteMatrixKernel p) μ ↔
      ∀ x : E, ∑' y : E, μ {y} * p y x = μ {x}) ∧
      (IsHarmonic (discreteMatrixKernel p) f ↔
        ∀ x : E, Summable (fun y : E ↦ (p x y).toReal * f y) ∧
          (p ⋆ᶠ f) x = f x) := by
  constructor
  · exact kernelInvariant_iff_leftEigenvectorAtOne p μ
  · exact isHarmonic_iff_rightEigenvectorAtOne p hp f

end

end ProbabilityTheory
