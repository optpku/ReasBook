/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Books.ProbabilityTheory_Klenke_2020.Items.Chap08.Example_8_27
import Books.ProbabilityTheory_Klenke_2020.Items.Chap19.Definition_19_11
import Mathlib

open MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory

noncomputable section

universe u

attribute [local instance] Classical.propDecidable

namespace ProbabilityTheory

variable {E : Type u}

/- Layering for Example 19.10:
- `source-facing`: the normalized conductance walk `p(x,y) = C(x,y) / conductance C x` and the
  reversing measure with singleton masses `π({x}) = conductance C x`.
- `core/canonical`: the owner declarations `conductance`, `IsRandomWalkWithWeights`, and
  `Kernel.IsReversible`.
- `bridge/view`: `conductanceTransitionMatrix` and `conductanceMeasure` package the textbook
  source-facing data in terms of those canonical owners. -/

/-- The transition matrix obtained by normalizing the conductances in the row of `x`. -/
def conductanceTransitionMatrix (C : E → E → ℝ≥0∞) (x y : E) : ℝ≥0∞ :=
  C x y / conductance C x

-- Proof sketch: unfold `conductanceTransitionMatrix`; the entry `(x,y)` is defined by the quotient
-- `C x y / conductance C x`.
/-- The conductance transition matrix satisfies `p(x,y) = C(x,y) / C(x)`. -/
@[simp]
theorem conductanceTransitionMatrix_apply (C : E → E → ℝ≥0∞) (x y : E) :
    conductanceTransitionMatrix C x y = C x y / conductance C x := rfl

section ConductanceReversibility

variable {C : E → E → ℝ≥0∞}

-- Proof sketch: use `hC_finite` and `hC_pos` to factor `conductance C x` out of the row sum
-- `∑' y, C x y / conductance C x`; this gives `(∑' y, C x y) / conductance C x = 1`.
/-- The normalized conductance matrix has row sum `1`, so it is a stochastic matrix. -/
theorem conductanceTransitionMatrix_isStochastic
    (hC_finite : ∀ x : E, conductance C x < ∞)
    (hC_pos : ∀ x : E, 0 < conductance C x) :
    IsStochasticMatrix (conductanceTransitionMatrix C) := by
  intro x
  -- Rewrite the row entries into a common normalization factor.
  calc
    ∑' y : E, conductanceTransitionMatrix C x y
        = ∑' y : E, C x y * (conductance C x)⁻¹ := by
            simp_rw [conductanceTransitionMatrix_apply, div_eq_mul_inv]
    _ = (∑' y : E, C x y) * (conductance C x)⁻¹ := ENNReal.tsum_mul_right
    _ = conductance C x * (conductance C x)⁻¹ := by rw [← conductance]
    _ = 1 := ENNReal.mul_inv_cancel (ne_of_gt (hC_pos x)) (ne_of_lt (hC_finite x))

-- Proof sketch: the owner abstraction `IsRandomWalkWithWeights` packages exactly the symmetry,
-- finiteness, and row-normalization data attached to the conductance transition matrix in
-- Example 19.10. Use `conductanceTransitionMatrix_isStochastic` for the row-sum field and
-- `conductanceTransitionMatrix_apply` for the normalization formula.
/-- The normalized conductance matrix is the random walk with weights `C` in the sense of
Definition 19.11. -/
theorem conductanceTransitionMatrix_isRandomWalkWithWeights
    (hC_symm : ∀ x y : E, C x y = C y x)
    (hC_finite : ∀ x : E, conductance C x < ∞)
    (hC_pos : ∀ x : E, 0 < conductance C x) :
    IsRandomWalkWithWeights (conductanceTransitionMatrix C) C where
  -- Package the row-sum normalization proved above.
  isStochastic := conductanceTransitionMatrix_isStochastic hC_finite hC_pos
  -- The source hypothesis already gives symmetry of the conductances.
  symmetric := hC_symm
  -- The transition formula is exactly the defining equation of the matrix.
  transition_eq := conductanceTransitionMatrix_apply C

-- Proof sketch: substitute the definition of `conductanceTransitionMatrix`; the factor
-- `conductance C x` cancels against the denominator because `hC_pos x` makes the
-- denominator strictly positive.
/-- Multiplying `p(x,y)` by the vertex weight `C(x)` recovers the original conductance `C(x,y)`. -/
theorem conductance_mul_transitionMatrix
    (hC_finite : ∀ x : E, conductance C x < ∞)
    (hC_pos : ∀ x : E, 0 < conductance C x) (x y : E) :
    conductance C x * conductanceTransitionMatrix C x y = C x y := by
  -- Expand the normalized entry and cancel the positive finite denominator.
  calc
    conductance C x * conductanceTransitionMatrix C x y
        = conductance C x * (C x y * (conductance C x)⁻¹) := by
            rw [conductanceTransitionMatrix_apply, div_eq_mul_inv]
    _ = C x y * (conductance C x * (conductance C x)⁻¹) := by
          simpa [mul_assoc, mul_left_comm, mul_comm]
    _ = C x y * 1 := by
          rw [ENNReal.mul_inv_cancel (ne_of_gt (hC_pos x)) (ne_of_lt (hC_finite x))]
    _ = C x y := by rw [mul_one]

end ConductanceReversibility

section ConductanceMeasure

variable [MeasurableSpace E] [DiscreteMeasurableSpace E]

/-- The measure on the vertex set whose singleton mass at `x` is the total conductance `C(x)`. -/
def conductanceMeasure (C : E → E → ℝ≥0∞) : Measure E :=
  Measure.sum fun x : E ↦ conductance C x • Measure.dirac x

-- Proof sketch: expand `conductanceMeasure` as a sum of weighted Dirac masses and evaluate it on
-- the singleton `{x}`; only the `x`-term survives.
/-- The conductance measure assigns to `{x}` the total outgoing conductance `C(x)`. -/
@[simp]
theorem conductanceMeasure_apply_singleton (C : E → E → ℝ≥0∞) (x : E) :
    conductanceMeasure C {x} = conductance C x := by
  -- Evaluate the sum of weighted Dirac masses on the singleton `{x}`.
  simpa [conductanceMeasure] using
    (Measure.sum_smul_dirac_singleton (f := fun y : E ↦ conductance C y) (a := x))

section ConductanceReversibility

variable {C : E → E → ℝ≥0∞}

/-- Helper for Example 19.10: integrating a nonnegative function against `conductanceMeasure C`
expands into the weighted sum over the Dirac masses at each vertex. -/
theorem lintegral_conductanceMeasure (f : E → ℝ≥0∞) :
    ∫⁻ x, f x ∂ conductanceMeasure C = ∑' x : E, conductance C x * f x := by
  rw [conductanceMeasure, lintegral_sum_measure]
  refine tsum_congr fun x ↦ ?_
  rw [lintegral_smul_measure, lintegral_dirac]
  simp [smul_eq_mul]

/-- Helper for Example 19.10: the conductance kernel applied to a measurable set `B` is the sum
of the matrix entries landing in `B`. -/
theorem discreteMatrixKernel_conductanceTransitionMatrix_apply
    (B : Set E) (hB : MeasurableSet B) (x : E) :
    discreteMatrixKernel (conductanceTransitionMatrix C) x B
      = ∑' y : E, if y ∈ B then conductanceTransitionMatrix C x y else (0 : ℝ≥0∞) := by
  rw [discreteMatrixKernel_apply, Measure.sum_apply _ hB]
  refine tsum_congr fun y ↦ ?_
  by_cases hy : y ∈ B
  · simp [Measure.smul_apply, hy]
  · simp [Measure.smul_apply, hy]

/-- Helper for Example 19.10: the mass that the conductance kernel transports from `A` to a
measurable set `B` is the double sum of the conductances on `A × B`. -/
theorem conductanceKernel_flow
    (hC_finite : ∀ x : E, conductance C x < ∞)
    (hC_pos : ∀ x : E, 0 < conductance C x)
    (A B : Set E) (hA : MeasurableSet A) (hB : MeasurableSet B) :
    ∫⁻ x in A, discreteMatrixKernel (conductanceTransitionMatrix C) x B ∂ conductanceMeasure C
      = ∑' x : E, Set.indicator A (fun x ↦ ∑' y : E, Set.indicator B (fun y ↦ C x y) y) x := by
  classical
  -- Expand the restricted integral through the Dirac-sum definition of `conductanceMeasure C`.
  rw [← lintegral_indicator hA, lintegral_conductanceMeasure]
  refine tsum_congr fun x ↦ ?_
  by_cases hx : x ∈ A
  · rw [Set.indicator_of_mem hx]
    calc
      conductance C x * discreteMatrixKernel (conductanceTransitionMatrix C) x B
          = conductance C x *
              ∑' y : E, if y ∈ B then conductanceTransitionMatrix C x y else (0 : ℝ≥0∞) := by
                rw [discreteMatrixKernel_conductanceTransitionMatrix_apply (C := C) B hB x]
      _ = ∑' y : E,
            conductance C x *
              (if y ∈ B then conductanceTransitionMatrix C x y else (0 : ℝ≥0∞)) := by
            rw [← ENNReal.tsum_mul_left]
      _ = ∑' y : E, Set.indicator B (fun y ↦ C x y) y := by
            refine tsum_congr fun y ↦ ?_
            by_cases hy : y ∈ B
            · rw [Set.indicator_of_mem hy, if_pos hy, conductance_mul_transitionMatrix hC_finite hC_pos]
            · rw [Set.indicator_of_notMem hy, if_neg hy, mul_zero]
      _ = Set.indicator A (fun x ↦ ∑' y : E, Set.indicator B (fun y ↦ C x y) y) x := by
            rw [Set.indicator_of_mem hx]
  · rw [Set.indicator_of_notMem hx]
    rw [Set.indicator_of_notMem hx]
    simp

-- Proof sketch: on singleton sets `{x}` and `{y}`, the reversibility identity becomes
-- `conductance C x * conductanceTransitionMatrix C x y =
-- conductance C y * conductanceTransitionMatrix C y x`. Apply
-- `conductance_mul_transitionMatrix` on both sides and use the symmetry hypothesis
-- `hC_symm`.
/-- Example 19.10: for a symmetric conductance family `C` with finite positive vertex weights, the
discrete kernel with transition matrix `p(x,y) = C(x,y) / C(x)` is reversible with respect to the
measure whose singleton masses are `π({x}) = C(x)`. -/
theorem conductanceKernel_isReversible
    (hC_symm : ∀ x y : E, C x y = C y x)
    (hC_finite : ∀ x : E, conductance C x < ∞)
    (hC_pos : ∀ x : E, 0 < conductance C x) :
    Kernel.IsReversible
      (discreteMatrixKernel (conductanceTransitionMatrix C))
      (conductanceMeasure C) := by
  classical
  intro A B hA hB
  let flowTerm : E → E → ℝ≥0∞ :=
    fun x y ↦ Set.indicator A (fun x ↦ Set.indicator B (fun y ↦ C x y) y) x
  have hflow_left :
      ∑' x : E, Set.indicator A (fun x ↦ ∑' y : E, Set.indicator B (fun y ↦ C x y) y) x
        = ∑' x : E, ∑' y : E, flowTerm x y := by
    -- Repackage the outer-inner condition into a single indicator on `A × B`.
    refine tsum_congr fun x => ?_
    by_cases hx : x ∈ A
    · rw [Set.indicator_of_mem hx]
      simp [flowTerm, hx]
    · rw [Set.indicator_of_notMem hx]
      simp [flowTerm, hx]
  have hflow_right :
      ∑' y : E, Set.indicator B (fun y ↦ ∑' x : E, Set.indicator A (fun x ↦ C y x) x) y
        = ∑' y : E, ∑' x : E, flowTerm x y := by
    -- After swapping variables, symmetry turns `C y x` back into `C x y`.
    refine tsum_congr fun y => ?_
    by_cases hy : y ∈ B
    · rw [Set.indicator_of_mem hy]
      simp [flowTerm, hy, hC_symm]
    · rw [Set.indicator_of_notMem hy]
      simp [flowTerm, hy]
  -- Rewrite both setwise flows by the helper theorem and swap the two `tsum`s.
  calc
    ∫⁻ x in A, discreteMatrixKernel (conductanceTransitionMatrix C) x B ∂ conductanceMeasure C
      = ∑' x : E, Set.indicator A (fun x ↦ ∑' y : E, Set.indicator B (fun y ↦ C x y) y) x :=
        conductanceKernel_flow hC_finite hC_pos A B hA hB
    _ = ∑' x : E, ∑' y : E, flowTerm x y := hflow_left
    _ = ∑' y : E, ∑' x : E, flowTerm x y := ENNReal.tsum_comm
    _ = ∑' y : E, Set.indicator B (fun y ↦ ∑' x : E, Set.indicator A (fun x ↦ C y x) x) y :=
          hflow_right.symm
    _ = ∫⁻ x in B, discreteMatrixKernel (conductanceTransitionMatrix C) x A ∂ conductanceMeasure C :=
        (conductanceKernel_flow hC_finite hC_pos B A hB hA).symm

end ConductanceReversibility
end ConductanceMeasure

end ProbabilityTheory
