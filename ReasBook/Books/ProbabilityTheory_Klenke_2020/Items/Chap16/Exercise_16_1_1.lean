/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib
import Books.ProbabilityTheory_Klenke_2020.Items.Chap16.Definition_16_1
import Books.ProbabilityTheory_Klenke_2020.Items.Chap16.Example_16_2

open MeasureTheory
open scoped MeasureTheory

noncomputable section

namespace MeasureTheory.ProbabilityMeasure

-- Proof sketch: choose an arbitrary convolution root `ν` of order `n`; since `μ` is supported on
-- `Icc a b`, the law `ν` is supported on an interval of width `(b - a) / n`, so
-- `Var[id; (ν : Measure ℝ)] ≤ ((b - a) / n)^2 / 4`. Passing to the `n`-fold convolution power and
-- using additivity of variance forces `Var[id; (μ : Measure ℝ)] = 0`, hence `μ` is Dirac.
/-- If an infinitely divisible probability measure on `ℝ` has full mass on a compact interval,
then it is a Dirac mass at a point of that interval. -/
theorem eq_diracProba_of_isInfinitelyDivisible_of_measure_Icc_eq_one
    (μ : ProbabilityMeasure ℝ) [IsInfinitelyDivisible μ] (a b : ℝ)
    (hμ : (μ : Measure ℝ) (Set.Icc a b) = 1) :
    ∃ x ∈ Set.Icc a b, μ = diracProba x := by
  rcases _root_.eq_dirac_of_isInfinitelyDivisible_of_measure_Icc_eq_one
      μ a b hμ with ⟨x, hx, hdirac⟩
  refine ⟨x, hx, ?_⟩
  apply ProbabilityMeasure.toMeasure_injective
  simpa [MeasureTheory.diracProba] using hdirac

-- Proof sketch: unpack the bounded-interval concentration hypothesis as some `Icc a b` of full
-- mass, then apply `eq_diracProba_of_isInfinitelyDivisible_of_measure_Icc_eq_one`.
/-- Exercise 16.1.1: an infinitely divisible probability distribution on `ℝ` that is concentrated
on a bounded interval is a Dirac measure. -/
theorem eq_diracProba_of_isInfinitelyDivisible_of_concentrated_on_bounded_interval
    (μ : ProbabilityMeasure ℝ) [IsInfinitelyDivisible μ]
    (hμ : ∃ a b : ℝ, (μ : Measure ℝ) (Set.Icc a b) = 1) :
    ∃ x : ℝ, μ = diracProba x := by
  rcases hμ with ⟨a, b, hμ⟩
  rcases eq_diracProba_of_isInfinitelyDivisible_of_measure_Icc_eq_one μ a b hμ with
    ⟨x, -, hx⟩
  exact ⟨x, hx⟩

end MeasureTheory.ProbabilityMeasure
