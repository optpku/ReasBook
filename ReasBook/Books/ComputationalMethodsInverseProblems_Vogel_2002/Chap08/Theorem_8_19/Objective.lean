/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import ComputationalMethodsInverseProblems_Vogel_2002.Chap08.Definition_8_9
public import ComputationalMethodsInverseProblems_Vogel_2002.Chap08.Theorem_8_18.Comparison

public section

noncomputable section

namespace VariationalRegularization

variable {d : ℕ}

/-- A quadratic-discrepancy `EReal`-valued regularized least-squares functional on
`Lᵖ(Ω)` with penalty `J` pulled back along `lpToL1 : Lᵖ(Ω) → L¹(Ω)`.

This item-owned helper is reused by later Chapter 8 approximation files; it is
not asserted here to be the exact source owner of `(8.73)`. -/
def regularizedLeastSquaresFunctional
    {Ω : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin d))}
    {p : ENNReal} [Fact ((1 : ENNReal) ≤ p)]
    [MeasureTheory.IsFiniteMeasure (domainMeasure Ω)]
    (K : MeasureTheory.Lp ℝ p (domainMeasure Ω) →L[ℝ]
      MeasureTheory.Lp ℝ 2 (domainMeasure Ω))
    (g : MeasureTheory.Lp ℝ 2 (domainMeasure Ω))
    (α : ℝ)
    (J : MeasureTheory.Lp ℝ 1 (domainMeasure Ω) → EReal) :
    MeasureTheory.Lp ℝ p (domainMeasure Ω) → EReal :=
  fun f ↦ ((‖K f - g‖ ^ 2 / 2 : ℝ) : EReal) + (α : EReal) * J (lpToL1 f)

/-- The defining formula for `regularizedLeastSquaresFunctional`. -/
theorem regularizedLeastSquaresFunctional_def
    {Ω : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin d))}
    {p : ENNReal} [Fact ((1 : ENNReal) ≤ p)]
    [MeasureTheory.IsFiniteMeasure (domainMeasure Ω)]
    (K : MeasureTheory.Lp ℝ p (domainMeasure Ω) →L[ℝ]
      MeasureTheory.Lp ℝ 2 (domainMeasure Ω))
    (g : MeasureTheory.Lp ℝ 2 (domainMeasure Ω))
    (α : ℝ)
    (J : MeasureTheory.Lp ℝ 1 (domainMeasure Ω) → EReal)
    (f : MeasureTheory.Lp ℝ p (domainMeasure Ω)) :
    regularizedLeastSquaresFunctional K g α J f =
      ((‖K f - g‖ ^ 2 / 2 : ℝ) : EReal) + (α : EReal) * J (lpToL1 f) := sorry

/-- The specialization of `regularizedLeastSquaresFunctional` with
`J = totalVariation`. -/
def tvRegularizedLeastSquaresFunctional
    {Ω : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin d))}
    {p : ENNReal} [Fact ((1 : ENNReal) ≤ p)]
    [MeasureTheory.IsFiniteMeasure (domainMeasure Ω)]
    (K : MeasureTheory.Lp ℝ p (domainMeasure Ω) →L[ℝ]
      MeasureTheory.Lp ℝ 2 (domainMeasure Ω))
    (g : MeasureTheory.Lp ℝ 2 (domainMeasure Ω))
    (α : ℝ) :
    MeasureTheory.Lp ℝ p (domainMeasure Ω) → EReal :=
  regularizedLeastSquaresFunctional K g α totalVariation

/-- `tvRegularizedLeastSquaresFunctional` is the specialization of
`regularizedLeastSquaresFunctional` with `J = totalVariation`. -/
theorem tvRegularizedLeastSquaresFunctional_def
    {Ω : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin d))}
    {p : ENNReal} [Fact ((1 : ENNReal) ≤ p)]
    [MeasureTheory.IsFiniteMeasure (domainMeasure Ω)]
    (K : MeasureTheory.Lp ℝ p (domainMeasure Ω) →L[ℝ]
      MeasureTheory.Lp ℝ 2 (domainMeasure Ω))
    (g : MeasureTheory.Lp ℝ 2 (domainMeasure Ω))
    (α : ℝ)
    (f : MeasureTheory.Lp ℝ p (domainMeasure Ω)) :
    tvRegularizedLeastSquaresFunctional K g α f =
      ((‖K f - g‖ ^ 2 / 2 : ℝ) : EReal) +
        (α : EReal) * totalVariation (lpToL1 f) := sorry

end VariationalRegularization
