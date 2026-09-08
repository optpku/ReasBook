module

public import ReasLib.Analysis.Calculus.LocalInvariantGraph.ExplicitContraction.MetricTopSectionFacade

public section

noncomputable section

universe u

namespace LocalInvariantGraph

variable {X : Type u} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-!
This module supplies the regularity-only bridge for the order-one top-section
interface.  It does not manufacture `ContDiff` from a metric fixed-point
equation; it exposes the standard first derivative section once that regularity
has already been established.
-/

/-- Helper for Infrastructure I.16a: the first iterated derivative of a globally
`C^1` graph is a continuous section. -/
theorem continuous_iteratedFDeriv_one_of_contDiff
    {ζ : ℝ → X}
    (hζ : ContDiff ℝ 1 ζ) :
    Continuous (fun u ↦ iteratedFDeriv ℝ 1 ζ u) := by
  have horder : (1 : ℕ) ≤ (1 : WithTop ℕ∞) := by norm_num
  exact hζ.continuous_iteratedFDeriv (m := 1) horder

/-- Helper for Infrastructure I.16a: the first iterated derivative of a globally
`C^1` graph differentiates the zeroth Taylor coefficient. -/
theorem iteratedFDeriv_one_hasFDerivAt_ftaylor_zero
    {ζ : ℝ → X}
    (hζ : ContDiff ℝ 1 ζ) :
    ∀ u, HasFDerivAt
      (fun y ↦ (ftaylorSeries ℝ ζ y) 0)
      ((iteratedFDeriv ℝ 1 ζ u).curryLeft) u := by
  intro u
  have horder : (0 : ℕ) < (1 : WithTop ℕ∞) := by norm_num
  simpa only [ftaylorSeries] using hζ.ftaylorSeries.fderiv 0 horder u

/-- Infrastructure I.16a: a globally `C^1` graph supplies the continuous first
derivative section and the predecessor Taylor derivative equation required by
`OrderOneHolonomicSectionData`. -/
noncomputable def orderOneHolonomicSectionData_of_contDiff
    {ζ : ℝ → X}
    (hζ : ContDiff ℝ 1 ζ) :
    OrderOneHolonomicSectionData ζ :=
  { value := fun u ↦ iteratedFDeriv ℝ 1 ζ u
    continuous_value := continuous_iteratedFDeriv_one_of_contDiff hζ
    derivative := iteratedFDeriv_one_hasFDerivAt_ftaylor_zero hζ }

end LocalInvariantGraph
