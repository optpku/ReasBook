module

public import ReasLib.Analysis.Calculus.LocalCutoff.GraphJetTransform.HolonomicFixedSection

public section

universe u

namespace LocalCutoff.GraphTransform

variable {X : Type u} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- Infrastructure I.16a: a bounded continuous top section together with the
predecessor derivative equation is a holonomic fixed-section certificate. -/
structure BoundedHolonomicFixedSection
    {r : ℕ} (ζ : ℝ → X) where
  value : BoundedContinuousFunction ℝ ((ℝ [×(r - 1 + 1)]→L[ℝ] X))
  derivative : ∀ u, HasFDerivAt
    (fun y ↦ (ftaylorSeries ℝ ζ y) (r - 1))
    ((value u).curryLeft) u

/-- Infrastructure I.16a: the bounded holonomic section upgrades a predecessor
smoothness statement to the successor order. -/
theorem BoundedHolonomicFixedSection.contDiff_succ
    {r : ℕ} {ζ : ℝ → X}
    (certificate : BoundedHolonomicFixedSection (r := r) ζ)
    (hr : 1 ≤ r) (hprev : ContDiff ℝ (r - 1) ζ) :
    ContDiff ℝ r ζ := by
  exact LocalCutoff.GraphTransform.contDiff_succ_of_holonomic_topSection
    hr hprev certificate.value certificate.value.continuous certificate.derivative

/-- Infrastructure I.16a: the bounded holonomic section is the next iterated
Fréchet derivative of the graph. -/
theorem BoundedHolonomicFixedSection.value_eq_iteratedFDeriv
    {r : ℕ} {ζ : ℝ → X}
    (certificate : BoundedHolonomicFixedSection (r := r) ζ)
    (hr : 1 ≤ r) (hprev : ContDiff ℝ (r - 1) ζ) :
    ∀ u, certificate.value u = iteratedFDeriv ℝ (r - 1 + 1) ζ u := by
  exact (LocalCutoff.GraphTransform.contDiff_succ_and_topSection_eq_iteratedFDeriv
    hr hprev certificate.value certificate.value.continuous certificate.derivative).2

/-- Infrastructure I.16a: the fixed-section bridge returns both successor
smoothness and iterated-derivative transport in one stable interface. -/
theorem BoundedHolonomicFixedSection.contDiff_succ_and_value_eq_iteratedFDeriv
    {r : ℕ} {ζ : ℝ → X}
    (certificate : BoundedHolonomicFixedSection (r := r) ζ)
    (hr : 1 ≤ r) (hprev : ContDiff ℝ (r - 1) ζ) :
    ContDiff ℝ r ζ ∧
      ∀ u, certificate.value u = iteratedFDeriv ℝ (r - 1 + 1) ζ u := by
  exact LocalCutoff.GraphTransform.contDiff_succ_and_topSection_eq_iteratedFDeriv
    hr hprev certificate.value certificate.value.continuous certificate.derivative

end LocalCutoff.GraphTransform
