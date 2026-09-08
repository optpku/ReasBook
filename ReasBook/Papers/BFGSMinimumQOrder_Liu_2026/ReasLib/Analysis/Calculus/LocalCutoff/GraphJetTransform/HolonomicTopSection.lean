module

public import ReasLib.Analysis.Calculus.LocalCutoff.GraphJetTransform
public import ReasLib.Analysis.Calculus.FiniteTaylorJet.UpdateTop

public section

namespace LocalCutoff.GraphTransform

universe u

variable {X : Type u} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- Helper for Infrastructure I.16 (Finite-order graph-jet contraction): a continuous
top Taylor section with the predecessor derivative equation upgrades a graph from
`C^(r - 1)` to `C^r`. -/
theorem contDiff_succ_of_holonomic_topSection
    {r : ℕ} {ζ : ℝ → X}
    (hr : 1 ≤ r)
    (hprev : ContDiff ℝ (r - 1) ζ)
    (a : ℝ → (ℝ [×(r - 1 + 1)]→L[ℝ] X))
    (ha : Continuous a)
    (hderiv : ∀ u, HasFDerivAt
      (fun y ↦ (ftaylorSeries ℝ ζ y) (r - 1))
      ((a u).curryLeft) u) :
    ContDiff ℝ r ζ := by
  have hseries : HasFTaylorSeriesUpTo (r - 1) ζ (ftaylorSeries ℝ ζ) :=
    hprev.ftaylorSeries
  have hupdated := HasFTaylorSeriesUpTo.contDiff_update_succ_top hseries a ha hderiv
  have horder : ((r - 1 : ℕ) : WithTop ENat) + 1 = (r : WithTop ENat) := by
    exact_mod_cast Nat.sub_add_cancel hr
  simpa only [horder] using hupdated

end LocalCutoff.GraphTransform
