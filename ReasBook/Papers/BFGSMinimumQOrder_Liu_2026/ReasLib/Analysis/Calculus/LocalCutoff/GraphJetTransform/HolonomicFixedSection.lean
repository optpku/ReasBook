module

public import ReasLib.Analysis.Calculus.LocalCutoff.GraphJetTransform.HolonomicTopSection
public import ReasLib.Analysis.Calculus.LocalCutoff.GraphJetRealization
public import ReasLib.Analysis.Calculus.LocalCutoff.GraphJetTransform.UniformLimit

public section

open Filter
open scoped Topology

universe u v

namespace LocalCutoff.GraphTransform

variable {X : Type u} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-!
This file provides the interface between a limiting top Taylor section and the
finite-smoothness bootstrap.  The graph-transform file constructs the section;
the present lemmas record the two reusable consequences needed by that
construction.
-/

/-- Helper for Infrastructure C: a top section satisfying the predecessor
derivative equation is the unnormalised next iterated derivative of the graph.
-/
theorem topSection_eq_iteratedFDeriv_of_derivative
    {r : ℕ} {ζ : ℝ → X}
    (hr : 1 ≤ r)
    (hprev : ContDiff ℝ (r - 1) ζ)
    (a : ℝ → (ℝ [×(r - 1 + 1)]→L[ℝ] X))
    (ha : Continuous a)
    (hderiv : ∀ u, HasFDerivAt
      (fun y ↦ (ftaylorSeries ℝ ζ y) (r - 1))
      ((a u).curryLeft) u) :
    ∀ u, a u = iteratedFDeriv ℝ (r - 1 + 1) ζ u := by
  have hreg : ContDiff ℝ r ζ :=
    contDiff_succ_of_holonomic_topSection hr hprev a ha hderiv
  have hseries : HasFTaylorSeriesUpTo r ζ (ftaylorSeries ℝ ζ) :=
    hreg.ftaylorSeries
  intro u
  have hlt : r - 1 < r := by omega
  have hlt_enat : ((r - 1 : ℕ) : WithTop ENat) < (r : WithTop ENat) := by
    exact_mod_cast hlt
  have hcanonical := (hseries.fderiv (r - 1) hlt_enat u).fderiv
  have hgiven := (hderiv u).fderiv
  have hcurry : (a u).curryLeft =
      ((ftaylorSeries ℝ ζ u) ((r - 1) + 1)).curryLeft :=
    hgiven.symm.trans hcanonical
  exact (continuousMultilinearCurryLeftEquiv ℝ
    (fun _ : Fin (r - 1 + 1) ↦ ℝ) X).injective hcurry

/-- Infrastructure C: a continuous top section satisfying the predecessor
derivative equation both gives the next smoothness order and identifies the
section with the next iterated derivative. -/
theorem contDiff_succ_and_topSection_eq_iteratedFDeriv
    {r : ℕ} {ζ : ℝ → X}
    (hr : 1 ≤ r)
    (hprev : ContDiff ℝ (r - 1) ζ)
    (a : ℝ → (ℝ [×(r - 1 + 1)]→L[ℝ] X))
    (ha : Continuous a)
    (hderiv : ∀ u, HasFDerivAt
      (fun y ↦ (ftaylorSeries ℝ ζ y) (r - 1))
      ((a u).curryLeft) u) :
    ContDiff ℝ r ζ ∧ ∀ u, a u = iteratedFDeriv ℝ (r - 1 + 1) ζ u := by
  constructor
  · exact contDiff_succ_of_holonomic_topSection hr hprev a ha hderiv
  · exact topSection_eq_iteratedFDeriv_of_derivative hr hprev a ha hderiv

end LocalCutoff.GraphTransform
