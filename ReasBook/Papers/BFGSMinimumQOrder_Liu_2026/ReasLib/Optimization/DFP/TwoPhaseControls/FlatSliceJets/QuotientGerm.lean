module

public import ReasLib.Optimization.DFP.TwoPhaseControls.FlatSliceJets.GermCongruence
import all ReasLib.Optimization.DFP.TwoPhaseControls.FlatSliceJets.GermCongruence

/-!
# Quotient algebra for finite-order scalar germs

This companion exposes the quotient-approximation argument used repeatedly by the
explicit DFP jet computations.  Keeping it public lets later coordinate expansions
share the same denominator bookkeeping.
-/

public section

noncomputable section

open Filter
open scoped Topology

namespace DFP.TwoLeg.EqModPow

/-- Pointwise equality gives a germ congruence of every order. -/
theorem of_eq (n : ℕ) {f g : ℝ → ℝ} (h : ∀ ε, f ε = g ε) :
    DFP.TwoLeg.EqModPow n f g := by
  exact congr (refl n f) (fun _ => rfl) (fun ε => (h ε).symm)

/-- Replace numerator and denominator by congruent germs, then verify a proposed
quotient by multiplication with the approximate denominator. -/
theorem div_approx {n : ℕ} {num den numP denP q : ℝ → ℝ}
    (hnum : DFP.TwoLeg.EqModPow n num numP)
    (hden : DFP.TwoLeg.EqModPow n den denP)
    (hpoly : DFP.TwoLeg.EqModPow n numP (fun ε => denP ε * q ε))
    (hdenP : ContinuousAt denP 0) (hq : ContinuousAt q 0)
    (hdenCont : ContinuousAt den 0) (hden0 : den 0 ≠ 0) :
    DFP.TwoLeg.EqModPow n (fun ε => num ε / den ε) q := by
  have hdenMul : DFP.TwoLeg.EqModPow n (fun ε => den ε * q ε)
      (fun ε => denP ε * q ε) :=
    hden.mul (refl n q) hdenP hq
  exact div_of_eq_mul (hnum.trans (hpoly.trans hdenMul.symm)) hdenCont hden0

end DFP.TwoLeg.EqModPow
