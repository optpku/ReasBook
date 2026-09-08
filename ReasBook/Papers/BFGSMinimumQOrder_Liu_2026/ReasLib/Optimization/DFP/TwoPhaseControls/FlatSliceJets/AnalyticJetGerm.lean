module

public import ReasLib.Optimization.DFP.TwoPhaseControls.FlatSliceJets.GermCongruence
public import ReasLib.Analysis.Calculus.FiniteTaylorJet.PeanoComparison
public import Mathlib.Analysis.Analytic.IteratedFDeriv

public section

noncomputable section

open Filter
open scoped Topology

namespace DFP.TwoLeg.EqModPow

/-- Analytic functions with equal order-`m` finite Taylor jets agree modulo
`O(ε^(m+1))`. -/
theorem of_analytic_jet_eq {m : ℕ} {f g : ℝ → ℝ}
    (hf : AnalyticAt ℝ f 0) (hg : AnalyticAt ℝ g 0)
    (hjet : FiniteTaylorJet.ofFunction ℝ m f 0 =
      FiniteTaylorJet.ofFunction ℝ m g 0) :
    EqModPow (m + 1) f g := by
  let h : ℝ → ℝ := fun x => f x - g x
  have hh : AnalyticAt ℝ h 0 := hf.sub hg
  obtain ⟨p, hpAt⟩ := hh
  have hrem := hpAt.isBigO_sub_partialSum_pow (m + 1)
  obtain ⟨r, hp⟩ := hpAt
  have hderiv (n : Fin (m + 1)) : iteratedDeriv (n : ℕ) h 0 = 0 := by
    have hfg :=
      (FiniteTaylorJet.ofFunction_eq_iff_iteratedDeriv_eq m f g 0 0).mp hjet n
    change iteratedDeriv (n : ℕ) (f - g) 0 = 0
    rw [iteratedDeriv_sub hf.contDiffAt hg.contDiffAt, hfg, sub_self]
  have hpartial (x : ℝ) : p.partialSum (m + 1) x = 0 := by
    rw [FormalMultilinearSeries.partialSum]
    apply Finset.sum_eq_zero
    intro n hn
    have hnlt : n < m + 1 := Finset.mem_range.mp hn
    let nf : Fin (m + 1) := ⟨n, hnlt⟩
    have happ : iteratedFDeriv ℝ n h 0 (fun _ => x) = 0 := by
      rw [iteratedFDeriv_apply_eq_iteratedDeriv_mul_prod, hderiv nf]
      simp
    have hz : (Nat.factorial n : ℕ) • p n (fun _ => x) = 0 :=
      (hp.factorial_smul x n).trans happ
    have hfac : (n.factorial : ℝ) ≠ 0 := by positivity
    exact (mul_eq_zero.mp (by simpa [nsmul_eq_mul] using hz)).resolve_left hfac
  apply EqModPow.of_isBigO
  apply Asymptotics.isBigO_norm_right.mp
  simpa only [zero_add, h, hpartial, sub_zero, norm_pow] using hrem

end DFP.TwoLeg.EqModPow
