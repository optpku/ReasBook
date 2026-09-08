module

public import DFPWolfe.A_uniformly_convex_counterexample_to_global_convergence_of_DFP_under_weak_Wolfe_.Lemma_3_15_Existence_of_a_local_C_7_invariant_slow_curve

open Filter
open scoped Topology

/- Lemma (Blown-up map and invariant slow curve) (1): the signed two-leg state
map is real analytic at `(0, 2, 1)`. -/
#check (DFP.TwoLeg.stateMapAnalytic :
  AnalyticAt ℝ DFP.TwoLeg.stateMap ((0, 2, 1) : ℝ × ℝ × ℝ))

/- Lemma (Blown-up map and invariant slow curve) (2): near `(0, 2, 1)`, the
analytic extension agrees with the recovered exact state on the positive-scale
branch. -/
#check (DFP.TwoLeg.stateMap_eventuallyEq_recovered :
  ∀ᶠ x in 𝓝 ((0, 2, 1) : ℝ × ℝ × ℝ), 0 < x.1 →
    DFP.TwoLeg.stateMap x =
      (Real.sqrt (DFP.SecondLeg.recovered x.1 x.2.1 x.2.2).1,
        (DFP.SecondLeg.recovered x.1 x.2.1 x.2.2).2,
        (DFP.SecondLeg.eigenvalues x.1 x.2.1 x.2.2).2))

/- Lemma (Blown-up map and invariant slow curve) (3): the derivative at
`(0, 2, 1)` has the displayed triangular coordinate action. -/
#check (DFP.TwoLeg.stateMap_fderiv_apply :
  ∀ v : ℝ × ℝ × ℝ,
    fderiv ℝ DFP.TwoLeg.stateMap ((0, 2, 1) : ℝ × ℝ × ℝ) v =
      (v.1, (-(1 : ℝ) / 9) * v.2.1 + ((2 : ℝ) / 3) * v.2.2, 0))

/- Lemma (Blown-up map and invariant slow curve) (4): the derivative at
`(0, 2, 1)` has center eigenvalue `1`. -/
#check (DFP.TwoLeg.stateMap_centerEigenvalue :
  Module.End.HasEigenvalue
    (fderiv ℝ DFP.TwoLeg.stateMap
      ((0, 2, 1) : ℝ × ℝ × ℝ)).toLinearMap (1 : ℝ))

/- Lemma (Blown-up map and invariant slow curve) (5): the derivative at
`(0, 2, 1)` has transverse eigenvalue `-1 / 9`. -/
#check (DFP.TwoLeg.stateMap_transverseEigenvalue_negNinth :
  Module.End.HasEigenvalue
    (fderiv ℝ DFP.TwoLeg.stateMap
      ((0, 2, 1) : ℝ × ℝ × ℝ)).toLinearMap (-(1 : ℝ) / 9))

/- Lemma (Blown-up map and invariant slow curve) (6): the derivative at
`(0, 2, 1)` has transverse eigenvalue `0`. -/
#check (DFP.TwoLeg.stateMap_transverseEigenvalue_zero :
  Module.End.HasEigenvalue
    (fderiv ℝ DFP.TwoLeg.stateMap
      ((0, 2, 1) : ℝ × ℝ × ℝ)).toLinearMap (0 : ℝ))

/- Lemma (Blown-up map and invariant slow curve) (7): there is one locally
forward-invariant `C^7` graph with shared functions `p` and `h`, the displayed
jets for `p` and `h`, and the displayed parabolic recurrence for `ε`. -/
#check (DFP.TwoLeg.exists_localForwardInvariantSlowCurve :
  ∃ p h : ℝ → ℝ,
    ContDiffAt ℝ 7 (fun ε ↦ (p ε, h ε)) 0 ∧
      (p 0, h 0) = (2, 1) ∧
        HasFDerivAt (fun ε ↦ (p ε, h ε)) (0 : ℝ →L[ℝ] (ℝ × ℝ)) 0 ∧
          (fun ε ↦ DFP.TwoLeg.stateMap (ε, p ε, h ε)) =ᶠ[𝓝 0]
            (fun ε ↦
              let ε' := (DFP.TwoLeg.stateMap (ε, p ε, h ε)).1
              (ε', p ε', h ε')) ∧
            (fun ε : ℝ ↦
              p ε - (2 + (198 / 5) * ε ^ 3 - (9 / 5) * ε ^ 4)) =O[𝓝 0]
              (fun ε : ℝ ↦ ε ^ 5) ∧
              (fun ε : ℝ ↦ h ε - (1 + 8 * ε ^ 3)) =O[𝓝 0]
                (fun ε : ℝ ↦ ε ^ 5) ∧
                (fun ε : ℝ ↦
                  (DFP.TwoLeg.stateMap (ε, p ε, h ε)).1 -
                    (ε - (3 / 2) * ε ^ 4 + (5 / 4) * ε ^ 5)) =O[𝓝 0]
                  (fun ε : ℝ ↦ ε ^ 6))
