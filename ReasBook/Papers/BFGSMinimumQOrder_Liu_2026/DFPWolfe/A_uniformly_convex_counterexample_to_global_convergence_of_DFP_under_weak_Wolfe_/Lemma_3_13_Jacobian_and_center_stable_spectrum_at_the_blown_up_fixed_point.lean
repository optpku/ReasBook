module

public import ReasLib.Optimization.DFP.TwoPhaseControls.StateMap.Linearization

public section

/- Lemma 3.13 (Jacobian and center/stable spectrum at the blown-up fixed point) (1):
the derivative of the extended map at `(0, 2, 1)` has the stated action. -/
#check (DFP.TwoLeg.stateMap_fderiv_apply :
  ∀ v : ℝ × ℝ × ℝ,
    fderiv ℝ DFP.TwoLeg.stateMap ((0, 2, 1) : ℝ × ℝ × ℝ) v =
      (v.1, (-(1 : ℝ) / 9) * v.2.1 + ((2 : ℝ) / 3) * v.2.2, 0))

/- Lemma 3.13 (Jacobian and center/stable spectrum at the blown-up fixed point) (2):
the derivative at `(0, 2, 1)` has center eigenvalue `1`. -/
#check (DFP.TwoLeg.stateMap_centerEigenvalue :
  Module.End.HasEigenvalue
    (fderiv ℝ DFP.TwoLeg.stateMap
      ((0, 2, 1) : ℝ × ℝ × ℝ)).toLinearMap (1 : ℝ))

/- Lemma 3.13 (Jacobian and center/stable spectrum at the blown-up fixed point) (3):
the derivative at `(0, 2, 1)` has transverse eigenvalue `-1 / 9`. -/
#check (DFP.TwoLeg.stateMap_transverseEigenvalue_negNinth :
  Module.End.HasEigenvalue
    (fderiv ℝ DFP.TwoLeg.stateMap
      ((0, 2, 1) : ℝ × ℝ × ℝ)).toLinearMap (-(1 : ℝ) / 9))

/- Lemma 3.13 (Jacobian and center/stable spectrum at the blown-up fixed point) (4):
the derivative at `(0, 2, 1)` has transverse eigenvalue `0`. -/
#check (DFP.TwoLeg.stateMap_transverseEigenvalue_zero :
  Module.End.HasEigenvalue
    (fderiv ℝ DFP.TwoLeg.stateMap
      ((0, 2, 1) : ℝ × ℝ × ℝ)).toLinearMap (0 : ℝ))
