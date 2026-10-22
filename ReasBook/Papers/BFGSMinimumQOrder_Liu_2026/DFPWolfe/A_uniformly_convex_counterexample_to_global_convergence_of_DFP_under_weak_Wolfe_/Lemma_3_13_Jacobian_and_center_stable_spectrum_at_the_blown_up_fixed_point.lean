/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Upstream attribution: https://github.com/imathwy/DFP_wolfe_local/blob/e308927f5b7930bdd002f0c0e42b9d112ad821cb/README.md (formalization author).
Upstream source: https://github.com/imathwy/DFP_wolfe_local/blob/e308927f5b7930bdd002f0c0e42b9d112ad821cb/DFPWolfe/A_uniformly_convex_counterexample_to_global_convergence_of_DFP_under_weak_Wolfe_/Lemma_3_13_Jacobian_and_center_stable_spectrum_at_the_blown_up_fixed_point.lean
-/

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
