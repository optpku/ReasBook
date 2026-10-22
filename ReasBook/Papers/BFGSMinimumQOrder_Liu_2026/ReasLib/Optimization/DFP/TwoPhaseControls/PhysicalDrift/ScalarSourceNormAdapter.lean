/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Upstream attribution: https://github.com/imathwy/DFP_wolfe_local/blob/e308927f5b7930bdd002f0c0e42b9d112ad821cb/README.md (formalization author).
Upstream source: https://github.com/imathwy/DFP_wolfe_local/blob/e308927f5b7930bdd002f0c0e42b9d112ad821cb/ReasLib/Optimization/DFP/TwoPhaseControls/PhysicalDrift/ScalarSourceNormAdapter.lean
-/

module

public import ReasLib.Optimization.DFP.TwoPhaseControls.PhysicalDrift.AngleQuadraticTransport

public section

universe u

namespace DFP.TwoLeg.Mixed

/-- Infrastructure for Appendix Lemma A.6: on a scalar source, the norm of a
continuous multilinear-map difference is attained at the all-ones vector. -/
theorem ContinuousMultilinearMap.norm_sub_eq_norm_apply_one
    {r : ℕ} {X : Type u} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (A B : (ℝ [×r]→L[ℝ] X)) :
    ‖A - B‖ = ‖(A - B) (fun _ : Fin r ↦ (1 : ℝ))‖ := by
  calc
    ‖A - B‖ = ‖(ContinuousMultilinearMap.piFieldEquiv ℝ (Fin r) X).symm
        (A - B)‖ := by
      rw [LinearIsometryEquiv.norm_map]
    _ = ‖(A - B) (fun _ : Fin r ↦ (1 : ℝ))‖ := by
      congr 1

/-- Infrastructure for Appendix Lemma A.6: the all-ones evaluation of a scalar
source map difference is unchanged by replacing the map with its pi-field image. -/
theorem ContinuousMultilinearMap.piFieldEquiv_apply_one
    {r : ℕ} {X : Type u} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (z : X) :
    (ContinuousMultilinearMap.piFieldEquiv ℝ (Fin r) X z)
        (fun _ : Fin r ↦ (1 : ℝ)) = z := by
  exact (ContinuousMultilinearMap.piFieldEquiv ℝ (Fin r) X).symm_apply_apply z

end DFP.TwoLeg.Mixed
