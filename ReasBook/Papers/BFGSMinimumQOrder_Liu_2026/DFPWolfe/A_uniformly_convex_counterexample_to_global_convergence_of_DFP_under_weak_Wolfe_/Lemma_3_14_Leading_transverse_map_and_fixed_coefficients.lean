/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Upstream attribution: https://github.com/imathwy/DFP_wolfe_local/blob/e308927f5b7930bdd002f0c0e42b9d112ad821cb/README.md (formalization author).
Upstream source: https://github.com/imathwy/DFP_wolfe_local/blob/e308927f5b7930bdd002f0c0e42b9d112ad821cb/DFPWolfe/A_uniformly_convex_counterexample_to_global_convergence_of_DFP_under_weak_Wolfe_/Lemma_3_14_Leading_transverse_map_and_fixed_coefficients.lean
-/

module

public import ReasLib.Optimization.DFP.TwoPhaseControls.MixedExpansion.LeadingTransverse

public section

noncomputable section

open Filter
open scoped Topology

/- Lemma 3.14 (Leading transverse map and fixed coefficients) (1): after
normalization by `ε ^ 3`, the exact transverse increment along `b = ε` and
`r = ε ^ 2` is asymptotic to the stated affine coefficient map. -/
#check (DFP.TwoLeg.Mixed.transverseIncrement_asymptotic :
  ∀ (P J : ℝ),
    (fun ε ↦
      (ε ^ 3)⁻¹ •
          (let y := DFP.TwoLeg.Mixed.map ε
              (DFP.TwoLeg.Mixed.input (ε, P, J) (ε ^ 2));
            (y.2.1 - 2, y.2.2 - 1)) -
        (((6 * J - P + 348) / 9, 8) : ℝ × ℝ))
      =o[𝓝[≠] 0] (fun _ ↦ (1 : ℝ)))

/- Lemma 3.14 (Leading transverse map and fixed coefficients) (2): the linear
part of the affine transverse map has matrix rows `(-1 / 9, 2 / 3)` and `(0, 0)`. -/
#check (DFP.TwoLeg.Mixed.leadingTransverse_fderiv_apply :
  ∀ (z v : ℝ × ℝ),
    fderiv ℝ DFP.TwoLeg.Mixed.leadingTransverse z v =
      ((-(1 : ℝ) / 9) * v.1 + ((2 : ℝ) / 3) * v.2, 0))

/- Lemma 3.14 (Leading transverse map and fixed coefficients) (3): the
coefficient pair `(198 / 5, 8)` is fixed by the affine leading transverse map. -/
#check (DFP.TwoLeg.Mixed.leadingTransverse_fixedCoefficient :
  DFP.TwoLeg.Mixed.leadingTransverse ((198 / 5 : ℝ), 8) =
    ((198 / 5 : ℝ), 8))
