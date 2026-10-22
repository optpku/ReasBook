/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Upstream attribution: https://github.com/imathwy/DFP_wolfe_local/blob/e308927f5b7930bdd002f0c0e42b9d112ad821cb/README.md (formalization author).
Upstream source: https://github.com/imathwy/DFP_wolfe_local/blob/e308927f5b7930bdd002f0c0e42b9d112ad821cb/DFPWolfe/A_uniformly_convex_counterexample_to_global_convergence_of_DFP_under_weak_Wolfe_/Appendix_Lemma_A_2_Determinant_identity_for_the_one_step_map.lean
-/

module

public import ReasLib.Optimization.DFP.InverseUpdate.Determinant

open scoped Matrix

universe u

/- Appendix Lemma A.2 (Determinant identity for the one-step map): the exact
inverse-form DFP update satisfies `det H₊ = det H * ((s ⬝ᵥ y) / (y ⬝ᵥ (H *ᵥ y)))`. -/
#check (Matrix.det_inverseDFPUpdate :
  ∀ {n : Type u} [Fintype n] [DecidableEq n] {H : Matrix n n ℝ} {s y : n → ℝ},
    H.PosDef → 0 < s ⬝ᵥ y →
      (Matrix.inverseDFPUpdate H s y).det =
        H.det * ((s ⬝ᵥ y) / (y ⬝ᵥ (H *ᵥ y))))
