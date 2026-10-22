/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Upstream attribution: https://github.com/imathwy/DFP_wolfe_local/blob/e308927f5b7930bdd002f0c0e42b9d112ad821cb/README.md (formalization author).
Upstream source: https://github.com/imathwy/DFP_wolfe_local/blob/e308927f5b7930bdd002f0c0e42b9d112ad821cb/DFPWolfe/A_uniformly_convex_counterexample_to_global_convergence_of_DFP_under_weak_Wolfe_/Lemma_6_4_Exact_weak_curvature_identity_and_c_2_3_4.lean
-/

module

public import ReasLib.Optimization.DFP.TwoPhaseOrbit.Wolfe

public section

open scoped Matrix

variable (orbit : DFP.TwoPhaseOrbit)
  (h_exact : ∀ j, DFP.TwoPhaseOrbit.State.ExactCycle (orbit.state j))
  (j : ℕ) (i : Fin 2) (k : ℕ)

/- Lemma 6.4 (Exact weak-curvature identity and $c_2=3/4$) -/
#check
  (DFP.AbstractSecantStep.nextGradient_pairing_eq_add_secantCurvature
      ((h_exact j).step i) :
    ((h_exact j).step i).nextGradient ⬝ᵥ ((h_exact j).step i).displacement =
      ((h_exact j).step i).gradient ⬝ᵥ ((h_exact j).step i).displacement +
        ((h_exact j).step i).displacement ⬝ᵥ ((h_exact j).step i).gradientChange)

#check
  (DFP.AbstractSecantStep.nextGradient_pairing_eq
      ((h_exact j).step i) :
    ((h_exact j).step i).nextGradient ⬝ᵥ ((h_exact j).step i).displacement =
      -(1 - ((h_exact j).step i).tau) * ((h_exact j).step i).predictedDecrease)

#check
  (DFP.TwoPhaseOrbit.State.ExactCycle.step_tau_mem (h_exact j) i :
    ((h_exact j).step i).tau = 2 / 3 ∨ ((h_exact j).step i).tau = 1 / 3)

#check
  (DFP.TwoPhaseOrbit.State.ExactCycle.step_weakCurvature (h_exact j) i :
    LineSearch.Wolfe.IsWeakCurvature (3 / 4 : ℝ)
      ((h_exact j).step i).slope ((h_exact j).step i).nextSlope)

/- Lemma 6.4, transported to the flattened physical endpoint sequence. -/
#check
  (DFP.TwoPhaseOrbit.endpointCurvatureCertificates orbit h_exact k :
    let d := orbit.endpoint (k + 1) - orbit.endpoint k
    LineSearch.Wolfe.IsWeakCurvature (3 / 4 : ℝ)
        (inner ℝ (orbit.endpointGradient k) d)
        (inner ℝ (orbit.endpointGradient (k + 1)) d) ∧
      0 < inner ℝ
        (orbit.endpointGradient (k + 1) - orbit.endpointGradient k) d)

#check
  (DFP.TwoPhaseOrbit.endpointWeakCurvature orbit h_exact k :
    let d := orbit.endpoint (k + 1) - orbit.endpoint k
    LineSearch.Wolfe.IsWeakCurvature (3 / 4 : ℝ)
      (inner ℝ (orbit.endpointGradient k) d)
      (inner ℝ (orbit.endpointGradient (k + 1)) d))

#check
  (DFP.TwoPhaseOrbit.endpointSecantCurvature_pos orbit h_exact k :
    let d := orbit.endpoint (k + 1) - orbit.endpoint k
    0 < inner ℝ
      (orbit.endpointGradient (k + 1) - orbit.endpointGradient k) d)
