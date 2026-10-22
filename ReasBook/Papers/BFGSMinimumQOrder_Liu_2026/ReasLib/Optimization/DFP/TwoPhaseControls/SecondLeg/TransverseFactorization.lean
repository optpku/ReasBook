/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Upstream attribution: https://github.com/imathwy/DFP_wolfe_local/blob/e308927f5b7930bdd002f0c0e42b9d112ad821cb/README.md (formalization author).
Upstream source: https://github.com/imathwy/DFP_wolfe_local/blob/e308927f5b7930bdd002f0c0e42b9d112ad821cb/ReasLib/Optimization/DFP/TwoPhaseControls/SecondLeg/TransverseFactorization.lean
-/

module

public import ReasLib.Optimization.DFP.TwoPhaseControls.SecondLeg.TransverseDerivative
public import ReasLib.Optimization.DFP.TwoPhaseControls.SecondLeg

public section

open Filter
open scoped Topology

namespace DFP.SecondLeg

/-- Lemma 4.15 companion for `lowGradientFactorTransverseFDeriv_norm_bound`: an explicit
cubic factorization with a continuous quotient is sufficient for the required local norm bound. -/
theorem lowGradientFactorTransverseFDeriv_norm_bound_of_factorization
    {A : ℝ × (ℝ × ℝ) → (ℝ × ℝ) →L[ℝ] ℝ}
    (hfactor : ∀ᶠ x in 𝓝 ((0, 2, 1) : ℝ × ℝ × ℝ),
      fderiv ℝ (fun z : ℝ × ℝ ↦
        (gradientFactors x.1 z.1 z.2).1) (x.2.1, x.2.2) =
        x.1 ^ (3 : ℕ) • A x)
    (hA : ContinuousAt A ((0, 2, 1) : ℝ × ℝ × ℝ)) :
    ∃ C > 0, ∀ᶠ x in 𝓝 ((0, 2, 1) : ℝ × ℝ × ℝ),
      ‖fderiv ℝ (fun z : ℝ × ℝ ↦
        (gradientFactors x.1 z.1 z.2).1) (x.2.1, x.2.2)‖ ≤
        C * ‖x.1 ^ (3 : ℕ)‖ := by
  apply eventually_transverse_fderiv_norm_le_of_cubic_factorization
    (g := fun ε z ↦ (gradientFactors ε z.1 z.2).1) (A := A)
    (x₀ := ((0, 2, 1) : ℝ × ℝ × ℝ))
  · exact hfactor
  · exact hA

end DFP.SecondLeg
