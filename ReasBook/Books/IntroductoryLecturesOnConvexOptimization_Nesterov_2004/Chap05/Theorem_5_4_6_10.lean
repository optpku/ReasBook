/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Definition_5_1_1
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Theorem_5_4_6_7
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Theorem_5_4_6_8
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Theorem_5_4_6_9

-- Declarations for this item will be appended below by the statement pipeline.

open ProperCone
open scoped Gradient HessianLocalNorm

noncomputable section

universe u v w

variable {E₁ : Type u} {E₂ : Type v} {E₃ : Type w}
  [NormedAddCommGroup E₁] [InnerProductSpace ℝ E₁] [CompleteSpace E₁]
  [NormedAddCommGroup E₂] [InnerProductSpace ℝ E₂] [CompleteSpace E₂]
  [NormedAddCommGroup E₃] [NormedSpace ℝ E₃]
  [InnerProductSpace ℝ (E₂ × E₃)] [CompleteSpace (E₂ × E₃)]

/- Theorem 5.4.6.10 lies in the subsection's third-directional-derivative / sigma-bound domain.

Sampled owner declarations:
* `compositionPotential_thirdDirectionalDerivative_eq` from `Theorem_5_4_6_7`, the source-facing
  decomposition `(5.4.25)`;
* `compositionPotential_crossTerm_le_sqrt_sigmaOne_mul_sigmaTwo` from `Theorem_5_4_6_8`, the
  owner-level cross-term estimate;
* `yGradient_pairing_vectorThirdDirectionalDerivative_le_of_betaCompatibility` from
  `Theorem_5_4_6_9`, the owner-level `β`-compatibility bound;
* `IsStandardSelfConcordantOn` from `Definition_5_1_1`, the chapter owner for the standard
  self-concordance hypothesis appearing in this item;
* `IsSelfConcordantOnWith.third_deriv_bound` and
  `IsSelfConcordantOnWith.hessian_isPositive` from `Definition_5_1_1`, the canonical
  quantitative self-concordance API recovered internally from that standard owner.

Source/core/bridge triage:
* source-facing: the textbook upper bound for the third directional derivative of the composition
  potential;
* core/canonical: the upstream theorems `Theorem_5_4_6_7`, `Theorem_5_4_6_8`, `Theorem_5_4_6_9`,
  and the standard self-concordance owner `IsStandardSelfConcordantOn`;
* bridge/view: the internal quantitative view `IsSelfConcordantOnWith dom 1 Φ` together with the
  source-facing scalars `compositionPotentialSigmaOne`, `compositionPotentialSigmaTwo`, and
  `sigmaThree`.

Primitive data:
* `F`, `Φ`, `ξ`, `β`, `x`, `z`, `d`;
* `ContDiffAt ℝ 3 ξ x`;
* the standard self-concordance owner `IsStandardSelfConcordantOn dom Φ`;
* the specialized local-norm estimate for the lifted derivative direction;
* the `β`-compatibility owner and the dual-cone hypothesis on `-∇ᵧ Φ(ξ(x), z)`.

Derived API:
* the final sigma-bound for the third directional derivative of the composition potential.

The public theorem should therefore be stated directly in terms of those owner-level inputs,
rather than exposing the intermediate outputs `hΔ₃`, `hCross`, `hBeta`, and the isolated
third-derivative estimate as primitive hypotheses. -/

-- Proof sketch: rewrite the third directional derivative using the decomposition into the third
-- derivative term of `Φ`, the mixed Hessian term, and the `y`-gradient pairing with
-- `D³ξ(x)[d, d, d]` using `Theorem_5_4_6_7`. Bound these three summands respectively by the
-- self-concordance owner API for `Φ`, `Theorem_5_4_6_8`, and `Theorem_5_4_6_9`, then add the
-- resulting inequalities.
/-- Theorem 5.4.6.10: if `ξ` is `C³` at `x`, if `Φ` is standard self-concordant on a domain
containing `(ξ(x), z)`, if the negative lifted derivative direction satisfies the specialized
local-norm estimate used in Theorem 5.4.6.8, and if `ξ` is `β`-compatible with the dual-cone
sign condition from Theorem 5.4.6.9, then the third directional derivative of
`x' ↦ Φ(ξ(x'), z)` is bounded above by
`2 σ₁^(3/2) + 3 σ₁^(1/2) σ₂ + 3 β σ₂ σ₃^(1/2)`, where
`σ₁ = compositionPotentialSigmaOne Φ ξ x z d`,
`σ₂ = compositionPotentialSigmaTwo Φ ξ x z d`, and
`σ₃ = sigmaThree F x d`. -/
theorem compositionPotential_thirdDirectionalDerivative_le_selfConcordant_sigma_bound
    {dom : Set (E₂ × E₃)} {Q₁ : Set E₁} {K : ConvexCone ℝ E₂}
    {F : E₁ → ℝ} {Φ : E₂ × E₃ → ℝ} {ξ : E₁ → E₂} {β : NNReal} {x d : E₁} {z : E₃}
    (hξ : ContDiffAt ℝ 3 ξ x)
    (hΦ_self : IsStandardSelfConcordantOn dom Φ)
    (hyz : (ξ x, z) ∈ dom)
    (hneg_liftedDirectionDerivative_le_sigmaTwo :
      ‖-compositionSecondLiftedDirectionDerivative ξ x d‖[Φ; (ξ x, z)] ≤
        compositionPotentialSigmaTwo Φ ξ x z d)
    (hξ_compat : IsBetaCompatibleWith Q₁ K F β ξ)
    (hx : x ∈ interior Q₁)
    (hneg_yGradient_mem_innerDual :
      -∇ (fun y : E₂ ↦ Φ (y, z)) (ξ x) ∈ innerDual (K : Set E₂)) :
    thirdDirectionalDerivative (fun x' : E₁ ↦ compositionPotential Φ ξ (x', z)) x d ≤
      2 * (Real.sqrt (compositionPotentialSigmaOne Φ ξ x z d)) ^ (3 : ℕ) +
        3 * Real.sqrt (compositionPotentialSigmaOne Φ ξ x z d) *
          compositionPotentialSigmaTwo Φ ξ x z d +
        3 * (β : ℝ) * compositionPotentialSigmaTwo Φ ξ x z d *
          Real.sqrt (sigmaThree F x d) := by
  let _ : NormedSpace ℝ (E₂ × E₃) := InnerProductSpace.toNormedSpace
  let l : E₂ × E₃ := (fderiv ℝ ξ x d, 0)
  have hΦ : ContDiffAt ℝ 3 Φ (ξ x, z) :=
    hΦ_self.contDiffOn.contDiffAt (hΦ_self.isOpen_domain.mem_nhds hyz)
  have hThirdDecomp :
      thirdDirectionalDerivative (fun x' : E₁ ↦ compositionPotential Φ ξ (x', z)) x d =
        thirdDirectionalDerivative Φ (ξ x, z) l +
          (3 : ℝ) * inner ℝ (hessian Φ (ξ x, z) l)
            (compositionSecondLiftedDirectionDerivative ξ x d) +
          inner ℝ (∇ (fun y : E₂ ↦ Φ (y, z)) (ξ x))
            (vectorThirdDirectionalDerivative ξ x d) := by
    simpa [l] using compositionPotential_thirdDirectionalDerivative_eq hξ hΦ
  have hThirdAbs :
      |thirdDirectionalDerivative Φ (ξ x, z) l| ≤
        2 * (Real.sqrt (compositionPotentialSigmaOne Φ ξ x z d)) ^ (3 : ℕ) := by
    simpa [compositionPotentialSigmaOne_def, hessianLocalNorm_def] using
      hΦ_self.third_deriv_bound hyz l
  have hThird :
      thirdDirectionalDerivative Φ (ξ x, z) l ≤
        2 * (Real.sqrt (compositionPotentialSigmaOne Φ ξ x z d)) ^ (3 : ℕ) :=
    le_trans (le_abs_self _) hThirdAbs
  have hH : (hessian Φ (ξ x, z)).IsPositive :=
    hΦ_self.hessian_isPositive hyz
  have hCrossBound :
      inner ℝ (hessian Φ (ξ x, z) l) (compositionSecondLiftedDirectionDerivative ξ x d) ≤
        Real.sqrt (compositionPotentialSigmaOne Φ ξ x z d) *
          compositionPotentialSigmaTwo Φ ξ x z d := by
    simpa using
      compositionPotential_crossTerm_le_sqrt_sigmaOne_mul_sigmaTwo hH
        hneg_liftedDirectionDerivative_le_sigmaTwo
  have hBetaBound :
      inner ℝ (∇ (fun y : E₂ ↦ Φ (y, z)) (ξ x))
          (vectorThirdDirectionalDerivative ξ x d) ≤
        3 * (β : ℝ) * compositionPotentialSigmaTwo Φ ξ x z d *
          Real.sqrt (sigmaThree F x d) :=
    yGradient_pairing_vectorThirdDirectionalDerivative_le_of_betaCompatibility hξ_compat hx
      hneg_yGradient_mem_innerDual
  rw [hThirdDecomp]
  linarith [hThird, hCrossBound, hBetaBound]

end
