/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import OptimizationTheoryAndMethods_SunYuan_2006.Chap05.Definition_5_4_extra_1
import OptimizationTheoryAndMethods_SunYuan_2006.Chap05.Corollary_5_4_11
import OptimizationTheoryAndMethods_SunYuan_2006.Chap05.Theorem_5_4_10
import OptimizationTheoryAndMethods_SunYuan_2006.Chap05.Theorem_5_4_3

noncomputable section

open Filter

section Chapter05Corollary5412

variable {n : ℕ}

local notation "Point" => EuclideanSpace ℝ (Fin n)
local notation "Operator" => Point →L[ℝ] Point

-- Domain sampling:
-- * primary domain: inverse-Jacobian-side quasi-Newton local convergence and `Q`-superlinear
--   rates;
-- * core/canonical owners inspected: `HasQuasiNewtonLocalConvergenceAssumptions` from
--   `Assumption_5_4_1`, `InverseJacobianQuasiNewtonSmallStartConvergence` and
--   `InverseJacobianQuasiNewtonIteration` from `Theorem_5_4_10`, and
--   `HasQSuperlinearConvergenceTo`, together with the reusable Chapter 5 subsequence owner
--   `HasSubsequenceTendstoTo`;
-- * layer choice: this corollary is a source-facing bridge statement. The vanishing-subsequence
--   hypothesis is expressed through `HasSubsequenceTendstoTo` applied to the inverse-error norm
--   sequence, while the ambient local-convergence assumptions and
--   inverse small-start owner are expressed through the chapter owners above.

namespace InverseJacobianQuasiNewtonSmallStartConvergence

/-- Helper for Chapter05 Corollary 5.4.12: under the inverse-side update hypotheses from
Theorem 5.4.10, any source-facing inverse run with invertible initial inverse approximation and
with a vanishing subsequence of inverse-approximation errors converges to `hF.xStar`
`Q`-superlinearly. -/
theorem qSuperlinear_of_vanishingInverseErrorSubsequence
    {D : Set Point} {F : Point → Point}
    (hF : HasQuasiNewtonLocalConvergenceAssumptions D F)
    {domU : Set (Point × Operator)}
    {U : JacobianUpdateFunction Point}
    {x0 : Point} {H0 : Operator}
    (h_update :
      (∃ γ : ℝ,
        SatisfiesInverseAdditiveLocalUpdateBound U F hF.xStar hF.referenceInverse domU γ) ∨
      ∃ α₁ α₂ : ℝ,
        SatisfiesInverseSigmaLocalUpdateBound U F hF.xStar hF.referenceInverse domU α₁ α₂)
    (hsmall :
      InverseJacobianQuasiNewtonSmallStartConvergence D F domU U hF.xStar x0 H0)
    (hH0inv : H0.IsInvertible)
    (A : InverseJacobianQuasiNewtonIteration D F domU U x0 H0)
    (h_vanishing :
      HasSubsequenceTendstoTo (fun k ↦ ‖A.H k - hF.referenceInverse‖) 0) :
    HasQSuperlinearConvergenceTo A.x hF.xStar := by
  let e : ℕ → ℝ := fun k ↦ ‖A.x k - hF.xStar‖
  let σ : ℕ → ℝ := fun k ↦ inverseQuasiNewtonSigma (A.x k) (A.x (k + 1)) hF.xStar
  let a : ℕ → ℝ := fun k ↦ ‖A.H k - hF.referenceInverse‖
  let DFstar : Operator := fderiv ℝ F hF.xStar
  have hlinear : LinearlyConvergesTo A.x hF.xStar := hsmall.linear A
  rcases linearlyConvergesTo_tendsto_and_summableErrorNorm hlinear with ⟨hx_tendsto, he_sum⟩
  have hσ_nonneg : ∀ k, 0 ≤ σ k := by
    intro k
    dsimp [σ]
    rw [inverseQuasiNewtonSigma]
    exact le_trans (norm_nonneg _) (le_max_left _ _)
  have hσ_le : ∀ k, σ k ≤ e k + e (k + 1) := by
    intro k
    dsimp [σ, e]
    rw [inverseQuasiNewtonSigma]
    refine max_le_iff.mpr ?_
    constructor
    · exact le_add_of_nonneg_right (norm_nonneg _)
    · exact le_add_of_nonneg_left (norm_nonneg _)
  have he_shift_sum : Summable (fun k ↦ e (k + 1)) := (summable_nat_add_iff 1).2 he_sum
  have hσ_sum : Summable σ := by
    refine Summable.of_nonneg_of_le hσ_nonneg hσ_le ?_
    exact he_sum.add he_shift_sum
  have ha_tendsto : Tendsto a atTop (nhds 0) := by
    rcases h_update with ⟨γu, hAdd⟩ | ⟨α1, α2, hSigma⟩
    · let γu0 : ℝ := max γu 0
      let v : ℕ → ℝ := fun k ↦ γu0 * σ k
      have ha_nonneg : ∀ k, 0 ≤ a k := by
        intro k
        dsimp [a]
        exact norm_nonneg _
      have hv_nonneg : ∀ k, 0 ≤ v k := by
        intro k
        dsimp [v, γu0]
        exact mul_nonneg (by simp) (hσ_nonneg k)
      have hv_sum : Summable v := by
        dsimp [v, γu0]
        exact hσ_sum.mul_left (max γu 0)
      have hrec : ∀ k, a (k + 1) ≤ a k + v k := by
        intro k
        have hraw := hAdd.2 (A.in_dom k) (A.update_mem k)
        have hsigma_sum : e (k + 1) + e k ≤ 2 * σ k := by
          have hcur : e k ≤ σ k := by
            dsimp [e, σ]
            rw [inverseQuasiNewtonSigma]
            exact le_max_left _ _
          have hnext : e (k + 1) ≤ σ k := by
            dsimp [e, σ]
            rw [inverseQuasiNewtonSigma]
            exact le_max_right _ _
          nlinarith [hcur, hnext, hσ_nonneg k]
        have hfactor : (γu / 2) * (e (k + 1) + e k) ≤ v k := by
          have hs_nonneg : 0 ≤ e (k + 1) + e k := by
            positivity
          have hγhalf : γu / 2 ≤ γu0 / 2 := by
            dsimp [γu0]
            nlinarith [le_max_left γu 0]
          calc
            (γu / 2) * (e (k + 1) + e k) ≤ (γu0 / 2) * (e (k + 1) + e k) := by
                  exact mul_le_mul_of_nonneg_right hγhalf hs_nonneg
            _ ≤ (γu0 / 2) * (2 * σ k) := by
                  exact mul_le_mul_of_nonneg_left hsigma_sum (by positivity)
            _ = v k := by
                  dsimp [v]
                  ring
        -- Route correction: keep the recurrence on `‖Hₖ - H*‖` itself, then apply the generic
        -- subsequence-control lemma from Corollary 5.4.11.
        calc
          a (k + 1) ≤ a k + (γu / 2) * (e (k + 1) + e k) := by
                simpa [a, e, A.step_eq k] using hraw
          _ ≤ a k + v k := by
                simpa [add_comm, add_left_comm, add_assoc] using add_le_add_left hfactor (a k)
      exact
        tendsto_zero_of_subsequence_and_additiveControl ha_nonneg hv_nonneg hrec hv_sum
          h_vanishing
    · let α10 : ℝ := max α1 0
      let α20 : ℝ := max α2 0
      let u : ℕ → ℝ := fun k ↦ α10 * σ k
      let v : ℕ → ℝ := fun k ↦ α20 * σ k
      have ha_nonneg : ∀ k, 0 ≤ a k := by
        intro k
        dsimp [a]
        exact norm_nonneg _
      have hu_nonneg : ∀ k, 0 ≤ u k := by
        intro k
        dsimp [u, α10]
        exact mul_nonneg (by simp) (hσ_nonneg k)
      have hv_nonneg : ∀ k, 0 ≤ v k := by
        intro k
        dsimp [v, α20]
        exact mul_nonneg (by simp) (hσ_nonneg k)
      have hu_sum : Summable u := by
        dsimp [u, α10]
        exact hσ_sum.mul_left (max α1 0)
      have hv_sum : Summable v := by
        dsimp [v, α20]
        exact hσ_sum.mul_left (max α2 0)
      have hrec : ∀ k, a (k + 1) ≤ (1 + u k) * a k + v k := by
        intro k
        have hraw := hSigma.2 (A.in_dom k) (A.update_mem k)
        have hsigma_nonneg : 0 ≤ σ k := hσ_nonneg k
        have ha_nonneg_k : 0 ≤ a k := ha_nonneg k
        have hcoeff :
            (1 + α1 * σ k) * a k + α2 * σ k ≤ (1 + α10 * σ k) * a k + α20 * σ k := by
          have hcoef_le : 1 + α1 * σ k ≤ 1 + α10 * σ k := by
            dsimp [α10]
            nlinarith [hsigma_nonneg, le_max_left α1 0]
          have hterm1 : (1 + α1 * σ k) * a k ≤ (1 + α10 * σ k) * a k := by
            exact mul_le_mul_of_nonneg_right hcoef_le ha_nonneg_k
          have hterm2 : α2 * σ k ≤ α20 * σ k := by
            dsimp [α20]
            nlinarith [hsigma_nonneg, le_max_left α2 0]
          exact add_le_add hterm1 hterm2
        -- Replace the raw coefficients by their nonnegative parts before using the generic
        -- `σ`-control convergence lemma.
        calc
          a (k + 1) ≤ (1 + α1 * σ k) * a k + α2 * σ k := by
                simpa [a, σ, A.step_eq k] using hraw
          _ ≤ (1 + u k) * a k + v k := by
                dsimp [u, v]
                simpa [α10, α20] using hcoeff
      exact
        tendsto_zero_of_subsequence_and_sigmaControl ha_nonneg hu_nonneg hv_nonneg hrec
          hu_sum hv_sum h_vanishing
  have hSupport :
      SupportsLocalWellDefinedInverseJacobianIteration U F hF.xStar hF.referenceInverse domU := by
    rcases h_update with ⟨γ, hAdd⟩ | ⟨α₁, α₂, hSigma⟩
    · exact hAdd.1
    · exact hSigma.1
  have hInvertibleAll : ∀ k : ℕ, (A.H k).IsInvertible := by
    intro k
    induction k with
    | zero =>
        simpa [A.H_zero] using hH0inv
    | succ k hk =>
        exact (hSupport.2.2 (A.x k) (A.H k) (A.H (k + 1)) (A.in_dom k) hk (A.update_mem k)).1
  let AJ := A.toJacobian hInvertibleAll
  have hInverseContinuous :
      ContinuousAt (fun H : Operator ↦ H.inverse) hF.referenceInverse := by
    exact
      (ContinuousLinearMap.IsInvertible.inverse hF.fderiv_isInvertible
        |>.contDiffAt_map_inverse (𝕜 := ℝ) (n := 1)).continuousAt
  have hH_tendsto : Tendsto A.H atTop (nhds hF.referenceInverse) := by
    exact (tendsto_iff_norm_sub_tendsto_zero).2 <| by simpa [a] using ha_tendsto
  have hInv_tendsto :
      Tendsto (fun k ↦ (A.H k).inverse) atTop (nhds hF.referenceInverse.inverse) := by
    exact hInverseContinuous.tendsto.comp hH_tendsto
  have hRefInv : hF.referenceInverse.inverse = DFstar := by
    simp [DFstar, HasQuasiNewtonLocalConvergenceAssumptions.referenceInverse,
      ContinuousLinearMap.IsInvertible.inverse_inverse hF.fderiv_isInvertible]
  have hJacobian_tendsto :
      Tendsto (fun k ↦ ‖AJ.B k - DFstar‖) atTop (nhds 0) := by
    have hB_tendsto_raw :
        Tendsto (fun k ↦ (A.H k).inverse) atTop (nhds DFstar) := by
      simpa [hRefInv] using hInv_tendsto
    have hB_tendsto : Tendsto AJ.B atTop (nhds DFstar) := by
      change Tendsto (fun k ↦ (A.H k).inverse) atTop (nhds DFstar)
      exact hB_tendsto_raw
    exact (tendsto_iff_norm_sub_tendsto_zero).1 hB_tendsto
  have hSecant_nonneg :
      ∀ᶠ k in atTop, 0 ≤ quasiNewtonSecantErrorRatio F hF.xStar AJ.B AJ.x k := by
    exact Eventually.of_forall fun k ↦ by
      rw [quasiNewtonSecantErrorRatio_apply]
      exact div_nonneg (norm_nonneg _) (norm_nonneg _)
  have hSecant_bound :
      ∀ᶠ k in atTop, quasiNewtonSecantErrorRatio F hF.xStar AJ.B AJ.x k ≤ ‖AJ.B k - DFstar‖ := by
    exact Eventually.of_forall (quasiNewtonSecantErrorRatio_le_jacobianErrorNorm hF AJ)
  have hSecant_tendsto :
      Tendsto (quasiNewtonSecantErrorRatio F hF.xStar AJ.B AJ.x) atTop (nhds 0) := by
    -- The transported Jacobian error sequence bounds the secant-error ratio from above.
    exact squeeze_zero' hSecant_nonneg hSecant_bound hJacobian_tendsto
  have hStep : ∀ k : ℕ, AJ.x (k + 1) = AJ.x k - (AJ.B k).inverse (F (AJ.x k)) := by
    intro k
    simpa [quasiNewtonNextIterate] using AJ.step_eq k
  -- Finish through the Chapter 5 secant-ratio characterization of `Q`-superlinear convergence.
  have hSuperAJ : HasQSuperlinearConvergenceTo AJ.x hF.xStar := by
    exact
      (quasiNewton_superlinear_iff_secantErrorRatio_tendsto_zero F hF AJ.B AJ.x
        AJ.matrices_invertible hStep AJ.iterates_mem hx_tendsto).2 hSecant_tendsto
  change HasQSuperlinearConvergenceTo AJ.x hF.xStar
  exact hSuperAJ

end InverseJacobianQuasiNewtonSmallStartConvergence

/-- Chapter05 Corollary 5.4.12: under the assumptions and small-start regime of
`inverseJacobianQuasiNewtonSmallStartConvergence_of_update_condition`, if some subsequence of the
inverse-approximation errors `‖H k - hF.referenceInverse‖` converges to `0`, then every
inverse-side quasi-Newton run from the same small start converges to `hF.xStar`
`Q`-superlinearly. -/
theorem inverseJacobianQuasiNewton_qSuperlinearConvergence_of_vanishingInverseErrorSubsequence
    {D : Set Point} {F : Point → Point}
    (hF : HasQuasiNewtonLocalConvergenceAssumptions D F)
    (domU : Set (Point × Operator))
    (U : JacobianUpdateFunction Point)
    (h_update :
      (∃ γ : ℝ,
        SatisfiesInverseAdditiveLocalUpdateBound U F hF.xStar hF.referenceInverse domU γ) ∨
      ∃ α₁ α₂ : ℝ,
        SatisfiesInverseSigmaLocalUpdateBound U F hF.xStar hF.referenceInverse domU α₁ α₂) :
    ∃ ε > 0, ∃ δ > 0,
      ∀ x0 : Point, ∀ H0 : Operator,
        ‖x0 - hF.xStar‖ < ε →
        ‖H0 - hF.referenceInverse‖ < δ →
          InverseJacobianQuasiNewtonSmallStartConvergence D F domU U hF.xStar x0 H0 ∧
            ∀ A : InverseJacobianQuasiNewtonIteration D F domU U x0 H0,
              HasSubsequenceTendstoTo (fun k ↦ ‖A.H k - hF.referenceInverse‖) 0 →
                HasQSuperlinearConvergenceTo A.x hF.xStar := by
  rcases existsSmallStartInverseConvergenceData hF domU U h_update with ⟨ε, hε, δ, hδ, hsmall⟩
  refine ⟨ε, hε, δ, hδ, ?_⟩
  intro x0 H0 hx0 hH0
  rcases hsmall x0 H0 hx0 hH0 with ⟨_, hH0inv, hconv⟩
  refine ⟨hconv, ?_⟩
  intro A h_vanishing
  -- Reuse the theorem-local inverse-side superlinear criterion with the initial invertibility
  -- delivered by Theorem 5.4.10's stronger small-start package.
  exact
    InverseJacobianQuasiNewtonSmallStartConvergence.qSuperlinear_of_vanishingInverseErrorSubsequence
      hF h_update hconv hH0inv A
      h_vanishing

end Chapter05Corollary5412
