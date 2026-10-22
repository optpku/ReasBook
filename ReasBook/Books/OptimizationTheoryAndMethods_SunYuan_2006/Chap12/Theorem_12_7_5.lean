/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Basic
import Mathlib.Order.Filter.AtTopBot.Basic
import OptimizationTheoryAndMethods_SunYuan_2006.Chap01.Definition_1_5_extra_1
import OptimizationTheoryAndMethods_SunYuan_2006.Chap12.Definition_12_3_extra_1
import OptimizationTheoryAndMethods_SunYuan_2006.Chap12.Lemma_12_7_4
import OptimizationTheoryAndMethods_SunYuan_2006.Chap12.Lemma_12_7_2

noncomputable section

open Filter

section

variable {n m : ℕ}
-- Domain sampling for this file:
-- * primary domain: eventual full-step acceptance and induced `Q`-superlinear iterate
--   convergence for the Section 12.7 smooth exact penalty SQP method;
-- * sampled owner declarations:
--   `SmoothExactPenaltyMethod`,
--   `eventually_fullStep_along_subsequence_of_trialPoint_superlinearStep`,
--   `HasSuperlinearlyConvergentStep`,
--   and `HasQSuperlinearConvergenceTo`;
-- * source/core/bridge triage:
--   the source-facing layer here is the eventual full-step conclusion
--   `method.stepSizeAt k = 1` and its Step-4 iterate-update consequence;
--   the core/canonical owners are the method owner `SmoothExactPenaltyMethod` and the chapter
--   convergence owners `HasSuperlinearlyConvergentStep` and `HasQSuperlinearConvergenceTo`;
--   the trial-point ratio wording and raw Step-4 update are bridge views of those owners;
-- * primitive vs. derived API:
--   the primitive data are the method owner together with the boundedness, rank, and
--   nullspace-curvature hypotheses already used in `Lemma_12_7_4`;
--   the eventual update identity and `Q`-superlinear iterate convergence are derived
--   consequences once eventual continuation is supplied.

variable
    (method : SmoothExactPenaltyMethod n m)
    (hx_bounded : Bornology.IsBounded (Set.range method.iterate))
    (hd_bounded : Bornology.IsBounded (Set.range method.searchDirection))
    (hB_bounded : Bornology.IsBounded (Set.range method.hessianOperator))
    (hA_fullColumnRank : ∀ x : Point n, Function.Injective (method.constraintJacobian x))
    {δ : ℝ} (hδ : 0 < δ)
    (hNullspaceCurvature :
      ∀ k : ℕ, ∀ d : Point n,
        (method.constraintJacobian (method.iterate k)).adjoint d = 0 →
          δ * ‖d‖ ^ (2 : ℕ) ≤ inner ℝ d (method.hessianOperator k d))

include
  method
  hx_bounded
  hd_bounded
  hB_bounded
  hA_fullColumnRank
  hδ
  hNullspaceCurvature

-- Semantic recall: the Section 12.7 method owner now lives in `Lemma_12_7_2`, and this file
-- only adds the Section 12.7 main theorem while reusing the chapter's canonical
-- `HasSuperlinearlyConvergentStep` owner for the trial-point ratio `(12.7.19)`. The accepted
-- Step-3 steplength `method.stepSizeAt` is the source-facing owner conclusion here; the raw
-- iterate update and the Chapter 1 `HasQSuperlinearConvergenceTo` conclusion are only bridge
-- consequences once an explicit eventual-continuation tail is supplied.

/-- Chapter12 Theorem 12.7.5: assume that the hypotheses of `Chapter12 Lemma 12.7.2` hold for
the Section 12.7 smooth exact penalty method `method`, and that the iterate sequence `x_k`
converges to `xStar`. If the trial-point ratio `(12.7.19)`
`‖x_k + d_k - xStar‖ / ‖x_k - xStar‖` tends to `0`, encoded by
`HasSuperlinearlyConvergentStep method.iterate method.searchDirection xStar`, then the accepted
Step-3 steplength is eventually the full step `method.stepSizeAt k = 1`. Under the current
algorithm owner this is the source-facing conclusion: Step 4 only records the raw update
`x_(k + 1) = x_k + β_k d_k` on nonterminal stages, so iterate-level consequences require a
separate continuation-tail hypothesis. -/
theorem eventually_fullStep_of_trialPointRatio_tendsto_zero
    {xStar : Point n}
    (hxstar : Tendsto method.iterate atTop (nhds xStar))
    (htrial : HasSuperlinearlyConvergentStep method.iterate method.searchDirection xStar) :
    ∀ᶠ k in atTop, method.stepSizeAt k = 1 :=
  eventually_fullStep_along_subsequence_of_trialPoint_superlinearStep
    method
    hx_bounded
    hd_bounded
    hB_bounded
    hA_fullColumnRank
    hδ
    hNullspaceCurvature
    hxstar
    id
    (strictMono_id : StrictMono id)
    htrial

/-- Bridge form of Theorem 12.7.5: if the Section 12.7 smooth exact penalty method eventually
stays on the continuation branch `¬ method.terminatedAt k`, then the eventual full-step
conclusion from `eventually_fullStep_of_trialPointRatio_tendsto_zero` upgrades to the raw
Step-4 identity `x_(k + 1) = x_k + d_k` on a tail, and therefore the iterate sequence
converges to `xStar` `Q`-superlinearly in the canonical Chapter 1 sense. -/
theorem eventually_iterateUpdate_and_hasQSuperlinearConvergenceTo_of_trialPointRatio_tendsto_zero
    {xStar : Point n}
    (hxstar : Tendsto method.iterate atTop (nhds xStar))
    (hcontinue : ∀ᶠ k in atTop, ¬ method.terminatedAt k)
    (htrial : HasSuperlinearlyConvergentStep method.iterate method.searchDirection xStar) :
    (∀ᶠ k in atTop, method.iterate (k + 1) = method.iterate k + method.searchDirection k) ∧
      HasQSuperlinearConvergenceTo method.iterate xStar := by
  have hstep :
      ∀ᶠ k in atTop, method.stepSizeAt k = 1 :=
    eventually_fullStep_of_trialPointRatio_tendsto_zero
      method
      hx_bounded
      hd_bounded
      hB_bounded
      hA_fullColumnRank
      hδ
      hNullspaceCurvature
      hxstar
      htrial
  have hupdate :
      ∀ᶠ k in atTop, method.iterate (k + 1) = method.iterate k + method.searchDirection k := by
    filter_upwards [eventually_ge_atTop 1, hcontinue, hstep] with k hk hcont hβ
    calc
      method.iterate (k + 1) =
          powellYuanTrialPoint
            (method.iterate k)
            (method.searchDirection k)
            (method.stepSizeAt k) :=
        method.iterate_succ_eq_trialPoint hk hcont
      _ = method.iterate k + method.stepSizeAt k • method.searchDirection k := by
        rw [powellYuanTrialPoint_eq]
      _ = method.iterate k + method.searchDirection k := by
        simp [hβ]
  exact ⟨hupdate, htrial.toHasQSuperlinearConvergenceTo hxstar hupdate⟩

end
