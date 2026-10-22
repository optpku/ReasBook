/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Basic
import Mathlib.Order.Filter.AtTopBot.Basic
import OptimizationTheoryAndMethods_SunYuan_2006.Chap12.Definition_12_3_extra_1
import OptimizationTheoryAndMethods_SunYuan_2006.Chap12.Lemma_12_7_2

noncomputable section

open Filter

section

variable {n m : ℕ}
-- Domain sampling for this file:
-- * primary domain: subsequential trial-step asymptotics for the Section 12.7 smooth exact
--   penalty SQP method;
-- * sampled owner declarations:
--   `HasSuperlinearlyConvergentStep`,
--   `hasSuperlinearlyConvergentStep_iff_isLittleO`,
--   `PowellYuanMethod.stepSizeAt`,
--   `PowellYuanMethod.iterate_succ_eq_trialPoint`,
--   and `SmoothExactPenaltyMethod`;
-- * source/core/bridge triage:
--   `eventually_fullStep_along_subsequence_of_trialPoint_superlinearStep` is the source-facing
--   theorem because Chapter 12 already owns both the trial-step notion through
--   `HasSuperlinearlyConvergentStep` and the accepted Step-3 steplength through
--   `PowellYuanMethod.stepSizeAt`;
--   `=o[atTop]` is the core/canonical asymptotic API;
--   `eventually_fullStep_along_subsequence_of_trialPoint_isLittleO` is the bridge theorem that
--   keeps the explicit little-`o` hypothesis surface.
-- * primitive vs. derived API:
--   the primitive trial-step datum is the owner predicate on the subsequence
--   `(method.iterate ∘ κ, method.searchDirection ∘ κ)`, together with the algorithm owner
--   `method.stepSizeAt` for the accepted Step-3 steplength;
--   the explicit little-`o` condition and the iterate identity
--   `x_(κ i + 1) = x_(κ i) + d_(κ i)` are derived bridge data.

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
    {xStar : Point n}
    (hxstar : Tendsto method.iterate atTop (nhds xStar))
    (κ : ℕ → ℕ)
    (hκ : StrictMono κ)

include
  method
  hx_bounded
  hd_bounded
  hB_bounded
  hA_fullColumnRank
  hδ
  hNullspaceCurvature
  hxstar
  κ
  hκ

/-- Chapter12 Lemma 12.7.4: assume that the hypotheses of `Chapter12 Lemma 12.7.2` hold for the
Section 12.7 smooth exact penalty method `method`, and that the iterate sequence `x_k`
converges to `xStar`. For any subsequence `κ`, if the trial-point error
`‖x_(κ i) + d_(κ i) - xStar‖ / ‖x_(κ i) - xStar‖` tends to `0`, encoded by the chapter owner
`HasSuperlinearlyConvergentStep (method.iterate ∘ κ) (method.searchDirection ∘ κ) xStar`, then
the accepted Step-3 steplength is eventually the full step
`method.stepSizeAt (κ i) = 1`. -/
theorem eventually_fullStep_along_subsequence_of_trialPoint_superlinearStep
    (htrial :
      HasSuperlinearlyConvergentStep
        (method.iterate ∘ κ)
        (method.searchDirection ∘ κ)
        xStar) :
    ∀ᶠ i : ℕ in atTop,
      method.stepSizeAt (κ i) = 1 := sorry

/-- Bridge form of `Chapter12 Lemma 12.7.4`: the core asymptotic hypothesis
`‖x_(κ i) + d_(κ i) - xStar‖ = o(‖x_(κ i) - xStar‖)` implies the chapter owner
`HasSuperlinearlyConvergentStep` on the subsequence, so the same eventual owner-level full-step
conclusion follows. -/
theorem eventually_fullStep_along_subsequence_of_trialPoint_isLittleO
    (htrial :
      (fun i : ℕ ↦
        ‖method.iterate (κ i) + method.searchDirection (κ i) - xStar‖) =o[atTop]
        (fun i : ℕ ↦ ‖method.iterate (κ i) - xStar‖)) :
    ∀ᶠ i : ℕ in atTop,
      method.stepSizeAt (κ i) = 1 := by
  have hzero :
      ∀ᶠ i : ℕ in atTop,
        method.iterate (κ i) = xStar →
          method.iterate (κ i) + method.searchDirection (κ i) = xStar := by
    filter_upwards [htrial.isBigO.eq_zero_imp] with i hi hxi
    have hden :
        ‖method.iterate (κ i) - xStar‖ = 0 := by
      simp [hxi]
    have hnum :
        ‖method.iterate (κ i) + method.searchDirection (κ i) - xStar‖ = 0 :=
      hi hden
    exact sub_eq_zero.1 (norm_eq_zero.1 hnum)
  have htrial' :
      HasSuperlinearlyConvergentStep
        (method.iterate ∘ κ)
        (method.searchDirection ∘ κ)
        xStar := by
    refine
      (hasSuperlinearlyConvergentStep_iff_isLittleO
        (method.iterate ∘ κ)
        (method.searchDirection ∘ κ)
        xStar
        ?_).2 ?_
    · simpa [Function.comp] using hzero
    · simpa [Function.comp] using htrial
  exact
    eventually_fullStep_along_subsequence_of_trialPoint_superlinearStep
      method
      hx_bounded
      hd_bounded
      hB_bounded
      hA_fullColumnRank
      hδ
      hNullspaceCurvature
      hxstar
      κ
      hκ
      htrial'

end
