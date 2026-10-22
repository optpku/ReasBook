/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Definition_3_3
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Lemma_3_3_1
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Proposition_3_50

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u

open scoped LevelMethodNotation

namespace LevelMethodNotation

scoped notation:max "𝓛[" Q:arg ", " model:arg ", " history:arg "](" α:arg ", " k:arg ")" =>
  constrainedSublevelSet
    Q
    (fun x ↦ (model k x : WithTop ℝ))
    (ℓ[history](α, k))

end LevelMethodNotation

open scoped LevelMethodNotation

/- Definition 3.68 lies in the chapter's level-method minimum-value / level-set domain.

Sampled owner declarations:
* `bestFunctionValueUpTo` in `Theorem_3_2_10`, the earlier chapter owner of the sampled minimum
  `f_k^*`
* `levelMethodHistoryFromApproximateValues` in `Proposition_3_50`, the chapter bridge attaching
  the derived interval/gap/level bundle to explicit real lower values `\hat f_k^*`
* `levelMethodApproximateProblem` in `Proposition_3_50`, together with the owner theorem
  `(levelMethodApproximateProblem Q model k).optimalValue_eq_sInf_image`, the faithful Chapter 1
  bridge for the exact model minimum
* `levelMethodHistoryFromApproximateValues_optimalValue_eq` in `Proposition_3_50`, the bridge
  from the history field to the earlier owner `bestFunctionValueUpTo`
* `LevelMethodHistory.valueInterval` in `Lemma_3_3_1`, the owner interval
  `Δ_k = [\hat f_k^*, f_k^*]`
* `LevelMethodHistory.gap` and `LevelMethodHistory.levelValue` in `Lemma_3_3_1`, the owner gap
  `δ_k` and level value `ℓ_k(α)`
* `constrainedSublevelSet` in `Definition_3_3`, the constrained sublevel-set owner used for
  `𝓛_k(α)`

Best owner abstraction:
* the source-facing exact model minimum is the canonical `EReal` owner
  `(levelMethodApproximateProblem Q model k).optimalValue`
* the sampled minimum and the real interval/gap/level bundle are organized by
  `levelMethodHistoryFromApproximateValues hatf f xSeq`
* the derived interval/gap/level bundle is organized by the explicit real lower-value bridge
  `levelMethodHistoryFromApproximateValues hatf f xSeq`

Primitive data:
* a feasible set `Q`
* a model family `model`
* an explicit real lower-value sequence `hatf`
* an objective `f`
* a sample sequence `xSeq`

Derived API:
* `(levelMethodApproximateProblem Q model k).optimalValue`
* `(levelMethodApproximateProblem Q model k).optimalValue
    = sInf ((fun x ↦ (model k x : EReal)) '' Q)`
* the bridge `((fhat(history, k) : ℝ) : EReal) =
    (levelMethodApproximateProblem Q model k).optimalValue`
* `fstar(history, k)` for `f_k^*`
* `Δ[history](k)`
* `δ[history](k)`
* `ℓ[history](α, k)`
* `𝓛[Q, model, history](α, k)`

Source/core/bridge triage:
* source-facing: the canonical exact model minimum
  `(levelMethodApproximateProblem Q model k).optimalValue`, the sampled minimum
  `f_k^* = fstar(history, k)`, and the associated level set
  `𝓛[Q, model, history](α, k)`
* core/canonical: `(levelMethodApproximateProblem Q model k).optimalValue`,
  `bestFunctionValueUpTo (fun i ↦ f (xSeq i)) k`, and
  `levelMethodHistoryFromApproximateValues hatf f xSeq`
* bridge/view: `(levelMethodApproximateProblem Q model k).optimalValue_eq_sInf_image`,
  the explicit `EReal` exactness assumption for `hatf`,
  `levelMethodHistoryFromApproximateValues_optimalValue_eq`,
  `LevelMethodHistory.valueInterval`, and the constrained-sublevel presentation of `𝓛_k(α)`

This file is therefore recall-only. It keeps the source-facing minimum-value objects centered on
their chapter owners and presents them directly on the theorem surface, using the derived history
bundle only for the interval, gap, level value, and level set.
-/

section

variable
    {X : Type u}
    (Q : Set X)
    (model : ℕ → X → ℝ)
    (hatf : ℕ → ℝ)
    (hhat :
      ∀ k : ℕ,
        ((hatf k : ℝ) : EReal) = (levelMethodApproximateProblem Q model k).optimalValue)
    (f : X → ℝ)
    (xSeq : ℕ → X)

section Scalars

variable (k : ℕ) (α : ℝ)

/- Definition 3.68: the exact model minimum `\hat f_k^*` is the canonical `EReal` owner
`(levelMethodApproximateProblem Q model k).optimalValue`. The real history coordinate
`fhat(history, k)` is supplied explicitly via `hatf`, together with the displayed exactness bridge
to the canonical `EReal` owner. -/
#check ((levelMethodApproximateProblem Q model k).optimalValue : EReal)
#check
  (show (levelMethodApproximateProblem Q model k).optimalValue =
      sInf ((fun x ↦ (model k x : EReal)) '' Q) from
    (levelMethodApproximateProblem Q model k).optimalValue_eq_sInf_image)
#check
  (LevelMethodHistory.approximateOptimalValue
    (levelMethodHistoryFromApproximateValues hatf f xSeq)
    k : ℝ)
#check
  (show
      ((LevelMethodHistory.approximateOptimalValue
          (levelMethodHistoryFromApproximateValues hatf f xSeq)
          k : ℝ) : EReal) =
      (levelMethodApproximateProblem Q model k).optimalValue from
    levelMethodHistoryFromApproximateValues_approximateOptimalValue_eq_optimalValue
      Q model hatf f xSeq hhat k)
#check
  (LevelMethodHistory.optimalValue
    (levelMethodHistoryFromApproximateValues hatf f xSeq)
    k : ℝ)
#check
  (show LevelMethodHistory.optimalValue (levelMethodHistoryFromApproximateValues hatf f xSeq) k =
      bestFunctionValueUpTo (fun i ↦ f (xSeq i)) k from
    rfl)
#check
  (LevelMethodHistory.valueInterval
    (levelMethodHistoryFromApproximateValues hatf f xSeq)
    k : Set ℝ)
#check
  (LevelMethodHistory.gap
    (levelMethodHistoryFromApproximateValues hatf f xSeq)
    k : ℝ)
#check
  (LevelMethodHistory.levelValue
    (levelMethodHistoryFromApproximateValues hatf f xSeq)
    α k : ℝ)

end Scalars

section Attainment

variable (k : ℕ) {xHat : X} (hxHat_mem : xHat ∈ Q) (hxHat_min : IsMinOn (model k) Q xHat)

/- If the model minimum is attained at `xHat`, the explicit real lower value `fhat(history, k)`
agrees with `model k xHat` after coercion to the canonical `EReal` owner. -/
#check
  (show
      ((LevelMethodHistory.approximateOptimalValue
          (levelMethodHistoryFromApproximateValues hatf f xSeq)
          k : ℝ) : EReal) =
        model k xHat
    from
    by
      simpa [levelMethodHistoryFromApproximateValues] using
      calc
        ((hatf k : ℝ) : EReal) = (levelMethodApproximateProblem Q model k).optimalValue := hhat k
        _ = model k xHat :=
          (levelMethodApproximateProblem Q model k).optimalValue_eq_of_isMinOn hxHat_mem hxHat_min)

end Attainment

section LevelSet

variable (α : ℝ) (k : ℕ)

/- The level set `𝓛_k(α)` is the constrained sublevel set cut out by the `k`-th model at the
owner level value of the canonical scalar history. -/
#check
  (constrainedSublevelSet
    Q
    (fun x ↦ (model k x : WithTop ℝ))
    (LevelMethodHistory.levelValue
      (levelMethodHistoryFromApproximateValues hatf f xSeq)
      α k) : Set X)

end LevelSet

end

end
