/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

/- Definition 1.5.1 is the Chapter 1 `source-facing` recall point in the multivariable
Taylor-series regularity domain.

Primary domain: higher-order Taylor control on a set together with a Lipschitz bound on a fixed
Taylor coefficient.

Sampled owner-style declarations:
* `HasFTaylorSeriesUpToOn`
* `HasFTaylorSeriesUpToOn.eq_iteratedFDerivWithin_of_uniqueDiffOn`
* `HasFTaylorSeriesUpToOn.continuousLinearMap_comp`
* `HasFTaylorSeriesUpToOn.add`

Owner abstraction:
* the source-facing class `taylorCoeffLipschitzClass k p L Q`, with notation
  `𝒞^{k,p}_{L}(Q)`
* the Taylor-series-on-a-set predicate `HasFTaylorSeriesUpToOn k f P Q`

Source/core/bridge triage:
* `source-facing`: the textbook class `C^{k,p}_L(Q)`, expressed as
  `p ≤ k ∧ ∃ P, HasFTaylorSeriesUpToOn k f P Q ∧ LipschitzOnWith L (fun x ↦ P x p) Q`
* `core/canonical`: the owner predicate `HasFTaylorSeriesUpToOn`
* `bridge/view`: on `UniqueDiffOn ℝ Q`, the coordinate formula through `iteratedFDerivWithin`
  recovered by `HasFTaylorSeriesUpToOn.eq_iteratedFDerivWithin_of_uniqueDiffOn`

Primitive data:
* the order constraint `p ≤ k`
* a Taylor witness `P`
* the owner predicate `HasFTaylorSeriesUpToOn k f P Q`
* the Lipschitz bound on the `p`-th Taylor coefficient `fun x ↦ P x p`

Derived API:
* the source-facing membership surface `f ∈ 𝒞^{k,p}_{L}(Q)`
* the `iteratedFDerivWithin` description under `UniqueDiffOn`
* linearity transport of Taylor witnesses via `HasFTaylorSeriesUpToOn.continuousLinearMap_comp`
* addition of Taylor witnesses via `HasFTaylorSeriesUpToOn.add`

This file keeps the textbook class as a thin source-facing owner on functions, while the
Taylor-series owner declarations remain the canonical core/bridge companions for downstream use.
-/

section

universe u

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable (k p : ℕ) (L : NNReal) (f : E → ℝ) (Q : Set E)

local notation "TaylorSeries" => E → FormalMultilinearSeries ℝ E ℝ

/-- Definition 1 5 1: the textbook class `C^{k,p}_L(Q)` of real-valued functions on `Q`
consists of functions that admit a Taylor-series witness up to order `k` on `Q` whose `p`-th
coefficient is `L`-Lipschitz on `Q`. -/
def taylorCoeffLipschitzClass (k p : ℕ) (L : NNReal) (Q : Set E) : Set (E → ℝ) :=
  {g | p ≤ k ∧ ∃ P : TaylorSeries,
    HasFTaylorSeriesUpToOn k g P Q ∧
      LipschitzOnWith L (fun x ↦ P x p) Q}

notation "𝒞^{" k "," p "}_{" L "}(" Q ")" => taylorCoeffLipschitzClass k p L Q

/-- Writing the source-facing owner with the textbook notation `𝒞^{k,p}_{L}(Q)` does not change
its membership criterion. -/
-- Proof sketch: unfold the notation `𝒞^{k,p}_{L}(Q)`.
@[simp] theorem mem_taylorCoeffLipschitzClass_notation_iff :
    f ∈ 𝒞^{k,p}_{L}(Q) ↔
      p ≤ k ∧ ∃ P : TaylorSeries,
        HasFTaylorSeriesUpToOn k f P Q ∧
          LipschitzOnWith L (fun x ↦ P x p) Q :=
  Iff.rfl

namespace taylorCoeffLipschitzClass

/-- Membership in the textbook class `𝒞^{k,p}_{L}(Q)` implies the order bound `p ≤ k`. -/
-- Proof sketch: extract the first conjunct from
-- `mem_taylorCoeffLipschitzClass_notation_iff`.
theorem order_le {k p : ℕ} {L : NNReal} {f : E → ℝ} {Q : Set E}
    (hf : f ∈ 𝒞^{k,p}_{L}(Q)) :
    p ≤ k := by
  exact hf.1

/-- Membership in the textbook class `𝒞^{k,p}_{L}(Q)` yields the Taylor witness and the
corresponding Lipschitz bound from Definition 1.5.1. -/
-- Proof sketch: extract the existential witness from
-- `mem_taylorCoeffLipschitzClass_notation_iff`.
theorem exists_taylorSeries
    {k p : ℕ} {L : NNReal} {f : E → ℝ} {Q : Set E}
    (hf : f ∈ 𝒞^{k,p}_{L}(Q)) :
    ∃ P : TaylorSeries,
      HasFTaylorSeriesUpToOn k f P Q ∧
        LipschitzOnWith L (fun x ↦ P x p) Q := by
  exact hf.2

end taylorCoeffLipschitzClass

#check (f ∈ 𝒞^{k,p}_{L}(Q))

end

recall HasFTaylorSeriesUpToOn
recall HasFTaylorSeriesUpToOn.eq_iteratedFDerivWithin_of_uniqueDiffOn
recall HasFTaylorSeriesUpToOn.continuousLinearMap_comp
recall HasFTaylorSeriesUpToOn.add
