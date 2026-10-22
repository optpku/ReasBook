/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap02.Lemma_2_7

-- Declarations for this item will be appended below by the statement pipeline.

open AffineMap

universe u

/- Primary domain: estimating sequences for real-valued objective functions.

Source/core/bridge triage for Definition 2.21:
* source-facing: `IsEstimatingSequence f φ lam`
* core/canonical: `Filter.Tendsto` for `λₖ → 0` and `AffineMap.lineMap` on the function space
  `X → ℝ` for the affine upper model between `f` and `φ₀`
* bridge/view: the pointwise textbook inequality `upper_bound_apply` and the gap consequences
  specialized from `Lemma_2_7`

Relevant declarations sampled before refining:
* `AffineMap.lineMap`
* `AffineMap.lineMap_apply_module`
* `estimatingSequence_gap_mem_Icc`
* `estimatingSequence_gap_tendsto_zero`

Owner abstraction:
* the chapter's source-facing owner is `IsEstimatingSequence`; its stagewise affine upper model is
  canonically expressed by `AffineMap.lineMap` rather than by repeating a raw function-space affine
  combination in every declaration. The source chapter applies it to functions on `ℝⁿ`, but the
  owner itself is purely pointwise and therefore lives on an arbitrary domain `X`.

Primitive data:
* the domain `X`
* the coefficient sequence `lam : ℕ → NNReal`
* the function sequence `φ`
* the asymptotic condition `lam ⟶ 0`
* the stagewise upper bound `φ k ≤ lineMap f (φ 0) (lam k : ℝ)`

Derived API:
* the projection lemmas `tendsto_zero` and `upper_bound`
* the source-facing pointwise bridge `upper_bound_apply`
* the gap corollaries `gap_mem_Icc` and `gap_tendsto_zero`
-/

/-- Definition 2.21: a pair of sequences `φₖ : X → ℝ` and `λₖ ∈ [0, ∞)` is an estimating
sequence for `f` when `λₖ → 0` and each model `φₖ` satisfies the upper estimate
`φₖ(x) ≤ (1 - λₖ) f(x) + λₖ φ₀(x)` for every `k` and every `x`. -/
def IsEstimatingSequence
    {X : Type u}
    (f : X → ℝ)
    (φ : ℕ → X → ℝ)
    (lam : ℕ → NNReal) : Prop :=
  Filter.Tendsto lam Filter.atTop (nhds 0) ∧
    ∀ k : ℕ,
      φ k ≤ lineMap f (φ 0) (lam k : ℝ)

namespace IsEstimatingSequence

variable {X : Type u} {f : X → ℝ} {φ : ℕ → X → ℝ} {lam : ℕ → NNReal}

section Core

/-- An estimating sequence has coefficient sequence converging to `0`. -/
theorem tendsto_zero (h : IsEstimatingSequence f φ lam) :
    Filter.Tendsto lam Filter.atTop (nhds 0) :=
  h.1

/-- An estimating sequence is bounded above by the canonical function-space line map from `f` to
`φ₀` at every index. -/
theorem upper_bound
    (h : IsEstimatingSequence f φ lam) (k : ℕ) :
    φ k ≤ lineMap f (φ 0) (lam k : ℝ) :=
  h.2 k

/-- Evaluating the function-space upper bound recovers the textbook pointwise inequality. -/
theorem upper_bound_apply
    (h : IsEstimatingSequence f φ lam) (k : ℕ) (x : X) :
    φ k x ≤ (1 - (lam k : ℝ)) * f x + (lam k : ℝ) * φ 0 x := by
  simpa [lineMap_apply_module] using h.upper_bound k x

end Core

section Gap

/-- An estimating sequence satisfying the Lemma 2.7 minimum-value hypotheses controls the
optimality gap by the canonical interval
`[0, lambda_k * (phi_0 x* - f x*)]`. -/
theorem gap_mem_Icc
    (h : IsEstimatingSequence f φ lam)
    (xStar : X)
    (hmin : IsMinOn f Set.univ xStar)
    (phiStar : ℕ → ℝ)
    (hphiStar : ∀ k, IsLeast (Set.range (φ k)) (phiStar k))
    (x : ℕ → X)
    (hx : ∀ k, f (x k) ≤ phiStar k)
    (k : ℕ) :
    f (x k) - f xStar ∈ Set.Icc 0 ((lam k : ℝ) * (φ 0 xStar - f xStar)) := by
  simpa using estimatingSequence_gap_mem_Icc xStar phiStar x hmin h.upper_bound hphiStar hx k

/-- Under the hypotheses of `gap_mem_Icc`, the optimality gap of an estimating sequence
converges to `0`. -/
theorem gap_tendsto_zero
    (h : IsEstimatingSequence f φ lam)
    (xStar : X)
    (hmin : IsMinOn f Set.univ xStar)
    (phiStar : ℕ → ℝ)
    (hphiStar : ∀ k, IsLeast (Set.range (φ k)) (phiStar k))
    (x : ℕ → X)
    (hx : ∀ k, f (x k) ≤ phiStar k) :
    Filter.Tendsto (fun k ↦ f (x k) - f xStar) Filter.atTop (nhds 0) := by
  simpa using estimatingSequence_gap_tendsto_zero xStar phiStar x hmin
    (NNReal.tendsto_coe.2 h.tendsto_zero) h.upper_bound hphiStar hx

end Gap

end IsEstimatingSequence
