/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

/- Definition 5.0.21 lies in the Chapter 5 one-variable self-concordant auxiliary-function
domain.

Sampled owner-style declarations:
* `HasDerivAt` / `HasStrictDerivAt` in mathlib, the standard one-variable calculus owners behind
  the explicit derivative formulas used downstream;
* `Set.Ioi` and `Set.Iio`, the canonical interval owners for the natural domains `(-1, ∞)` and
  `(-∞, 1)`;
* `Function.invFun` in mathlib, the canonical inverse-function owner later reused for `ω` in
  `Theorem_5_2_4`;
* the adjacent chapter files `Lemma_5_1_4` and `Lemma_5_1_5`, which already treat `ω`, `ω_*`,
  `ω'`, and `ω'_*` as the owner-level Chapter 5 vocabulary.

Source/core/bridge triage:
* source-facing: the four Chapter 5 auxiliary scalar functions `ω`, `ω_*`, `ω'`, and `ω'_*`;
* core/canonical: those owners as maps on their intrinsic interval domains;
* bridge/view: the canonical subtype arguments `selfConcordantOmegaArg`,
  `selfConcordantOmegaStarArg`, and the owner-level evaluation lemmas.

Primitive data:
* the owner functions `ω` and `ω_*`.

Derived API:
* the derivative/inverse branches `ω'` and `ω'_*`;
* the canonical scaled-domain arguments for evaluating `ω` and `ω_*`;
* owner-level `[simp]` evaluation lemmas on the actual subtype domains.

This refinement keeps the Chapter 5 owners unchanged and trims only the duplicate scalar
specializations that were recoverable from the subtype-level evaluation lemmas by ordinary
elaboration. -/

/-- Definition 5.0.21 (1): the auxiliary function `ω(t) = t - log (1 + t)` on `(-1, ∞)`. -/
def selfConcordantOmega : Set.Ioi (-1 : ℝ) → ℝ :=
  fun t ↦ t - Real.log (1 + t)

/-- Definition 5.0.21 (2): the auxiliary function `ω_*(τ) = -τ - log (1 - τ)` on `(-∞, 1)`. -/
def selfConcordantOmegaStar : Set.Iio (1 : ℝ) → ℝ :=
  fun τ ↦ -τ - Real.log (1 - τ)

/-- The derivative branch `ω'(t) = t / (1 + t)` of `ω`, defined on its natural domain
`(-1, ∞)`. -/
def selfConcordantOmegaDeriv : Set.Ioi (-1 : ℝ) → ℝ :=
  fun t ↦ t / (1 + t)

/-- The inverse branch `ω'_*(τ) = τ / (1 - τ)` associated with `ω` and `ω_*`, defined on its
natural domain `(-∞, 1)`. -/
def selfConcordantOmegaPrimeStar : Set.Iio (1 : ℝ) → ℝ :=
  fun τ ↦ τ / (1 - τ)

namespace SelfConcordantAuxiliaryFunction

scoped notation:max "ω" => selfConcordantOmega
scoped notation:max "ω_*" => selfConcordantOmegaStar
scoped notation:max "ω'" => selfConcordantOmegaDeriv
scoped notation:max "ω'_*" => selfConcordantOmegaPrimeStar

end SelfConcordantAuxiliaryFunction

open scoped SelfConcordantAuxiliaryFunction

/-- If `r < 1 / M_f`, then the scaled quantity `M_f r` lies in the natural domain of `ω_*`. -/
theorem mf_mul_lt_one_of_lt_inv {Mf : NNReal} {r : ℝ} (hr : r < 1 / (Mf : ℝ)) :
    (Mf : ℝ) * r < 1 := by
  by_cases hMf : Mf = 0
  · simp [hMf]
  · have hMf_pos : 0 < Mf := lt_of_le_of_ne Mf.2 (Ne.symm hMf)
    have hMf' : 0 < (Mf : ℝ) := by
      exact_mod_cast hMf_pos
    have hlt :
        (Mf : ℝ) * r < (Mf : ℝ) * (1 / (Mf : ℝ)) := by
      exact mul_lt_mul_of_pos_left hr hMf'
    have hunit : (Mf : ℝ) * (1 / (Mf : ℝ)) = 1 := by
      field_simp [ne_of_gt hMf']
    calc
      (Mf : ℝ) * r < (Mf : ℝ) * (1 / (Mf : ℝ)) := hlt
      _ = 1 := hunit

/-- If `r ≥ 0`, then the scaled quantity `M_f r` lies in the natural domain of `ω`. -/
theorem neg_one_lt_mf_mul_of_nonneg {Mf : NNReal} {r : ℝ} (hr : 0 ≤ r) :
    -1 < (Mf : ℝ) * r := by
  have hMf : 0 ≤ (Mf : ℝ) := by
    exact_mod_cast Mf.2
  nlinarith

/-- The canonical `ω` argument attached to a scalar `r` whose scaled value lies in the natural
domain of `ω`. -/
def selfConcordantOmegaArg (Mf : NNReal) (r : ℝ) (hr : -1 < (Mf : ℝ) * r) : Set.Ioi (-1 : ℝ) :=
  ⟨(Mf : ℝ) * r, hr⟩

/-- Coercing `selfConcordantOmegaArg Mf r hr` back to `ℝ` recovers `M_f r`. -/
@[simp] theorem coe_selfConcordantOmegaArg
    (Mf : NNReal) (r : ℝ) (hr : -1 < (Mf : ℝ) * r) :
    ↑(selfConcordantOmegaArg Mf r hr) = (Mf : ℝ) * r :=
  rfl

/-- The textbook point `1 / 2` in the natural domain `(-1, ∞)` of `ω`. -/
def selfConcordantOmegaOneHalfArg : Set.Ioi (-1 : ℝ) :=
  ⟨1 / 2, by norm_num⟩

/-- Coercing `selfConcordantOmegaOneHalfArg` back to `ℝ` recovers `1 / 2`. -/
@[simp] theorem coe_selfConcordantOmegaOneHalfArg :
    ↑selfConcordantOmegaOneHalfArg = (1 / 2 : ℝ) :=
  rfl

/-- The Chapter 5 textbook constant `ω(1 / 2)`. -/
def selfConcordantOmegaAtOneHalf : ℝ :=
  ω selfConcordantOmegaOneHalfArg

/-- The canonical `ω_*` argument attached to a scalar `r` satisfying `(Mf : ℝ) * r < 1`. -/
def selfConcordantOmegaStarArg (Mf : NNReal) (r : ℝ) (hr : (Mf : ℝ) * r < 1) :
    Set.Iio (1 : ℝ) :=
  ⟨(Mf : ℝ) * r, hr⟩

/-- Coercing `selfConcordantOmegaStarArg Mf r hr` back to `ℝ` recovers `M_f r`. -/
@[simp] theorem coe_selfConcordantOmegaStarArg
    (Mf : NNReal) (r : ℝ) (hr : (Mf : ℝ) * r < 1) :
    ↑(selfConcordantOmegaStarArg Mf r hr) = (Mf : ℝ) * r :=
  rfl

/-- Evaluating `ω` at a point of `(-1, ∞)` recovers the explicit formula
`t - log (1 + t)`. -/
@[simp] theorem selfConcordantOmega_apply (t : Set.Ioi (-1 : ℝ)) :
    ω t = t - Real.log (1 + t) :=
  rfl

/-- Evaluating `ω_*` at a point of `(-∞, 1)` recovers the textbook
formula `-τ - log (1 - τ)`. -/
@[simp] theorem selfConcordantOmegaStar_apply (τ : Set.Iio (1 : ℝ)) :
    ω_* τ = -τ - Real.log (1 - τ) :=
  rfl

/-- Evaluating `ω'` at a point of `(-1, ∞)` recovers the explicit derivative formula
`t / (1 + t)`. -/
@[simp] theorem selfConcordantOmegaDeriv_apply (t : Set.Ioi (-1 : ℝ)) :
    ω' t = t / (1 + t) :=
  rfl

/-- Evaluating `ω'_*` at a point of `(-∞, 1)` recovers the explicit inverse-branch formula
`τ / (1 - τ)`. -/
@[simp] theorem selfConcordantOmegaPrimeStar_apply (τ : Set.Iio (1 : ℝ)) :
    ω'_* τ = τ / (1 - τ) :=
  rfl

end
