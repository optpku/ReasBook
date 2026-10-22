/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap01.Definition_1_4_16
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap01.Definition_1_5_2

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Gradient

noncomputable section

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

section

variable {L : NNReal} {f : E → ℝ}

/- Lemma 1.5.4 is `source-facing` in second-order smooth optimization.

Source/core/bridge triage:
* `source-facing`: the textbook equivalence between an `L`-Lipschitz gradient and the pointwise
  operator-norm bound `‖∇² f(x)‖ ≤ L` under `C²` regularity
* `core/canonical`: the owner hypotheses `LipschitzWith L (∇ f)` from Definition 1.5.2 and the
  Hessian operator `hessian f x` from Definition 1.4.16
* `bridge/view`: the pointwise real inequality `‖hessian f x‖ ≤ L`

Sampled owner-style declarations:
* `gradient`
* `hessian f x`, the chapter's intrinsic Hessian owner from Definition 1.4.16
* `norm_fderiv_le_of_lipschitz`
* `lipschitzWith_of_nnnorm_fderiv_le`

Owner abstraction:
* the gradient map `∇ f` together with its canonical Hessian operator `hessian f x`

Primitive data:
* a twice continuously differentiable function `f`
* a Lipschitz constant `L`

Derived API:
* the global Lipschitz predicate `LipschitzWith L (∇ f)`
* the pointwise Hessian-operator bound `∀ x, ‖hessian f x‖ ≤ L`

The theorem is stated on a real Hilbert space, and specializing `E` to `EuclideanSpace ℝ (Fin n)`
recovers the textbook `ℝⁿ` formulation. -/
/-- Helper for Lemma 1.5.4: a pointwise operator-norm bound on the Hessian makes the gradient
globally `L`-Lipschitz once the gradient is differentiable. -/
-- Proof sketch: apply the mean value theorem in the form
-- `lipschitzWith_of_nnnorm_fderiv_le` to the gradient map, using differentiability of `∇ f` as
-- primitive data and the pointwise Hessian-operator bound as the derivative estimate.
theorem lipschitzGradient_of_norm_hessian_le
    (hgrad : Differentiable ℝ (∇ f))
    (hbound : ∀ x : E, ‖hessian f x‖ ≤ (L : ℝ)) :
    LipschitzWith L (∇ f) := by
  refine lipschitzWith_of_nnnorm_fderiv_le hgrad ?_
  intro x
  simpa [hessian] using hbound x

/-- Bridge form of Lemma 1.5.4: once the gradient map is differentiable, `∇ f` is globally
`L`-Lipschitz if and only if the Hessian operator satisfies the pointwise norm bound
`‖∇² f(x)‖ ≤ L`, expressed through the chapter owner `hessian f x`. -/
-- Proof sketch: if `∇ f` is globally `L`-Lipschitz, apply
-- `norm_fderiv_le_of_lipschitz` to the map `x ↦ ∇ f x`. Conversely, use
-- `lipschitzWith_of_nnnorm_fderiv_le` for `∇ f`, with differentiability supplied directly by
-- `hgrad`.
theorem lipschitzGradient_iff_norm_hessian_le
    (hgrad : Differentiable ℝ (∇ f)) :
    LipschitzWith L (∇ f) ↔ ∀ x : E, ‖hessian f x‖ ≤ (L : ℝ) := by
  constructor
  · intro hgrad x
    simpa [hessian] using norm_fderiv_le_of_lipschitz ℝ hgrad
  · exact lipschitzGradient_of_norm_hessian_le hgrad

/-- Helper for Lemma 1.5.4: a `C²` function has a differentiable gradient field. -/
-- Proof sketch: first upgrade the gradient to a `C¹` map by composing the derivative of `f`
-- with the inverse Riesz isomorphism, then read off differentiability of that gradient map.
theorem differentiable_gradient_of_contDiff_two
    (hf : ContDiff ℝ 2 f) :
    Differentiable ℝ (∇ f) := by
  have hcontDiffGradient : ContDiff ℝ 1 (∇ f) := by
    simpa [gradient, Function.comp] using
      ((InnerProductSpace.toDual ℝ E).symm.contDiff.comp
        (hf.fderiv_right (by norm_num)))
  -- A `C¹` map is differentiable everywhere, which is the only bridge the main equivalence needs.
  exact hcontDiffGradient.differentiable_one

/-- Lemma 1.5.4 in textbook `C²` form: if `f` is twice continuously differentiable, then the
gradient-Lipschitz condition is equivalent to the pointwise Hessian operator-norm bound. -/
theorem lipschitzGradient_iff_norm_hessian_le_of_contDiff
    (hf : ContDiff ℝ 2 f) :
    LipschitzWith L (∇ f) ↔ ∀ x : E, ‖hessian f x‖ ≤ (L : ℝ) := by
  -- The `C²` hypothesis provides differentiability of `∇ f`.
  -- That bridge lets us invoke the abstract Hessian/Lipschitz equivalence.
  have hgrad : Differentiable ℝ (∇ f) := differentiable_gradient_of_contDiff_two hf
  exact lipschitzGradient_iff_norm_hessian_le hgrad

end

end
