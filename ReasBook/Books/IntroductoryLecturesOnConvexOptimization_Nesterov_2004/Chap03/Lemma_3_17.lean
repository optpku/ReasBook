/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import Mathlib.Tactic.Recall
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Lemma_3_1_17
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Theorem_3_44

-- Declarations for this item will be appended below by the statement pipeline.

open scoped BigOperators Gradient Pointwise WithTopConvexAnalysis

noncomputable section

universe u

variable {m : ℕ} {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

local notation "Y" => EuclideanSpace ℝ (Fin m)

/- Lemma 3.17 lies in the constrained convex-composition / relative-subdifferential domain.

Sampled owner-style declarations:
- `vectorMap` in `Lemma_3_1_16`
- mathlib `Monotone` and `HasGradientAt` on `Fin m → ℝ`
- `constrainedSubdifferential_comp_coordinatewiseMonotone_eq_weighted_sum` in `Lemma_3_1_17`
- the real-valued constrained-subdifferential notation `∂[Q] f(x)` and bridge
  `subdifferentialWithin` in `Theorem_3_44`

Best owner abstractions:
- source-facing: Lemma 3.17's real-valued relative-subdifferential chain rule
- core/canonical: `vectorMap` together with
  `constrainedSubdifferential_comp_coordinatewiseMonotone_eq_weighted_sum`
- bridge/view: the chapter's real-valued relative-subdifferential surface `∂[Q] f(x)`, implemented
  through `subdifferentialWithin`

Primitive data:
- a convex feasible set `Q`
- a coordinate family `fs : Fin m → E → ℝ`
- a convex coordinatewise-monotone outer function `F : Y → ℝ`

Derived API:
- convexity of `F ∘ vectorMap fs` on `Q`
- the real-valued chain-rule equality and its subset corollary on `∂[Q] f(x)`

Source/core/bridge triage:
- source-facing: Lemma 3.17's chain-rule statement for real-valued relative subdifferentials
- core/canonical: the constrained-subdifferential owner theorem in `Lemma_3_1_17`
- bridge/view: this file's `∂[Q] f(x)` reformulation of that owner theorem

This file therefore deletes the exact-interface duplicate wrapper theorem and keeps only the
real-valued bridge to the canonical owner surface `∂[Q] f(x)`, plus the one genuine local
subset corollary.
-/

/- Upstream owner theorem reused below:
`convexOn_comp_coordinatewiseMonotone` from `Lemma_3_1_17`. -/

recall convexOn_comp_coordinatewiseMonotone

section

variable {Q : Set E} {fs : Fin m → E → ℝ} {F : Y → ℝ}
variable (hF_convex : ConvexOn ℝ Set.univ F)
variable (hQ_convex : Convex ℝ Q)
variable (hfs_convex : ∀ i, ConvexOn ℝ Q (fs i))
variable (hF_mono : Monotone (F ∘ (EuclideanSpace.equiv (Fin m) ℝ).symm))

/-- Lemma 3.17 (2): under the same hypotheses, the real-valued relative subdifferential
`∂[Q] (F ∘ vectorMap fs) (x)` equals the weighted sum of the coordinate relative
subdifferentials `∑ i, g i • ∂[Q] (fs i) (x)` for a gradient witness
`HasGradientAt F g (vectorMap fs x)`. -/
theorem subdifferentialWithin_comp_coordinatewiseMonotone_eq_weighted_sum
    {x : E} (_hx : x ∈ interior Q) {g : Y}
    (_hF_grad : HasGradientAt F g (vectorMap fs x)) :
    ∂[Q] (F ∘ vectorMap fs) (x) =
      ∑ i,
        (g i) • ∂[Q] (fs i) (x) :=
  let _ : Decidable (x ∈ interior Q) := Classical.decPred (fun y : E ↦ y ∈ interior Q) x
  if hx' : x ∈ interior Q then
    constrainedSubdifferential_comp_coordinatewiseMonotone_eq_weighted_sum
      hQ_convex hF_convex hfs_convex hF_mono hx' _hF_grad
  else
    False.elim (hx' _hx)

/-- Lemma 3.17 (1): at each interior point `x ∈ interior Q`, the weighted sum of the coordinate
relative subdifferentials `∂[Q] (fs i) (x)`, with weights given by the coordinates of
the gradient witness `g`, is contained in
`∂[Q] (F ∘ vectorMap fs) (x)`. -/
theorem weighted_sum_subdifferentialWithin_subset_comp_coordinatewiseMonotone
    {x : E} (_hx : x ∈ interior Q) {g : Y}
    (_hF_grad : HasGradientAt F g (vectorMap fs x)) :
    (∑ i,
        (g i) • ∂[Q] (fs i) (x)) ⊆
      ∂[Q] (F ∘ vectorMap fs) (x) :=
  let _ : Decidable (x ∈ interior Q) := Classical.decPred (fun y : E ↦ y ∈ interior Q) x
  if hx' : x ∈ interior Q then
    fun g hg ↦
      (subdifferentialWithin_comp_coordinatewiseMonotone_eq_weighted_sum
        hF_convex hQ_convex hfs_convex hF_mono hx' _hF_grad).symm ▸ hg
  else
    False.elim (hx' _hx)

end

end
