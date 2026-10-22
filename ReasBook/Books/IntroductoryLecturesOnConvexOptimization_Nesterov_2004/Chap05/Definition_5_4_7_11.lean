/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Definition_3_3
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Remark_3_1_2_3

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open scoped BigOperators

/- Definition 5.4.7.11 lies in the Chapter 5 log-sum-exp / perspective-epigraph domain.

Sampled owner declarations:
* `convexOn_log_sum_exp_of_convexOn` from `Chap03/Proposition_3_21`, the project owner theorem
  for finite-family log-sum-exp on a common domain;
* `perspectiveTransform` from `Chap03/Remark_3_1_2_3`, the chapter owner for the scaled-input
  construction `(τ, x) ↦ τ f (τ⁻¹ • x)`;
* `constrainedEpigraph` from `Chap03/Definition_3_3`, the chapter owner for epigraphs over a
  specified feasible domain;
* `mem_constrainedEpigraph_iff` from `Chap03/Definition_3_3`, the atomic membership bridge for
  that owner.

Best owner abstraction:
* source-facing: `logSumExp` and the textbook cone `logSumExpEpigraphCone`;
* core/canonical: `perspectiveTransform` together with `constrainedEpigraph`;
* bridge/view: the `Fin n` specialization `EuclideanSpace ℝ (Fin n)` of the intrinsic finite-family
  owner below, together with the coordinate permutation `(x, t, τ) ↦ (((τ, x), t))`.

Primitive data:
* a finite index type `ι`;
* the source-facing log-sum-exp function on `EuclideanSpace ℝ ι`.

Derived API:
* the evaluation lemma `logSumExp_apply`;
* the perspective-epigraph owner `logSumExpEpigraphCone`;
* the membership bridge `mem_logSumExpEpigraphCone_iff`.

The previous version stored the conic epigraph as a raw inequality set and pinned the owner to the
coordinate model `EuclideanSpace ℝ (Fin n)`. The mathematics is still the same source-facing cone,
but its implementation should reuse the chapter owners for perspectives and constrained epigraphs
at the canonical finite-family level, with the textbook `ℝⁿ` presentation obtained by
specialization to `ι = Fin n`. -/

universe v

variable {ι : Type v} [Fintype ι]

local notation "E" => EuclideanSpace ℝ ι
local notation "P" => ℝ × E

/-- The finite-family log-sum-exp function `x ↦ log (∑ i, exp (x i))` on
`EuclideanSpace ℝ ι`. Specializing to `ι = Fin n` recovers the textbook `n`-variable formula. -/
def logSumExp : E → ℝ :=
  fun x ↦ Real.log (∑ i : ι, Real.exp (x i))

/-- Evaluating `logSumExp` at `x` gives `log (∑ i, exp (x i))`. -/
@[simp] theorem logSumExp_apply (x : E) :
    logSumExp x = Real.log (∑ i : ι, Real.exp (x i)) :=
  rfl

/-- Definition 5.4.7.11: the conic-hull epigraph of the finite-family log-sum-exp function is the
set of triples `(x, t, τ)` with `τ > 0` and `t ≥ τ * logSumExp (τ⁻¹ • x)`, i.e. the scaled-input
form of `t ≥ τ f(x / τ)`. This is the constrained epigraph of the perspective transform of
`logSumExp`, written in the source-facing coordinates `(x, t, τ)`. Specializing to `ι = Fin n`
recovers the textbook `n`-variable cone. -/
def logSumExpEpigraphCone : Set (E × ℝ × ℝ) :=
  (fun p : E × ℝ × ℝ ↦ (((p.2.2, p.1), p.2.1) : P × ℝ)) ⁻¹'
    constrainedEpigraph
      (Set.Ioi (0 : ℝ) ×ˢ (Set.univ : Set E))
      (fun z : P ↦ (perspectiveTransform logSumExp z : WithTop ℝ))

/-- A triple `(x, t, τ)` lies in `logSumExpEpigraphCone` exactly when `τ > 0` and
`t ≥ τ * logSumExp (τ⁻¹ • x)`. -/
theorem mem_logSumExpEpigraphCone_iff
    (x : E) (t τ : ℝ) :
    (x, t, τ) ∈ logSumExpEpigraphCone ↔
      0 < τ ∧ t ≥ τ * logSumExp (τ⁻¹ • x) := by
  rw [logSumExpEpigraphCone, Set.mem_preimage, mem_constrainedEpigraph_iff]
  simp only [Set.mem_prod, Set.mem_Ioi, Set.mem_univ, and_true]
  constructor
  · rintro ⟨hτ, ht⟩
    refine ⟨hτ, ?_⟩
    rw [perspectiveTransform_apply_of_pos logSumExp hτ] at ht
    exact_mod_cast ht
  · rintro ⟨hτ, ht⟩
    refine ⟨hτ, ?_⟩
    rw [perspectiveTransform_apply_of_pos logSumExp hτ]
    exact_mod_cast ht

end
