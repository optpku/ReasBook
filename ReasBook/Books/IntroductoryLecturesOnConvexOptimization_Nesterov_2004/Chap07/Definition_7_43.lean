/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap02.Lemma_2_18
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap01.Definition_1_10_2

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open EuclideanSpace (nonnegativeOrthant)
open scoped BigOperators

variable {ι : Type*} [Fintype ι] [Nonempty ι] {n : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin n)

/- Definition 7.43 lies in the chapter's finite max-type / weighted absolute-coordinate domain.

Sampled owner-style declarations:
- `maxTypeObjective` and `maxTypeObjective_apply` in `Chap02/Lemma_2_18`, the project owner and
  evaluation bridge for pointwise maxima of nonempty finite families;
- `maxAbsoluteValueOptimizationObjective` in `Chap06/Definition_6_21`, the nearby source-facing
  pattern of introducing a chapter objective by specializing `maxTypeObjective`;
- `minMaxAbsoluteDeviationObjective` in `Chap07/Definition_7_36`, the Chapter 7 pattern of
  keeping a source-facing owner while delegating its finite-max structure upstream.

Best owner abstraction:
- source-facing: `maxWeightedAbsoluteCoordinateSum`, since Definition 7.43 introduces this
  weighted max-absolute-coordinate objective itself;
- core/canonical: `maxTypeObjective`;
- bridge/view: `maxWeightedAbsoluteCoordinateSum_apply` and
  `maxWeightedAbsoluteCoordinateSumOfOrthant`.

Primitive data:
- the nonempty finite index type `ι`;
- the nonnegative coefficient family `a : ι → Fin n → NNReal`.

Derived API:
- the source-facing objective below;
- its evaluation theorem;
- the orthant-valued bridge `maxWeightedAbsoluteCoordinateSumOfOrthant`.

This file keeps the textbook Chapter 7 owner but deletes the bespoke `Finset.sup'` wheel from the
public implementation. The finite-max structure is now supplied canonically by `maxTypeObjective`,
and the max-family index is exposed at the chapter's standard nonempty finite-family layer rather
than the over-concrete display model `Fin (m : ℕ)`.
-/

/-- Definition 7.43: for a nonempty finite family of nonnegative coefficient vectors
`aᵢ ∈ ℝⁿ_+`, the homogeneous function `\hat f : ℝⁿ → ℝ` is the finite maximum of the weighted
absolute-coordinate sums `∑ⱼ aᵢ⁽ʲ⁾ |x⁽ʲ⁾|`. -/
def maxWeightedAbsoluteCoordinateSum
    (a : ι → Fin n → NNReal) : E → ℝ :=
  maxTypeObjective fun i x ↦ ∑ j : Fin n, (a i j : ℝ) * |x j|

/-- Evaluating `maxWeightedAbsoluteCoordinateSum a` at `x` gives the defining finite maximum
`maxᵢ ∑ⱼ aᵢ⁽ʲ⁾ |x⁽ʲ⁾|`. -/
-- Proof sketch: specialize the canonical evaluation theorem `maxTypeObjective_apply` to the
-- weighted absolute-coordinate family `i ↦ ∑ⱼ aᵢ⁽ʲ⁾ |x⁽ʲ⁾|`.
theorem maxWeightedAbsoluteCoordinateSum_apply
    (a : ι → Fin n → NNReal) (x : E) :
    maxWeightedAbsoluteCoordinateSum a x =
      Finset.univ.sup' Finset.univ_nonempty (fun i : ι ↦
        ∑ j : Fin n, (a i j : ℝ) * |x j|) := by
  simpa [maxWeightedAbsoluteCoordinateSum] using
    (maxTypeObjective_apply
      (fun i (y : E) ↦ ∑ j : Fin n, (a i j : ℝ) * |y j|) x)

/-- The same Chapter 7 objective, now read from a family of coefficient vectors in the canonical
orthant owner `ℝⁿ_+`. This is the source-facing bridge from orthant-valued data to the core
`NNReal` owner `maxWeightedAbsoluteCoordinateSum`. -/
abbrev maxWeightedAbsoluteCoordinateSumOfOrthant
    (a : ι → E) (ha : ∀ i : ι, a i ∈ nonnegativeOrthant n) : E → ℝ :=
  maxWeightedAbsoluteCoordinateSum fun i j ↦
    ⟨a i j, by
      have hai : ∀ j : Fin n, 0 ≤ a i j := by
        simpa using ha i
      exact hai j⟩

end
