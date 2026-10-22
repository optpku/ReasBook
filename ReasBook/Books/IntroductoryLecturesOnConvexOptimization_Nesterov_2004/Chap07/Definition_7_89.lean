/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat

-- Declarations for this item will be appended below by the statement pipeline.

universe u

/- Definition 7.89 lies in Chapter 7's scalar mixed-accuracy / approximate-solution domain.

Sampled owner-style declarations:
- `IsApproximateSolution` in `Chap03/Definition_3_34`, the scalar objective-gap owner relative to a
  chosen minimizer;
- `IsRelativeAccuracy` in `Chap07/Definition_7_1`, the chapter owner for pure relative accuracy;
- `IsMixedApproximateSolution` in `Chap07/Definition_7_90`, the direct downstream optimization
  notion that should derive its scalar accuracy data from this file instead of re-packaging it.

Best owner abstraction:
- source-facing: the scalar mixed `(ε, δ)`-accuracy relation between `hatf xBar` and `hatf xStar`;
- core/canonical: a direct `Prop` on `hatf`, `xStar`, `ε`, `δ`, and `xBar`;
- bridge/view: the constrained mixed-approximate-solution predicate in Definition 7.90.

Primitive data:
- the objective `hatf`;
- the reference point `xStar`;
- the accuracy parameters `ε` and `δ`;
- the comparison point `xBar`.

Derived API:
- the projection theorems `HasMixedAccuracy.epsilon_pos`,
  `HasMixedAccuracy.delta_mem_Ioo`, and `HasMixedAccuracy.mixed_accuracy_bound`;
- the expansion theorem `hasMixedAccuracy_iff`.

The previous version packaged three scalar inequalities as a typeclass and then re-exposed the
same conjunction through `Fact`. Those inequalities are already the full mathematical content, so
the owner surface should be the direct `Prop`, matching the chapter style for scalar
approximate-solution notions. -/

/-- Definition 7.89: `xBar` has mixed `(ε, δ)`-accuracy for the objective `hatf` with respect to
the reference point `xStar` when `ε > 0`, `δ ∈ (0, 1)`, and
`(1 - δ) * hatf xBar ≤ hatf xStar + ε`. -/
def HasMixedAccuracy {Q : Type u} (hatf : Q → ℝ) (xStar : Q) (ε δ : ℝ) (xBar : Q) : Prop :=
  0 < ε ∧
    δ ∈ Set.Ioo (0 : ℝ) 1 ∧
      (1 - δ) * hatf xBar ≤ hatf xStar + ε

namespace HasMixedAccuracy

variable {Q : Type u} {hatf : Q → ℝ} {xStar xBar : Q} {ε δ : ℝ}

/-- The additive-accuracy parameter of a mixed-accuracy hypothesis is positive. -/
theorem epsilon_pos (h : HasMixedAccuracy hatf xStar ε δ xBar) :
    0 < ε :=
  h.1

/-- The relative-accuracy parameter of a mixed-accuracy hypothesis lies in `(0, 1)`. -/
theorem delta_mem_Ioo (h : HasMixedAccuracy hatf xStar ε δ xBar) :
    δ ∈ Set.Ioo (0 : ℝ) 1 :=
  h.2.1

/-- A mixed-accuracy hypothesis supplies the defining mixed absolute-relative inequality. -/
theorem mixed_accuracy_bound (h : HasMixedAccuracy hatf xStar ε δ xBar) :
    (1 - δ) * hatf xBar ≤ hatf xStar + ε :=
  h.2.2

end HasMixedAccuracy

-- Proof sketch: unpack the three fields of `HasMixedAccuracy` in one direction, and in the
-- other direction build the structure from the displayed positivity assumptions and inequality.
/-- Expanding `HasMixedAccuracy` gives the positivity assumptions on `ε` and `δ` together with the
defining inequality `(1 - δ) * hatf xBar ≤ hatf xStar + ε`. -/
theorem hasMixedAccuracy_iff {Q : Type u} (hatf : Q → ℝ) (xStar : Q) (ε δ : ℝ) (xBar : Q) :
    HasMixedAccuracy hatf xStar ε δ xBar ↔
      0 < ε ∧ δ ∈ Set.Ioo (0 : ℝ) 1 ∧ (1 - δ) * hatf xBar ≤ hatf xStar + ε :=
  Iff.rfl
