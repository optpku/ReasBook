/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import Mathlib.Tactic.Recall
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Definition_3_75

-- Declarations for this item will be appended below by the statement pipeline.

universe u

/-
Lemma 3.38 lies in the chapter's set-constrained scalar parametric max-value-function domain.

Sampled owner-style declarations:
- `parametricValueFunction` in `Chap03/Lemma_3_3_6`, the chapter owner for the feasible-set
  infimum of `x ↦ max (f x - t) (barf x)`;
- `parametricValueFunction_sub_le_shift` in `Chap03/Lemma_3_3_6`, the owner shift bound for one
  model `f`;
- `Definition_3_75` in `Chap03/Definition_3_75`, where the textbook approximate value
  `\hat f_k^*(X; ·)` is already identified with the specialization
  `parametricValueFunction Q (hatModel xSeq k) (checkModel xSeq k)`;
- `LagrangianProblem.constrainedAuxiliaryOptimalValue_shift_bounds` in `Chap02/Lemma_2_22`, the
  matching owner-style shift bound for the same max-type infimum pattern in the Chapter 2
  constrained auxiliary-value setting.

Best owner abstraction:
- `parametricValueFunction Q f barf`

Primitive data:
- feasible set `Q`;
- exact model `f`;
- stage model pair `(hatModel xSeq k, checkModel xSeq k)`;
- parameters `t` and `Δ`.

Derived API:
- the owner shift theorem `parametricValueFunction_sub_le_shift`;
- the textbook approximate case is the stage-`k` specialization already recognized in
  `Definition_3_75`.

Source/core/bridge triage:
- source-facing: the exact-value shift inequality together with its stage-`k` approximate-model
  specialization;
- core/canonical: `parametricValueFunction_sub_le_shift`;
- bridge/view: the `Definition_3_75` stage-`k` specialization of the textbook approximate
  notation.

This file therefore reuses the exact-value statement by direct recall of the owner theorem and
keeps only the stage-`k` specialization as a separate bridge theorem.
-/

/- Lemma 3.38, exact-value part: direct reuse of the chapter owner shift theorem. -/
recall parametricValueFunction_sub_le_shift

section

variable {X : Type u}
variable (Q : Set X)
variable (hatModel checkModel : (ℕ → X) → ℕ → X → ℝ) (xSeq : ℕ → X) (k : ℕ)

/-- Lemma 3.38, approximate-value part: the stage-`k` model value from `Definition_3_75`
satisfies the same parameter-shift bound as the exact owner value. -/
theorem stageParametricValueFunction_sub_le_shift
    {Δ t : ℝ} (hΔ : 0 ≤ Δ) :
    parametricValueFunction Q (hatModel xSeq k) (checkModel xSeq k) t - Δ ≤
      parametricValueFunction Q (hatModel xSeq k) (checkModel xSeq k) (t + Δ) :=
  parametricValueFunction_sub_le_shift Q (hatModel xSeq k) (checkModel xSeq k) Δ t hΔ

end
