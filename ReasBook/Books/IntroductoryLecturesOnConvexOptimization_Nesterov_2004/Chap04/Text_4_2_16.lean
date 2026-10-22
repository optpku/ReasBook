/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat

-- Declarations for this item will be appended below by the statement pipeline.

universe u

/- Text 4.2.16 lives in the chapter's whole-space minimization domain.

Sampled owner declarations:
* mathlib `IsMinOn`, the canonical owner of whole-space minimality;
* mathlib `isMinOn_univ_iff`, the textbook bridge `IsMinOn f Set.univ xStar ↔ ∀ x, f xStar ≤ f x`;
* Chapter 2 `Definition_2_1`, which already fixes `IsMinOn f Set.univ xStar` as the project's
  source-facing owner for unconstrained minimizers.

Best owner abstraction:
* `IsMinOn f Set.univ xStar`

Primitive data:
* the objective `f`;
* the iterate sequence `x`;
* the minimizer witness `hxStar : IsMinOn f Set.univ xStar`;
* the two indices `hatK` and `N + 1` whose objective values are compared.

Derived API:
* the pointwise inequality `f xStar ≤ f (x (N + 1))`, obtained from the minimizer owner.

Source/core/bridge triage:
* source-facing: the comparison between the gap at the displayed iterate and the gap to `x_{N+1}`;
* core/canonical: `IsMinOn f Set.univ xStar`;
* bridge/view: the textbook pointwise inequality recovered from the owner predicate.

The arithmetic relation identifying `hatK` with the two-thirds index is not used in this
comparison itself, so the refined public statement drops that redundant binder and keeps only the
canonical minimizer data that actually drives the inequality.
-/

-- Proof sketch: use the canonical bridge `isMinOn_univ_iff` at `x (N + 1)` to get
-- `f xStar ≤ f (x (N + 1))`, then apply monotonicity of left subtraction by `f (x hatK)`.
/-- Text 4.2.16: if `xStar` is a global minimizer of `f`, then the objective gap at any iterate
`x_hatK` dominates the gap from the same iterate to the later point `x_{N+1}`. In the textbook
application, `hatK` is the two-thirds index from the preceding step. -/
theorem false_acceleration_gap_ge_gap_to_next_iterate_of_isMinOn
    {E : Type u} (f : E → ℝ) (x : ℕ → E) (xStar : E) (N hatK : ℕ)
    (hxStar : IsMinOn f Set.univ xStar) :
    f (x hatK) - f xStar ≥ f (x hatK) - f (x (N + 1)) := by
  have hxStar_le : f xStar ≤ f (x (N + 1)) := (isMinOn_univ_iff.mp hxStar) (x (N + 1))
  simpa [ge_iff_le] using sub_le_sub_left hxStar_le (f (x hatK))
