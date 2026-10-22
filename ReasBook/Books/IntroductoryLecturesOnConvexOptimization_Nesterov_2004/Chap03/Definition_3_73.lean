/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Definition_3_65

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u

variable {E : Type u} [SeminormedAddCommGroup E] [InnerProductSpace ℝ E]

open scoped NonsmoothModelNotation

/- Definition 3.73 lies in the chapter's sampled max-affine lower-model domain.

Primary domain:
- sampled max-affine lower models in convex nonsmooth optimization.

Relevant owner-style declarations sampled before refining:
- `nonsmoothModel` in `Lemma_3_3_2`, recalled in `Definition_3_65`
- `nonsmoothModel_apply` in `Lemma_3_3_2`, recalled in `Definition_3_65`
- `maxTypeObjective_le_iff` in `Chap02/Lemma_2_18`, the canonical owner-level criterion for
  bounding a finite maximum by a pointwise upper bound
- `maxTypeObjective` and `maxTypeObjective_apply` in `Chap02/Lemma_2_18`, the ambient finite-max
  owner pattern specialized upstream by `nonsmoothModel`

Best owner abstraction:
- `nonsmoothModel φ X g k`

Primitive data:
- the base function `φ : E → ℝ`
- the sample sequence `X : ℕ → E`
- the sampled affine slopes `g : ℕ → E`
- the stage `k : ℕ`

Derived API:
- the source-facing specializations `f̂[X; f; g](k)` and `f̂[X; fBar; gBar](k)`
- the owner-level domination companion `nonsmoothModel_le_on`, derived through
  `maxTypeObjective_le_iff`

Source/core/bridge triage:
- source-facing: the textbook sampled models `f̂[X; f; g](k) = \hat f_k(X; ·)` and
  `f̂[X; fBar; gBar](k) = \check f_k(X; ·)`
- core/canonical: `nonsmoothModel`
- bridge/view: `nonsmoothModel_apply` and `nonsmoothModel_le_on`

This file therefore keeps the two source-facing model objects as direct specializations of the
chapter owner `nonsmoothModel` and leaves the domination theorem as a companion. It introduces no
parallel public aliases such as `hatCuttingPlaneModel` or `checkCuttingPlaneModel`. -/

section

variable (φ : E → ℝ) (X : ℕ → E) (g : ℕ → E) (k : ℕ)

/- Definition 3.73: both textbook sampled models `\hat f_k(X; ·)` and `\check f_k(X; ·)` are
direct owner specializations of the same chapter owner `nonsmoothModel`, obtained by
instantiating `(φ, g)` with `(f, g)` and `(fBar, gBar)` respectively. -/
#check (f̂[X; φ; g](k) : E → ℝ)

end

variable
    {X : ℕ → E}
    {φ : E → ℝ}
    {g : ℕ → E}
    {k : ℕ}

/-- Companion domination theorem for the owner `nonsmoothModel`: on a feasible set `Q`, the
sampled max-affine model stays below `φ` whenever each sampled affine minorant stays below `φ` on
`Q`. Instantiating `φ` with `f` and `fBar` gives the textbook inequalities
`\hat f_k(X; x) ≤ f(x)` and `\check f_k(X; x) ≤ \bar f(x)` for all `x ∈ Q`. -/
-- Proof sketch: unfold the owner specialization `nonsmoothModel` to the finite-max owner
-- `maxTypeObjective`; every sampled affine minorant is bounded above by `φ x` via `hminor j hx`,
-- then apply the owner criterion
-- `maxTypeObjective_le_iff` to pass from the componentwise bounds to the model bound.
theorem nonsmoothModel_le_on
    {Q : Set E}
    (hminor : ∀ j : Fin (k + 1), ∀ ⦃y : E⦄, y ∈ Q →
      φ (X j) + inner ℝ (g j) (y - X j) ≤ φ y)
    (x : E) (hx : x ∈ Q) :
    f̂[X; φ; g](k) x ≤ φ x := by
  simpa [nonsmoothModel] using
    (maxTypeObjective_le_iff
      (fun j : Fin (k + 1) ↦ fun y ↦ φ (X j) + inner ℝ (g j) (y - X j))
      x (φ x)).2
      (fun j ↦ hminor j hx)

end
