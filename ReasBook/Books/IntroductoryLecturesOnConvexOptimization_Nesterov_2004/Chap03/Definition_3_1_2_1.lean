/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Definition_3_3
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap06.Definition_6_1

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/- Definition 3.1.2.1 is a `bridge/view` recall in the chapter's Fenchel-conjugacy domain.

Primary domain:
- Fenchel conjugates of `ℝ ∪ {+∞}`-valued functions on real inner-product spaces.

Sampled owner-style declarations:
- project `fenchelConjugate`
- project `fenchelConjugate_apply`
- mathlib `innerₗ`
- mathlib `innerₗ_apply_apply`

Best owner abstraction:
- the source-facing owner `fenchelDual`

Primitive data:
- `f : E → WithTop ℝ`

Derived API:
- the source-facing notation `f⋆`
- the definitional supremum formula `fenchelDual_apply`

Source/core/bridge triage:
- source-facing: the textbook Fenchel conjugate for `ℝ ∪ {+∞}`-valued functions
- core/canonical: `fenchelConjugate`
- bridge/view: the canonical coercion `((↑) : WithTop ℝ → EReal)` together with
  evaluation at `innerₗ E s`

Definition 3.1.2.1 is source-facing only after specializing the dual-space owner to the
`WithTop ℝ` setting and then viewing vectors as dual functionals through `innerₗ`. The textbook
`ℝⁿ` statement is the specialization `E = EuclideanSpace ℝ (Fin n)`. This file therefore owns the
reusable source-facing bridge `fenchelDual`, equips it with the textbook notation `f⋆`, and
derives the supremum formula from the canonical owner evaluation theorem.
-/

/-- Definition 3.1.2.1: the Fenchel dual of an `ℝ ∪ {+∞}`-valued function on a real inner-product
space, obtained by evaluating `fenchelConjugate` along the Riesz map `innerₗ`. -/
abbrev fenchelDual (f : E → WithTop ℝ) : E → EReal :=
  fenchelConjugate (withTopToEReal ∘ f) ∘ innerₗ E

/- Lean spelling `f⋆` for the source-facing Fenchel dual `fenchelDual f`. -/
scoped[ConvexAnalysis] postfix:max "⋆" => fenchelDual

open scoped ConvexAnalysis

/-- Evaluating `fenchelDual f` gives the textbook supremum formula. -/
theorem fenchelDual_apply (f : E → WithTop ℝ) (s : E) :
    (f⋆) s =
      ⨆ x : E, (inner ℝ s x : EReal) - withTopToEReal (f x) := by
  rfl

end
