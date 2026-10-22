/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-
Definition 1.4.11 is source-facing in first-order differential calculus over real normed spaces.

Relevant owner-style declarations sampled before refinement:
- `HasDerivWithinAt`
- `HasLineDerivAt`
- `HasLineDerivWithinAt`
- `HasFDerivAt.hasLineDerivAt`

Best owner abstraction:
- the one-variable right derivative
  `HasDerivWithinAt (fun α ↦ f (xBar + α • s)) Δ (Set.Ici (0 : ℝ)) 0`

Primitive data:
- `f`, `xBar`, `s`, and the derivative value `Δ`

Derived API:
- ambient differentiability of `f` at `xBar` gives the line-derivative owner
  `HasLineDerivAt ℝ f (fderiv ℝ f xBar s) xBar s`;
- restricting that ambient derivative at `0` to `Set.Ici 0` yields the textbook one-sided
  directional derivative along the ray.

Source/core/bridge triage:
- source-facing: the right derivative of the directional slice along the ray
  `α ↦ f (xBar + α • s)`
- core/canonical: `HasDerivWithinAt` on that scalar slice over `Set.Ici 0`
- bridge/view: the differentiability bridge through `HasLineDerivAt`

The ambient space is generalized from `ℝⁿ` to an arbitrary real normed space because no Euclidean
coordinates or finite-dimensional structure enter the owner notion or the bridge theorem. The
scalar field remains `ℝ` because the source notion is explicitly the one-sided derivative for
`α ↓ 0` on `Set.Ici 0`.
-/
recall HasDerivWithinAt
recall HasLineDerivAt
recall HasLineDerivWithinAt
recall HasFDerivAt.hasLineDerivAt

section

variable {f : E → ℝ} {xBar s : E} {Δ : ℝ}

/- Definition 1.4.11: the directional derivative of `f` at `xBar` along `s` is the right
derivative at `0` of the directional slice `α ↦ f (xBar + α • s)`. In Lean the source-facing
owner is the canonical one-variable derivative statement on `Set.Ici 0`. -/
#check (
  HasDerivWithinAt (fun α : ℝ ↦ f (xBar + α • s)) Δ (Set.Ici (0 : ℝ)) 0
)

/-- A differentiable function has the expected one-sided derivative along every ray. -/
-- Proof sketch: `hf` gives the Fréchet derivative of `f` at `xBar`, and mathlib's owner line
-- derivative API specializes this derivative to the line `α ↦ xBar + α • s`. Restricting the
-- resulting derivative at `0` to `Set.Ici 0` gives the desired one-sided derivative.
theorem hasDerivWithinAt_directionalSlice_of_differentiableAt
    (hf : DifferentiableAt ℝ f xBar) :
    HasDerivWithinAt (fun α : ℝ ↦ f (xBar + α • s)) (fderiv ℝ f xBar s) (Set.Ici (0 : ℝ)) 0 := by
  simpa [HasLineDerivAt] using (hf.hasFDerivAt.hasLineDerivAt s).hasDerivWithinAt

end
