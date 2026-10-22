/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Theorem_5_1_4

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

/- Chapter 5 planar half-space / logarithmic-barrier context for this item.

Sampled owner declarations:
* `sublevelLogBarrier` from `Theorem_5_1_4`, the chapter owner for barriers of the form
  `x ↦ -log (β - f x)`;
* `powerConeQ2` from `Definition_5_4_7_1`, the neighboring planar comparison-set owner;
* `qTwoBarrier` from `Definition_5_4_7_2`, the neighboring planar-cone barrier recall;
* mathlib set-builder half-spaces, the canonical owner layer for affine half-space domains.

Source/core/bridge triage:
* source-facing: `qTwoPlus`, with notation `Q₂⁺`, for the textbook half-space
  `Q₂⁺ = {(y, z) | z ≤ y}`;
* core/canonical: `sublevelLogBarrier (fun yz ↦ yz.2 - yz.1) 0`;
* bridge/view: the membership theorem and the pointwise evaluation theorem.

Primitive data:
* the source-facing half-space `Q₂⁺`.

Derived API:
* the recalled canonical barrier specialization
  `sublevelLogBarrier (fun yz : ℝ × ℝ ↦ yz.2 - yz.1) 0`;
* the source-facing membership and evaluation lemmas below.

This file therefore keeps `Q₂⁺` as the source-facing owner and reuses the chapter barrier owner
directly. The barrier clause of the numbered item is presented as a canonical recall, rather than
through a second public logarithmic-barrier alias. The textbook parameter `μ = 1` is already the
literal canonical parameter value, so no separate owner or bridge declaration is introduced for
it. -/

/-- The one-sided planar comparison set `Q₂⁺ = {(y, z) : z ≤ y}`. -/
def qTwoPlus : Set (ℝ × ℝ) :=
  {yz | yz.2 ≤ yz.1}

namespace QTwoPlus

/- Source-facing Lean notation for the textbook half-space `Q₂⁺`. -/
scoped notation:max "Q₂⁺" => qTwoPlus

end QTwoPlus

open scoped QTwoPlus

-- Proof sketch: unfold `qTwoPlus`; membership is exactly the defining inequality `z ≤ y` for the
-- half-space `Q₂⁺`.
/-- A pair `(y, z)` belongs to `Q₂⁺` exactly when `z ≤ y`. -/
theorem mem_qTwoPlus_iff (y z : ℝ) :
    (y, z) ∈ Q₂⁺ ↔ z ≤ y := by
  rfl

set_option linter.hashCommand false in
/- Definition 5.4.7.5 recalls the canonical logarithmic barrier specialization for
`Q₂⁺ = {(y, z) : z ≤ y}`. -/
#check (sublevelLogBarrier (fun yz : ℝ × ℝ ↦ yz.2 - yz.1) 0 : (ℝ × ℝ) → ℝ)

-- Proof sketch: apply `sublevelLogBarrier_apply` to the affine function
-- `fun yz : ℝ × ℝ ↦ yz.2 - yz.1` and rewrite `0 - (z - y)` as `y - z`.
/-- Evaluating the recalled barrier specialization at `(y, z)` recovers the textbook formula
`Phi^+(y, z) = -log (y - z)`. -/
theorem qTwoPlus_sublevelLogBarrier_apply (y z : ℝ) :
    sublevelLogBarrier (fun yz ↦ yz.2 - yz.1) 0 (y, z) = -Real.log (y - z) := by
  rw [sublevelLogBarrier_apply]
  ring_nf

end
