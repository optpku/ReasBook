/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat

-- Declarations for this item will be appended below by the statement pipeline.

/- Definition 1.3.1 lies in the finite-dimensional Euclidean box domain.

Sampled owner-style declarations:
* `Set.Icc` and `Set.mem_Icc` for the scalar closed interval `[0, 1]`
* `EuclideanSpace.equiv (Fin n) ℝ`, the old coordinate-transport bridge being removed here
* the project's coordinatewise Euclidean box owners such as `coordinatewiseUnitBox` and
  `symmetricBox`, whose public surface is intrinsic rather than transported

Source/core/bridge triage:
* source-facing: the textbook box `B_n = [0,1]^n`
* core/canonical in this workspace: the intrinsic coordinatewise scalar interval condition on
  `EuclideanSpace ℝ (Fin n)`
* bridge/view: the coordinatewise membership theorem `mem_zeroOneBox_iff`

Primitive data:
* only the dimension `n`

Derived API:
* the coordinatewise membership criterion
* the origin-feasibility lemma

This removes the redundant `EuclideanSpace.equiv` transport wrapper from the owner itself while
keeping the source semantics unchanged. -/

/-- Definition 1.3.1: the textbook box `B_n = [0,1]^n` in `ℝⁿ`. -/
abbrev zeroOneBox (n : ℕ) : Set (EuclideanSpace ℝ (Fin n)) :=
  {x | ∀ i : Fin n, x i ∈ Set.Icc (0 : ℝ) 1}

/-- Membership in `zeroOneBox n` is exactly the coordinatewise interval condition. -/
-- Proof sketch: unfold membership in the defining set comprehension for `zeroOneBox`.
@[simp] theorem mem_zeroOneBox_iff {n : ℕ} {x : EuclideanSpace ℝ (Fin n)} :
    x ∈ zeroOneBox n ↔ ∀ i : Fin n, x i ∈ Set.Icc (0 : ℝ) 1 :=
  Iff.rfl

/-- The origin belongs to the textbook box `B_n = [0,1]^n`. -/
-- Proof sketch: evaluate each coordinate of the zero vector and use `Set.mem_Icc`.
theorem zeroOneBox_zero_mem (n : ℕ) :
    (0 : EuclideanSpace ℝ (Fin n)) ∈ zeroOneBox n := by
  intro i
  simp [Set.mem_Icc]
