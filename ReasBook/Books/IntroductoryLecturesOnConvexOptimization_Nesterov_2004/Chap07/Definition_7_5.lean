/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import Mathlib.Tactic.Recall
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Remark_3_1_2_3

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u

variable {E : Type u} [AddCommMonoid E] [Module ℝ E]

local notation "P" => ℝ × E

/- Definition 7.5 lies in the perspective-homogenization / unconstrained-minimization domain.

Sampled owner-style declarations:
* `perspectiveCone` in `Chap03/Remark_3_1_2_3`, the project owner of the positive cone supporting
  homogenized objectives;
* `perspectiveTransform` in `Chap03/Remark_3_1_2_3`, the project owner of the homogenized
  objective `(τ, y) ↦ τ φ(τ⁻¹ • y)`;
* `perspectiveTransform_isPositivelyHomogeneousOn` in `Chap03/Remark_3_1_2_3`, the canonical
  positive-scaling law for that homogenized objective on `perspectiveCone`;
* `IsMinOn f Set.univ x` and `isMinOn_univ_iff` in mathlib, the canonical whole-space minimizer
  language for the original problem.

Best owner abstraction:
* source-facing: the homogenized objective as the perspective transform on the perspective cone;
* core/canonical: `perspectiveTransform` together with
  `IsPositivelyHomogeneousOn 1 (perspectiveCone E : Set P)`;
* bridge/view: the unit slice `{z : P | z.1 = 1}` recovering the original objective.

Primitive data:
* the original objective `φ : E → ℝ`;
* the canonical cone owner `perspectiveCone E`;
* the canonical homogenized objective `perspectiveTransform φ`.

Derived API:
* the positive-homogeneity theorem on `perspectiveCone E`;
* evaluation on the unit slice `(1, y)`;
* the equivalence between minimizing `φ` on `E` and minimizing `perspectiveTransform φ` on the
  unit slice.

Source/core/bridge triage:
* source-facing: the homogenized perspective objective;
* core/canonical: `perspectiveTransform` on `perspectiveCone`;
* bridge/view: the unit-slice minimization statement.

The previous version collapsed Definition 7.5 to a Chapter 1
`SetConstrainedMinimizationProblem` on the affine slice `τ = 1`. That lost the chapter's actual
owner layer: the conic/perspective homogenization itself. This file therefore recalls the existing
project owner `perspectiveTransform` as the main entry and keeps the slice description only as a
bridge back to the original unconstrained problem.
-/

/- Definition 7.5: the homogenized objective of `φ` is the existing perspective transform on
`ℝ × E`, with its natural cone domain `perspectiveCone E`. -/
recall perspectiveCone
recall perspectiveTransform
recall perspectiveTransform_isPositivelyHomogeneousOn

/-- On the unit slice `τ = 1`, the perspective transform recovers the original objective `φ`. -/
@[simp] theorem perspectiveTransform_apply_one (φ : E → ℝ) (y : E) :
    perspectiveTransform φ (1, y) = φ y := by
  simp [perspectiveTransform, zero_lt_one]

/-- Minimizing `φ` on `E` is equivalent to minimizing its homogenized perspective transform on the
unit slice `τ = 1`. -/
theorem isMinOn_univ_iff_isMinOn_perspectiveTransform_unitSlice {φ : E → ℝ} {y : E} :
    IsMinOn φ Set.univ y ↔
      IsMinOn (perspectiveTransform φ) {z : P | z.1 = 1} (1, y) := by
  constructor
  · intro hy
    rw [isMinOn_iff]
    intro z hz
    rcases z with ⟨τ, x⟩
    have hy' : ∀ x : E, φ y ≤ φ x := isMinOn_univ_iff.mp hy
    have hτ : τ = 1 := hz
    subst hτ
    simpa using hy' x
  · intro hy
    rw [isMinOn_univ_iff]
    intro x
    have hx : (1, x) ∈ ({z : P | z.1 = 1} : Set P) := rfl
    simpa using (isMinOn_iff.mp hy) (1, x) hx

end
