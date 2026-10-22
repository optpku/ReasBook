/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Definition_5_4_6_3
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Definition_5_4_7_1
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Definition_5_4_7_5

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

/- Definition 5.4.7.4 lies in the Chapter 5 power-cone / cone-composition domain.

Sampled owner declarations:
* `powerCone` from `Definition_5_4_7_1`, the earlier chapter owner for the symmetric power cone;
* `powerConeQ1` and `powerConeGeometricMean` from `Definition_5_4_7_1`, the primitive power-cone
  data reused here;
* `qTwoPlus` / `Q₂⁺` from `Definition_5_4_7_5`, the source-facing owner/notation for the
  comparison half-space `Q₂⁺`;
* `coneCompositionFeasibleSet` from `Definition_5_4_6_3`, the generic owner for feasible sets cut
  out by a cone-order comparison;
* mathlib `ConvexCone.positive`, the canonical owner for the nonnegative ray.

Source/core/bridge triage:
* source-facing: `power_cone_plus α`, the textbook one-sided power cone `K_α^+`;
* core/canonical: `coneCompositionFeasibleSet` specialized to the power-cone data and the
  positive cone on `ℝ`;
* bridge/view: the coordinate membership lemma `mem_power_cone_plus_iff`.

Primitive data:
* the orthant `powerConeQ1 = ℝ_+²`;
* the weighted geometric mean `powerConeGeometricMean α`;
* the positive cone `ConvexCone.positive ℝ ℝ`;
* the planar comparison set `Q₂⁺ = {(y, z) | z ≤ y}`.

Derived API:
* the source-facing owner `power_cone_plus α`;
* the coordinate membership characterization below.

This refinement keeps the textbook owner `K_α^+`, but defines it through the chapter's canonical
cone-composition owner instead of repeating the existential comparison geometry entrywise. -/

open scoped QTwoPlus

/-- Definition 5.4.7.4: for `α ∈ (0, 1)`, the one-sided power cone `K_α^+` consists of the
triples `((x₁, x₂), z)` with `(x₁, x₂) ∈ ℝ_+²` and `z ≤ x₁^α x₂^(1 - α)`. -/
def power_cone_plus (α : ℝ) : Set ((ℝ × ℝ) × ℝ) :=
  coneCompositionFeasibleSet
    powerConeQ1
    (ConvexCone.positive ℝ ℝ)
    (powerConeGeometricMean α)
    Q₂⁺

namespace PowerConePlus

/- Source-facing Lean notation for the textbook one-sided power cone `K_α^+`. -/
scoped notation:max "K_[" α:arg "]⁺" => power_cone_plus α

end PowerConePlus

open scoped PowerConePlus

-- Proof sketch: expand `power_cone_plus` through `mem_coneCompositionFeasibleSet_iff`. The
-- existential witness `y` satisfies `z ≤ y ≤ powerConeGeometricMean α (x₁, x₂)`, hence
-- `z ≤ powerConeGeometricMean α (x₁, x₂)`; conversely, if
-- `z ≤ powerConeGeometricMean α (x₁, x₂)`, choose `y = z`.
/-- A triple `((x₁, x₂), z)` lies in `K_[α]⁺` exactly when `x₁, x₂ ≥ 0` and
`z ≤ x₁^α x₂^(1 - α)`, equivalently `z ≤ powerConeGeometricMean α (x₁, x₂)`. -/
theorem mem_power_cone_plus_iff (α x₁ x₂ z : ℝ) :
    ((x₁, x₂), z) ∈ K_[α]⁺ ↔
      0 ≤ x₁ ∧ 0 ≤ x₂ ∧ z ≤ powerConeGeometricMean α (x₁, x₂) := by
  rw [power_cone_plus, mem_coneCompositionFeasibleSet_iff]
  constructor
  · rintro ⟨y, hQ1, hy, hyz⟩
    rw [mem_powerConeQ1_iff] at hQ1
    have hy' : y ≤ powerConeGeometricMean α (x₁, x₂) := by
      simpa [sub_nonneg] using hy
    exact ⟨hQ1.1, hQ1.2, le_trans hyz hy'⟩
  · rintro ⟨hx₁, hx₂, hz⟩
    refine ⟨z, (mem_powerConeQ1_iff x₁ x₂).2 ⟨hx₁, hx₂⟩, ?_, ?_⟩
    · simpa [sub_nonneg] using hz
    · exact (mem_qTwoPlus_iff z z).2 le_rfl
