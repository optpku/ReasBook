/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Definition_5_4_6_3
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Definition_5_4_7_9

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open scoped EntropyEpigraph

/-
Definition 5.4.7.8 lies in the Chapter 5 entropy-epigraph / cone-composition domain.

Sampled owner declarations:
* `constrainedEpigraph` and `mem_constrainedEpigraph_iff` from `Chap03/Definition_3_3`, the
  chapter owner for epigraphs over a specified feasible set;
* `ξ` and `Q₂` from `Definition_5_4_7_9`, the entropy-specific map and downstream half-space
  already used by the later barrier theorem;
* `coneCompositionFeasibleSet` and `mem_coneCompositionFeasibleSet_iff` from
  `Definition_5_4_6_3`, the chapter owner for the composed feasible-set construction;
* mathlib `ConvexCone.positive`, the canonical owner for the scalar cone `ℝ₊`.

Best owner abstraction:
* `constrainedEpigraph (Set.Ioi (0 : ℝ) ×ˢ Set.Ioi (0 : ℝ))
    (fun x : ℝ × ℝ ↦ ((-ξ x : ℝ) : WithTop ℝ))`.

Primitive data:
* the strict positive orthant in the source-facing statement of Definition 5.4.7.8;
* the entropy map `ξ`, whose negative is the relative-entropy height on that orthant.

Derived API:
* the explicit coordinate membership theorem below;
* the cone-composition identification used by the later barrier construction.

Source/core/bridge triage:
* source-facing: `entropyEpigraphCone`;
* core/canonical: `constrainedEpigraph`;
* bridge/view: `entropyEpigraphCone_eq_coneCompositionFeasibleSet`.

The later file `Definition_5_4_7_9` supplies the entropy-specific map `ξ` and the half-space
`Q₂`, while reusing the earlier Chapter 5 orthant owners directly. Definition 5.4.7.8 itself is
the open-domain source-facing constrained epigraph of relative entropy, and the cone-composition
presentation is retained only as a companion bridge for the later barrier theorem. -/

/-- Definition 5.4.7.8: the entropy-epigraph cone is the constrained epigraph of the
relative-entropy height `-ξ(x) = x^(1) [log x^(1) - log x^(2)]` on the strict positive
orthant. -/
def entropyEpigraphCone : Set ((ℝ × ℝ) × ℝ) :=
  constrainedEpigraph
    (Set.Ioi (0 : ℝ) ×ˢ Set.Ioi (0 : ℝ))
    (fun x : ℝ × ℝ ↦ ((-ξ x : ℝ) : WithTop ℝ))

/-- A triple `((x₁, x₂), z)` lies in `entropyEpigraphCone` exactly when `x₁ > 0`, `x₂ > 0`, and
`z ≥ x₁ (log x₁ - log x₂)`. -/
theorem mem_entropyEpigraphCone_iff (x₁ x₂ z : ℝ) :
    ((x₁, x₂), z) ∈ entropyEpigraphCone ↔
      x₁ > 0 ∧ x₂ > 0 ∧ z ≥ x₁ * (Real.log x₁ - Real.log x₂) := by
  rw [entropyEpigraphCone, mem_constrainedEpigraph_iff]
  constructor
  · rintro ⟨hx, hz'⟩
    have hξ : (-ξ (x₁, x₂) : ℝ) = x₁ * (Real.log x₁ - Real.log x₂) := by
      rw [entropyEpigraphRelativeEntropy_eq_neg_mul_log_sub hx.1 hx.2]
      ring
    have hz : x₁ * (Real.log x₁ - Real.log x₂) ≤ z := by
      exact_mod_cast (show (((x₁ * (Real.log x₁ - Real.log x₂) : ℝ) : WithTop ℝ) ≤ z) from by
        simpa [hξ] using hz')
    refine ⟨hx.1, hx.2, ?_⟩
    simpa using hz
  · rintro ⟨hx₁, hx₂, hz⟩
    have hξ : (-ξ (x₁, x₂) : ℝ) = x₁ * (Real.log x₁ - Real.log x₂) := by
      rw [entropyEpigraphRelativeEntropy_eq_neg_mul_log_sub hx₁ hx₂]
      ring
    have hz' : (((x₁ * (Real.log x₁ - Real.log x₂) : ℝ) : WithTop ℝ) ≤ z) := by
      exact_mod_cast hz
    refine ⟨by simpa using And.intro hx₁ hx₂, ?_⟩
    simpa [hξ] using hz'

/-- The source-facing entropy epigraph cone is exactly the chapter cone-composition feasible set
built from `ξ` and `Q₂`. -/
theorem entropyEpigraphCone_eq_coneCompositionFeasibleSet :
    entropyEpigraphCone =
      coneCompositionFeasibleSet
        (Set.Ioi (0 : ℝ) ×ˢ Set.Ioi (0 : ℝ))
        (ConvexCone.positive ℝ ℝ)
        ξ
        Q₂ := by
  ext p
  rcases p with ⟨⟨x₁, x₂⟩, z⟩
  rw [mem_entropyEpigraphCone_iff, mem_coneCompositionFeasibleSet_iff]
  constructor
  · rintro ⟨hx₁, hx₂, hz⟩
    refine ⟨ξ (x₁, x₂), ?_, ?_, ?_⟩
    · simpa using And.intro hx₁ hx₂
    · rw [ConvexCone.mem_positive]
      simp
    · rw [mem_entropyEpigraphQ2_iff]
      have hξ := entropyEpigraphRelativeEntropy_eq_neg_mul_log_sub hx₁ hx₂
      simpa [hξ, sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using
        sub_nonneg.mpr hz
  · rintro ⟨y, hx, hy, hz⟩
    have hx₁ : 0 < x₁ := by simpa using hx.1
    have hx₂ : 0 < x₂ := by simpa using hx.2
    have hy_le : y ≤ ξ (x₁, x₂) := by
      rw [ConvexCone.mem_positive] at hy
      exact sub_nonneg.mp hy
    have hyz : -y ≤ z := by
      rw [mem_entropyEpigraphQ2_iff] at hz
      exact neg_le_iff_add_nonneg.mpr <| by simpa [add_comm] using hz
    refine ⟨hx₁, hx₂, ?_⟩
    have hξ := entropyEpigraphRelativeEntropy_eq_neg_mul_log_sub hx₁ hx₂
    have hnegξ : -ξ (x₁, x₂) ≤ z := by
      calc
        -ξ (x₁, x₂) ≤ -y := neg_le_neg hy_le
        _ ≤ z := hyz
    simpa [hξ] using hnegξ
