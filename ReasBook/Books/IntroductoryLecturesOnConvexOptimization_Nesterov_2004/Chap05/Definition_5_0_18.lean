/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import Mathlib.Tactic.Recall
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Theorem_3_1_2_3

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u v w

open scoped ConvexAnalysis

variable {E₁ : Type u} {E₂ : Type v}

/- Definition 5.0.18 lies in the chapter's partial-minimization / infimal-projection domain.

Primary domain:
* fiberwise infima of a partial objective `Φ : E₁ × E₂ → ℝ` over a feasible set
  `domΦ ⊆ E₁ × E₂`

Sampled owner-style declarations:
* chapter `partialInfProjection` in `Chap03/Theorem_3_1_2_3`, the canonical owner of constrained
  fiberwise infima with `EReal` values
* chapter `partialInfProjection_eq_sInf` in `Chap03/Theorem_3_1_2_3`, the owner specification
  theorem on the fiber in `E₁ × E₂`
* chapter `extendedRealRealPart` in `Chap03/Definition_3_1_1_3`, the finite-value bridge from
  `EReal` to `ℝ`
* chapter `extendedRealRealPart_partialInfProjection_eq_sInf` in
  `Chap03/Theorem_3_1_2_3`, the finite-real-part bridge for the fiberwise infimum

Best owner abstraction:
* core/canonical: `partialInfProjection domΦ (Real.toEReal ∘ Φ)`
* source-facing: its finite real part `extendedRealRealPart` on
  `dom (partialInfProjection domΦ (Real.toEReal ∘ Φ))`
* bridge/view: the `y`-fiber reformulation
  `extendedRealRealPart_partialInfProjection_eq_sInf_image`

Primitive data:
* the feasible relation `domΦ : Set (E₁ × E₂)`
* the real-valued partial objective `Φ : E₁ × E₂ → ℝ`

Derived API:
* the canonical Chapter 3 infimal projection
* its finite-value domain `dom (partialInfProjection domΦ (Real.toEReal ∘ Φ))`
* the real-surface bridge theorem below

Source/core/bridge triage:
* source-facing: the finite real value of the partial-minimization problem at a base point `x`
* core/canonical: `partialInfProjection domΦ (Real.toEReal ∘ Φ)`
* bridge/view: `extendedRealRealPart_partialInfProjection_eq_sInf_image`

This file therefore introduces no parallel public `valueFunction` owner. The partial value
function is the Chapter 3 owner `partialInfProjection`, and the textbook real-valued surface is
obtained only on its finite-value domain via `extendedRealRealPart`.
-/

section

variable (domΦ : Set (E₁ × E₂)) (Φ : E₁ × E₂ → ℝ) (x : E₁)

/- Definition 5.0.18: the partial-minimization value function is the canonical Chapter 3
infimal-projection owner `partialInfProjection domΦ (Real.toEReal ∘ Φ)`, with real values
recovered on its finite-value domain by `extendedRealRealPart`. -/
recall partialInfProjection
recall extendedRealRealPart
recall extendedRealRealPart_partialInfProjection_eq_sInf

set_option linter.hashCommand false in
#check (dom (partialInfProjection domΦ (Real.toEReal ∘ Φ)) : Set E₁)

set_option linter.hashCommand false in
#check (extendedRealRealPart (partialInfProjection domΦ (Real.toEReal ∘ Φ)) : E₁ → ℝ)

end

private theorem pairFiber_image_eq_secondFiber_image
    {α : Type w} (domΦ : Set (E₁ × E₂)) (Φ : E₁ × E₂ → α) (x : E₁) :
    Φ '' {z : E₁ × E₂ | z ∈ domΦ ∧ z.1 = x} =
      (fun y : E₂ ↦ Φ (x, y)) '' {y | (x, y) ∈ domΦ} := by
  ext r
  constructor
  · rintro ⟨⟨x', y⟩, hz, rfl⟩
    rcases hz with ⟨hxy, rfl⟩
    exact ⟨y, hxy, rfl⟩
  · rintro ⟨y, hy, rfl⟩
    exact ⟨(x, y), ⟨hy, rfl⟩, rfl⟩

/-- On the finite-value domain of the canonical Chapter 3 infimal projection, the real part of
the partial value function agrees with the textbook infimum of `Φ (x, y)` over the feasible
second-coordinate fiber above `x`. -/
theorem extendedRealRealPart_partialInfProjection_eq_sInf_image
    {domΦ : Set (E₁ × E₂)} {Φ : E₁ × E₂ → ℝ} {x : E₁}
    (hx : x ∈ dom (partialInfProjection domΦ (Real.toEReal ∘ Φ))) :
    extendedRealRealPart (partialInfProjection domΦ (Real.toEReal ∘ Φ)) x =
      sInf ((fun y : E₂ ↦ Φ (x, y)) '' {y | (x, y) ∈ domΦ}) := by
  rw [extendedRealRealPart_partialInfProjection_eq_sInf hx]
  rw [pairFiber_image_eq_secondFiber_image domΦ Φ x]

end
