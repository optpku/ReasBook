/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u v w

variable {E₁ : Type u} {E₂ : Type v} {E₃ : Type w}

/- Definition 5.4.6.6 lies in the subsection's basic product-composition domain.

Sampled owner declarations:
* `fderiv`, the canonical mathlib owner for the auxiliary derivative term `Dξ(x)[h]`;
* `Prod.map`, the canonical product-map owner packaging `(x, z) ↦ (ξ x, z)`;
* `coneCompositionBarrier` in `Definition_5_4_6_5`, an adjacent source-facing owner file whose
  public API is a named function together with atomic evaluation lemmas.

Source/core/bridge triage:
* source-facing: the textbook potential `ψ(x, z) = Φ (ξ x, z)`;
* core/canonical: `Φ ∘ Prod.map ξ id`, while the auxiliary direction
  `l = (Dξ(x)[h], v)` is already the canonical pair `(fderiv ℝ ξ x h, v)`;
* bridge/view: the atomic evaluation lemma below.

Primitive data:
* the outer scalar map `Φ`;
* the map `ξ`.

Derived API:
* the canonical product-map composite for the source-facing potential.

The auxiliary lifted direction from the source,
`l = (Dξ(x)[h], v)`, is already the canonical pair `(fderiv ℝ ξ x h, v)`, so this file keeps no
separate public wrapper for it. -/

section CompositionPotential

variable (Φ : E₂ × E₃ → ℝ) (ξ : E₁ → E₂) (x : E₁) (z : E₃)

/-- Definition 5.4.6.6 (2): the textbook scalar potential `ψ(x, z) = Φ (ξ x, z)`. -/
abbrev compositionPotential : E₁ × E₃ → ℝ :=
  Φ ∘ Prod.map ξ id

/-- Evaluating `compositionPotential Φ ξ` at `(x, z)` recovers `Φ (ξ x, z)`. -/
@[simp] theorem compositionPotential_apply :
    compositionPotential Φ ξ (x, z) = Φ (ξ x, z) :=
  rfl

end CompositionPotential
