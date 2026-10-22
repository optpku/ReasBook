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

/- Definition 5.4.6.5 lies in the subsection's composed-barrier domain.

Sampled owner declarations:
* ordinary product-space function evaluation, the canonical ambient owner layer for a barrier on
  `E₁ × E₃`;
* `coneCompositionFeasibleSet` from `Definition_5_4_6_3`, the adjacent source-facing set owner
  paired with this barrier later in the subsection;
* `compositionPotential` from `Definition_5_4_6_6`, the nearby source-facing owner for the
  unweighted term `(x, z) ↦ Φ (ξ x, z)`;
* the downstream canonical directional-derivative owners from `Definition_5_4_6_9`, obtained by
  applying `lineDeriv`, `secondDirectionalDerivative`, and `thirdDirectionalDerivative` to this
  barrier.

Source/core/bridge triage:
* source-facing: `coneCompositionBarrier F Φ ξ β`;
* core/canonical: the plain function `E₁ × E₃ → ℝ`;
* bridge/view: the pointwise evaluation lemma below.

Primitive data:
* the inner barrier `F`;
* the outer barrier `Φ`;
* the map `ξ`;
* the parameter `β`.

Derived API:
* the pointwise formula for evaluating the owner function.

No higher packaged abstraction is needed here: the mathematics is exactly the concrete barrier
function on the product space, so the refined owner remains the plain function with a single
atomic evaluation lemma. The redundant extensionality wrapper is deleted in favor of the owner
definition itself. -/

/-- Definition 5.4.6.5: given a barrier `F` on `Q₁`, a barrier `Φ` on `Q₂`, a map `ξ : Q₁ → E₂`,
and a compatibility parameter `β`, the composed barrier on pairs `(x, z)` is
`Ψ(x, z) = Φ(ξ(x), z) + β^3 F(x)`. -/
def coneCompositionBarrier
    (F : E₁ → ℝ) (Φ : E₂ × E₃ → ℝ) (ξ : E₁ → E₂) (β : NNReal) : E₁ × E₃ → ℝ :=
  fun p ↦ Φ (ξ p.1, p.2) + ((β : ℝ) ^ 3) * F p.1

-- Proof sketch: unfold `coneCompositionBarrier`; the definition evaluates `Φ` at the pair
-- `(ξ x, z)` and adds the scaled barrier term `β^3 F x`.
/-- Evaluating `coneCompositionBarrier F Φ ξ β` at `(x, z)` reproduces the textbook formula
`Ψ(x, z) = Φ(ξ(x), z) + β^3 F(x)`. -/
@[simp] theorem coneCompositionBarrier_apply
    (F : E₁ → ℝ) (Φ : E₂ × E₃ → ℝ) (ξ : E₁ → E₂) (β : NNReal) (x : E₁) (z : E₃) :
    coneCompositionBarrier F Φ ξ β (x, z) = Φ (ξ x, z) + ((β : ℝ) ^ 3) * F x :=
  rfl

end
