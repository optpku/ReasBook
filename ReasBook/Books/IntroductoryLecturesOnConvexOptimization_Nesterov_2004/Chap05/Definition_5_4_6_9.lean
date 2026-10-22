/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Definition_5_0_10
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Definition_5_4_6_5

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u v w

variable {E₁ : Type u} {E₂ : Type v} {E₃ : Type w}
  [NormedAddCommGroup E₁] [NormedSpace ℝ E₁]
  [NormedAddCommGroup E₃] [NormedSpace ℝ E₃]

/- Definition 5.4.6.9 is a recall-only item in the subsection's directional differential-calculus
domain for the composed barrier `Ψ = coneCompositionBarrier F Φ ξ β`.

Sampled owner declarations:
* mathlib `lineDeriv`, the canonical first directional-derivative owner;
* `secondDirectionalDerivative` from `Definition_5_0_10`, the chapter owner for repeated second
  directional derivatives of real-valued functions;
* `thirdDirectionalDerivative` from `Definition_5_0_10`, the corresponding third-order owner;
* `coneCompositionBarrier` from `Definition_5_4_6_5`, the source-facing barrier whose
  directional derivatives are being recalled here.

Best owner abstraction:
* source-facing: the textbook quantities `D₁`, `D₂`, and `D₃` attached to `Ψ`;
* core/canonical: `lineDeriv`, `secondDirectionalDerivative`, and `thirdDirectionalDerivative`
  applied to `coneCompositionBarrier F Φ ξ β`;
* bridge/view: none beyond this direct specialization.

Primitive data:
* the barrier `F`, outer term `Φ`, map `ξ`, and parameter `β`;
* the base point `(x, z)` and direction `(h, v)`.

Derived API:
* the three canonical owner expressions for the first, second, and third directional derivatives
  of `coneCompositionBarrier F Φ ξ β`.

Definition 5.4.6.9 introduces no new owner beyond those established derivative operators, so the
file recalls the canonical applications directly instead of keeping exact-interface wrapper aliases
with `rfl` companion lemmas. -/

section

variable (F : E₁ → ℝ) (Φ : E₂ × E₃ → ℝ) (ξ : E₁ → E₂) (β : NNReal)
  (x : E₁) (z : E₃) (h : E₁) (v : E₃)

local notation "Ψ" => coneCompositionBarrier F Φ ξ β

/- Definition 5.4.6.9: for `Ψ(x, z) = Φ (ξ x, z) + β^3 F x`, the textbook quantities `D₁`, `D₂`,
and `D₃` are the following direct canonical directional-derivative owners applied to `Ψ`. -/
#check lineDeriv ℝ Ψ (x, z) (h, v)
#check secondDirectionalDerivative Ψ (x, z) (h, v)
#check thirdDirectionalDerivative Ψ (x, z) (h, v)

end

end
