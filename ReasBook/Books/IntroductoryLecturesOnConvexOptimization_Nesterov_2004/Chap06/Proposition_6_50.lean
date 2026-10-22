/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap06.Definition_6_67

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open scoped SecondOrderLocalModel.SecondOrderOptimalityMeasureNotation WithTopConvexAnalysis
open SecondOrderLocalModel

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/- Proposition 6.50 lies in the Chapter 6 second-order composite optimality-measure domain.

Sampled owner-style declarations:
- `SecondOrderLocalModel.secondOrderOptimalityMeasure` in `Chap06/Theorem_6_16`, the chapter
  owner of the second-order optimality measure `θ(x)`;
- the scoped notation `θ[Q, f, Ψ](x)` in `Chap06/Theorem_6_16`, the source-facing theorem surface
  for that owner;
- `SecondOrderLocalModel.secondOrderOptimalityMeasure_def` in `Chap06/Theorem_6_16`, the direct
  bridge from that owner to its defining supremum over `Q ∩ dom Ψ`;
- `dom` and `withTopRealPart` in `Chap03/Definition_3_3`, the canonical finite-value bridge for
  `WithTop ℝ`-valued regularizers;
- mathlib `le_sSup`, the canonical complete-lattice introduction rule for lower bounds of a
  supremum.

Best owner abstraction:
- source-facing/core-canonical: `secondOrderOptimalityMeasure Q f Ψ`;
- theorem-surface notation: `θ[Q, f, Ψ](x)`;
- bridge/view: `secondOrderOptimalityMeasure_def`.

Primitive data:
- the feasible set `Q`, smooth term `f`, regularizer `Ψ`, and finite feasible point
  `x : ↥(Q ∩ dom Ψ)`.

Derived API:
- the source-facing notation `θ[Q, f, Ψ](x)` for the owner evaluated at `x`;
- the nonnegativity statement below, obtained by evaluating the defining supremum at the base
  point `y = x`.

Source/core/bridge triage:
- source-facing: Proposition 6.50's claim `0 ≤ θ(x)`;
- core/canonical: `secondOrderOptimalityMeasure`;
- bridge/view: `secondOrderOptimalityMeasure_def`.

The proposition does not use finite dimensionality. The canonical owner already lives over the
weaker `[CompleteSpace E]` context, so this file stays on that owner surface and proves the
nonnegativity claim directly from the defining supremum instead of adding any local wrapper.
-/

-- Proof sketch: rewrite `θ[Q, f, Ψ](x)` through
-- `SecondOrderLocalModel.secondOrderOptimalityMeasure_def`. Because `x ∈ dom Ψ`, the candidate
-- `y = x` belongs to the index set `Q ∩ dom Ψ`; the linear and quadratic terms vanish at zero
-- displacement, and the remaining finite-value term `withTopRealPart Ψ x - withTopRealPart Ψ x`
-- is zero.
/-- Proposition 6.50: under the assumptions of Definition 6.67, the second-order optimality
measure `θ(x)` is nonnegative at every finite feasible point `x ∈ Q ∩ dom Ψ`. -/
theorem secondOrderOptimalityMeasure_nonneg
    (Q : Set E) (f : E → ℝ) (Ψ : E → WithTop ℝ) (x : ↥(Q ∩ dom Ψ)) :
    0 ≤ θ[Q, f, Ψ](x) := by
  rw [secondOrderOptimalityMeasure_def]
  refine le_sSup ?_
  refine ⟨(x : E), x.2, ?_⟩
  simp

end
