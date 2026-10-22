/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import Mathlib.Tactic.Recall
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap06.Theorem_6_16

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open scoped WithTopConvexAnalysis

universe u

/- Definition 6.67 is a recall-only item in the Chapter 6 second-order composite
optimality-measure domain.

Sampled owner-style declarations:
- `SecondOrderLocalModel.secondOrderOptimalityMeasure` in `Chap06/Theorem_6_16`, the chapter's
  source-facing owner for the second-order optimality measure `θ(x)`;
- `SecondOrderLocalModel.secondOrderOptimalityMeasure_def` in `Chap06/Theorem_6_16`, the
  defining `EReal` supremum expansion on `Q ∩ dom Ψ`;
- `withTopRealPart` and `dom` in `Chap03/Definition_3_3`, the canonical finite-domain bridge for
  `WithTop`-valued regularizers.

Best owner abstraction:
- `SecondOrderLocalModel.secondOrderOptimalityMeasure`.

Primitive data:
- the feasible set `Q`;
- the smooth term `f`;
- the extended-valued regularizer `Ψ`.

Derived API:
- the recalled owner
  `SecondOrderLocalModel.secondOrderOptimalityMeasure Q f Ψ :
    ↥(Q ∩ dom Ψ) → EReal`;
- the companion expansion theorem
  `SecondOrderLocalModel.secondOrderOptimalityMeasure_def`.

Source/core/bridge triage:
- source-facing: Definition 6.67's second-order optimality measure `θ(x)`;
- core/canonical: the same owner from `Theorem_6_16`;
- bridge/view: the finite-domain bridge data `dom Ψ` and `withTopRealPart Ψ`.

The previous version duplicated the owner here and left `Theorem_6_16` using a separate
real-valued `progressMeasure`. The chapter now keeps a single source-facing owner,
`SecondOrderLocalModel.secondOrderOptimalityMeasure`, and this numbered definition simply recalls
that canonical declaration.
-/

section

/- Definition 6.67: the second-order optimality measure `θ(x)` is the Chapter 6 owner
`SecondOrderLocalModel.secondOrderOptimalityMeasure`, defined on the finite feasible domain
`Q ∩ dom Ψ` and valued in `EReal`. -/
recall SecondOrderLocalModel.secondOrderOptimalityMeasure
    {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (Q : Set E) (f : E → ℝ) (Ψ : E → WithTop ℝ) :
    ↥(Q ∩ dom Ψ) → EReal

end

end
