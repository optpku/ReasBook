/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Definition_3_55
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Definition_3_75

-- Declarations for this item will be appended below by the statement pipeline.

universe u

/- Definition 3.76 lies in the chapter's sampled parametric-record-value domain.

Primary domain:
- best sampled values of the fixed-stage parametric model from Definition 3.75.

Relevant owner declarations sampled before refining:
- `bestFunctionValueUpTo` and `bestFunctionValueUpTo_le`, owned by `Definition_3_55`;
- `setConstrainedParametricObjective`, owned by `Proposition_3_52` and specialized to the fixed
  stage `(hatModel xSeq k, checkModel xSeq k)` in `Definition_3_75`;
- the fixed-stage bridge surface of `Definition_3_75`, which already treats the parametric model
  itself as derived API rather than as a second owner.

Best owner abstraction:
- source-facing/core owner: `bestFunctionValueUpTo`.

Primitive data:
- a sampled sequence `xSeq : ℕ → X`;
- upper and lower model families
  `hatModel checkModel : (ℕ → X) → ℕ → X → ℝ`;
- a stage `k`;
- a parameter `t`.

Derived API:
- the fixed-stage parametric model
  `setConstrainedParametricObjective (hatModel xSeq k) (checkModel xSeq k)`,
  then specialized at `t` and evaluated along `xSeq`;
- its sampled scalar sequence
  `(setConstrainedParametricObjective (hatModel xSeq k) (checkModel xSeq k)) t ∘ xSeq`;
- the textbook record value `f_k^*(X; t)` as the sampled-prefix minimum
  `bestFunctionValueUpTo
    (setConstrainedParametricObjective (hatModel xSeq k) (checkModel xSeq k) t ∘ xSeq) k`;
- the pointwise bound from `bestFunctionValueUpTo_le`.

Source/core/bridge triage:
- source-facing: the textbook record value `f_k^*(X; t)`;
- core/canonical: `bestFunctionValueUpTo`;
- bridge/view: the fixed-stage parametric model from Definition 3.75, evaluated along `xSeq`.

Definition 3.76 adds no new mathematical data beyond this best-prefix specialization. The file
therefore reuses `bestFunctionValueUpTo` directly and keeps the fixed-stage parametric model only
as a local bridge, with no parallel public wrapper such as `parametricRecordValue`.
-/

section

variable {X : Type u}

variable (hatModel checkModel : (ℕ → X) → ℕ → X → ℝ) (xSeq : ℕ → X) (k : ℕ) (t : ℝ)

local notation "stageObjective" =>
  setConstrainedParametricObjective (hatModel xSeq k) (checkModel xSeq k)

local notation "sampledValues" =>
  stageObjective t ∘ xSeq

/- Definition 3.76: the textbook record value `f_k^*(X; t)` is the best sampled value of the
fixed-stage parametric model from Definition 3.75. -/
#check (bestFunctionValueUpTo sampledValues k : ℝ)

/- The owner inequality bounds the record value by each sampled parametric value
`f_k(X; t, x_j)`. -/
variable (j : Fin (k + 1))

#check
  (show bestFunctionValueUpTo sampledValues k ≤ sampledValues j from
    bestFunctionValueUpTo_le j)

end
