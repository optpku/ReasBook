/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Definition_3_55

-- Declarations for this item will be appended below by the statement pipeline.

universe u

variable {α : Type u}

/- Definition 3.58 lies in the chapter's best-feasible-value / selected-sequence domain.

Primary domain:
- best feasible objective values along an already selected feasible sequence.

Relevant owner declarations sampled before refining:
- `bestFunctionValueUpTo` in `Definition_3_55`, the earlier chapter recall of best-so-far
  objective values;
- `bestFunctionValueUpTo_le` in `Definition_3_55`, the earlier chapter recall of the owner
  inequality for prefix evaluation.

Best owner abstraction:
- core/canonical owner: `bestFunctionValueUpTo`, already recalled in `Definition_3_55`;
- bridge/view: specialize it to the objective sequence `fun j ↦ values (X j)`.

Primitive data:
- a selected feasible sequence `X : ℕ → α`;
- an objective `values : α → ℝ`;
- a prefix index `k : ℕ`.

Derived API:
- the best feasible objective value `bestFunctionValueUpTo (fun j ↦ values (X j)) k`;
- the pointwise upper bound of that best feasible value by each sampled feasible value.

Source/core/bridge triage:
- source-facing: best feasible values along the selected feasible sequence `X`;
- core/canonical: `bestFunctionValueUpTo`;
- bridge/view: the specialization `fun j ↦ values (X j)`.

This file is therefore a bridge/view use of the earlier chapter recall: Definition 3.58 is the
direct owner specialization of `bestFunctionValueUpTo` along a feasible sequence, not a second
owner or a second recall layer built from the same prefix-infimum API. -/

section

variable {X : ℕ → α}
variable (values : α → ℝ) (k : ℕ)

local notation "sampledValues" => values ∘ X

/- Definition 3.58: for a feasible sequence `X`, the best feasible objective value up to step
`k` is the direct owner specialization below. -/
#check (bestFunctionValueUpTo sampledValues k : ℝ)

/- The owner inequality bounds the best feasible value by each sampled feasible value among the
first `k + 1` selected terms. -/
variable (j : Fin (k + 1))

#check
  (show bestFunctionValueUpTo sampledValues k ≤ sampledValues j from
    bestFunctionValueUpTo_le j)

end
