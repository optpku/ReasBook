/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap02.Definition_2_12

-- Declarations for this item will be appended below by the statement pipeline.

open scoped CoordinateSubspace

section

variable {n : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin n)

/- Primary domain: linear-algebraic coordinate subspaces in `ℝⁿ`.

Sampled owner-style declarations in this domain:
- `coordinateSubspace k n`, the chapter’s canonical `Submodule` owner for `ℝ^{k,n}`;
- `mem_coordinateSubspace_iff`, the canonical coordinatewise membership criterion;
- `Submodule.span`, the owner construction for the linear span of the first `k` vectors in a
  sequence;
- `Submodule.span_le`, the canonical way to prove a span lies in a target submodule.

Best owner abstraction:
- source-facing/core: a sequence `g : ℕ → E` together with the coordinate-subspace hypothesis
  `g j ∈ ℝ^{j.1 + 1,n}` on the relevant prefix `j : Fin k`;
- bridge/view: any later specialization `g j = ∇ f (x j)`.

Primitive data:
- the ambient Euclidean space `E`,
- the sequence `g`,
- the hypothesis that each prefix term `g j` for `j : Fin k` already belongs to the appropriate
  owner `coordinateSubspace (j.1 + 1) n`.

Derived API:
- `mem_coordinateSubspace_iff`, which upgrades membership from `ℝ^{j.1 + 1,n}` to `ℝ^{k,n}` by
  comparing the coordinate-vanishing ranges when `j.1 + 1 ≤ k`;
- the resulting prefix span lies in the owner coordinate subspace
  `coordinateSubspace k n`.

Source/core/bridge triage:
- source-facing: the textbook fact that the first `k` search directions lie in `ℝ^{k,n}`;
- core/canonical: the sequence-level span theorem below;
- bridge/view: applying it to a gradient sequence when a later argument truly needs gradient
  notation.
-/

/-- Lemma 2.5: if each of the first `k` terms of a sequence `g` lies in its natural owner
coordinate subspace `ℝ^{j.1+1,n}`, then the span of that prefix lies in `ℝ^{k,n}`. Applying this
with `g j = ∇ f (x j)` recovers the gradient-prefix span statement used later in the chapter. -/
-- Proof sketch: use `Submodule.span_le`. For a generator `g j` with `j : Fin k`, the hypothesis
-- gives membership in `ℝ^{j.1 + 1,n}`. Rewriting by `mem_coordinateSubspace_iff`, every
-- coordinate with index at least `k` also lies in the vanishing range for `ℝ^{j.1 + 1,n}`, since
-- `j.1 + 1 ≤ k`.
theorem prefix_span_le_coordinateSubspace {k : ℕ}
    (g : ℕ → E)
    (hg : ∀ j : Fin k, g j ∈ ℝ^{j.1 + 1,n}) :
    Submodule.span ℝ (Set.range fun j : Fin k ↦ g j) ≤ ℝ^{k,n} := by
  refine Submodule.span_le.2 ?_
  rintro _ ⟨j, rfl⟩
  have hj : g j ∈ ℝ^{j.1 + 1,n} := hg j
  change g j ∈ ℝ^{k,n}
  rw [mem_coordinateSubspace_iff] at hj ⊢
  intro i hik
  exact hj i (le_trans (Nat.succ_le_of_lt j.is_lt) hik)

end
