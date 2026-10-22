/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import Mathlib.Tactic.Recall
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap02.Text_2_13

-- Declarations for this item will be appended below by the statement pipeline.

open scoped CoordinateSubspace

/- Definition 2.12 is a source-facing recall in the finite-dimensional linear-algebra domain of
coordinate subspaces of `ℝⁿ`.

Primary domain:
- linear-algebraic coordinate subspaces in Euclidean space.

Sampled owner-style declarations:
- `coordinateSubspace k n`, the chapter's canonical `Submodule` owner for `ℝ^{k,n}`;
- `mem_coordinateSubspace_iff`, the coordinatewise derived membership criterion;
- the scoped notation `ℝ^{k,n}`, the source-facing surface for that owner;
- `Submodule.comap`, the canonical way to realize a subspace by pulling back a product-side
  submodule along a linear equivalence;
- `Submodule.pi`, the canonical product-side owner used to encode coordinatewise vanishing.

Best owner abstraction:
- `coordinateSubspace k n : Submodule ℝ (EuclideanSpace ℝ (Fin n))`

Primitive data:
- the cut index `k`;
- the ambient dimension `n`.

Derived API:
- `mem_coordinateSubspace_iff`, which rewrites membership in the owner submodule into the textbook
  coordinate-vanishing condition.
- the notation `ℝ^{k,n}`, which exposes the source-facing surface while keeping
  `coordinateSubspace k n` as the raw owner.

Source/core/bridge triage:
- source-facing: the textbook coordinate subspace `ℝ^{k,n} ⊆ ℝⁿ`;
- core/canonical: the owner submodule `coordinateSubspace k n`;
- bridge/view: the coordinatewise criterion `mem_coordinateSubspace_iff`.

This recall file therefore uses the upstream owner declaration directly and introduces no parallel
wrapper or duplicate local definition. It also reuses the upstream notation `ℝ^{k,n}` rather than
adding a second alias layer.
-/

recall coordinateSubspace (k n : ℕ) : Submodule ℝ (EuclideanSpace ℝ (Fin n))

recall mem_coordinateSubspace_iff
    {k n : ℕ} {x : EuclideanSpace ℝ (Fin n)} :
    x ∈ ℝ^{k,n} ↔ ∀ i : Fin n, k ≤ i.1 → x i = 0
