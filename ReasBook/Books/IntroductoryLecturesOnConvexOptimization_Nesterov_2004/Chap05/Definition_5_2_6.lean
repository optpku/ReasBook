/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import Mathlib.Tactic.Recall
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Lemma_5_2_2

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u

/- Definition 5.2.6 lies in the Chapter 5 self-concordant path-following / intermediate-Newton
update domain.

Mandatory domain-style sampling before refinement:
* `pathFollowingUpdate` in `Lemma_5_2_2`, the chapter owner for the path-following map
  `(t, y) ↦ (t₊, y₊)` and its source-facing notation
  `𝒫[f; M_f; y₀ | hy; γ](t, y)`;
* `pathFollowingUpdate_fst` in `Lemma_5_2_2`, the canonical scalar-update projection theorem;
* `pathFollowingUpdate_snd` in `Lemma_5_2_2`, the canonical second-projection theorem.

Best owner abstraction:
* source-facing: Definition 5.2.6's path-following map and its two projection formulas;
* core/canonical: `pathFollowingUpdate`;
* bridge/view: `pathFollowingUpdate_fst` and `pathFollowingUpdate_snd`.

Primitive data:
* the already-defined owner `pathFollowingUpdate`.

Derived API:
* the first-coordinate formula `pathFollowingUpdate_fst`;
* the second-coordinate formula `pathFollowingUpdate_snd`.

This file is therefore a recall/bridge file. Redefining `pathFollowingUpdate` here would duplicate
the chapter owner already introduced in `Lemma_5_2_2` and would split downstream vocabulary for
the same source-facing map. -/

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/- Definition 5.2.6 recalls the chapter owner for the path-following update map `𝒫_γ`. -/
recall pathFollowingUpdate

/- The scalar update `t₊` is already the canonical first-projection companion theorem. -/
recall pathFollowingUpdate_fst

/- The vector update `y₊` is already the canonical second-projection companion theorem. -/
recall pathFollowingUpdate_snd

end
