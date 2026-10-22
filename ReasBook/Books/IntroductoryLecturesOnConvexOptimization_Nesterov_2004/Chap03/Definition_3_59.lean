/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Definition_3_50

-- Declarations for this item will be appended below by the statement pipeline.

variable {E : Type*} [PseudoMetricSpace E]

open Set Metric

/- Definition 3.59 lies in the chapter's interior-ball / interior-nonemptiness domain.

Sampled owner-style declarations:
- `ball`, the metric owner of fixed-radius open balls;
- `mem_ball_self`, which derives center membership from positive radius;
- `mem_interior`, the canonical owner theorem for membership in `interior Q`;
- `interior_ball_assumption_iff_interior_nonempty` in `Definition_3_50`, the chapter's owner
  bridge from textbook ball containment to the intrinsic predicate `(interior Q).Nonempty`.

Best owner abstraction:
- `Definition_3_50` already keeps `(interior Q).Nonempty` as the chapter's canonical owner for
  the unparameterized interior-ball condition;
- Definition 3.59 is still source-facing because it adds genuine data, namely a specified radius
  `ρ`, so the public definition should remain the explicit radius-`ρ` ball-containment predicate;
- the Euclidean textbook case is just the specialization of this metric owner to `E = ℝⁿ`, so no
  separate Euclidean-only wrapper is needed.

Primitive data:
- the radius positivity `0 < ρ`;
- a center `xBar`;
- the inclusion `ball xBar ρ ⊆ Q`.

Derived API:
- the center belongs to `Q`;
- `Q` has nonempty interior. -/

namespace Set

/-- Definition 3.59: a set `Q` satisfies the interior ball condition with parameter `ρ` when `ρ`
is positive and `Q` contains an open ball of radius `ρ`. In the textbook Euclidean setting, this
is exactly the interior Euclidean ball condition on `Q ⊆ ℝⁿ`. -/
def SatisfiesInteriorBallCondition (Q : Set E) (ρ : ℝ) : Prop :=
  0 < ρ ∧ ∃ xBar : E, ball xBar ρ ⊆ Q

namespace SatisfiesInteriorBallCondition

variable {Q : Set E} {ρ : ℝ}

/-- A set satisfying the interior ball condition has nonempty interior. -/
theorem interior_nonempty (hQ : Q.SatisfiesInteriorBallCondition ρ) :
    (interior Q).Nonempty := by
  rcases hQ with ⟨hρ, xBar, hball⟩
  exact (interior_ball_assumption_iff_interior_nonempty Q).mp ⟨xBar, ρ, hρ, hball⟩

end SatisfiesInteriorBallCondition

end Set
