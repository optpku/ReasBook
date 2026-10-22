/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Definition_3_1_1_6

-- Declarations for this item will be appended below by the statement pipeline.

universe u

/- Definition 3.6 is a recall-only item in the seminorm-geometry domain.

Layer targeted by this refinement:
- source-facing recall of the closed unit ball attached to a seminorm

Primary domain:
- closed balls of seminorms, specialized here to the origin-centered radius-`1` case.

Sampled owner-style declarations:
- `Seminorm.closedBall`
- `Seminorm.mem_closedBall`
- `Seminorm.mem_closedBall_zero`
- `Seminorm.closedBall_zero_eq`

Best owner abstraction:
- `Seminorm.closedBall`

Primitive data:
- a seminorm `p : Seminorm 𝕜 E`
- a center `x : E`
- a radius `r : ℝ`

Derived API:
- the source-facing unit-ball specialization `p.closedBall 0 1`
- the set-builder bridge `p.closedBall 0 1 = {x | p x ≤ 1}`

Source/core/bridge triage:
- source-facing: the unit ball of a seminorm
- core/canonical: `Seminorm.closedBall`
- bridge/view: `Seminorm.closedBall_zero_eq` specialized to radius `1`

The unit ball does not need a new chapter-local owner or wrapper: it is exactly the canonical
origin-centered closed ball of radius `1`. Although the textbook states this in the real vector
space setting, the canonical owner and its zero-center bridge already live at the more primitive
`SeminormedRing`/`SMul` level, so this recall is stated there.
-/

section

variable {𝕜 E : Type u} [SeminormedRing 𝕜] [AddCommGroup E] [SMul 𝕜 E]
variable (p : Seminorm 𝕜 E)

/- Definition 3.6: the unit ball is the canonical owner specialization `p.closedBall 0 1`.
-/
#check p.closedBall 0 1

/- The source-facing set-builder description is the zero-center bridge theorem specialized to
radius `1`. -/
#check (p.closedBall_zero_eq : p.closedBall 0 1 = {x | p x ≤ 1})

end
