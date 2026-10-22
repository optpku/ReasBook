/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap07.Definition_7_81

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open scoped WithTopConvexAnalysis

universe u

/- Definition 7.83 lies in the Chapter 7 real-valued whole-space subdifferential / convex-set
domain.

Mandatory domain-style sampling before refinement:
- `StrictlyPositiveOn` and `StrictlyPositiveOn.inequality` in
  `Nesterov.Chap07.Definition_7_81`, the source-facing Chapter 7 owner for the
  subgradient inequality;
- the recall-only conjunction surface in `Nesterov.Chap03.Definition_3_36`, which keeps
  closedness, convexity, and whole-space objective convexity directly on canonical owners instead
  of introducing a second wrapper predicate;
- `ConvexOn ℝ Set.univ f` in `Nesterov.Chap03.Definition_3_33`, the project's canonical
  owner for whole-space convexity of a real-valued objective;
- `EverywhereNonemptySubdifferentialCondition` in `Nesterov.Chap07.Definition_7_80`, which
  likewise treats owner-level subdifferential data as primitive and uses a named condition only
  when the source adds genuine new content.

Best owner abstraction:
- source-facing: the textbook phrase “`f` is strictly positive on the closed convex set `Q`”;
- core/canonical: the direct conjunction
  `IsClosed Q ∧ Convex ℝ Q ∧ ConvexOn ℝ Set.univ f ∧ StrictlyPositiveOn Q f`;
- bridge/view: the already existing projection lemma `StrictlyPositiveOn.inequality`.

Primitive data:
- the set `Q`;
- the real-valued objective `f`.

Derived API:
- the four canonical conjuncts above;
- the inequality consequence supplied already by `StrictlyPositiveOn.inequality`.

Source/core/bridge triage:
- source-facing: Definition 7.83's textbook conjunction of closedness, convexity, whole-space
  convexity, and strict positivity on `Q`;
- core/canonical: `IsClosed`, `Convex`, `ConvexOn`, and `StrictlyPositiveOn`;
- bridge/view: no second owner is needed, because the only nontrivial derived API is already
  owned by `StrictlyPositiveOn`.

The earlier file introduced a duplicate wrapper predicate whose body was exactly a conjunction of
existing owners and whose projection lemmas merely re-exposed existing conjuncts. This refinement
keeps the source meaning but makes the numbered item a direct recall of the canonical conjunction,
matching the chapter's owner-first style and avoiding an unnecessary parallel public API. -/

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable (Q : Set E) (f : E → ℝ)

set_option linter.hashCommand false in
/- Definition 7.83: a real-valued function is strictly positive on a closed convex set `Q` when
`Q` is closed and convex, `f` is convex on the whole ambient space, and `f` is strictly positive
on `Q` in the sense of Definition 7.81. -/
#check
  (IsClosed Q ∧
    Convex ℝ Q ∧
    ConvexOn ℝ Set.univ f ∧
    StrictlyPositiveOn Q f)

end
