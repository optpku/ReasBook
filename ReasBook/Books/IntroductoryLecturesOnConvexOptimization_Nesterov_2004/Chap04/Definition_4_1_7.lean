/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap01.Definition_1_3_3
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap04.Theorem_4_1_4

-- Declarations for this item will be appended below by the statement pipeline.

open scoped ConstrainedArgmin

noncomputable section

variable {E : Type*} [AddCommMonoid E] [Module ℝ E]

/- Definition 4.1.7 lies in the unconstrained star-convex optimization domain over a real module.

Sampled owner-style declarations:
* `IsMinOn` and `isMinOn_univ_iff`, the canonical mathlib owner for whole-space minimizers;
* `argmin[Q]` and `mem_constrainedArgmin_iff` in `Chap01/Definition_1_3_3`, the project owner
  for minimizer sets on a feasible set, specialized here to `Q = Set.univ`;
* mathlib `StarConvex ℝ x s`, the ambient owner pattern for star-shaped geometry of sets;
* `StarConvexWithRespectToOn` in `Theorem_4_1_4`, the chapter bridge owner for the textbook
  star-convexity inequality with a fixed reference point on a feasible set.

Best owner abstraction:
* the source-facing property `StarConvexFunction f`, asserting existence of a global minimizer
  that serves as a star center;
* the fixed-center canonical data `xStar ∈ argmin[Set.univ] f` and
  `StarConvexWithRespectToOn f xStar Set.univ`.

Primitive data:
* a real-valued objective `f`;
* existence of a point `xStar` in the canonical minimizer set `argmin[Set.univ] f`;
* the textbook star-convexity inequality from that feasible `xStar`.

Derived API:
* nonemptiness of `argmin[Set.univ] f`;
* the bridge from `xStar ∈ argmin[Set.univ] f` to `IsMinOn f Set.univ xStar`.

Source/core/bridge triage:
* source-facing: `StarConvexFunction`;
* core/canonical: `argmin[Set.univ] f`, `IsMinOn f Set.univ xStar`, and
  `StarConvexWithRespectToOn f xStar Set.univ`;
* bridge/view: `StarConvexFunction.exists_starCenter_isMinOn`.

This refinement keeps `StarConvexFunction` as the source-facing owner, but moves the chosen
minimizer into the canonical `argmin[Set.univ]` owner and reuses `IsMinOn` only through the
standard Chapter 1 bridge. -/

/-- Definition 4.1.7: a real-valued function is star-convex if it has a global minimizer `x*`
such that, for every point `x` and every `α ∈ [0,1]`, the value of `f` at
`α x* + (1 - α) x` is bounded by the corresponding convex combination of `f x*` and `f x`. -/
class StarConvexFunction (f : E → ℝ) : Prop where
  /-- The function has a global minimizer that is a valid star center on the whole ambient
  space. -/
  exists_starCenter :
    ∃ xStar, xStar ∈ argmin[Set.univ] f ∧
      StarConvexWithRespectToOn f xStar Set.univ

/-- A global minimizer in the canonical minimizer set that is a valid star center yields a
star-convex function. -/
theorem starConvexFunction_of_mem_argmin
    {f : E → ℝ} {xStar : E}
    (hxStar : xStar ∈ argmin[Set.univ] f)
    (hstar : StarConvexWithRespectToOn f xStar Set.univ) :
    StarConvexFunction f :=
  ⟨⟨xStar, hxStar, hstar⟩⟩

/-- A fixed global minimizer that is a valid star center yields a star-convex function. -/
theorem starConvexFunction_of_isMinOn
    {f : E → ℝ} {xStar : E}
    (hxStar : IsMinOn f Set.univ xStar)
    (hstar : StarConvexWithRespectToOn f xStar Set.univ) :
    StarConvexFunction f := by
  refine starConvexFunction_of_mem_argmin ?_ hstar
  rw [mem_constrainedArgmin_iff]
  exact ⟨by simp, hxStar⟩

/-- A star-convex function admits a global minimizer serving as a star center. -/
theorem StarConvexFunction.exists_starCenter_isMinOn
    {f : E → ℝ} (hf : StarConvexFunction f) :
    ∃ xStar, IsMinOn f Set.univ xStar ∧
      StarConvexWithRespectToOn f xStar Set.univ :=
by
  rcases hf.exists_starCenter with ⟨xStar, hxStar, hstar⟩
  rw [mem_constrainedArgmin_iff] at hxStar
  exact ⟨xStar, hxStar.2, hstar⟩

/-- The global minimizer set of a star-convex function is nonempty. -/
theorem StarConvexFunction.argmin_nonempty
    {f : E → ℝ} (hf : StarConvexFunction f) :
    (argmin[Set.univ] f).Nonempty := by
  rcases hf.exists_starCenter with ⟨xStar, hxStar, -⟩
  exact ⟨xStar, hxStar⟩

/-- Constant real-valued functions are star-convex. -/
instance starConvexFunction_const [Nonempty E] (c : ℝ) :
    StarConvexFunction (fun _ : E ↦ c) := by
  rcases ‹Nonempty E› with ⟨xStar⟩
  refine ⟨⟨xStar, ?_, ?_⟩⟩
  · simp [isMinOn_univ_iff]
  · constructor
    · simp
    · intro x hx α hα
      have hconst : (1 - α) * c + α * c = c := by ring
      simp [hconst]
