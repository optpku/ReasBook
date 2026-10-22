/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Definition_3_3

-- Declarations for this item will be appended below by the statement pipeline.

/- Definition 5.4.8.9 lies in the chapter's real epigraph domain.

Sampled owner declarations:
- `constrainedEpigraph` and `mem_constrainedEpigraph_iff` from `Chap03/Definition_3_3`, the
  chapter owner for epigraphs over a feasible set;
- `mem_constrainedEpigraph_negLog_iff` from `Definition_5_4_8_5`, the nearby chapter pattern for
  specializing this owner to a one-variable barrier epigraph;
- `ConvexOn.convex_epigraph`, the standard convex-epigraph owner theorem;
- `LowerSemicontinuous.isClosed_epigraph`, the standard closed-epigraph owner theorem.

Best owner abstraction:
- core/canonical:
  `constrainedEpigraph (Set.Ici (0 : ℝ))
    (fun x : ℝ ↦ ((x * Real.log x : ℝ) : WithTop ℝ))`.

Primitive data:
- the nonnegative half-line `[0, ∞)`;
- the function `x ↦ x log x`.

Derived API:
- the specialized epigraph expression itself;
- its membership expansion.

Source/core/bridge triage:
- source-facing: the textbook set `Q₃`;
- core/canonical: the chapter epigraph owner `constrainedEpigraph`;
- bridge/view: the specialized membership theorem below.

This item therefore keeps the source-facing owner `Q₃` while realizing it directly through the
chapter epigraph owner, deleting the parallel local set `qThreeEpigraph`. -/

/-- Definition 5.4.8.9: the set `Q₃`, namely the epigraph of `x ↦ x log x` on `[0, ∞)`. -/
abbrev Q₃ : Set (ℝ × ℝ) :=
  constrainedEpigraph (Set.Ici (0 : ℝ))
    (fun x : ℝ ↦ ((x * Real.log x : ℝ) : WithTop ℝ))

/-- Membership in `Q₃` means exactly that `x ≥ 0` and `t ≥ x log x`. -/
@[simp] theorem mem_Q₃_iff {x t : ℝ} :
    (x, t) ∈ Q₃ ↔ 0 ≤ x ∧ t ≥ x * Real.log x := by
  rw [Q₃, mem_constrainedEpigraph_iff]
  constructor
  · rintro ⟨hx, hxt⟩
    refine ⟨hx, ?_⟩
    have hxt' : x * Real.log x ≤ t := by
      exact_mod_cast hxt
    simpa [ge_iff_le] using hxt'
  · rintro ⟨hx, hxt⟩
    refine ⟨hx, ?_⟩
    have hxt' : x * Real.log x ≤ t := by
      simpa [ge_iff_le] using hxt
    exact_mod_cast hxt'
