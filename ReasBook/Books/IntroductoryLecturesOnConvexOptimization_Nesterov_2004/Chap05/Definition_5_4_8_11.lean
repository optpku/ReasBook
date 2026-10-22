/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Definition_3_3

-- Declarations for this item will be appended below by the statement pipeline.

/- Definition 5.4.8.11 lies in the chapter's real epigraph domain.

Sampled owner declarations:
- `constrainedEpigraph` and `mem_constrainedEpigraph_iff` from `Chap03/Definition_3_3`, the
  chapter owner for epigraphs over a feasible set;
- `mem_constrainedEpigraph_negLog_iff` from `Definition_5_4_8_5`, the nearby chapter pattern for
  specializing this owner to a one-variable epigraph;
- `Q₃` and `mem_Q₃_iff` from `Definition_5_4_8_9`, another nearby source-facing
  epigraph-owner/membership pair;
- `mem_Q₆_iff` from `Definition_5_4_8_15`, the matching source-facing `Real.rpow`
  specialization pattern later in the same subsection.

Best owner abstraction:
- core/canonical:
  `constrainedEpigraph (Set.univ : Set ℝ) (fun x : ℝ ↦ ((|x| ^ p : ℝ) : WithTop ℝ))`.

Primitive data:
- the feasible set `Set.univ`;
- the function `x ↦ |x| ^ p`.

Derived API:
- the canonical epigraph expression itself;
- its specialized membership expansion.

Source/core/bridge triage:
- source-facing: the textbook set `Q₄`;
- core/canonical: the chapter epigraph owner `constrainedEpigraph`;
- bridge/view: the specialized membership theorem below.

This item therefore deletes the parallel local abbreviation `Q₄` and reuses the chapter epigraph
owner directly. -/

/- Definition 5.4.8.11 recalls the chapter epigraph owner specialized to `x ↦ |x| ^ p` on `ℝ`. -/
#check
  (fun p : ℝ ↦ constrainedEpigraph (Set.univ : Set ℝ)
    (fun x : ℝ ↦ ((|x| ^ p : ℝ) : WithTop ℝ)) : ℝ → Set (ℝ × ℝ))

-- Proof sketch: specialize `mem_constrainedEpigraph_iff` to `Q = Set.univ`; the feasible-set
-- condition is automatic, leaving exactly the inequality `|x| ^ p ≤ t`.
/-- Membership in the canonical epigraph expression for Definition 5.4.8.11, i.e. the textbook
set `Q₄`, means exactly that `t` lies above `|x| ^ p`. -/
@[simp] theorem mem_constrainedEpigraph_abs_pow_iff {p x t : ℝ} :
    (x, t) ∈ constrainedEpigraph (Set.univ : Set ℝ)
      (fun y : ℝ ↦ ((|y| ^ p : ℝ) : WithTop ℝ)) ↔
      t ≥ |x| ^ p := by
  rw [mem_constrainedEpigraph_iff]
  constructor
  · rintro ⟨_, hxt⟩
    exact_mod_cast hxt
  · intro hxt
    refine ⟨by simp, ?_⟩
    exact_mod_cast hxt
