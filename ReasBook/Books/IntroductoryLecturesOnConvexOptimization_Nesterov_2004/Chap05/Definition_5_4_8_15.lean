/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Definition_3_3

-- Declarations for this item will be appended below by the statement pipeline.

/- Definition 5.4.8.15 lies in the chapter's scalar epigraph domain.

Sampled owner declarations:
- `constrainedEpigraph` and `mem_constrainedEpigraph_iff` from `Chap03/Definition_3_3`, the
  chapter owner and its atomic membership expansion for constrained epigraphs;
- `Q₃` and `mem_Q₃_iff` from `Definition_5_4_8_9`, the nearby source-facing pattern where the
  textbook epigraph remains the public owner because later items reuse that name directly;
- the direct `constrainedEpigraph` recall in `Definition_5_4_8_11`, the neighboring pattern for a
  non-reused textbook epigraph whose public surface needs only the canonical owner and a thin
  membership bridge.

Best owner abstraction:
- source-facing owner: `Q₆`;
- canonical realization:
  `constrainedEpigraph (Set.Ioi (0 : ℝ)) (fun x : ℝ ↦ ((1 / Real.rpow x p : ℝ) : WithTop ℝ))`.

Primitive data:
- the positive half-line `(0, ∞)`;
- the scalar function `x ↦ x^{-p}`, written in Lean as `x ↦ 1 / Real.rpow x p`.

Derived API:
- the source-facing membership expansion `mem_Q₆_iff`.

Source/core/bridge triage:
- source-facing: the textbook set `Q₆`;
- core/canonical: `constrainedEpigraph`;
- bridge/view: the specialized membership theorem below.
-/

/-- Definition 5.4.8.15: the set `Q₆`, namely the epigraph of the function `x ↦ x^{-p}` on
`(0, ∞)`. -/
abbrev Q₆ (p : ℝ) : Set (ℝ × ℝ) :=
  constrainedEpigraph (Set.Ioi (0 : ℝ))
    (fun x : ℝ ↦ ((1 / Real.rpow x p : ℝ) : WithTop ℝ))

-- Proof sketch: unfold `Q₆` and then use the Chapter 3 characterization
-- `mem_constrainedEpigraph_iff`; the feasible-set condition gives `x > 0`, and the remaining
-- inequality is exactly the epigraph inequality `t ≥ x^{-p}`.
/-- Membership in `Q₆ p` means exactly that `x > 0` and `t ≥ x^{-p}`. -/
@[simp]
theorem mem_Q₆_iff {p x t : ℝ} :
    (x, t) ∈ Q₆ p ↔
      0 < x ∧ t ≥ 1 / Real.rpow x p := by
  rw [Q₆, mem_constrainedEpigraph_iff]
  constructor
  · rintro ⟨hx, hxt⟩
    refine ⟨hx, ?_⟩
    exact_mod_cast hxt
  · rintro ⟨hx, hxt⟩
    refine ⟨hx, ?_⟩
    exact_mod_cast hxt
