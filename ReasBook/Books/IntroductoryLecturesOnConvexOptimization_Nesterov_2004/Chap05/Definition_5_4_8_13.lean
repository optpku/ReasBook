/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Definition_3_3

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

/- Definition 5.4.8.13 lies in the chapter's real hypograph / sublevel-set domain.

Sampled owner declarations:
- `constrainedSublevelSet` and `mem_constrainedSublevelSet_iff` from `Chap03/Definition_3_3`, the
  chapter owner for closed constraint sets cut out by a feasible region and a scalar inequality;
- `hypographBarrierDomain` from `Definition_5_4_7_20`, the nearby strict hypograph owner built
  from the same gap-map idea;
- `Q₃`, `mem_Q₃_iff`, and `mem_Q₆_iff` from `Definition_5_4_8_9` and
  `Definition_5_4_8_15`, the neighboring Chapter 5 pattern of exposing a source-facing owner when
  it is reused downstream.

Best owner abstraction:
- source-facing: the textbook set `Q₅`;
- core/canonical:
  `constrainedSublevelSet ((Set.univ : Set ℝ) ×ˢ Set.Ici (0 : ℝ))
    (fun xt : ℝ × ℝ ↦ ((xt.1 - Real.rpow xt.2 p : ℝ) : WithTop ℝ)) 0`;
- bridge/view: `mem_Q₅_iff`.

Primitive data:
- the feasible strip `ℝ × [0, ∞)`;
- the gap map `(x, t) ↦ x - t^p`.

Derived API:
- the source-facing owner `Q₅`;
- its coordinate membership theorem.

Source/core/bridge triage:
- source-facing: the textbook set `Q₅`;
- core/canonical: the constrained sublevel-set owner from Chapter 3;
- bridge/view: the specialized membership expansion below.

This item follows the same reused-owner pattern as `Q₃` and `Q₆`: the mathematical content is a
closed constrained sublevel set on `(x, t)`, and later theorems refer to the textbook set by name.
The public owner is therefore `Q₅`, realized directly through the chapter constrained
sublevel-set owner. -/

/-- Definition 5.4.8.13: the set `Q₅`, namely the constrained hypograph-type region
`{(x, t) ∈ ℝ² | t ≥ 0, x ≤ t^p}`. -/
abbrev Q₅ (p : ℝ) : Set (ℝ × ℝ) :=
  constrainedSublevelSet (Set.univ ×ˢ Set.Ici (0 : ℝ))
    (fun xt : ℝ × ℝ ↦ ((xt.1 - xt.2.rpow p : ℝ) : WithTop ℝ))
    0

-- Proof sketch: unfold `Q₅` and then `mem_constrainedSublevelSet_iff`; membership in the
-- feasible strip gives `0 ≤ t`, and the scalar inequality `x - t^p ≤ 0` is equivalent to
-- `t^p ≥ x`.
/-- Membership in `Q₅ p` means exactly that `t ≥ 0` and `t^p ≥ x`. -/
@[simp] theorem mem_Q₅_iff {p x t : ℝ} :
    (x, t) ∈ Q₅ p ↔ 0 ≤ t ∧ t.rpow p ≥ x := by
  rw [Q₅, mem_constrainedSublevelSet_iff]
  constructor
  · rintro ⟨hxt, hsub⟩
    have ht : 0 ≤ t := by
      simpa [Set.mem_prod] using hxt.2
    have hsub' : x - t.rpow p ≤ 0 := by
      exact_mod_cast hsub
    constructor
    · exact ht
    · linarith
  · rintro ⟨ht, htx⟩
    refine ⟨?_, ?_⟩
    · simpa [Set.mem_prod] using And.intro (Set.mem_univ x) ht
    · have hsub : x - t.rpow p ≤ 0 := by
        linarith
      exact_mod_cast hsub
