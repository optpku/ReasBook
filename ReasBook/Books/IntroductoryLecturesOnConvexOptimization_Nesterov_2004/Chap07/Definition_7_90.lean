/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap07.Definition_7_89

-- Declarations for this item will be appended below by the statement pipeline.

universe u

section

variable {X : Type u}

/- Definition 7.90 lies in the chapter's mixed-accuracy / set-constrained minimization domain.

Mandatory domain-style sampling before refinement:
- `HasMixedAccuracy` in `Chap07/Definition_7_89`, the chapter owner of the scalar
  `(ε, δ)`-mixed-accuracy inequalities;
- `IsRelativeDeltaApproximateSolutionOn` in `Chap07/Definition_7_92`, the nearby source-facing
  optimization predicate on a feasible set;
- `IsAbsoluteAccuracyApproximateSolutionOn` in `Chap07/Definition_7_93`, the sibling
  source-facing additive approximation predicate on a feasible set;
- `SetConstrainedMinimizationProblem.IsApproximateMinimizer` in `Chap01/Definition_1_3_7`, the
  project owner for additive approximate minimizers on a fixed feasible set.

Best owner abstraction:
- source-facing: `IsMixedApproximateSolution Q hatF xStar ε δ xBar`;
- core/canonical: `HasMixedAccuracy hatF xStar ε δ xBar` together with the canonical minimizer
  owner `IsMinOn hatF Q xStar`;
- bridge/view: the expanded conjunction in `isMixedApproximateSolution_iff`.

Primitive data:
- the feasible-set membership `xBar ∈ Q`;
- the chosen optimality witness `IsMinOn hatF Q xStar`;
- the owner-level scalar mixed-accuracy datum `HasMixedAccuracy hatF xStar ε δ xBar`.

Derived API:
- positivity of `ε`;
- the interval condition `δ ∈ (0, 1)`;
- the mixed-accuracy inequality `(1 - δ) * hatF xBar ≤ hatF xStar + ε`.

Source/core/bridge triage:
- source-facing: the constrained mixed-accuracy approximate-solution predicate;
- core/canonical: `HasMixedAccuracy` and `IsMinOn`;
- bridge/view: the projection theorems and the expanded `iff` theorem.

The previous file duplicated the scalar mixed-accuracy owner from Definition 7.89 as primitive
fields of a second class. This refinement keeps Definition 7.90 source-facing, but it shrinks the
primitive data to the actual constrained content and reuses `HasMixedAccuracy` as the canonical
owner of the scalar accuracy component.
-/

/-- Definition 7.90: a feasible point `xBar ∈ Q` is an approximate solution with mixed
`(ε, δ)`-accuracy for the minimization of `hatF` over `Q` with chosen optimal solution `xStar`
when `xStar` minimizes `hatF` on `Q` and `xBar` satisfies the scalar mixed-accuracy owner from
Definition 7.89 relative to `xStar`. -/
structure IsMixedApproximateSolution
    (Q : Set X) (hatF : X → ℝ) (xStar : X) (ε δ : ℝ) (xBar : X) : Prop where
  /-- The candidate point `xBar` belongs to the feasible set `Q`. -/
  feasible : xBar ∈ Q
  /-- The reference point `xStar` is an optimal solution of `hatF` on `Q`. -/
  optimal : IsMinOn hatF Q xStar
  /-- The scalar mixed-accuracy data are owned by `HasMixedAccuracy`. -/
  mixedAccuracy : HasMixedAccuracy hatF xStar ε δ xBar

/-- A mixed approximate solution canonically supplies the chosen minimizer witness on `Q`. -/
instance {Q : Set X} {hatF : X → ℝ} {xStar xBar : X} {ε δ : ℝ}
    (h : IsMixedApproximateSolution Q hatF xStar ε δ xBar) :
    Fact (IsMinOn hatF Q xStar) where
  out := h.optimal

/-- A mixed approximate solution canonically supplies its scalar mixed-accuracy owner datum. -/
instance {Q : Set X} {hatF : X → ℝ} {xStar xBar : X} {ε δ : ℝ}
    (h : IsMixedApproximateSolution Q hatF xStar ε δ xBar) :
    Fact (HasMixedAccuracy hatF xStar ε δ xBar) where
  out := h.mixedAccuracy

namespace IsMixedApproximateSolution

variable {Q : Set X} {hatF : X → ℝ} {xStar xBar : X} {ε δ : ℝ}

/-- A mixed approximate solution carries the scalar mixed-accuracy owner from Definition 7.89. -/
theorem hasMixedAccuracy
    (h : IsMixedApproximateSolution Q hatF xStar ε δ xBar) :
    HasMixedAccuracy hatF xStar ε δ xBar :=
  h.mixedAccuracy

/-- The absolute-accuracy parameter of a mixed approximate solution is positive. -/
theorem epsilon_pos
    (h : IsMixedApproximateSolution Q hatF xStar ε δ xBar) :
    0 < ε :=
  h.mixedAccuracy.epsilon_pos

/-- The relative-accuracy parameter of a mixed approximate solution lies in `(0, 1)`. -/
theorem delta_mem_Ioo
    (h : IsMixedApproximateSolution Q hatF xStar ε δ xBar) :
    δ ∈ Set.Ioo (0 : ℝ) 1 :=
  h.mixedAccuracy.delta_mem_Ioo

/-- A mixed approximate solution satisfies the defining mixed absolute-relative accuracy bound. -/
theorem mixed_accuracy
    (h : IsMixedApproximateSolution Q hatF xStar ε δ xBar) :
    (1 - δ) * hatF xBar ≤ hatF xStar + ε :=
  h.mixedAccuracy.mixed_accuracy_bound

end IsMixedApproximateSolution

-- Proof sketch: unpack the feasible and optimal fields directly, then use the owner theorem
-- `hasMixedAccuracy_iff` for the scalar mixed-accuracy component. In the reverse direction, rebuild
-- the structure from feasibility, optimality, and the reconstructed `HasMixedAccuracy` datum.
/-- Expanding `IsMixedApproximateSolution` gives feasibility of `xBar`, optimality of `xStar`,
positivity of `ε`, the constraint `δ ∈ (0, 1)`, and the mixed-accuracy inequality
`(1 - δ) * hatF xBar ≤ hatF xStar + ε`. -/
theorem isMixedApproximateSolution_iff
    (Q : Set X) (hatF : X → ℝ) (xStar : X) (ε δ : ℝ) (xBar : X) :
    IsMixedApproximateSolution Q hatF xStar ε δ xBar ↔
      xBar ∈ Q ∧
        IsMinOn hatF Q xStar ∧
        0 < ε ∧
        δ ∈ Set.Ioo (0 : ℝ) 1 ∧
        (1 - δ) * hatF xBar ≤ hatF xStar + ε := by
  constructor
  · intro h
    exact ⟨h.feasible, h.optimal, h.epsilon_pos, h.delta_mem_Ioo, h.mixed_accuracy⟩
  · rintro ⟨hfeasible, hoptimal, hε, hδ, hmixed⟩
    refine ⟨hfeasible, hoptimal, ?_⟩
    exact (hasMixedAccuracy_iff hatF xStar ε δ xBar).2 ⟨hε, hδ, hmixed⟩

end
