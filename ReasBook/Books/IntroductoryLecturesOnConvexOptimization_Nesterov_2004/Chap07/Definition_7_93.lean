/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap01.Definition_1_3_7

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u

section

variable {X : Type u}

/- Definition 7.93 lies in the constrained minimization / additive approximate-solution domain.

Mandatory domain-style sampling before refinement:
- `SetConstrainedMinimizationProblem` in `Chap01/Definition_1_3_3`, the project owner of a
  feasible set together with a real-valued objective;
- `SetConstrainedMinimizationProblem.optimalValue` in `Chap01/Definition_1_3_7`, the canonical
  Chapter 1 optimal-value owner in `EReal`;
- `SetConstrainedMinimizationProblem.IsApproximateMinimizer` in `Chap01/Definition_1_3_7`, the
  canonical Chapter 1 owner for additive `ε`-suboptimality on a constrained problem;
- `IsRelativeDeltaApproximateSolutionOn` in `Chap07/Definition_7_92`, the nearby Chapter 7
  source-facing predicate already stated through the owner optimal value rather than a raw real
  `sInf`.

Best owner abstraction:
- source-facing: `IsAbsoluteAccuracyApproximateSolutionOn Q phi ε xBar`;
- core/canonical: `(.mk Q phi : SetConstrainedMinimizationProblem X).IsApproximateMinimizer ε xBar`
  together with the owner `optimalValue : EReal`;
- bridge/view: the bounded-below comparison between the owner optimal value and the textbook real
  infimum `sInf (phi '' Q)`.

Primitive data:
- the accuracy parameter `ε`;
- the Chapter 1 approximate-minimizer owner for the constrained problem on `(Q, phi)`.

Derived API:
- positivity of `ε`;
- feasibility of `xBar`;
- the owner-valued additive objective-gap bound;
- the bounded-below bridge back to the textbook real inequality
  `phi xBar ≤ sInf (phi '' Q) + ε`.

The previous version still used the raw real infimum `sInf (phi '' Q)` in the main definition.
On an unbounded-below feasible image, `Real.sInf_of_not_bddBelow` collapses that value to `0`, so
the predicate no longer matches the textbook infimum `-∞`. This refinement therefore moves the
main owner to the Chapter 1 `EReal` optimal value and keeps the real-infimum surface only as a
bounded-below bridge. -/

/-- Definition 7.93: a point `xBar` is an absolute-accuracy `ε`-approximate solution for the
minimization of `phi` over the feasible set `Q` when `ε > 0` and `xBar` is an `ε`-approximate
minimizer for the Chapter 1 constrained-minimization owner on `(Q, phi)`. -/
def IsAbsoluteAccuracyApproximateSolutionOn
    (Q : Set X) (phi : X → ℝ) (ε : ℝ) (xBar : X) : Prop :=
  0 < ε ∧
    (.mk Q phi : SetConstrainedMinimizationProblem X).IsApproximateMinimizer ε xBar

namespace IsAbsoluteAccuracyApproximateSolutionOn

variable {Q : Set X} {phi : X → ℝ} {ε : ℝ} {xBar : X}

/-- The absolute-accuracy parameter of an absolute-accuracy approximate solution is positive. -/
theorem epsilon_pos
    (h : IsAbsoluteAccuracyApproximateSolutionOn Q phi ε xBar) :
    0 < ε :=
  h.1

/-- An absolute-accuracy approximate solution is an approximate minimizer for the canonical
Chapter 1 constrained-minimization owner on `(Q, phi)`. -/
theorem isApproximateMinimizer
    (h : IsAbsoluteAccuracyApproximateSolutionOn Q phi ε xBar) :
    (.mk Q phi : SetConstrainedMinimizationProblem X).IsApproximateMinimizer ε xBar :=
  h.2

/-- An absolute-accuracy approximate solution is feasible for the original constrained problem. -/
theorem feasible
    (h : IsAbsoluteAccuracyApproximateSolutionOn Q phi ε xBar) :
    xBar ∈ Q :=
  h.isApproximateMinimizer.1

/-- An absolute-accuracy approximate solution satisfies the defining owner-valued additive
objective bound. -/
theorem objective_le
    (h : IsAbsoluteAccuracyApproximateSolutionOn Q phi ε xBar) :
    (phi xBar : EReal) ≤ (.mk Q phi : SetConstrainedMinimizationProblem X).optimalValue + ε :=
  h.isApproximateMinimizer.2

/-- If the feasible objective values are nonempty and bounded below, then the Chapter 1 owner
optimal value agrees with the textbook real infimum. -/
theorem optimalValue_eq_coe_sInf
    (hQ : Q.Nonempty) (hbounded : BddBelow (phi '' Q)) :
    (.mk Q phi : SetConstrainedMinimizationProblem X).optimalValue =
      (((sInf (phi '' Q) : ℝ)) : EReal) := by
  rw [SetConstrainedMinimizationProblem.optimalValue_eq_sInf_image]
  have hs :
      IsGLB ((fun x : ℝ ↦ (x : EReal)) '' (phi '' Q)) (((sInf (phi '' Q) : ℝ) : EReal)) := by
    refine ⟨?_, ?_⟩
    · rintro _ ⟨y, hy, rfl⟩
      exact EReal.coe_le_coe (csInf_le hbounded hy)
    · intro z hz
      by_cases hz_bot : z = ⊥
      · simp [hz_bot]
      · have hz_top : z ≠ ⊤ := by
          intro hz_eq_top
          rcases hQ with ⟨x, hx⟩
          have hz_mem : z ≤ (phi x : EReal) := by
            exact hz ⟨phi x, ⟨x, hx, rfl⟩, rfl⟩
          simp [hz_eq_top] at hz_mem
        lift z to ℝ using ⟨hz_top, hz_bot⟩ with r
        have hr : r ≤ sInf (phi '' Q) := by
          refine le_csInf ?_ ?_
          · rcases hQ with ⟨x, hx⟩
            exact ⟨phi x, ⟨x, hx, rfl⟩⟩
          · intro y hy
            have hzy : (r : EReal) ≤ (y : EReal) := by
              exact hz ⟨y, hy, rfl⟩
            exact_mod_cast hzy
        exact_mod_cast hr
  have hs' : ((fun x : ℝ ↦ (x : EReal)) '' (phi '' Q)).Nonempty := by
    rcases hQ with ⟨x, hx⟩
    exact ⟨phi x, ⟨phi x, ⟨x, hx, rfl⟩, rfl⟩⟩
  simpa [Set.image_image] using hs.csInf_eq hs'

/-- If the feasible objective values are nonempty and bounded below, then the owner optimal value
has the textbook real infimum as its `toReal`. -/
theorem optimalValue_toReal_eq_sInf
    (hQ : Q.Nonempty) (hbounded : BddBelow (phi '' Q)) :
    ((.mk Q phi : SetConstrainedMinimizationProblem X).optimalValue).toReal = sInf (phi '' Q) := by
  rw [optimalValue_eq_coe_sInf hQ hbounded]
  simp

/-- If the feasible objective values are bounded below, then the owner-valued additive bound in
Definition 7.93 recovers the textbook real inequality against `sInf (phi '' Q)`. -/
theorem objective_le_sInf_add
    (h : IsAbsoluteAccuracyApproximateSolutionOn Q phi ε xBar)
    (hbounded : BddBelow (phi '' Q)) :
    phi xBar ≤ sInf (phi '' Q) + ε := by
  have hopt :
      (.mk Q phi : SetConstrainedMinimizationProblem X).optimalValue =
        (((sInf (phi '' Q) : ℝ)) : EReal) :=
    optimalValue_eq_coe_sInf ⟨xBar, h.feasible⟩ hbounded
  have hle : (phi xBar : EReal) ≤ ((sInf (phi '' Q) + ε : ℝ) : EReal) := by
    simpa [hopt] using h.objective_le
  exact_mod_cast hle

/-- If the feasible objective values are bounded below, then Definition 7.93 is equivalent to the
textbook positive-`ε` additive objective-gap inequality. -/
theorem iff_epsilon_pos_and_feasible_and_objective_le_sInf_add
    (hbounded : BddBelow (phi '' Q)) :
    IsAbsoluteAccuracyApproximateSolutionOn Q phi ε xBar ↔
      0 < ε ∧
        xBar ∈ Q ∧
        phi xBar ≤ sInf (phi '' Q) + ε := by
  constructor
  · intro h
    exact ⟨h.epsilon_pos, h.feasible, h.objective_le_sInf_add hbounded⟩
  · rintro ⟨hε, hx, hobj⟩
    refine ⟨hε, ?_⟩
    rw [SetConstrainedMinimizationProblem.isApproximateMinimizer_iff]
    refine ⟨hx, ?_⟩
    have hopt :
        (.mk Q phi : SetConstrainedMinimizationProblem X).optimalValue =
          (((sInf (phi '' Q) : ℝ)) : EReal) :=
      optimalValue_eq_coe_sInf ⟨xBar, hx⟩ hbounded
    have hle : (phi xBar : EReal) ≤ ((sInf (phi '' Q) + ε : ℝ) : EReal) := by
      exact_mod_cast hobj
    simpa [hopt] using hle

end IsAbsoluteAccuracyApproximateSolutionOn

/-- Unfolding `IsAbsoluteAccuracyApproximateSolutionOn Q phi ε xBar` gives positivity of `ε`
together with the canonical Chapter 1 approximate-minimizer owner on `(Q, phi)`. -/
theorem isAbsoluteAccuracyApproximateSolutionOn_iff
    (Q : Set X) (phi : X → ℝ) (ε : ℝ) (xBar : X) :
    IsAbsoluteAccuracyApproximateSolutionOn Q phi ε xBar ↔
      0 < ε ∧
        (.mk Q phi : SetConstrainedMinimizationProblem X).IsApproximateMinimizer ε xBar :=
  Iff.rfl

end
