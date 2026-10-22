/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import ComputationalMethodsInverseProblems_Vogel_2002.Chap04.Notation_4_5.DiscreteEM
public import Mathlib.Order.Filter.Extr

public section

noncomputable section

namespace DiscreteEM

universe u v w

variable {Theta : Type u} {X : Type v} {Y : Type w}

/-- A one-step discrete EM update from `thetaV` to `thetaNext` for the observed datum
`y` consists of a nonvanishing observed mass at `thetaV` together with `thetaNext`
maximizing `qFunction` on `Set.univ`. -/
def IsStep
    [Fintype X] (joint : Theta → PMF (X × Y)) (y : Y) (thetaV thetaNext : Theta) : Prop :=
  ∃ hV : observedPmf joint thetaV y ≠ 0,
    IsMaxOn (fun theta ↦ qFunction joint theta thetaV y hV) Set.univ thetaNext

/-- The defining characterization of `IsStep`. -/
theorem isStep_iff
    [Fintype X] (joint : Theta → PMF (X × Y)) (y : Y) (thetaV thetaNext : Theta) :
    IsStep joint y thetaV thetaNext ↔
      ∃ hV : observedPmf joint thetaV y ≠ 0,
        IsMaxOn (fun theta ↦ qFunction joint theta thetaV y hV) Set.univ thetaNext := by
  -- This is just the definitional expansion of the packaged one-step update relation.
  rfl

/-- An EM sequence starts at the prescribed initial guess and every successive pair
of iterates satisfies the one-step EM update relation. -/
def IsSequence
    [Fintype X] (joint : Theta → PMF (X × Y)) (y : Y) (theta0 : Theta) (theta : ℕ → Theta) :
    Prop :=
  theta 0 = theta0 ∧ ∀ v, IsStep joint y (theta v) (theta (v + 1))

/-- The defining characterization of `IsSequence`. -/
theorem isSequence_iff
    [Fintype X] (joint : Theta → PMF (X × Y)) (y : Y) (theta0 : Theta) (theta : ℕ → Theta) :
    IsSequence joint y theta0 theta ↔
      theta 0 = theta0 ∧ ∀ v, IsStep joint y (theta v) (theta (v + 1)) := by
  -- This is just the definitional expansion of the packaged EM sequence predicate.
  rfl

/-- An `IsSequence` witness records the prescribed initial guess at index `0`. -/
theorem IsSequence.initial
    [Fintype X] {joint : Theta → PMF (X × Y)} {y : Y} {theta0 : Theta} {theta : ℕ → Theta}
    (hseq : IsSequence joint y theta0 theta) :
    theta 0 = theta0 := by
  -- Normalize the sequence predicate once, then project the initial-value field.
  exact (isSequence_iff joint y theta0 theta).mp hseq |>.1

/-- An `IsSequence` witness records the one-step EM update relation at every index. -/
theorem IsSequence.step
    [Fintype X] {joint : Theta → PMF (X × Y)} {y : Y} {theta0 : Theta} {theta : ℕ → Theta}
    (hseq : IsSequence joint y theta0 theta) (v : ℕ) :
    IsStep joint y (theta v) (theta (v + 1)) := by
  -- Normalize the sequence predicate once, then project the recurrence field at `v`.
  exact (isSequence_iff joint y theta0 theta).mp hseq |>.2 v

/-- A one-step EM update exposes the M-step maximization clause for some witness
`hV : observedPmf joint thetaV y ≠ 0`. -/
theorem IsStep.isMaxOn
    [Fintype X] {joint : Theta → PMF (X × Y)} {y : Y} {thetaV thetaNext : Theta}
    (hstep : IsStep joint y thetaV thetaNext) :
    ∃ hV : observedPmf joint thetaV y ≠ 0,
      IsMaxOn (fun theta ↦ qFunction joint theta thetaV y hV) Set.univ thetaNext := by
  -- Normalize the step predicate once, then expose its existential witness unchanged.
  exact (isStep_iff joint y thetaV thetaNext).mp hstep

end DiscreteEM
