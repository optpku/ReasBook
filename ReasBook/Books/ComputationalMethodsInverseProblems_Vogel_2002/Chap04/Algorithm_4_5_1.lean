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

/-- Helper for Algorithm 4.5.1: a one-step discrete EM update from `thetaV` to
`thetaNext` for the observed datum `y` consists of a nonvanishing observed mass
at `thetaV` together with `thetaNext` maximizing `qFunction` on `Set.univ`. -/
def IsStep
    [Fintype X] (joint : Theta → PMF (X × Y)) (y : Y) (thetaV thetaNext : Theta) : Prop :=
  ∃ hV : observedPmf joint thetaV y ≠ 0,
    IsMaxOn (fun theta ↦ qFunction joint theta thetaV y hV) Set.univ thetaNext

/-- Helper for Algorithm 4.5.1: `IsStep` is definitionally equivalent to the
existence of the E-step witness and the M-step maximization clause. -/
theorem isStep_iff
    [Fintype X] (joint : Theta → PMF (X × Y)) (y : Y) (thetaV thetaNext : Theta) :
    IsStep joint y thetaV thetaNext ↔
      ∃ hV : observedPmf joint thetaV y ≠ 0,
        IsMaxOn (fun theta ↦ qFunction joint theta thetaV y hV) Set.univ thetaNext := by
  -- Expand the packaged one-step update relation once.
  rfl

/-- Algorithm 4.5.1. An EM sequence starts at the prescribed initial guess and
every successive pair of iterates satisfies the one-step EM update relation. -/
def IsSequence
    [Fintype X] (joint : Theta → PMF (X × Y)) (y : Y) (theta0 : Theta) (theta : ℕ → Theta) :
    Prop :=
  theta 0 = theta0 ∧ ∀ v, IsStep joint y (theta v) (theta (v + 1))

/-- Helper for Algorithm 4.5.1: `IsSequence` is definitionally equivalent to
the initial-value condition together with the stepwise EM update rule. -/
theorem isSequence_iff
    [Fintype X] (joint : Theta → PMF (X × Y)) (y : Y) (theta0 : Theta) (theta : ℕ → Theta) :
    IsSequence joint y theta0 theta ↔
      theta 0 = theta0 ∧ ∀ v, IsStep joint y (theta v) (theta (v + 1)) := by
  -- Expand the packaged sequence predicate once.
  rfl

/-- Helper for Algorithm 4.5.1: an `IsSequence` witness records the prescribed
initial guess at index `0`. -/
theorem IsSequence.initial
    [Fintype X] {joint : Theta → PMF (X × Y)} {y : Y} {theta0 : Theta} {theta : ℕ → Theta}
    (hseq : IsSequence joint y theta0 theta) :
    theta 0 = theta0 := by
  -- Normalize the sequence predicate, then project the initial-value field.
  exact (isSequence_iff joint y theta0 theta).mp hseq |>.1

/-- Helper for Algorithm 4.5.1: an `IsSequence` witness records the one-step EM
update relation at every index. -/
theorem IsSequence.step
    [Fintype X] {joint : Theta → PMF (X × Y)} {y : Y} {theta0 : Theta} {theta : ℕ → Theta}
    (hseq : IsSequence joint y theta0 theta) (v : ℕ) :
    IsStep joint y (theta v) (theta (v + 1)) := by
  -- Normalize the sequence predicate, then project the recurrence at `v`.
  exact (isSequence_iff joint y theta0 theta).mp hseq |>.2 v

/-- Helper for Algorithm 4.5.1: a one-step EM update exposes the M-step
maximization clause for some witness `hV : observedPmf joint thetaV y ≠ 0`. -/
theorem IsStep.isMaxOn
    [Fintype X] {joint : Theta → PMF (X × Y)} {y : Y} {thetaV thetaNext : Theta}
    (hstep : IsStep joint y thetaV thetaNext) :
    ∃ hV : observedPmf joint thetaV y ≠ 0,
      IsMaxOn (fun theta ↦ qFunction joint theta thetaV y hV) Set.univ thetaNext := by
  -- Normalize the step predicate, then expose its existential witness unchanged.
  exact (isStep_iff joint y thetaV thetaNext).mp hstep

end DiscreteEM

#check DiscreteEM.IsStep
#check DiscreteEM.IsSequence
