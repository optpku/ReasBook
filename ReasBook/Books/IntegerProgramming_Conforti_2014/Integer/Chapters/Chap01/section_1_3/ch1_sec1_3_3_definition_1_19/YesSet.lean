/-
Authors: Ziyu Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@d380aaa277a7a97379616d8bd2809e751c1052f4:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization contributors, confirmed by the submitter on 2026-11-04.
-/

module

public import Mathlib.Data.Set.Defs
public import Mathlib.Logic.Basic
public import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap01.section_1_3.ch1_sec1_3_3_definition_1_19.Problem

@[expose] public section

namespace DecisionProblem

/-- A decision problem is specified by an instance type `I` together with a set of yes-instances;
relative to an encoding-size function, this data determines the canonical Boolean-valued decision
problem whose output is `true` exactly on those instances. -/
noncomputable def ofYesSet {I : Type} (encodingSize : I → Nat) (yesInstances : Set I) :
    DecisionProblem :=
  { Instance := I
    encodingSize := encodingSize
    answer := fun x ↦ @decide (x ∈ yesInstances) (Classical.decPred yesInstances x) }

/-- The subset of instances on which a decision problem returns the Boolean answer `true`. -/
def yesInstances (D : DecisionProblem) : Set D.Instance :=
  { x | D.answer x = true }

/-- Expanding `D.yesInstances` recovers the underlying set of true-valued instances. -/
@[simp] theorem yesInstances_def (D : DecisionProblem) :
    D.yesInstances = { x | D.answer x = true } :=
  rfl

/-- The Boolean answer of `DecisionProblem.ofYesSet encodingSize yesInstances` is `true` exactly on
the specified yes-instances. -/
@[simp] theorem ofYesSet_answer_eq_true_iff
    {I : Type}
    (encodingSize : I → Nat)
    (yesInstances : Set I)
    (x : I) :
    (DecisionProblem.ofYesSet encodingSize yesInstances).answer x = true ↔ x ∈ yesInstances := by
  classical
  simp [DecisionProblem.ofYesSet]

/-- Membership in `D.yesInstances` is equivalent to the Boolean answer of `D` being `true`. -/
@[simp] theorem mem_yesInstances_iff (D : DecisionProblem) (x : D.Instance) :
    x ∈ D.yesInstances ↔ D.answer x = true :=
  Iff.rfl

/-- Recovering the yes-instances of a decision problem built from `yesInstances` returns exactly
the original set. -/
@[simp] theorem ofYesSet_yesInstances
    {I : Type}
    (encodingSize : I → Nat)
    (yesInstances : Set I) :
    (DecisionProblem.ofYesSet encodingSize yesInstances).yesInstances = yesInstances := by
  ext x
  change (DecisionProblem.ofYesSet encodingSize yesInstances).answer x = true ↔ x ∈ yesInstances
  exact DecisionProblem.ofYesSet_answer_eq_true_iff encodingSize yesInstances x

/-- A decision problem is recovered by rebuilding it from its encoding-size function and its
yes-instances. -/
theorem ofYesSet_yesInstances_eq_self (D : DecisionProblem) :
    DecisionProblem.ofYesSet D.encodingSize D.yesInstances = D := by
  classical
  cases D with
  | mk Instance encodingSize answer =>
      change
        DecisionProblem.mk
            Instance
            encodingSize
            (fun x ↦ @decide (x ∈ { y | answer y = true }) (Classical.decPred _ x)) =
          DecisionProblem.mk Instance encodingSize answer
      congr
      funext x
      cases h : answer x with
      | false =>
          rw [decide_eq_false_iff_not]
          change ¬ answer x = true
          simpa using h
      | true =>
          rw [decide_eq_true_eq]
          change answer x = true
          exact h

end DecisionProblem
