/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap01.Definition_1_3_7

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u

section FunctionalConstraintStandardForm

variable {X : Type u} {m : ℕ}

local notation "StdPoint" => ℝ × ℝ × X

/-- The original optimization problem with ambient set `Q`, objective `f₀`, and inequality
constraints `fⱼ(x) ≤ 0`. -/
def functionalConstraintProblem
    (Q : Set X) (f0 : X → ℝ) (fj : Fin m → X → ℝ) :
    FunctionalConstraintsMinimizationProblem X m where
  basicFeasibleSet := Q
  objective := fun x ↦ f0 x
  constraints := fun j x ↦ fj j x
  senses := fun _ ↦ .le

/-- Evaluating the original functional-constraint owner recovers the original objective. -/
@[simp] theorem functionalConstraintProblem_apply
    (Q : Set X) (f0 : X → ℝ) (fj : Fin m → X → ℝ) (x : Q) :
    functionalConstraintProblem Q f0 fj x = f0 x :=
  rfl

/-- Membership in the original owner feasible set is exactly coordinatewise inequality
constraint satisfaction. -/
@[simp] theorem mem_functionalConstraintProblem_feasibleSet_iff
    {Q : Set X} {f0 : X → ℝ} {fj : Fin m → X → ℝ} {x : Q} :
    x ∈ (functionalConstraintProblem Q f0 fj).feasibleSet ↔
      ∀ j : Fin m, fj j x ≤ 0 :=
  Iff.rfl

/-- The `(ξ, κ, x)` standard-form reformulation of the original functional-constraint problem. -/
def functionalConstraintStandardFormProblem
    (Q : Set X) (f0 : X → ℝ) (fj : Fin m → X → ℝ) (xiBar : ℝ) :
    SetConstrainedMinimizationProblem StdPoint where
  feasibleSet := {p | p.1 ≤ xiBar ∧
    p.2.1 ≤ 0 ∧
    p.2.2 ∈ Q ∧
    f0 p.2.2 ≤ p.1 ∧
    ∀ j : Fin m, fj j p.2.2 ≤ p.2.1}
  objective := Prod.fst

/-- Membership in the standard-form feasible set is exactly the conjunction of the bounds
`ξ ≤ ξBar`, `κ ≤ 0`, the ambient constraint `x ∈ Q`, and the lifted inequalities
`f₀(x) ≤ ξ`, `fⱼ(x) ≤ κ`. -/
@[simp] theorem mem_functionalConstraintStandardFormProblem_feasibleSet_iff
    {Q : Set X} {f0 : X → ℝ} {fj : Fin m → X → ℝ} {xiBar : ℝ} {p : StdPoint} :
    p ∈ (functionalConstraintStandardFormProblem Q f0 fj xiBar).feasibleSet ↔
      p.1 ≤ xiBar ∧
        p.2.1 ≤ 0 ∧
        p.2.2 ∈ Q ∧
        f0 p.2.2 ≤ p.1 ∧
        ∀ j : Fin m, fj j p.2.2 ≤ p.2.1 :=
  Iff.rfl

/-- Evaluating the standard-form objective returns the `ξ`-coordinate. -/
@[simp] theorem functionalConstraintStandardFormProblem_apply
    (Q : Set X) (f0 : X → ℝ) (fj : Fin m → X → ℝ) (xiBar : ℝ) (p : StdPoint) :
    functionalConstraintStandardFormProblem Q f0 fj xiBar p = p.1 :=
  rfl

-- Proof sketch: every feasible point `x` of the original problem lifts to the feasible triple
-- `(f₀(x), 0, x)` because `f₀(x) ≤ ξBar` on the original feasible set and `fⱼ(x) ≤ 0`.
-- Conversely, every feasible triple `(ξ, κ, x)` projects to an original feasible point `x`, and
-- the lifted inequality `f₀(x) ≤ ξ` compares the original optimal value with the standard-form
-- one. These two comparisons show that the two constrained problems have the same optimal value.
/-- Proposition 5.3.6.1: if `ξBar` bounds the original objective on the original feasible set,
then the original problem and its standard-form reformulation have the same canonical Chapter 1
optimal value. -/
theorem functionalConstraintOptimalValue_eq_standardFormOptimalValue
    {Q : Set X} {f0 : X → ℝ} {fj : Fin m → X → ℝ} {xiBar : ℝ}
    (hUpper :
      ∀ x : Q, x ∈ (functionalConstraintProblem Q f0 fj).feasibleSet → f0 x ≤ xiBar) :
    (functionalConstraintProblem Q f0 fj).toSetConstrainedMinimizationProblem.optimalValue =
      (functionalConstraintStandardFormProblem Q f0 fj xiBar).optimalValue := by
  let originalProblem := functionalConstraintProblem Q f0 fj
  let problem := originalProblem.toSetConstrainedMinimizationProblem
  let standardProblem := functionalConstraintStandardFormProblem Q f0 fj xiBar
  apply le_antisymm
  · rw [SetConstrainedMinimizationProblem.optimalValue_eq_sInf_image]
    refine le_sInf ?_
    rintro _ ⟨p, hp, rfl⟩
    rcases (mem_functionalConstraintStandardFormProblem_feasibleSet_iff.mp hp) with
      ⟨_, hkappa, hxQ, hf0, hfj⟩
    let x : Q := ⟨p.2.2, hxQ⟩
    have hx : x ∈ originalProblem.feasibleSet :=
      mem_functionalConstraintProblem_feasibleSet_iff.mpr
        (fun j ↦ le_trans (hfj j) hkappa)
    have hproblem :
        problem.optimalValue ≤ (f0 x : EReal) := by
      simpa [problem] using problem.optimalValue_le_of_mem_feasibleSet hx
    exact hproblem.trans <| by
      change (f0 x : EReal) ≤ (p.1 : EReal)
      exact_mod_cast hf0
  · rw [SetConstrainedMinimizationProblem.optimalValue_eq_sInf_image]
    refine le_sInf ?_
    rintro _ ⟨x, hx, rfl⟩
    have hfj : ∀ j : Fin m, fj j x ≤ 0 :=
      mem_functionalConstraintProblem_feasibleSet_iff.mp hx
    have hstandard : (f0 x, 0, (x : X)) ∈ standardProblem.feasibleSet :=
      mem_functionalConstraintStandardFormProblem_feasibleSet_iff.mpr
        ⟨hUpper x hx, le_rfl, x.2, le_rfl, hfj⟩
    simpa [standardProblem] using
      standardProblem.optimalValue_le_of_mem_feasibleSet hstandard

end FunctionalConstraintStandardForm
