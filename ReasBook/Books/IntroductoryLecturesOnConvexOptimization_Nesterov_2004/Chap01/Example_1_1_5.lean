/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap01.Definition_1_1_1

-- Declarations for this item will be appended below by the statement pipeline.

universe u

variable {m : ℕ} {X : Type u}

/- Example 1.1.5 lies in the constrained-optimization domain of bounded functional characteristics.

Sampled owner-style declarations:
* `FunctionalConstraintsMinimizationProblem` and `problem.IsFeasible` in
  `Chap01/Definition_1_1_3`
* `FunctionalConstraintsMinimizationProblem.HasLeConstraints` in
  `Chap01/Definition_1_1_1`
* `FunctionalConstraintsMinimizationProblem.mem_feasibleSet_iff` in
  `Chap01/Definition_1_1_1`
* `LagrangianProblem.toFunctionalConstraintsMinimizationProblem` in
  `Chap01/Definition_1_10_2`

Best owner abstraction:
* `FunctionalConstraintsMinimizationProblem X (m + m)`, obtained by adjoining the lower- and
  upper-bound inequalities as one owner constraint family on the structural set `Q`

Primitive data:
* the structural set `Q`
* the distinguished objective `f₀`
* the characteristic family `fⱼ`
* the lower and upper scalar bounds

Derived API:
* the owner object `boundedCharacteristicProblem`
* the fact that all owner constraints are inequalities
* simp lemmas identifying the lower and upper appended constraint coordinates
* the source-facing feasibility characterization in terms of the paired bounds

Source/core/bridge triage:
* source-facing: the bounded-characteristic optimization problem from the textbook
* core/canonical: `FunctionalConstraintsMinimizationProblem X (m + m)`
* bridge/view: the Euclidean specialization `GeneralMinimizationProblem n (m + m)` and the
  feasibility equivalence unpacking the owner inequalities into lower and upper scalar bounds

The source states `Q ⊆ ℝⁿ`, but this construction only uses the structural set `Q` and the scalar
characteristic family on its subtype. The faithful owner is therefore the ambient
`FunctionalConstraintsMinimizationProblem`, with the textbook Euclidean problem recovered as its
specialization. -/

section

variable (Q : Set X) (objective : Q → ℝ)
variable (characteristics : Fin m → Q → ℝ) (lowerBounds upperBounds : Fin m → ℝ)

/-- Example 1.1.5: Functional characteristics with lower and upper bounds define a general
minimization problem on the structural set `Q`: the distinguished characteristic `f₀` is the
objective, and the remaining characteristics appear as paired lower and upper scalar constraints.
The textbook Euclidean formulation is the specialization of this owner to `X = ℝⁿ`. -/
def boundedCharacteristicProblem
    : FunctionalConstraintsMinimizationProblem X (m + m) where
  basicFeasibleSet := Q
  objective := objective
  constraints :=
    Fin.append
      (fun j x ↦ lowerBounds j - characteristics j x)
      (fun j x ↦ characteristics j x - upperBounds j)
  senses := fun _ ↦ .le

@[simp] theorem boundedCharacteristicProblem_hasLeConstraints
    :
    (boundedCharacteristicProblem Q objective characteristics lowerBounds
      upperBounds).HasLeConstraints :=
  fun _ ↦ rfl

end

section

variable {Q : Set X} {objective : Q → ℝ}
variable {characteristics : Fin m → Q → ℝ} {lowerBounds upperBounds : Fin m → ℝ}

@[simp] theorem boundedCharacteristicProblem_constraints_castAdd
    (j : Fin m)
    (x : Q) :
    (boundedCharacteristicProblem Q objective characteristics lowerBounds upperBounds).constraints
        (j.castAdd m) x =
      lowerBounds j - characteristics j x := by
  change
    Fin.append
        (fun k x ↦ lowerBounds k - characteristics k x)
        (fun k x ↦ characteristics k x - upperBounds k)
        (j.castAdd m) x =
      lowerBounds j - characteristics j x
  exact congrFun
    (Fin.append_left
      (fun k x ↦ lowerBounds k - characteristics k x)
      (fun k x ↦ characteristics k x - upperBounds k)
      j) x

@[simp] theorem boundedCharacteristicProblem_constraints_addNat
    (j : Fin m)
    (x : Q) :
    (boundedCharacteristicProblem Q objective characteristics lowerBounds upperBounds).constraints
        (j.addNat m) x =
      characteristics j x - upperBounds j := by
  simpa [boundedCharacteristicProblem] using
    congrFun
      (Fin.append_right
        (fun k x ↦ lowerBounds k - characteristics k x)
        (fun k x ↦ characteristics k x - upperBounds k)
        j) x

/-- Feasibility for the bounded-characteristic problem is exactly satisfaction of each lower and
upper bound constraint. -/
-- Proof sketch: unfold the owner predicate `IsFeasible`, then use the canonical `Fin.append_left`
-- and `Fin.append_right` equations for the paired lower/upper constraint family; each resulting
-- scalar inequality rewrites by `sub_nonpos`.
theorem boundedCharacteristicProblem_isFeasible_iff
    {x : Q} :
    (boundedCharacteristicProblem Q objective characteristics lowerBounds
      upperBounds).IsFeasible x ↔
      ∀ j : Fin m, lowerBounds j ≤ characteristics j x ∧ characteristics j x ≤ upperBounds j := by
  let problem := boundedCharacteristicProblem Q objective characteristics lowerBounds upperBounds
  change x ∈ problem.feasibleSet ↔ _
  have hproblem :
      x ∈ problem.feasibleSet ↔
        ∀ i : Fin (m + m), problem.constraints i x ≤ 0 :=
    problem.mem_feasibleSet_iff
      (boundedCharacteristicProblem_hasLeConstraints Q objective characteristics lowerBounds
        upperBounds)
  refine hproblem.trans ?_
  constructor
  · intro hx j
    exact
      ⟨by simpa [problem, sub_nonpos] using hx (j.castAdd m),
        by simpa [problem, sub_nonpos] using hx (j.addNat m)⟩
  · intro hx i
    cases i using Fin.addCases with
    | left j =>
        simpa [problem, sub_nonpos] using (hx j).1
    | right j =>
        simpa [problem, sub_nonpos] using (hx j).2

end
