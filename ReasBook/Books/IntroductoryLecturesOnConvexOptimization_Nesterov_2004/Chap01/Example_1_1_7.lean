/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap01.Example_1_1_5

-- Declarations for this item will be appended below by the statement pipeline.

variable {n m : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin n)

/- Primary domain: constrained optimization with a transcendental equality encoding of integrality.

Source/core/bridge triage for Example 1.1.7:
* source-facing: the bounded characteristic problem together with the adjoined equalities
  `sin (π x_i) = 0`
* core/canonical: `GeneralMinimizationProblem` and its owner predicate
  `problem.IsFeasible`
* bridge/view: `boundedCharacteristicProblem` and
  `boundedCharacteristicProblem_isFeasible_iff`, which package the lower/upper characteristic
  bounds into the chapter's owner object and unpack feasibility back to the coordinate conditions

Relevant declarations sampled before refining:
* the owner feasible predicate `problem.IsFeasible` in `Chap01/Definition_1_1_3.lean`
* `boundedCharacteristicProblem` in `Chap01/Example_1_1_5.lean`
* `boundedCharacteristicProblem_isFeasible_iff` in `Chap01/Example_1_1_5.lean`
* `Real.sin_eq_zero_iff` in mathlib, the ambient zero-set description behind the integrality
  encoding

Best owner abstraction:
* `GeneralMinimizationProblem n (m + m + n)`, built by adjoining the new equality constraints to
  the existing source-facing bounded problem from Example 1.1.5

Primitive data:
* the structural set `Q`, objective, characteristic family, and lower/upper bounds
* the coordinate equalities `sin (π x_i) = 0`

Derived API:
* `transcendentalIntegerOptimizationProblem`, the resulting owner object
* `isFeasible_transcendentalIntegerOptimizationProblem_iff`, the source-facing feasibility view
  obtained by combining the owner-level decomposition with the upstream bounded-characteristic
  bridge and the canonical mathlib theorem `Real.sin_eq_zero_iff` -/

/-- Example 1.1.7: Integer constraints can be encoded by adjoining the transcendental equalities
`sin (π x_i) = 0` to the bounded optimization problem on `Q`. -/
noncomputable def transcendentalIntegerOptimizationProblem
    (Q : Set E)
    (objective : Q → ℝ)
    (characteristics : Fin m → Q → ℝ)
    (lowerBounds upperBounds : Fin m → ℝ) :
    GeneralMinimizationProblem n (m + m + n) :=
  let boundedProblem :=
    boundedCharacteristicProblem Q objective characteristics lowerBounds upperBounds
  { boundedProblem with
    constraints :=
      Fin.append boundedProblem.constraints (fun i x ↦ Real.sin (Real.pi * (x.1 i)))
    senses := Fin.append boundedProblem.senses (fun _ ↦ .eq) }

/-- Feasibility for the transcendental integer optimization problem is exactly the conjunction of
the original lower and upper bounds with coordinatewise integrality of the decision variables. -/
theorem isFeasible_transcendentalIntegerOptimizationProblem_iff
    {Q : Set E}
    {objective : Q → ℝ}
    {characteristics : Fin m → Q → ℝ}
    {lowerBounds upperBounds : Fin m → ℝ}
    {x : Q} :
    (transcendentalIntegerOptimizationProblem Q objective characteristics lowerBounds
      upperBounds).IsFeasible x ↔
      (∀ j : Fin m, lowerBounds j ≤ characteristics j x ∧ characteristics j x ≤ upperBounds j) ∧
        ∀ i : Fin n, ∃ z : ℤ, x.1 i = z := by
  let boundedProblem :=
    boundedCharacteristicProblem Q objective characteristics lowerBounds upperBounds
  have hproblem :
    (transcendentalIntegerOptimizationProblem Q objective characteristics lowerBounds
      upperBounds).IsFeasible x ↔
      boundedProblem.IsFeasible x ∧
        ∀ i : Fin n, Real.sin (Real.pi * (x.1 i)) = 0 := by
    constructor
    · intro hx
      refine ⟨?_, ?_⟩
      · intro j
        simpa [transcendentalIntegerOptimizationProblem, boundedProblem, Fin.append_left] using
          hx (j.castAdd n)
      · intro i
        simpa [ConstraintSense.Holds, transcendentalIntegerOptimizationProblem, boundedProblem,
          Fin.append_right] using hx (i.natAdd (m + m))
    · rintro ⟨hbounded, hsin⟩ i
      cases i using Fin.addCases with
      | left j =>
          simpa [transcendentalIntegerOptimizationProblem, boundedProblem, Fin.append_left] using
            hbounded j
      | right j =>
          simpa [ConstraintSense.Holds, transcendentalIntegerOptimizationProblem, boundedProblem,
            Fin.append_right] using hsin j
  constructor
  · intro hx
    rcases hproblem.mp hx with ⟨hbounded, hsin⟩
    refine ⟨?_, ?_⟩
    · exact (boundedCharacteristicProblem_isFeasible_iff.mp hbounded)
    · intro i
      rcases Real.sin_eq_zero_iff.mp (hsin i) with ⟨z, hz⟩
      refine ⟨z, ?_⟩
      have hz' : x.1 i * Real.pi = (z : ℝ) * Real.pi := by
        simpa [mul_comm] using hz.symm
      exact (mul_left_inj' Real.pi_ne_zero).mp hz'
  · rintro ⟨hbounded, hinteger⟩
    refine hproblem.mpr ⟨boundedCharacteristicProblem_isFeasible_iff.mpr hbounded, ?_⟩
    intro i
    rcases hinteger i with ⟨z, hz⟩
    rw [hz]
    exact Real.sin_eq_zero_iff.mpr ⟨z, by simp [mul_comm]⟩
