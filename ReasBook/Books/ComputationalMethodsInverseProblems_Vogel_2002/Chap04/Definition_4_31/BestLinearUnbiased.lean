/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import ComputationalMethodsInverseProblems_Vogel_2002.Chap04.Definition_4_31.LinearEstimator
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
public import Mathlib.Order.Filter.Extr
public import Mathlib.Probability.Notation

public section

noncomputable section

open scoped ProbabilityTheory

namespace ProbabilityTheory

universe u v w

section

variable {Ω : Type u} [MeasurableSpace Ω]
variable {n : Type v} [Fintype n]
variable {m : Type w} [Fintype m] [DecidableEq m]

/-- The BLUE objective `J(Xhat) = μ[fun ω ↦ ‖Xhat ω - x‖ ^ 2]`. -/
def blueObjective (μ : MeasureTheory.Measure Ω) (x : EuclideanSpace ℝ n)
    (Xhat : Ω → EuclideanSpace ℝ n) : ℝ :=
  μ[fun ω ↦ ‖Xhat ω - x‖ ^ 2]

/-- The defining formula for `blueObjective`. -/
theorem blueObjective_def (μ : MeasureTheory.Measure Ω) (x : EuclideanSpace ℝ n)
    (Xhat : Ω → EuclideanSpace ℝ n) :
    blueObjective μ x Xhat = μ[fun ω ↦ ‖Xhat ω - x‖ ^ 2] := by
  -- Unfold the objective to expose the defining expectation formula.
  simp [blueObjective]

/-- The admissible class of linear unbiased estimators with finite second moment. -/
def blueAdmissibleSet (μ : MeasureTheory.Measure Ω) (x : EuclideanSpace ℝ n)
    (Z : Ω → EuclideanSpace ℝ m) : Set (Ω → EuclideanSpace ℝ n) :=
  { Xhat | (∃ B : Matrix n m ℝ, Xhat = linearEstimator B Z) ∧
      μ[Xhat] = x ∧
      MeasureTheory.MemLp Xhat 2 μ }

/-- Membership in `blueAdmissibleSet` means linearity in `Z`, unbiasedness for `x`, and finite
second moment. -/
theorem mem_blueAdmissibleSet_iff (μ : MeasureTheory.Measure Ω) (x : EuclideanSpace ℝ n)
    (Z : Ω → EuclideanSpace ℝ m) (Xhat : Ω → EuclideanSpace ℝ n) :
    Xhat ∈ blueAdmissibleSet μ x Z ↔
      (∃ B : Matrix n m ℝ, Xhat = linearEstimator B Z) ∧
        μ[Xhat] = x ∧
        MeasureTheory.MemLp Xhat 2 μ := by
  -- Membership is definitionally the conjunction of the three admissibility conditions.
  rfl

/-- A candidate estimator is BLUE when it is admissible and minimizes `blueObjective` on the
admissible class. -/
structure IsBestLinearUnbiasedEstimator
    (μ : MeasureTheory.Measure Ω) (x : EuclideanSpace ℝ n) (Z : Ω → EuclideanSpace ℝ m)
    (Xhat : Ω → EuclideanSpace ℝ n) : Prop where
  /-- The estimator belongs to the admissible BLUE class. -/
  mem_admissible : Xhat ∈ blueAdmissibleSet μ x Z
  /-- The estimator minimizes the mean squared error on the admissible BLUE class. -/
  optimal : IsMinOn (blueObjective μ x) (blueAdmissibleSet μ x Z) Xhat

/-- `IsBestLinearUnbiasedEstimator μ x Z Xhat` means that `Xhat` is admissible and minimizes
`blueObjective μ x` on `blueAdmissibleSet μ x Z`. -/
theorem isBestLinearUnbiasedEstimator_iff
    (μ : MeasureTheory.Measure Ω) (x : EuclideanSpace ℝ n) (Z : Ω → EuclideanSpace ℝ m)
    (Xhat : Ω → EuclideanSpace ℝ n) :
    IsBestLinearUnbiasedEstimator μ x Z Xhat ↔
      Xhat ∈ blueAdmissibleSet μ x Z ∧
      IsMinOn (blueObjective μ x) (blueAdmissibleSet μ x Z) Xhat :=
  by
    constructor
    · intro h
      exact ⟨h.mem_admissible, h.optimal⟩
    · rintro ⟨h_mem, h_opt⟩
      exact ⟨h_mem, h_opt⟩

namespace IsBestLinearUnbiasedEstimator

set_option linter.defProp false in
/-- Construct a BLUE certificate from admissibility and optimality data. -/
def ofMemOptimal (μ : MeasureTheory.Measure Ω) (x : EuclideanSpace ℝ n)
    (Z : Ω → EuclideanSpace ℝ m) (Xhat : Ω → EuclideanSpace ℝ n)
    (h_mem : Xhat ∈ blueAdmissibleSet μ x Z)
    (h_opt : IsMinOn (blueObjective μ x) (blueAdmissibleSet μ x Z) Xhat) :
    IsBestLinearUnbiasedEstimator μ x Z Xhat :=
  { mem_admissible := h_mem
    optimal := h_opt }

end IsBestLinearUnbiasedEstimator

end

end ProbabilityTheory
