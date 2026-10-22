/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import ComputationalMethodsInverseProblems_Vogel_2002.Chap08.Definition_8_9
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Data.EReal.Basic

public section

noncomputable section

namespace VariationalRegularization

variable {d : ℕ}

/-- Definition 8.4-extra-2 (1). The nonsmooth dual approximation `(8.76)` of the
total-variation functional on `L¹(Ω)` with explicit dual penalty `φStar`. -/
def approximateTotalVariation
    {Ω : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin d))}
    (φStar : EuclideanSpace ℝ (Fin d) → ℝ)
    (f : MeasureTheory.Lp ℝ 1 (domainMeasure Ω)) : EReal :=
  sSup (Set.range fun v : AdmissibleTestField Ω ↦
    (((∫ x, (-(f x)) * admissibleDivergence v x - φStar (v.toTestFunction x)
          ∂domainMeasure Ω) : ℝ) : EReal))

/-- The defining supremum formula for `approximateTotalVariation`. -/
theorem approximateTotalVariation_def
    {Ω : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin d))}
    (φStar : EuclideanSpace ℝ (Fin d) → ℝ)
    (f : MeasureTheory.Lp ℝ 1 (domainMeasure Ω)) :
    approximateTotalVariation φStar f =
      sSup (Set.range fun v : AdmissibleTestField Ω ↦
        (((∫ x, (-(f x)) * admissibleDivergence v x - φStar (v.toTestFunction x)
              ∂domainMeasure Ω) : ℝ) : EReal)) := by
  simp [approximateTotalVariation]

/-- Definition 8.4-extra-2 (2). The smooth-norm approximation `(8.77)` of total
variation motivated by Example 8.5. -/
def smoothNormApproxTotalVariation
    {Ω : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin d))}
    (β : ℝ)
    (f : MeasureTheory.Lp ℝ 1 (domainMeasure Ω)) : EReal :=
  approximateTotalVariation
    (fun y ↦ (-β) * Real.sqrt (1 - ‖y‖ ^ 2)) f

namespace Approximation

/-- Scoped notation for the Chapter 8 smooth-norm approximation `J_β`. -/
scoped notation "J_β" => smoothNormApproxTotalVariation

end Approximation

open scoped VariationalRegularization.Approximation

/-- The defining supremum formula for the Chapter 8 smooth approximation `J_β`. -/
theorem smoothNormApproxTotalVariation_def
    {Ω : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin d))}
    (β : ℝ)
    (f : MeasureTheory.Lp ℝ 1 (domainMeasure Ω)) :
    J_β β f =
      sSup (Set.range fun v : AdmissibleTestField Ω ↦
        (((∫ x, (-(f x)) * admissibleDivergence v x +
                β * Real.sqrt (1 - ‖v.toTestFunction x‖ ^ 2)
              ∂domainMeasure Ω) : ℝ) : EReal)) := by
  simp [smoothNormApproxTotalVariation, approximateTotalVariation, sub_eq_add_neg]

/-- `J_β` is the `(8.76)` owner specialized to the Example 8.5 dual term. -/
theorem smoothNormApproxTotalVariation_eq_approximateTotalVariation
    {Ω : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin d))}
    (β : ℝ)
    (f : MeasureTheory.Lp ℝ 1 (domainMeasure Ω)) :
    J_β β f =
      approximateTotalVariation
        (fun y ↦ (-β) * Real.sqrt (1 - ‖y‖ ^ 2)) f := by
  simp [smoothNormApproxTotalVariation]

/-- Definition 8.4-extra-2 (3). The Huber approximation `(8.78)` of total
variation motivated by Example 8.6. -/
def huberApproxTotalVariation
    {Ω : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin d))}
    (ε : ℝ)
    (f : MeasureTheory.Lp ℝ 1 (domainMeasure Ω)) : EReal :=
  approximateTotalVariation
    (fun y ↦ (ε / 2) * ‖y‖ ^ 2) f

namespace Approximation

/-- Scoped notation for the Chapter 8 Huber approximation `J_ε`. -/
scoped notation "J_ε" => huberApproxTotalVariation

end Approximation

/-- The defining supremum formula for the Chapter 8 Huber approximation `J_ε`. -/
theorem huberApproxTotalVariation_def
    {Ω : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin d))}
    (ε : ℝ)
    (f : MeasureTheory.Lp ℝ 1 (domainMeasure Ω)) :
    J_ε ε f =
      sSup (Set.range fun v : AdmissibleTestField Ω ↦
        (((∫ x, (-(f x)) * admissibleDivergence v x -
                (ε / 2) * ‖v.toTestFunction x‖ ^ 2
              ∂domainMeasure Ω) : ℝ) : EReal)) := by
  simp [huberApproxTotalVariation, approximateTotalVariation]

/-- `J_ε` is the `(8.76)` owner specialized to the Example 8.6 dual term. -/
theorem huberApproxTotalVariation_eq_approximateTotalVariation
    {Ω : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin d))}
    (ε : ℝ)
    (f : MeasureTheory.Lp ℝ 1 (domainMeasure Ω)) :
    J_ε ε f =
      approximateTotalVariation
        (fun y ↦ (ε / 2) * ‖y‖ ^ 2) f := by
  simp [huberApproxTotalVariation]

end VariationalRegularization
