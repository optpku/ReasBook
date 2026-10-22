/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import ComputationalMethodsInverseProblems_Vogel_2002.Chap08.Definition_8_9.Pairing

public section

noncomputable section

namespace VariationalRegularization

open scoped BigOperators

variable {d : ℕ}

/-- The Chapter 8 total variation of `f ∈ L¹(Ω)` is the supremum of the
divergence pairing `∫ x, f x * admissibleDivergence v x ∂domainMeasure Ω`
over admissible compactly supported `C¹` vector fields `v` on `Ω` with
`‖v x‖ ≤ 1` for all `x ∈ Ω`. -/
@[expose]
def totalVariation
    {Ω : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin d))}
    (f : MeasureTheory.Lp ℝ 1 (domainMeasure Ω)) : EReal :=
  sSup (Set.range fun v : AdmissibleTestField Ω ↦
    (admissibleDivergencePairing f v : EReal))

/-- Definition 8.9. The total variation of `f ∈ L¹(Ω)` is given by the
defining supremum formula over admissible divergence pairings. -/
theorem totalVariation_def
    {Ω : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin d))}
    (f : MeasureTheory.Lp ℝ 1 (domainMeasure Ω)) :
    totalVariation f =
      sSup (Set.range fun v : AdmissibleTestField Ω ↦
        (admissibleDivergencePairing f v : EReal)) := by
  -- Unfold the definition to expose the defining supremum.
  simp [totalVariation]

/-- Every admissible divergence pairing is bounded above by `totalVariation`. -/
theorem admissibleDivergencePairing_le_totalVariation
    {Ω : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin d))}
    (f : MeasureTheory.Lp ℝ 1 (domainMeasure Ω))
    (v : AdmissibleTestField Ω) :
    (admissibleDivergencePairing f v : EReal) ≤ totalVariation f := by
  rw [totalVariation_def]
  exact le_sSup ⟨v, rfl⟩

/-- An `EReal` upper bound for every admissible divergence pairing bounds
`totalVariation`. -/
theorem totalVariation_le_of_forall_admissibleDivergencePairing_le
    {Ω : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin d))}
    (f : MeasureTheory.Lp ℝ 1 (domainMeasure Ω))
    {a : EReal}
    (ha : ∀ v : AdmissibleTestField Ω, (admissibleDivergencePairing f v : EReal) ≤ a) :
    totalVariation f ≤ a := by
  rw [totalVariation_def]
  refine sSup_le ?_
  rintro _ ⟨v, rfl⟩
  exact ha v

/-- A total-variation value is identified once every admissible divergence pairing is bounded
above by `a` and one admissible test field attains `a`. -/
theorem totalVariation_eq_of_pairing_upper_bound_and_attained
    {Ω : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin d))}
    (f : MeasureTheory.Lp ℝ 1 (domainMeasure Ω))
    {a : EReal}
    (hupper :
      ∀ v : AdmissibleTestField Ω, (admissibleDivergencePairing f v : EReal) ≤ a)
    (v : AdmissibleTestField Ω)
    (hsharp : (admissibleDivergencePairing f v : EReal) = a) :
    totalVariation f = a := by
  apply le_antisymm
  · exact totalVariation_le_of_forall_admissibleDivergencePairing_le f hupper
  · rw [← hsharp]
    exact admissibleDivergencePairing_le_totalVariation f v

end VariationalRegularization
