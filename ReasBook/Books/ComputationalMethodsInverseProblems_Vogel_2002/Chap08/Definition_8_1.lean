/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import ComputationalMethodsInverseProblems_Vogel_2002.Chap08.Definition_8_1.Pairing

public section

noncomputable section

namespace VariationalRegularization

/-- The Chapter 8 total variation of a canonical unit-square `L¹` datum, defined
as the supremum of its divergence pairing against admissible `C¹` test vector
fields with pointwise norm at most `1` and zero boundary values on
`[0,1] × [0,1]`. -/
@[expose]
def unitSquareL1TotalVariation
    (f : UnitSquareL1) : EReal :=
  sSup (Set.range fun v : UnitSquareTestField ↦
    (unitSquareL1DivergencePairing f v : EReal))

/-- The defining supremum formula for `unitSquareL1TotalVariation`. -/
theorem unitSquareL1TotalVariation_def
    (f : UnitSquareL1) :
    unitSquareL1TotalVariation f =
      sSup (Set.range fun v : UnitSquareTestField ↦
        (unitSquareL1DivergencePairing f v : EReal)) := rfl

/-- Definition 8.1-extra-1. Formulas `(8.1)`-`(8.3)` are motivational only;
the Chapter 8 total variation of `f : ℝ × ℝ → ℝ` on the unit square is defined
by the dual formula `(8.4)`, namely as the supremum of the divergence pairing
against admissible `C¹` test vector fields with pointwise norm at most `1` and
zero boundary values on `[0,1] × [0,1]`, for `f` integrable on the unit square.
The integrability witness is used through the canonical unit-square `L¹`
representative `unitSquareToL1 f hf`. The value is taken in `EReal`, so it may
be `⊤` for general integrable `f`. -/
@[expose]
def unitSquareTotalVariation
    (f : ℝ × ℝ → ℝ)
    (hf : MeasureTheory.IntegrableOn f unitSquare) : EReal :=
  unitSquareL1TotalVariation (unitSquareToL1 f hf)

/-- The source-facing bridge from integrable raw functions to the canonical
unit-square `L¹` total-variation owner. -/
theorem unitSquareTotalVariation_eq_unitSquareL1TotalVariation
    (f : ℝ × ℝ → ℝ)
    (hf : MeasureTheory.IntegrableOn f unitSquare) :
    unitSquareTotalVariation f hf = unitSquareL1TotalVariation (unitSquareToL1 f hf) := rfl

/-- The defining supremum formula for `unitSquareTotalVariation`. -/
theorem unitSquareTotalVariation_def
    (f : ℝ × ℝ → ℝ)
    (hf : MeasureTheory.IntegrableOn f unitSquare) :
    unitSquareTotalVariation f hf =
      sSup (Set.range fun v : UnitSquareTestField ↦
        (unitSquareDivergencePairing f hf v : EReal)) := rfl

/-- Every admissible unit-square divergence pairing is bounded above by
`unitSquareTotalVariation`. -/
theorem unitSquareDivergencePairing_le_unitSquareTotalVariation
    (f : ℝ × ℝ → ℝ)
    (hf : MeasureTheory.IntegrableOn f unitSquare)
    (v : UnitSquareTestField) :
    (unitSquareDivergencePairing f hf v : EReal) ≤ unitSquareTotalVariation f hf := by
  rw [unitSquareTotalVariation_def]
  exact le_sSup ⟨v, rfl⟩

/-- An `EReal` upper bound for every admissible unit-square divergence pairing
bounds `unitSquareTotalVariation`. -/
theorem unitSquareTotalVariation_le_of_forall_unitSquareDivergencePairing_le
    (f : ℝ × ℝ → ℝ)
    (hf : MeasureTheory.IntegrableOn f unitSquare)
    {a : EReal}
    (ha : ∀ v : UnitSquareTestField, (unitSquareDivergencePairing f hf v : EReal) ≤ a) :
    unitSquareTotalVariation f hf ≤ a := by
  rw [unitSquareTotalVariation_def]
  refine sSup_le ?_
  rintro _ ⟨v, rfl⟩
  exact ha v

/-- A unit-square total-variation value is identified once every admissible
unit-square divergence pairing is bounded above by `a` and one admissible test
field attains `a`. -/
theorem unitSquareTotalVariation_eq_of_pairing_upper_bound_and_attained
    (f : ℝ × ℝ → ℝ)
    (hf : MeasureTheory.IntegrableOn f unitSquare)
    {a : EReal}
    (hupper :
      ∀ v : UnitSquareTestField, (unitSquareDivergencePairing f hf v : EReal) ≤ a)
    (v : UnitSquareTestField)
    (hsharp : (unitSquareDivergencePairing f hf v : EReal) = a) :
    unitSquareTotalVariation f hf = a := by
  apply le_antisymm
  · exact unitSquareTotalVariation_le_of_forall_unitSquareDivergencePairing_le f hf hupper
  · rw [← hsharp]
    exact unitSquareDivergencePairing_le_unitSquareTotalVariation f hf v

end VariationalRegularization
