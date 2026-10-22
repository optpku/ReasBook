/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import ComputationalMethodsInverseProblems_Vogel_2002.Chap08.Definition_8_1.VectorFields

public section

noncomputable section

namespace VariationalRegularization

/-- The canonical `L¹` carrier on the unit square `[0,1] × [0,1]`. -/
abbrev UnitSquareL1 := MeasureTheory.Lp ℝ 1 (MeasureTheory.volume.restrict unitSquare)

/-- The canonical `L¹` representative of an integrable function on the unit
square. -/
@[expose]
def unitSquareToL1
    (f : ℝ × ℝ → ℝ)
    (hf : MeasureTheory.IntegrableOn f unitSquare) : UnitSquareL1 :=
  hf.toL1 f

/-- The defining `L¹`-bridge formula for `unitSquareToL1`. -/
theorem unitSquareToL1_def
    (f : ℝ × ℝ → ℝ)
    (hf : MeasureTheory.IntegrableOn f unitSquare) :
    unitSquareToL1 f hf = hf.toL1 f := rfl

/-- The unit-square divergence pairing `∫_[0,1]^2 f · div v` against an
admissible test field, expressed on the canonical unit-square `L¹` carrier. -/
@[expose]
def unitSquareL1DivergencePairing
    (f : UnitSquareL1)
    (v : UnitSquareTestField) : ℝ :=
  ∫ x in (0 : ℝ)..1, ∫ y in (0 : ℝ)..1, f (x, y) * unitSquareDivergence v (x, y)

/-- The defining iterated-integral formula for
`unitSquareL1DivergencePairing`. -/
theorem unitSquareL1DivergencePairing_def
    (f : UnitSquareL1)
    (v : UnitSquareTestField) :
    unitSquareL1DivergencePairing f v =
      ∫ x in (0 : ℝ)..1, ∫ y in (0 : ℝ)..1, f (x, y) * unitSquareDivergence v (x, y) := rfl

/-- The unit-square divergence pairing `∫_[0,1]^2 f · div v` against an
admissible test field, for an `f` that is integrable on `[0,1] × [0,1]`. The
integrability witness is used through the canonical unit-square `L¹`
representative `unitSquareToL1 f hf`. -/
@[expose]
def unitSquareDivergencePairing
    (f : ℝ × ℝ → ℝ)
    (hf : MeasureTheory.IntegrableOn f unitSquare)
    (v : UnitSquareTestField) : ℝ :=
  unitSquareL1DivergencePairing (unitSquareToL1 f hf) v

/-- The source-facing bridge from integrable raw functions to the canonical
unit-square `L¹` divergence pairing. -/
theorem unitSquareDivergencePairing_def
    (f : ℝ × ℝ → ℝ)
    (hf : MeasureTheory.IntegrableOn f unitSquare)
    (v : UnitSquareTestField) :
    unitSquareDivergencePairing f hf v =
      unitSquareL1DivergencePairing (unitSquareToL1 f hf) v := rfl

/-- The source-facing iterated-integral formula for
`unitSquareDivergencePairing`, written using the canonical unit-square `L¹`
representative of `f`. -/
theorem unitSquareDivergencePairing_integral_def
    (f : ℝ × ℝ → ℝ)
    (hf : MeasureTheory.IntegrableOn f unitSquare)
    (v : UnitSquareTestField) :
    unitSquareDivergencePairing f hf v =
      ∫ x in (0 : ℝ)..1, ∫ y in (0 : ℝ)..1,
        (unitSquareToL1 f hf) (x, y) * unitSquareDivergence v (x, y) := rfl

end VariationalRegularization
