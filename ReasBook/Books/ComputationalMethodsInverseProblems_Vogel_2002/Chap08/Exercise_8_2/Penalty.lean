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

/-- The within-derivative of `f` in the first coordinate direction on the unit
square `[0,1] × [0,1]`. -/
@[expose]
def unitSquarePartialX (f : ℝ × ℝ → ℝ) : ℝ × ℝ → ℝ :=
  fun p ↦ fderivWithin ℝ f unitSquare p (1, 0)

/-- The defining formula for `unitSquarePartialX`. -/
theorem unitSquarePartialX_def (f : ℝ × ℝ → ℝ) (p : ℝ × ℝ) :
    unitSquarePartialX f p = fderivWithin ℝ f unitSquare p (1, 0) := by
  -- This is the exposed definition of the first within-partial derivative.
  rfl

/-- The within-derivative of `f` in the second coordinate direction on the unit
square `[0,1] × [0,1]`. -/
@[expose]
def unitSquarePartialY (f : ℝ × ℝ → ℝ) : ℝ × ℝ → ℝ :=
  fun p ↦ fderivWithin ℝ f unitSquare p (0, 1)

/-- The defining formula for `unitSquarePartialY`. -/
theorem unitSquarePartialY_def (f : ℝ × ℝ → ℝ) (p : ℝ × ℝ) :
    unitSquarePartialY f p = fderivWithin ℝ f unitSquare p (0, 1) := by
  -- This is the exposed definition of the second within-partial derivative.
  rfl

/-- The squared gradient magnitude `|∇f|²` on the unit square, expressed
through the named within-partial derivatives. -/
@[expose]
def unitSquareGradientSq (f : ℝ × ℝ → ℝ) : ℝ × ℝ → ℝ :=
  fun p ↦ unitSquarePartialX f p ^ 2 + unitSquarePartialY f p ^ 2

/-- The defining formula for `unitSquareGradientSq`. -/
theorem unitSquareGradientSq_def (f : ℝ × ℝ → ℝ) (p : ℝ × ℝ) :
    unitSquareGradientSq f p = unitSquarePartialX f p ^ 2 + unitSquarePartialY f p ^ 2 := by
  -- Unfold the named squared-gradient integrand.
  rfl

/-- The pointwise gradient pairing `∇fᵀ ∇h` on the unit square, expressed
through the named within-partial derivatives. -/
@[expose]
def unitSquareGradientDot (f h : ℝ × ℝ → ℝ) : ℝ × ℝ → ℝ :=
  fun p ↦ unitSquarePartialX f p * unitSquarePartialX h p +
    unitSquarePartialY f p * unitSquarePartialY h p

/-- The defining formula for `unitSquareGradientDot`. -/
theorem unitSquareGradientDot_def (f h : ℝ × ℝ → ℝ) (p : ℝ × ℝ) :
    unitSquareGradientDot f h p =
      unitSquarePartialX f p * unitSquarePartialX h p +
        unitSquarePartialY f p * unitSquarePartialY h p := by
  -- Unfold the named pointwise gradient pairing.
  rfl

/-- The smooth unit-square penalty `(8.28)` associated to `ψ`. -/
@[expose]
def unitSquareSmoothPenalty (ψ : ℝ → ℝ) : (ℝ × ℝ → ℝ) → ℝ :=
  fun f ↦
    (1 / 2 : ℝ) *
      (∫ x in (0 : ℝ)..1, ∫ y in (0 : ℝ)..1, ψ (unitSquareGradientSq f (x, y)))

/-- The defining integral formula for `unitSquareSmoothPenalty`. -/
theorem unitSquareSmoothPenalty_def (ψ : ℝ → ℝ) (f : ℝ × ℝ → ℝ) :
    unitSquareSmoothPenalty ψ f =
      (1 / 2 : ℝ) *
        (∫ x in (0 : ℝ)..1, ∫ y in (0 : ℝ)..1, ψ (unitSquareGradientSq f (x, y))) := by
  -- This is exactly the exposed definition of the smooth penalty.
  rfl

end VariationalRegularization
